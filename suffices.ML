(*  Title:      suffices.ML
    Author:     Balazs Toth

One step of backward reasoning within Isar proof text: it suffices to show
the given statement(s). The justification proves that the statements imply
the current conclusion, which they then replace among the pending goals.
*)

signature SUFFICES =
sig
  val suffices: (binding * typ option * mixfix) list ->
    (Thm.binding * (term * term list) list) list ->
    (Thm.binding * (term * term list) list) list ->
    bool -> Proof.state -> Proof.state
  val suffices_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * (string * string list) list) list ->
    (Attrib.binding * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
end;

structure Suffices: SUFFICES =
struct

(** the conclusion of the current pending goal **)

fun unprotect t = the_default t (try Logic.unprotect t);

(*the conclusion of a pending subgoal, with its parameters substituted by
  frees that are fresh in the context*)
fun subgoal_concl ctxt sg =
  let
    val params = Logic.strip_params sg;
    val (xs, _) = Variable.variant_fixes (map #1 params) ctxt;
    val frees = map2 (fn x => fn (_, T) => Free (x, T)) xs params;
    val concl = unprotect (Term.subst_bounds (rev frees, Logic.strip_assums_concl sg));
  in Object_Logic.drop_judgment ctxt concl end;

(*Schematic variables in the conclusion (e.g. the witness of "rule exI")
  must be instantiated uniformly, before any local variables are fixed or
  obtained, so the goal cannot be reduced relative to the local context.*)
fun no_schematics ctxt c =
  (case Term.add_vars c [] of
    [] => c
  | vars =>
      error (Pretty.string_of (Pretty.chunks
        [Pretty.block
          (Pretty.text "The pending goal contains schematic variables" @ [Pretty.brk 1] @
            Pretty.commas (map (Pretty.quote o Syntax.pretty_term ctxt o Var) (rev vars))),
         Pretty.block
          (Pretty.text "Their instantiation cannot depend on locally fixed or obtained \
            \variables; instantiate first, e.g. via a rule instance such as \
            \\"rule exI [where x = t]\"")])));

(*Determine the current conclusion: the term of any context binding that
  denotes the conclusion of a pending subgoal (?thesis, ?case, ...), or a
  bare pending subgoal itself. Returns the conclusion as a proposition,
  together with the bindings that denoted it.*)
fun current_concl state =
  let
    val ctxt = Proof.context_of state;
    val thy = Proof_Context.theory_of ctxt;
    val {context = goal_ctxt, goal} =
      (case try Proof.simple_goal state of
        SOME res => res
      | NONE => error "No pending goal");
    val subgoals = Thm.prems_of goal;
    val _ = null subgoals andalso error "No pending subgoals";
    val concls = map (subgoal_concl ctxt) subgoals;
    fun matches t =
      let val t' = singleton (Variable.export_terms ctxt goal_ctxt) t in
        exists (fn c =>
          t' aconv c orelse (Pattern.matches thy (t', c) handle Pattern.Pattern => false)) concls
      end;
    val binds =
      Vartab.dest (Variable.binds_of ctxt)
      |> filter_out (member (op =) Auto_Bind.no_facts o fst)  (*?this, ?dddot denote facts*)
      |> map_filter (fn (xi, (_, t)) => if matches t then SOME (xi, t) else NONE);
  in
    (case distinct (op aconv) (map snd binds) of
      [] =>
        (*no abbreviation: work on a pending subgoal directly, instantiating
          its parameters by the fixed variables of the same name*)
        let
          val visible = perhaps (try Name.dest_skolem);
          fun instance sg =
            let
              val params = Logic.strip_params sg;
              val frees = params |> map (fn (x, T) =>
                Option.map (fn x' => Free (x', T))
                  (Variable.lookup_fixed ctxt (visible x)));
            in
              if forall is_some frees then
                SOME (unprotect
                  (Term.subst_bounds (rev (map the frees), Logic.strip_assums_concl sg)))
              else NONE
            end;
          val instances = map_filter instance subgoals;
        in
          (case find_first (fn c => null (Term.add_vars c [])) instances of
            SOME c => (c, [])
          | NONE =>
              (case instances of
                c :: _ => (no_schematics ctxt c, [])
              | [] =>
                  error "Cannot determine the current conclusion: no term abbreviation \
                    \denotes a pending subgoal, and no pending subgoal has all its \
                    \parameters fixed"))
        end
    | [c] =>
        (no_schematics ctxt (Object_Logic.ensure_propT ctxt c),
         map fst (filter (fn (_, t) => t aconv c) binds))
    | cs =>
        error ("Ambiguous current conclusion: " ^
          commas_quote (map (Syntax.string_of_term ctxt) cs)))
  end;



(** generalization over scope-bound variables (e.g. introduced by obtain) **)

(*a fixed variable whose mere occurrence cannot be exported into the goal
  context, i.e. an obtained parameter*)
fun scope_bound ctxt goal_ctxt (x, T) =
  Variable.is_fixed ctxt x andalso not (Variable.is_fixed goal_ctxt x) andalso
  not (can (Assumption.export_term ctxt goal_ctxt) (Free (x, T)));

(*close the props over their scope-bound frees, together with the local
  assumptions characterizing them: P y becomes \<And>y. A y \<Longrightarrow> P y; all props
  share the same context of variables and assumptions, in the style of the
  subgoals of a proof case*)
fun lift_over ctxt goal_ctxt props =
  let
    val local_prems = Assumption.local_prems_of ctxt goal_ctxt;
    val bad =
      fold (fn prop => fold (insert (op =))
        (filter (scope_bound ctxt goal_ctxt) (rev (Term.add_frees prop [])))) props [];
    fun close ys asms =
      let
        val asms' = local_prems |> filter (fn th =>
          exists (member (op =) (Term.add_frees (Thm.prop_of th) [])) ys);
        val ys' = ys |> fold (fn th =>
            fold (insert (op =)) (filter (scope_bound ctxt goal_ctxt)
              (rev (Term.add_frees (Thm.prop_of th) [])))) asms';
      in if length ys' = length ys andalso length asms' = length asms
        then (ys, asms')
        else close ys' asms'
      end;
  in
    if null bad then (props, [], [])
    else
      let
        val (ys, asms) = close bad [];
        val lifted =
          map (fn prop =>
            fold_rev (Logic.all o Free) ys
              (Logic.list_implies (map Thm.prop_of asms, prop))) props;
      in (lifted, ys, asms) end
  end;



(** the suffices command **)

local

fun gen_suffices prep_stmt prep_att raw_fixes raw_assumes raw_shows int state =
  let
    val ctxt = Proof.context_of state;
    val (concl, concl_binds) = current_concl state;
    val shows = [(Binding.empty_atts, [(concl, [])])];
    fun prep_atts (b, raw_atts) = (b, map (prep_att ctxt) raw_atts);

    val ({vars, propss, result_binds, ...}, _) =
      prep_stmt raw_fixes (map snd raw_shows @ map snd raw_assumes) ctxt;
    val (show_propss, if_propss) = chop (length raw_shows) propss;
    val if_props = flat if_propss;
    val bare_props = flat show_propss;
    val params = map #2 vars;  (*visible name and Free of each for-fix*)

    (*incorporate the if/for elements into the statements themselves:
      P becomes \<And>for-fixes. if-assumptions \<Longrightarrow> P*)
    fun statement_of p =
      if null params andalso null if_props then p
      else fold_rev (Logic.all o #2) params (Logic.list_implies (if_props, p));
    val stmt_propss = (map o map) statement_of show_propss;
    val stmt_props = flat stmt_propss;

    val assumes =
      map2 (fn b => fn ps => (prep_atts b, map (fn p => (p, [])) ps))
        (map fst raw_shows) stmt_propss;

    (*after the justification of "concl if props" is finished: replace concl
      among the pending goals by the (generalized) sufficient statements*)
    fun after_qed _ state' =
      let
        val ctxt' = Proof.context_of state';
        val rule = Proof.the_fact state';
        val goal_ctxt = #context (Proof.simple_goal state');
        val (new_goals, ys, asms) = lift_over ctxt' goal_ctxt stmt_props;

        val new_assumes = map (fn g => (Binding.empty_atts, [(g, [])])) new_goals;
        val (goal_thms, goal_state) =
          Proof.show false NONE (K I) [] new_assumes shows int state';

        (*conclude concl from the justification rule, whose premises are the
          sufficient statements: instances of the presumed (generalized)
          statements, whose premises in turn are local assumptions or
          if-assumptions of the statements themselves*)
        fun concl_tac c =
          HEADGOAL (resolve_tac c [rule]
            THEN_ALL_NEW (resolve_tac c goal_thms
              THEN_ALL_NEW (resolve_tac c asms ORELSE' assume_tac c)));
        val state'' =
          goal_state
          |> Proof.refine_singleton (Method.Basic (fn c => METHOD (fn _ => concl_tac c)))
          |> Proof.local_done_proof;

        (*continue the block in the style of a proof case: fix the for-fixes
          and fresh copies of all scope-bound variables, and assume the
          if-assumptions and the characterizing assumptions for those copies*)
        val (substitution, state''') =
          if null ys andalso null params andalso null if_props then (I, state'')
          else
            let
              val visible = perhaps (try Name.dest_skolem);
              val st1 =
                state'' |> Proof.fix
                  (map (fn (x, T) => (Binding.name (visible x), SOME T, NoSyn)) ys @
                   map2 (fn (b, _, mx) => fn (_, t) =>
                     (b, SOME (snd (Term.dest_Free t)), mx)) (map #1 vars) params);
              val ctxt1 = Proof.context_of st1;
              fun fresh_free (x_visible, t) =
                let val (x, T) = Term.dest_Free t in
                  (t, Free (the_default x (Variable.lookup_fixed ctxt1 x_visible), T))
                end;
              val substitution = Term.subst_atomic
                (map (fn (x, T) => fresh_free (visible x, Free (x, T))) ys @
                 map fresh_free params);
              val st2 = st1
                |> Proof.assume [] []
                    (map (fn th =>
                      (Binding.empty_atts, [(substitution (Thm.prop_of th), [])])) asms @
                     map2 (fn b => fn ps =>
                       (prep_atts b, map (fn p => (substitution p, [])) ps))
                       (map fst raw_assumes) if_propss);
              val new_prems = Assumption.local_prems_of (Proof.context_of st2) ctxt1;
              val asm_prems = asms ~~ take (length asms) new_prems;
              fun fresh_prem th =
                #2 (the (find_first (fn (asm, _) => Thm.eq_thm_prop (asm, th)) asm_prems));

              (*local fact names that denoted the original assumptions now
                denote the fresh copies*)
              val renamed =
                Facts.dest_static false [Proof_Context.facts_of goal_ctxt]
                  (Proof_Context.facts_of ctxt')
                |> filter_out (fn (name, _) =>
                    member (op =) [Auto_Bind.thisN, Auto_Bind.thatN]
                      (Long_Name.base_name name))
                |> map_filter (fn (name, ths) =>
                    if not (null ths) andalso forall (member Thm.eq_thm_prop asms) ths
                    then SOME (Long_Name.base_name name, map fresh_prem ths)
                    else NONE);
              val st3 = st2 |> Proof.map_context (fold (fn (name, ths) =>
                  snd o Proof_Context.note_thms ""
                    ((Binding.name name, []), [(ths, [])])) renamed);
            in (substitution, st3) end;

        (*rebind the abbreviations that denoted the old conclusion to the new
          statement (for the fresh copies); with several statements they are
          merely discarded*)
        val rebind =
          (case bare_props of
            [p] => SOME (Object_Logic.drop_judgment ctxt' (substitution p))
          | _ => NONE);
      in
        state'''
        |> Proof.map_context
            (fold (fn xi => Proof_Context.maybe_bind_term (xi, rebind)) concl_binds)
      end;
  in
    state
    |> Proof.map_context (fold Variable.bind_term result_binds)
    |> Proof.have true NONE after_qed [] assumes shows int
    |-> (fn that_facts =>
          Proof.refine_singleton (Method.Basic (K (Method.insert that_facts))))
  end;

in

val suffices = gen_suffices Proof_Context.cert_stmt (K I);
val suffices_cmd = gen_suffices Proof_Context.read_stmt Attrib.attribute_cmd;

end;



(** concrete syntax **)

local

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes
    >> (fn ((shows, (strict, assumes)), fixes) => (strict, fixes, assumes, shows));

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>suffices\<close>
    "one step of backward reasoning: it suffices to show the given statement(s)"
    (structured_statement >> (fn (strict, fixes, assumes, shows) =>
      Toplevel.proof' (fn int => fn state =>
        if strict then suffices_cmd fixes assumes shows int state
        else
          error "Weak premises (\"when\") are not supported: the sufficient \
            \statements become goals as a whole; use \"if\" for premises of \
            \the statements")));

end;

end;
