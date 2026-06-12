theory Suffices
  imports Pure
  keywords "suffices" :: prf_goal % "proof"
begin

section \<open>The \<^theory_text>\<open>suffices\<close> command \<comment> \<open>one step of backward reasoning in Isar\<close>\<close>

text \<open>
  \<^theory_text>\<open>suffices "P" \<proof>\<close> states that, in order to establish the current
  conclusion \<open>C\<close>, it suffices to show \<open>P\<close>. The proof justifies the reduction
  by proving \<open>P \<Longrightarrow> C\<close> (the sufficient statements are inserted as premises and
  are also available as the fact \<open>that\<close>). Afterwards \<open>P\<close> replaces \<open>C\<close> among
  the pending goals, to be established later by a regular \<^theory_text>\<open>show\<close>:

  \<^theory_text>\<open>
    suffices "P"
      by easy_justification
    \<dots>
    show "P"
    proof -
      \<dots>
    qed
  \<close>

  The current conclusion is determined from the pending goal: any term
  abbreviation of the proof context that denotes the conclusion of a pending
  subgoal is used (e.g. \<open>?thesis\<close> or \<open>?case\<close>, but any binding works); if no
  abbreviation matches, a pending subgoal is taken directly, instantiating
  its parameters by the fixed variables of the same name \<comment> \<open>so suffices also
  works after, say, \<^theory_text>\<open>proof (rule allI)\<close> followed by \<^theory_text>\<open>fix z\<close>\<close>. The
  abbreviation that denoted the old conclusion is
  rebound to the new statement, so the \<^theory_text>\<open>show\<close> above can also be written as
  \<^theory_text>\<open>show ?thesis\<close> resp. \<^theory_text>\<open>show ?case\<close>. This also makes consecutive
  \<^theory_text>\<open>suffices\<close> steps compose. If no abbreviation denoted the conclusion, none
  is added; if several statements are given (juxtaposed or separated by
  \<^theory_text>\<open>and\<close>, as in \<^theory_text>\<open>have\<close>), the stale abbreviation is discarded.

  Sufficient statements may mention variables introduced by \<^theory_text>\<open>obtain\<close>: since
  such variables must not escape their scope, the new goal is generalized
  over them together with their characterizing assumptions, i.e. for
  \<^theory_text>\<open>obtain y where "A y"\<close> the statement \<open>P y\<close> becomes the new goal
  \<open>\<And>y. A y \<Longrightarrow> P y\<close>. In the style of a proof case, \<^theory_text>\<open>suffices\<close> then fixes a
  fresh \<open>y\<close> and assumes \<open>A y\<close> for it, and the rebound abbreviation denotes
  \<open>P y\<close> for that copy \<comment> \<open>so the following proof can use \<open>y\<close> and the literal
  quotation \<open>\<open>A y\<close>\<close> exactly as with the obtained variable\<close>.

  Statements may be generalized explicitly with \<^theory_text>\<open>if\<close> and \<^theory_text>\<open>for\<close>, as in
  \<^theory_text>\<open>have\<close>: \<^theory_text>\<open>suffices "P x" if "A x" for x \<proof>\<close> reduces the conclusion to
  the new goal \<open>\<And>x. A x \<Longrightarrow> P x\<close>, with the justification proving the
  conclusion from that rule; the block then continues with \<open>x\<close> fixed and
  \<open>A x\<close> assumed, like above. The \<^theory_text>\<open>when\<close> element is rejected: its weak
  premises would have to remain as further goals, but the sufficient
  statements become goals as a whole anyway.
\<close>

ML \<open>
local

(* the conclusion of the current pending goal *)

fun unprotect t = the_default t (try Logic.unprotect t);

fun subgoal_concl ctxt sg =
  let
    val params = Logic.strip_params sg;
    val frees =
      map_index (fn (i, (x, T)) => Free (Name.internal (x ^ string_of_int i), T)) params;
    val concl = unprotect (Term.subst_bounds (rev frees, Logic.strip_assums_concl sg));
  in Object_Logic.drop_judgment ctxt concl end;

(*Schematic variables in the conclusion (e.g. the witness of "rule exI")
  must be instantiated uniformly, before any local variables are fixed or
  obtained, so the goal cannot be reduced relative to the local context.*)
fun no_schematics ctxt c =
  (case Term.add_vars c [] of
    [] => c
  | vars =>
      error ("suffices: the pending goal contains the schematic " ^
        commas_quote (map (Syntax.string_of_term ctxt o Var) (rev vars)) ^
        ", whose instantiation cannot depend on locally fixed or obtained \
        \variables; instantiate first, e.g. via a rule instance such as \
        \\"rule exI [where x = t]\""));

(*Determine the current conclusion: the term of any context binding that
  denotes the conclusion of a pending subgoal (?thesis, ?case, ...), or a
  bare pending subgoal itself. Returns the conclusion as a proposition,
  together with the bindings that denoted it.*)
fun current_concl state =
  let
    val ctxt = Proof.context_of state;
    val {context = goal_ctxt, goal} =
      (case try Proof.simple_goal state of
        SOME res => res
      | NONE => error "suffices: no pending goal");
    val subgoals = Thm.prems_of goal;
    val _ = null subgoals andalso error "suffices: no pending subgoals";
    val concls = map (subgoal_concl ctxt) subgoals;
    fun matches t =
      let val t' = singleton (Variable.export_terms ctxt goal_ctxt) t
      in exists (fn c => Term.could_unify (t', c)) concls end;
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
                  error "suffices: cannot determine the current conclusion \
                    \(no term abbreviation denotes a pending subgoal, and no pending \
                    \subgoal has all its parameters fixed)"))
        end
    | [c] =>
        (no_schematics ctxt (Object_Logic.ensure_propT ctxt c),
         map fst (filter (fn (_, t) => t aconv c) binds))
    | cs =>
        error ("suffices: ambiguous current conclusion: " ^
          commas_quote (map (Syntax.string_of_term ctxt) cs)))
  end;


(* generalization over scope-bound variables (e.g. introduced by obtain) *)

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


(* the suffices command *)

fun suffices_cmd (strict, raw_fixes, raw_assumes, raw_shows) int state =
  let
    val _ = strict orelse
      error "suffices: \"when\" makes no sense here, the sufficient statements \
        \become goals anyway; use \"if\" for premises of the statements";

    val ctxt = Proof.context_of state;
    val (concl, concl_binds) = current_concl state;
    val shows = [(Binding.empty_atts, [(concl, [])])];
    fun prep_atts (b, srcs) = (b, map (Attrib.attribute_cmd ctxt) srcs);

    val ({vars, propss, result_binds, ...}, _) =
      Proof_Context.read_stmt raw_fixes (map snd raw_shows @ map snd raw_assumes) ctxt;
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
                    then SOME (Long_Name.base_name name, map (fn th =>
                      nth new_prems
                        (find_index (fn a => Thm.eq_thm_prop (a, th)) asms)) ths)
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

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes
    >> (fn ((shows, (strict, assumes)), fixes) => (strict, fixes, assumes, shows));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>suffices\<close>
    "one step of backward reasoning: it suffices to show the given statement(s)"
    (structured_statement >> (fn args => Toplevel.proof' (suffices_cmd args)));

in end
\<close>

end
