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

ML_file \<open>suffices.ML\<close>

text \<open>
  The implementation provides the Isabelle/ML entry points
  \<^ML>\<open>Suffices.suffices\<close> (internal interface, on certified terms) and
  \<^ML>\<open>Suffices.suffices_cmd\<close> (concrete syntax, on strings).
\<close>

end
