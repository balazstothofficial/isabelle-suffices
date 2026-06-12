theory Suffices_Example
  imports Main Suffices.Suffices
begin

section \<open>Examples for the \<^theory_text>\<open>suffices\<close> command\<close>

text \<open>
  \<^theory_text>\<open>suffices\<close> allows one step of backward reasoning in Isar proofs. It adds
  semantic information to those proofs that establish \<open>?thesis\<close> by first
  showing something stronger and then inferring \<open>?thesis\<close> by an easy
  justification. Instead of

  \<^theory_text>\<open>
    have "statement"
    proof -
      \<dots>  \<comment> \<open>long proof\<close>
    qed
    then show ?thesis
      by easy_justification
  \<close>

  we can now write

  \<^theory_text>\<open>
    suffices "statement"
      by easy_justification
    show ?thesis  \<comment> \<open>now denotes \<open>statement\<close>\<close>
    proof -
      \<dots>  \<comment> \<open>long proof\<close>
    qed
  \<close>

  \<^theory_text>\<open>suffices\<close> works by first making you prove that the specified statements
  really imply the current goal, and then replacing the goal by those
  statements, which are established later by a regular \<^theory_text>\<open>show\<close>. The current
  goal is determined from the pending goal itself: whatever term abbreviation
  denotes it (\<open>?thesis\<close>, \<open>?case\<close>, ...) is found automatically and rebound to
  the new statement, so consecutive \<^theory_text>\<open>suffices\<close> steps compose.

  Unlike \<^theory_text>\<open>show \<dots> when \<dots>\<close>, the sufficient statements may mention variables
  introduced by \<^theory_text>\<open>obtain\<close>: since such variables must not escape their scope,
  the new goal is automatically generalized over them together with their
  characterizing assumptions \<comment> \<open>so for \<^theory_text>\<open>obtain y where "A y"\<close>, a statement
  \<open>P y\<close> becomes the new goal \<open>\<And>y. A y \<Longrightarrow> P y\<close>, and \<^theory_text>\<open>show ?case\<close> fixes \<open>y\<close>
  and assumes \<open>A y\<close> again\<close>.
\<close>

subsection \<open>Comparison with the built-in \<^theory_text>\<open>show \<dots> when\<close>\<close>

text \<open>The built-in \<^theory_text>\<open>show \<dots> when\<close> also leaves a stronger statement as a new
  goal, but restates the conclusion and does not rebind the abbreviation.\<close>

lemma demo_show_when:
  assumes "(n :: nat) > 10"
  shows "n > 4" and \<open>n > 3\<close>
proof -
  show "n > 4" when \<open>n > 5\<close>
    using that
    by simp

  show "n > 5"
    using assms
    by fastforce
next
  show \<open>n > 3\<close> using assms
    by simp
qed

subsection \<open>A worked induction proof\<close>

text \<open>First without \<^theory_text>\<open>suffices\<close>: the statement mentions the obtained \<open>y\<close>,
  so \<^theory_text>\<open>show ?case when\<close> cannot be used directly and the reduction has to be
  spelled out via an explicitly quantified statement.\<close>

lemma finite_imageD_no_suffices:
  assumes "finite (f ` A)" and "inj_on f A"
  shows "finite A"
  using assms
proof (induct "f ` A" arbitrary: A)
  case empty

  then show ?case by simp
next
  case (insert x B)

  then have B_A: "insert x B = f ` A"
    by simp

  show ?case when "\<exists>y. x = f y  \<and> y \<in> A \<and> finite (A - {y})"
    using that
    by auto

  show "\<exists>y. x = f y  \<and> y \<in> A \<and> finite (A - {y})"
  proof -

    from B_A obtain y where "x = f y" and "y \<in> A"
    by blast

    from B_A \<open>x \<notin> B\<close> have "B = f ` A - {x}"
      by blast

    with B_A \<open>x \<notin> B\<close> \<open>x = f y\<close> \<open>inj_on f A\<close> \<open>y \<in> A\<close> have "B = f ` (A - {y})"
      by (simp add: inj_on_image_set_diff)

    moreover from \<open>inj_on f A\<close> have "inj_on f (A - {y})"
      by (rule inj_on_diff)

    ultimately show ?thesis
      using insert.hyps
      by blast
  qed
qed

text \<open>With \<^theory_text>\<open>suffices\<close>, the statement may mention the obtained \<open>y\<close>
  directly; the generalization happens automatically.\<close>

lemma finite_imageD_suffices:
  assumes "finite (f ` A)" and "inj_on f A"
  shows "finite A"
  using assms
proof (induct "f ` A" arbitrary: A)
  case empty

  then show ?case by simp
next
  case (insert x B)

  then have B_A: "insert x B = f ` A"
    by simp

  then obtain y where "x = f y" and "y \<in> A"
    by blast

  suffices "finite (A - {y})"
    by simp

  show ?case \<comment> \<open>now denotes \<open>finite (A - {y})\<close>, for a fresh \<open>y\<close> with
    \<open>x = f y\<close> and \<open>y \<in> A\<close> assumed again\<close>
  proof (rule insert.hyps)

    from B_A \<open>x \<notin> B\<close> have "B = f ` A - {x}"
      by blast

    with B_A \<open>x \<notin> B\<close> \<open>x = f y\<close> \<open>inj_on f A\<close> \<open>y \<in> A\<close> show "B = f ` (A - {y})"
      by (simp add: inj_on_image_set_diff)

   from \<open>inj_on f A\<close> show "inj_on f (A - {y})"
      by (rule inj_on_diff)
  qed
qed

end
