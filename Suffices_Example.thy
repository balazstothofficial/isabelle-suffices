theory Suffices_Example
  imports Main Suffices
begin


section \<open>\<open>Suffices_Examples\<close> – Examples how to use \texttt{suffices}\<close>

text\<open>Suffices allows one step of backwards reasoning in Isar proofs.
It adds semantic information to those Isar proofs, where you show the ?thesis via first
showing something stronger, and then inferring the ?thesis by an easy justification. Instead of

have \<open>statement\<close>
proof-

  \<comment> \<open>long proof\<close>

qed
then show ?thesis \<comment> \<open>easy justification\<close>.
qed


we can now write:
suffices \<open>statement\<close>
  by easy_justification

show ?thesis \<comment> \<open>now denotes \<open>statement\<close>\<close>
proof-

\<comment> \<open>long proof\<close>

qed

Suffices works, by first making you prove that your specified statements really
imply the current goal, and then replacing the goal by your specified
statements, which are established later by a regular show. The current goal is
determined from the pending goal itself: whatever term abbreviation denotes it
(?thesis, ?case, ...) is found automatically and rebound to the new statement,
so consecutive suffices steps compose.

Unlike \<open>show \<dots> when \<dots>\<close>, the sufficient statements may mention variables
introduced by obtain: since such variables must not escape their scope, the
new goal is automatically generalized over them together with their
characterizing assumptions \<comment> \<open>so for obtain y where "A y", a statement P y
becomes the new goal "\<And>y. A y \<Longrightarrow> P y", and show ?case fixes y and assumes
A y again\<close>.

\<close>

subsection\<open>simple demos, showing how to syntactically use \texttt{suffices}\<close>

text\<open>Demo using suffices with multiple new (but here unnessecary) goals\<close>

lemma demo2:
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
