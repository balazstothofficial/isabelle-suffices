theory Suffices_Tests
  imports Suffices Main
begin

text \<open>Basic use: the abbreviation that denoted the goal (?thesis) is rebound
  to the sufficient statement.\<close>

lemma test_simple: "(1::nat) + 1 = 2"
proof -
  suffices "(2::nat) = 2"
    by simp
  show ?thesis
    by simp
qed

text \<open>The justification may be a structured proof block, and the new goal
  may be stated explicitly instead of via the rebound abbreviation.\<close>

lemma test_structured:
  assumes a: "A" shows "A \<or> B"
proof -

  suffices A
  proof -
    show "A \<or> B" if A using that ..
  qed

  show "A" by (rule a)
qed

text \<open>Consecutive suffices steps compose, since the abbreviation is rebound
  at every step.\<close>

lemma test_chain:
  fixes n :: nat
  assumes a: "n > 10"
  shows "n > 2"
proof -

  suffices "n > 5"
    by simp

  suffices "n > 8"
    by simp

  show ?thesis
    using a by simp
qed

text \<open>Multiple statements via \<open>and\<close>; the stale abbreviation is discarded, and
  a later suffices falls back to a bare pending subgoal.\<close>

lemma test_multi:
  fixes n :: nat
  assumes a: "n > 10"
  shows "n > 4 \<and> n > 3"
proof -

  suffices "n > 4" and "n > 3"
    by simp

  suffices "n > 5"
    by simp

  show "n > 5"
    using a
    by simp

  show "n > 3"
    using a
    by simp
qed

text \<open>Chained facts flow into the justification; named statements give a
  named premise there.\<close>

lemma test_chained_facts:
  fixes n :: nat
  assumes a: "n > 10"
  shows "n > 4"
proof -

  from a suffices stronger: "n > 5"
    using stronger
    by simp

  show ?thesis
    using a
    by simp
qed

text \<open>Statements may mention obtained variables: the new goal is generalized
  over them together with their characterizing assumptions, and the rebound
  abbreviation denotes the generalized statement.\<close>

lemma test_obtain_1:
  fixes n :: nat
  assumes "\<exists>k. n = 4 * k"
  shows "\<exists>m. n = 2 * m"
proof -
  obtain k where "n = 4 * k"
    using assms
    by blast

  suffices "n = 2 * (2 * k)"
    by blast

  show ?thesis \<comment> \<open>denotes \<open>n = 2 * (2 * k)\<close> for a fresh \<open>k\<close> with \<open>n = 4 * k\<close>\<close>
    using \<open>n = 4 * k\<close>
    by simp
qed

lemma test_obtain_2:
  assumes "\<exists>x. P x" "\<exists>y. Q y"
  shows "\<exists>x y. P x \<and> Q y"
proof -
  obtain x y where "P x" "Q y"
    using assms
    by presburger

  suffices "P x \<and> Q y"
    by auto

  show "P x \<and> Q y"
    using \<open>P x\<close> \<open>Q y\<close>
    by auto
qed

lemma test_obtain_3: 
  assumes "\<exists>x. P x" "\<exists>y. Q y"
  shows "\<exists>x y. P x \<and> Q y"
proof -
  obtain x y where P_Q: "P x" "Q y"
    using assms
    by presburger

  suffices "P x" and "Q y"
    by auto

  show "P x" and "Q y"
    using P_Q
    by auto
qed

lemma test_obtain_4:
  assumes "\<exists>x. P x" "\<exists>y. Q y"
  shows "\<exists>x y. P x \<and> Q y"
proof -
  obtain x y where P_Q: "P x" "Q y"
    using assms
    by presburger

  suffices "P x" "Q y"
    by auto

  show "P x" and "Q y" 
    using P_Q
    by auto
qed

lemma test_obtain_5:
  assumes "\<forall>z. \<exists>x. P x z" "\<forall>z. \<exists>y. Q y z"
  shows "\<forall>z. \<exists>x y. P x z \<and> Q y z"
proof (rule allI)
  fix z
  obtain x y where P_Q: "P x z" "Q y z"
    using assms
    by presburger

  then have P: "P x z"
    by presburger

  have Q: "Q y z"
    using P_Q(2) .

  suffices "P x z" "Q y z"
    by auto

  show "P x z" and "Q y z"
    using P Q
    by auto
qed

lemma test_obtain_bad:
  shows "\<exists>a :: bool. \<forall>b. a = b"
proof (rule exI, rule allI)
  fix b :: bool

  obtain a :: bool where a_b: "a = b"
    by presburger

  (* 
  Correctly does not work and prints a nice error.
  suffices "a = b"  
  *)
  oops

text \<open>Suffices works in nested proof blocks.\<close>

lemma test_nested: "(0::nat) < 4"
proof -
  have "(0::nat) < 3"
  proof -
    suffices "(0::nat) < 2"
      by simp
    show ?thesis
      by simp
  qed
  then show ?thesis
    by simp
qed

text \<open>The statement syntax is that of \<open>shows\<close>, including (is ...) patterns.\<close>

lemma test_is_pattern:
  fixes n :: nat
  assumes a: "n > 10"
  shows "n > 4"
proof -
  suffices "n > 5" (is ?goal)
    by simp
  show ?goal
    using a by simp
qed

text \<open>Statements may be generalized with \<open>if\<close> and \<open>for\<close>, as in \<open>have\<close>; the
  block continues with the variables fixed and the premises assumed.
  (\<open>when\<close> is rejected: its weak premises would have to remain as further
  goals, but the sufficient statements become goals as a whole anyway.)\<close>

lemma test_if_for: "\<forall>m \<in> {1, 2, 3}. m > (0::nat)"
proof -
  suffices "m > 0" if "m \<in> {1, 2, 3}" for m :: nat
    by auto

  show ?thesis \<comment> \<open>denotes \<open>m > 0\<close>, with \<open>m \<in> {1, 2, 3}\<close> assumed\<close>
    using \<open>m \<in> {1, 2, 3}\<close>
    by auto
qed

lemma test_if_for_2: "\<forall>m \<in> {1, 2, 3}. m > (0::nat)"
proof -
  suffices "m > 0" if m_in: "m \<in> {1, 2, 3}" for m :: nat
    by auto

  show ?thesis \<comment> \<open>denotes \<open>m > 0\<close>, with \<open>m \<in> {1, 2, 3}\<close> assumed\<close>
    using m_in
    by auto
qed

end
