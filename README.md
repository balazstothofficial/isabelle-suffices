# isabelle-playground

## The `suffices` command

[Suffices.thy](Suffices.thy) defines a new Isar command for one step of *backward*
reasoning: state something stronger, justify in place that it implies the current
goal, and then prove the stronger statement — instead of proving it first and
deriving the goal at the very end.

```isabelle
lemma
  fixes n :: nat
  assumes "n > 10"
  shows "n > 2"
proof -
  suffices "n > 5"          ― ‹it is enough to show n > 5 ...›
    by simp                 ― ‹... since n > 5 ⟹ n > 2›
  show ?thesis              ― ‹?thesis now denotes n > 5›
    using assms by simp
qed
```

`suffices` finds the current goal automatically (whatever `?thesis`/`?case`
denotes, or a pending subgoal directly) and rebinds that abbreviation to the new
statement, so consecutive `suffices` steps compose. The statement syntax is that
of `have`/`show`: several statements (`and`/juxtaposed), names, `(is ...)`
patterns, and `if`/`for` generalization.

It is closely related to the built-in `show C when "P"` — both leave `P` as a new
subgoal of the enclosing goal after proving `P ⟹ C` — but `suffices` does not
restate the conclusion `C`, rebinds the goal abbreviation, and accepts statements
that `when` must reject because they mention `obtain`ed variables.

Statements may mention `obtain`ed variables — the new goal is then generalized
over them together with their characterizing assumptions, and the proof simply
continues with fresh copies under the same names:

```isabelle
obtain k where "n = 4 * k" using assms by blast
suffices "n = 2 * (2 * k)"
  by blast
show ?thesis using ‹n = 4 * k› by simp
```

See [Suffices_Example.thy](Suffices_Example.thy) for a worked induction proof and
[Suffices_Tests.thy](Suffices_Tests.thy) for all supported forms.

## Building

```sh
isabelle build -d . Suffices_Playground
```
