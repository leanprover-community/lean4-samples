import MyNat.Definition
/-!
# Tactic <;>

`tac1 <;> tac2` runs `tac1` on the main goal and `tac2` on each produced goal,
concatenating all goals produced by `tac2`.

`tac1 <;> (tac2; tac3)` runs `tac1` on the main goal and
then runs `tac2` followed by `tac3` on every subgoal produced by `tac1`.

-/