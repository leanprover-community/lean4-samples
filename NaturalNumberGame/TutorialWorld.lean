import TutorialWorld.Level1
import TutorialWorld.Level2
import TutorialWorld.Level3
import TutorialWorld.Level4

/-!
# The Natural Number Game, version 1.3.4

By Kevin Buzzard and Mohammad Pedramfar.

This is a version of the awesome [Natural Number
Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) that is designed to run in
Visual Studio Code with the Lean4 "extension".  The extension will install the Lean4 compiler and
language service for you so it is easy to setup - see the [Quick
Start](https://leanprover.github.io/lean4/doc/quickstart.html) for more information.

You must open the `NaturalNumberGame` in Visual Studio Code using `File/Open folder" in order
for it to function correctly.

## What is this game?

Welcome to the natural number game -- a part-book part-game which shows the power of induction.

In this game, you will not use the built in support for natural numbers in Lean because that would
be too easy.  You will start from scratch defining your own new type called `MyNat`. Your version of
the natural numbers will satisfy something called the principle of mathematical induction, and a
couple of other things too (Peano's axioms). Since you are starting from scratch, you will have to
prove all the basic theorems about your numbers like `x + y = y + x` and so on. This is your job.
You're going to prove mathematical theorems using the Lean theorem prover. In other words,
you're going to solve levels in a computer game.

You're going to prove these theorems using tactics. The introductory world, Tutorial World, will
take you through some of these tactics. During your proofs, your "goal" (i.e. what you're supposed
to be proving) will be displayed in the Visual Studio Code InfoView with a `⊢` symbol in front of
it. If the InfoView says "Goals accomplished 🎉", you have closed all the goals in the level
and can move on to the next level in the world you're in.

If you want to see the "Lean 3" version of this game go to
https://github.com/ImperialCollegeLondon/natural_number_game
which is also hosted in this [online version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).
-/