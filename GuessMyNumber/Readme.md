# Guess My Number

Let's implement a classic "Guess My Number" game. The program generates a random number between 0-99 and prompts if your guess is correct, too high, or too low.

### Generate the secret number

```lean
import Std.Data

-- Generate a "random" number in [0, 99]
-- It's not actually random. We'll talk about it later.
def GetSecret : IO Nat :=
  IO.rand 0 99
```

First, `IO.rand` is not actually a random number. It's a pseudo random number generator **with the same seed every time**! But that's not important for this discussios. Let's assume it returns a number randomly.

For those who know `IO Monad`, you can skip the rest of the article and just understand the code by reading it.

For those who doesn't:

What is `IO Nat`? You can simply imagine that it's an integer inside a box called `IO`. There are plenty of good tutorials explaining `IO Monad`. The analogy should be suffice for our purpose.

--------------------------------------------------------------------------------

```lean
partial def guess (secret : Nat) (prompt : String) : IO Unit := do
  IO.println prompt
  let stdin := (←IO.getStdin)
  let str   := (←stdin.getLine)

  -- handles eof.
  if str.length == 0 then
    return

  let num   := str.trim.toNat?
  match num with
  | none   => guess secret "Please enter a valid number"
  | some i =>
    match (Ord.compare i secret) with
    | Ordering.eq => IO.println "It's correct!"
    | Ordering.lt => guess secret "Too small"
    | Ordering.gt => guess secret "Too large"
```

Lean is a pure functional programming language. But with the magic `do` notation, it allows us to think imperatively, see <https://leanprover.github.io/lean4/doc/do.html> for details. In short, don't worry. Just as that when you first learn C++, you don't worry about how `cin` works. It might take some time before you really understand this. But, there's an easy explanation. Remember that the explanation is not very accurate, or even wrong! But it helps to quickly understand the code.

`IO.println prompt`. `prompt` is a string. This line just prints the string to the standard out (the screen).

`let` notation creates a local variable. It can be shadowed but not reassigned. Use `mut` to allow reassignment. You can specify the type manually, or let Lean deduct the type if it is omitted.

```lean
let     x : List Nat := [1,2,3]       -- full form
let     x            := [1,2,3].tail! -- type omitted.
--      x            := x.tail!       -- 'x' cannot be reassigned
let mut y            := [1,2,3]       -- mut
        y            := y.tail!       -- re-assign
```

These 2 lines just read a line from user input (stdin).

```lean
let stdin := (←IO.getStdin)
let str   := (←stdin.getLine)
```

The `←` notation is just to get things out of the box. The type of `stdin.getLine` is `IO String`, and `str` is of type `String`.

What if user hit `^D` (ctrl-D)? Simply add `IO.println str` and see what happens. It turns out that `stdin.getLine` just gives empty string every time. Just check if the string length is zero.

```lean
if str.length == 0 then -- handles eof.
  return
```

The `return` is not returning from the function. It just exits the `do` block. In this example, they are the same. But it's important to remember that it's different than it in an imperative language. e.g. If you want to fake some user input (that is `IO String`), you could use `return` as in

```lean
let fake : IO String := return "123"
```

Now we get the string, we trim the newline character ('\n') before converting to Nat.
by the way, `str.trim` is just equivalent to `String.trim str`.

```
let num   := str.trim.toNat?
```

`num` is of type `Option Nat`. `Option α` is an inductive type that has 2 constructors, as you can see from its definition:

```lean
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

It means, an `Option α` is either a `none`, or `some val` where `val` is of type α.

We can then use pattern matching to find out which case it is.

```lean
  match num with
  | none   => guess secret "Please enter a valid number"
  | some i =>
    match (Ord.compare i secret) with
    | Ordering.eq => IO.println "It's correct!"
    | Ordering.lt => guess secret "Too small"
    | Ordering.gt => guess secret "Too large"
```

Similarly, we use pattern matching to deal with the result of `Ord.compare`.

--------------------------------------------------------------------------------

```lean
partial def main : IO Unit := do
  let secret := (←GetSecret)
  guess secret "Please enter a number"
```

`partial` means that the function may not terminate. It's borrowed from the mathematics world, where a partial function `f : X ⇀ Y` is only defined on a subset of `X`, meaning that the result may be undefined for some input value of `X`. Here, undefined just means it could never terminate.

The counterpart is called total function. Every function is by default garaunteed to terminate. Usually Lean will figure out why the function terminates, but in case it doesn't, Lean will refuse the function and ask you for hints.

```lean
def f (a : Nat) : Nat := f (a + 1) -- fail to show termination for f, use `termination_by` to specify a well-founded relation
```

--------------------------------------------------------------------------------

Enjoy the game. You only need to guess once.
