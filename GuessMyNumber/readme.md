# Guess My Number

Let's implement a classic "Guess My Number" game. The program generates a random number between 0-99 and prompts if your guess is correct, too high, or too low. For example:

```
I am thinking of a number between 0 and 99...
Please guess what it is: 50
Too large, try again: 25
Too small, try again: 35
Too small, try again: 43
Too large, try again: 37
Too small, try again: 41
Too large, try again: 39
Too small, try again: 40
It's correct! The number was 40!
```

### Generate the secret number

First we need to generate a random secret number.

```lean

-- Generate a "random" number in [0, 99]
def getSecret : IO Nat :=
  IO.rand 0 99
```

Here `getSecret` is a function that takes no arguments and returns `IO Nat`. `Nat` is a natural
number but what is `IO Nat`?  You can simply imagine that it's an integer inside a box called `IO`.
There are plenty of good tutorials explaining the `IO Monad` but this simple analogy should be
sufficient for our purpose.  How do you call this function?

```lean
let secret ← getSecret
```

The `←` notation is just to get things out of the IO box, so `secret` is of type `Nat`.

### Recursively prompt for the correct answer

We want to enable the user to keep guessing until they get it right and to do that we can use
recursion:

```lean
partial def guess (secret : Nat) (prompt : String) : IO Unit := do
  IO.println prompt
  let stdin ← IO.getStdin
  let mut str ← stdin.getLine
  str := str.trim

  if str.length == 0 then
    IO.println s!"Giving up? Well the number was {secret}"
    return

  match str.toNat? with
  | none   => guess secret "Please enter a valid number"
  | some i =>
    match compare i secret with
    | .eq => IO.println s!"It's correct! The number was {secret}!"
    | .lt => guess secret "Too small, try again?"
    | .gt => guess secret "Too large, try again?"
```

`partial` means that the function may not terminate. It's borrowed from the mathematics world, where
a partial function `f : X ⇀ Y` is only defined on a subset of `X`, meaning that the result may be
undefined for some input value of `X`. Here, undefined just means it could never terminate.

The counterpart is called total function. Every function is by default garaunteed to terminate.
Usually Lean will figure out why the function terminates, but in case it doesn't, Lean will refuse
the function and ask you for hints.

The `guess` function takes 2 parameters `(secret : Nat)` which is the secret as a natural number and
`(prompt : String)` which is the string to prompt the user with on each subsequent question.
It has a return type of `IO Unit` meaning it returns nothing but has a side effect on IO.RealWorld,
and as a result it could also return an error.

Lean is a pure functional programming language. But with the [`do`
notation](https://leanprover.github.io/lean4/doc/do.html), you can think more imperatively and write
a sequence of statements, like the `IO.println` and the `let` statements and so on. This is pretty
cool, the Lean syntax is itself extensible so you can create whatever DSL you want to make your
programs easier to write and `do` is just an example of that.

`IO.println prompt` prints the `prompt` string argument to the standard out (your terminal window).

`let` notation is like a local variable where that variable can be used in the following block. It
can be shadowed but not reassigned. Use `let mut` to allow reassignment. You can specify the type
manually, or let Lean deduct the type if it is omitted, here's some examples of that:

```lean
let     x : List Nat := [1,2,3]       -- full form
let     x            := [1,2,3].tail! -- type omitted.
        x            := x.tail!       -- error: 'x' cannot be reassigned
let mut y            := [1,2,3]       -- mut
        y            := y.tail!       -- re-assignment ok on mutables
```

Ok so we can use `let` to read a line from user input (stdin):

```lean
let stdin ← IO.getStdin
let str ← stdin.getLine
```

The `←` notation is just to get things out of the IO box. The type of `stdin.getLine` is `IO
String`, and `str` is of type `String`.

We made the `str` mutable so we can trim whitespace from it as follows:

```lean
str := str.trim
```

By the way, `str.trim` is equivalent to `String.trim str`. Now what if user hits `^D` (ctrl-D) (on
Linux) or just `ENTER`? It turns out that `stdin.getLine` just gives empty string. So we can just
check if the string length is zero and tease the user for giving up.

```lean
  if str.length == 0 then
    IO.println s!"Giving up? Well the number was {secret}"
    return
```

The `return` is not returning from the function. It just exits the `do` block. In this example, they
are the same. But it's important to remember that it's different than it in an imperative language.
e.g. If you want to fake some user input (that is `IO String`), you could use `return` as in:

```lean
let fake : IO String := return "123"
```

Now we are ready to try convert the string to a Natural number:

```
str.toNat?
```

This results in an object of type `Option Nat` because it might have a valid value or no value if
the string is not actually a number at all like `xyz`.  `Option α` is an inductive type that has 2
constructors, as you can see from its definition:

```lean
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

It means, an `Option α` is either a `none`, or `some val` where `val` is of type α, in our case Nat.
Finally we can then use pattern matching to find out which case it is:

```lean
  match str.toNat? with
  | none   => guess secret "Please enter a valid number"
  | some i =>
    match compare i secret with
    | .eq => IO.println "It's correct!"
    | .lt => guess secret "Too small, try again?"
    | .gt => guess secret "Too large, try again?"
```

Notice the pattern `some i` extracts the value into a new variable named `i`.
Then we can do a nested pattern match to handle the result of the `Ord.compare` function.
If the user is high or low we perform a recursive call to our guess function so it
will keep prompting until the user gets the answer right, or the program runs out of
stack space.  Lean programs usually have lots of stack space.

What is `Ord.compare`, well `Ord` is just a type class that is defined for comparing things.

```lean
class Ord (α : Type u) where
  compare : α → α → Ordering
```

Where the `compare` function returns an Ordering:

```
inductive Ordering where
  | lt | eq | gt
```

Then there are instances of this type class defined on things like Nat so we can compare
two natural numbers.

To finish up we need a main function:

```lean
def main : IO Unit := do
  IO.println "I am thinking of a number between 0 and 99..."
  let secret ← getSecret
  guess secret "Please guess what it is?"
```

To build and run the program type this in your terminal window:
```
lake build
```

Then find the program output and run it:

[Windows]
```
.\build\bin\guess
```

[Linux]
```
./build/bin/guess
```


Enjoy the game!
