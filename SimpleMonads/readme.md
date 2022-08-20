# Simple Monads in Lean

Lean is a pure Functional programming language.  This means all inputs and outputs must be described
in the function arguments and return values and no other side effects are allowed to happen and this
is enforced by the Lean compiler.  This allows the Lean Compiler to do some very interesting things,
like proofs.

Pure functions are easy to test, they are completely predictable, less prone to bugs and compose
incredibly well into larger functions. The following is an example of a pure function:

```lean
def divide (x: Float) (y: Float) : Float :=
  x / y
```

This function takes two floating point numbers and returns the division `x` divided by `y`:

```lean
#eval divide 6 2    -- 3.000000
```

But, real world programs usually need to have some side effects, like reading and writing files,
terminal IO, networking, logging, exception handling, and reading or writing some sort of global
settings, or state.  Monads can solve this problem, and they can be used for other useful things
like metaprogramming.

More generally monads are useful when you want to introduce a new concept to your programs without
messing up the clarity, composability and maintainability of your pure functions.

For example, suppose your Lean program must not allow divide by zero because that might cause
your variables to get tainted with `Float.inf` and let's pretend that for your particular application
that would be a huge problem (there are many real world applications where this is the case).

But you don't want to stop using the `Float` because that would then mean you lose the nice benefits
of the system provided `Float` type. So how can you get the compiler to ensure that `Float.inf`
never happens in your program?

There is a `Monad` defined in lean that adds exception handling behavior as an add on feature and
the way you do it is to add to your return type information about the exception handling behavior
your function might have:

```lean
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divide 5 0  -- Except.error "can't divide by zero"
```

All these code snippets are included in [Monads.lean](Monads.lean)

Here the `throw` function is available because our return type includes `ExceptT`. So `throw` is not
available everywhere like it is in most imperative programming languages.  You have to declare your
function can throw by including the `ExceptT` type in your result type.  This creates a function
that might return an error of type String or it might return a value of type Float in the non-error
case.

Once your function is monadic you also need to use the `pure` constructor
of the `ExceptT` monad to convert the pure non-monadic value `x / y` into the `Except` object.

If the word `pure` here is confusing to you, you could define a helper function called `ok` that
maps to `pure` and now your code reads more nicely, you can see a `throw` result and an `ok` result.

```lean
def ok {ε : Type u} (a : α) : Except ε α := pure a

/- simple exception handling monad -/
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    ok (x / y)
```

Now this return typing would get tedious if you had to include it everywhere that you call this
function, however, Lean type inference can clean this up. For example, you can define a test
function can calls the `divide` function and you don't need to say anything here about the fact that
it might throw an error, because that is inferred:

```lean
def test :=
  divide 5 0
```

The Lean compiler propagates the type information for you:
```lean
#check test     -- ExceptT String Id Float
```

And now we can run this test and get the expected exception:

```lean
#eval test      -- Except.error "can't divide by zero"
```

But with all good exception handling you also want to be able to catch exceptions so your program
can continue on, which you can do like this:

```lean
def testCatch :=
    try
      let r ← divide 8 0  -- 'r' is type Float
      return toString r
    catch e =>
      return s!"Caught exception: {e}"
```

Note that the type inferred by Lean for this function is `ExceptT String Id String` so the
`ExceptT String Id Float` return type from the divide has been transformed.
The ok type changed from `Float` to `String`. This is called "monad transformation" and is
what the T stands for in `ExceptT`.  The secret to Lean is how easily it does monad transformation
for you in most cases.  Notice here you didn't have to do any extra work for the compiler to figure
out the transform you were trying to do.

You can now see the try/catch working in this eval:

```lean
#eval testCatch -- Except.ok "Caught exception: can't divide by zero"
```

Notice the `Caught exception:` wrapped message is returned, and that it is returned as an
`Except.ok` value, meaning `testCatch` eliminated the error result as expected.

So we've interleaved a new concept into our functions (exception handling) and the compiler is still
able to type check everything just as well as it does for pure functions and it's been able to infer
some things along the way to make it even easier to manage.

## Under the covers

So what really just happened under the covers? Exceptions start with this inductive type:

```lean
inductive Except (ε : Type u) (α : Type v) where
  | error : ε → Except ε α
  | ok    : α → Except ε α
```

This is similar to the `Sum` type shown in the
[Theorem Proving in Lean chapter on Inductive Types](https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html#constructors-with-arguments).

It can represent an object that contains either an `error` or and `ok` value where the error can be
any type `ε` and the `ok` value can be any type `α`.

You can use `Except` by filling in those type parameters like this: `Except String Float`.
This creates a new Type, if you like, that represents an Except object that that has a string
in the error case or a floating point value in the ok case.

If you partially construct an `Except ε` you have something of type `Type → Type` which
is a type transformer, for example, it takes type `Float` and returns type `Except String Float`.
So it transforms types. Monads in Lean are also type transformers, and you can turn `Except ε`
into an official `Monad` by declaring a Monad type instance:

```lean
instance : Monad (Except ε) where
  pure := Except.pure
  bind := Except.bind
  map  := Except.map
```

Where `Except` has defined some helper functions that implement pure, bind and map.
The `ExceptT` function uses a monad `m` to transform the type `Except ε α`:

```lean
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)
```

This takes an error type `ε`, a monad `m`, and the ok type `α` and uses the monad `m` to transform
the type `Except ε α` to create a new return type, whatever type is defined by the monad we choose
to use here.  The `T` in `ExceptT` is short for "transformer", so `ExceptT` is a monad based type
transformer.

| side note |
| ----- |
| Now remember that in Lean, any function `f (x) (y) (z)` can be turned into compositional subfunctions, so `f x y` is a function that returns a function that takes a `z` and `f x` is a function that returns a function that takes `y z` and so on.

Using this we have this:
- `ExceptT String` is a monad transformer.
- `ExceptT String Id` is a monad
- `ExceptT String Id Float` is a monadic action in the monad `ExceptT String Id` which produces a Float
when you call the `run` method on that action.

Note that `ExceptT String Id` is a monad because of another instance:
```lean
instance {ε : Type u} {m : Type u → Type v}  [Monad m] : Monad (ExceptT ε m) where
  pure := ExceptT.pure
  bind := ExceptT.bind
  map  := ExceptT.map
```

Yes `ExceptT` also provides a `run` method as follows:
```lean
def ExceptT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x
```

Now the `#eval` command can implicitly call `run` for you in some cases, so when we did `#eval test`
we were really doing this:

```lean
#eval test.run
```

You could think of this as invoke the test function, then run the monadic action returned so you can
see the Float answer (or Except.error).

Now the `divide` function is using the `Id` monad which is the identity transform so the return type
in this case will be unchanged `Except String Float`.  This `Id` monad might seem a bit weird right
now, but it is a placeholder that will allow us to chain monads, which we will do later.

So the `divide` function can return an Exception object containing an error of type `String` or an ok
result of type Float - which is exactly what we wanted.

The divide function also used this `pure` function which is defined as :

```lean
namespace Except
def pure {ε : Type u} (a : α) : Except ε α :=
  Except.ok a
```

So in the case of `Except String Float` the implicit error type `ε` is `String` and the pure value
is a `Float` and the `Except.pure` implementation then simply uses the `Except.ok` constructor
passing the pure value to be wrapped in an `Except` object.  So `pure (x / y)` converts the pure value
`x / y` into something that matches the return type `Except String Float`.

All this is built on the `Monad` type class which is defined as follows:

```lean
class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
```

![Monad](./assets/monads.png)

Remember that type classes in Lean allow the compiler to do type inference using the declared
instances.  So the instance `Monad (Except ε)` allows the compiler to invoke `Except.pure` when we
call the `pure` method, and `Except.bind` if we call `bind` and so on.

Notice the `instance : Monad (Except ε)` doesn't define the ok type `(α : Type v)`. If you
`#check (Except String)` you will find you get a function that operates on types, in other words a monad:
```lean
Except String : Type u_1 → Type (max 0 u_1)
```

Notice this matches the inputs to the Monad class: `(m : Type u → Type v)` and is why you can think
of a Monad as something that transforms types.

The next method to consider is the Monad `bind` method which is defined on the `Bind` type class as:

```lean
class Bind (m : Type u → Type v) where
  /-- If `x : m α` and `f : α → m β`, then `x >>= f : m β` represents the
  result of executing `x` to get a value of type `α` and then passing it to `f`. -/
  bind : {α β : Type u} → m α → (α → m β) → m β
```

Here you can see that `bind` is using a function to transform the return type from `m α` to `m β`
and is specialized in the case of the `Except.bind` as follows:

```lean
namespace Except
@[inline] protected def bind (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
  match ma with
  | Except.error err => Except.error err
  | Except.ok v      => f v
```

So this bind function can be used to transform the type `Except String Float` to `Except String String`.
First we need a function that takes `Float → Except String String` and it then unwraps the
given `Except String Float` into its `error` and `ok` cases, passing the error through unchanged as
`Except.error err` and using the function `f` to transform the `ok` variable `v` into a string by
applying `f v` which returns a new type `Except String String`.

This transformation happened automatically in the `testCatch` function earlier because we used the
`do` notation which is a powerful tool that can chain monad actions finding and applying the right
bind operations automatically when needed. In the `testCatch` function the following line of code
shows this in action:

```lean
    return toString r -- ExceptT String Id String
```
Here the `toString` function was composed into something that contructs an `Except.ok String`
result.  So this monad type inference and composition of binding operations is pretty powerful.

Now you might be wondering why `testCatch` doesn't have return type `String`? Lean does this as a
convenience since you could have a rethrow in or after the catch block. If you really want to stop
the `ExceptT` type from bubbling up you can do this:

```lean
def testUnwrap : String := Id.run do
    let r := divide 8 0 -- r is type ExceptT String Id Float = Except String Float
    match r with
    | .ok a => toString a -- 'a' is type Float
    | .error e => s!"Caught exception: {e}"

#check testUnwrap -- String
#eval testUnwrap -- "Caught exception: can't divide by zero"
```

Alternatively you could solve this using coercions, although that is not always recommended.

```lean
instance : Coe (ExceptT α Id α) α where
  coe a := match a with
    | .ok v => v
    | .error v => v

def testCoerce : String :=
  let act : ExceptT String Id String := do
    let r ← divide 8 0
    return r.toString
  act

#check testCoerce -- String
#eval testCoerce  -- "can't divide by zero"
```

You can also use `bind` manually if you want to control how it works which we'll see below.

## Monad Composition

This is great, but how do you add another dimension to your program using monads? Well it turns out
in Lean monads compose very nicely, their side effects can be chained.

Suppose now you want to add some logging to your program so you know how many times divide succeeds
without throwing an exception.  Logging is very useful in large complex programs to figure out what
is really happening.

You have probably already used the IO monad to do terminal IO like `IO.println "Hello, world!"` but
that's not the kind of logging we want here. Sometimes you need something more structured, and more
light weight, and easier to consume programmatically.  So let's create a counter that is simply
incremented every time divide succeeds and pass that "logging state" into our program so you can
then also read that state when the program is finished.

There is a monad already defined for this kind of stateful side effect, it is called `StateT`:

```lean
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
```
which has some additional functions available through `MonadStateOf`:
```
instance [Monad m] : MonadStateOf σ (StateT σ m) where
  get       := StateT.get
  set       := StateT.set
  modifyGet := StateT.modifyGet
```

Tee `get` function can read the state, the `set` function updates it, and
`modifyGet` does a read and an update.

If your "context state" is a simple natural number - the count of the number of times divide
succeeds -- then you could create a divide function that logs this state information as follows:

```lean
def divideLog (x: Float ) (y: Float): StateT Nat Id Float :=
  if y == 0 then do
    return 0
  else do
    modify fun s => s + 1
    return x / y
```

But how does adding a return type of `StateT` allow stateful "inputs" to be passed to the
`divideLog` function?  How can a return type add an input? You can use "currying" again check the reduced type:

```lean
#check divideLog              -- Float → Float → StateT Nat Id Float
#reduce StateT Nat Id Float   -- Nat → Float × Nat
```

So effectively StateT has changed our function into:

```
Float → Float → Nat → Float × Nat
```

So `StateT` has turned the return type into a function that takes a natural number as input and
returns the updated state in the pair `Float × Nat`. So it has essentially then added an input
parameter to our `divideLog` function.  This parameter can be accessed by the `StateT`
interface `get`, and `modifyGet`. `modify` is a helper that makes it easier to use `modifyGet`.

The following 3 ways of calling this function are equivalent:
```lean
#eval divideLog 8 4 0         -- (2.000000, 1)
#eval (divideLog 8 4).run 0   -- (2.000000, 1)
#eval divideLog 8 4 |>.run 0  -- (2.000000, 1)
```

The first way of simply tacking on the state argument is not recommended because it makes your
code hard to maintain if the divideLog parameters change or the StateT monad is changed and so on.
it is better to use the `run` method explicitly which you can do using parentheses, but if you
have lots of monads in your chain the right associative operator '|>' is more convenient as it
drops the need for parentheses.

An added benefit of calling `run` explicitly is that the Lean type checker will always ensure for
you that the result of `divideLog 8 4` is a type that has some `run` method and so on, if this is
not the case it will highlight the right section of your code instead of giving a confusing big
error on your entire application that contains some weird monad stack mess. So this is the
recommended pattern.

You can call this function in a test function, passing in the state on each call, and storing the
updates in a mutable state variable and with the nested for loops this will divide by zero exactly
10 times, which means the result of successful divides should be 90:

```lean
def testDivideLog := do
  let mut state := 0
  for x in [0:10] do
    for y in [0:10] do
      let r ← divideLog x.toFloat y.toFloat |>.run state
      state := r.2
  state

#eval testDivideLog -- 90
```

Great, a completely different example of adding an orthogonal dimension to our code (logging).  But
now what if we want both logging and exception handling? Well you can chain `StateT`, and `ExceptT`
-- this is why the `*T` monad transformers take a monad as input.  We were passing `Id` before, but
now we can pass the monad `ExceptT String Id` instead resulting in the return type
`StateT Nat (ExceptT String Id) Float`! Phew, that's a mouth full.  Lean allows very sophisticated type
construction.

So this means `StateT` will transform `Except String Float` into some new return type, in this case
it will become `Nat → Except String (Float × Nat)` because we need the to be able to pass in the state
and get back the modified state, so it returns the division result, and the updated state as a tuple.

You can now use `bind` manually to chain the 2 monadic functions, in this case (`modify` from StateT
and `pure` from `ExceptT`) and the `bind` function on StateT is defined as:

```lean
@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do let (a, s) ← x s; f a s
```

So it returns the pair `(a, s)` which means in this case `β` is inferred to be the
type `Float × Nat`.  Here's the combined monadic function using a manual bind:

```lean
def divideIt (x:Float) (y:Float) : StateT Nat (ExceptT String Id) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) (fun _ => pure (x / y))

#check divideIt -- Float → Float → StateT Nat (ExceptT String Id) Float
```

```lean
#eval divideIt 5 2 |>.run 0 -- Except.ok (5.000000, 1)
```

The `run` parameter passed here is the initial value of the `StateT Nat` being passed in. The function
incremented this state and returned it as the second member of the pair `(5.000000, 1)`.

You can test this new composite `divideIt` function in a very similar way to `testDivideLog` and you
can add a try/catch so the test doesn't stop when it hits a divide by zero:

```lean
def testIt := do
  let mut log := 0
  for x in [0:10] do
    for y in [0:10] do
      try
        let r ← divideIt x.toFloat y.toFloat |>.run log
        log := r.2
      catch _  =>
        ok ()
  ok log

#eval testIt -- 90
```

Notice here the extracted value in `r` is the pair `Float × Nat` so `r.2` then is the updated
`state` which we want to keep around so we get the running tally of the number of times we did a
successful divide and we get the same result: 90 good divides.

Ok, now to bring it all together, you don't need to use `bind` manually like this because the
`do` notation can chain monadic actions using bind automatically, so you can rewrite the divideIt
function as:

```lean
def divideDo (x:Float) (y:Float) : (StateT Nat (ExceptT String Id)) Float := do
  if y == 0 then
    throw "can't divide by zero"
  else
    modify fun s => s + 1
    pure (x / y)

#eval divideDo 5 2 |>.run 0 -- Except.ok (2.500000, 1)
```

So here the do Notation DSL generated the code `bind (modify fun s => s + 1) (fun _ => pure (x / y))`
for you.  Pretty neat.  Note that we used the do notation in `divideLog` to do some chaining also.

So an imperative program can be modelled in a functional language as a chain of monadic actions
and this is a major innovation in the Lean language.

## Add one more for fun!

`ReaderT` is like `StateT` but it is read only, so it is ideal for "context" or "global state". We
can use it to pass around our command line arguments so different parts of our program can behave
differently as a result of those arguments.  `ReaderT` provides the additional function `read`
to access that read only context.

Let's first see the manual binding so you get a better idea of how they compose:

```lean
def divideWithArgs (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  bind (modify fun s => s + 1) fun _ =>
    bind (get) fun s =>
      bind (read) fun args =>
        if (s > 10 && args.contains "--limit") then
          throw "too many divides"
        else if y == 0 then
          throw "can't divide by zero"
        else
          pure (x / y)
/-
List String → Nat → Except String (Float × Nat)
-/
#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float

#eval divideWithArgs 5 2 |>.run [] |>.run 0 -- Except.ok (2.500000, 1)
#eval divideWithArgs 5 0 |>.run [] |>.run 0 -- Except.error "can't divide by zero"
#eval divideWithArgs 5 2 |>.run ["--limit"] |>.run 10 -- Except.error "too many divides"
```

Notice that because we have added 2 monads now, `ReaderT` and `StateT` we want to see 2 `run` method
calls.

Fortunately, the `do` Notation cleans this up very nicely:

```lean
def divideWithArgsDo (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float := do
  modify fun s => s + 1
  let s ← get
  let args ← read
  if (s > 10 && args.contains "--limit") then
    throw "too many divides"
  else if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divideWithArgsDo 5 2 |>.run [] |>.run 0 -- Except.ok (2.500000, 1)
#eval divideWithArgsDo 5 0 |>.run [] |>.run 0 -- Except.error "can't divide by zero"
#eval divideWithArgsDo 5 2 |>.run["--limit"] |>.run 10 -- Except.error "too many divides"
```

Oooh, isn't that loverly.  You can even prove that these functions are equivalent:

```lean
example : divideWithArgs x y = divideWithArgsDo x y := by
  simp[divideWithArgs, divideWithArgsDo]    -- Goals accomplished 🎉
```

## Monad Lifting

An important part of any program is functional decomposition, breaking large functions up into
smaller ones. When you do that you don't always want the smaller functions to have the big complex
return types of the outer function.  Let's take a look at an example.  Remember our first divide
function that throws on divide by zero?

```lean
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)
```

Well we can reuse this smaller function in our `divideWithArgsDo` with some refactoring like this:

```lean
def divideRefactored (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float := do
  modify fun s => s + 1
  let s ← get
  let args ← read
  if (s > 10 && args.contains "--limit") then
    throw "too many divides"
  else
    divide x y

#eval divideRefactored 5 2 |>.run [] |>.run 0 -- Except.ok (2.500000, 1)
#eval divideRefactored 5 0 |>.run [] |>.run 0 -- Except.error "can't divide by zero"
#eval divideRefactored 5 2 |>.run ["--limit"] |>.run 10 -- Except.error "too many divides"
```

Very cool - but some magic happened here. The smaller `divide` function has a different return type
`ExceptT String Id Float` yet you returned it's value no problem and the compiler turned that into
`ReaderT (List String) (StateT Nat (ExceptT String Id)) Float` for you, somehow.

This is called "monad lifting" and is another secret sauce that Lean provides in order to make
monads super easy to use.  You could imagine manual monad lifting would be very tedious indeed. You
can see this in action with the following test:

```lean
def lift1 (x : ExceptT String Id Float) : (StateT Nat (ExceptT String Id)) Float :=
  x

#eval lift1 (divide 5 1) |>.run 3 -- Except.ok (5.000000, 3)
```

You can see this is lifted to `StateT` because we were able to then `.run` that with initial state `3`
and the StateT monad converted that into the pair `(5.000000, 3)`.  `lift1` didn't modify the state
so it came back to us unmodified.  Now we need a second lift to ReaderT:

```lean
def lift2 (x : StateT Nat (ExceptT String Id) Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  x

#eval lift2 (lift1 (divide 5 1)) |>.run ["discarded", "state"] |>.run 4 -- Except.ok (5.000000, 4)
```

So you can see how the lifts compose nicely, we can pass in the `ReaderT` args, and the initial
state, and we get back the divide result and the returned state. In this case `lift2` does nothing
with the `ReaderT` args so they are discarded.

So what Lean did for you in `divideRefactored` is a transitive closure of monad lifting operations!

## Lifting Deep Dive

Let's see how that works.  If you `#print lift1` you will see it is implemented as `fun x => liftM x` and
`liftM` is an abbreviation for `monadLift` from `MonadLiftT`.

```lean
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  /-- Lifts a value from monad `m` into monad `n`. -/
  monadLift : {α : Type u} → m α → n α
```

The `T` in `MonadLiftT` stands for "transitive" it is able to transitively lift monadic computations
using `MonadLift` which is a function for lifting a computation from an inner `Monad` to an
outer `Monad`.

So now we can check all the `MonadLift` instances defined in Lean, and in our case we will be using:

```lean
instance : MonadLift m (StateT σ m)  -- to lift to StateT
instance : MonadLift m (ReaderT ρ m) -- to lift to ReaderT
```

These instances override the `lift` function for these types, showing the compiler how to generate
that code.  Let's see how that works for StateT:

```lean
@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)
```

So this is very generic, given some implicit type `α` and a monad `m` that acts on `α` it is able to
generate the return type `StateT σ m α` by returning a function that takes some state `s` from which
it can then create the pair `(a, s)` where `a` is the result of applying the monad `m α`.  And this
is what we saw, the state `3` passed in resulted in a pair coming back out as `(5.000000, 3)`.  It
is not inventing the state, it is lifting that state so it is an input and an output resulting in a
valid `StateT Nat (ExceptT String Id)`.

Similarly, for `ReaderT` we find:

```lean
instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x
```
This one is a bit simpler, remember `ReaderT` is about passing in some read-only state, but to lift
from something that does not know about `ReaderT` then the thing we are calling obviously doesn't
care about this read only state, so we can throw it away using the underscore `_` and simply call
the inner function, which is what we saw with this eval:

```lean
#eval lift2 (lift1 (divide 5 1)) |>.run ["discarded", "state"] |>.run 4 -- Except.ok (5.000000, 4)
```

The ReaderT state here is `["discarded", "state"]` and it is thrown away when calling `lift1`
because `lift1` doesn't know (or care) about `ReaderT`.

So looking at `divideRefactored` again, you get an appreciation for what is going on under the
covers to make that monadic code nice and composable, both on the way in with monads like `ReaderT`
and `StateT` adding additional input parameters, and on the way out with automatic transitive monad
lifting. Lift happens very often in Lean.

## Common Patterns

Sometimes you want your `StateT` state to be more interesting, like this `Config` structure:

```lean
structure Config where
  x : Nat
  y : Nat
  deriving Repr
```

And in real Lean programs people often use abbreviations to come up with a nice name for
their long monadic types:

```lean
abbrev CoolM := StateT Config (ExceptT Nat Id)
```

Now you can use this state and update it like this:

```lean
def doSomethingCool : CoolM Nat :=do
  let s ← get             -- read the state Config structure
  set {s with x := 10}    -- update the state modifying the x component
  pure 0
```
Here we are using [record update syntax](https://leanprover.github.io/theorem_proving_in_lean4/structures_and_records.html#objects)
`{s with x := 10}` which means start with structure `s` and update just the `x` component.

Now you can see clean type information:
```lean
#check doSomethingCool -- CoolM Nat
```

And you can see what CoolM is using:
```
#synth Monad CoolM     -- StateT.instMonadStateT
```

But you can also see what it really maps to:
```lean
#reduce CoolM Nat      -- Config → Except Nat (Nat × Config)
```

And you can call the function passing an initial Config and see the resulting
updated state:

```lean
#eval doSomethingCool |>.run {x := 0, y := 0} -- Except.ok (0, { x := 10, y := 0 })
```

Abbreviations like this are used heavily in the Lean code base.  Here's some examples:

```lean
#reduce CliM Unit -- in Lake
-- ArgList → LakeOptions → IO.RealWorld → EStateM.Result UInt32 PUnit (Except CliError ((PUnit × List String) × LakeOptions))

#reduce IO Unit -- the type for main
-- IO.RealWorld → EStateM.Result IO.Error PUnit PUnit
```

## Add your own Custom Lifting

You can now build the sample app with `lake build` and try out this main function:

```lean
def main (args: List String): IO Unit := do
  try
    let ret ← divideRefactored 5 0 |>.run args |>.run 10
    IO.println (toString ret)
  catch e =>
    IO.println e
```

This function would not normally compile saying:
```
typeclass instance problem is stuck, it is often due to metavariables
```
and you can see this error if you add this line before the `main` function:
```
set_option autoLift false
```

`divideRefactored` returns the big `ReaderT (List String) (StateT Nat (ExceptT String Id)) Float`
and the problem is that cannot be automatically transformed into the `main` return type of `IO Unit`
unless we give it some help.

The following custom `MonadLift` solves this problem:

```lean
def liftIO (t : ExceptT String Id α) : IO α := do
  match t with
  | .ok r => EStateM.Result.ok r
  | .error s => EStateM.Result.error s

instance : MonadLift (ExceptT String Id) IO where
  monadLift := liftIO
```

This instance makes it possible to lift the result of type `ExceptT String Id` into the type
required by main which is `IO Unit`. Fortunately this lift is relatively easy because IO is just an
alias for the `EStateM.Result` which is very similar to the `Except` object in that it also has an
`ok` or `error` state. The difference is `Result` has one more data member, which is a return code.

If we have an instance `MonadLiftT m n` that means there is a way to turn a computation that happens
inside of `m` into one that happens inside of `n` and (this is the key part) usually *without* the
instance itself creating any additional data that feeds into the computation. This means you can in
principle declare lifting instances from any monad to any other monad, it does not, however, mean that
you should do this in all cases.  You can get a report from Lean of how all this was done by
uncommenting the line `set_option trace.Meta.synthInstance true in` before main and moving the
cursor to the end of the first line after `do` and you will see a nice detailed report.

Now `lake build` will create a binary named `simpleMonads` which  you can run from the command line and
you can pass command line parameters as follows:

```
> simpleMonads
can't divide by zero

> simpleMonads --limit
too many divides
```

So we were able to influence the behavior of our program by passing some command line arguments and
some logging state, and we added some exception handling and we did it all in a purely functional
way using monads.  Then we also showed how monad chaining and lifing makes functional decomposition
nice and manageable.
