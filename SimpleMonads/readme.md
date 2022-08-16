# Simple Monads in Lean

Lean is a pure Functional programming language.  This means all inputs and outputs must be described
in the function arguments and return types and no other side effects are allowed to happen and this
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

More generally monads are useful when you want to introduce a new concept to your programs
without messing up the clarity, composability and maintainability of your pure functions.

For example, suppose your Lean program must not allow divide by zero because that might cause
your variables to get tainted with `Float.inf` and let's pretend that for your particular application
that would be a huge problem (there are many real world applications where this is the case).

But you don't want to change the `Float` to something else that means `Float` but never `Float.inf`
because that would then mean you lose the nice benefits of the system provided `Float` type.
So how can you get the compiler to ensure that `Float.inf` never happens in your program?

There is a `Monad` defined in lean that adds exception handling behavior as an add on feature
and the way you do it is to add to your return type information about the exception handling
behavior your function might have:

```lean
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divide 5 0  -- Except.error "can't divide by zero"
```

Here the `throw` function is available because our return type includes `ExceptT`. So `throw` is not
available everywhere like it is in most imperative programming languages.  You have to declare your
function can throw by including the `ExceptT` type in your result type.  This creates a function
that might return an error of type String or it might return a value of type Float in the non-error
case.

Once your function is monadic you also need to use the `pure` constructor
of the `Except` monad to convert the floating point return value `x / y` into the `Except` monad.

This return typing would get tedious if you had to include it everywhere that you call this
function, however, Lean type inference can clean this up. For example, you can define a test
function can calls the `divide` function with lots of values and you don't need to say anything here
about the fact that it might throw an error, because that is inferred:

```lean
def test :=
  for x in [1:10] do
    for y in [0:10] do
      discard (divide x.toFloat y.toFloat)
```

The Lean compiler propagates the type information for us:
```lean
#check test     -- ExceptT String Id PUnit
```

And now we can run this test and get the expected exception:

```lean
#eval test      -- Except.error "can't divide by zero"
```

But with all good exception handling you also want to be able to catch exceptions so your program
can continue on, which you can do like this:

```lean
def testCatch := do
  try
    let r ← divide 8 0
    return toString r
  catch e =>
    return s!"Caught exception: {e}"
```

Note that the type inferred by Lean for this function is `ExceptT String Id String` so the
`ExceptT String Id Float` return type from the divide has been transformed. The ok type changed from `Float`
to `String`. This is called "monad transformation" and is what the T stands for in `ExceptT`.  The
secret to Lean is how easily it does monad transformation for you in most cases.  Notice here you
didn't have to do any extra work for the compiler to figure out that is the transform you were
trying to do.

You can now see the try/catch working in this eval:

```lean
#eval testCatch -- Except.ok "Caught exception: can't divide by zero"
```

Notice the `Caught exception:` wrapped message is returned, and that it is returned
as an `Except.ok` value, meaning it is an expected result in this case and it is a String.

So we've interleaved a new concept into our functions (exception handling) and the
compiler is still able to type check everything just as well as it does for pure functions
and it's been able to infer some things along the way to make it every easier to manage.

## Under the covers

So what really just happened under the covers? Exceptions start with this inductive type:

```lean
inductive Except (ε : Type u) (α : Type v) where
  | error : ε → Except ε α -- A failure value of type `ε`
  | ok    : α → Except ε α -- A success value of type `α`
```

It can represent an error case where the error is type `ε` or an ok case where
the ok value is type `α`.  So the type `Except String Float` represents an exception
that has a String in the error case or a floating point value in the ok case.

This Except type is then turned into a Monad by declaring this Monad type instance:

```lean
instance : Monad (Except ε) where
  pure := Except.pure
  bind := Except.bind
  map  := Except.map
```

The `ExceptT` function uses a monad to transform the type `Except ε α`:

```lean
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)
```

This takes an error type `ε`, a monad `m`, and the ok type `α` and uses the monad `m` to transform
the type `Except ε α` to create the return type.  The `T` in `ExceptT` is short for "transformer",
so `ExceptT` is a monad based type transformer.

Now the `divide` function is using the `Id` monad which is the identity transform so the return type
in this case will simply be `Except String Float`.

So the `divide` function can return an Exception object containing an error of type `String` or a ok
result of type Float - which is exactly what we wanted.

But notice that our `test` function discards the result of the `divide` since it is just a test, and
therefore lean has figured out that the `test` function then has a different `ok` type, namely
`PUnit`, which is the type meaning no value is returned.

The divide function also used this `pure` function which is defined as :

```lean
namespace Except
def pure {ε : Type u} (a : α) : Except ε α :=
  Except.ok a
```

So in the case of `Except String Float` the implicit error type `ε` is `String` and the
pure value is a `Float` and the `Except.pure` implementation then simply
uses the `Except.ok` constructor passing the pure value to be wrapped in an Except
object.  So `pure (x / y)` converts the pure value `x / y` into something that
matches the return type `Except String Float`.

All this is built on the `Monad` type class which is defined as follows:

```lean
class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
```

![Monad](./assets/monads.png)

Remember that type classes in Lean allow the compiler to do type inference using
the declared instances.  So the instance `Monad (Except ε)` allows the compiler to
invoke `Except.pure` when we call the `pure` method, and `Except.bind` if we call
`bind` and so on.

Notice the `instance : Monad (Except ε) ` doesn't define the ok type `(α : Type v)`.
If you `#check (Except String)` you will find you get a function that operates on types.
```lean
Except String : Type u_1 → Type (max 0 u_1)
```

Notice this matches the inputs to the Monad class: `(m : Type u → Type v)` and is why
you can think of a Monad as something that transforms types.

The next method to consider is the Monad `bind` method which is defined on the `Bind` type class as:

```lean
class Bind (m : Type u → Type v) where
  /-- If `x : m α` and `f : α → m β`, then `x >>= f : m β` represents the
  result of executing `x` to get a value of type `α` and then passing it to `f`. -/
  bind : {α β : Type u} → m α → (α → m β) → m β
```

Here you can see that `bind` is using a function to transform the return type
from `m α` to `m β` and is specialized in the case of the `Except.bind` as follows:

```lean
namespace Except
@[inline] protected def bind (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
  match ma with
  | Except.error err => Except.error err
  | Except.ok v      => f v
```

So this bind function can be used to transform the type `Except String Float`
to `Except String String`.  First we need a function that takes `Float → Except String String`
and it then unwraps the given `Except String Float` into its `error` and `ok` cases,
passing the error through unchanged as `Except.error err` but using the function to
transform the `ok` variable `v` into a string by applying `f v` which returns a new type
`Except String String`.

This transformation happened automatically in the `testCatch` function earlier
because we used the `do` notation which is a powerful tool that can chain monad actions
finding and applying the right bind operations automatically when needed.
In the `testCatch` function the following line of code shows how this works:

```
    return toString r -- ExceptT String Id String
```
Here the `toString` function was composed into something that contructs an
`Except.ok string` result.  So this monad type inference and composition of binding
operations is pretty powerful.

You can also use `bind` yourself if you want to control how it works which
we'll see below.


## Monad Composition

This is great, but how do you add another dimension to your program using monads?
Well it turns out in Lean monads compose very nicely, their side effects can be chained.

Suppose now you want to add some logging to your program so you know how many times
divide succeeds without throwing an exception.  Logging is very useful in large complex programs
to figure out what is really happening.

You have probably already used the IO monad to do terminal IO like `IO.println "Hello, world!"` but
that's not the kind of logging we want here. Sometimes you need something more structured, and more
light weight, and easier to consume programmatically.  So let's create a counter that is simply
incremented every time divide succeeds and pass that "logging state" into our program so you
can then also read that state when the program is finished.

There is a monad already defined for this kind of stateful side effect, it is called `MonadStateOf`:

```lean
instance [Monad m] : MonadStateOf σ (StateT σ m) where
  get       := StateT.get
  set       := StateT.set
  modifyGet := StateT.modifyGet
```

Notice it provides a `get` function to read the state, `set` function to update it, and
a `modifyGet` that does a read and an update.

If your "context state" is a simple natural number - the count of the number of times divide
succeeds -- then you could create a divide function that logs this state information
as follows:

```lean
def divideLog (x: Float ) (y: Float): StateT Nat Id Float :=
  if y == 0 then do
    return 0
  else do
    (modify) fun s => s + 1
    return x / y
```

`modify` is a helper that makes it easier to use modifyGet.

You can call this function in a test function, passing in the state on each
call, and storing the updates in a mutable state variable and with the nested for loops
this will divide by zero exactly 10 times, which means the result of successful
divides should be 90:

```lean
def testDivideLog := do
  let mut state := 0
  for x in [0:10] do
    for y in [0:10] do
      let r ← (divideLog x.toFloat y.toFloat) state
      state := r.2
  state

#eval testDivideLog -- 90
```

Great, a completely different example of adding an orthogonal dimension to our code
(logging).  But now what if we want both logging and exception handling?
Well you can chain StateT, and ExceptT because remember they take a monad as
input.  We were passing `Id` before, but now we can pass the monad `ExceptT String Id` instead
resulting in the return type `StateT Nat (ExceptT String Id) Float`! Phew, that's a
mouth full.  Lean allows very sophisticated type construction.

So this means `StateT` will transform `Except String Float` into some new return
type, in this case it will become `Except String (Float × Nat)` because we need
the modified state to be returned as well as the division result, so they are
returned as a pair.

Here's the combined monadic function:

```lean
def divideIt (x:Float) (y:Float) : StateT Nat (ExceptT String Id) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) (fun _ => pure (x / y))

#check divideIt -- Float → Float → StateT Nat (ExceptT String Id) Float
```

But how does adding a return type of `StateT` allow stateful "inputs" to be
passed to the divideIt function?  How can a return type add an input?
Are well that gets back to "curryint", check the reduced type:

```lean
#reduce StateT Nat (ExceptT String Id) Float -- Nat → Except String (Float × Nat)
```

So StateT has turned the return type into a function that takes a natural number
as input.  This has essentially then added an input parameter to our function,
but it doesn't have a name, and can only be accessed by the StateT interface
`get`, `set` and `modifyGet`.

You can now use `bind` manually to chain the 2 monadic functions, in this case
(`modify` from StateT and `pure` from `ExceptT`) and the `bind` function on StateT
is defined as:

```lean
@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do let (a, s) ← x s; f a s
```

So it returns the pair `(a, s)` which means in this case `β` is inferred to be the
type `Float × Nat`:

```lean
#eval divideIt 5 1 0 -- Except.ok (5.000000, 1)
```

The 3rd parameter passed here is the initial value of the `StateT Nat` being passed in.

You can test this new composite `divideIt` function in a very similar way to `testDivideLog`
and you can add a try/catch so the test doesn't stop when it hits a divide by zero:

```lean
def testIt := do
  let mut log := 0
  for x in [0:10] do
    for y in [0:10] do
      try
        let r ← divideIt x.toFloat y.toFloat log
        log := r.2
      catch _  =>
        pure ()
  pure log

#eval testIt -- 90
```

Notice here the extracted value in `r` is the pair `Float × Nat` so `r.2` then is
the updated `state`, or the count of times we did a successful divide and we get
the same result, 90 good divides.

Ok, now to bring it all together, you don't need to use `bind` manually like this
because the `do Notation` can chain monadic actions using bind automatically,
so you can rewrite the divideIt function as:

```lean
def divideDo (x:Float) (y:Float) : (StateT Nat (ExceptT String Id)) Float := do
  if y == 0 then
    throw "can't divide by zero"
  else
    (modify fun s => s + 1)
    pure (x / y)
```

So here the do Notation DSL generated the code `bind (modify fun s => s + 1) (fun _ => pure (x / y))`
for you.  Pretty neat.  Note that we used the do notation in `divideLog` to do some chaining also.

So an imperative programs can be modelled in functional languages as a chain of monadic actions :-)

## Add one more for fun!

`ReaderT` is like `StateT` but it is read only, so it is ideal for "context" or "global state".
We can use it to pass around our command line arguments so different parts of our program can
behave differently as a result of those arguments.

```
def divide (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) fun _ =>
      bind (get) fun s =>
        bind (read) fun args =>
          if (s > 10 && args.contains "--limit") then
            throw "too many tries"
          else
            pure (x / y)

/-
List String → Nat → Except String (Float × Nat)
-/
#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float

#eval divideWithArgs 5 2 [] 0 -- Except.ok (2.500000, 1)
#eval divideWithArgs 5 0 [] 0 -- Except.error "can't divide by zero"
#eval divideWithArgs 5 2 ["--limit"] 10 -- Except.error "too many divides"
```

And of course `do` Notation cleans this up nicely:

```lean
def divideWithArgsDo (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float := do
  if y == 0 then
    throw "can't divide by zero"
  else
    modify fun s => s + 1
    let s ← get
    let args ← read
    if (s > 10 && args.contains "--limit") then
      throw "too many divides"
    else
      pure (x / y)

#eval divideWithArgsDo 5 2 ["--limit"] 10 -- Except.ok (2.500000, 1)
#eval divideWithArgsDo 5 2 ["--limit"] 10 -- Except.error "too many divides"
#eval divideWithArgsDo 5 0 ["--limit"] 10 -- Except.error "can't divide by zero"
```

Oooh, isn't that loverly.

## Lifting

An important part of any program is functional decomposition, breaking large functions up into
smaller ones. When you do that you don't always want the smaller functions to have the big
complex return types of the outer function.  Let's take a look at an example.  Remember
our first divide function that throws on divide by zero?

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

#eval divideRefactored 5 0 [] 0 -- Except.error "can't divide by zero"
```

Very cool - but some magic happened here. The smaller `divide` function has a different return type
`ExceptT String Id Float` yet we returned it's value no problem and the compiler turned it into
`ReaderT (List String) (StateT Nat (ExceptT String Id)) Float` for us somehow.

This is called "monad lifting" and is another secret sauce that Lean provides that make Monads
super easy to use.  You could imagine manual monad lifting would be very tedious indeed.
You can see this in action with the following test:

```lean
def lift1 : ExceptT String Id Float → (StateT Nat (ExceptT String Id)) Float :=
  fun x => liftM x

#eval lift1 (divide 5 1) 3 -- Except.ok (5.000000, 3)
```

You can see this is lifted because the `Execpt.ok` value is a pair.
Now we need a second lift to ReaderT:

```lean
def lift2 (x : StateT Nat (ExceptT String Id) Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  x

#eval lift2 (lift1 (divide 5 1)) [] 0 -- Except.ok (5.000000, 0)
```

So you can see how the lifts compose nicely, we can pass in the ReaderT args, and the initial state, and
we get back the divide result and the returned state.

So what Lean did for you here is a transitive closer of lifting operations.
Let's see how that works.  `liftM` is an abbreviation for `monadLift` from `MonadLiftT`.

```lean
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  /-- Lifts a value from monad `m` into monad `n`. -/
  monadLift : {α : Type u} → m α → n α
```

The `T` in `MonadLiftT` stands for "transitive" it is able to transitively
lift monadic computations using `MonadLift` which is a function for
for lifting a computation from an inner `Monad` to an outer `Monad`.

So now we can check all the `instance : MonadLift` defined in Lean, and in our case we will be using:

```lean
instance : MonadLift m (StateT σ m)  -- to add the StateT Nat wrapper
instance  : MonadLift m (ReaderT ρ m) -- to add the ReaderT wrapper
```

These instances override the `lift` function for these types, showing the compiler
how to generate that code.  Let's see how that works for StateT:

```lean
@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)
```

So given some implicit type `α` and a monad `m` that acts on `α` it is able to
generate the return type `StateT σ m α` by returning a function that takes some
state `s` from which it can then create the pair (a, s) where `a` is the result
of applying the monad `m α`.  And this is what we saw, the state `0` passed in
resulted in a pair coming back out as `(5.000000, 0)`.  It is not inventing
the state, it is simply making it an input and an output so the output is
a valid `StateT Nat (ExceptT String Id)`.

Similarly, for `ReaderT` we find

```lean
instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x
```
This one is a bit simpler, remember `ReaderT` is about passing in some read-only
state, but to lift something that is not `ReaderT` that thing that is not
`ReaderT` obviously doesn't care about this read only state, so we can throw
it away using the underscore `_` and simply return the type being lifted,
which is what we saw with this eval:

```lean
#eval lift2 (lift1 (divide 5 1)) [] 0 -- Except.ok (5.000000, 0)
```

The ReaderT state here is the empty list `[]`, it is thrown away when
calling lift1 because `lift` didn't want it.

So looking at `divideRefactored` again, you get an appreciation for what is
going on under the covers to make that monadic code nice and composable,
both on the way in with monads like `ReaderT` and `StateT` adding additional
input parameters, and on the way out with automatic transitive monad lifting.
Lift happens very often in Lean.

## Testing

You can now build the app with `lake build` and try out our main function:

```
def main (s: List String): IO Unit := do
  IO.println (match (divideRefactored 5 2 s 10) with
  | Except.error s => s
  | Except.ok r => toString r)
```

`lake build` will create a binary named `simpleMonads` which  you can
run from the command line and you can pass command line parameters
as follows:

```shell
simpleMonads
(2.500000, 11)

simpleMonads --limit
too many divides
```

So we were able to influence the behavior of our program by passing a
command line argument all in a purely functional way.