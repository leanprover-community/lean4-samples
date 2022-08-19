
@[inline] def ok {ε : Type u} (a : α) : Except ε α := pure a

/- simple exception handling monad -/
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    ok (x / y)

#eval divide 5 0  -- Except.error "can't divide by zero"

#check (Except String) -- Type u_1 → Type (max 0 u_1)

#check ExceptT String Id

def test :=
  divide 5 0

#check test  -- ExceptT String Id Float
#eval test -- Except.error "can't divide by zero"
#eval test.run -- this was done implicitly for us
#eval test |>.run -- this is the best way to call run if run takes arguments.

def testCatch :=
    try
      let r ← divide 8 0 -- 'r' is type Float
      return toString r
    catch e =>
      return s!"Caught exception: {e}"

#check testCatch -- ExceptT String Id String
#eval testCatch -- Caught exception: can't divide by zero

/- unwrap Except using match -/
def testUnwrap : String := Id.run do
    let r := divide 8 0 -- r is type ExceptT String Id Float
    match r with
    | .ok a => toString a -- 'a' is type Float
    | .error e => s!"Caught exception: {e}"

#check testUnwrap -- String
#eval testUnwrap -- "Caught exception: can't divide by zero"

/- unwrap Except using coercion -/
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

/- adding StateT -/

def divideLog (x: Float ) (y: Float): StateT Nat Id Float :=
  if y == 0 then
    return 0
  else do
    modify fun s => s + 1
    return x / y

#check divideLog              -- Float → Float → StateT Nat Id Float
#reduce StateT Nat Id Float   -- Nat → Float × Nat

#eval divideLog 8 4 0         -- (2.000000, 1)
#eval (divideLog 8 4).run 0   -- (2.000000, 1)
#eval divideLog 8 4 |>.run 0  -- (2.000000, 1)

def testDivideLog := do
  let mut state := 0
  for x in [0:10] do
    for y in [0:10] do
      let r ← divideLog x.toFloat y.toFloat |>.run state
      state := r.2
  state


#eval testDivideLog -- 90

/- chaining monads using bind -/
def divideIt (x:Float) (y:Float) : StateT Nat (ExceptT String Id) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) (fun _ => pure (x / y))

#check divideIt
#reduce StateT Nat (ExceptT String Id) Float
#eval divideIt 5 2 |>.run 0 -- Except.ok (5.000000, 1)

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

/- using do notation -/
def divideDo (x:Float) (y:Float) : (StateT Nat (ExceptT String Id)) Float := do
  if y == 0 then
    throw "can't divide by zero"
  else
    modify fun s => s + 1
    pure (x / y)

#eval divideDo 5 2 |>.run 0 -- Except.ok (2.500000, 1)

/- Adding ReadeT monad -/
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

#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float -- List String → Nat → Except String (Float × Nat)
#eval divideWithArgs 5 2 |>.run [] |>.run 0 -- Except.ok (2.500000, 1)
#eval divideWithArgs 5 0 |>.run [] |>.run 0 -- Except.error "can't divide by zero"
#eval divideWithArgs 5 2 |>.run ["--limit"] |>.run 10 -- Except.error "too many divides"

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
#eval divideWithArgsDo 5 2 |>.run ["--limit"] |>.run 10 -- Except.error "too many divides"

/- proof that these are the same-/
example : divideWithArgs x y = divideWithArgsDo x y := by
  simp[divideWithArgs, divideWithArgsDo]    -- Goals accomplished 🎉

/- monad composition using lifting -/
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

#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float
#reduce ExceptT String Id Float

def lift1 (x : ExceptT String Id Float) : (StateT Nat (ExceptT String Id)) Float :=
  x

#print lift1  -- fun x => liftM x

#reduce lift1 -- fun x s => Except.rec (fun a => Except.error a) (fun a => Except.ok (a, s)) x

#eval lift1 (divide 5 1) |>.run 3 -- Except.ok (5.000000, 3)

def lift2 (x : StateT Nat (ExceptT String Id) Float)  : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  x

def transitive (x : StateT Nat (ExceptT String Id) Float) := do
  let x := lift1 (divide 5 1)
  lift2 x


#eval lift2 (lift1 (divide 5 1)) |>.run ["discarded", "state"] |>.run 4 -- Except.ok (5.000000, 4)

#reduce ExceptT String Id -- Except String α

/- some common patterns with structures and abbreviations -/
structure Config where
  x : Nat
  y : Nat
  deriving Repr

abbrev CoolM := StateT Config (ExceptT Nat Id)

def doSomethingCool : CoolM Nat :=do
  let s ← get
  set {s with x := 10}
  pure 0

#check doSomethingCool -- CoolM Nat
#reduce CoolM Nat      -- Config → Except Nat (Nat × Config)
#synth Monad CoolM     -- StateT.instMonadStateT
#eval doSomethingCool |>.run  {x := 0, y := 0} -- Except.ok (0, { x := 10, y := 0 })

