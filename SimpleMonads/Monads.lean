/- simple exception handling monad -/
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#check (Except String) -- Type u_1 → Type (max 0 u_1)

def test :=
  for x in [1:10] do
    for y in [0:10] do
      discard (divide x.toFloat y.toFloat)

#eval (test).run -- Except.error "can't divide by zero"

#eval test -- interesting, eval doesn't need (test).run in this case.

#check  (Except.pure 6.5) --  Except ?m.727 Float

def testCatch := do
    try
      let r ← divide 8 0
      return toString r -- ExceptT String Id String
    catch e =>
      return s!"Caught exception: {e}"

#check testCatch -- ExceptT String Id String

#eval testCatch -- Caught exception: can't divide by zero

#check ExceptT String Id PUnit

#eval divide 5 0  -- Except.error "can't divide by zero"

def divideLog (x: Float ) (y: Float): StateT Nat Id Float :=
  if y == 0 then
    return 0
  else do
    (modify) fun s => s + 1
    return x / y

def testDivideLog := do
  let mut state := 0
  for x in [0:10] do
    for y in [0:10] do
      let r ← (divideLog x.toFloat y.toFloat) state
      state := r.2
  state


#eval testDivideLog -- 90


/- chaining monads using bind -/
def divideIt (x:Float) (y:Float) : StateT Nat (ExceptT String Id) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) fun _ => pure (x / y)

#check divideIt

#reduce StateT Nat (ExceptT String Id) Float

#eval divideIt 5 2 0 -- Except.ok (5.000000, 1)

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

/- using do notation -/
def divideDo (x:Float) (y:Float) : (StateT Nat (ExceptT String Id)) Float := do
  if y == 0 then
    throw "can't divide by zero"
  else
    modify fun s => s + 1
    pure (x / y)

#eval divideDo 5 2 0 -- Except.ok (2.500000, 1)


def divideWithArgs (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    bind (modify fun s => s + 1) fun _ =>
      bind (get) fun s =>
        bind (read) fun args =>
          if (s > 10 && args.contains "--limit") then
            throw "too many divides"
          else
            pure (x / y)

/-
List String → Nat → Except String (Float × Nat)
-/
#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float

#eval divideWithArgs 5 2 [] 0 -- Except.ok (2.500000, 1)
#eval divideWithArgs 5 0 [] 0 -- Except.error "can't divide by zero"
#eval divideWithArgs 5 2 ["--limit"] 10 -- Except.error "too many divides"


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

#eval divideWithArgsDo 5 2 [] 0 -- Except.ok (2.500000, 1)
#eval divideWithArgsDo 5 0 [] 0 -- Except.error "can't divide by zero"
#eval divideWithArgsDo 5 2 ["--limit"] 10 -- Except.error "too many divides"


def divideRefactored (x:Float) (y:Float) : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float := do
  modify fun s => s + 1
  let s ← get
  let args ← read
  if (s > 10 && args.contains "--limit") then
    throw "too many divides"
  else
    divide x y

#eval divideRefactored 5 0 [] 0 -- Except.error "can't divide by zero"

#reduce ReaderT (List String) (StateT Nat (ExceptT String Id)) Float
#reduce ExceptT String Id Float

def lift1 (x : ExceptT String Id Float) : (StateT Nat (ExceptT String Id)) Float :=
  x

#print lift1  -- fun x => liftM x

#reduce lift1 -- fun x s => Except.rec (fun a => Except.error a) (fun a => Except.ok (a, s)) x

#eval lift1 (divide 5 1) 3 -- Except.ok (5.000000, 3)

def lift2 (x : StateT Nat (ExceptT String Id) Float)  : ReaderT (List String) (StateT Nat (ExceptT String Id)) Float :=
  x

def transitive (x : StateT Nat (ExceptT String Id) Float) := do
  let x := lift1 (divide 5 1)
  lift2 x


#eval lift2 (lift1 (divide 5 1)) ["discarded", "state"] 0 -- Except.ok (5.000000, 0)