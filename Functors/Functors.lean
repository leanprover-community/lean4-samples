#eval [1,2,3].map (λ x => toString x)

#eval  (λ x => toString x) <$> [1,2,3]

#eval ["elephant", "tiger", "giraffe"].map (fun s => s.length) -- [8, 5, 7]

#eval [1,2,3,4,5].map (fun s => (s.toFloat) ^ 3.0) -- [1, 8, 27, 64, 125]

#eval (fun s => s.capitalize) <$> ["chris", "david", "mark"] -- ["Chris", "David", "Mark"]

#check some 5 -- Option Nat
#eval some 5 -- some 5

#eval (some 5).map (fun x => x + 1) -- some 6

#eval (some 5).map (fun x => toString x) -- some "5"

def x : Option Nat := none
#eval x.map (fun x => toString x) -- none

#check x.map (fun x => toString x) -- Option String

/- Custom Functors -/
structure LivingSpace (α: Type) where
  totalSize : α
  numBedrooms : Nat
  masterBedroomSize : α
  livingRoomSize : α
  kitchenSize : α
  deriving Repr, BEq

/- in square feet -/
abbrev SquareFeet := Float

def mySpace : LivingSpace SquareFeet :=
  { totalSize := 1800, numBedrooms := 4, masterBedroomSize := 500, livingRoomSize := 900, kitchenSize := 400 }

#eval mySpace
/-
{ totalSize := 1800.000000,
  numBedrooms := 4,
  masterBedroomSize := 500.000000,
  livingRoomSize := 900.000000,
  kitchenSize := 400.000000 } -/

def LivingSpace.map (f : α → β) (s : LivingSpace α) : LivingSpace β :=
  {
    totalSize := f s.totalSize,
    numBedrooms := s.numBedrooms,
    masterBedroomSize := f s.masterBedroomSize,
    livingRoomSize := f s.livingRoomSize,
    kitchenSize := f s.kitchenSize }

instance : Functor LivingSpace where
  map := LivingSpace.map

#check LivingSpace -- Type → Type

abbrev SquareMeters := Float
def squareFeetToMeters (ft : SquareFeet ) : SquareMeters := (ft / 10.7639104)

/- use map to convert this to square meters -/
#eval squareFeetToMeters <$> mySpace

/-
{ totalSize := 167.224080,
  numBedrooms := 4,
  masterBedroomSize := 46.451133,
  livingRoomSize := 83.612040,
  kitchenSize := 37.160907 }
  -/

#eval id <$> mySpace == mySpace -- true

example : mySpace.map id = mySpace := by
  simp[LivingSpace.map] -- Goals accomplished 🎉

#eval squareFeetToMeters <$> (id <$> mySpace)

#eval (squareFeetToMeters ∘ id) <$> mySpace

#eval (squareFeetToMeters <$> (id <$> mySpace)) == ((squareFeetToMeters ∘ id) <$> mySpace)
