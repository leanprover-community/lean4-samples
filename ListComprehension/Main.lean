import ListComprehension

def main : IO Unit :=
  IO.println s!"Hello to list comprehension!"

#eval List.map (λ x => toString x) [1,2,3] -- ["1", "2", "3"]

#eval [1,2,3,4,5,6,7].map (λ x => x + 1)
-- [2, 3, 4, 5, 6, 7, 8]

#eval (λ x => x + 1) <$> [1,2,3,4,5,6,7]
-- [2, 3, 4, 5, 6, 7, 8]


#eval (List.range 10).map (λ x => x * x)
-- [0, 1, 4, 9, 16, 25, 36, 49, 64, 81]


#eval (List.range 10).map (· ^ 2)
-- [0, 1, 4, 9, 16, 25, 36, 49, 64, 81]

#eval [(x, y) | for x in [1,2,3], for y in [3,1,4], if x != y]
-- [(1, 3), (1, 4), (2, 3), (2, 1), (2, 4), (3, 1), (3, 4)]

def vec : List Int := [-4, -2, 0, 2, 4]

-- create a new list with the values doubled
#eval [x*2 | for x in vec]
-- [-8, -4, 0, 4, 8]

-- filter the list to exclude negative numbers
#eval [x | for x in vec, if x >= 0]
-- [0, 2, 4]


-- apply a function to all the elements
#eval [x.natAbs | for x in vec]
-- [4, 2, 0, 2, 4]

-- call a method on each element
def freshfruit := ["  banana", "  loganberry ", "passion fruit  "]
#eval [weapon.trim | for weapon in freshfruit]
-- ["banana", "loganberry", "passion fruit"]

-- create a list of 2-tuples like (number, square)
#eval [(x, x^2) | for x in List.range 6]
-- [(0, 0), (1, 1), (2, 4), (3, 9), (4, 16), (5, 25)]

-- flatten a list using a listcomp with two 'for'
def nested := [[1,2,3], [4,5,6], [7,8,9]]
#eval [num | for elem in nested, for num in elem]
-- [1, 2, 3, 4, 5, 6, 7, 8, 9]

def pi := 3.1415926535
-- List comprehensions can contain complex expressions and nested functions:
#eval [let x := i.toFloat * pi; toString (Float.round x) | for i in List.range 6]
-- ["0.000000", "3.000000", "6.000000", "9.000000", "13.000000", "16.000000"]

def matrix := [
    [1, 2, 3, 4],
    [5, 6, 7, 8],
    [9, 10, 11, 12]]

#eval [[row[i]! | for row in matrix] | for i in List.range 4]
--[[1, 5, 9], [2, 6, 10], [3, 7, 11], [4, 8, 12]]

#eval List.prod (List.range 3) (List.range 3)
-- [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

#eval [(x, y) | for x in List.range 5, for y in List.range 5, if x + y <= 5 && x + y > 3]
-- [(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (3, 1), (3, 2), (4, 0), (4, 1)]


#eval [x * y | for (x, y) in List.prod (List.range 3) (List.range 3)]
-- [0, 0, 0, 0, 1, 2, 0, 2, 4]

#eval [num | for elem in nested, for num in elem, if num < 5]
-- [1, 2, 3, 4]

#eval List.join [[num | for num in elem, if num < 5] | for elem in nested]
-- [1, 2, 3, 4]

#eval List.map' [1,2,3] (λ num => if num < 5 then [num] else [])
-- [[1], [2], [3]]

#eval List.join (List.map' [1,2,3] (λ num => if num < 5 then [num] else []))
-- [1, 2, 3]

#eval List.map' nested  (λ elem =>
         List.join (List.map' elem (λ num => if num < 5 then [num] else []) ))
-- [[1, 2, 3], [4], []]

#eval List.join ( List.map' nested  (λ elem =>
        List.join (List.map' elem (λ num => if num < 5 then [num] else []) )))
-- [1, 2, 3, 4]