import Tutorial.L03_TypeClass

/-!
# Solution 03 · Polymorphism and type class

Reference answers for `Exercise/E03_TypeClass.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S03

open L03

/-- **1.** Negation of a vector, so that `-v` works. -/
instance : Neg Vec2 where
  neg v := ⟨-v.x, -v.y⟩
#guard -(Vec2.mk 1 2) == ⟨-1, -2⟩

/-- **2.** Centroid (arithmetic mean) of a non-empty list of points. Hint: `List.sum` works
on `Vec2` (section 4), and `HMul Float Vec2 Vec2` scales a vector. -/
def centroid (ps : List Vec2) : Vec2 := (1 / ps.length.toFloat) * ps.sum
#guard centroid [⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨0, 2⟩] == ⟨1, 1⟩

/-- **3.** The element maximising `f`, or `none` for the empty list. Polymorphic in the
element type. Hint: recursion as in `maxList` (exercise 02.4), comparing `f x`. -/
def maxBy {α : Type} (f : α → Float) : List α → Option α
  | [] => none
  | x :: xs =>
    match maxBy f xs with
    | none => some x
    | some m => some (if f x > f m then x else m)
#guard maxBy (·.norm) [Vec2.mk 1 1, ⟨3, 4⟩, ⟨0, 2⟩] == some ⟨3, 4⟩
#guard maxBy (fun (n : Nat) => n.toFloat) [] == none

/-- **4.** A class for types with a norm, instances for `Float` (absolute value) and `Vec2`,
and a generic `normalize` that scales `x` to norm `1`. Hint: scale by the reciprocal of
the norm; the `HMul` instance argument is what makes the scaling generic. -/
class Norm (α : Type) where
  norm : α → Float

export Norm (norm)

instance : Norm Float where
  norm x := x.abs

instance : Norm Vec2 where
  norm v := v.norm

def normalize {α : Type} [Norm α] [HMul Float α α] (x : α) : α := (1 / norm x) * x
#guard (norm (normalize (Vec2.mk 3 4)) - 1).abs < 1e-12
#guard normalize (-2 : Float) == -1

/-- The implicit midpoint rule, a one-stage *implicit* method (`a₁₁ ≠ 0`). -/
def implicitMidpoint : Tableau where
  a := #[#[1/2]]
  b := #[1]
  c := #[1/2]

/-- **5.** A tableau is explicit when `a` is strictly lower triangular: `aᵢⱼ = 0` whenever
`j ≥ i`. Hint: `List.range`, `List.all`, and `t.a[i]![j]!` indexing (lesson 01, section 5).
-/
def isExplicit (t : Tableau) : Bool :=
  (List.range t.a.size).all fun i =>
    (List.range t.a[i]!.size).all fun j => j < i || t.a[i]![j]! == 0
#guard isExplicit rk4
#guard !isExplicit implicitMidpoint

/-- **6.** Consistency: `a`, `b`, `c` have the same number of stages, the row sums of `a`
equal `c` (reuse `Tableau.rowSumOk`), and `Σ bᵢ = 1`. -/
def consistent (t : Tableau) : Bool :=
  t.a.size == t.c.size && t.b.size == t.c.size && t.rowSumOk && t.b.foldl (· + ·) 0 == 1
#guard consistent rk4
#guard consistent implicitMidpoint

/-- **7.** In-order traversal of a tree, and building a search tree from a list by repeated
`Tree.insert` (section 2). Together they sort a list of distinct elements (`Tree.insert`
drops duplicates). Hint: `List.foldl`. -/
def toList {α : Type} : Tree α → List α
  | .leaf => []
  | .node l v r => toList l ++ [v] ++ toList r

def fromList {α : Type} [Ord α] (xs : List α) : Tree α :=
  xs.foldl (fun t x => t.insert x) .leaf
#guard toList (fromList [3, 1, 2]) == [1, 2, 3]
#guard toList (fromList ["b", "a"]) == ["a", "b"]

/-- **8.** Matrix–vector product over `Rat`, row by row. For a consistent tableau,
`A · (1, …, 1) = c`. Hint: `Array.map`, `Array.zip`, `Array.foldl`. -/
def matVec (A : Array (Array Rat)) (v : Array Rat) : Array Rat :=
  A.map fun row => (row.zip v).foldl (fun acc (a, x) => acc + a * x) 0
#guard matVec rk4.a #[1, 1, 1, 1] == rk4.c

end S03
