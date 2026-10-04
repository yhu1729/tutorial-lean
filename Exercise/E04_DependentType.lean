import Tutorial.L04_DependentType

/-!
# Exercise 04 · Dependent type

Replace each `sorry`, then uncomment the checks. Section numbers refer to
`Tutorial/L04_DependentType.lean`. Answers: `Solution/S04_DependentType.lean`.

`grid`, `Tableau`, and `rk4` come from the lesson through `open L04`.
-/

namespace E04

open L04

/-- **1.** The next index, wrapping around: `cyclicNext (Fin.last n) = 0`. Hint: `Fin`
arithmetic already wraps (section 3). The bound is written `n + 1` so that the literal
`1` exists. -/
def cyclicNext {n : Nat} (i : Fin (n + 1)) : Fin (n + 1) := sorry
-- #guard cyclicNext (2 : Fin 3) == 0
-- #guard (List.finRange 4).map cyclicNext == [1, 2, 3, 0]

/-- **2.** Componentwise sum of two vectors of the same length. Hint: `Vector.zipWith`
(section 1). Then try `addV #v[1, 2] #v[1, 2, 3]` in a scratch line and read the error. -/
def addV {n : Nat} (v w : Vector Float n) : Vector Float n := sorry
-- #guard addV #v[1, 2, 3] #v[10, 20, 30] == #v[11, 22, 33]

/-- **3.** The last element of a non-empty vector. Hint: which index is the last one in a
`Vector α (n + 1)`? Its bound is proved for you (section 6). -/
def last {α : Type} {n : Nat} (v : Vector α (n + 1)) : α := sorry
-- #guard last #v[1, 2, 3] == 3
-- #guard last #v["only"] == "only"

/-- **4.** A bounded index from a plain number, when it is in range. Hint:
`if h : … then … else …` and the anonymous constructor of `Fin` (sections 3, 7). -/
def toFin? (i n : Nat) : Option (Fin n) := sorry
-- #guard toFin? 2 3 == some 2
-- #guard toFin? 3 3 == none

/-- `d` divides `n`. -/
def Divisor (d n : Nat) : Prop := n % d = 0

/-- **5.** Make `Divisor` decidable, so that `if Divisor 3 n then …`, `by decide`, and
`List.filter (Divisor 3)` all work. Hint: `inferInstanceAs` (section 5). -/
instance (d n : Nat) : Decidable (Divisor d n) := sorry
-- example : Divisor 3 12 := by decide
-- #guard !decide (Divisor 5 12)
-- #guard (List.range 10).filter (Divisor 3) == [0, 3, 6, 9]

/-- **6.** Arithmetic mean of a non-empty list. Hint: `xs.val` is the list (section 9); no
proof is needed inside, the subtype only keeps the caller honest. -/
def mean (xs : { xs : List Float // xs ≠ [] }) : Float := sorry
-- #guard mean ⟨[1, 2, 3], by decide⟩ == 2
-- #guard mean ⟨[4], by decide⟩ == 4

/-- **7.** Second differences `fᵢ₊₂ - 2fᵢ₊₁ + fᵢ`, two elements shorter than the input.
Hint: `Vector.ofFn` with `i : Fin n`, as in `diff` (section 6); `omega` proves the three
bounds from `i.isLt`. For a quadratic the result is constant. -/
def diff2 {n : Nat} (v : Vector Float (n + 2)) : Vector Float n := sorry
-- #guard diff2 #v[1, 4, 9, 16] == #v[2, 2]
-- #guard diff2 ((grid 0 1 4).map fun x => x * x) == #v[0.125, 0.125, 0.125]

/-- The implicit midpoint rule, a one-stage *implicit* method (`a₁₁ ≠ 0`). -/
def implicitMidpoint : Tableau 1 where
  a := #v[#v[1/2]]
  b := #v[1]
  c := #v[1/2]

/-- **8.** A tableau is explicit when `a` is strictly lower triangular: `aᵢⱼ = 0` whenever
`j ≥ i`. Hint: `List.finRange s` gives the indices as `Fin s`, and `t.a[i][j]` needs no
proof when `i j : Fin s` (section 6). Compare with exercise 03.5. -/
def isExplicit {s : Nat} (t : Tableau s) : Bool := sorry
-- #guard isExplicit rk4
-- #guard !isExplicit implicitMidpoint

/-- **9.** Composite Simpson rule on `2m + 1` samples at spacing `h`:
`h/3 · (f₀ + f₂ₘ + 4 Σ f₂ᵢ₊₁ + 2 Σ f₂ᵢ₊₂)`, the first sum over `i < m`, the second over
`i < m - 1`. Hint: fold over `List.finRange`, starting from `(0 : Float)`, and write `h / (3 : Float)`:
a bare `0` or `3` to the left of an index is typed `Nat` (section 7). At the call site,
write `simpson (m := 2) …`: Lean does not solve `2 * m + 1 = 5` for `m` (section 11).
Simpson is exact for cubics. -/
def simpson {m : Nat} (h : Float) (f : Vector Float (2 * m + 1)) : Float := sorry
-- #guard (simpson (m := 2) 0.25 ((grid 0 1 4).map fun x => x * x) - 1 / 3).abs < 1e-12
-- #guard (simpson (m := 2) 0.25 ((grid 0 1 4).map fun x => x * x * x) - 1 / 4).abs < 1e-12

end E04
