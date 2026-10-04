import Tutorial.L01_GetStarted

/-!
# Exercise 01 · Get started

Replace each `sorry`, then uncomment the checks. Section numbers refer to
`Tutorial/L01_GetStarted.lean`. Answers: `Solution/S01_GetStarted.lean`.

The checks start commented out because Lean refuses to evaluate a term that still
depends on `sorry`. To start over: `git restore Exercise/E01_GetStarted.lean`.
-/

namespace E01

open L01

/-- **1.** The cube of `x`. Hint: a one-line `def` (section 3). -/
def cube (x : Float) : Float := sorry
-- #guard cube 2 == 8

/-- **2.** Celsius to Fahrenheit: `c · 9 / 5 + 32`. Hint: every literal here is a `Float`
because `c` is (section 2). -/
def fahrenheit (c : Float) : Float := sorry
-- #guard fahrenheit 100 == 212

/-- **3.** `0² + 1² + … + (n-1)²`. Hint: `List.range`, `map`, `sum` (section 5). -/
def sumSquare (n : Nat) : Nat := sorry
-- example : sumSquare 4 = 14 := by decide

/-- **4.** Arithmetic mean, `0` for the empty list. Hint: `xs.length.toFloat`, `if`. -/
def mean (xs : List Float) : Float := sorry
-- #guard mean [1, 2, 3, 4] == 2.5
-- #guard mean [] == 0

/-- **5.** Horner's rule over `Nat`: port `horner` from section 5. -/
def hornerNat (coeff : List Nat) (x : Nat) : Nat := sorry
-- example : hornerNat [1, 2, 3] 2 = 17 := by decide

/-- **6.** The `n + 1` equally spaced points from `a` to `b` inclusive, like NumPy's
`linspace` with `n` intervals. Hint: `List.range (n + 1)`, `i.toFloat / n.toFloat`. -/
def linspace (a b : Float) (n : Nat) : List Float := sorry
-- #guard linspace 0 1 4 == [0, 0.25, 0.5, 0.75, 1]

/-- **7.** Composite trapezoidal rule for `∫ₐᵇ f` with `n` intervals of width `h`:
`h · (f x₀ / 2 + f x₁ + … + f xₙ₋₁ + f xₙ / 2)`. Hint: reuse `linspace`, then `map`
and `sum`; the two endpoints need separate treatment. -/
def trapezoid (f : Float → Float) (a b : Float) (n : Nat) : Float := sorry
-- #guard (trapezoid (fun x => x * x) 0 1 4 - 0.34375).abs < 1e-12

/-- **8.** Mean and population standard deviation `σ = √(Σ (xᵢ - μ)² / N)` as a pair.
Hint: `let`, reuse `mean`, `Float.sqrt`. -/
def stat (xs : List Float) : Float × Float := sorry
-- #guard stat [2, 4, 4, 4, 5, 5, 7, 9] == (5, 2)

end E01
