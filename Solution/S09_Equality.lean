import Tutorial.L09_Equality

/-!
# Solution 09 · Equality and rewrite

Reference answers for `Exercise/E09_Equality.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S09

open L09

/-- **1.** Two rewrites, one of them right to left; the goal closes itself once both sides
agree (section 2). -/
theorem eq_chain (a b c : Nat) (h₁ : b = a) (h₂ : b = c) : a = c := by
  rw [← h₁, h₂]

/-- **2.** Rewrite in a hypothesis, then use it (section 2). -/
theorem lt_of_eq (a b : Nat) (h : a = b) (hb : b < 7) : a < 7 := by
  rw [← h] at hb
  exact hb

/-- **3.** With `rw` and library lemmas only. Hint: the same lemma twice, each time with
explicit arguments to pick the occurrence (section 3). -/
theorem add_shuffle (a b c : Nat) : a + b + c = c + (b + a) := by
  rw [Nat.add_comm (a + b) c, Nat.add_comm a b]

/-- **4.** With `simp` and `omega`: `simp` rewrites with `twice_eq`, `omega` finishes
(section 4). -/
theorem twice_add (m n : Nat) : twice (m + n) = twice m + twice n := by
  simp
  omega

/-- **5.** Tag your own simp lemma. Prove `quad_eq`, mark it `@[simp]` (the attribute goes
before `theorem`), and then `quad_twice` is `simp` followed by `omega`, as in exercise 4
(section 4). -/
def quad (n : Nat) : Nat := twice (twice n)

@[simp] theorem quad_eq (n : Nat) : quad n = 4 * n := by
  unfold quad
  simp
  omega

theorem quad_twice (n : Nat) : quad n = twice n + twice n := by
  simp
  omega

/-- **6.** A `calc` chain with three steps, `≤`, `≤`, `<`: the error after two RK stages
each bounded by `tol` is below `2 * tol + 1` (section 5). Hint: `Nat.add_le_add_right`,
`Nat.add_le_add_left`, `Nat.lt_succ_of_le` or `omega` for the last step. -/
theorem two_stage_bound (e₁ e₂ tol : Nat) (h₁ : e₁ ≤ tol) (h₂ : e₂ ≤ tol) :
    e₁ + e₂ < 2 * tol + 1 := by
  calc e₁ + e₂ ≤ tol + e₂ := Nat.add_le_add_right h₁ e₂
    _ ≤ tol + tol := Nat.add_le_add_left h₂ tol
    _ < 2 * tol + 1 := by omega

/-- **7.** Integer midpoint, as in bisection: with `a < b` the midpoint is strictly below
`b` and at least `a`. Hint: `constructor`, then `omega` on each goal; `<;>` does both
at once (section 6). -/
theorem mid_strict (a b : Nat) (h : a < b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 < b := by
  constructor <;> omega

/-- **8.** Two implementations of the same function are equal. Hint: as in section 7. -/
def triple (x : Nat) : Nat := 3 * x

def triple' (x : Nat) : Nat := x + x + x

theorem triple_eq_triple' : triple = triple' := by
  funext x
  unfold triple triple'
  omega

/-- **9.** Move an equation through a function with `congrArg` (section 7), as a term. -/
theorem succ_eq_of_eq (a b : Nat) (h : a = b) : a + 1 = b + 1 := congrArg (· + 1) h

/-- **10.** `simp?` first, then write the `simp only […]` it reports (section 4). -/
theorem reverse_map_length (xs : List Nat) (f : Nat → Nat) :
    ((xs.map f).reverse).length = xs.length := by
  simp only [List.length_reverse, List.length_map]

end S09
