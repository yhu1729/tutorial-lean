import Tutorial.L09_Equality

/-!
# Exercise 09 · Equality and rewrite

Replace each `sorry`, then uncomment the checks. Section numbers refer to
`Tutorial/L09_Equality.lean`. Answers: `Solution/S09_Equality.lean`.

`twice` and its simp lemma `twice_eq` come from the lesson through `open L09`. Where a
hint names a tactic, use that tactic even if `omega` would also work; the point is the
tool.
-/

namespace E09

open L09

/-- **1.** Two rewrites, one of them right to left; the goal closes itself once both sides
agree (section 2). -/
theorem eq_chain (a b c : Nat) (h₁ : b = a) (h₂ : b = c) : a = c := by
  sorry

/-- **2.** Rewrite in a hypothesis, then use it (section 2). -/
theorem lt_of_eq (a b : Nat) (h : a = b) (hb : b < 7) : a < 7 := by
  sorry

/-- **3.** With `rw` and library lemmas only. Hint: the same lemma twice, each time with
explicit arguments to pick the occurrence (section 3). -/
theorem add_shuffle (a b c : Nat) : a + b + c = c + (b + a) := by
  sorry

/-- **4.** With `simp` and `omega`: `simp` rewrites with `twice_eq`, `omega` finishes
(section 4). -/
theorem twice_add (m n : Nat) : twice (m + n) = twice m + twice n := by
  sorry

/-- **5.** Tag your own simp lemma. Prove `quad_eq`, mark it `@[simp]` (the attribute goes
before `theorem`), and then `quad_twice` is `simp` followed by `omega`, as in exercise 4
(section 4). -/
def quad (n : Nat) : Nat := twice (twice n)

theorem quad_eq (n : Nat) : quad n = 4 * n := by
  sorry

theorem quad_twice (n : Nat) : quad n = twice n + twice n := by
  sorry

/-- **6.** A `calc` chain with three steps, `≤`, `≤`, `<`: the error after two RK stages
each bounded by `tol` is below `2 * tol + 1` (section 5). Hint: `Nat.add_le_add_right`,
`Nat.add_le_add_left`, `Nat.lt_succ_of_le` or `omega` for the last step. -/
theorem two_stage_bound (e₁ e₂ tol : Nat) (h₁ : e₁ ≤ tol) (h₂ : e₂ ≤ tol) :
    e₁ + e₂ < 2 * tol + 1 := by
  sorry

/-- **7.** Integer midpoint, as in bisection: with `a < b` the midpoint is strictly below
`b` and at least `a`. Hint: `constructor`, then `omega` on each goal; `<;>` does both
at once (section 6). -/
theorem mid_strict (a b : Nat) (h : a < b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 < b := by
  sorry

/-- **8.** Two implementations of the same function are equal. Hint: as in section 7. -/
def triple (x : Nat) : Nat := 3 * x

def triple' (x : Nat) : Nat := x + x + x

theorem triple_eq_triple' : triple = triple' := by
  sorry

/-- **9.** Move an equation through a function with `congrArg` (section 7), as a term. -/
theorem succ_eq_of_eq (a b : Nat) (h : a = b) : a + 1 = b + 1 := sorry

/-- **10.** `simp?` first, then write the `simp only […]` it reports (section 4). -/
theorem reverse_map_length (xs : List Nat) (f : Nat → Nat) :
    ((xs.map f).reverse).length = xs.length := by
  sorry

end E09
