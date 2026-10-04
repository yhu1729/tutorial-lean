import Tutorial.L08_Debug

/-!
# Exercise 08 · Interlude: read an error, debug a proof

Each stub records an attempt that failed and the first line of its error. Replace the
`sorry` with a version that works, then uncomment the checks. Section numbers refer to
`Tutorial/L08_Debug.lean`. Answers: `Solution/S08_Debug.lean`.

`digitCount` comes from the lesson through `open L08`.
-/

namespace E08

open L08

/-- **1.** Attempt: `exact h`. Error: `Type mismatch … ↑n ≤ 7 … n ≤ 7`. The `↑` is the
`Nat → Int` coercion (section 2). -/
theorem nat_le_of_int_le (n : Nat) (h : (n : Int) ≤ 7) : n ≤ 7 := by
  sorry

/-- **2.** Attempt: `n + x`. Error: `failed to synthesize … HAdd Nat Float` (section 3). -/
def mix (n : Nat) (x : Float) : Float := sorry
-- #guard mix 2 1.5 == 3.5

/-- **3.** Attempt: `exact Nat.le_succ`. Error: `Type mismatch … ∀ (n : Nat), n ≤ n.succ`
(section 2). -/
theorem le_succ_self (n : Nat) : n ≤ n + 1 := by
  sorry

/-- **4.** Attempt: `⟨_, by decide⟩`. Error: `Expected type must not contain
metavariables` (section 4). -/
theorem exists_sq_gt : ∃ n : Nat, n * n > 50 := by
  sorry

/-- A convergence criterion, as a definition. -/
def WithinTol (err tol : Nat) : Prop := err ≤ tol

/-- **5.** Attempt: `omega`. Error: `omega could not prove the goal: No usable constraints
found` (section 6). -/
theorem withinTol_mono (e t : Nat) (h : WithinTol e t) : WithinTol e (t + 1) := by
  sorry

/-- **6.** Attempt: `example : WithinTol 3 5 := by decide`. Error: `failed to synthesize
Decidable (WithinTol 3 5)`. Make it decidable (section 6). -/
instance (e t : Nat) : Decidable (WithinTol e t) := sorry
-- example : WithinTol 3 5 := by decide
-- #guard decide (WithinTol 7 5) == false

/-- **7.** Attempt: `decide`. Error: `… did not reduce to isTrue or isFalse` (section 7).
Fix it without `native_decide`, then confirm the axioms with the commented block. -/
theorem digitCount_98765 : digitCount 98765 = 5 := by
  sorry
-- /-- info: 'E08.digitCount_98765' depends on axioms: [propext, Quot.sound] -/
-- #guard_msgs in
-- #print axioms digitCount_98765

/-- **8.** Attempt: `rfl`. Error: `The left-hand side xs ++ [] is not definitionally equal
to the right-hand side xs` (section 8; lesson 09, section 1 names the lemma). -/
theorem append_nil' (xs : List Nat) : xs ++ [] = xs := by
  sorry

/-- **9.** Attempt: `exact ⟨hp, hq⟩`. Error: `Application type mismatch: The argument hp
has type p but is expected to have type q` (section 2). -/
theorem and_swap (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  sorry

/-- **10.** Attempt: `theorem half_twice (n : Nat) : n / 2 * 2 = n := by omega`. Error:
`omega could not prove the goal: a possible counterexample …`. The statement is false
(`#eval 3 / 2 * 2`); the one below is the corrected statement. Prove it (section 11,
step 6). -/
theorem half_twice (n : Nat) : n / 2 * 2 + n % 2 = n := by
  sorry

end E08
