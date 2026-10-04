/-!
# Lesson 04 · Dependent type

**Goal.** Put values into types: a vector whose length is part of its type, an index that
cannot be out of range, a number that is provably positive. On the way, meet the two
halves of Lean's universe, `Prop` and `Type`; the `Decidable` class behind every `if`;
and `omega`, the tactic that discharges most index bounds for you.

In Fortran an explicit-shape dummy argument `real :: x(n)` names its length, but nothing
checks the caller's array against it. In C the length is a separate `int`, kept next to
the pointer by convention. In Lean the length can be *in the type*, `Vector Float n`.
Passing a vector of the wrong length is then a compile-time type error, and wherever the
compiler cannot see by itself that an index is in range, it asks you for a proof.
-/

namespace L04

/-! ## 1. A type that depends on a value: `Vector α n`

`Vector α n` is an `Array α` packaged with a proof that its size is `n`. The literal
`#v[…]` builds one; its length is read off the literal. -/

/-- info: #v[1, 2, 3] : Vector Nat 3 -/
#guard_msgs in
#check #v[1, 2, 3]

/-- info: { toArray := #[1, 2, 3], size_toArray := _ } -/
#guard_msgs in
#eval #v[1, 2, 3]

/-! `#eval` prints the structure: the array, and `_` for the proof, which carries no data.
The definition shows where that proof lives. `self.toArray.size = n` is a proposition
about the field next to it; a field whose *type* mentions another field is the first
dependent type of this lesson. -/

/--
info: structure Vector.{u} (α : Type u) (n : Nat) : Type u
number of parameters: 2
fields:
  Vector.toArray : Array α
  Vector.size_toArray : self.toArray.size = n
constructor:
  Vector.mk.{u} {α : Type u} {n : Nat} (toArray : Array α) (size_toArray : toArray.size = n) : Vector α n
-/
#guard_msgs in
#print Vector

/-! The usual operations exist, and their types track the length. `push` adds one element,
so the result has length `n + 1`, and the type says so literally. -/

/-- info: #v[1, 2, 3].push 4 : Vector Nat (3 + 1) -/
#guard_msgs in
#check #v[1, 2, 3].push 4

/-- info: { toArray := #[0.000000, 0.000000, 0.000000], size_toArray := _ } -/
#guard_msgs in
#eval Vector.replicate 3 (0.0 : Float)

/-- info: { toArray := #[0, 1, 4, 9], size_toArray := _ } -/
#guard_msgs in
#eval Vector.ofFn fun (i : Fin 4) => i.val * i.val

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval (#v[1, 2, 3].map (· * 2)).toList

/-! `zipWith` requires both inputs to have the *same* length `n`, so a dot product over
`Vector` has no "what if the lengths differ" case. -/

def dotV {n : Nat} (v w : Vector Float n) : Float := (v.zipWith (· * ·) w).foldl (· + ·) 0

/-- info: 32.000000 -/
#guard_msgs in
#eval dotV #v[1, 2, 3] #v[4, 5, 6]

/-! A length mismatch is a type error, reported before anything runs. The `n` of `dotV` was
fixed to `2` by the first argument, so the second must have length `2`: -/

/--
error: Application type mismatch: The argument
  #v[4, 5, 6]
has type
  Vector Float 3
but is expected to have type
  Vector Float 2
in the application
  dotV #v[1, 2] #v[4, 5, 6]
-/
#guard_msgs in
#eval dotV (#v[1, 2] : Vector Float 2) (#v[4, 5, 6] : Vector Float 3)

/-! ## 2. The dependent function type

`zeroVec n` returns a vector of length `n`. Its result type mentions its argument. -/

def zeroVec (n : Nat) : Vector Float n := Vector.replicate n 0

/-- info: zeroVec : (n : Nat) → Vector Float n -/
#guard_msgs in
#check @zeroVec

/-- info: zeroVec 3 : Vector Float 3 -/
#guard_msgs in
#check zeroVec 3

/-!
`(n : Nat) → Vector Float n` is a **dependent function type**: an arrow whose right-hand
side may use the name bound on the left. `Nat → Vector Float 3` would be an ordinary
function type, and in fact an ordinary function type is the special case where the name
is not used. The implicit `{n : Nat}` of `dotV` is the same thing, with `n` inferred
instead of passed.

The length does not have to be a literal. `grid a b n` produces `n + 1` equally spaced
points, and `toVec` turns *any* array into a vector whose length is the array's size, a
number known only at run time; the type records it symbolically. -/

/-- `n + 1` equally spaced points from `a` to `b`. -/
def grid (a b : Float) (n : Nat) : Vector Float (n + 1) :=
  Vector.ofFn fun i => a + (b - a) * i.val.toFloat / n.toFloat

/-- info: { toArray := #[0.000000, 0.250000, 0.500000, 0.750000, 1.000000], size_toArray := _ } -/
#guard_msgs in
#eval grid 0 1 4

def toVec (a : Array Float) : Vector Float a.size := ⟨a, rfl⟩

/-- info: toVec #[1, 2] : Vector Float #[1, 2].size -/
#guard_msgs in
#check toVec #[1, 2]

/-! `⟨a, rfl⟩` is the anonymous constructor of `Vector`: the array, then the proof of
`a.size = a.size`, which `rfl` (reflexivity of `=`) provides. The proof is a real
obligation. Claim the wrong length and the constructor is rejected; here `decide`
evaluated `#[1, 2, 3].size = 4` and reports that it is false. -/

/--
error: Tactic `decide` proved that the proposition
  #[1, 2, 3].size = 4
is false
-/
#guard_msgs in
example : Vector Nat 4 := ⟨#[1, 2, 3], by decide⟩

/-! ## 3. `Fin n`: a bounded index

`Fin n` is a natural number `val` together with a proof `isLt` that `val < n`. The `↑`
in the printout is the coercion from `Fin n` back to `Nat`; `i.val` and `(i : Nat)` are
the same thing. -/

/--
info: structure Fin (n : Nat) : Type
number of parameters: 1
fields:
  Fin.val : Nat
  Fin.isLt : ↑self < n
constructor:
  Fin.mk {n : Nat} (val : Nat) (isLt : val < n) : Fin n
-/
#guard_msgs in
#print Fin

/-! Numeric literals are taken modulo `n`, and arithmetic wraps around, like unsigned
integers in C but with any modulus: -/

/-- info: 2 -/
#guard_msgs in
#eval (2 : Fin 3)

/-- info: 0 -/
#guard_msgs in
#eval (3 : Fin 3)

/-- info: 1 -/
#guard_msgs in
#eval (2 : Fin 3) + 2

/-- info: 2 -/
#guard_msgs in
#eval (0 : Fin 3) - 1

/-! `Fin 0` has no elements, so there is no literal for it either: -/

/--
error: failed to synthesize instance of type class
  OfNat (Fin 0) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (1 : Fin 0)

/-! The anonymous constructor takes the value and the proof. `by omega` or `by decide`
proves `2 < 3`. In the printout the proof is shown as `⋯`: Lean elides proofs because,
as section 4 explains, their content never matters. -/

/-- info: ⟨2, ⋯⟩ : Fin 3 -/
#guard_msgs in
#check (⟨2, by omega⟩ : Fin 3)

/-- info: 3 -/
#guard_msgs in
#eval Fin.last 3        -- `Fin.last n : Fin (n + 1)`, the largest element

/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval List.finRange 4   -- `[0, 1, …, n-1]` as a `List (Fin n)`

/-! ## 4. `Prop` and `Type`

Every type lives in a universe. `Nat` lives in `Type`; `1 < 2` lives in `Prop`. -/

/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/-- info: 1 < 2 : Prop -/
#guard_msgs in
#check 1 < 2

/-!
A proposition is a type whose values are its *proofs*. `theorem` is `def` for a value of
such a type, and `#check` shows the proposition as the type of the proof. `by decide`
runs the decision procedure for `<` on `Nat` and packages the answer as a proof. -/

theorem one_lt_two : 1 < 2 := by decide

/-- info: L04.one_lt_two : 1 < 2 -/
#guard_msgs in
#check one_lt_two

/-! Two things make `Prop` different from `Type`.

**Proof irrelevance.** Any two proofs of the same proposition are equal, by definition.
So two `Fin` values with the same `val` are equal no matter how their bounds were proved,
and a `Vector` is determined by its array. -/

example (h₁ h₂ : 1 < 2) : h₁ = h₂ := rfl

example : (⟨1, by omega⟩ : Fin 3) = ⟨1, by decide⟩ := rfl

/-! **Erasure.** The compiler deletes proofs. At run time a `Fin n` is a `Nat`, a `Vector α
n` is an `Array α`, and the `_` printed by `#eval` in section 1 is literally nothing. All
the checking happens at compile time and costs nothing afterwards.

A proposition `p` can be turned into a `Bool` with `decide p`, provided Lean knows how to
decide it; the next section says what that means. -/

/-- info: true -/
#guard_msgs in
#eval decide (1 < 2)

/-- info: decide : (p : Prop) → [h : Decidable p] → Bool -/
#guard_msgs in
#check @decide

/-! ## 5. `Decidable`, and the condition of an `if`

`Decidable p` is a type class with two constructors: a proof of `p`, or a proof of `¬p`.
An instance is an algorithm that settles `p` and hands back the matching proof. -/

/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in
#print Decidable

/-! The condition of an `if` is a `Prop`, not a `Bool`, and `if` demands a `Decidable`
instance for it. `if c then t else e` is the function `ite`; the `[h : Decidable c]`
argument is found by instance search, as in lesson 03. -/

/-- info: @ite : {α : Sort u_1} → (c : Prop) → [h : Decidable c] → α → α → α -/
#guard_msgs in
#check @ite

/-- info: "yes" -/
#guard_msgs in
#eval if 3 ∣ 12 then "yes" else "no"

/-! A statement with no decision procedure cannot be the condition of an `if`. Nothing can
check every natural number at run time: -/

/--
error: failed to synthesize instance of type class
  Decidable (∀ (n : Nat), n = n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval if (∀ n : Nat, n = n) then 1 else 0

/-! A *bounded* quantifier is different: there are finitely many cases, and the standard
library has an instance that tries them all. -/

example : ∀ i, i < 5 → i * i < 30 := by decide

/-- info: true -/
#guard_msgs in
#eval decide (∀ i, i < 5 → i * i < 30)

/-! The same error appears for a `Prop` you define yourself, because Lean does not look
through the definition. The remedy is an instance; `inferInstanceAs` says "decide it the
way you would decide this other, unfolded, proposition". -/

def IsEven (n : Nat) : Prop := n % 2 = 0

/--
error: failed to synthesize instance of type class
  Decidable (IsEven 4)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval if IsEven 4 then "even" else "odd"

instance : DecidablePred IsEven := fun n => inferInstanceAs (Decidable (n % 2 = 0))

/-- info: "even" -/
#guard_msgs in
#eval if IsEven 4 then "even" else "odd"

example : IsEven 4 := by decide

example : ¬ IsEven 3 := by decide

/-! With the instance in place, `IsEven` can go wherever a `Bool`-valued function is
expected: Lean inserts `decide` for you. In the other direction a `Bool` `b` used as a
proposition means `b = true`, which is how `if n == 0 then …` type-checks. -/

/-- info: [0, 2, 4] -/
#guard_msgs in
#eval (List.range 6).filter IsEven

/-! ## 6. Index safely

Lesson 01 showed `a[i]!`, which panics when out of range, and `a[i]?`, which returns an
`Option`. The third form, `a[i]`, requires a proof that `i < a.size`, and Lean tries to
find one automatically. When that fails, the error lists every option: -/

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
a : Array Nat
⊢ 1 < a.size
-/
#guard_msgs in
def unsafeSecond (a : Array Nat) : Nat := a[1]

/-! Nothing in that context implies `1 < a.size`. Add the hypothesis to the signature and
the same `a[1]` is accepted: the automatic search runs `omega`, the linear-arithmetic
tactic from lesson 02, over the hypotheses in scope, and `2 ≤ a.size` implies
`1 < a.size`. The caller now has to supply the proof, and `by decide` computes it for a
literal array. -/

def second (a : Array Nat) (h : 2 ≤ a.size) : Nat := a[1]

/-- info: 20 -/
#guard_msgs in
#eval second #[10, 20, 30] (by decide)

/-! `a[i]'h` passes the proof explicitly when the automation needs help; `second'` is
`second` with the step spelled out. -/

def second' (a : Array Nat) (h : 2 ≤ a.size) : Nat := a[1]'(by omega)

/-! With `Vector` the bound is in the type, so most proofs are about `n` alone. The
composite trapezoid rule reads the first and last sample: `f[0]` needs `0 < n + 1` and
`f[n]` needs `n < n + 1`, both of which `omega` proves without any hypothesis. -/

/-- Composite trapezoid rule for the samples `f₀, …, fₙ` at spacing `h`. -/
def trapezoid {n : Nat} (h : Float) (f : Vector Float (n + 1)) : Float :=
  h * (f.sum - (f[0] + f[n]) / 2)

/-- info: 0.343750 -/
#guard_msgs in
#eval trapezoid 0.25 ((grid 0 1 4).map fun x => x * x)   -- ∫₀¹ x² dx = 1/3, error h²/6

/-! Indexing with a `Fin` brings its own bound along. In `diff`, `i : Fin n` satisfies
`i.val < n`, which `omega` reads off `i` and combines with the arithmetic to prove
`i.val + 1 < n + 1`. The result type `Vector Float n` tells `Vector.ofFn` how many
elements to produce. -/

/-- Forward differences `fᵢ₊₁ - fᵢ`; one element shorter than the input. -/
def diff {n : Nat} (v : Vector Float (n + 1)) : Vector Float n :=
  Vector.ofFn fun i => v[i.val + 1] - v[i.val]

/-- info: { toArray := #[3.000000, 5.000000, 7.000000], size_toArray := _ } -/
#guard_msgs in
#eval diff #v[1, 4, 9, 16]

/-! ## 7. A numeral next to an index

One elaboration quirk bites exactly this kind of code. Elaborating an index `f[i]`
forces Lean to settle the numerals still pending in the same expression with their
default type, `Nat`. A numeral to the *left* of an index therefore becomes a `Nat`, and
the error names a mixed operation that has no instance: -/

/--
error: failed to synthesize instance of type class
  HDiv Float Nat ?m.21

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def thirdPlusFirst {n : Nat} (h : Float) (f : Vector Float (n + 1)) : Float := h / 3 + f[0]

/-! Annotate the numeral, `h / (3 : Float) + f[0]`, or put the index first: `f[0] + h / 3`
elaborates as intended. In `trapezoid` the `2` already sits to the right of `f[0]` and
`f[n]`. -/

/-! ## 8. `if h : c then … else …`

A plain `if` tests the condition and forgets it. Inside the `then` branch below, nothing
records that `i < a.size` held, so the index proof fails and the goal shows a bare `i`: -/

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
a : Array Float
i : Nat
⊢ i < a.size
-/
#guard_msgs in
def getOrZeroForgetful (a : Array Float) (i : Nat) : Float :=
  if i < a.size then a[i] else 0

/-! The **dependent `if`** names the fact: `if h : c then t else e` makes a proof `h : c`
available in `t` and `h : ¬c` in `e`. Underneath it is `dite`, whose branches are
functions of the proof. -/

/-- info: @dite : {α : Sort u_1} → (c : Prop) → [h : Decidable c] → (c → α) → (¬c → α) → α -/
#guard_msgs in
#check @dite

def getOrZero (a : Array Float) (i : Nat) : Float :=
  if h : i < a.size then a[i] else 0

/-- info: 2.500000 -/
#guard_msgs in
#eval getOrZero #[1.5, 2.5] 1

/-- info: 0.000000 -/
#guard_msgs in
#eval getOrZero #[1.5, 2.5] 7

/-! This is the general pattern for moving run-time data into the typed world: one check
produces a proof, and the proof feeds a constructor that demands it. `fromArray?` tests
the length of an array once, and from then on the result is a `Vector Float n`. -/

def fromArray? (a : Array Float) (n : Nat) : Option (Vector Float n) :=
  if h : a.size = n then some ⟨a, h⟩ else none

/-- info: some { toArray := #[1.000000, 2.000000, 3.000000], size_toArray := _ } -/
#guard_msgs in
#eval fromArray? #[1, 2, 3] 3

/-- info: none -/
#guard_msgs in
#eval fromArray? #[1, 2, 3] 2

/-! ## 9. `Subtype`: a value with a property

`{ x : α // p x }` is the type of values of `α` that satisfy `p`, each paired with the
proof. `Fin n` is this idea specialised to `{ i : Nat // i < n }`. -/

/--
info: structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
number of parameters: 2
fields:
  Subtype.val : α
  Subtype.property : p self.val
constructor:
  Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p
-/
#guard_msgs in
#print Subtype

abbrev PosNat := { n : Nat // 0 < n }

def three : PosNat := ⟨3, by decide⟩

/-- info: 3 -/
#guard_msgs in
#eval three.val

/-- info: three.property : 0 < three.val -/
#guard_msgs in
#check three.property

/-! A function that takes a `PosNat` cannot be called with zero. The `Nat` division is the
same as before; what changed is that the caller has to prove the divisor positive, and
`decide` refuses when it is not. -/

def safeDiv (a : Nat) (b : PosNat) : Nat := a / b.val

/-- info: 3 -/
#guard_msgs in
#eval safeDiv 7 ⟨2, by decide⟩

/--
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
#eval safeDiv 7 ⟨0, by decide⟩

/-! The same move removes an empty-list case. `List.head` requires a proof that the list
is not empty, and the subtype's `property` is exactly that proof. Exercise 6 applies
this to a mean, where exercise 03.2 had to divide by zero. -/

abbrev NonEmptyList := { xs : List Float // xs ≠ [] }

def first (xs : NonEmptyList) : Float := xs.val.head xs.property

/-- info: 1.500000 -/
#guard_msgs in
#eval first ⟨[1.5, 2.5], by decide⟩

/-! ## 10. A Butcher tableau, with its stage count in the type

Lesson 03 stored a tableau as three arrays, and exercise 03.6 had to *check* that their
sizes agreed. With the stage count `s` as a parameter of the structure, agreement is a
type-checking fact:
`a` is an `s × s` matrix, `b` and `c` have `s` entries, or the definition does not
compile. -/

structure Tableau (s : Nat) where
  a : Vector (Vector Rat s) s
  b : Vector Rat s
  c : Vector Rat s

/-- The classical fourth-order Runge–Kutta method, now a `Tableau 4`. -/
def rk4 : Tableau 4 where
  a := #v[#v[0, 0, 0, 0], #v[1/2, 0, 0, 0], #v[0, 1/2, 0, 0], #v[0, 0, 1, 0]]
  b := #v[1/6, 1/3, 1/3, 1/6]
  c := #v[0, 1/2, 1/2, 1]

/-- info: { toArray := #[(1 : Rat)/6, (1 : Rat)/3, (1 : Rat)/3, (1 : Rat)/6], size_toArray := _ } -/
#guard_msgs in
#eval rk4.b

/--
error: Type mismatch
  #v[1 / 6, 1 / 3, 1 / 3]
has type
  Vector Rat 3
but is expected to have type
  Vector Rat 4
-/
#guard_msgs in
def rk4Short : Tableau 4 where
  a := #v[#v[0, 0, 0, 0], #v[1/2, 0, 0, 0], #v[0, 1/2, 0, 0], #v[0, 0, 1, 0]]
  b := (#v[1/6, 1/3, 1/3] : Vector Rat 3)
  c := #v[0, 1/2, 1/2, 1]

/-! The remaining consistency conditions are still computations, now written with
`zipWith` instead of the `zip`-and-hope of lesson 03. A matrix–vector product over
`Matrix m n` and `Vector Rat n` can only be asked for compatible dimensions. -/

abbrev Matrix (m n : Nat) := Vector (Vector Rat n) m

def matVec {m n : Nat} (A : Matrix m n) (v : Vector Rat n) : Vector Rat m :=
  A.map fun row => (row.zipWith (· * ·) v).foldl (· + ·) 0

/-- Row-sum condition `Σⱼ aᵢⱼ = cᵢ`, as `A · (1, …, 1) = c`. -/
def Tableau.rowSumOk {s : Nat} (t : Tableau s) : Bool :=
  matVec t.a (Vector.replicate s 1) == t.c

#guard rk4.rowSumOk && rk4.b.sum == 1

/-! ## 11. Pitfall for the C, Fortran, or Python programmer

* Types are compared *up to computation*: `Vector Nat (3 + 1)` and `Vector Nat 4` are the
  same type, so `#v[1, 2, 3].push 4` can be used where a `Vector Nat 4` is expected. But
  unification does not solve equations: a `Vector Float 5` is not accepted where
  `Vector Float (2 * m + 1)` is expected, because Lean will not invert `2 * m + 1 = 5`
  to find `m`. Pass it by name, `f (m := 2) …` (exercise 9).
* `(3 : Fin 3)` is `0`. Literals are reduced modulo `n` and arithmetic wraps, unlike `Nat`,
  whose subtraction truncates at `0` (lesson 01).
* `if c then …` gives the branches no hypothesis. Write `if h : c then …` when the
  branch needs the fact, typically for `a[i]` or a constructor that wants a proof.
* The index proof search runs `omega`, which knows linear arithmetic over `Nat` and `Int`
  and reads bounds off `Fin` values, but it does not look inside your definitions, and
  a `Bool` test such as `n == 0` tells it nothing (lesson 02, exercise 7).
* `decide` needs a `Decidable` instance, and the instance has to *reduce* inside the
  kernel. Comparisons on `Nat`, `Int`, `Fin`, and `Float` do; `Rat` arithmetic gets stuck
  the way `gcd'` did in lesson 02, section 7 (pinned below this list), so check `Rat`
  arithmetic with `#guard` or `native_decide`. A `Prop` you define has no instance until
  you write one, usually with
  `inferInstanceAs`. An unbounded `∀ n : Nat, …` has no instance; a bounded one such as
  `∀ i, i < 5 → …` does (section 5).
* Proofs cost nothing at run time, but they can cost compile time: `by decide` on a large
  literal array evaluates the whole array inside the kernel.
* `#eval` refuses to run an expression that depends on `sorry`. That is why the checks
  in the exercise files start out commented.
* A numeral to the left of an `f[i]` in the same expression may be typed `Nat`; the
  symptom is `failed to synthesize HDiv Float Nat`. Annotate it, `(3 : Float)`, or move
  the index to the front (section 7). -/

/--
error: Tactic `decide` failed for proposition
  1 / 2 + 1 / 2 = 1
because its `Decidable` instance
  instDecidableEqRat (1 / 2 + 1 / 2) 1
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqRat`, `Int.decEq`, `Int.instDecidableEq`, and `instDecidableEqRat.decEq`, reduction got stuck at the `Decidable` instance
  match ((1 / 2).add (1 / 2)).num, ↑1 with
  | Int.ofNat a, Int.ofNat b =>
    match decEq a b with
    | isTrue h => isTrue ⋯
    | isFalse h => isFalse ⋯
  | Int.ofNat a, Int.negSucc a_1 => isFalse ⋯
  | Int.negSucc a, Int.ofNat a_1 => isFalse ⋯
  | Int.negSucc a, Int.negSucc b =>
    match decEq a b with
    | isTrue h => isTrue ⋯
    | isFalse h => isFalse ⋯
-/
#guard_msgs in
example : (1 : Rat) / 2 + 1 / 2 = 1 := by decide

#guard (1 : Rat) / 2 + 1 / 2 == 1

example : (1 : Rat) < 2 := by decide

/-!
## Exercise

Open `Exercise/E04_DependentType.lean`. -/

end L04
