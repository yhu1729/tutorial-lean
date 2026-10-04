/-!
# Lesson 03 · Polymorphism and type class

**Goal.** Write code that works for any type, understand the implicit arguments Lean
fills in for you, and use *type classes*, Lean's mechanism for overloading (`+`, `==`,
`toString`, …) and for passing "the operations a type supports" into generic code.

If you know C++ templates and Rust traits, or Fortran generic interfaces: type classes
play the role of traits. If you know Python: this is what makes `+` work on your own
types, except that the compiler checks at compile time that an implementation exists.
-/

namespace L03

/-! ## 1. Polymorphism and the implicit argument

A function can take *types* as arguments. `swapE` takes the two component types
explicitly, then the pair. -/

def swapE (α β : Type) (p : α × β) : β × α := (p.2, p.1)

/-- info: ("a", 1) -/
#guard_msgs in
#eval swapE Nat String (1, "a")

/-!
Writing `Nat String` is redundant: both types are determined by the pair. Braces `{α β :
Type}` make the arguments **implicit**. Lean infers them from the other arguments at each
call site. -/

def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)

/-- info: ("a", 1) -/
#guard_msgs in
#eval swap (1, "a")

/-! `#check` shows the signature; `#check @f` shows the full type with the implicit
arguments made visible. `@f` is also how you pass them by hand, and `(α := Nat)` passes a
single one by name. -/

/-- info: L03.swap {α β : Type} (p : α × β) : β × α -/
#guard_msgs in
#check swap

/-- info: @swap : {α β : Type} → α × β → β × α -/
#guard_msgs in
#check @swap

/-- info: ("a", 1) -/
#guard_msgs in
#eval @swap Nat String (1, "a")

/-- info: ("a", 1) -/
#guard_msgs in
#eval swap (α := Nat) (1, "a")

/-! Implicit arguments are inferred from the *other* arguments. When nothing determines
them, elaboration fails and the message names the argument it could not fill in; the
`?m.4`, `?m.5` are *metavariables*, placeholders for the still-unknown types. -/

/--
error: don't know how to synthesize implicit argument `β`
  @swap ?m.4 ?m.5
context:
⊢ Type
---
error: don't know how to synthesize implicit argument `α`
  @swap ?m.4 ?m.5
context:
⊢ Type
---
error: Failed to infer type of definition `noSwap`
-/
#guard_msgs in
def noSwap := swap

/-!
### The universe, briefly

`Type` is the type of ordinary types such as `Nat` and `List Nat`. `Type` itself is not a
member of `Type` (that would be inconsistent); it lives in `Type 1`, and so on. Library
functions are usually *universe polymorphic*, written with `Type u`, so that they also
accept types of types. You will mostly meet this as the `u_1` in signatures. In your own
code `Type` is almost always what you want. -/

/-- info: Type : Type 1 -/
#guard_msgs in
#check Type

/-- info: List Type : Type 1 -/
#guard_msgs in
#check List Type

universe u

def idU {α : Type u} (a : α) : α := a

/-- info: @idU : {α : Type u_1} → α → α -/
#guard_msgs in
#check @idU

/-! The declared `u` prints as `u_1`: `#check` elaborates the expression afresh, with
universe variables of its own, since the name `u` belongs to the definition. -/

/-! ## 2. Polymorphic inductive type

An inductive type can take type parameters. `Tree α` is a binary tree with values of
type `α` at the nodes. The parameter is written before the colon and is available in
every constructor. -/

inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr

def Tree.size {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

/-!
Insertion into a search tree needs to *compare* values, so it only makes sense for types
that have an ordering. The instance argument `[Ord α]` says exactly that: "any `α`, as
long as Lean can find an `Ord α` instance". `compare x y` returns an `Ordering`, which is
`.lt`, `.eq`, or `.gt`. -/

def Tree.insert {α : Type} [Ord α] (x : α) : Tree α → Tree α
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    match compare x v with
    | .lt => .node (l.insert x) v r
    | .eq => .node l v r
    | .gt => .node l v (r.insert x)

/-- info: L03.Tree.node (L03.Tree.node (L03.Tree.leaf) 1 (L03.Tree.leaf)) 2 (L03.Tree.node (L03.Tree.leaf) 3 (L03.Tree.leaf)) -/
#guard_msgs in
#eval (Tree.leaf.insert 2 |>.insert 1 |>.insert 3 : Tree Nat)

/-- info: 3 -/
#guard_msgs in
#eval (Tree.leaf.insert 2 |>.insert 1 |>.insert 3 : Tree Nat).size

/-! ## 3. Type class

Suppose several unrelated types each have an area. A `class` declares the interface: a
type `α` "has an area" if there is a function `area : α → Float` for it. An `instance`
provides that function for one specific type. -/

class Area (α : Type) where
  area : α → Float

export Area (area)      -- lets us write `area` instead of `Area.area`

structure Circle where
  r : Float

structure Square where
  side : Float

instance : Area Circle where
  area c := 3.141592653589793 * c.r * c.r

instance : Area Square where
  area s := s.side * s.side

/-- info: 15.707963 -/
#guard_msgs in
#eval area (Circle.mk 1) + area (Circle.mk 2)

/-! Generic code asks for the instance with a square-bracket argument. The caller does
not pass it: Lean searches for it, at compile time, from the type. It is an ordinary
argument underneath, so `@totalArea Circle inferInstance xs` passes one by hand, with
`inferInstance` standing for "the one the search would find"; that is rarely needed. -/

def totalArea {α : Type} [Area α] (xs : List α) : Float := (xs.map area).sum

/-- info: 15.707963 -/
#guard_msgs in
#eval @totalArea Circle inferInstance [Circle.mk 1, Circle.mk 2]

/-- info: 15.707963 -/
#guard_msgs in
#eval totalArea [Circle.mk 1, Circle.mk 2]

/-- info: 5.000000 -/
#guard_msgs in
#eval totalArea [Square.mk 1, Square.mk 2]

/-! The signature of `area` shows how an instance is really just another (implicit)
argument, named `self` here: -/

/-- info: @area : {α : Type} → [self : Area α] → α → Float -/
#guard_msgs in
#check @area

/-! When no instance exists, the error says which one is missing. You will see this
message often; it is the type-class equivalent of "no matching overload". -/

/--
error: failed to synthesize instance of type class
  Area Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval totalArea [1, 2]

/-! ## 4. Standard class: `Add`, `HMul`, `Zero`, `ToString`, `OfNat`

Operators and conversions in Lean are all type classes: `+` is `HAdd.hAdd`, `*` is
`HMul.hMul`, `==` is `BEq.beq`, string conversion is `ToString.toString`, printing in
`#eval` is `Repr`, numeric literals are `OfNat`. To support them for your own type, write
instances. `Add α` is the common case of `HAdd α α α`; `HMul Float Vec2 Vec2` below is a
*heterogeneous* multiplication, scalar times vector. -/

structure Vec2 where
  x : Float
  y : Float
  deriving Repr, BEq

instance : Add Vec2 where
  add v w := ⟨v.x + w.x, v.y + w.y⟩

instance : HMul Float Vec2 Vec2 where
  hMul s v := ⟨s * v.x, s * v.y⟩

instance : Zero Vec2 where
  zero := ⟨0, 0⟩

instance : ToString Vec2 where
  toString v := s!"({v.x}, {v.y})"

/-- info: { x := 4.000000, y := 6.000000 } -/
#guard_msgs in
#eval Vec2.mk 1 2 + ⟨3, 4⟩

/-- info: { x := 2.000000, y := 4.000000 } -/
#guard_msgs in
#eval (2 : Float) * Vec2.mk 1 2

/-- info: "(1.000000, 2.000000)" -/
#guard_msgs in
#eval toString (Vec2.mk 1 2)

/-! `#eval` prefers `Repr` over `ToString` when both exist, which is why the first output
above has the `{ x := … }` form. `List.sum` needs `Add` and `Zero`, both now available: -/

/-- info: { x := 4.000000, y := 6.000000 } -/
#guard_msgs in
#eval [Vec2.mk 1 2, ⟨3, 4⟩].sum

/-! Numeric literals are resolved through `OfNat α n`, indexed by the type *and* the
literal. Without an instance for `1`, `(1 : Vec2)` is an error, and the message explains
the mechanism: -/

/--
error: failed to synthesize instance of type class
  OfNat Vec2 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Vec2
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval (1 : Vec2)

/-! The literal `0` is the exception: the `Zero Vec2` instance above provides `OfNat Vec2 0`
automatically, which is what lets generic code write `0` for "the zero of `α`" below. -/

/-- info: { x := 0.000000, y := 0.000000 } -/
#guard_msgs in
#eval (0 : Vec2)

/-! ## 5. Generic algorithm

With the classes as vocabulary, one function serves every type that has the operations.
-/

def sumAll {α : Type} [Add α] [Zero α] (xs : List α) : α := xs.foldl (· + ·) 0

/-- info: 6 -/
#guard_msgs in
#eval sumAll [1, 2, 3]

/-- info: 4.000000 -/
#guard_msgs in
#eval sumAll [1.5, 2.5]

/-- info: { x := 4.000000, y := 6.000000 } -/
#guard_msgs in
#eval sumAll [Vec2.mk 1 2, ⟨3, 4⟩]

/-! When the element type cannot be inferred, instance search cannot even start. The
message says the problem is "stuck" on a metavariable, and the fix is an annotation such
as `sumAll ([] : List Nat)`: -/

/--
error: typeclass instance problem is stuck
  Zero ?m.7

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Zero` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
example := sumAll []

/-! ## 6. Exact arithmetic with `Rat`

Lean's core library includes `Rat`, exact rational numbers. Literals and `/` work on
it, and unlike `Float` (lesson 01) its arithmetic is exact. The Butcher tableaux of the
explicit methods used in this course (Euler, Heun, RK4) and the Newton–Cotes
quadrature weights are rational, so this is the right type for checking them. (Not every
tableau is: Gauss–Legendre methods have entries such as `√3 / 6`.) -/

/-- info: (1 : Rat)/2 -/
#guard_msgs in
#eval (1 : Rat) / 3 + 1 / 6

/-- info: true -/
#guard_msgs in
#eval (0.1 : Rat) + 0.2 == 0.3

/-- info: (3 : Rat)/10 -/
#guard_msgs in
#eval (0.1 : Rat) + 0.2

/-- info: 1 -/
#guard_msgs in
#eval sumAll [(1 : Rat) / 2, 1 / 3, 1 / 6]

/-! ## 7. Derive an instance

For the standard classes on your own inductive types, `deriving` writes the instances:
`Repr` (printing), `BEq` (`==`), `DecidableEq` (`=` decidable, enables `decide`),
`Hashable`, `Inhabited` (a `default` value, which satisfies the `Nonempty` requirement of
`partial def` and is needed by `a[i]!`), `Ord` (`compare`). -/

inductive Color where
  | red
  | green
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited, Ord

/-- info: L03.Color.red -/
#guard_msgs in
#eval (default : Color)

/-- info: Ordering.lt -/
#guard_msgs in
#eval compare Color.red Color.green

/-! ## 8. Notation

You can define operators. `infixl:70` is a left-associative infix operator with
precedence 70 (the precedence of `*`; `+` is 65, function application binds tightest).
`notation` handles arbitrary mixfix shapes.

The `scoped` keyword restricts the notation to this namespace (active inside
`namespace L03` and after `open L03`). Unscoped notation is global, and Mathlib already
uses `‖·‖` for norms, so a global definition here would clash with it in Part III. -/

def Vec2.dot (v w : Vec2) : Float := v.x * w.x + v.y * w.y

def Vec2.norm (v : Vec2) : Float := Float.sqrt (v.dot v)

scoped infixl:70 " ⋅ " => Vec2.dot

scoped notation "‖" v "‖" => Vec2.norm v

/-- info: 11.000000 -/
#guard_msgs in
#eval Vec2.mk 1 2 ⋅ Vec2.mk 3 4

/-- info: 5.000000 -/
#guard_msgs in
#eval ‖Vec2.mk 3 4‖

/-! ## 9. A Butcher tableau, as data

A preview of where this course goes. A Runge–Kutta method is determined by its Butcher
tableau `(A, b, c)`. With `Rat` entries the consistency conditions `Σⱼ aᵢⱼ = cᵢ` and
`Σ bᵢ = 1` are exact computations, and `#guard` checks them at compile time. Lesson 11
checks the order conditions of RK4 the same way, and lesson 17 *proves* them. -/

structure Tableau where
  a : Array (Array Rat)
  b : Array Rat
  c : Array Rat
  deriving Repr

/-- The classical fourth-order Runge–Kutta method. -/
def rk4 : Tableau where
  a := #[#[0, 0, 0, 0], #[1/2, 0, 0, 0], #[0, 1/2, 0, 0], #[0, 0, 1, 0]]
  b := #[1/6, 1/3, 1/3, 1/6]
  c := #[0, 1/2, 1/2, 1]

/-- Row-sum condition: every row of `a` sums to the corresponding entry of `c`. -/
def Tableau.rowSumOk (t : Tableau) : Bool :=
  (t.a.zip t.c).all fun (row, ci) => row.foldl (· + ·) 0 == ci

#guard rk4.rowSumOk && rk4.b.foldl (· + ·) 0 == 1

/-- info: #[(1 : Rat)/6, (1 : Rat)/3, (1 : Rat)/3, (1 : Rat)/6] -/
#guard_msgs in
#eval rk4.b

/-! Note the literals: `1/2` inside `#[…]` became a `Rat` because the field type says so.
The same text in a `Nat` context would be `0` (lesson 01). -/

/-! ## 10. Pitfall for the C, Fortran, or Python programmer

* Implicit `{α}` arguments are inferred from *other arguments*; if nothing determines
  them, Lean reports "don't know how to synthesize implicit argument" or a typeclass
  problem "stuck" on a metavariable `?m.N` (sections 1 and 5). Add an annotation or use
  `@f`.
* Instance arguments `[C α]` are found by search, not passed at call sites. If Lean
  cannot find one, write the instance; passing one by hand through `@f` is possible but
  is the exception. A bracket binder `[C α]` has no name, so `(inst := …)` does not
  work unless you write `[inst : C α]`.
* `Type` is not a `Type`. If you ever need "a type of types", that is `Type 1`.
* Literals are per type: `(1 : Vec2)` fails unless you write an `OfNat Vec2 1` instance.
  Conversely, `1/2` is `Rat` or `Float` only if the context says so.
* `Float` has no `Ord`, so `deriving Ord` fails on a structure with a `Float` field
  (lesson 02, section 1).
* `#eval` prints with `Repr` when it can; your `ToString` is used by `s!"…"` and
  `toString`.
* Unscoped `notation` is global and leaks into every file that imports yours. Prefer
  `scoped`.
* `==` on `Rat` is exact equality; `==` on `Float` is IEEE equality (lesson 01,
  section 2).

## Exercise

Open `Exercise/E03_TypeClass.lean`. -/

end L03
