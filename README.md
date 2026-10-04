# Learn Lean 4

A self-paced course in Lean 4 for a scientific-software engineer, written lesson by
lesson together with Claude. Each lesson is a literate `.lean` file: read it in VS Code,
where every `#eval` shows its result live, then work through the matching exercise file.

The course runs from zero to verifying numerical methods with Mathlib. Part I treats Lean
as a functional programming language, Part II as a proof assistant, and Part III adds
Mathlib and ends with a formal proof of the order conditions of the classical
fourth-order Runge–Kutta method.

## Setup

1. **elan**, the Lean version manager: see <https://lean-lang.org/install/>. The Lean
   release pinned in `lean-toolchain` is installed automatically the first time `lake`
   runs in this directory (network required), or explicitly with
   `elan toolchain install leanprover/lean4:v4.34.1`.
2. **VS Code** with the Lean 4 extension:

   ```bash
   code --install-extension leanprover.lean4
   ```

3. **Mathlib's build cache**, needed from lesson 13 on; lessons 01–12 build without it.
   The cache keeps Mathlib from being compiled from source (that takes hours). About
   1.3 GB is downloaded and about 7.6 GB unpacked under `.lake/` (measured with Mathlib
   v4.34.1):

   ```bash
   lake exe cache get
   ```

4. Build everything:

   ```bash
   lake build
   ```

   Lessons and solutions compile without warnings. Each open exercise reports
   ``declaration uses `sorry` ``; that is expected.

Open the **repository root folder** in VS Code, not a single file: the extension looks
for `lean-toolchain` and `lakefile.toml` at the workspace root.

## How to study

1. Read `Tutorial/L0N_Topic.lean` top to bottom with the infoview open
   (`Cmd+Shift+Enter` on macOS, `Ctrl+Shift+Enter` elsewhere). Put the cursor on `#eval`
   and `#check` lines and read the result. To try a variation, add a line of your own
   below the block: the shown lines are pinned to their output, so editing one gives a
   mismatch error. `git restore Tutorial/` undoes experiments. The lesson text is in the
   `/-! … -/` comments; the code between them is the worked examples.
2. Open `Exercise/E0N_Topic.lean`. Replace each `sorry`, then uncomment the check below
   it: a `-- #guard …` line, a `-- example …` line, or a whole commented `#guard_msgs`
   block (`Cmd+/` toggles the selection). A theorem with no check is its own check.
   No red squiggles means done.
3. Compare with `Solution/S0N_Topic.lean`.
4. To start an exercise file over: `git restore Exercise/E0N_Topic.lean`.

From a terminal, `lake build` checks everything at once, and `script/check.sh` runs the
build plus the repository's consistency checks.

## Roadmap

### Part I · Lean as a functional language (core Lean only)

| # | Lesson | Status | Topic |
|---|--------|--------|-------|
| 01 | [Get started](Tutorial/L01_GetStarted.lean) | done | VS Code workflow, `#eval`/`#check`/`#print`, `Nat`/`Int`/`Float` semantics, function, currying, lambda, list and pipeline, string, namespace, read an error |
| 02 | [Inductive type and recursion](Tutorial/L02_InductiveType.lean) | done | `structure`, `inductive`, pattern match, `Option`, structural recursion, `termination_by`/`decreasing_by`, fuel, `partial` |
| 03 | [Polymorphism and type class](Tutorial/L03_TypeClass.lean) | done | implicit argument, universe, `class`/`instance`, the standard operator class, generic code, exact `Rat`, `deriving`, `scoped` notation, a Butcher tableau as data |
| 04 | [Dependent type](Tutorial/L04_DependentType.lean) | done | `Vector α n`, dependent function type, `Fin n`, `Prop` vs `Type`, `Decidable`, `if h : …`, index safely with `omega`, `Subtype`, a Butcher tableau with its stage count in the type |
| 05 | [IO and monad](Tutorial/L05_Monad.lean) | done | `IO`, `do`, `let mut`, `for`, `Id.run`, `Option`/`Except`/`StateM` as monads, `StateT` over `IO`, an RK4 command-line program with its convergence table |

### Part II · Proposition and proof (core Lean only)

| # | Lesson | Status | Topic |
|---|--------|--------|-------|
| 06 | [Proposition as type](Tutorial/L06_Proposition.lean) | done | `Prop`, `theorem`/`example`/`variable`, `→ ∧ ∨ ¬ ↔ ∀ ∃` with term-mode proof, `rfl` and bounded `decide`, why an `∃` witness cannot be extracted, `#print axioms` |
| 07 | [Tactic I](Tutorial/L07_Tactic.lean) | done | the goal state via `trace_state`, `intro exact apply refine constructor left right exists cases rcases obtain rintro have show specialize assumption exfalso contradiction omega by_cases exact? apply?`, `·` bullet and `<;>`, most tactics next to the lesson 06 term they abbreviate |
| 08 | [Interlude: read an error, debug a proof](Tutorial/L08_Debug.lean) | done | a field guide of pinned messages: type mismatch, `Function expected`, coercion `↑`, instance failure, metavariable and `?_`, missing or extra tactic, a `def` in the way (`unfold`, `show`, `Decidable`), the four ways `decide` fails and `decide +kernel`, `rfl`, `pp.explicit`, `simp?`, a recipe to debug a proof |
| 09 | [Equality and rewrite](Tutorial/L09_Equality.lean) | done | definitional vs propositional `=`, `rfl`, `rw` and `rw … at`, library lemma name, `simp`/`simp only`/`simp?`/`@[simp]`, `calc` with mixed `≤` and `<`, `omega` for an equation and its nonlinear limit, `congrArg`/`congrFun`/`funext`, `subst` and `▸` |
| 10 | Induction | to do | `induction … with` on `Nat` and `List`, `fun_induction`, correctness of a recursive function, strong induction |
| 11 | Verify a program | to do | a specification as `Prop`, exact `Rat` checks of the RK4 order conditions, `decide` vs `decide +kernel` vs `native_decide` as a trust decision (lesson 08 showed the mechanics) |
| 12 | Interlude: project hygiene | to do | docstring, `#guard_msgs`, `lake test`/`lake lint`, linter, `warningAsError`, axiom audit, update Mathlib |

### Part III · Mathlib for numerics

| # | Lesson | Status | Topic |
|---|--------|--------|-------|
| 13 | Get started with Mathlib | to do | `import Mathlib`, `ℕ ℤ ℚ ℝ`, coercion, find a lemma (Loogle, `exact?` with Mathlib), name convention, `Finset.sum` |
| 14 | ℚ, ℝ and the algebra tactic | to do | `ring field_simp norm_num linarith nlinarith positivity gcongr`, quadrature weight identities, order-2 conditions of two-stage RK methods |
| 15 | Elementary real analysis | to do | `|x|`, limits via `Filter.Tendsto`, ε–δ, derivatives, Taylor's theorem; the local error of Euler's method is O(h²) |
| 16 | Linear algebra | to do | `Matrix (Fin n) (Fin n) ℝ`, `![…]`, `*ᵥ`, `⬝ᵥ`, `det` |
| 17 | Capstone: RK4 order condition | to do | the eight Butcher conditions through order 4 for RK4 over ℚ, proved in Lean; the stability polynomial as a stretch goal |

## Layout

```
Tutorial/    L0N_Topic.lean   lessons, inside `namespace L0N`; built with warningAsError
Exercise/    E0N_Topic.lean   your workspace, inside `namespace E0N`; `sorry` allowed
Solution/    S0N_Topic.lean   reference answers, inside `namespace S0N`; built with warningAsError
Tutorial.lean  Exercise.lean  Solution.lean   root modules importing every file of their library
script/check.sh                                the test entry point: build plus consistency checks
lakefile.toml  lean-toolchain  lake-manifest.json   Lake project; Mathlib pinned to the toolchain's tag
```

Lean module names are identifiers, so the numbering lives in the `L0N_` prefix rather
than in folder names such as `01-getting-started/`. Every output shown in a lesson is
pinned with `#guard` or `#guard_msgs`, which means the text is checked against the Lean
version in `lean-toolchain` on every build. Authoring rules for new lessons are in
[CLAUDE.md](CLAUDE.md).

## Troubleshoot

- **Infoview empty or stale.** Click inside the file. After changing imports, run
  *Lean 4: Restart File* from the command palette.
- **Mathlib missing or a message about the manifest.** Run `lake exe cache get` after
  cloning. `lake update` is only for bumping versions; see `CLAUDE.md`.
- **`lake build` starts compiling hundreds of Mathlib files.** The cache was not used.
  Stop it, run `lake exe cache get!`, then build again.
- **Everything broken.** `rm -rf .lake`, then `lake exe cache get && lake build`.

## Reference

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), the companion book for Part I
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), the companion book for Part II
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), for Part III
- [Lean Language Reference](https://lean-lang.org/doc/reference/latest/)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) and [Loogle](https://loogle.lean-lang.org/) for finding lemmas
- [Lean Zulip chat](https://leanprover.zulipchat.com/), where questions get answered quickly
- [Live Lean editor](https://live.lean-lang.org/) for trying things without a project

## License

GPL-3.0, see [LICENSE](LICENSE).
