# tutorial-lean

Self-paced Lean 4 course for Yifan, written lesson by lesson with Claude. The lesson
files are re-read later, so their prose is a deliverable, not a comment.

## Toolchain policy

- `lean-toolchain` pins the Lean release. The Mathlib `rev` in `lakefile.toml` must be
  the Mathlib tag with the same name (Mathlib `vX.Y.Z` is built with Lean `vX.Y.Z`).
- Bump both together: edit both files, run `lake update`, then `lake exe cache get`,
  then `lake build`. Commit `lake-manifest.json`. Never depend on Mathlib `master`.
- `lake update`, `lake exe cache get`, and a first-time toolchain install need network
  and write outside the repo (`~/.elan`, `~/.cache/mathlib`). `lake build` does not.
- Lessons 01–12 import core Lean only, so they build without the Mathlib cache.
- `.lake/build` keeps output under old module names after a rename; `lake clean`
  removes it.

## Layout and name

- `Tutorial/L0N_Topic.lean`: lesson N, everything inside `namespace L0N`.
- `Exercise/E0N_Topic.lean`: stubs for lesson N, inside `namespace E0N`; starts with
  `import Tutorial.L0N_Topic` and `open L0N`. The solution file opens `L0N` too.
- `Solution/S0N_Topic.lean`: reference answers, inside `namespace S0N`.
- `Tutorial.lean`, `Exercise.lean`, `Solution.lean` import every file of their
  library. A new file is not built until its `import` line is added there.
- Module names are identifiers: no leading digit, no hyphen. Numbering goes in the
  `L0N_` prefix, not in a folder name.

## Name style

Yifan's preference, applied to every name in this project: **single-form nouns and
base-form verbs**. A name is a directory, file, Lake library, module, namespace, Lean
declaration, binder, or heading (file title, section title, table column).

- Nouns are singular: `Exercise/`, `Solution/`, `script/`, `L02_InductiveType`,
  `Vec2.norm`, `digitList`, `stageCount`. For "a number of X" write `xCount`; for "a
  list of X" write `xList` or a singular collective (`poly`, `tableau`).
- Verbs are in base form, in names and in headings: `L01_GetStarted`, `## Define a
  function`, `## Derive an instance`, `## Troubleshoot`, not `GettingStarted`,
  `Defining`, `Deriving`, `Troubleshooting`. Table columns and statuses follow suit:
  `Topic` not `Covers`, `done` / `to do` not `written` / `planned`.
- Two Lean idioms stay as they are because the core library uses them: the `is` prefix
  on `Bool` predicates (`isEven`, `isExplicit`, like `List.isEmpty`), and the plural
  list variables `xs`, `ys`, `ps` (like `x :: xs`). Class names drop `Has`: `Area`, not
  `HasArea`, like `Zero` and `Repr`.
- Running prose inside a paragraph stays grammatical ("the decimal digits of `n`");
  the rule is about names, not sentences.

## Lesson rule

- Lesson text goes in `/-! ... -/` module doc comments (Markdown). Short, concrete,
  numerics-flavoured examples; one idea per section; a pitfall section for readers
  coming from C, Fortran, and Python.
- Every output shown in a lesson is pinned: `#guard <bool>` for values, or
  `/-- info: ... -/ #guard_msgs in #eval ...` for printed output, so the text cannot
  drift from what Lean actually does. `script/check.sh` enforces this for `#eval`,
  `#check`, `#print`, `#synth`, `#reduce`.
- An exercise is a numbered docstring with a hint that names the idea or the section,
  never the answer, a `def`/`theorem` stub ending in `sorry`, and zero or more commented
  checks that the learner uncomments when done: a `-- #guard …` line, a `-- example …`
  line, or a whole commented `#guard_msgs` block. A theorem exercise is its own check.
  Evaluating a term that depends on `sorry` is an error, which is why the checks start
  commented. An exercise must not be a verbatim copy of lesson code.
- A solution file mirrors its exercise file declaration for declaration, with `sorry`
  replaced and the checks active. Keep the two files in sync when editing either.
- `Tutorial` and `Solution` contain no `sorry`. Both are built with
  `warningAsError = true`.
- `autoImplicit = false` stays on. Parts I and II import core Lean only; Mathlib starts
  at lesson 13. Do not use the `module` / `public import` system in lesson files.
- Fix deprecation warnings by using the new name; never silence them.
- Probe a claim about Lean's behaviour with `lake env lean` on a scratch file before
  writing it as prose; unpinned prose is where errors hide.

## Verification before every commit

```bash
lake build && script/check.sh
```

`script/check.sh` is the test entry point until lesson 12 wires up `lake test`. A
pinned message that quotes a line number (lesson 02, `gcdNaive`) shifts whenever lines
are added above it; the build reports the new number.

Both must pass. `Exercise` may only warn with ``declaration uses `sorry` ``.

## Lesson loop

- The learner works in `Exercise/`. Claude checks with `lake build`, explains, and
  then writes the next lesson. Progress and status live in the README roadmap table;
  flip a lesson's status to `done` when it lands.
- Reset one exercise file with `git restore Exercise/E0N_Topic.lean`.

## Git

- Stage files explicitly (`git add <paths>`), never `git add -A`.
- Small, review-ready commits that each build. Conventional Commits
  (`feat:`, `docs:`, `chore:`, `fix:`, `refactor:`).
- Never push. Never commit `.lake/`.
