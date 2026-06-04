# Logika v Računalništvu — Project

Solution to the LVR project (Problems 1–12), written in Agda, with
study notes covering the underlying theory and tests for every
computational component.

## Layout

```
exercise-project/
├── project.pdf                -- the project handout
├── README.md                  -- you are here
├── src/
│   ├── Solution.agda          -- ALL TWELVE problems, in order
│   └── Tests.agda             -- refl-tests for problems 3–12
└── notes/
    ├── 00-agda-intro.md       -- just enough Agda to read the rest
    ├── 01-formulas.md         -- Problem 1.      Propositional formulas
    ├── 02-nnf.md              -- Problems 2, 3.  NNF and to-nnf
    ├── 04-assignments.md      -- Problems 4–6.   Assignments and evaluation
    ├── 07-cnf.md              -- Problems 7, 8.  CNF and its evaluator
    ├── 09-sat.md              -- Problem 9.      DPLL-style SAT solver
    ├── 10-sat-correctness.md  -- Problem 10.     Why the solver is correct
    ├── 11-tseytin.md          -- Problem 11.     Tseytin transformation
    ├── 12-formula-sat.md      -- Problem 12.     SAT for any Formula
    └── problem{9,10,11,12}-visual.html  -- interactive visualisations
```

`src/Solution.agda` is intentionally the *single source of truth*: every
problem is solved there in order, with section banners and inline
comments. The `notes/` files are companion explanations — they introduce
the theory, justify design choices, and give worked examples that go
beyond what fits in code comments. Notes are numbered by the (first)
problem they cover.

## Mapping problems to code

| Problem | Asks for                                          | Defined in `Solution.agda`                       |
| ------- | ------------------------------------------------- | ------------------------------------------------ |
| 1 (\*)  | type `Formula`                                     | `Formula`                                        |
| 2 (\*)  | types `Literal`, `NNF`                             | `Literal`, `NNF`                                 |
| 3 (\*)  | `to-nnf : Formula → NNF`                           | `nnf⁺` / `nnf⁻`, `to-nnf`                        |
| 4 (\*\*)| a working associative structure for assignments    | `_∈ᴬ_`, `get`, `_∈ᴬ?_`, `Assignment`, `lookup`, `insert` |
| 5 (\*)  | `eval : Assignment → Formula → Maybe Bool`         | `eval`                                           |
| 6 (\*)  | `eval-nnf : Assignment → NNF → Maybe Bool`         | `eval-lit`, `eval-nnf`                           |
| 7 (\*)  | types `Disjunct`, `CNF`                            | `Disjunct`, `CNF`                                |
| 8 (\*)  | `eval-cnf : Assignment → CNF → Maybe Bool`         | `eval-disjunct`, `eval-cnf`                      |
| 9 (\*\*/\*\*\*) | SAT solver returning a model or "no model"  | `SatResult`, `sat-search`/`decide`/`try-assign`, `sat?` |
| 10 (\*\*)| show the solver is correct                        | `sat?-sound` + the comment block on completeness |
| 11 (\*\*/\*\*\*) | NNF → equisatisfiable CNF (Tseytin)        | `flip-lit`, `max-var`, `tseytin`, `to-cnf`       |
| 12 (\*) | SAT solver for any `Formula`                       | `FormulaSat`, `sat-formula?`, `solve`            |

Design highlights:

- The Problem 9 solver is **DPLL-style** (splitting + pure-literal rule
  + conflict pruning), and its result type carries a *proof*: `sat ρ p`
  contains `p : eval-cnf ρ φ ≡ just true`, so a found model is correct
  by construction (this is exactly what Problem 10 asks about).
- Problem 11 is the genuine Tseytin transformation: fresh variables
  above `max-var`, three biconditional clauses per internal node,
  linear output size.
- Problem 12 re-evaluates the solver's model on the *original* formula,
  so its `sat` answers carry a proof about `eval` — no formal Tseytin
  correctness theorem needed.

## Building and running the tests

Tested with **Agda 2.8.0** + the standard library that ships with the
Homebrew `agda` formula (`/opt/homebrew/opt/agda/share/agda/stdlib`).
Any reasonably recent stdlib (≥ 1.7) should work.

A project-local `lvr-project.agda-lib` declares `src/` as the include
path and `standard-library` as a dependency, so once stdlib is
registered globally, the build is a one-liner from the project root:

```sh
agda src/Solution.agda
```

The tests in `src/Tests.agda` are propositional equalities proved by
`refl`, so they *run at type-checking time* — checking the file is
running the tests:

```sh
agda src/Tests.agda
```

A clean exit means every test passed. The tests cover `to-nnf` (worked
examples, De Morgan, double negation), `lookup`/`insert`, all three
evaluators (including `nothing` propagation), the SAT solver on
satisfiable and unsatisfiable inputs (with the concrete model pinned
down), Tseytin equisatisfiability spot checks, and the full
`solve` pipeline.

If you have **never registered the standard library** with Agda before,
do it once: create (or append to) `~/.agda/libraries` with the line

```
/opt/homebrew/opt/agda/share/agda/stdlib/standard-library.agda-lib
```

(adjust the path to wherever your stdlib lives). After that the
commands above pick up the project's `lvr-project.agda-lib`
automatically. No language extensions or extra build flags are used.

If you don't want to touch `~/.agda`, you can also build directly:

```sh
agda --include-path=src --include-path=/opt/homebrew/opt/agda/share/agda/stdlib/src src/Solution.agda
```

## Reading order

If you are a reader rather than a grader, read top-to-bottom:

1. `notes/00-agda-intro.md` — enough Agda to follow along.
2. `notes/01-formulas.md` — what we are even talking about.
3. `notes/02-nnf.md` — first non-trivial transformation; introduces the
   recurring "two functions for two polarities" trick.
4. `notes/04-assignments.md` — gives semantics; explains why `eval`
   returns `Maybe Bool`.
5. `notes/07-cnf.md` — the clause-based representation.
6. `notes/09-sat.md` — the DPLL-style solver and its proof-carrying
   result type.
7. `notes/10-sat-correctness.md` — soundness from the type; honest
   discussion of completeness.
8. `notes/11-tseytin.md` — arbitrary NNF to linear-size CNF.
9. `notes/12-formula-sat.md` — the bow on top: SAT for any formula.

The notes deliberately overlap a little so each can be read on its own.

## Conventions in the Agda code

- `Formula` connectives are written `¬f_`, `_∧f_`, `_∨f_` (the `f` for
  *formula*) so they don't clash with `Bool`'s own `_∧_` / `_∨_`. NNF
  and CNF connectives use the suffixes `n`, `d`, `c` similarly.
- Variables are identified by `ℕ`. Any infinite type with decidable
  equality would do; `ℕ` is convenient and gives a free way to mint
  fresh identifiers in Tseytin (`suc (max-var φ)`).
- `Assignment` is a plain association list `List (ℕ × Bool)`, with a
  proof-relevant membership relation `_∈ᴬ_` backing `lookup`, and an
  `insert` that overwrites existing keys (so duplicates never arise in
  practice). The handout explicitly allows specialising the week-9
  `Assoc` interface to `K = ℕ`, `V = Bool`, which is what we do — in
  the simplest form that supports everything the later problems need.
- `eval`, `eval-nnf`, `eval-cnf` all return `Maybe Bool`: `nothing`
  when the assignment doesn't bind some variable of the formula. See
  `notes/04-assignments.md` for the design rationale.

## What is *not* here

Formal Agda proofs of three meta-theorems, which the project does not
ask for:

- `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)` (to-nnf preserves meaning),
- completeness of `sat?` (`unsat` answers are never wrong),
- equisatisfiability of `tseytin`.

Each is sketched informally in the corresponding note
(`02-nnf.md` §7, `10-sat-correctness.md` §3, `11-tseytin.md` §7), the
completeness obstacles are documented at length in the Problem 10
comment block in `Solution.agda`, and `src/Tests.agda` spot-checks all
three on concrete formulas.
