# Logika v Računalništvu — Project

Solution to the LVR project (Problems 1–10), written in Agda, with extensive
study notes covering the underlying theory.

## Layout

```
exercise-project/
├── project.pdf            -- the project handout
├── README.md              -- you are here
├── src/
│   └── Solution.agda      -- ALL TEN problems, in order
└── notes/
    ├── 01-formulas.md     -- Problem 1.   Propositional formulas
    ├── 02-nnf.md          -- Problems 2,3.  NNF and the to-nnf conversion
    ├── 03-cnf.md          -- Problems 7,8.  CNF and its evaluator
    ├── 04-assoc.md        -- Problems 4,5,6. Assignments and evaluation
    ├── 05-sat.md          -- Problem 9.    SAT and DPLL
    └── 06-tseytin.md      -- Problem 10.   Tseytin transformation
```

`src/Solution.agda` is intentionally the *single source of truth* for the
project: every problem is solved there in order, with section banners and
inline comments. The `notes/` files are companion explanations — they
introduce the theory, justify design choices, and give worked examples that
go beyond what fits in code comments.

## Mapping problems to code

| Problem | Asks for                                       | Defined in `Solution.agda` (approx. line) |
| ------- | ---------------------------------------------- | ----------------------------------------- |
| 1 (\*)  | type `Formula`                                 | 33–52                                     |
| 2 (\*)  | types `Literal`, `NNF`                         | 54–71                                     |
| 3 (\*)  | `to-nnf : Formula → NNF`                       | 74–101                                    |
| 4 (\*\*)| `Assignment` (NoDup-backed Assoc)              | 104–219                                   |
| 5 (\*)  | `eval : Assignment → Formula → Maybe Bool`     | 222–240                                   |
| 6 (\*)  | `eval-nnf : Assignment → NNF → Maybe Bool`     | 244–260                                   |
| 7 (\*)  | types `Disjunct`, `CNF`                        | 264–285                                   |
| 8 (\*)  | `eval-cnf : Assignment → CNF → Maybe Bool`     | 289–302                                   |
| 9 (\*\*/\*\*\*) | `sat? : CNF → Bool`                    | 306–363                                   |
| 10 (\*\*/\*\*\*)| `tseytin : NNF → CNF`                  | 366–441                                   |

## Building

Tested with **Agda 2.8.0** + the standard library that ships with the
Homebrew `agda` formula (`/opt/homebrew/opt/agda/share/agda/stdlib`).
Any reasonably recent stdlib (≥ 1.7) should work.

A project-local `lvr-project.agda-lib` declares `src/` as the include
path and `standard-library` as a dependency, so once stdlib is
registered globally, the build is a one-liner from the project root:

```sh
agda src/Solution.agda
```

If you have **never registered the standard library** with Agda before,
do it once: create (or append to) `~/.agda/libraries` with the line

```
/opt/homebrew/opt/agda/share/agda/stdlib/standard-library.agda-lib
```

(adjust the path to wherever your stdlib lives). After that the
`agda src/Solution.agda` command above will pick up the project's
`lvr-project.agda-lib` automatically and find stdlib via the global
registration. No language extensions or extra build flags are used.

If you don't want to touch `~/.agda`, you can also build directly:

```sh
agda --include-path=src --include-path=/opt/homebrew/opt/agda/share/agda/stdlib/src src/Solution.agda
```

## Reading order

If you are a reader rather than a grader, read top-to-bottom in this order:

1. `notes/01-formulas.md` — what we are even talking about.
2. `notes/02-nnf.md` — first non-trivial transformation; introduces the
   recurring "two functions for two polarities" trick.
3. `notes/04-assoc.md` — gives semantics; explains why `eval` returns
   `Maybe Bool`.
4. `notes/03-cnf.md` — clause-based representation, plus a note on the
   typo in the project's CNF grammar.
5. `notes/05-sat.md` — SAT, DPLL, and what our solver actually does.
6. `notes/06-tseytin.md` — turns arbitrary NNF into linear-size CNF for
   the solver to chew on.

The notes deliberately overlap a little so each can be read on its own.

## Conventions in the Agda code

- `Formula` connectives are written `¬f_`, `_∧f_`, `_∨f_` (the `f` for
  *formula*) so they don't clash with `Bool`'s own `_∧_` / `_∨_`. NNF and
  CNF connectives use the suffixes `n`, `d`, `c` similarly.
- Variables are identified by `ℕ`. Any infinite type would do; `ℕ` is just
  convenient and gives us a free way to mint fresh identifiers in Tseytin.
- `Assignment` is specialised to a list of `(ℕ × Bool)` pairs bundled
  with a `NoDup` proof that no key appears twice — the week-9 `Assoc`
  module, completed. Keys are `ℕ`, decidable equality via `_≟_`.
- `eval`, `eval-nnf`, `eval-cnf` all return `Maybe Bool`: `nothing` when
  the assignment doesn't bind one of the variables in the formula. See
  `notes/04-assoc.md` for the design rationale.

## What is *not* here

The project does not ask for it, and we did not write it: formal Agda
proofs of the correctness theorems

- `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)`,
- `sat? φ ≡ true  ⇔  ∃ρ. eval-cnf ρ φ ≡ just true`,
- `(∃ρ. eval-nnf ρ φ ≡ just true)  ⇔  (∃σ. eval-cnf σ (tseytin φ) ≡ just true)`.

Each of these is sketched informally in the corresponding note, and would
be a natural follow-up exercise.
