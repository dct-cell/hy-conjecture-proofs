# HY conjecture proofs

HY results for five problems in *Open Problems in Commutative Ring Theory*, with subsequent Lean formalizations tracked separately.

| Problem | Topic | Text review | Lean |
|---|---|---|---|
| [5a](problem_05a/) | Group-ring global dimension | Reviewed | Full formalization verified (2026-11-09) |
| [32b](problem_32b/) | Two-v-generated Mori domains | Reviewed | Full formalization verified (2026-11-09) |
| [41](problem_41/) | Normality of monomial ideals | Reviewed | Full formalization verified (2026-11-09) |
| [43](problem_43/) | A relaxation of the Lipman–Sathaye theorem | Reviewed | Partial local formalization; [full target pending](reports/2026-11-09-followup.md) |
| [44](problem_44/) | A surface with no one-fibered primary ideals | Reviewed | Partial local formalization; [full target pending](reports/2026-11-09-37c-44.md) |

Each directory contains the evaluation problem, the HY result, and its scope and references. These include counterexamples, an algorithmic classification, a relaxation of a theorem, and a geometric construction. No blanket claim of new resolutions of open problems is made.

Problem 37(c) was removed from the current collection because the cited preprint already supplies a negative answer. Its formalization work has stopped; the manuscript remains in Git history. [Source and withdrawal record](reports/2026-11-09-problem-37c-withdrawal.md).

Lean projects separate the mathematical specification from the proof. Kernel checking establishes the formal theorem; correspondence of the specification with the written problem is reviewed separately. Complete formalization requires the full target and all necessary dependencies, without unproved axioms.

[Citation review and fresh Lean checks (2026-11-09)](reports/2026-11-09-citation-review.md).
