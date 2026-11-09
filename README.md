# HY conjecture proofs

HY results for six problems in *Open Problems in Commutative Ring Theory*, with subsequent Lean formalizations tracked separately.

| Problem | Topic | Text review | Lean |
|---|---|---|---|
| [5a](problem_05a/) | Group-ring global dimension | Reviewed | Full formalization verified (2026-11-09) |
| [32b](problem_32b/) | Two-v-generated Mori domains | Reviewed | Full formalization verified (2026-11-09) |
| [37c](problem_37c/) | Intermediate subalgebras and the locally Jaffard property | Reviewed | Not yet formalized |
| [41](problem_41/) | Normality of monomial ideals | Reviewed | Full formalization verified (2026-11-09) |
| [43](problem_43/) | A relaxation of the Lipman–Sathaye theorem | Reviewed | Partial local formalization; [full target pending](reports/2026-11-09-followup.md) |
| [44](problem_44/) | A surface with no one-fibered primary ideals | Reviewed | Not yet formalized |

Each directory contains the evaluation problem, the HY result, and its scope and references. These include counterexamples, an algorithmic classification, a relaxation of a theorem, and a geometric construction. No blanket claim of new resolutions of six open problems is made.

Lean projects separate the mathematical specification from the proof. Kernel checking establishes the formal theorem; correspondence of the specification with the written problem is reviewed separately. Complete formalization requires the full target and all necessary dependencies, without unproved axioms.
