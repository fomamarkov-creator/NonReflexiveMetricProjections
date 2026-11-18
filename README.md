# Linear Metric Projections and Discretization in Non-Reflexive Banach Spaces (Lean 4)

Formal machine verification in **Lean 4** (using Mathlib) by **E. S. Markov** of analytical, geometric, and combinatorial results on continuous linear selections of multivalued metric projections in non-reflexive Banach spaces.

## Associated Publications & Zenodo Archives

1. **Part 1:** DOI: `10.5281/zenodo.24318041` (Concept DOI: `10.5281/zenodo.24247032`).
2. **Part 2:** DOI: `10.5281/zenodo.24250160`.

## Mathlib4 Upstream Pull Requests (`leanprover-community/mathlib4`)

- **`#46189`** — `Mathlib/Analysis/Normed/Module/Proximinal.lean`
- **`#46191`** — `Mathlib/Analysis/Normed/Module/BirkhoffOrthogonality.lean`
- **`#46193`** — `Mathlib/Topology/ContinuousMap/Kolmogorov.lean`
- **`#46194`** — `Mathlib/MeasureTheory/Function/L1Space/Projection.lean`
- **`#46195`** — `Mathlib/Analysis/Normed/Module/HybridDiscretization.lean`

## Repository Structure & Build

- **Files:** `NonReflexiveProjections/NonReflexiveProjections_v3.lean`, `NonReflexiveProjections/HybridDiscretizationVerification.lean`, and modules in `MathlibPR/`.
- **Build:** Verified without `sorry` or custom axioms (`lake exe cache get`, `lake build`).
- **License:** Dual-licensed under GNU AGPL-3.0 and Apache License 2.0.
