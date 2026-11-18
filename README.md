# Linear Metric Projections and Discretization in Non-Reflexive Banach Spaces (Lean 4)

Formal machine verification in **Lean 4** (using `Mathlib`) of the analytical, geometric, and combinatorial results on continuous linear selections of multivalued metric projections in non-reflexive Banach spaces ($L_1(\Omega)$, $C(K)$, hybrid spaces $L_1(\Omega, \Sigma, \mu) \oplus \ell_1(\mathbb{N})$, and $\ell_1^m$).

## Author
* **E. S. Markov** (Independent Researcher, Astrakhan, Russian Federation)
* **ORCID:** [0009-0005-2235-5464](https://orcid.org)

## Associated Publications & Zenodo Archives
1. **Part 1 (Proximinal Lattices & Linear Selections):**  
   *On Linear Metric Projections in Non-Reflexive Banach Spaces: Proximinal Lattices, Multivalued Boundaries and Linear Selections* (2026).  
   Zenodo Code Archive: [DOI: 10.5281/zenodo.24318041](https://doi.org) (Concept DOI: `10.5281/zenodo.24247032`).
2. **Part 2 (Hybrid Spaces, Quantization & NP-Hardness):**  
   *On Discretization of Linear Selections in Non-Reflexive Spaces: Hybrid Spaces, Operator Stability and Combinatorial Complexity of Null Layers* (2026).  
   Zenodo Code Archive: [DOI: 10.5281/zenodo.24250160](https://doi.org).

## Repository Structure
* `NonReflexiveProjections/BasicProjections.lean` — Proximinal subspaces, consistent selector lattices, Deutsch's splitting theorem, Birkhoff–James orthogonality criteria in $L_1(\Omega)$, Kolmogorov's criterion in $C(K)$, and global Lipschitz stability bounds via mutual inclination $\delta(V, U)$.
* `NonReflexiveProjections/HybridDiscretization.lean` — Joint sign-weighted integral-discrete criteria in $L_1(\Omega) \oplus \ell_1(\mathbb{N})$, finite-precision operator quantization bounds, pipeline perturbation stability, polynomial-time reductions from `Subset-Sum` and `Partition`, and explicit matrix verification in $\ell_1^8$.

## Verification & Build Instructions
All theorems are proven completely without `sorry` or custom axioms. To build the project locally:

```bash
lake exe cache get
lake build
```

## License
This repository is dual-licensed:
* **Primary License:** [GNU Affero General Public License v3.0 (AGPL-3.0)](LICENSE) — in alignment with the associated Zenodo archival releases.
* **Alternative License (for Mathlib4 integration):** [Apache License, Version 2.0](https://apache.org) — at your option, you may use, modify, and upstream any part of this code into `leanprover-community/mathlib4` or other Lean 4 projects under the terms of the Apache License 2.0.
* 
