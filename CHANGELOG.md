# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- `Langlands/Statements/Modularity.lean`: the statements `ModularityEllipticQ`, `ModularitySemistableQ`, `HasseWeilEllipticQ`, `RamanujanPeterssonHolomorphic` and `SatoTate`, with the structure `IsNormalizedEigenform` and the predicate `HasCMOverQ`. The coefficients of an elliptic curve come from `WeierstrassCurve.LFunction` in Mathlib, and the coefficients of a cusp form come from its $q$-expansion.

- `Langlands/Fidelity/ClassField.lean`: the positive instances `localExistence_top` and `kroneckerWeber_bot`, and the lemma `normGroup_bot`.
- `Langlands/Fidelity/Modularity.lean`: the total mass of the Sato-Tate measure, the CM curve $y^2 = x^3 - x$ and the curve $X_0(11)$ without CM.
- `Langlands/Ported/FormalConjectures/Wikipedia.lean`: the statements of modularity, Sato-Tate, Ramanujan-Petersson for $\tau$ and Hasse-Weil from formal-conjectures at commit 9097e2f, as `def ... : Prop`.
- `Langlands/Bridge/FormalConjectures.lean`: `HasseWeilEllipticQ` implies the Hasse-Weil statement of formal-conjectures over $\mathbb{Q}$. The statement `modularity_conjecture` of formal-conjectures is false as stated, because it reads the coefficients in the parameter $q_N$ and not in $q_1$ (`not_modularity_conjecture`).
- `manifests/ported.yaml`: the record of each ported source.

## v0.0.1 (2026-11-25)

### Added

- The package `Langlands` on Lean v4.35.0 and Mathlib v4.35.0.
- The workflows `build`, `check`, `trust` and `scorecard`, and the scripts `Export.lean`, `Decls.lean`, `axioms.py`, `scan.sh` and `style.py`.
- `Langlands/Statements/Basic.lean`: the Weil group `WeilGroup K` of a nonarchimedean local field as a subgroup of the absolute Galois group, its topology, the inertia subgroup, `IsGeometricFrobenius`, the abelianization `WeilGroup.Ab` and the restriction to a finite abelian extension. The file has no `sorry`.
- `Langlands/Statements/ClassField.lean`: the statements `LocalReciprocityGL1`, `LocalExistence`, `GlobalReciprocity`, `GlobalExistence` and `KroneckerWeber`, with the structures `IsLocalArtinMap` and `IsArtinMap` in the geometric normalization.
