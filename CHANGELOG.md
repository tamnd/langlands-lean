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
- `Langlands/Ported/NYLL/`: the port of finite abelian local reciprocity from n-yamaguchi-0729/ClassFieldTheory at commit fc644f4. These are the 327 files of the import closure of `ClassFieldTheory.finiteAbelianLocalReciprocity`, with the Mathlib names of v4.35.0. The entry `nyll` of `manifests/ported.yaml` lists the changes.
- `Langlands/Bridge/NYLL.lean`: `finiteAbelianLocalReciprocity` for a finite abelian extension in an algebraic closure, with the kernel given by `Langlands.normGroup`. This is the first theorem of the project with a full proof.
- `Langlands/Fidelity/ClassField.lean`: the checks F2 and F3 for the class field statements. `LocalReciprocityGL1` implies finite abelian local reciprocity (F2). Without the condition at a uniformizer the local reciprocity map is never unique, and this proof uses no hypothesis (F3). A map is a geometric Artin map if and only if its composite with inversion is an arithmetic Artin map (F3).
- `Langlands/Fidelity/Modularity.lean`: `ModularityEllipticQ` implies `ModularitySemistableQ` (F2), and `SatoTate` contradicts the variant with the uniform measure (F3).
- `Langlands/Fidelity/ClassField.lean` and `Langlands/Fidelity/Modularity.lean`: the positive instances `isArtinMap_bot` for `GlobalReciprocity` and `satoTate_full` for `SatoTate`.
- `Langlands/Bridge/FormalConjectures.lean`: the bridge `satoTate_conjecture_of_satoTate` from `SatoTate` to the Sato-Tate statement of formal-conjectures, with the hypotheses `ApAgree` and `HasseBound`, and the bridge `ramanujan_petersson_of_ramanujanPeterssonHolomorphic` from `RamanujanPeterssonHolomorphic` to the statement for $\tau$, with the hypothesis `DeltaIsEigenform`.
- `manifests/statements.sha256`: the hashes of the three files of `Langlands/Statements/`. The workflow `check` now compares them (check F7 of spec 06.3).

### Changed

- `formalization.yaml` uses the key `BLGHT11` for the paper of Barnet-Lamb, Geraghty, Harris and Taylor.
- `formalization.yaml` lists the sources of the modularity statements, the copied statements of formal-conjectures, the classification and the status of each main result.

## v0.0.1 (2026-11-25)

### Added

- The package `Langlands` on Lean v4.35.0 and Mathlib v4.35.0.
- The workflows `build`, `check`, `trust` and `scorecard`, and the scripts `Export.lean`, `Decls.lean`, `axioms.py`, `scan.sh` and `style.py`.
- `Langlands/Statements/Basic.lean`: the Weil group `WeilGroup K` of a nonarchimedean local field as a subgroup of the absolute Galois group, its topology, the inertia subgroup, `IsGeometricFrobenius`, the abelianization `WeilGroup.Ab` and the restriction to a finite abelian extension. The file has no `sorry`.
- `Langlands/Statements/ClassField.lean`: the statements `LocalReciprocityGL1`, `LocalExistence`, `GlobalReciprocity`, `GlobalExistence` and `KroneckerWeber`, with the structures `IsLocalArtinMap` and `IsArtinMap` in the geometric normalization.
