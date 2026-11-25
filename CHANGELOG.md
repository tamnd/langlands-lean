# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- The package `Langlands` on Lean v4.35.0 and Mathlib v4.35.0.
- The workflows `build`, `check`, `trust` and `scorecard`, and the scripts `Export.lean`, `Decls.lean`, `axioms.py`, `scan.sh` and `style.py`.
- `Langlands/Statements/Basic.lean`: the Weil group `WeilGroup K` of a nonarchimedean local field as a subgroup of the absolute Galois group, its topology, the inertia subgroup, `IsGeometricFrobenius`, the abelianization `WeilGroup.Ab` and the restriction to a finite abelian extension. The file has no `sorry`.
- `Langlands/Statements/ClassField.lean`: the statements `LocalReciprocityGL1`, `LocalExistence`, `GlobalReciprocity`, `GlobalExistence` and `KroneckerWeber`, with the structures `IsLocalArtinMap` and `IsArtinMap` in the geometric normalization.
