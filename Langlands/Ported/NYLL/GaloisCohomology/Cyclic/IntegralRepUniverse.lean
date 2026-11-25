/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

/-!
# Universe boundary for integral group cohomology

Mathlib's `Rep` permits independent universes for the coefficient ring, acting
group, and representation carrier. The group cohomology, group homology, and
Tate cohomology APIs used here instead share a universe for the coefficient
ring and acting group. With the actual coefficient ring `ℤ : Type 0`, those
APIs require the group in `Type 0`. This named boundary records that constraint
for the integral cohomology constructions and their class field theory users.
The `IntegralGroupCohomology` API in `IntegralCoefficientCohomology` instead
transports the same representation to `ULift.{u} ℤ`, uses the native complexes,
and restricts the result back to integers. It includes proved comparisons with
this original API in universe zero. This alias remains the boundary for users
that still explicitly request the native literal-integer cohomology objects.
-/


@[expose] public section

/-- The universe-zero group boundary used by integral group and Tate cohomology. -/
abbrev IntegralRepGroupType := Type 0
