/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/NarrowRayClassModulus.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# The narrow class-group modulus
-/



@[expose] public section

noncomputable section


namespace ClassFieldTheory

universe u

open scoped Classical in
/-- The modulus with no finite exponent and positivity at every real place.
Its ray class group is the narrow ideal class group. -/
def narrowRayClassModulus
    (K : Type u) [Field K] [NumberField K] : RayClassModulus K where
  finitePart := 0
  infinitePart := Finset.univ

end ClassFieldTheory
