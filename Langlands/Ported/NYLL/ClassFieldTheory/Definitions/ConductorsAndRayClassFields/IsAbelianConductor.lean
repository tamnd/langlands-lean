/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/IsAbelianConductor.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField

/-!
# Conductors of finite abelian extensions
-/



@[expose] public section

namespace ClassFieldTheory

universe u v

/-- A modulus is the conductor of a finite abelian extension when it is
exactly the least modulus whose ray class field contains the extension. -/
def IsAbelianConductor
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (c : RayClassModulus K) : Prop :=
  ∀ m : RayClassModulus K,
    EmbedsInRayClassField K L m ↔ c ≤ m

end ClassFieldTheory
