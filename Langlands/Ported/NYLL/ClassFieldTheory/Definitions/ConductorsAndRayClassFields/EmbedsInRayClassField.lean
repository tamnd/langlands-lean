/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/EmbedsInRayClassField.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

/-!
# Embedding into a ray class field
-/



@[expose] public section

namespace ClassFieldTheory

universe u v

/-- A finite extension embeds into a ray class field for `m`.  The existential
formulation avoids making a global choice of ray class field. -/
def EmbedsInRayClassField
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) : Prop :=
  ∃ R : RayClassFieldRealization K m,
    Nonempty (L →ₐ[K] R.extension)

end ClassFieldTheory
