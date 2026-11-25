/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FullConductorRayClassField.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization

/-!
# Full conductors and ray class field containment

This module identifies the full conductor of a finite abelian extension
as the least modulus of a selected ray class field into which the extension
embeds.  The proof combines the ray-field embedding criterion with the
minimality theorem for the full conductor.
-/



@[expose] public section

universe u v w

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type u} [Field K] [NumberField K]

/-- A finite abelian extension embeds in the selected ray class field
exactly when the modulus is at least its full conductor. -/
theorem nonempty_algHom_to_rayClassField_iff_fullConductor_le
    (L : Type v) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor ≤ m := by
  rw [nonempty_algHom_to_rayClassField_iff_isDefiningModulus]
  exact
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).isDefiningModulus_iff_fullConductor_le m

end GlobalClassFields
end GlobalClassFieldTheory
