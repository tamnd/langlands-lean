/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/MathlibGlobalArtinRayComparison.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteReciprocityDataComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality

/-!
# Finite ray reciprocity and the named absolute Artin map

The finite reciprocity datum has arithmetic normalization; the existing
named absolute map has geometric normalization. Their pointwise comparison
therefore contains an explicit inverse. Both maps retain their original values.
-/

@[expose] public section

open scoped NumberField
open GlobalClassFieldTheory.Reciprocity
open ClassFieldTheory

noncomputable section

namespace ClassFieldTheory.FiniteAbelianReciprocityData

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (maximalAbelianExtension K)]
  [IsScalarTower K L (maximalAbelianExtension K)]

/-- For any supplied finite reciprocity datum and its actual finite-field
embedding, the ray value is the inverse of the named absolute Artin restriction. -/
theorem ideleClassArtin_eq_inv_mathlibGlobalArtin_restrict
    (D : FiniteAbelianReciprocityData K L) (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    D.ideleClassArtin x =
      (AlgEquiv.restrictNormalHom L
        (mathlibAbelianizationToMaximal K
          (mathlibGlobalArtin K x)))⁻¹ := by
  have hfinite := mathlibGlobalArtin_finiteProjection_standard_of_scalarTower
    (K := K) L x
  rw [hfinite, D.ideleClassArtin_apply, arithmeticGlobalNormResidueMonoidHom_apply]
  rfl

end ClassFieldTheory.FiniteAbelianReciprocityData
