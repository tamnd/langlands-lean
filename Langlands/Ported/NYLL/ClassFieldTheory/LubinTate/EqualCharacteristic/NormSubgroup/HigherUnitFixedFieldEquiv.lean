/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LubinTate/EqualCharacteristic/NormSubgroup/HigherUnitFixedFieldEquiv.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective

/-!
# LubinTate the explicit norm-subgroup computation: the standard level is the higher-unit fixed
field

The standard-level embedding is an equivalence because its source and target
have the same degree `(q - 1) q^n`.
-/



@[expose] public section

universe u v

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

attribute [local instance]
  equalCharacteristicCompletedLevelBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- Defines `equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit`. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgEquiv
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgEquiv.ofBijective
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit F a n ha)
    ⟨fun _ _ h =>
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).injective
        (congrArg Subtype.val h),
      equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit_surjective
        F a n ha⟩

end EqualCharacteristic
end LubinTate
