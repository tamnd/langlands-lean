/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LubinTate/EqualCharacteristic/NormSubgroup/LevelAlgebra.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-!
# LubinTate the explicit norm-subgroup computation: canonical algebra and norm subgroup at a
finite level

This light leaf names the canonical base algebra and its norm subgroup once,
so the later inclusion and index arguments do not repeat expensive fallback
typeclass searches.
-/



@[expose] public section

universe u v

noncomputable section


open scoped LaurentSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

attribute [local instance]
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule

/-- The canonical base algebra on the explicit Lubin--Tate level field. -/
@[reducible] noncomputable def equalCharacteristicLubinTateLevelAlgebra
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelFieldAlgebra F n

/-- The norm subgroup of the explicit Lubin--Tate level, with the canonical
base algebra fixed once for downstream statements. -/
noncomputable def equalCharacteristicLubinTateNormSubgroup
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    Subgroup F.residueField⸨X⸩ˣ := by
  letI : Algebra F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelAlgebra F n
  exact LocalFieldTheory.localNormSubgroup F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)

end EqualCharacteristic
end LubinTate
