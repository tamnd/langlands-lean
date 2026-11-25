/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/ShrinkLocalClassification.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MathlibFieldClassification
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkChosenFiniteAbelianNorms
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup

/-!
# Finite abelian local classification in arbitrary universes

The concrete classification for a small local field transfers to an arbitrary
nonarchimedean local field. The transfer respects the actual field-norm subgroup.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The finite abelian classification after moving through the small
representative of `K`. -/
def shrinkFiniteAbelianFieldNormSubgroupOrderIso :
    ClassFieldTheory.FiniteAbelianLocalExtension K ≃o
      (ClassFieldTheory.OpenFiniteIndexSubgroup K)ᵒᵈ := by
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  letI : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  exact (shrinkChosenFiniteAbelianOrderIso K).trans
    ((LocalClassFieldTheory.finiteAbelianFieldNormSubgroupOrderIso (Shrink.{0} K)).trans
      (shrinkOpenFiniteIndexOrderIso K).dual)

/-- The transported order equivalence sends a finite abelian field to its
actual field-norm subgroup. -/
theorem shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    (OrderDual.ofDual (shrinkFiniteAbelianFieldNormSubgroupOrderIso K E)).1.toSubgroup =
      E.normSubgroup := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  let F := shrinkChosenFiniteAbelianField K E
  have hsmall := LocalClassFieldTheory.finiteAbelianFieldNormSubgroupOrderIso_apply
    (Shrink.{0} K) F
  have hnorm :
      E.normSubgroup.map
          (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
        F.normSubgroup :=
    shrinkChosenFiniteAbelian_normSubgroup_map K E
  have heq :
      (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
        (shrinkUnitsContinuousMulEquiv K).symm.toMulEquiv.toMonoidHom := by
    ext x
    rfl
  rw [heq] at hnorm
  change ((OrderDual.ofDual
    (LocalClassFieldTheory.finiteAbelianFieldNormSubgroupOrderIso
      (Shrink.{0} K) F)).1.toSubgroup.map
        (shrinkUnitsContinuousMulEquiv K).toMulEquiv.toMonoidHom) = E.normSubgroup
  rw [hsmall]
  change (F.normSubgroup.map
    (shrinkUnitsContinuousMulEquiv K).toMulEquiv.toMonoidHom) = E.normSubgroup
  rw [← hnorm]
  exact (shrinkUnitsContinuousMulEquiv K).toMulEquiv.mapSubgroup.apply_symm_apply
    E.normSubgroup

end LocalFieldTheory
