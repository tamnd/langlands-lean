/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/ShrinkChosenFiniteAbelianNorms.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkChosenFiniteAbelianFields
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianNorms
public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.FiniteAbelianIntermediateFieldAlgEquiv
public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnitsBaseChange

/-!
# Actual norm subgroups in the chosen small-base separable closure

The finite-abelian-field order equivalence carries the actual field-norm
subgroup, not merely an abstract subgroup assigned by a classification.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two-step finite-field transport preserves the actual field-norm
subgroup after identifying the multiplicative groups of `K` and `Shrink K`. -/
theorem shrinkChosenFiniteAbelian_normSubgroup_map
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    let : Small.{0} K := nonarchimedeanLocalField_small K
    (E.normSubgroup).map
        (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
      (shrinkChosenFiniteAbelianField K E).normSubgroup := by
  intro sharedOwner1
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  let M := shrinkIntermediateField K E.1
  let c := shrinkSeparableClosureEquiv K
  let : FiniteDimensional (Shrink.{0} K) M :=
    shrinkIntermediateField_finiteDimensional K E
  let : FiniteDimensional (Shrink.{0} K) (M.map c.symm.toAlgHom) :=
    ClassFieldTheory.finiteDimensional_intermediateField_map_algEquiv c.symm M
  change (localNormSubgroup K E.1).map
      (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
    localNormSubgroup (Shrink.{0} K)
      (M.map c.symm.toAlgHom)
  calc
    _ = localNormSubgroup (Shrink.{0} K) M :=
      shrinkIntermediateField_normSubgroup_map K E
    _ = localNormSubgroup (Shrink.{0} K)
        (M.map c.symm.toAlgHom) := by
          have h := LocalFieldTheory.localNormSubgroup_map_ringEquiv
            (RingEquiv.refl (Shrink.{0} K))
            (IntermediateField.intermediateFieldMap c.symm M).toRingEquiv
            (ClassFieldTheory.intermediateFieldMap_commutes c.symm M)
          have hmapid :
              (Units.mapEquiv
                (RingEquiv.refl (Shrink.{0} K)).toMulEquiv).toMonoidHom =
                MonoidHom.id (Shrink.{0} K)ˣ := by
            ext x
            rfl
          rw [hmapid, Subgroup.map_id] at h
          exact h

end LocalFieldTheory
