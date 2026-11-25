/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockTensorSmul.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteLocalFactor

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock

/-!
# Equivariance of the integral tensor block

This file proves equivariance of the finite-place tensor-unit block under the
restricted global Galois action.
-/



@[expose] public section

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- The local-place block equivalence intertwines the restricted integral
tensor action with the global Galois action. -/
theorem
    finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    let :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  intro sharedOwner1
  let tensorUnitsAction :=
    scalarTensorUnitsAction
      (K := K) (L := L) (A := w₀.adicCompletion K)
  calc
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (τ • (x : (w₀.adicCompletion K ⊗[K] L)ˣ)) :=
      congrArg
        (finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀))
        (relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
          (K := K) (L := L) w₀ τ x)
    _ = τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) :=
      finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀) τ
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ)

end ChosenFinitePlace
