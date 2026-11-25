/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FinitePlaceRayArtinDecomposition.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteReciprocityDataComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import Langlands.Ported.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup

/-!
# Ray Artin values at a finite place

The canonical one-place map into an ideal-theoretic ray class group has the
actual local norm subgroup as its Artin kernel. Its Artin values preserve
the absolute-value class of one extension of that place to the top field,
including when the place divides the ray modulus.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A Frobenius-normalized ray Artin map restricts at every finite place to
the local norm quotient and lands in a decomposition group. The extension
absolute value and the local-to-ray map are chosen independently of `D`'s
Artin values. -/
theorem exists_finitePlaceRayArtin_decomposition
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (w : ExtendingAbsoluteValue
        (NumberField.HeightOneSpectrum.adicAbv K v) L)
      (ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus),
      (D.artin.comp ι).ker = finitePlaceTensorNormSubgroup K L v ∧
      ∀ (x : (v.adicCompletion K)ˣ) (y : L),
        w.1 ((D.artin (ι x)) y) < 1 ↔ w.1 y < 1 := by
  classical
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal K D.modulus
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K D.modulus
  let w : ExtendingAbsoluteValue
      (NumberField.HeightOneSpectrum.adicAbv K v) L :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' m.congruenceSubgroup).comp
        (IdeleGroup.finitePlaceIdeleClass v))
  have hvalue (x : (v.adicCompletion K)ˣ) :
      D.artin (ι x) =
        GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
          K L v x := by
    calc
      D.artin (ι x) =
          GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
            K L (IdeleGroup.finitePlaceIdeleClass v x) :=
        D.ideleClassArtin_apply (IdeleGroup.finitePlaceIdeleClass v x)
      _ = GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
            K L v x := by
        exact DFunLike.congr_fun
          ((open GlobalClassFieldTheory.Reciprocity in
            arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
              (K := K) (L := L) v)) x
  refine ⟨w, ι, ?_, ?_⟩
  · ext x
    change D.artin (ι x) = 1 ↔
      x ∈ finitePlaceTensorNormSubgroup K L v
    rw [hvalue x,
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply,
      inv_eq_one,
      GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
      ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := L) v]
    rfl
  · intro x y
    rw [hvalue x,
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply]
    have hgeo :
        GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x ∈
          HilbertRamification.absoluteValueDecompositionGroup K w.1 := by
      change GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x ∈ _
      rw [GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor,
        MonoidHom.comp_apply]
      change ((HilbertRamification.absoluteValueDecompositionGroup K w.1).subtype
        _) ∈ _
      exact Subtype.property _
    have hinv :=
      (HilbertRamification.absoluteValueDecompositionGroup K w.1).inv_mem hgeo
    exact hinv y

end ClassFieldTheory
