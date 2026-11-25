/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/InfiniteAlgEquiv.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.Compat.InfinitePlaceAbsMap
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Adele.Equiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv

/-!
# Infinite completions under a number-field equivalence

The completion maps along an isomorphism of number fields are mutually
inverse. This is the archimedean local input for the topology of `adeleCongr`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- The map between the completions at corresponding infinite places. -/
noncomputable def infinitePlaceCompletionCongrHom
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion →+*
      W.Completion := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  exact InfinitePlace.Completion.absMap w W

/-- The archimedean completion map is continuous. -/
theorem infinitePlaceCompletionCongrHom_continuous
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    Continuous (infinitePlaceCompletionCongrHom e W) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  change Continuous (InfinitePlace.Completion.absMap w W)
  exact InfinitePlace.Completion.continuous_absMap w W

/-- Transport along a field isomorphism is an equivalence of the
corresponding infinite-place completions. -/
noncomputable def infinitePlaceCompletionCongrEquiv
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) :
    ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion ≃+*
      W.Completion := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : Algebra M K := e.symm.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  have hMK : infinitePlaceBelow (K := M) w = W := by
    change (W.comap e.toRingHom).comap e.symm.toRingHom = W
    exact (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).right_inv W
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  let : w.1.LiesOver W.1 :=
    ⟨congrArg (fun v : InfinitePlace M => v.1) hMK⟩
  let f : w.Completion →+* W.Completion :=
    InfinitePlace.Completion.absMap w W
  let g : W.Completion →+* w.Completion :=
    InfinitePlace.Completion.absMap W w
  exact RingEquiv.ofRingHom f g
    (by
      apply RingHom.ext
      intro x
      change f (g x) = x
      refine InfinitePlace.Completion.induction_on W x ?_ ?_
      · exact isClosed_eq
          ((InfinitePlace.Completion.continuous_absMap w W).comp
            (InfinitePlace.Completion.continuous_absMap W w))
          continuous_id
      · intro y
        dsimp only [f, g]
        rw [InfinitePlace.Completion.absMap_coe
            W w y,
          InfinitePlace.Completion.absMap_coe w W]
        apply congrArg (fun z : WithAbs W.1 => (z : W.Completion))
        apply (WithAbs.equiv W.1).injective
        change e (e.symm (WithAbs.equiv W.1 y)) =
          WithAbs.equiv W.1 y
        exact e.apply_symm_apply _)
    (by
      apply RingHom.ext
      intro x
      change g (f x) = x
      refine InfinitePlace.Completion.induction_on w x ?_ ?_
      · exact isClosed_eq
          ((InfinitePlace.Completion.continuous_absMap W w).comp
            (InfinitePlace.Completion.continuous_absMap w W))
          continuous_id
      · intro y
        dsimp only [f, g]
        rw [InfinitePlace.Completion.absMap_coe
            w W y,
          InfinitePlace.Completion.absMap_coe W w]
        apply congrArg (fun z : WithAbs w.1 => (z : w.Completion))
        apply (WithAbs.equiv w.1).injective
        change e.symm (e (WithAbs.equiv w.1 y)) =
          WithAbs.equiv w.1 y
        exact e.symm_apply_apply _)

/-- The completion map agrees with the number-field equivalence on
elements of the number field. -/
theorem infinitePlaceCompletionCongrHom_algebraMap
    (e : K ≃ₐ[ℚ] M) (W : InfinitePlace M) (x : K) :
    infinitePlaceCompletionCongrHom e W
        (algebraMap K
          ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W).Completion x) =
      algebraMap M W.Completion (e x) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  have hKM : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  let : W.1.LiesOver w.1 :=
    ⟨congrArg (fun v : InfinitePlace K => v.1) hKM⟩
  change InfinitePlace.Completion.absMap w W (algebraMap K w.Completion x) =
    algebraMap M W.Completion (e x)
  have hAlg : algebraMap K M x = e x := by
    change e.toRingHom x = e x
    rfl
  rw [← hAlg]
  apply InfinitePlace.Completion.ext
  change AbsoluteValue.Completion.map w.1 W.1 (algebraMap K w.1.Completion x) =
    algebraMap M W.1.Completion (algebraMap K M x)
  simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, WithAbs.map_apply, WithAbs.ofAbs_toAbs] using
    (AbsoluteValue.Completion.map_coe w.1 W.1 (WithAbs.toAbs w.1 x))

/-- On infinite coordinates, `adeleCongr` is the completion map at the
corresponding infinite place. -/
theorem adeleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : InfinitePlace M) :
    (adeleCongr e a).1 W =
      infinitePlaceCompletionCongrHom e W
        (a.1 ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W)) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : IsScalarTower ℚ K M :=
    IsScalarTower.of_algHom e.toAlgHom
  let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm W
  let componentK : NumberField.AdeleRing (𝓞 K) K →+* w.Completion :=
    (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing K)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  let componentM : NumberField.AdeleRing (𝓞 M) M →+* W.Completion :=
    (Pi.evalRingHom (fun v : InfinitePlace M => v.Completion) W).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing M)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 M) M))
  change componentM (adeleCongr e a) =
    infinitePlaceCompletionCongrHom e W (componentK a)
  have hW : infinitePlaceBelow (K := K) W = w := by
    change W.comap e.toRingHom = W.comap e.toRingHom
    rfl
  have hq : infinitePlaceBelow (K := ℚ) w =
      infinitePlaceBelow (K := ℚ) W := by
    rw [← hW, infinitePlaceBelow_infinitePlaceBelow]
  let z := (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)).symm a
  have ha : relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)).apply_symm_apply a
  rw [← ha]
  have htransport :
      componentM (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z)) =
      componentM (adeleCongr e
        (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K) z)) :=
    congrArg componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr e z)
  rw [← htransport]
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      let v := infinitePlaceBelow (K := ℚ) W
      let : W.1.LiesOver
          (infinitePlaceBelow (K := ℚ) W).1 := ⟨rfl⟩
      let : w.1.LiesOver
          (infinitePlaceBelow (K := ℚ) w).1 := ⟨rfl⟩
      let : W.1.LiesOver w.1 :=
        ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
      have hcomponent
          (v' : InfinitePlace ℚ) (hv' : v' = v)
          [hWv : W.1.LiesOver v.1]
          [hwv' : w.1.LiesOver v'.1]
          [hWw : W.1.LiesOver w.1] :
          InfinitePlace.Completion.absMap
              v W (b.1 v) =
            InfinitePlace.Completion.absMap
              w W
              (InfinitePlace.Completion.absMap
                v' w (b.1 v')) := by
        subst v'
        exact (infinitePlaceCompletionMap_comp_apply
          (K := ℚ) (M := K) (L := M) W (b.1 v)).symm
      change
        (relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := M)
          (relativeAdeleCongr (K := ℚ) e (b ⊗ₜ[ℚ] x))).1 W =
        infinitePlaceCompletionCongrHom e W
          ((relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)
            (b ⊗ₜ[ℚ] x)).1 w)
      rw [relativeAdeleCongr_tmul,
        relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul,
        relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
      rw [map_mul, infinitePlaceCompletionCongrHom_algebraMap]
      exact congrArg₂ (· * ·)
        (hcomponent (infinitePlaceBelow (K := ℚ) w) hq
          (hWv := ⟨rfl⟩) (hwv' := ⟨rfl⟩)
          (hWw := ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩))
        rfl

end
