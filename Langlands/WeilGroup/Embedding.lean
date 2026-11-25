/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.WeilGroup.Restrict

/-!
# The Weil group of a finite extension as a topological subgroup

Let $L$ be a finite extension of $K$ inside $\bar K$. The file `Langlands.WeilGroup.Restrict` gives an injective continuous homomorphism $W_L \to W_K$ with image the open subgroup `restrictSubgroup K L`. This file proves that this map is a homeomorphism onto its image.

* `Langlands.WeilGroup.t2Space_weilGroup`: the Weil group is Hausdorff.
* `Langlands.WeilGroup.weilHom_mem_inertia_iff`: an element of $W_L$ is in the inertia subgroup of $L$ if and only if its image is in the inertia subgroup of $K$.
* `Langlands.WeilGroup.weilEquiv`: the isomorphism of topological groups $W_L \cong$ `restrictSubgroup K L`.
* `Langlands.WeilGroup.isEmbedding_weilHom`: the map $W_L \to W_K$ is an embedding.

## Implementation notes

The inverse map is continuous at the identity by a compactness argument. The inertia subgroup $I_L$ is compact and $W_K$ is Hausdorff, so the restriction of the map to $I_L$ is a closed embedding. Its image is $I_K \cap W_L$, which is open in $W_K$. A homomorphism that is continuous at the identity is continuous.
-/

open Topology

namespace Langlands

universe u

namespace WeilGroup

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The Weil group is Hausdorff, since it injects continuously into the absolute Galois group. -/
instance t2Space_weilGroup : T2Space (WeilGroup K) := by
  have : T2Space (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure K/K))
  exact .of_injective_continuous (toGalois_injective K) (continuous_toGalois K)

open FiniteExt

variable (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]

theorem weilHom_mem (w : WeilGroup L) : weilHom K L w ∈ restrictSubgroup K L :=
  range_weilHom K L ▸ ⟨w, rfl⟩

/-- An element of $W_L$ is in the inertia subgroup of $L$ if and only if its image in $W_K$ is in the inertia subgroup of $K$. -/
theorem weilHom_mem_inertia_iff (w : WeilGroup L) :
    weilHom K L w ∈ inertia K ↔ w ∈ inertia L := by
  rw [← ker_degree, ← ker_degree, MonoidHom.mem_ker, MonoidHom.mem_ker, degree_weilHom]
  have hf : (residueFinrank K L : ℤ) ≠ 0 := by exact_mod_cast (residueFinrank_pos K L).ne'
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one, mul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 hf
    · exact Multiplicative.toAdd.injective h0
  · intro h
    rw [h]
    rfl

/-- The map `weilHom K L` with codomain `restrictSubgroup K L`. -/
noncomputable def weilHomRestrict : WeilGroup L →* restrictSubgroup K L :=
  (weilHom K L).codRestrict _ (weilHom_mem K L)

theorem weilHomRestrict_bijective : Function.Bijective (weilHomRestrict K L) := by
  refine ⟨fun a b h => weilHom_injective K L (congrArg Subtype.val h), fun y => ?_⟩
  have hy : (y : WeilGroup K) ∈ (weilHom K L).range := (range_weilHom K L).symm ▸ y.2
  obtain ⟨w, hw⟩ := hy
  exact ⟨w, Subtype.ext hw⟩

/-- The inverse of `weilHomRestrict K L` is continuous at the identity. -/
theorem continuousAt_weilHomRestrict_symm :
    ContinuousAt (MulEquiv.ofBijective _ (weilHomRestrict_bijective K L)).symm 1 := by
  set e := MulEquiv.ofBijective _ (weilHomRestrict_bijective K L)
  have : CompactSpace (inertia L) := isCompact_iff_compactSpace.mp (isCompact_inertia L)
  let g : inertia L → WeilGroup K := fun x => weilHom K L x
  have hg : IsClosedEmbedding g :=
    ((continuous_weilHom K L).comp continuous_subtype_val).isClosedEmbedding
      ((weilHom_injective K L).comp Subtype.val_injective)
  rw [ContinuousAt, map_one, Filter.Tendsto]
  intro V hV
  obtain ⟨V0, hV0V, hV0, h1V0⟩ := mem_nhds_iff.mp hV
  have hS : IsOpen (Subtype.val ⁻¹' V0 : Set (inertia L)) := hV0.preimage continuous_subtype_val
  obtain ⟨O, hO, hOS⟩ := hg.isInducing.isOpen_iff.mp hS
  have h1O : (1 : WeilGroup K) ∈ O := by
    have : (1 : inertia L) ∈ g ⁻¹' O := by rw [hOS]; exact h1V0
    simpa [g] using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((hO.inter (isOpen_inertia K)).preimage continuous_subtype_val |>.mem_nhds
      (show ((1 : restrictSubgroup K L) : WeilGroup K) ∈ O ∩ inertia K from
        ⟨h1O, (inertia K).one_mem⟩)) ?_
  rintro y ⟨hyO, hyI⟩
  set w := e.symm y
  have hwy : weilHom K L w = y := congrArg Subtype.val (e.apply_symm_apply y)
  have hwI : w ∈ inertia L := (weilHom_mem_inertia_iff K L w).mp (hwy ▸ hyI)
  have : (⟨w, hwI⟩ : inertia L) ∈ g ⁻¹' O := by
    change weilHom K L w ∈ O
    rw [hwy]
    exact hyO
  rw [hOS] at this
  exact hV0V this

/-- The Weil group $W_L$ of a finite extension, as a topological group, is isomorphic to the open subgroup `restrictSubgroup K L` of $W_K$. -/
noncomputable def weilEquiv : WeilGroup L ≃ₜ* restrictSubgroup K L where
  toMulEquiv := MulEquiv.ofBijective _ (weilHomRestrict_bijective K L)
  continuous_toFun := (continuous_weilHom K L).subtype_mk _
  continuous_invFun :=
    continuous_of_continuousAt_one
      (MulEquiv.ofBijective _ (weilHomRestrict_bijective K L)).symm.toMonoidHom
      (continuousAt_weilHomRestrict_symm K L)

@[simp] theorem weilEquiv_apply (w : WeilGroup L) :
    weilEquiv K L w = ⟨weilHom K L w, weilHom_mem K L w⟩ := rfl

/-- The map `weilHom K L` is an embedding. -/
theorem isEmbedding_weilHom : IsEmbedding (weilHom K L) :=
  IsEmbedding.subtypeVal.comp (weilEquiv K L).toHomeomorph.isEmbedding

/-- For the trivial extension $L = K$, the subgroup `restrictSubgroup K ⊥` is all of $W_K$. -/
theorem restrictSubgroup_bot : restrictSubgroup K ⊥ = ⊤ := by
  ext w
  simp only [Subgroup.mem_top, iff_true, mem_restrictSubgroup]
  intro x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact AlgEquiv.commutes _ a

end WeilGroup

end Langlands
