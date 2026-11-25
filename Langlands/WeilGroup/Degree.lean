/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.WeilGroup.Ab

/-!
# The degree map of the Weil group

This file proves that the residue field $\bar k$ of $\bar K$ is algebraically closed and that the Frobenius has infinite order. Then it defines the degree map $d : W_K \to \mathbb{Z}$, with $w$ acting on $\bar k$ as $\mathrm{Frob}^{-d(w)}$. A geometric Frobenius has degree one.

* `Langlands.LocalField.isAlgClosed_residueFieldBar`: $\bar k$ is algebraically closed.
* `Langlands.LocalField.not_isOfFinOrder_frobenius`: the Frobenius $x \mapsto x^q$ of $\bar k$ has infinite order.
* `Langlands.WeilGroup.degree`: the degree map, with `toResidue_eq_zpow_degree`.
* `Langlands.WeilGroup.ker_degree`: the kernel of the degree map is the inertia subgroup.
* `Langlands.WeilGroup.degree_surjective` and `Langlands.WeilGroup.continuous_degree`: the degree map is surjective and locally constant.
-/

namespace Langlands

open Polynomial ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace LocalField

/-- The residue field `residueFieldBar K` of the integral closure is algebraically closed. -/
instance isAlgClosed_residueFieldBar : IsAlgClosed (residueFieldBar K) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ Polynomial.lifts (Ideal.Quotient.mk (prime K)) :=
    Polynomial.lifts_iff_coeff_lifts _ |>.mpr fun n => Ideal.Quotient.mk_surjective _
  obtain ⟨g, hg, hdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hp
  set ι : integers K →+* AlgebraicClosure K := algebraMap (integers K) (AlgebraicClosure K)
  have hpos : (g.map ι).degree ≠ 0 := by
    rw [degree_map_eq_of_injective Subtype.val_injective, degree_eq_natDegree hgm.ne_zero,
      hdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (g.map ι) hpos
  have h1 : IsIntegral (integers K) a := by
    refine ⟨g, hgm, ?_⟩
    rwa [IsRoot, eval_map] at ha
  have h2 : IsIntegral 𝒪[K] a := isIntegral_trans a h1
  let ζ : integers K := ⟨a, h2⟩
  refine ⟨Ideal.Quotient.mk (prime K) ζ, ?_⟩
  have hζ : g.eval ζ = 0 := by
    apply Subtype.val_injective
    change ι (g.eval ζ) = ι 0
    rw [map_zero, ← eval₂_hom, ← eval_map]
    exact ha
  rw [← hg, eval_map, eval₂_hom, hζ, map_zero]

/-- The Frobenius of `residueFieldBar K` has infinite order. -/
theorem not_isOfFinOrder_frobenius : ¬ IsOfFinOrder (LocalField.frobenius K) := by
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hq : 1 < Fintype.card (residueField K) := Fintype.one_lt_card
  have hx : ∀ x : residueFieldBar K, x ^ (Fintype.card (residueField K) ^ n) = x := by
    intro x
    have h := congrArg (fun σ : residueFieldBar K ≃ₐ[residueField K] residueFieldBar K => σ x)
      hpow
    simp only [AlgEquiv.one_apply] at h
    rwa [frobenius, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h
  have hne := FiniteField.X_pow_card_pow_sub_X_ne_zero (residueFieldBar K) hn.ne' hq
  apply hne
  apply Polynomial.eq_zero_of_infinite_isRoot
  convert Set.infinite_univ (α := residueFieldBar K)
  ext x
  simp [hx x]

end LocalField

open LocalField

namespace WeilGroup

/-- The integral powers of the inverse of the Frobenius are pairwise distinct. -/
theorem injective_zpowersHom_frobenius_inv :
    Function.Injective (zpowersHom _ (LocalField.frobenius K)⁻¹) := by
  have h := (injective_zpow_iff_not_isOfFinOrder (x := (LocalField.frobenius K)⁻¹)).mpr
    (by rw [isOfFinOrder_inv_iff]; exact not_isOfFinOrder_frobenius K)
  intro a b hab
  exact h hab

/-- The degree map $W_K \to \mathbb{Z}$, normalized so that a geometric Frobenius has degree one. An element of degree $n$ acts on the residue field as the $n$-th power of the inverse of the Frobenius. -/
noncomputable def degree : WeilGroup K →* Multiplicative ℤ :=
  (MonoidHom.ofInjective (injective_zpowersHom_frobenius_inv K)).symm.toMonoidHom.comp
    ((toResidue K).codRestrict _ fun w => by
      rw [Subgroup.range_zpowersHom, Subgroup.zpowers_inv]
      exact toResidue_mem_zpowers K w)

/-- An element of the Weil group acts on the residue field as the inverse of the Frobenius raised to its degree. -/
theorem toResidue_eq_zpow_degree (w : WeilGroup K) :
    toResidue K w = (LocalField.frobenius K)⁻¹ ^ (Multiplicative.toAdd (degree K w)) := by
  rw [← zpowersHom_apply]
  have := MonoidHom.ofInjective_apply (hf := injective_zpowersHom_frobenius_inv K) (x := degree K w)
  rw [← this]
  simp [degree]

/-- An element of the Weil group has degree one if and only if it is a geometric Frobenius. -/
theorem degree_eq_one_iff (w : WeilGroup K) :
    degree K w = Multiplicative.ofAdd 1 ↔ IsGeometricFrobenius K w := by
  rw [IsGeometricFrobenius, toResidue_eq_zpow_degree]
  constructor
  · intro h
    rw [h, toAdd_ofAdd, zpow_one]
  · intro h
    apply injective_zpowersHom_frobenius_inv K
    rw [zpowersHom_apply, zpowersHom_apply, h, toAdd_ofAdd, zpow_one]

/-- The kernel of the degree map is the inertia subgroup. -/
theorem ker_degree : (degree K).ker = inertia K := by
  ext w
  rw [MonoidHom.mem_ker, inertia, MonoidHom.mem_ker, toResidue_eq_zpow_degree]
  constructor
  · intro h
    rw [h, toAdd_one, zpow_zero]
  · intro h
    apply injective_zpowersHom_frobenius_inv K
    rw [zpowersHom_apply, zpowersHom_apply, h, toAdd_one, zpow_zero]

/-- The Weil group contains a geometric Frobenius. -/
theorem exists_isGeometricFrobenius : ∃ w, IsGeometricFrobenius K w := by
  obtain ⟨g, hg⟩ := residueAut_surjective K (LocalField.frobenius K)⁻¹
  have hmem : g ∈ weilSubgroup K := by
    rw [← SetLike.mem_coe, coe_weilSubgroup, Set.mem_preimage, hg]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  exact ⟨⟨g, hmem⟩, hg⟩

/-- The degree map is surjective. -/
theorem degree_surjective : Function.Surjective (degree K) := by
  obtain ⟨w, hw⟩ := exists_isGeometricFrobenius K
  have h1 := (degree_eq_one_iff K w).mpr hw
  intro n
  refine ⟨w ^ Multiplicative.toAdd n, ?_⟩
  rw [map_zpow, h1]
  apply Multiplicative.toAdd.injective
  simp

/-- The degree map is continuous for the discrete topology on `Multiplicative ℤ`. -/
theorem continuous_degree : Continuous (degree K) := by
  apply continuous_discrete_rng.mpr
  intro n
  have h : degree K ⁻¹' {n} = toResidue K ⁻¹' {(LocalField.frobenius K)⁻¹ ^ Multiplicative.toAdd n} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, toResidue_eq_zpow_degree]
    constructor
    · rintro rfl
      rfl
    · intro h
      apply Multiplicative.toAdd.injective
      exact injective_zpow_iff_not_isOfFinOrder.mpr
        (by rw [isOfFinOrder_inv_iff]; exact not_isOfFinOrder_frobenius K) h
  rw [h]
  exact isOpen_fiber_toResidue K _

end WeilGroup

end Langlands

