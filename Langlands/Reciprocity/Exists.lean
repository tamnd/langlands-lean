/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.WeilGroup.Ab
import Langlands.Statements.ClassField
import Langlands.Bridge.NYLL
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseInertia
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

/-!
# Existence of the local reciprocity map

This file proves `Langlands.exists_isLocalArtinMap`: there is a topological isomorphism $\mathrm{rec}_K : K^\times \cong W_K^{ab}$ with the properties of `Langlands.IsLocalArtinMap`.

The map is $\mathrm{rec}_K = \iota^{-1} \circ \mathrm{art}_K$. Here $\mathrm{art}_K : K^\times \to G_K^{ab}$ is the absolute local Artin map of the port of n-yamaguchi-0729/ClassFieldTheory, and $\iota : W_K^{ab} \to G_K^{ab}$ is the injective map `Langlands.WeilGroup.toGaloisAb`.

* `Langlands.RecExists.resAb_art`: $\mathrm{art}_K(x)$ acts on $\bar k$ as $\mathrm{Frob}^{v(x)}$, so the image of $\mathrm{art}_K$ is in the image of $\iota$.
* `Langlands.RecExists.mem_range_sepArt`: the image of the inertia subgroup is the image of the units $\mathcal{O}_K^\times$. The proof works at each finite level and ends with a compactness argument.
* `Langlands.RecExists.recEquiv`: the isomorphism $\mathrm{rec}_K$. It is continuous in both directions because it sends the compact open subgroup $\mathcal{O}_K^\times$ onto the image of the compact open inertia subgroup.
* `Langlands.RecExists.rec_uniformizer`, `Langlands.RecExists.rec_ker` and `Langlands.RecExists.rec_surjective`: the three conditions of `IsLocalArtinMap`.

## Implementation notes

The local field structures on the finite quotient fields of the port are scoped instances of the namespace `Langlands.RecExists`. They are not global, because a global norm on a field can make a second instance path for the topology.
-/

open LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Topology ValuativeRel

universe u

set_option linter.unusedSectionVars false

namespace Langlands

namespace RecExists

open LocalField WeilGroup

attribute [local instance] LocalClassFieldTheory.localAbsoluteAbelianProfiniteCommGroup

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The absolute Artin map -/

/-- The absolute Artin map `Kˣ → G_K^ab`. -/
noncomputable def art : Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  (absoluteLocalArtinMap K).toMonoidHom

theorem continuous_art : Continuous (art K) :=
  (absoluteLocalArtinMap K).continuous

theorem art_injective : Function.Injective (art K) :=
  absoluteLocalArtinMap_injective K

theorem sepEquiv_art (x : Kˣ) :
    absoluteGaloisGroupAbelianizationEquivSeparable K (art K x) =
      separableAbsoluteLocalArtinMap K x :=
  absoluteGaloisGroupAbelianizationEquivSeparable_artinMap K x

/-! ### Restriction to finite subextensions of the separable closure -/

open scoped IsMulCommutative in
/-- Restriction `Gal(K^sep/K)^ab → Gal(F/K)`. -/
noncomputable def sepAbRestrict (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    TopologicalAbelianization Gal(SeparableClosure K/K) →* Gal(F/K) :=
  QuotientGroup.lift _ (AlgEquiv.restrictNormalHom F)
    (Subgroup.topologicalClosure_minimal _ (Group.Abelianization.commutator_le_ker _)
      (by rw [IntermediateField.restrictNormalHom_ker]; exact F.fixingSubgroup_isClosed))

theorem sepAbRestrict_mk (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] (σ : Gal(SeparableClosure K/K)) :
    sepAbRestrict K F (QuotientGroup.mk σ) = AlgEquiv.restrictNormalHom F σ :=
  rfl

/-- The open normal subgroup of `Gal(K^sep/K)^ab` cut out by `F`. -/
noncomputable def kerN (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite K) where
  toSubgroup := (sepAbRestrict K F).ker
  isOpen' := by
    show IsOpen ((sepAbRestrict K F).ker :
      Set (TopologicalAbelianization Gal(SeparableClosure K/K)))
    rw [← (QuotientGroup.isQuotientMap_mk _).isOpen_preimage]
    have : ((QuotientGroup.mk : Gal(SeparableClosure K/K) →
        TopologicalAbelianization Gal(SeparableClosure K/K)) ⁻¹'
          ((sepAbRestrict K F).ker : Set _)) = (F.fixingSubgroup : Set _) := by
      ext σ
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker]
      rw [← IntermediateField.restrictNormalHom_ker]
      rfl
    rw [this]
    exact IntermediateField.fixingSubgroup_isOpen F
  isNormal' := MonoidHom.normal_ker _

theorem le_absoluteFiniteQuotientField_kerN (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    F ≤ absoluteFiniteQuotientField K (kerN K F) := by
  intro z hz
  rw [absoluteFiniteQuotientField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have h1 : τ.restrictNormal F = 1 := hτ
  have h2 := AlgEquiv.restrictNormal_commutes τ F ⟨z, hz⟩
  rw [h1] at h2
  simpa using h2.symm

/-- Bridge: the restriction of the absolute Artin map is the finite Artin map. -/
theorem sepAbRestrict_art (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] (x : Kˣ) :
    sepAbRestrict K F (separableAbsoluteLocalArtinMap K x) = abelianLocalArtinMap K F x := by
  set N := kerN K F
  have hle := le_absoluteFiniteQuotientField_kerN K F
  have key : ∀ y : localAbsoluteAbelianProfinite K,
      RamificationTheory.intermediateFieldRestrictNormalHom F _ hle
        (absoluteFiniteQuotientEquiv K N (QuotientGroup.mk' N.toSubgroup y)) =
        sepAbRestrict K F y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H σ =>
      refine (congrArg (RamificationTheory.intermediateFieldRestrictNormalHom F _ hle)
        (absoluteFiniteQuotientEquiv_mk_mk K N σ)).trans ?_
      apply AlgEquiv.ext
      intro z
      apply Subtype.ext
      have h1 := RamificationTheory.intermediateFieldRestrictNormalHom_apply_val F _ hle
        (AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ) z
      have h2 := AlgEquiv.restrictNormal_commutes σ (absoluteFiniteQuotientField K N)
        (IntermediateField.inclusion hle z)
      have h3 := AlgEquiv.restrictNormal_commutes σ F z
      exact h1.trans (h2.trans h3.symm)
  rw [← key, separableAbsoluteLocalArtinMap_finiteProjection]
  have h4 := DFunLike.congr_fun
    (abelianLocalArtinMap_restrict K F (absoluteFiniteQuotientField K N) hle) x
  refine Eq.trans ?_ h4
  change RamificationTheory.intermediateFieldRestrictNormalHom F _ hle
      (absoluteFiniteQuotientEquiv K N ((absoluteFiniteQuotientEquiv K N).symm
        (abelianLocalArtinMap K (absoluteFiniteQuotientField K N) x))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- The embedding of a subfield of `K^sep` into `K̄`. -/
noncomputable def sepIncl (F : IntermediateField K (SeparableClosure K)) :
    F →ₐ[K] AlgebraicClosure K :=
  (separableClosure K (AlgebraicClosure K)).val.comp F.val

/-- A lift `g` of `art x` acts on a finite abelian subextension `F` of `K^sep` as the finite Artin symbol. -/
theorem apply_sepIncl_of_mk_eq_art (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] (x : Kˣ) (g : Field.absoluteGaloisGroup K)
    (hg : (QuotientGroup.mk g : Field.absoluteGaloisGroupAbelianization K) = art K x) (z : F) :
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (sepIncl K F z) =
      sepIncl K F (abelianLocalArtinMap K F x z) := by
  have h1 := absoluteGaloisGroupAbelianizationEquivSeparable_mk K g
  rw [hg, sepEquiv_art] at h1
  have h2 := sepAbRestrict_art K F x
  rw [h1, sepAbRestrict_mk] at h2
  rw [← h2]
  have h3 := AlgEquiv.restrictNormal_commutes (AlgEquiv.separableClosure g) F z
  have h4 : sepIncl K F ((AlgEquiv.restrictNormalHom F (AlgEquiv.separableClosure g)) z) =
      ((AlgEquiv.separableClosure g (z : SeparableClosure K) : SeparableClosure K) :
        AlgebraicClosure K) :=
    congrArg (fun w : SeparableClosure K => (w : AlgebraicClosure K)) h3
  rw [h4]
  rfl

/-! ### Integers and residues of finite subextensions -/

section Plumbing

variable (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
  [IsIntegralClosure 𝒪[F] 𝒪[K] F]

theorem isIntegral_sepIncl (z : 𝒪[F]) : IsIntegral 𝒪[K] (sepIncl K F (z : F)) := by
  have h : IsIntegral 𝒪[K] (z : F) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[F]) (R := 𝒪[K]) (B := F)).2 ⟨z, rfl⟩
  exact IsIntegral.map (sepIncl K F) h

/-- The ring map `𝒪_F → 𝒪_{K̄}`. -/
noncomputable def toIntegers : 𝒪[F] →+* integers K :=
  ((sepIncl K F).toRingHom.comp (algebraMap 𝒪[F] F)).codRestrict
    (integralClosure 𝒪[K] (AlgebraicClosure K)) (isIntegral_sepIncl K F)

theorem coe_toIntegers (z : 𝒪[F]) :
    (toIntegers K F z : AlgebraicClosure K) = sepIncl K F (z : F) :=
  rfl

theorem toIntegers_mem_prime_iff (z : 𝒪[F]) :
    toIntegers K F z ∈ prime K ↔ z ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  rw [prime_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : sepIncl K F (z : F) * (w : AlgebraicClosure K) = 1 :=
      congrArg Subtype.val hw
    have hz : (z : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    have hinv : sepIncl K F ((z : F)⁻¹) = (w : AlgebraicClosure K) := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right hw'
    have hint : IsIntegral 𝒪[K] ((z : F)⁻¹) := by
      rw [← isIntegral_algHom_iff ((sepIncl K F).restrictScalars 𝒪[K])
        (sepIncl K F).injective]
      change IsIntegral 𝒪[K] (sepIncl K F ((z : F)⁻¹))
      rw [hinv]
      exact w.2
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝒪[F])).mp hint
    refine IsUnit.of_mul_eq_one y ?_
    apply Subtype.ext
    change (z : F) * algebraMap 𝒪[F] F y = 1
    rw [hy, mul_inv_cancel₀ hz]
  · intro hu
    exact hu.map (toIntegers K F)

/-- The residue map `𝓀_F → k̄`. -/
noncomputable def residueMap : 𝓀[F] →+* residueFieldBar K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[F])
    ((Ideal.Quotient.mk (prime K)).comp (toIntegers K F)) fun z hz => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact (toIntegers_mem_prime_iff K F z).mpr hz

theorem residueMap_residue (z : 𝒪[F]) :
    residueMap K F (IsLocalRing.residue 𝒪[F] z) =
      Ideal.Quotient.mk (prime K) (toIntegers K F z) :=
  rfl

end Plumbing

/-! ### Restriction from `K^sep` -/

theorem sepIncl_restrictNormal (F : IntermediateField K (SeparableClosure K)) [Normal K F]
    (g : Field.absoluteGaloisGroup K) (z : F) :
    sepIncl K F (AlgEquiv.restrictNormalHom F (AlgEquiv.separableClosure g) z) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) (sepIncl K F z) := by
  have h3 := AlgEquiv.restrictNormal_commutes (AlgEquiv.separableClosure g) F z
  have h4 : sepIncl K F ((AlgEquiv.restrictNormalHom F (AlgEquiv.separableClosure g)) z) =
      ((AlgEquiv.separableClosure g (z : SeparableClosure K) : SeparableClosure K) :
        AlgebraicClosure K) :=
    congrArg (fun w : SeparableClosure K => (w : AlgebraicClosure K)) h3
  rw [h4]
  rfl


/-! ### The residue action on `G_K^{ab}` -/

local notation "Γ" => residueFieldBar K ≃ₐ[residueField K] residueFieldBar K

theorem closure_commutator_le_ker_residueAut :
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure ≤ (residueAut K).ker := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := topologicalClosure_commutator_le_map_inertia K hg
  exact hw

/-- The action of `G_K^{ab}` on `k̄`. -/
noncomputable def resAb : Field.absoluteGaloisGroupAbelianization K →* Γ :=
  QuotientGroup.lift _ (residueAut K) (closure_commutator_le_ker_residueAut K)

theorem resAb_mk (g : Field.absoluteGaloisGroup K) :
    resAb K (QuotientGroup.mk g) = residueAut K g :=
  rfl

theorem resAb_toGaloisAb_mk (w : WeilGroup K) :
    resAb K (toGaloisAb K (QuotientGroup.mk w)) = toResidue K w :=
  rfl

/-! ### Finite unramified extensions -/

scoped instance isIntegralClosure_unramified (m : ℕ) (hm : 0 < m) :
    IsIntegralClosure 𝒪[localFiniteUnramifiedField K m hm] 𝒪[K]
      (localFiniteUnramifiedField K m hm) :=
  localCompleteDVF_integerRing_isIntegralClosure K _

theorem natCard_residue_unramified (m : ℕ) (hm : 0 < m) :
    Nat.card 𝓀[localFiniteUnramifiedField K m hm] = Nat.card 𝓀[K] ^ m := by
  have h := localFiniteUnramifiedField_residue_finrank K m hm
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let : Fintype 𝓀[localFiniteUnramifiedField K m hm] := Fintype.ofFinite _
  let := IsLocalRing.ResidueField.instModule (R := 𝒪[K])
    (S := 𝒪[localFiniteUnramifiedField K m hm])
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[localFiniteUnramifiedField K m hm]), h]

open Polynomial in
theorem mem_range_of_pow_eq {L : Type*} [Field L] [Fintype L] (f : L →+* residueFieldBar K)
    (N : ℕ) (hN : Fintype.card L = N) (hN1 : 1 < N) (y : residueFieldBar K)
    (hy : y ^ N = y) : y ∈ Set.range f := by
  classical
  by_contra hne
  set Z : Finset (residueFieldBar K) := insert y (Finset.univ.image f)
  have hp := Polynomial.X_pow_sub_X_ne_zero (R := residueFieldBar K) hN1
  have hsub : Z.val ⊆ (X ^ N - X : (residueFieldBar K)[X]).roots := by
    intro a ha
    rw [mem_roots hp, IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hy
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
      rw [← map_pow, ← hN, FiniteField.pow_card]
  have h1 := card_le_degree_of_subset_roots hsub
  rw [Polynomial.natDegree_X_pow_sub_X hN1] at h1
  have h2 : Z.card = N + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ f.injective,
      Finset.card_univ, hN]
    intro hmem
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hmem
    exact hne ⟨b, rfl⟩
  omega

/-- Every element of `k̄` is the residue of an integer of a finite unramified extension. -/
theorem exists_unramified_lift (y : residueFieldBar K) :
    ∃ (m : ℕ) (hm : 0 < m) (z : 𝒪[localFiniteUnramifiedField K m hm]),
      residueMap K (localFiniteUnramifiedField K m hm) (IsLocalRing.residue _ z) = y := by
  obtain ⟨m, hm, hy⟩ := exists_pow_card_pow_eq_self K y
  let : Fintype 𝓀[localFiniteUnramifiedField K m hm] := Fintype.ofFinite _
  have hq : Nat.card 𝓀[K] = Fintype.card (residueField K) :=
    (show Nat.card 𝓀[K] = Nat.card (residueField K) from rfl).trans Nat.card_eq_fintype_card
  have hcard : Fintype.card 𝓀[localFiniteUnramifiedField K m hm] =
      Fintype.card (residueField K) ^ m := by
    rw [← Nat.card_eq_fintype_card, natCard_residue_unramified, hq]
  have hq1 : 1 < Fintype.card (residueField K) := Fintype.one_lt_card
  obtain ⟨w, hw⟩ := mem_range_of_pow_eq K (residueMap K (localFiniteUnramifiedField K m hm)) _
    hcard (Nat.one_lt_pow hm.ne' hq1) y hy
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
  exact ⟨m, hm, z, hw⟩

/-! ### The residue action of `art x` -/

theorem resAb_art_unit (u : 𝒪[K]ˣ) : resAb K (art K (integerUnitsToFieldUnits K u)) = 1 := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (art K (integerUnitsToFieldUnits K u))
  rw [← hg, resAb_mk]
  apply AlgEquiv.ext
  intro y
  obtain ⟨m, hm, z, rfl⟩ := exists_unramified_lift K y
  rw [AlgEquiv.one_apply, residueMap_residue, residueAut_mk]
  congr 1
  apply Subtype.ext
  rw [coe_smul_integers, coe_toIntegers, apply_sepIncl_of_mk_eq_art K _ _ g hg]
  have h1 := DFunLike.congr_fun
    (abelianLocalArtinMap_toMonoidHom K (localFiniteUnramifiedField K m hm))
    (integerUnitsToFieldUnits K u)
  have h2 : abelianLocalArtinMap K (localFiniteUnramifiedField K m hm)
      (integerUnitsToFieldUnits K u) = 1 :=
    h1.trans (Universe.abelianLocalArtinMonoidHom_integerUnit_eq_one K _ u)
  rw [h2]
  rfl

theorem resAb_art_of_valuationMap_eq_one (t : Kˣ) (ht : valuationMap K (Additive.ofMul t) = 1) :
    resAb K (art K t) = LocalField.frobenius K := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (art K t)
  rw [← hg, resAb_mk]
  apply AlgEquiv.ext
  intro y
  obtain ⟨m, hm, z, rfl⟩ := exists_unramified_lift K y
  obtain ⟨w, hw1, hw2⟩ := Universe.abelianLocalArtinMap_inverseUniformizer_residue_pow K
    (localFiniteUnramifiedField K m hm) t ht z
  have hq : Nat.card 𝓀[K] = Fintype.card (residueField K) :=
    (show Nat.card 𝓀[K] = Nat.card (residueField K) from rfl).trans Nat.card_eq_fintype_card
  have e1 : Ideal.Quotient.mk (prime K) (toIntegers K (localFiniteUnramifiedField K m hm) w) =
      Ideal.Quotient.mk (prime K) (toIntegers K (localFiniteUnramifiedField K m hm) z) ^
        Fintype.card (residueField K) := by
    rw [← residueMap_residue, hw2, map_pow, residueMap_residue, hq]
  rw [residueMap_residue, residueAut_mk]
  refine Eq.trans ?_ (e1.trans rfl)
  congr 1
  apply Subtype.ext
  rw [coe_smul_integers, coe_toIntegers, coe_toIntegers, apply_sepIncl_of_mk_eq_art K _ t g hg,
    hw1]

theorem resAb_art (x : Kˣ) :
    resAb K (art K x) = LocalField.frobenius K ^ valuationMap K (Additive.ofMul x) := by
  obtain ⟨t, ht⟩ := valuationMap_uniformiser K
  obtain ⟨u, hu⟩ := exists_integerUnit_mul_uniformizer_zpow K t ht x
  conv_lhs => rw [← hu]
  rw [map_mul, map_mul, map_zpow, map_zpow, resAb_art_unit,
    resAb_art_of_valuationMap_eq_one K t ht, one_mul]

/-! ### The map `rec₀ : Kˣ → W_K^{ab}` -/

theorem art_mem_range (x : Kˣ) : art K x ∈ (toGaloisAb K).range := by
  rw [mem_range_toGaloisAb]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (art K x)
  refine ⟨g, ?_, hg⟩
  rw [← SetLike.mem_coe, coe_weilSubgroup]
  show residueAut K g ∈ Subgroup.zpowers (LocalField.frobenius K)
  have h := resAb_art K x
  rw [← hg, resAb_mk] at h
  rw [h]
  exact Subgroup.zpow_mem_zpowers _ _

/-- The reciprocity map as a homomorphism. -/
noncomputable def rec₀ : Kˣ →* Ab K :=
  (MonoidHom.ofInjective (toGaloisAb_injective K)).symm.toMonoidHom.comp
    ((art K).codRestrict _ (art_mem_range K))

theorem toGaloisAb_rec₀ (x : Kˣ) : toGaloisAb K (rec₀ K x) = art K x :=
  MonoidHom.apply_ofInjective_symm (toGaloisAb_injective K) _

theorem rec₀_injective : Function.Injective (rec₀ K) := fun a b h =>
  art_injective K (by rw [← toGaloisAb_rec₀, ← toGaloisAb_rec₀, h])

/-! ### Inertia is in the image of the units -/

noncomputable scoped instance afqNormed (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    NontriviallyNormedField (absoluteFiniteQuotientField K N) :=
  finiteExtensionSpectralNormedField K _

noncomputable scoped instance afqValuativeRel (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    ValuativeRel (absoluteFiniteQuotientField K N) :=
  finiteExtensionSpectralValuativeRel K _

scoped instance afqLocal (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IsNonarchimedeanLocalField (absoluteFiniteQuotientField K N) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K _

scoped instance afqHasExt (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (absoluteFiniteQuotientField K N)) :=
  finiteExtensionSpectralValuation_hasExtension K _

scoped instance afqIntClosure (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IsIntegralClosure 𝒪[absoluteFiniteQuotientField K N] 𝒪[K] (absoluteFiniteQuotientField K N) :=
  localCompleteDVF_integerRing_isIntegralClosure K _

theorem restrictNormal_mem_residue_ker (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (g : Field.absoluteGaloisGroup K) (hg : residueAut K g = 1) :
    AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) (AlgEquiv.separableClosure g) ∈
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K (absoluteFiniteQuotientField K N)).ker := by
  refine (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal
    K (absoluteFiniteQuotientField K N) _).2 fun x => ?_
  rw [← toIntegers_mem_prime_iff K, RingHom.map_sub, ← Ideal.Quotient.eq]
  have h2 : residueAut K g (Ideal.Quotient.mk (prime K) (toIntegers K (absoluteFiniteQuotientField K N) x)) =
      Ideal.Quotient.mk (prime K) (toIntegers K (absoluteFiniteQuotientField K N) x) := by
    rw [hg]
    rfl
  rw [residueAut_mk] at h2
  refine Eq.trans ?_ h2
  congr 1
  apply Subtype.ext
  rw [coe_smul_integers, coe_toIntegers, coe_toIntegers,
    galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
  exact sepIncl_restrictNormal K (absoluteFiniteQuotientField K N) g
    (x : absoluteFiniteQuotientField K N)

theorem finite_level (g : Field.absoluteGaloisGroup K) (hg : residueAut K g = 1)
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    ∃ u : 𝒪[K]ˣ, QuotientGroup.mk' N.toSubgroup
        (separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u)) =
      QuotientGroup.mk' N.toSubgroup
        (QuotientGroup.mk (AlgEquiv.separableClosure g) : localAbsoluteAbelianProfinite K) := by
  have hσ := restrictNormal_mem_residue_ker K N g hg
  rw [← Universe.abelianLocalArtinMonoidHom_units_eq_residue_ker K
    (absoluteFiniteQuotientField K N)] at hσ
  obtain ⟨x, hx, hxσ⟩ := Subgroup.mem_map.mp hσ
  rw [fieldPrincipalUnits, principalUnits_zero] at hx
  obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨u, (absoluteFiniteQuotientEquiv K N).injective ?_⟩
  rw [separableAbsoluteLocalArtinMap_finiteProjection]
  refine Eq.trans ?_ (absoluteFiniteQuotientEquiv_mk_mk K N _).symm
  change absoluteFiniteQuotientEquiv K N ((absoluteFiniteQuotientEquiv K N).symm
    (abelianLocalArtinMap K (absoluteFiniteQuotientField K N) (integerUnitsToFieldUnits K u))) = _
  rw [ContinuousMulEquiv.apply_symm_apply, ← hxσ]
  exact DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K _) _

theorem mem_range_sepArt (h : Field.absoluteGaloisGroup K) (hh : residueAut K h = 1) :
    ∃ u : 𝒪[K]ˣ, separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u) =
      (QuotientGroup.mk (AlgEquiv.separableClosure h) : localAbsoluteAbelianProfinite K) := by
  set a : localAbsoluteAbelianProfinite K := QuotientGroup.mk (AlgEquiv.separableClosure h)
  set C : Set (localAbsoluteAbelianProfinite K) := Set.range
    (fun u : 𝒪[K]ˣ => separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u))
  have hC : IsClosed C := (isCompact_range ((separableAbsoluteLocalArtinMap K).continuous.comp
    (integerUnitsToFieldUnits_continuous K))).isClosed
  by_contra ha
  have ha' : a ∉ C := fun ⟨u, hu⟩ => ha ⟨u, hu⟩
  have hV : IsOpen {z : localAbsoluteAbelianProfinite K | a * z ∈ Cᶜ} :=
    hC.isOpen_compl.preimage (continuous_const_mul a)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV
    (by simpa using ha')
  obtain ⟨u, hu⟩ := finite_level K h hh N
  have h2 : a⁻¹ * separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u) ∈
      N.toSubgroup := QuotientGroup.eq.mp hu.symm
  have h3 : a * (a⁻¹ * separableAbsoluteLocalArtinMap K (integerUnitsToFieldUnits K u)) ∉ C :=
    hN h2
  exact h3 ⟨u, (mul_inv_cancel_left a _).symm⟩

theorem exists_unit_of_resAb_eq_one (b : Field.absoluteGaloisGroupAbelianization K)
    (hb : resAb K b = 1) : ∃ u : 𝒪[K]ˣ, art K (integerUnitsToFieldUnits K u) = b := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨u, hu⟩ := mem_range_sepArt K h hb
  refine ⟨u, (absoluteGaloisGroupAbelianizationEquivSeparable K).injective ?_⟩
  rw [sepEquiv_art, absoluteGaloisGroupAbelianizationEquivSeparable_mk, hu]

theorem rec₀_surjective : Function.Surjective (rec₀ K) := by
  intro a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (toResidue_mem_zpowers K w)
  obtain ⟨t, ht⟩ := valuationMap_uniformiser K
  have hb : resAb K (toGaloisAb K (QuotientGroup.mk w) * (art K (t ^ n))⁻¹) = 1 := by
    rw [map_mul, map_inv, resAb_toGaloisAb_mk, resAb_art, valuationMap_ofMul_zpow, ht, mul_one,
      hn, mul_inv_cancel]
  obtain ⟨u, hu⟩ := exists_unit_of_resAb_eq_one K _ hb
  refine ⟨integerUnitsToFieldUnits K u * t ^ n, toGaloisAb_injective K ?_⟩
  rw [toGaloisAb_rec₀, map_mul, hu, inv_mul_cancel_right]

/-! ### Topology -/

/-- The units of `𝒪_K` inside `Kˣ`. -/
noncomputable def S : Set Kˣ := Set.range (integerUnitsToFieldUnits K)

/-- The image of inertia in `W_K^{ab}`. -/
noncomputable def I : Set (Ab K) := QuotientGroup.mk '' (inertia K : Set (WeilGroup K))

theorem isCompact_S : IsCompact (S K) := isCompact_range (integerUnitsToFieldUnits_continuous K)

theorem isOpen_S : IsOpen (S K) := by
  have : S K = {x : Kˣ | (x : K) ∈ 𝒪[K] ∧ ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K]} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(u : 𝒪[K]).2, ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨x, h1⟩, ⟨_, h2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, Units.ext rfl⟩
  rw [this]
  exact ((Valuation.isOpen_integer (v := ValuativeRel.valuation K)).preimage
    Units.continuous_val).inter
    ((Valuation.isOpen_integer (v := ValuativeRel.valuation K)).preimage Units.continuous_coe_inv)

theorem mem_weilSubgroup_of_residueAut_eq_one (g : Field.absoluteGaloisGroup K)
    (hg : residueAut K g = 1) : g ∈ weilSubgroup K := by
  rw [← SetLike.mem_coe, coe_weilSubgroup]
  show residueAut K g ∈ Subgroup.zpowers (LocalField.frobenius K)
  rw [hg]
  exact one_mem _

/-- The inclusion of the kernel of `residueAut` into `W_K`. -/
noncomputable def inertiaLift : (residueAut K).ker → WeilGroup K := fun g =>
  ⟨g.1, mem_weilSubgroup_of_residueAut_eq_one K g.1 g.2⟩

theorem toResidue_inertiaLift (g : (residueAut K).ker) : toResidue K (inertiaLift K g) = 1 :=
  g.2

theorem continuous_inertiaLift : Continuous (inertiaLift K) := by
  have hr : (toResidue K ∘ inertiaLift K) = fun _ => 1 := funext (toResidue_inertiaLift K)
  have h : Continuous[_, TopologicalSpace.induced (toGalois K)
      (inferInstance : TopologicalSpace (Field.absoluteGaloisGroup K)) ⊓
      TopologicalSpace.induced (toResidue K) (⊥ : TopologicalSpace Γ)] (inertiaLift K) := by
    have h1 : Continuous (toGalois K ∘ inertiaLift K) := continuous_subtype_val
    have h2 : Continuous[_, (⊥ : TopologicalSpace Γ)] (toResidue K ∘ inertiaLift K) := by
      rw [hr]
      exact @continuous_const _ _ _ (⊥ : TopologicalSpace Γ) _
    exact continuous_inf_rng.2 ⟨continuous_induced_rng.2 h1, continuous_induced_rng.2 h2⟩
  exact h

theorem range_inertiaLift : Set.range (inertiaLift K) = (inertia K : Set (WeilGroup K)) := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    exact toResidue_inertiaLift K g
  · intro hw
    exact ⟨⟨toGalois K w, hw⟩, rfl⟩

theorem isClosed_ker_residueAut : IsClosed ((residueAut K).ker : Set (Field.absoluteGaloisGroup K)) :=
  haveI : T2Space Γ := krullTopology_t2
  haveI : T1Space Γ := T2Space.t1Space
  isClosed_singleton.preimage (continuous_residueAut K)

instance : CompactSpace (residueAut K).ker :=
  isCompact_iff_compactSpace.mp (isClosed_ker_residueAut K).isCompact

theorem isCompact_I : IsCompact (I K) := by
  unfold I
  rw [← range_inertiaLift]
  exact (isCompact_range (continuous_inertiaLift K)).image QuotientGroup.continuous_mk

theorem isOpen_I : IsOpen (I K) :=
  QuotientGroup.isOpenMap_coe _ (isOpen_inertia K)

instance : T2Space (Field.absoluteGaloisGroupAbelianization K) := by
  show T2Space (standardLocalAbsoluteAbelianProfinite K)
  infer_instance

theorem image_rec₀_S : rec₀ K '' S K = I K := by
  ext a
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (rec₀ K (integerUnitsToFieldUnits K u))
    refine ⟨w, ?_, hw⟩
    show toResidue K w = 1
    rw [← resAb_toGaloisAb_mk, hw, toGaloisAb_rec₀, resAb_art_unit]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := exists_unit_of_resAb_eq_one K (toGaloisAb K (QuotientGroup.mk w)) hw
    refine ⟨_, ⟨u, rfl⟩, toGaloisAb_injective K ?_⟩
    rw [toGaloisAb_rec₀, hu]

theorem mapsTo_rec₀ : Set.MapsTo (rec₀ K) (S K) (I K) := fun _ hx =>
  image_rec₀_S K ▸ Set.mem_image_of_mem _ hx

theorem continuousAt_rec₀ : ContinuousAt (rec₀ K) 1 := by
  have hj : Topology.IsEmbedding (fun a : I K => toGaloisAb K a) := by
    have : CompactSpace (I K) := isCompact_iff_compactSpace.mp (isCompact_I K)
    exact (((continuous_toGaloisAb K).comp continuous_subtype_val).isClosedEmbedding
      ((toGaloisAb_injective K).comp Subtype.val_injective)).isEmbedding
  have hf : Continuous (Set.MapsTo.restrict _ _ _ (mapsTo_rec₀ K)) := by
    rw [hj.continuous_iff]
    have : (fun a : I K => toGaloisAb K a) ∘ Set.MapsTo.restrict _ _ _ (mapsTo_rec₀ K) =
        fun x : S K => art K x := by
      funext x
      exact toGaloisAb_rec₀ K x
    rw [this]
    exact (continuous_art K).comp continuous_subtype_val
  have hon : ContinuousOn (rec₀ K) (S K) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp hf
  exact hon.continuousAt ((isOpen_S K).mem_nhds ⟨1, map_one _⟩)

theorem continuous_rec₀ : Continuous (rec₀ K) :=
  continuous_of_continuousAt_one (rec₀ K) (continuousAt_rec₀ K)

/-- The reciprocity map as a group isomorphism. -/
noncomputable def recMulEquiv : Kˣ ≃* Ab K :=
  MulEquiv.ofBijective (rec₀ K) ⟨rec₀_injective K, rec₀_surjective K⟩

theorem recMulEquiv_apply (x : Kˣ) : recMulEquiv K x = rec₀ K x := rfl

theorem mapsTo_recMulEquiv_symm : Set.MapsTo (recMulEquiv K).symm (I K) (S K) := by
  intro a ha
  rw [← image_rec₀_S K] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  rw [← recMulEquiv_apply, MulEquiv.symm_apply_apply]
  exact hx

theorem continuousAt_recMulEquiv_symm : ContinuousAt (recMulEquiv K).symm 1 := by
  have hk : Topology.IsEmbedding (fun x : S K => art K x) := by
    have : CompactSpace (S K) := isCompact_iff_compactSpace.mp (isCompact_S K)
    exact (((continuous_art K).comp continuous_subtype_val).isClosedEmbedding
      ((art_injective K).comp Subtype.val_injective)).isEmbedding
  have hf : Continuous (Set.MapsTo.restrict _ _ _ (mapsTo_recMulEquiv_symm K)) := by
    rw [hk.continuous_iff]
    have : (fun x : S K => art K x) ∘ Set.MapsTo.restrict _ _ _ (mapsTo_recMulEquiv_symm K) =
        fun a : I K => toGaloisAb K a := by
      funext a
      show art K ((recMulEquiv K).symm a) = toGaloisAb K a
      rw [← toGaloisAb_rec₀, ← recMulEquiv_apply, MulEquiv.apply_symm_apply]
    rw [this]
    exact (continuous_toGaloisAb K).comp continuous_subtype_val
  have hon : ContinuousOn (recMulEquiv K).symm (I K) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp hf
  exact hon.continuousAt ((isOpen_I K).mem_nhds ⟨1, (inertia K).one_mem, rfl⟩)

/-- The reciprocity map `Kˣ ≃ₜ* W_K^{ab}`. -/
noncomputable def recEquiv : Kˣ ≃ₜ* Ab K :=
  { recMulEquiv K with
    continuous_toFun := continuous_rec₀ K
    continuous_invFun := continuous_of_continuousAt_one (recMulEquiv K).symm
      (continuousAt_recMulEquiv_symm K) }

theorem recEquiv_apply (x : Kˣ) : recEquiv K x = rec₀ K x := rfl

/-! ### The properties of `IsLocalArtinMap` -/

theorem rec_uniformizer (ϖ : Kˣ) (hϖ : IsUniformizer (ϖ : K)) :
    ∃ Φ : WeilGroup K, IsGeometricFrobenius K Φ ∧ recEquiv K ϖ = (Φ : Ab K) := by
  obtain ⟨π, hπ, hπϖ⟩ := hϖ
  have hv : valuationMap K (Additive.ofMul ϖ⁻¹) = 1 :=
    v_integerRingIrreducibleFieldUnit_inv K π hπ ϖ hπϖ.symm
  have hv' : valuationMap K (Additive.ofMul ϖ) = -1 := by
    rw [valuationMap_ofMul_inv] at hv
    omega
  obtain ⟨Φ, hΦ⟩ := QuotientGroup.mk_surjective (rec₀ K ϖ)
  refine ⟨Φ, ?_, hΦ.symm⟩
  show toResidue K Φ = (LocalField.frobenius K)⁻¹
  rw [← resAb_toGaloisAb_mk, hΦ, toGaloisAb_rec₀, resAb_art, hv', zpow_neg, zpow_one]

section Restrict

variable (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
  [IsAbelianGalois K L]

theorem le_sep : L ≤ separableClosure K (AlgebraicClosure K) :=
  le_separableClosure K (AlgebraicClosure K) L

/-- `L` as a subfield of `K^sep`. -/
noncomputable abbrev L' : IntermediateField K (SeparableClosure K) :=
  IntermediateField.restrict (le_sep K L)

/-- The isomorphism `L ≃ L'`. -/
noncomputable def φ : L ≃ₐ[K] L' K L := IntermediateField.restrictAlgEquiv (le_sep K L)

instance : FiniteDimensional K (L' K L) := LinearEquiv.finiteDimensional (φ K L).toLinearEquiv

instance : IsAbelianGalois K (L' K L) := IsAbelianGalois.of_algHom (φ K L).symm.toAlgHom

theorem sepIncl_φ (z : L) : sepIncl K (L' K L) (φ K L z) = (z : AlgebraicClosure K) := rfl

theorem restrict_rec₀_apply (x : Kˣ) (z : L) :
    ((Ab.restrict K L (rec₀ K x) z : L) : AlgebraicClosure K) =
      (((φ K L).symm (abelianLocalArtinMap K (L' K L) x (φ K L z)) : L) :
        AlgebraicClosure K) := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (rec₀ K x)
  have hg : (QuotientGroup.mk (toGalois K w) : Field.absoluteGaloisGroupAbelianization K) =
      art K x := by
    rw [← toGaloisAb_rec₀, ← hw]
    rfl
  rw [← hw, Ab.restrict_mk]
  have h1 := AlgEquiv.restrictNormal_commutes
    (toGalois K w : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) L z
  have h2 := apply_sepIncl_of_mk_eq_art K (L' K L) x (toGalois K w) hg (φ K L z)
  have h3 : (((φ K L).symm (abelianLocalArtinMap K (L' K L) x (φ K L z)) : L) :
      AlgebraicClosure K) = sepIncl K (L' K L) (abelianLocalArtinMap K (L' K L) x (φ K L z)) := by
    rw [← sepIncl_φ, AlgEquiv.apply_symm_apply]
  rw [h3, ← h2]
  exact h1

theorem restrict_rec₀ (x : Kˣ) :
    Ab.restrict K L (rec₀ K x) = AlgEquiv.autCongr (φ K L).symm (abelianLocalArtinMap K (L' K L) x) := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.val_injective
  rw [restrict_rec₀_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_symm]

theorem localNormSubgroup_L' : localNormSubgroup K (L' K L) = normGroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map ((φ K L).symm : L' K L →* L) y, Units.ext ?_⟩
    exact Algebra.norm_eq_of_algEquiv (φ K L).symm (y : L' K L)
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map ((φ K L) : L →* L' K L) y, Units.ext ?_⟩
    exact Algebra.norm_eq_of_algEquiv (φ K L) (y : L)

theorem rec_ker (x : Kˣ) : Ab.restrict K L (recEquiv K x) = 1 ↔ x ∈ normGroup K L := by
  rw [recEquiv_apply, restrict_rec₀, MulEquiv.map_eq_one_iff, ← localNormSubgroup_L',
    ← abelianLocalArtinMap_ker]
  rfl

theorem rec_surjective : Function.Surjective (Ab.restrict K L ∘ recEquiv K) := by
  intro τ
  obtain ⟨x, hx⟩ := abelianLocalArtinMap_surjective K (L' K L)
    ((AlgEquiv.autCongr (φ K L).symm).symm τ)
  refine ⟨x, ?_⟩
  rw [Function.comp_apply, recEquiv_apply, restrict_rec₀, hx, MulEquiv.apply_symm_apply]

end Restrict

end RecExists

open RecExists in
/-- Existence of the local reciprocity map. -/
theorem exists_isLocalArtinMap (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ rec : Kˣ ≃ₜ* WeilGroup.Ab K, IsLocalArtinMap K rec :=
  ⟨recEquiv K,
    { uniformizer := rec_uniformizer K
      surjective := fun L _ _ => rec_surjective K L
      ker := fun L _ _ => rec_ker K L }⟩

end Langlands

