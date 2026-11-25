/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Bridge.NYLL
import Langlands.WeilGroup.Ab
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityFamilyExt
import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF

/-!
# Uniqueness of the local reciprocity map

This file proves `Langlands.isLocalArtinMap_unique`: two topological isomorphisms $K^\times \cong W_K^{ab}$ with the properties of `Langlands.IsLocalArtinMap` are equal.

Each such map gives a coherent family of finite Artin maps, one for each finite abelian extension of $K$ in the separable closure. The family satisfies the hypotheses of the uniqueness theorem `ClassFieldTheory.finiteAbelianLocalReciprocity_family_ext` of the port. So the two families are equal. An element of $G_K$ that fixes each finite abelian extension of $K$ is in the closure of the commutator subgroup (`Langlands.RecUnique.mem_closure_commutator_of_forall`), and $W_K^{ab} \to G_K^{ab}$ is injective. So the two maps are equal.
-/

namespace Langlands.RecUnique

open scoped commutatorElement

/-- An element of the Galois group of a normal extension that fixes every finite abelian
subextension lies in the closure of the commutator subgroup. -/
theorem mem_closure_commutator_of_forall {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [Normal F Ω] (g : Gal(Ω/F))
    (hg : ∀ L : IntermediateField F Ω, FiniteDimensional F L → IsAbelianGalois F L →
      ∀ x ∈ L, g x = x) :
    g ∈ (commutator Gal(Ω/F)).topologicalClosure := by
  set S := separableClosure F Ω
  set ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) S
  set C := (commutator Gal(Ω/F)).topologicalClosure
  set H := C.map ρ
  have hρc : Continuous ρ := InfiniteGalois.restrictNormalHom_continuous S
  have hHc : IsClosed (H : Set Gal(S/F)) := by
    rw [Subgroup.coe_map]
    exact ((Subgroup.isClosed_topologicalClosure _).isCompact.image hρc).isClosed
  have hρs : Function.Surjective ρ := AlgEquiv.restrictNormalHom_surjective Ω
  have hcomm : commutator Gal(S/F) ≤ H := by
    have : (commutator Gal(Ω/F)).map ρ = commutator Gal(S/F) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hρs]
    rw [← this]
    exact Subgroup.map_mono (Subgroup.le_topologicalClosure _)
  by_contra hgC
  have hγ : ρ g ∉ H := by
    rintro ⟨c, hc, hcg⟩
    exact hgC (LocalField.restrictNormalHom_separableClosure_injective F Ω hcg ▸ hc)
  have hnhds : (fun v => ρ g * v) ⁻¹' (H : Set Gal(S/F))ᶜ ∈ nhds (1 : Gal(S/F)) := by
    apply (continuous_const_mul (ρ g)).continuousAt.preimage_mem_nhds
    rw [mul_one]
    exact hHc.isOpen_compl.mem_nhds hγ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff F S _).mp hnhds
  set N := H ⊔ E.fixingSubgroup
  have hHn : H.Normal :=
    Subgroup.commutator_top_left_le_iff.mp
      ((Subgroup.commutator_mono le_rfl le_top).trans hcomm)
  have hγN : ρ g ∉ N := by
    intro hmem
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
    obtain ⟨h, hh, v, hv, hhv⟩ := hmem
    have h1 := hEsub (inv_mem (SetLike.mem_coe.mp hv))
    apply h1
    change ρ g * v⁻¹ ∈ H
    rw [← hhv, mul_inv_cancel_right]
    exact hh
  have hNopen : IsOpen (N : Set Gal(S/F)) :=
    Subgroup.isOpen_mono le_sup_right E.fixingSubgroup_isOpen
  have hNclosed : IsClosed (N : Set Gal(S/F)) := Subgroup.isClosed_of_isOpen N hNopen
  have hNn : N.Normal :=
    Subgroup.commutator_top_left_le_iff.mp
      ((Subgroup.commutator_mono le_rfl le_top).trans (hcomm.trans le_sup_left))
  set L := IntermediateField.fixedField N
  have hLfix : L.fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hNclosed⟩
  have hLfin : FiniteDimensional F L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hLfix]; exact hNopen)
  have hLgal : IsGalois F L :=
    (InfiniteGalois.normal_iff_isGalois L).mp (by rw [hLfix]; exact hNn)
  have hLab : IsAbelianGalois F L := by
    have : IsMulCommutative Gal(L/F) := .of_comm fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective S a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective S b
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
        ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hLfix]
      exact (le_sup_left : H ≤ N) (hcomm (Subgroup.commutator_mem_commutator trivial trivial))
    exact {}
  let e : L ≃ₐ[F] IntermediateField.lift L := IntermediateField.liftAlgEquiv L
  have hL'fin : FiniteDimensional F (IntermediateField.lift L) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  have hL'ab : IsAbelianGalois F (IntermediateField.lift L) :=
    IsAbelianGalois.of_algHom (e.symm : IntermediateField.lift L →ₐ[F] L)
  have hfix := hg _ hL'fin hL'ab
  apply hγN
  rw [← hLfix, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply]
  exact hfix _ ((IntermediateField.mem_lift y).mpr hy)

open ValuativeRel LocalField WeilGroup ClassFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The inclusion of the separable closure of NYLL into the algebraic closure. -/
noncomputable abbrev ι : SeparableClosure K →ₐ[K] AlgebraicClosure K :=
  (separableClosure K (AlgebraicClosure K)).val

/-- A finite abelian extension of NYLL as an intermediate field of the algebraic closure. -/
noncomputable abbrev liftE (E : FiniteAbelianLocalExtension K) :
    IntermediateField K (AlgebraicClosure K) :=
  E.1.map (ι K)

/-- The identification of `E` with its image in the algebraic closure. -/
noncomputable abbrev eqv (E : FiniteAbelianLocalExtension K) : E.1 ≃ₐ[K] liftE K E :=
  E.1.equivMap (ι K)

instance (E : FiniteAbelianLocalExtension K) : FiniteDimensional K (liftE K E) :=
  LinearEquiv.finiteDimensional (eqv K E).toLinearEquiv

instance (E : FiniteAbelianLocalExtension K) : IsAbelianGalois K (liftE K E) :=
  IsAbelianGalois.of_algHom ((eqv K E).symm : liftE K E →ₐ[K] E.1)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem eqv_apply (E : FiniteAbelianLocalExtension K) (y : E.1) :
    ((eqv K E y : liftE K E) : AlgebraicClosure K) = ((y : SeparableClosure K) : AlgebraicClosure K) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem eqv_symm_apply (E : FiniteAbelianLocalExtension K) (z : liftE K E) :
    (((eqv K E).symm z : SeparableClosure K) : AlgebraicClosure K) = (z : AlgebraicClosure K) := by
  calc _ = ((eqv K E ((eqv K E).symm z) : liftE K E) : AlgebraicClosure K) := rfl
    _ = _ := by rw [AlgEquiv.apply_symm_apply]

theorem continuous_restrict (L : IntermediateField K (AlgebraicClosure K)) [IsAbelianGalois K L]
    [FiniteDimensional K L] : Continuous (Ab.restrict K L) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact (InfiniteGalois.restrictNormalHom_continuous L).comp (continuous_toGalois K)

/-- An element of the absolute Galois group as an automorphism. -/
abbrev gal (g : Field.absoluteGaloisGroup K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g

/-- The family of finite Artin maps attached to a candidate reciprocity map. -/
noncomputable def family (rec : Kˣ ≃ₜ* Ab K) (E : FiniteAbelianLocalExtension K) :
    Kˣ →ₜ* (E.1 ≃ₐ[K] E.1) where
  toMonoidHom := (((AlgEquiv.autCongr (eqv K E).symm).toMonoidHom.comp
    (Ab.restrict K (liftE K E))).comp rec.toMonoidHom)
  continuous_toFun := by
    have := krullTopology_discreteTopology_of_finiteDimensional K (liftE K E)
    exact (continuous_of_discreteTopology (f := ((AlgEquiv.autCongr (eqv K E).symm :
      Gal(liftE K E/K) ≃* Gal(E.1/K)) : Gal(liftE K E/K) → Gal(E.1/K)))).comp
      ((continuous_restrict K _).comp rec.continuous)

theorem family_apply_eq (rec : Kˣ ≃ₜ* Ab K) (E : FiniteAbelianLocalExtension K) (x : Kˣ) :
    family K rec E x = AlgEquiv.autCongr (eqv K E).symm (Ab.restrict K (liftE K E) (rec x)) :=
  rfl

theorem family_val (rec : Kˣ ≃ₜ* Ab K) (E : FiniteAbelianLocalExtension K) (x : Kˣ)
    (w : WeilGroup K) (hw : rec x = (QuotientGroup.mk w : Ab K)) (y : E.1) :
    (((family K rec E x y : E.1) : SeparableClosure K) : AlgebraicClosure K) =
      gal K (toGalois K w) ((y : SeparableClosure K) : AlgebraicClosure K) := by
  rw [family_apply_eq, hw, Ab.restrict_mk, AlgEquiv.autCongr_apply]
  change (((eqv K E).symm (restrict K (liftE K E) w (eqv K E y)) : SeparableClosure K) :
    AlgebraicClosure K) = _
  rw [eqv_symm_apply]
  exact AlgEquiv.restrictNormalHom_apply _ _ _

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_normGroup_liftE (E : FiniteAbelianLocalExtension K) (x : Kˣ) :
    x ∈ normGroup K (liftE K E) ↔ x ∈ E.normSubgroup := by
  let e := eqv K E
  simp only [normGroup, FiniteAbelianLocalExtension.normSubgroup,
    LocalFieldTheory.localNormSubgroup, LocalFieldTheory.normUnits, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (e.symm : liftE K E →* E.1) y, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    exact Algebra.norm_eq_of_algEquiv e.symm (y : liftE K E)
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (e : E.1 →* liftE K E) y, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    exact Algebra.norm_eq_of_algEquiv e (y : E.1)

theorem family_ker (rec : Kˣ ≃ₜ* Ab K) (h : IsLocalArtinMap K rec)
    (E : FiniteAbelianLocalExtension K) :
    (family K rec E).toMonoidHom.ker = E.normSubgroup := by
  ext x
  rw [MonoidHom.mem_ker, ← mem_normGroup_liftE, ← h.ker]
  change AlgEquiv.autCongr (eqv K E).symm (Ab.restrict K (liftE K E) (rec x)) = 1 ↔ _
  exact (AlgEquiv.autCongr (eqv K E).symm).map_eq_one_iff

theorem family_coh (rec : Kˣ ≃ₜ* Ab K) (E F : FiniteAbelianLocalExtension K)
    (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1) :
    IntermediateField.inclusion hEF ((family K rec E x) y) =
      (family K rec F x) (IntermediateField.inclusion hEF y) := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (rec x)
  apply Subtype.ext
  apply Subtype.ext
  change (((family K rec E x y : E.1) : SeparableClosure K) : AlgebraicClosure K) =
    (((family K rec F x (IntermediateField.inclusion hEF y) : F.1) : SeparableClosure K) :
      AlgebraicClosure K)
  rw [family_val K rec E x w hw.symm, family_val K rec F x w hw.symm]
  rfl

set_option maxHeartbeats 400000 in
/-- The Frobenius condition of NYLL for an automorphism that is the restriction of an element of
the absolute Galois group acting on `residueFieldBar K` as `x ↦ x ^ q`. -/
theorem frob_aux (E : FiniteAbelianLocalExtension K)
    [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
    [IsNonarchimedeanLocalField E.1]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E.1)]
    (τ : Field.absoluteGaloisGroup K)
    (hτ : ∀ ζ : integers K, Ideal.Quotient.mk (prime K) (τ • ζ) =
      Ideal.Quotient.mk (prime K) ζ ^ Fintype.card (residueField K))
    (σ : E.1 ≃ₐ[K] E.1)
    (hσ : ∀ y : E.1, (((σ y : E.1) : SeparableClosure K) : AlgebraicClosure K) =
      gal K τ ((y : SeparableClosure K) : AlgebraicClosure K))
    (x : 𝒪[E.1]) :
    ∃ z : 𝒪[E.1], (z : E.1) = σ (x : E.1) ∧
      IsLocalRing.residue 𝒪[E.1] z = (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K] := by
  have hIC : IsIntegralClosure 𝒪[E.1] 𝒪[K] E.1 :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K E.1
  let ψ : E.1 →ₐ[K] AlgebraicClosure K := (ι K).comp E.1.val
  have hψ : ∀ y : E.1, ψ y = ((y : SeparableClosure K) : AlgebraicClosure K) := fun _ => rfl
  have hint0 : ∀ u : 𝒪[E.1], IsIntegral 𝒪[K] (u : E.1) := fun u =>
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[E.1]) (R := 𝒪[K]) (B := E.1)).2 ⟨u, rfl⟩
  have hst1 : IsScalarTower 𝒪[K] K E.1 := inferInstance
  have hst2 : IsScalarTower 𝒪[K] K (AlgebraicClosure K) := inferInstance
  let ψ' : E.1 →ₐ[𝒪[K]] AlgebraicClosure K := ψ.restrictScalars 𝒪[K]
  have hint : ∀ u : 𝒪[E.1], IsIntegral 𝒪[K] (ψ (u : E.1)) := fun u =>
    (hint0 u).map ψ'
  let J : 𝒪[E.1] →+* integers K :=
    RingHom.codRestrict ((ψ : E.1 →+* AlgebraicClosure K).comp (algebraMap 𝒪[E.1] E.1))
      (integralClosure 𝒪[K] (AlgebraicClosure K)) hint
  have hJ : ∀ u : 𝒪[E.1], (J u : AlgebraicClosure K) = ψ (u : E.1) := fun _ => rfl
  -- the image of `σ x` is integral, so it lies in `𝒪[E.1]`
  have hz : IsIntegral 𝒪[K] (σ (x : E.1)) := by
    refine (isIntegral_algHom_iff (ψ.restrictScalars 𝒪[K]) ψ.injective).mp ?_
    change IsIntegral 𝒪[K] (ψ (σ (x : E.1)))
    rw [hψ, hσ]
    exact (τ • J x).2
  obtain ⟨z, hzx⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝒪[E.1])).mp hz
  refine ⟨z, hzx, ?_⟩
  have hq : Nat.card 𝓀[K] = Fintype.card (residueField K) :=
    Nat.card_eq_fintype_card (α := residueField K)
  rw [hq, ← map_pow]
  apply Ideal.Quotient.eq.mpr
  by_contra hnot
  have hu : IsUnit (J (z - x ^ Fintype.card (residueField K))) :=
    (IsLocalRing.notMem_maximalIdeal.mp hnot).map J
  have hmem : J (z - x ^ Fintype.card (residueField K)) ∈ prime K := by
    have hJz : J z = τ • J x := by
      apply Subtype.ext
      rw [hJ, coe_smul_integers]
      change ψ (algebraMap 𝒪[E.1] E.1 z) = _
      rw [hzx, hψ, hσ]
      rfl
    rw [J.map_sub, J.map_pow, hJz]
    exact Ideal.Quotient.eq.mp (hτ (J x))
  exact (inferInstance : (prime K).IsMaximal).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

/-- A uniformizer in the sense of Mathlib's `Valuation.IsUniformizer` is irreducible. -/
theorem irreducible_of_isUniformizer (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) : Irreducible π := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact Valuation.IsUniformizer.is_generator (π := π) hπ

/-- The inverse of a geometric Frobenius acts on `residueFieldBar K` as `x ↦ x ^ q`. -/
theorem smul_mk_of_isGeometricFrobenius (Φ : WeilGroup K) (hΦ : IsGeometricFrobenius K Φ)
    (ζ : integers K) :
    Ideal.Quotient.mk (prime K) (toGalois K Φ⁻¹ • ζ) =
      Ideal.Quotient.mk (prime K) ζ ^ Fintype.card (residueField K) := by
  have h1 : toResidue K Φ⁻¹ = LocalField.frobenius K := by
    rw [map_inv, show toResidue K Φ = (LocalField.frobenius K)⁻¹ from hΦ, inv_inv]
  have h2 : toResidue K Φ⁻¹ (Ideal.Quotient.mk (prime K) ζ) =
      Ideal.Quotient.mk (prime K) (toGalois K Φ⁻¹ • ζ) := rfl
  rw [← h2, h1, LocalField.frobenius, FiniteField.frobeniusAlgEquivOfAlgebraic_apply]

/-- The family attached to a map with the properties of `IsLocalArtinMap` satisfies the
Frobenius normalization of NYLL. -/
theorem family_frob (rec : Kˣ ≃ₜ* Ab K) (h : IsLocalArtinMap K rec)
    (E : FiniteAbelianLocalExtension K)
    [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
    [IsNonarchimedeanLocalField E.1]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E.1)]
    (π : 𝒪[K]) (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) (x : 𝒪[E.1]) :
    ∃ z : 𝒪[E.1],
      (z : E.1) = (family K rec E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) (x : E.1) ∧
      IsLocalRing.residue 𝒪[E.1] z = (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K] := by
  obtain ⟨Φ, hΦ, hrec⟩ := h.uniformizer (Units.mk0 (π : K) hπ.ne_zero)
    ⟨π, irreducible_of_isUniformizer K π hπ, rfl⟩
  have hw : rec (Units.mk0 (π : K) hπ.ne_zero)⁻¹ = (QuotientGroup.mk Φ⁻¹ : Ab K) := by
    rw [map_inv, hrec]
    rfl
  exact frob_aux K E (toGalois K Φ⁻¹) (smul_mk_of_isGeometricFrobenius K Φ hΦ) _
    (fun y => family_val K rec E _ Φ⁻¹ hw y) x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Every finite abelian extension in the algebraic closure comes from a finite abelian extension
of NYLL in the separable closure. -/
theorem exists_liftE_eq (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L] : ∃ E : FiniteAbelianLocalExtension K, liftE K E = L := by
  have hLS : L ≤ separableClosure K (AlgebraicClosure K) :=
    le_separableClosure K (AlgebraicClosure K) L
  let E1 : IntermediateField K (SeparableClosure K) := IntermediateField.restrict hLS
  have hEq : IntermediateField.lift E1 = L := IntermediateField.lift_restrict hLS
  have h1 : FiniteDimensional K (IntermediateField.lift E1) := by rw [hEq]; infer_instance
  have h2 : IsAbelianGalois K (IntermediateField.lift E1) := by rw [hEq]; infer_instance
  let e := IntermediateField.liftAlgEquiv E1
  have h3 : FiniteDimensional K E1 := LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have h4 : IsAbelianGalois K E1 := IsAbelianGalois.of_algHom e.toAlgHom
  exact ⟨⟨E1, h3, h4⟩, hEq⟩

theorem restrict_eq (rec₁ rec₂ : Kˣ ≃ₜ* Ab K) (hf : family K rec₁ = family K rec₂)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ) :
    Ab.restrict K L (rec₁ x) = Ab.restrict K L (rec₂ x) := by
  obtain ⟨E, rfl⟩ := exists_liftE_eq K L
  have := congrArg (fun f => f E x) hf
  exact (AlgEquiv.autCongr (eqv K E).symm).injective this

end Langlands.RecUnique

namespace Langlands

open RecUnique WeilGroup

/-- **Uniqueness of local reciprocity.** Two topological isomorphisms $K^\times \cong W_K^{ab}$
with the properties of `IsLocalArtinMap` are equal. -/
theorem isLocalArtinMap_unique (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (rec₁ rec₂ : Kˣ ≃ₜ* WeilGroup.Ab K)
    (h₁ : IsLocalArtinMap K rec₁) (h₂ : IsLocalArtinMap K rec₂) : rec₁ = rec₂ := by
  have hf : family K rec₁ = family K rec₂ :=
    ClassFieldTheory.finiteAbelianLocalReciprocity_family_ext K _ _
      (family_ker K rec₁ h₁) (family_ker K rec₂ h₂) (family_coh K rec₁) (family_coh K rec₂)
      (fun E _ _ _ _ _ _ π hπ x => family_frob K rec₁ h₁ E π hπ x)
      (fun E _ _ _ _ _ _ π hπ x => family_frob K rec₂ h₂ E π hπ x)
  apply ContinuousMulEquiv.ext
  intro x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (rec₁ x * (rec₂ x)⁻¹)
  have hres : ∀ (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
      [IsAbelianGalois K L], restrict K L w = 1 := by
    intro L _ _
    rw [← Ab.restrict_mk, hw, map_mul, map_inv, restrict_eq K rec₁ rec₂ hf L x, mul_inv_cancel]
  have hmem : toGalois K w ∈
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure := by
    apply mem_closure_commutator_of_forall (F := K) (Ω := AlgebraicClosure K) (toGalois K w)
    intro L hfin hab y hy
    have h3 := congrArg (fun σ : Gal(L/K) => ((σ ⟨y, hy⟩ : L) : AlgebraicClosure K)) (hres L)
    exact (AlgEquiv.restrictNormalHom_apply L (toGalois K w) ⟨y, hy⟩).symm.trans h3
  have h1 : rec₁ x * (rec₂ x)⁻¹ = 1 := by
    apply toGaloisAb_injective K
    rw [← hw, toGaloisAb_mk, map_one, QuotientGroup.eq_one_iff]
    exact hmem
  exact mul_inv_eq_one.mp h1

end Langlands

