/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.All
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.KroneckerWeber
import Langlands.Statements.ClassField
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The bridge to the NYLL port of global class field theory

The port in `Langlands/Ported/NYLL` proves the main theorems of global class field theory for number fields: finite abelian global reciprocity, the existence theorem, the Artin map to the abelianized absolute Galois group, and the theorem of Kronecker and Weber. This file restates these theorems in the terms of `Langlands/Statements/ClassField.lean`.

* `Langlands.Bridge.kroneckerWeber`: the statement `Langlands.KroneckerWeber`, from the theorem `ClassFieldTheory.kroneckerWeber` of NYLL.
* `Langlands.Bridge.globalReciprocity`: the statement `Langlands.GlobalReciprocity`, from the norm residue map `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom` of NYLL.
* `Langlands.Bridge.globalExistence`: the statement `Langlands.GlobalExistence`, from the theorem `ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup` of NYLL.

## Implementation notes

The theorem of NYLL gives an embedding of a finite abelian extension $L$ of $\mathbb{Q}$ into the cyclotomic field $\mathbb{Q}(\zeta_n)$ as an abstract field. The statement of the project is about a subfield $L$ of the fixed algebraic closure $\overline{\mathbb{Q}}$. An embedding $\psi$ of $\mathbb{Q}(\zeta_n)$ into $\overline{\mathbb{Q}}$ gives an embedding of $L$ into $\overline{\mathbb{Q}}$. Its image is $L$, because $L$ is normal over $\mathbb{Q}$. So $L$ is in the image of $\psi$, which is $\mathbb{Q}(\psi(\zeta_n))$.

NYLL has more than one normalization of the Artin map. The norm residue map `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom` sends a uniformizer at an unramified place to the geometric Frobenius. Its pointwise inverse `arithmeticGlobalNormResidueMonoidHom` sends a uniformizer to the arithmetic Frobenius. The statement `Langlands.IsArtinMap` asks that the inverse of the image of a uniformizer is an arithmetic Frobenius. Thus the statement uses the geometric normalization, and the bridge uses the geometric map of NYLL with no change.

NYLL proves the existence theorem for a class field in the separable closure $K^{\mathrm{sep}}$. The statement of the project is about a subfield of the fixed algebraic closure $\overline{K}$. An embedding of the class field into $\overline{K}$ gives an isomorphic subfield. Isomorphic extensions have the same norm group. The kernel of the norm residue map is the norm group, so the two kernels are equal.
-/

namespace Langlands.Bridge

/-- **The theorem of Kronecker and Weber** (NYLL). Each finite abelian extension of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ is in $\mathbb{Q}(\zeta)$ for a primitive root of unity $\zeta$. -/
theorem kroneckerWeber : KroneckerWeber := by
  intro L hfin hab
  have : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨n, hn, ⟨φ⟩⟩ := ClassFieldTheory.kroneckerWeber L
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ℚ) := ⟨by exact_mod_cast hn.ne'⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let ψ : CyclotomicField n ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ζ := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  refine ⟨n, ψ ζ, hn, hζ.map_of_injective ψ.injective, ?_⟩
  have : Normal ℚ L := hab.toIsGalois.to_normal
  rw [← AlgHom.fieldRange_of_normal (ψ.comp φ)]
  rintro _ ⟨x, rfl⟩
  have hx : φ x ∈ Algebra.adjoin ℚ {ζ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    trivial
  have : ψ (φ x) ∈ Algebra.adjoin ℚ (ψ '' {ζ}) := by
    rw [← AlgHom.map_adjoin]
    exact ⟨φ x, hx, rfl⟩
  rw [Set.image_singleton] at this
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ _ this

section ClassField

open NumberField IsDedekindDomain ValuativeRel GlobalClassFieldTheory.Reciprocity

universe u v

/-- A uniformizer $\varpi$ of the completion $K_v$ has valuation $\exp(-1)$. The ring of integers of $K_v$ is the set of elements of valuation at most one. An element of valuation one is a unit. The valuation of $\varpi$ is at most $\exp(-1)$, because $\varpi$ is not a unit. It is at least $\exp(-1)$, because $\varpi$ is irreducible. -/
theorem valued_eq_exp_neg_one_of_isUniformizer {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K} (hx : IsUniformizer x) :
    Valued.v x = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ, rfl⟩ := hx
  have hE : (HeightOneSpectrum.adicCompletion.valuation K v).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion K)) :=
    ValuativeRel.isEquiv _ _
  have hmem : ∀ y : v.adicCompletion K, y ∈ 𝒪[v.adicCompletion K] ↔ Valued.v y ≤ 1 := by
    intro y
    change ValuativeRel.valuation _ y ≤ 1 ↔
      HeightOneSpectrum.adicCompletion.valuation K v y ≤ 1
    have := hE y 1
    simpa only [map_one] using this.symm
  have hunit : ∀ a : 𝒪[v.adicCompletion K], IsUnit a →
      Valued.v (a : v.adicCompletion K) = 1 := by
    rintro a ⟨u, rfl⟩
    have h1 := congrArg (fun z : 𝒪[v.adicCompletion K] => Valued.v (z : v.adicCompletion K))
      u.mul_inv
    simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at h1
    have ha : Valued.v ((u : 𝒪[v.adicCompletion K]) : v.adicCompletion K) ≤ 1 :=
      (hmem _).1 (u : 𝒪[v.adicCompletion K]).2
    have hb : Valued.v (((u⁻¹ : (𝒪[v.adicCompletion K])ˣ) : 𝒪[v.adicCompletion K]) :
        v.adicCompletion K) ≤ 1 :=
      (hmem _).1 ((u⁻¹ : (𝒪[v.adicCompletion K])ˣ) : 𝒪[v.adicCompletion K]).2
    refine le_antisymm ha ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ _ * 1 := by gcongr
      _ = _ := mul_one _
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hval0 : Valued.v (π : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  set n := WithZero.log (Valued.v (π : v.adicCompletion K)) with hn
  have hπn : Valued.v (π : v.adicCompletion K) = WithZero.exp n := (WithZero.exp_log hval0).symm
  have hlt : n < 0 := by
    have h1 : Valued.v (π : v.adicCompletion K) ≤ 1 := (hmem _).1 π.2
    rw [hπn, WithZero.exp_le_one_iff] at h1
    refine lt_of_le_of_ne h1 fun h0 => hπ.not_isUnit ?_
    have h2 : Valued.v (π : v.adicCompletion K) = 1 := by rw [hπn, h0, WithZero.exp_zero]
    have hinv : (π : v.adicCompletion K)⁻¹ ∈ 𝒪[v.adicCompletion K] :=
      (hmem _).2 (by rw [map_inv₀, h2, inv_one])
    exact ⟨⟨π, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπ0),
      Subtype.ext (inv_mul_cancel₀ hπ0)⟩,
      rfl⟩
  obtain ⟨s, hs⟩ :=
    HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hs
    exact WithZero.exp_ne_zero hs.symm
  have hge : -1 ≤ n := by
    by_contra hcon
    have hsmem : s ∈ 𝒪[v.adicCompletion K] :=
      (hmem s).2 (by rw [hs, WithZero.exp_le_one_iff]; norm_num)
    have hq : Valued.v ((π : v.adicCompletion K) / s) = WithZero.exp (n + 1) := by
      rw [map_div₀, hs, hπn, ← WithZero.exp_sub, sub_neg_eq_add]
    have hqmem : (π : v.adicCompletion K) / s ∈ 𝒪[v.adicCompletion K] :=
      (hmem _).2 (by rw [hq, WithZero.exp_le_one_iff]; omega)
    have hfac : π = (⟨s, hsmem⟩ : 𝒪[v.adicCompletion K]) * ⟨_, hqmem⟩ := by
      apply Subtype.ext
      change (π : v.adicCompletion K) = s * ((π : v.adicCompletion K) / s)
      field_simp
    rcases hπ.isUnit_or_isUnit hfac with h | h
    · have := hunit _ h
      change Valued.v s = 1 at this
      rw [hs, ← WithZero.exp_zero, WithZero.exp_inj] at this
      norm_num at this
    · have := hunit _ h
      change Valued.v ((π : v.adicCompletion K) / s) = 1 at this
      rw [hq, ← WithZero.exp_zero, WithZero.exp_inj] at this
      omega
  rw [hπn]
  congr 1
  omega

/-- Let $L/K$ be a finite abelian extension of number fields, and let $w$ be a maximal ideal of $\mathcal{O}_L$ over the finite place $v$ of $K$ where $L/K$ is unramified. Let $\varpi$ be a uniformizer of $K_v$. Then the inverse of the image of $\varpi$ under the norm residue map `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom` of NYLL is an arithmetic Frobenius at $w$. NYLL normalizes this map so that $\varpi$ goes to the geometric Frobenius. -/
theorem globalNormResidue_ofAdicCompletion_inv_isArithFrobAt
    (K : Type u) [Field K] [NumberField K] (L : Type v) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : HeightOneSpectrum (𝓞 K)) (w : Ideal (𝓞 L)) [w.IsMaximal]
    (hw : w.LiesOver p.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w)
    (ϖ : (p.adicCompletion K)ˣ) (hϖ : IsUniformizer (ϖ : p.adicCompletion K)) :
    IsArithFrobAt (𝓞 K)
      (globalNormResidueMonoidHom K L
        (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K p ϖ))⁻¹ w := by
  classical
  have hw0 : w ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (NumberField.RingOfIntegers.not_isField L)
  let W : HeightOneSpectrum (𝓞 L) := ⟨w, inferInstance, hw0⟩
  let w₀ := chosenFinitePlaceExtension (L := L) p
  let Wc := finitePlaceExtensionCentre (K := K) (L := L) p w₀
  let P : Ideal (𝓞 K) := p.asIdeal
  let Q : Ideal (𝓞 L) := Wc.asIdeal
  let G := L ≃ₐ[K] L
  have hW : Q.LiesOver P := finitePlaceExtensionCentre_liesOver (K := K) (L := L) p w₀
  let : Q.LiesOver P := hW
  let : w.LiesOver P := hw
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hEw : w.ramificationIdx (𝓞 K) = 1 := (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : Q.ramificationIdx (𝓞 K) = w.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Q w G
  have hunramQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)
  have hChosen : ChosenFinitePlaceIsUnramified (K := K) (L := L) p :=
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt (K := K) (L := L) p hunramQ
  have hord : (FiniteIdeleGroup.localOrder p ϖ).toAdd = 1 := by
    rw [FiniteIdeleGroup.localOrder_apply, valued_eq_exp_neg_one_of_isUniformizer p hϖ,
      WithZero.log_exp, neg_neg]
  have hgeo : globalNormResidueMonoidHom K L
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K p ϖ) =
      GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin (K := K) (L := L) p := by
    have h1 := DFunLike.congr_fun
      (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass (K := K) (L := L) p) ϖ
    rw [MonoidHom.comp_apply] at h1
    change globalNormResidueMonoidHom K L (IdeleGroup.finitePlaceIdeleClass p ϖ) = _
    rw [h1,
      GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArtin_eq_primeArtin_zpow_of_chosenUnramified
        p hChosen ϖ, hord, zpow_one]
  rw [hgeo, ← GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv,
    ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
      p W hw hunram]
  exact IsArithFrobAt.arithFrobAt (𝓞 K) G W.asIdeal

/-- The norm residue map `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom` of NYLL is an Artin map in the sense of `Langlands.IsArtinMap`. -/
theorem isArtinMap_globalNormResidue (K : Type u) [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsAbelianGalois K L]
    [NumberField L] :
    IsArtinMap K L (globalNormResidueMonoidHom K L) where
  continuous := globalNormResidueMonoidHom_continuous K L
  surjective := globalNormResidueMonoidHom_surjective K L
  frobenius p w _ hw hunram ϖ hϖ :=
    globalNormResidue_ofAdicCompletion_inv_isArithFrobAt K L p w hw hunram ϖ hϖ

/-- **Global reciprocity** (NYLL). Each finite abelian extension $L$ of a number field $K$ in $\overline{K}$ has an Artin map from the idele class group of $K$ to $\mathrm{Gal}(L/K)$. -/
theorem globalReciprocity : GlobalReciprocity.{u} := by
  intro K _ _ L hfin hab
  have : NumberField L := NumberField.of_module_finite K L
  exact ⟨_, isArtinMap_globalNormResidue K L⟩

/-- **The global existence theorem** (NYLL). Each open subgroup of finite index of the idele class group of a number field $K$ is the kernel of the Artin map of a finite abelian extension of $K$ in $\overline{K}$. -/
theorem globalExistence : GlobalExistence.{u} := by
  intro K _ _ U hU hfi
  have hclosed : IsClosed (U : Set (NumberField.IdeleClassGroup (𝓞 K) K)) :=
    U.isClosed_of_isOpen hU
  let E := GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField (K := K) U hclosed
  have : NumberField E := NumberField.of_module_finite K E
  let φ : E →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let L : IntermediateField K (AlgebraicClosure K) := φ.fieldRange
  let e : E ≃ₐ[K] L := AlgEquiv.ofInjectiveField φ
  have hfinL : FiniteDimensional K L := LinearEquiv.finiteDimensional e.toLinearEquiv
  have habL : IsAbelianGalois K L := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have : NumberField L := NumberField.of_module_finite K L
  refine ⟨L, GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom K L, hfinL, habL,
    isArtinMap_globalNormResidue K L, ?_⟩
  have hrange : (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K E).range := by
    rw [ordinaryIdeleClassNorm_range_eq_relative (K := K) (L := L),
      ordinaryIdeleClassNorm_range_eq_relative (K := K) (L := E)]
    exact ideleClassNorm_range_algEquiv (K := K) e
  ext c
  rw [MonoidHom.mem_ker, GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_eq_one_iff,
    hrange,
    ClassFieldTheory.GlobalClassFieldComparison.classFieldExistence_normSubgroup K U hclosed]

end ClassField

end Langlands.Bridge
