/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.ReducibleCase

/-!
# The reducible quotient case of the principal series of $GL_2$

Let $K$ be a nonarchimedean local field, let $G = GL_2(K)$ and $B = TN$ the Borel subgroup of the upper triangular matrices. Let $\chi_1, \chi_2$ be smooth characters of $K^\times$. The file `Langlands/Smooth/ReducibleCase.lean` proves that the normalized principal series of $(\chi_1, \chi_2)$ is reducible if $\chi_2 = \chi_1 |\cdot|$. This file proves that it is reducible if $\chi_1 = \chi_2 |\cdot|$ too. With `Langlands.normPrincipalSeries_irreducible`, this gives the full irreducibility criterion: the normalized principal series is irreducible exactly when $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$.

## Main results

* `Langlands.absChar_ne_one`: the character $|\cdot|$ of $K^\times$ is not trivial.
* `Langlands.GL2.torus_mul_comm`: the diagonal torus $T$ is commutative.
* `Langlands.principalSeriesJacquet_exists_hom_bigCellChar`: if $\alpha_1 \otimes \alpha_2 \neq$ `Langlands.bigCellChar` on $T$, then the Jacquet module of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ has a nonzero map of representations of $T$ to `Langlands.bigCellChar`.
* `Langlands.principalSeriesInd_exists_bijective_of_isIrreducible`: if moreover $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ is irreducible, then it is isomorphic to $\mathrm{Ind}_B^G(\alpha_2 |\cdot| \otimes \alpha_1 |\cdot|^{-1})$.
* `Langlands.SmoothRep.IsIrreducible.of_bijective`: a representation with a bijective map of representations from an irreducible one is irreducible.
* `Langlands.principalSeriesInd_not_isIrreducible_of_eq_mul_sq`: if $\alpha_1 = \alpha_2 |\cdot|^2$, then $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ is not irreducible.
* `Langlands.normPrincipalSeries_not_isIrreducible_of_eq_mul`: if $\chi_1 = \chi_2 |\cdot|$, then the normalized principal series of $(\chi_1, \chi_2)$ is not irreducible.
* `Langlands.normPrincipalSeries_isIrreducible_iff`: the normalized principal series of $(\chi_1, \chi_2)$ is irreducible exactly when $\chi_1 \neq \chi_2 |\cdot|$ and $\chi_2 \neq \chi_1 |\cdot|$.

## Method

The proof is by contradiction and uses the Jacquet module, not an integral over $GL_2(\mathcal{O}_K)$. Let $\chi_1 = \chi_2 |\cdot|$. Then the normalized principal series is $V = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ with $\alpha_1 = \chi_1 |\cdot|^{1/2}$ and $\alpha_2 = \chi_2 |\cdot|^{-1/2}$, so $\alpha_1 = \alpha_2 |\cdot|^2$. The Jacquet module $V_N$ has dimension $2$, with the character $\beta = $ `Langlands.bigCellChar` on a line and $\alpha_1 \otimes \alpha_2$ on the quotient. These characters differ since $|\cdot| \neq 1$. Thus, for $t_0 \in T$ with distinct values of the two characters, the operator $t_0 - (\alpha_1 \otimes \alpha_2)(t_0)$ maps $V_N$ onto the line of $\beta$, and $V_N$ maps onto $\beta$. Frobenius reciprocity gives a nonzero map $\Phi : V \to V' = \mathrm{Ind}_B^G(\beta)$, with $\beta = \chi \otimes \chi$ for $\chi = \alpha_2 |\cdot|$.

Suppose that $V$ is irreducible. Then $\Phi$ is injective. Its image $W$ meets the big cell subspace $V'_w$, because the evaluation at $1$ of $\Phi(v)$ is the image of the class of $v$ in $\beta$, and this map has a kernel on the space $V_N$ of dimension $2$. By `Langlands.jacquetKer_le_of_inf_ne_bot`, $W$ contains $V'(N)$. The Jacquet functor keeps injections, so $V_N \to V'_N$ is injective, thus bijective since both spaces have dimension $2$. Then $W + V'(N) = V'$, so $W = V'$ and $\Phi$ is bijective. But $V' = \mathrm{Ind}_B^G(\chi \otimes \chi)$ contains the line of $\chi \circ \det$ by `Langlands.principalSeriesInd_not_isIrreducible`, so $V'$ is not irreducible, and neither is $V$.

## Open parts

The file does not construct the map from the principal series onto the character $\chi \circ \det$ with $\chi = \chi_2 |\cdot|^{1/2}$ in the case $\chi_1 = \chi_2 |\cdot|$. It only proves that a proper nonzero stable subspace exists, without a description of it. The file also does not prove that the principal series has length $2$ in the reducible cases, nor that the twisted Steinberg representation is irreducible.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
-/

universe u

open Representation Matrix

namespace Langlands

section Absolute

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open ValuativeRel

/-- The residue field of $K$ has more than one element. -/
theorem one_lt_residueCard' : 1 < residueCard K := by
  unfold residueCard
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- The character $|\cdot|$ of $K^\times$ is not trivial: a uniformizer has absolute value $q^{-1} \neq 1$. -/
theorem absChar_ne_one : absChar K ≠ 1 := by
  intro h
  obtain ⟨π, hπ0, hπ⟩ := exists_valuation_eq_uniformizer (K := K)
  have h1 := congrArg (fun χ : Kˣ →* ℂˣ => ((χ (Units.mk0 π hπ0) : ℂˣ) : ℂ)) h
  simp only [absChar_apply, MonoidHom.one_apply, Units.val_one] at h1
  rw [Units.val_mk0, normAbs_eq_zpow hπ0 (k := 1) (by rw [zpow_one]; exact hπ)] at h1
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard'
  have h2 : ((residueCard K : ℝ) ^ (-1 : ℤ)) = 1 := by exact_mod_cast h1
  rw [_root_.zpow_neg_one] at h2
  have := inv_lt_one_of_one_lt₀ hq
  linarith

end Absolute

namespace GL2

variable {K : Type u} [Field K]

/-- The diagonal torus is commutative. -/
theorem torus_mul_comm (s t : torus K) : s * t = t * s := by
  have hs := (mem_torus _).1 s.2
  have ht := (mem_torus _).1 t.2
  refine Subtype.ext (Units.ext ?_)
  change (s : GL (Fin 2) K).1 * (t : GL (Fin 2) K).1 = (t : GL (Fin 2) K).1 * (s : GL (Fin 2) K).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hs.1, hs.2, ht.1, ht.2, mul_comm]

end GL2

section JacquetSplitting

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

variable {α₁ α₂ : Kˣ →* ℂˣ} {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}

local notation "Ψ" => principalSeriesInd α₁ α₂ hα₁ hα₂

local notation "ΨN" => principalSeriesJacquet α₁ α₂ hα₁ hα₂

local notation "ev" => principalSeriesJacquetEval α₁ α₂ hα₁ hα₂

/-- If the two characters $\alpha_1 \otimes \alpha_2$ and `bigCellChar` of $T$ differ, then the Jacquet module $V_N$ of the principal series has a nonzero map of representations of $T$ to `bigCellChar`. For $t_0$ with $\lambda = (\alpha_1 \otimes \alpha_2)(t_0) \neq$ `bigCellChar` $(t_0)$, the operator $t_0 - \lambda$ maps $V_N$ into the line of $y_1$, and a linear form that is not zero at $y_1$ gives the map. -/
theorem principalSeriesJacquet_exists_hom_bigCellChar
    (h : ∃ t, torusChar α₁ α₂ t ≠ bigCellChar α₁ α₂ t) :
    ∃ φ : IntertwiningMap (ΨN).ρ
      (charRep (bigCellChar α₁ α₂) (isOpen_ker_bigCellChar hα₁ hα₂)).ρ, φ ≠ 0 := by
  obtain ⟨t₀, ht₀⟩ := h
  obtain ⟨x₀, y₁, -, hy0, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := α₁) (χ₂ := α₂) (hχ₁ := hα₁) (hχ₂ := hα₂)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (ΨN).V, ℓ y₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy0 ((Module.forall_dual_apply_eq_zero_iff ℂ y₁).1 hc)
  set c₀ : ℂ := (torusChar α₁ α₂ t₀ : ℂ)
  set ψ : (ΨN).V →ₗ[ℂ] (ΨN).V := (ΨN).ρ t₀ - c₀ • LinearMap.id
  have hψ : ∀ x, ∃ c : ℂ, ψ x = c • y₁ := by
    intro x
    obtain ⟨c, hc⟩ := hspan (ψ x)
    have he : (ev (ψ x)).down = 0 := by
      change (ev ((ΨN).ρ t₀ x - c₀ • x)).down = 0
      rw [map_sub, map_smul]
      change (ev ((ΨN).ρ t₀ x)).down - c₀ * (ev x).down = 0
      rw [principalSeriesJacquetEval_ρ]
      ring
    exact ⟨c, by rw [hc, he, zero_smul, zero_add]⟩
  have hρψ : ∀ t x, (ΨN).ρ t (ψ x) = (bigCellChar α₁ α₂ t : ℂ) • ψ x := by
    intro t x
    obtain ⟨c, hc⟩ := hψ x
    rw [hc, map_smul, hρy, smul_comm]
  have hcomm : ∀ t x, ψ ((ΨN).ρ t x) = (ΨN).ρ t (ψ x) := by
    intro t x
    change (ΨN).ρ t₀ ((ΨN).ρ t x) - c₀ • (ΨN).ρ t x =
      (ΨN).ρ t ((ΨN).ρ t₀ x - c₀ • x)
    rw [map_sub, map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul, torus_mul_comm]
  refine ⟨{ toLinearMap := (ULift.moduleEquiv.symm : ℂ ≃ₗ[ℂ] ULift.{u} ℂ).toLinearMap ∘ₗ ℓ ∘ₗ ψ
            isIntertwining' := fun t => ?_ }, fun h0 => ?_⟩
  · ext x
    apply ULift.ext
    change ℓ (ψ ((ΨN).ρ t x)) = (bigCellChar α₁ α₂ t : ℂ) * ℓ (ψ x)
    rw [hcomm, hρψ, map_smul, smul_eq_mul]
  · have h1 := congrArg (fun F : IntertwiningMap _ _ => (F y₁).down) h0
    change ℓ ((ΨN).ρ t₀ y₁ - c₀ • y₁) = 0 at h1
    rw [hρy, ← sub_smul, map_smul, smul_eq_mul] at h1
    refine (mul_ne_zero (sub_ne_zero.2 fun e => ht₀ (Units.ext e.symm)) hℓ) h1

local notation "Ψ'" => principalSeriesInd (α₂ * absChar K) (α₁ * (absChar K)⁻¹)
  (hα₂.mul isSmoothChar_absChar) (hα₁.mul isSmoothChar_absChar.inv)

/-- Let the principal series $V = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ be irreducible, and let $\alpha_1 \otimes \alpha_2 \neq$ `bigCellChar` on $T$. Then $V$ is isomorphic to $V' = \mathrm{Ind}_B^G(\alpha_2 |\cdot| \otimes \alpha_1 |\cdot|^{-1})$: there is a bijective map of representations $V \to V'$. Frobenius reciprocity gives a nonzero map $\Phi$, which is injective since $V$ is irreducible. Its image $W$ meets the big cell subspace $V'_w$, so $W$ contains $V'(N)$. The map $V_N \to V'_N$ is injective, and both spaces have dimension $2$, so it is bijective and $W + V'(N) = V'$. -/
theorem principalSeriesInd_exists_bijective_of_isIrreducible (hirr : (Ψ).IsIrreducible)
    (h : ∃ t, torusChar α₁ α₂ t ≠ bigCellChar α₁ α₂ t) :
    ∃ Φ : IntertwiningMap (Ψ).ρ (Ψ').ρ, Function.Bijective Φ := by
  obtain ⟨φ, hφ⟩ := principalSeriesJacquet_exists_hom_bigCellChar h
  set e := (Ψ).jacquetFrobenius (hα₂.mul isSmoothChar_absChar)
    (hα₁.mul isSmoothChar_absChar.inv)
  set Φ : IntertwiningMap (Ψ).ρ (Ψ').ρ := e.symm φ
  have hΦ0 : Φ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hφ
  have hinj : Function.Injective Φ := hirr.injective Φ hΦ0
  have hΦ1 : ∀ v, ind.toFun (Φ v) 1 = φ ((Ψ).jacquetMk _ _ torus_le_normalizer_unipotent v) := by
    intro v
    have h1 := (Ψ).jacquetFrobenius_symm_apply (hα₂.mul isSmoothChar_absChar)
      (hα₁.mul isSmoothChar_absChar.inv) φ v 1
    rw [map_one, Module.End.one_apply] at h1
    exact h1
  set W : Submodule ℂ (Ψ').V := LinearMap.range Φ.toLinearMap
  have hW : IsStableSubspace (Ψ').ρ W := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨(Ψ).ρ g v, IntertwiningMap.isIntertwining _ _ Φ g v⟩
  have := principalSeriesJacquet_finite (χ₁ := α₁) (χ₂ := α₂) (hχ₁ := hα₁) (hχ₂ := hα₂)
  have hker : LinearMap.ker φ.toLinearMap ≠ ⊥ := by
    have : Module.Finite ℂ (charRep (bigCellChar α₁ α₂) (isOpen_ker_bigCellChar hα₁ hα₂)).V :=
      Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).symm
    intro hk
    have h1 := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    rw [hk, finrank_bot, add_zero, finrank_principalSeriesJacquet] at h1
    have h2 := Submodule.finrank_le (LinearMap.range φ.toLinearMap)
    have h3 : Module.finrank ℂ (ULift.{u} ℂ) = 1 := by
      rw [ULift.moduleEquiv.finrank_eq, Module.finrank_self]
    change _ ≤ Module.finrank ℂ (ULift.{u} ℂ) at h2
    omega
  have hWw : W ⊓ principalSeriesBigCell _ _ (hα₂.mul isSmoothChar_absChar)
      (hα₁.mul isSmoothChar_absChar.inv) ≠ ⊥ := by
    intro hb
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    obtain ⟨v, rfl⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent x
    have hmem : Φ v ∈ W ⊓ principalSeriesBigCell _ _ (hα₂.mul isSmoothChar_absChar)
        (hα₁.mul isSmoothChar_absChar.inv) := by
      refine Submodule.mem_inf.2 ⟨⟨v, rfl⟩, ?_⟩
      change ind.toFun (Φ v) 1 = 0
      rw [hΦ1]
      exact hx
    rw [hb, Submodule.mem_bot] at hmem
    have hv : v = 0 := hinj (hmem.trans (map_zero Φ).symm)
    exact hx0 (by rw [hv]; exact map_zero _)
  have hN : (Ψ').jacquetKer (unipotent K) ≤ W := jacquetKer_le_of_inf_ne_bot hW hWw
  set J := SmoothRep.jacquetMap torus_le_normalizer_unipotent Φ
  have hJinj : Function.Injective J :=
    SmoothRep.jacquetMap_unipotent_injective torus_le_normalizer_unipotent Φ hinj
  have := principalSeriesJacquet_finite (χ₁ := α₂ * absChar K) (χ₂ := α₁ * (absChar K)⁻¹)
    (hχ₁ := hα₂.mul isSmoothChar_absChar) (hχ₂ := hα₁.mul isSmoothChar_absChar.inv)
  have hJsurj : Function.Surjective J := by
    have hd := (finrank_principalSeriesJacquet (χ₁ := α₁) (χ₂ := α₂) (hχ₁ := hα₁)
      (hχ₂ := hα₂)).trans (finrank_principalSeriesJacquet (χ₁ := α₂ * absChar K)
      (χ₂ := α₁ * (absChar K)⁻¹) (hχ₁ := hα₂.mul isSmoothChar_absChar)
      (hχ₂ := hα₁.mul isSmoothChar_absChar.inv)).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd (f := J.toLinearMap)).1
      hJinj
  refine ⟨Φ, hinj, fun v' => ?_⟩
  obtain ⟨x, hx⟩ := hJsurj ((Ψ').jacquetMk _ _ torus_le_normalizer_unipotent v')
  obtain ⟨v, rfl⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent x
  rw [SmoothRep.jacquetMap_mk] at hx
  have hk : v' - Φ v ∈ (Ψ').jacquetKer (unipotent K) := by
    rw [← (Ψ').jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, hx, sub_self]
  obtain ⟨u, hu⟩ := hN hk
  exact ⟨u + v, by rw [map_add]; rw [show Φ u = v' - Φ v from hu]; abel⟩

end JacquetSplitting

section Transfer

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- If $\pi$ is irreducible and $\Phi : \pi \to \sigma$ is a bijective map of representations, then $\sigma$ is irreducible: the preimage of a stable subspace of $\sigma$ is a stable subspace of $\pi$. -/
theorem SmoothRep.IsIrreducible.of_bijective {π σ : SmoothRep G} (hπ : π.IsIrreducible)
    (Φ : IntertwiningMap π.ρ σ.ρ) (hΦ : Function.Bijective Φ) : σ.IsIrreducible := by
  have := hπ.1
  refine ⟨hΦ.1.nontrivial, fun W hW => ?_⟩
  have hU : IsStableSubspace π.ρ (W.comap Φ.toLinearMap) := by
    intro g v hv
    change Φ (π.ρ g v) ∈ W
    rw [IntertwiningMap.isIntertwining]
    exact hW g hv
  rcases hπ.2 _ hU with h | h
  · refine Or.inl ((Submodule.eq_bot_iff W).2 fun w hw => ?_)
    obtain ⟨v, rfl⟩ := hΦ.2 w
    have hv : v ∈ W.comap Φ.toLinearMap := hw
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · refine Or.inr (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨v, rfl⟩ := hΦ.2 w
    have hv : v ∈ W.comap Φ.toLinearMap := h ▸ Submodule.mem_top
    exact hv

end Transfer

section Reducible

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- The principal series $\mathrm{Ind}_B^G(\beta_1 \otimes \beta_2)$ with $\beta_1 = \beta_2$ is not irreducible, in a form with an equation between the two characters. -/
theorem principalSeriesInd_not_isIrreducible_of_eq {β₁ β₂ : Kˣ →* ℂˣ}
    {hβ₁ : IsSmoothChar K β₁} {hβ₂ : IsSmoothChar K β₂} (h : β₁ = β₂) :
    ¬ (principalSeriesInd β₁ β₂ hβ₁ hβ₂).IsIrreducible := by
  subst h
  exact principalSeriesInd_not_isIrreducible hβ₁

variable {α₁ α₂ : Kˣ →* ℂˣ} {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}

local notation "Ψ" => principalSeriesInd α₁ α₂ hα₁ hα₂

/-- The unnormalized reducible quotient case: if $\alpha_1 = \alpha_2 |\cdot|^2$, then $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ is not irreducible. If it were irreducible, it would be isomorphic to $\mathrm{Ind}_B^G(\chi \otimes \chi)$ with $\chi = \alpha_2 |\cdot|$, by `principalSeriesInd_exists_bijective_of_isIrreducible`, and that representation contains the line of $\chi \circ \det$. -/
theorem principalSeriesInd_not_isIrreducible_of_eq_mul_sq (h : α₁ = α₂ * absChar K ^ 2) :
    ¬ (Ψ).IsIrreducible := by
  intro hirr
  have hne : ∃ t, torusChar α₁ α₂ t ≠ bigCellChar α₁ α₂ t := by
    by_contra hc
    push Not at hc
    have he := (torusChar_inj.1 (MonoidHom.ext hc)).1
    apply absChar_ne_one (K := K)
    refine MonoidHom.ext fun x => ?_
    have h1 := DFunLike.congr_fun (h.symm.trans he) x
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, pow_two, MonoidHom.mul_apply,
      ← mul_assoc] at h1
    exact mul_eq_left.1 h1
  obtain ⟨Φ, hΦ⟩ := principalSeriesInd_exists_bijective_of_isIrreducible hirr hne
  refine principalSeriesInd_not_isIrreducible_of_eq ?_ (hirr.of_bijective Φ hΦ)
  rw [h, pow_two]
  ext x
  simp [mul_assoc]

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- The reducible quotient case: if $\chi_1 = \chi_2 |\cdot|$, that is, $\chi_1 \chi_2^{-1} = |\cdot|$, then the normalized principal series of $(\chi_1, \chi_2)$ is not irreducible. The unnormalized characters are $\alpha_1 = \chi_1 |\cdot|^{1/2}$ and $\alpha_2 = \chi_2 |\cdot|^{-1/2}$, with $\alpha_1 = \alpha_2 |\cdot|^2$. -/
theorem normPrincipalSeries_not_isIrreducible_of_eq_mul (h : χ₁ = χ₂ * absChar K) :
    ¬ (Π).IsIrreducible := by
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  refine principalSeriesInd_not_isIrreducible_of_eq_mul_sq ?_
  rw [h, ← sqrtAbsChar_sq]
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, pow_two, Units.val_mul,
    Units.val_inv_eq_inv_val]
  have hs : (sqrtAbsChar K x : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

/-- The irreducibility criterion of Bushnell and Henniart, chapter 3, section 9: the normalized principal series of $(\chi_1, \chi_2)$ is irreducible exactly when $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$, that is, when $\chi_1 \neq \chi_2 |\cdot|$ and $\chi_2 \neq \chi_1 |\cdot|$. -/
theorem normPrincipalSeries_isIrreducible_iff :
    (Π).IsIrreducible ↔ χ₁ ≠ χ₂ * absChar K ∧ χ₂ ≠ χ₁ * absChar K :=
  ⟨fun hirr => ⟨fun h => normPrincipalSeries_not_isIrreducible_of_eq_mul h hirr,
    fun h => normPrincipalSeries_not_isIrreducible h hirr⟩,
    fun h => normPrincipalSeries_irreducible h.1 h.2⟩

end Reducible

end Langlands
