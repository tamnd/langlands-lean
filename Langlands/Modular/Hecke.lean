/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex
import Langlands.Statements.Modularity

/-!
# The Hecke operators $T_p$ and $U_p$ on modular forms for $\Gamma_0(N)$

Let $p$ be a prime, let $N \ge 1$ and let $\alpha = \mathrm{diag}(1, p)$. This file defines the Hecke operator of the double coset $\Gamma_0(N) \alpha \Gamma_0(N)$ on modular forms and on cusp forms of weight $k$ for $\Gamma_0(N)$. For $p \nmid N$ this is the operator $T_p$, and for $p \mid N$ it is the operator $U_p$. The file computes the operator explicitly, it computes its effect on $q$-expansions, it shows that $T_p T_q = T_q T_p$ for distinct primes, and it defines Hecke eigenforms.

## Main definitions

* `Langlands.Modular.heckeT`: the operator $f \mapsto \sum_{\gamma} f \mid_k \alpha \gamma$ on `ModularForm Γ₀(N) k`, where $\gamma$ runs over the cosets of $\alpha^{-1} \Gamma_0(N) \alpha \cap \Gamma_0(N)$ in $\Gamma_0(N)$.
* `Langlands.Modular.cuspHeckeT`: the same operator on `CuspForm Γ₀(N) k`.
* `Langlands.Modular.heckeCoeff`: the map $a \mapsto (m \mapsto a_{mp} + p^{k-1} a_{m/p})$ on coefficient sequences, where the second term is present only for $p \nmid N$ and $p \mid m$.
* `Langlands.Modular.IsHeckeEigenvector`: $T_p f = c f$.
* `Langlands.Modular.IsHeckeEigenform`: $f \neq 0$ and $f$ is an eigenvector of $T_\ell$ for each prime $\ell$.
* `Langlands.Modular.IsNormalizedHeckeEigenform`: a Hecke eigenform with $a_1 = 1$.

## Main results

* `Langlands.Modular.heckeT_apply_of_not_dvd`: for $p \nmid N$, $(T_p f)(\tau) = p^{-1} \sum_{j < p} f((\tau + j)/p) + p^{k-1} f(p \tau)$.
* `Langlands.Modular.heckeT_apply_of_dvd`: for $p \mid N$, $(U_p f)(\tau) = p^{-1} \sum_{j < p} f((\tau + j)/p)$.
* `Langlands.Modular.coeff_heckeT`: $a_m(T_p f) = a_{mp}(f) + p^{k-1} a_{m/p}(f)$, where the second term is present only for $p \nmid N$ and $p \mid m$.
* `Langlands.Modular.coeff_heckeT_of_not_dvd` and `Langlands.Modular.coeff_heckeT_of_dvd`: the two cases of `coeff_heckeT`.
* `Langlands.Modular.heckeT_comm`: $T_p T_q = T_q T_p$ for distinct primes $p$ and $q$.
* `Langlands.Modular.eigenvalue_eq_qCoeff`: if $T_p f = c f$ and $a_1(f) = 1$, then $c = a_p(f)$.
* `Langlands.Modular.IsNormalizedHeckeEigenform.good` and `Langlands.Modular.IsNormalizedHeckeEigenform.bad`: a normalized Hecke eigenform satisfies the fields `good` and `bad` of `Langlands.IsNormalizedEigenform`.

## Proof

The operator is `ModularForm.trace Γ₀(N) (ModularForm.translate f α)` from Mathlib, so the trace and the translation give that $T_p f$ is a modular form, and a cusp form if $f$ is a cusp form. Mathlib uses the slash action $f \mid_k g = \det(g)^{k-1} (c\tau + d)^{-k} f(g\tau)$, so this operator is the operator $T_p$ of Diamond and Shurman. The group $\alpha^{-1} \Gamma_0(N) \alpha \cap \Gamma_0(N)$ is the set of $\gamma \in \Gamma_0(N)$ with $p \mid \gamma_{01}$ (`mapGL_mem_conj_iff`). Its cosets are the cosets of $T^{-j}$ for $0 \le j < p$, and for $p \nmid N$ also the coset of $\delta^{-1}$, where $\delta = [[p, b], [N, d]]$ with $pd - Nb = 1$ (`bijective_cosetMk_tRep` and `bijective_cosetRep`). The identity $\alpha \delta = \gamma' \mathrm{diag}(p, 1)$ with $\gamma' \in \Gamma_0(N)$ gives the term $p^{k-1} f(p\tau)$. The $q$-expansion formula follows from the orthogonality of the $p$-th roots of unity (`sum_exp_pow`) and the uniqueness of $q$-expansion coefficients. The commutation follows because the maps `heckeCoeff p` and `heckeCoeff q` commute, and because a modular form is determined by its $q$-expansion.

## What is left

The file does not define the operators $T_n$ for composite $n$, and it does not prove the relation $T_{mn} = T_m T_n$ for coprime $m$ and $n$. Thus it does not prove that a normalized Hecke eigenform has multiplicative coefficients, which is the field `mul` of `Langlands.IsNormalizedEigenform`. The file does not show that $T_p$ is linear, and it does not treat the diamond operators or the forms with a nontrivial character.

## References

* F. Diamond and J. Shurman, A first course in modular forms, chapter 5, sections 5.1 to 5.3.
* G. Shimura, Introduction to the arithmetic theory of automorphic functions, chapter 3.
-/

namespace Langlands.Modular

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup ConjAct Pointwise
open scoped MatrixGroups ModularForm

/-- The matrix `diag(1, p)` in `GL(2, ℚ)`. -/
noncomputable def heckeMatQ (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (p : ℚ)]
    (by simp [Matrix.det_fin_two_of, (Fact.out : p.Prime).ne_zero])

/-- The matrix `diag(1, p)` in `GL(2, ℝ)`. -/
noncomputable def heckeMat (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  (heckeMatQ p).map (Rat.castHom ℝ)

variable (p : ℕ) [Fact p.Prime] (N : ℕ)

/-- The matrix of `heckeMat p` is `diag(1, p)`. -/
lemma heckeMat_coe : (heckeMat p : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [heckeMat, heckeMatQ]

/-- The conjugate `α⁻¹ Γ₀(N) α` is an arithmetic subgroup, with `α = diag(1, p)`. -/
instance [NeZero N] : (toConjAct (heckeMat p)⁻¹ • (Gamma0 N : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  have := Subgroup.IsArithmetic.conj (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (heckeMatQ p)⁻¹
  simpa [heckeMat, map_inv] using this

/-- The group `α⁻¹ Γ₀(N) α ∩ Γ₀(N)` has finite index in `Γ₀(N)`. -/
instance [NeZero N] : (toConjAct (heckeMat p)⁻¹ • (Gamma0 N : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  (Subgroup.IsArithmetic.is_commensurable.trans
    Subgroup.IsArithmetic.is_commensurable.symm).1

omit [Fact p.Prime] in
/-- The entries of the image of `g` in `GL(2, ℝ)` are the entries of `g`. -/
lemma mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : Matrix (Fin 2) (Fin 2) ℝ) i j = (g i j : ℝ) := rfl

omit [Fact p.Prime] in
/-- The entries of the image in `GL(2, ℝ)` of the matrix `A` of determinant 1 are the entries of `A`. -/
lemma mapGL_mk_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (h : A.det = 1) (i j : Fin 2) :
    (mapGL ℝ (⟨A, h⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := rfl

/-- An element `γ` of `Γ₀(N)` is in `α⁻¹ Γ₀(N) α` if and only if `p` divides its upper right entry. -/
lemma mapGL_mem_conj_iff {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    mapGL ℝ γ ∈ toConjAct (heckeMat p)⁻¹ • (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ↔
      (p : ℤ) ∣ γ 0 1 := by
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  constructor
  · rintro ⟨δ, -, h⟩
    have h2 : mapGL ℝ δ * heckeMat p = heckeMat p * mapGL ℝ γ := by rw [h]; group
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) h2
    simp [heckeMat_coe, Matrix.mul_apply, Fin.sum_univ_two] at this
    exact ⟨δ 0 1, by exact_mod_cast (this.symm.trans (mul_comm _ _))⟩
  · rintro ⟨b, hb⟩
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have hδ : (!![γ 0 0, b; p * γ 1 0, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; rw [hb] at hdet; linear_combination hdet
    refine ⟨⟨_, hδ⟩, ?_, ?_⟩
    · have h0 := Gamma0_mem.mp hγ
      change ((p * γ 1 0 : ℤ) : ZMod N) = 0
      simp [h0]
    · rw [eq_mul_inv_iff_mul_eq]
      ext i j
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_mk_apply,
        mapGL_apply, heckeMat_coe]
      fin_cases i <;> fin_cases j <;> simp [hb] <;> ring

local notation "Γ₀" => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "𝒢" => toConjAct (heckeMat p)⁻¹ • (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The coset in `Γ₀(N) ⧸ (α⁻¹ Γ₀(N) α ∩ Γ₀(N))` of an element `γ` of `Γ₀(N)`, with `α = diag(1, p)`. -/
noncomputable def cosetMk (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : Γ₀ ⧸ (𝒢).subgroupOf Γ₀ :=
  QuotientGroup.mk (⟨mapGL ℝ γ, γ, hγ, rfl⟩ : Γ₀)

/-- Two elements of `Γ₀(N)` give the same coset if and only if `p` divides the upper right entry of `γ₁⁻¹ γ₂`. -/
lemma cosetMk_eq_iff {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    cosetMk p N γ₁ h₁ = cosetMk p N γ₂ h₂ ↔ (p : ℤ) ∣ (γ₁⁻¹ * γ₂) 0 1 := by
  rw [cosetMk, cosetMk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← map_inv, ← map_mul]
  exact mapGL_mem_conj_iff p N (mul_mem (inv_mem h₁) h₂)

/-- Each coset is the coset of an element of `Γ₀(N)`. -/
lemma exists_cosetMk (q : Γ₀ ⧸ (𝒢).subgroupOf Γ₀) : ∃ γ h, cosetMk p N γ h = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨x, γ, hγ, rfl⟩ := x
    exact ⟨γ, hγ, rfl⟩

/-- The representative `T⁻ʲ` of `SL(2, ℤ)`. -/
noncomputable def tRep (j : ℕ) : SL(2, ℤ) := ModularGroup.T ^ (-(j : ℤ))

/-- The matrix `T⁻ʲ` is in `Γ₀(N)`. -/
lemma tRep_mem (j : ℕ) : tRep j ∈ Gamma0 N := by
  rw [Gamma0_mem, tRep, ModularGroup.coe_T_zpow]
  simp

/-- The upper right entry of `Tⁿ γ` is `γ₀₁ + n γ₁₁`. -/
lemma T_zpow_mul_apply (n : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T ^ n * γ) 0 1 = γ 0 1 + n * γ 1 1 := by
  simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper right entry of `Tʲ γ` is `γ₀₁ + j γ₁₁`. -/
lemma tRep_inv_mul_apply (j : ℕ) (γ : SL(2, ℤ)) : ((tRep j)⁻¹ * γ) 0 1 = γ 0 1 + j * γ 1 1 := by
  rw [tRep, ← zpow_neg, neg_neg, T_zpow_mul_apply]

/-- The upper right entry of `T⁻ʲ` is `-j`. -/
lemma tRep_apply_01 (j : ℕ) : tRep j 0 1 = -j := by
  rw [tRep, ModularGroup.coe_T_zpow]; simp

/-- The lower right entry of `T⁻ʲ` is `1`. -/
lemma tRep_apply_11 (j : ℕ) : tRep j 1 1 = 1 := by
  rw [tRep, ModularGroup.coe_T_zpow]; simp

/-- The cosets of `T⁻ʲ` for `0 ≤ j < p` are distinct. -/
lemma cosetMk_tRep_injective :
    Function.Injective (fun j : Fin p => cosetMk p N (tRep j) (tRep_mem N j)) := by
  intro i j hij
  rw [cosetMk_eq_iff, tRep_inv_mul_apply, tRep_apply_01, tRep_apply_11] at hij
  obtain ⟨c, hc⟩ := hij
  have hi := i.isLt
  have hj := j.isLt
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  ext
  rcases lt_trichotomy c 0 with h | h | h
  · nlinarith
  · subst h; omega
  · nlinarith

/-- If `p ∤ N`, then `p` and `N` are coprime in `ℤ`. -/
lemma isCoprime_of_not_dvd (hpN : ¬ p ∣ N) : IsCoprime (p : ℤ) N :=
  Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN)

/-- The matrix `δ = [[p, b], [N, d]]` of `Γ₀(N)` with `p d - N b = 1`, for `p ∤ N`. -/
noncomputable def deltaRep (hpN : ¬ p ∣ N) : SL(2, ℤ) :=
  ⟨!![(p : ℤ), -(isCoprime_of_not_dvd p N hpN).choose_spec.choose;
      (N : ℤ), (isCoprime_of_not_dvd p N hpN).choose], by
    rw [Matrix.det_fin_two_of]
    linear_combination (isCoprime_of_not_dvd p N hpN).choose_spec.choose_spec⟩

/-- The matrix `δ` is in `Γ₀(N)`. -/
lemma deltaRep_mem (hpN : ¬ p ∣ N) : deltaRep p N hpN ∈ Gamma0 N := by
  rw [Gamma0_mem]
  change ((N : ℤ) : ZMod N) = 0
  simp

/-- The determinant relation `p d - N b = 1` for `δ = [[p, b], [N, d]]`. -/
lemma deltaRep_det (hpN : ¬ p ∣ N) :
    (p : ℤ) * deltaRep p N hpN 1 1 - N * deltaRep p N hpN 0 1 = 1 := by
  change (p : ℤ) * (isCoprime_of_not_dvd p N hpN).choose -
    N * -(isCoprime_of_not_dvd p N hpN).choose_spec.choose = 1
  linear_combination (isCoprime_of_not_dvd p N hpN).choose_spec.choose_spec

/-- The upper left entry of `δ` is `p`. -/
lemma deltaRep_apply_00 (hpN : ¬ p ∣ N) : deltaRep p N hpN 0 0 = p := rfl

/-- The lower left entry of `δ` is `N`. -/
lemma deltaRep_apply_10 (hpN : ¬ p ∣ N) : deltaRep p N hpN 1 0 = N := rfl

/-- The matrix `δ⁻¹` is in `Γ₀(N)`. -/
lemma deltaRep_inv_mem (hpN : ¬ p ∣ N) : (deltaRep p N hpN)⁻¹ ∈ Gamma0 N :=
  inv_mem (deltaRep_mem p N hpN)

/-- The prime `p` does not divide the upper right entry of `δ`. -/
lemma not_dvd_deltaRep_apply_01 (hpN : ¬ p ∣ N) : ¬ (p : ℤ) ∣ deltaRep p N hpN 0 1 := by
  rintro ⟨c, hc⟩
  have h := deltaRep_det p N hpN
  rw [hc] at h
  have : (p : ℤ) ∣ 1 := ⟨deltaRep p N hpN 1 1 - N * c, by linear_combination -h⟩
  exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- Each coset contains `T⁻ʲ` for some `j < p`, or `δ⁻¹` if `p ∤ N`. -/
lemma exists_tRep_or (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (∃ j : Fin p, cosetMk p N (tRep j) (tRep_mem N j) = cosetMk p N γ hγ) ∨
      ∃ hpN : ¬ p ∣ N, cosetMk p N _ (deltaRep_inv_mem p N hpN) = cosetMk p N γ hγ := by
  by_cases hd : (p : ℤ) ∣ γ 1 1
  · right
    have hpN : ¬ p ∣ N := by
      intro hpN
      have h0 := Gamma0_mem.mp hγ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      have hc : (p : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hpN).trans h0
      have hdet := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at hdet
      have : (p : ℤ) ∣ 1 := hdet ▸ dvd_sub (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right hc _)
      exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    refine ⟨hpN, ?_⟩
    rw [cosetMk_eq_iff, inv_inv]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      deltaRep_apply_00]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hd _)
  · left
    have hp : Fact p.Prime := inferInstance
    have hd' : ((γ 1 1 : ℤ) : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨⟨((-(γ 0 1 : ZMod p)) * ((γ 1 1 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _⟩, ?_⟩
    rw [cosetMk_eq_iff, tRep_inv_mul_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    ring

/-- The coset of `T⁻ʲ` is not the coset of `δ⁻¹`. -/
lemma cosetMk_tRep_ne_delta (hpN : ¬ p ∣ N) (j : ℕ) :
    cosetMk p N (tRep j) (tRep_mem N j) ≠ cosetMk p N _ (deltaRep_inv_mem p N hpN) := by
  rw [Ne, cosetMk_eq_iff, tRep_inv_mul_apply, Matrix.SpecialLinearGroup.SL2_inv_expl]
  change ¬ (p : ℤ) ∣ -deltaRep p N hpN 0 1 + j * deltaRep p N hpN 0 0
  rw [deltaRep_apply_00]
  intro h
  exact not_dvd_deltaRep_apply_01 p N hpN (by
    simpa using (dvd_neg.mpr (h.sub (dvd_mul_left (p : ℤ) j))))

/-- For `p ∣ N`, the cosets of `T⁻ʲ`, `0 ≤ j < p`, are all the cosets. -/
lemma bijective_cosetMk_tRep (hpN : p ∣ N) :
    Function.Bijective (fun j : Fin p => cosetMk p N (tRep j) (tRep_mem N j)) := by
  refine ⟨cosetMk_tRep_injective p N, fun q => ?_⟩
  obtain ⟨γ, hγ, rfl⟩ := exists_cosetMk p N q
  rcases exists_tRep_or p N γ hγ with h | ⟨h, -⟩
  · exact h
  · exact absurd hpN h

/-- The cosets of `δ⁻¹` and of `T⁻ʲ` for `0 ≤ j < p`, for `p ∤ N`. -/
noncomputable def cosetRep (hpN : ¬ p ∣ N) : Option (Fin p) → Γ₀ ⧸ (𝒢).subgroupOf Γ₀
  | none => cosetMk p N _ (deltaRep_inv_mem p N hpN)
  | some j => cosetMk p N (tRep j) (tRep_mem N j)

/-- For `p ∤ N`, the cosets of `δ⁻¹` and of `T⁻ʲ`, `0 ≤ j < p`, are all the cosets. -/
lemma bijective_cosetRep (hpN : ¬ p ∣ N) : Function.Bijective (cosetRep p N hpN) := by
  refine ⟨?_, fun q => ?_⟩
  · rintro (_ | i) (_ | j) h
    · rfl
    · exact absurd h.symm (cosetMk_tRep_ne_delta p N hpN j)
    · exact absurd h (cosetMk_tRep_ne_delta p N hpN i)
    · exact congrArg some (cosetMk_tRep_injective p N h)
  · obtain ⟨γ, hγ, rfl⟩ := exists_cosetMk p N q
    rcases exists_tRep_or p N γ hγ with ⟨j, h⟩ | ⟨_, h⟩
    · exact ⟨some j, h⟩
    · exact ⟨none, h⟩

section Operator

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- The Hecke operator `T_p` of the double coset `Γ₀(N) diag(1, p) Γ₀(N)` on modular forms of weight `k` for `Γ₀(N)`. It is the sum of the translates `f ∣[k] (α γ)` over the cosets `(α⁻¹ Γ₀(N) α ∩ Γ₀(N)) γ` of `Γ₀(N)`, with `α = diag(1, p)`. For `p ∣ N` this is the operator `U_p`. -/
noncomputable def heckeT [NeZero N] (f : F) [ModularFormClass F Γ₀ k] : ModularForm Γ₀ k :=
  ModularForm.trace Γ₀ (ModularForm.translate f (heckeMat p))

/-- The Hecke operator `T_p` on cusp forms of weight `k` for `Γ₀(N)`. -/
noncomputable def cuspHeckeT [NeZero N] (f : F) [CuspFormClass F Γ₀ k] : CuspForm Γ₀ k :=
  CuspForm.trace Γ₀ (CuspForm.translate f (heckeMat p))

/-- The function of `T_p f` for a cusp form `f` is the function of `T_p f` for `f` as a modular form. -/
lemma coe_cuspHeckeT [NeZero N] (f : F) [CuspFormClass F Γ₀ k] :
    ⇑(cuspHeckeT p N f) = ⇑(heckeT p N f) := rfl

/-- The term of the trace at the coset of `γ` is `f ∣[k] (α γ⁻¹)`. -/
lemma quotientFunc_cosetMk [ModularFormClass F Γ₀ k] (f : F) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    SlashInvariantForm.quotientFunc (ModularForm.translate f (heckeMat p)) (cosetMk p N γ hγ) =
      ⇑f ∣[k] (heckeMat p * mapGL ℝ γ⁻¹) := by
  rw [cosetMk]
  change (⇑f ∣[k] heckeMat p) ∣[k] (mapGL ℝ γ)⁻¹ = _
  rw [← SlashAction.slash_mul, map_inv]

omit [Fact p.Prime] in
/-- The determinant of an upper triangular matrix `[[a, b], [0, d]]` is `a d`. -/
lemma det_upper {g : GL (Fin 2) ℝ} {a b d : ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d]) : g.det.val = a * d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_fin_two_of]; ring

omit [Fact p.Prime] in
/-- The slash action of an upper triangular matrix `[[a, b], [0, d]]` with `a, d > 0`. -/
lemma slash_upper_apply {g : GL (Fin 2) ℝ} {a b d : ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d]) (ha : 0 < a) (hd : 0 < d)
    (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ = f (g • τ) * ((a * d : ℝ) : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) := by
  have hdet := det_upper hg
  rw [slash_def]
  simp [σ, hdet, mul_pos ha hd, abs_of_pos (mul_pos ha hd), denom, hg]

omit [Fact p.Prime] in
/-- The action of an upper triangular matrix `[[a, b], [0, d]]` with `a, d > 0` on `ℍ` is `τ ↦ (a τ + b) / d`. -/
lemma coe_smul_upper {g : GL (Fin 2) ℝ} {a b d : ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d]) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) = (a * τ + b) / d := by
  rw [coe_smul_of_det_pos (by rw [det_upper hg]; positivity)]
  simp [num, denom, hg]

/-- The matrix `[[1, j], [0, p]] = diag(1, p) Tʲ` in `GL(2, ℝ)`. -/
noncomputable def upperMat (j : ℕ) : GL (Fin 2) ℝ := heckeMat p * mapGL ℝ (ModularGroup.T ^ (j : ℤ))

/-- The matrix of `upperMat p j` is `[[1, j], [0, p]]`. -/
lemma upperMat_coe (j : ℕ) :
    (upperMat p j : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (j : ℝ); 0, (p : ℝ)] := by
  ext i j
  simp only [upperMat, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply,
    heckeMat_coe, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp

/-- The matrix `diag(p, 1)` in `GL(2, ℝ)`. -/
noncomputable def lowerMat : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℝ), 0; 0, 1]
    (by simp [Matrix.det_fin_two_of, (Fact.out : p.Prime).ne_zero])

/-- The matrix of `lowerMat p` is `diag(p, 1)`. -/
lemma lowerMat_coe : (lowerMat p : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := rfl

/-- The matrix `[[1, j], [0, p]]` acts on `ℍ` by `τ ↦ (τ + j) / p`. -/
lemma coe_upperMat_smul (j : ℕ) (τ : ℍ) : ((upperMat p j • τ : ℍ) : ℂ) = (τ + j) / p := by
  rw [coe_smul_upper (upperMat_coe p j) one_pos (by exact_mod_cast (Fact.out : p.Prime).pos)]
  simp

/-- The matrix `diag(p, 1)` acts on `ℍ` by `τ ↦ p τ`. -/
lemma coe_lowerMat_smul (τ : ℍ) : ((lowerMat p • τ : ℍ) : ℂ) = p * τ := by
  rw [coe_smul_upper (lowerMat_coe p) (by exact_mod_cast (Fact.out : p.Prime).pos) one_pos]
  simp

/-- The formula `(f ∣[k] [[1, j], [0, p]])(τ) = p⁻¹ f((τ + j) / p)`. -/
lemma slash_upperMat_apply (f : ℍ → ℂ) (j : ℕ) (τ : ℍ) :
    (f ∣[k] upperMat p j) τ = (p : ℂ)⁻¹ * f (upperMat p j • τ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [slash_upper_apply (upperMat_coe p j) one_pos (by exact_mod_cast (Fact.out : p.Prime).pos)]
  push_cast
  rw [one_mul, zpow_sub₀ hp, zpow_neg, zpow_one]
  field_simp

/-- The formula `(f ∣[k] diag(p, 1))(τ) = p^(k - 1) f(p τ)`. -/
lemma slash_lowerMat_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] lowerMat p) τ = (p : ℂ) ^ (k - 1) * f (lowerMat p • τ) := by
  rw [slash_upper_apply (lowerMat_coe p) (by exact_mod_cast (Fact.out : p.Prime).pos) one_pos]
  push_cast
  simp [mul_comm]

/-- The matrix `γ' = [[1, b], [N, p d]]` of `Γ₀(N)` with `diag(1, p) δ = γ' diag(p, 1)`. -/
noncomputable def gammaRep (hpN : ¬ p ∣ N) : SL(2, ℤ) :=
  ⟨!![1, deltaRep p N hpN 0 1; (N : ℤ), p * deltaRep p N hpN 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination deltaRep_det p N hpN⟩

/-- The matrix `γ'` is in `Γ₀(N)`. -/
lemma gammaRep_mem (hpN : ¬ p ∣ N) : gammaRep p N hpN ∈ Gamma0 N := by
  rw [Gamma0_mem]
  change ((N : ℤ) : ZMod N) = 0
  simp

/-- The identity `diag(1, p) δ = γ' diag(p, 1)`. -/
lemma heckeMat_mul_deltaRep (hpN : ¬ p ∣ N) :
    heckeMat p * mapGL ℝ (deltaRep p N hpN) = mapGL ℝ (gammaRep p N hpN) * lowerMat p := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply, heckeMat_coe,
    lowerMat_coe]
  fin_cases i <;> fin_cases j <;>
    simp [gammaRep, deltaRep_apply_00, deltaRep_apply_10, mul_comm]

/-- The term of the trace at the coset of `T⁻ʲ` is `f ∣[k] [[1, j], [0, p]]`. -/
lemma quotientFunc_tRep [ModularFormClass F Γ₀ k] (f : F) (j : ℕ) :
    SlashInvariantForm.quotientFunc (ModularForm.translate f (heckeMat p))
      (cosetMk p N (tRep j) (tRep_mem N j)) = ⇑f ∣[k] upperMat p j := by
  rw [quotientFunc_cosetMk, tRep, ← zpow_neg, neg_neg, upperMat]

/-- The term of the trace at the coset of `δ⁻¹` is `f ∣[k] diag(p, 1)`. -/
lemma quotientFunc_deltaRep [ModularFormClass F Γ₀ k] (f : F) (hpN : ¬ p ∣ N) :
    SlashInvariantForm.quotientFunc (ModularForm.translate f (heckeMat p))
      (cosetMk p N _ (deltaRep_inv_mem p N hpN)) = ⇑f ∣[k] lowerMat p := by
  have hmem : mapGL ℝ (gammaRep p N hpN) ∈ Γ₀ := ⟨_, gammaRep_mem p N hpN, rfl⟩
  rw [quotientFunc_cosetMk, inv_inv, heckeMat_mul_deltaRep, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ hmem]

/-- For `p ∣ N`: `(U_p f)(τ) = p⁻¹ ∑_{j < p} f((τ + j) / p)`. -/
theorem heckeT_apply_of_dvd [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (hpN : p ∣ N)
    (τ : ℍ) : heckeT p N f τ = ∑ j : Fin p, (p : ℂ)⁻¹ * f (upperMat p j • τ) := by
  let : Fintype (Γ₀ ⧸ (𝒢).subgroupOf Γ₀) := Fintype.ofFinite _
  rw [heckeT, ModularForm.coe_trace, Finset.sum_apply,
    ← Fintype.sum_bijective _ (bijective_cosetMk_tRep p N hpN) _ _ (fun _ => rfl)]
  simp only [quotientFunc_tRep, slash_upperMat_apply]

/-- For `p ∤ N`: `(T_p f)(τ) = p⁻¹ ∑_{j < p} f((τ + j) / p) + p^(k - 1) f(p τ)`. -/
theorem heckeT_apply_of_not_dvd [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (hpN : ¬ p ∣ N)
    (τ : ℍ) : heckeT p N f τ = ∑ j : Fin p, (p : ℂ)⁻¹ * f (upperMat p j • τ) +
      (p : ℂ) ^ (k - 1) * f (lowerMat p • τ) := by
  let : Fintype (Γ₀ ⧸ (𝒢).subgroupOf Γ₀) := Fintype.ofFinite _
  rw [heckeT, ModularForm.coe_trace, Finset.sum_apply,
    ← Fintype.sum_bijective _ (bijective_cosetRep p N hpN) _ _ (fun _ => rfl),
    Fintype.sum_option, add_comm]
  simp only [cosetRep, quotientFunc_tRep, quotientFunc_deltaRep, slash_upperMat_apply,
    slash_lowerMat_apply]

end Operator

section QExpansion

open Complex Function

local notation "𝕢" => Periodic.qParam

/-- The sum of the `n`-th powers of the `p`-th roots of unity. -/
lemma sum_exp_pow (n : ℕ) :
    ∑ j : Fin p, (exp (2 * Real.pi * Complex.I / p) ^ n) ^ (j : ℕ) =
      if p ∣ n then (p : ℂ) else 0 := by
  have hp := (Fact.out : p.Prime)
  have hζ := isPrimitiveRoot_exp p hp.ne_zero
  rw [Fin.sum_univ_eq_sum_range (fun j => (exp (2 * Real.pi * Complex.I / p) ^ n) ^ j) p]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr h]
    simp
  · exact (hζ.pow_of_coprime n ((hp.coprime_iff_not_dvd.mpr h).symm)).geom_sum_eq_zero hp.one_lt

/-- The `n`-th power of `q` at `(τ + j) / p`. -/
lemma qParam_upperMat_pow (τ : ℍ) (j n : ℕ) :
    𝕢 1 (upperMat p j • τ : ℍ) ^ n = exp (2 * Real.pi * Complex.I * τ / p) ^ n *
      (exp (2 * Real.pi * Complex.I / p) ^ n) ^ j := by
  have h : 𝕢 1 (upperMat p j • τ : ℍ) = exp (2 * Real.pi * Complex.I * τ / p) *
      exp (2 * Real.pi * Complex.I / p) ^ j := by
    rw [Periodic.qParam, coe_upperMat_smul, ← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  rw [h, mul_pow, ← pow_mul, ← pow_mul, mul_comm j n]

/-- The `n`-th power of `q` at `p τ` is the `n p`-th power of `q` at `τ`. -/
lemma qParam_lowerMat_pow (τ : ℍ) (n : ℕ) :
    𝕢 1 (lowerMat p • τ : ℍ) ^ n = 𝕢 1 τ ^ (n * p) := by
  have h : 𝕢 1 (lowerMat p • τ : ℍ) = 𝕢 1 τ ^ p := by
    rw [Periodic.qParam, Periodic.qParam, coe_lowerMat_smul, ← exp_nat_mul]
    congr 1
    ring
  rw [h, ← pow_mul, mul_comm]

/-- The `q`-expansion of `τ ↦ p⁻¹ ∑_{j < p} f((τ + j) / p)` is `∑ a_{m p} qᵐ`. -/
lemma hasSum_upper (a : ℕ → ℂ) (f : ℍ → ℂ) (hf : ∀ z : ℍ, HasSum (fun n => a n * 𝕢 1 z ^ n) (f z))
    (τ : ℍ) : HasSum (fun m => a (m * p) * 𝕢 1 τ ^ m)
      (∑ j : Fin p, (p : ℂ)⁻¹ * f (upperMat p j • τ)) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := hasSum_sum (s := Finset.univ)
    (fun (j : Fin p) _ => (hf (upperMat p j • τ)).mul_left ((p : ℂ)⁻¹))
  rw [← hasSum_extend_zero (mul_left_injective₀ hp.ne_zero : Injective (· * p))]
  convert h using 1
  funext n
  simp only [qParam_upperMat_pow]
  have : ∑ j : Fin p, (p : ℂ)⁻¹ * (a n * (exp (2 * Real.pi * Complex.I * τ / p) ^ n *
      (exp (2 * Real.pi * Complex.I / p) ^ n) ^ (j : ℕ))) =
      (p : ℂ)⁻¹ * a n * exp (2 * Real.pi * Complex.I * τ / p) ^ n *
        ∑ j : Fin p, (exp (2 * Real.pi * Complex.I / p) ^ n) ^ (j : ℕ) := by
    rw [Finset.mul_sum]; congr 1; funext j; ring
  rw [this, sum_exp_pow]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    rw [mul_comm p m, (mul_left_injective₀ hp.ne_zero).extend_apply]
    rw [Periodic.qParam, pow_mul, ← exp_nat_mul, ← exp_nat_mul]
    field_simp
    congr 2
    push_cast
    field_simp
    rw [← exp_nat_mul]
    congr 1
    field_simp
  · rw [extend_apply' _ _ _ (fun ⟨m, hm⟩ => hn ⟨m, by rw [← hm, mul_comm]⟩)]
    simp

/-- The `q`-expansion of `τ ↦ f(p τ)` is `∑ a_{m / p} qᵐ`, with `a_{m / p} = 0` for `p ∤ m`. -/
lemma hasSum_lower (a : ℕ → ℂ) (f : ℍ → ℂ) (hf : ∀ z : ℍ, HasSum (fun n => a n * 𝕢 1 z ^ n) (f z))
    (τ : ℍ) : HasSum (fun m => (if p ∣ m then a (m / p) else 0) * 𝕢 1 τ ^ m)
      (f (lowerMat p • τ)) := by
  have hp := (Fact.out : p.Prime)
  have h := hf (lowerMat p • τ)
  simp only [qParam_lowerMat_pow] at h
  rw [← hasSum_extend_zero (mul_left_injective₀ hp.ne_zero : Injective (· * p))] at h
  convert h using 1
  funext m
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := hm
    rw [mul_comm p n, (mul_left_injective₀ hp.ne_zero).extend_apply,
      Nat.mul_div_cancel _ hp.pos]
  · rw [extend_apply' _ _ _ (fun ⟨n, hn⟩ => hm ⟨n, by rw [← hn, mul_comm]⟩)]
    simp

/-- The coefficients `a_{m p} + p^(k - 1) a_{m / p}` of `T_p f`, where the second term is present only for `p ∤ N` and `p ∣ m`. -/
noncomputable def heckeCoeff (k : ℤ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  a (m * p) + if ¬ p ∣ N ∧ p ∣ m then (p : ℂ) ^ (k - 1) * a (m / p) else 0

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

omit [Fact p.Prime] in
/-- The number 1 is a strict period of `Γ₀(N)`. -/
lemma one_mem_strictPeriods : (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-- The `q`-expansion of `T_p f`, as a convergent series. -/
theorem hasSum_heckeT [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (τ : ℍ) :
    HasSum (fun m => heckeCoeff p N k (fun n => (qExpansion 1 f).coeff n) m * 𝕢 1 τ ^ m)
      (heckeT p N f τ) := by
  have hf : ∀ z : ℍ, HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 z ^ n) (f z) :=
    fun z => ModularForm.hasSum_qExpansion f one_pos (one_mem_strictPeriods N) z
  by_cases hpN : p ∣ N
  · rw [heckeT_apply_of_dvd p N f hpN]
    convert hasSum_upper p _ _ hf τ using 2 with m
    simp [heckeCoeff, hpN]
  · rw [heckeT_apply_of_not_dvd p N f hpN]
    convert (hasSum_upper p _ _ hf τ).add ((hasSum_lower p _ _ hf τ).mul_left ((p : ℂ) ^ (k - 1)))
      using 1
    funext m
    simp only [heckeCoeff, hpN, not_false_eq_true, true_and]
    split_ifs <;> ring

/-- **The `q`-expansion of `T_p f`**: `a_m(T_p f) = a_{m p}(f) + p^(k - 1) a_{m / p}(f)`, where the second term is present only for `p ∤ N` and `p ∣ m`. -/
theorem coeff_heckeT [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (m : ℕ) :
    (qExpansion 1 (heckeT p N f)).coeff m = heckeCoeff p N k (fun n => (qExpansion 1 f).coeff n) m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods N)
    (fun τ => by simpa [smul_eq_mul] using hasSum_heckeT p N f τ) m).symm

/-- For `p ∤ N`: `a_m(T_p f) = a_{m p}(f) + p^(k - 1) a_{m / p}(f)`, with `a_{m / p} = 0` for `p ∤ m`. -/
theorem coeff_heckeT_of_not_dvd [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (hpN : ¬ p ∣ N)
    (m : ℕ) : (qExpansion 1 (heckeT p N f)).coeff m = (qExpansion 1 f).coeff (m * p) +
      if p ∣ m then (p : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m / p) else 0 := by
  simp [coeff_heckeT, heckeCoeff, hpN]

/-- For `p ∣ N`: `a_m(U_p f) = a_{m p}(f)`. -/
theorem coeff_heckeT_of_dvd [NeZero N] [ModularFormClass F Γ₀ k] (f : F) (hpN : p ∣ N)
    (m : ℕ) : (qExpansion 1 (heckeT p N f)).coeff m = (qExpansion 1 f).coeff (m * p) := by
  simp [coeff_heckeT, heckeCoeff, hpN]

end QExpansion

section Commute

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

omit [Fact p.Prime] in
/-- The coefficient map of `T_p T_q` in expanded form, for distinct primes `p` and `q`. -/
lemma heckeCoeff_heckeCoeff (q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : ℕ → ℂ) (m : ℕ) :
    heckeCoeff p N k (heckeCoeff q N k a) m = a (m * p * q) +
      (if ¬ q ∣ N ∧ q ∣ m then (q : ℂ) ^ (k - 1) * a (m / q * p) else 0) +
      (if ¬ p ∣ N ∧ p ∣ m then (p : ℂ) ^ (k - 1) * (a (m / p * q) +
        if ¬ q ∣ N ∧ q ∣ m then (q : ℂ) ^ (k - 1) * a (m / p / q) else 0) else 0) := by
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have h1 : ∀ r, q ∣ r * p ↔ q ∣ r := fun r =>
    ⟨fun h => (hq.dvd_mul.mp h).resolve_right hqp, fun h => dvd_mul_of_dvd_left h _⟩
  have h2 : ∀ r, q ∣ r → r * p / q = r / q * p := by
    rintro r ⟨s, rfl⟩
    rw [mul_assoc, Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_cancel_left _ hq.pos]
  have h3 : ∀ r, p ∣ r → (q ∣ r / p ↔ q ∣ r) := by
    rintro r ⟨s, rfl⟩
    rw [Nat.mul_div_cancel_left _ hp.pos, mul_comm, h1]
  simp only [heckeCoeff, h1]
  by_cases hpm : p ∣ m
  · simp only [h3 m hpm]
    by_cases hqm : q ∣ m
    · simp only [hqm, h2 m hqm]
    · simp [hqm]
  · by_cases hqm : q ∣ m
    · simp only [hpm, hqm, h2 m hqm, and_false, ite_false]
    · simp [hpm, hqm]

omit [Fact p.Prime] in
/-- The coefficient maps of `T_p` and `T_q` commute for distinct primes `p` and `q`. -/
lemma heckeCoeff_comm (q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a : ℕ → ℂ) :
    heckeCoeff p N k (heckeCoeff q N k a) = heckeCoeff q N k (heckeCoeff p N k a) := by
  funext m
  rw [heckeCoeff_heckeCoeff p N q hp hq hpq, heckeCoeff_heckeCoeff q N p hq hp hpq.symm,
    mul_right_comm m p q, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm p q]
  split_ifs <;> ring

/-- **Commutation of Hecke operators**: `T_p T_q = T_q T_p` for distinct primes `p` and `q`. -/
theorem heckeT_comm [NeZero N] (q : ℕ) [Fact q.Prime] (hpq : p ≠ q)
    (f : ModularForm Γ₀ k) : heckeT p N (heckeT q N f) = heckeT q N (heckeT p N f) := by
  apply ModularForm.qExpansion_injective one_pos (one_mem_strictPeriods N)
  ext m
  simp only [coeff_heckeT]
  exact congrFun (heckeCoeff_comm p N q Fact.out Fact.out hpq _) m

end Commute

section Eigenform

variable {k : ℤ}

/-- The cusp form `f` is an eigenvector of `T_p` with eigenvalue `c`. -/
def IsHeckeEigenvector [NeZero N] (f : CuspForm Γ₀ k) (c : ℂ) : Prop :=
  ⇑(cuspHeckeT p N f) = c • ⇑f

/-- A Hecke eigenform is a nonzero cusp form that is an eigenvector of `T_ℓ` for each prime `ℓ`. For `ℓ ∣ N` the operator `T_ℓ` is the operator `U_ℓ`. -/
def IsHeckeEigenform [NeZero N] (f : CuspForm Γ₀ k) : Prop :=
  f ≠ 0 ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ c : ℂ, IsHeckeEigenvector ℓ N f c

/-- A normalized Hecke eigenform is a Hecke eigenform with `a_1 = 1`. -/
structure IsNormalizedHeckeEigenform [NeZero N] (f : CuspForm Γ₀ k) : Prop where
  eigen : IsHeckeEigenform N f
  one : qCoeff f 1 = 1

/-- The eigenvalue equation on `q`-expansion coefficients: if `T_p f = c f`, then the coefficients of `f` satisfy `heckeCoeff p N k a m = c a_m` for each `m`. -/
theorem heckeCoeff_qCoeff_of_eigenvector [NeZero N] {f : CuspForm Γ₀ k} {c : ℂ}
    (hc : IsHeckeEigenvector p N f c) (m : ℕ) :
    heckeCoeff p N k (qCoeff f) m = c * qCoeff f m := by
  have h1 := coeff_heckeT p N f m
  rw [← coe_cuspHeckeT, show ⇑(cuspHeckeT p N f) = c • ⇑f from hc,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f] at h1
  exact h1.symm.trans (by simp [qCoeff])

/-- The eigenvalue of `T_p` on an eigenvector with `a_1 = 1` is `a_p`. -/
theorem eigenvalue_eq_qCoeff [NeZero N] {f : CuspForm Γ₀ k} {c : ℂ}
    (hc : IsHeckeEigenvector p N f c) (h1 : qCoeff f 1 = 1) : c = qCoeff f p := by
  have h := heckeCoeff_qCoeff_of_eigenvector p N hc 1
  have hp1 : ¬ p ∣ 1 := (Fact.out : p.Prime).not_dvd_one
  simpa [heckeCoeff, hp1, h1] using h.symm

/-- For `p ∤ N`, an eigenvector of `T_p` with `a_1 = 1` satisfies the recursion `a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}` of the Euler factor at `p`. -/
theorem qCoeff_pow_succ_succ_of_not_dvd [NeZero N] {f : CuspForm Γ₀ k} {c : ℂ}
    (hc : IsHeckeEigenvector p N f c) (h1 : qCoeff f 1 = 1) (hpN : ¬ p ∣ N) (r : ℕ) :
    qCoeff f (p ^ (r + 2)) =
      qCoeff f p * qCoeff f (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * qCoeff f (p ^ r) := by
  have hp := (Fact.out : p.Prime)
  have h := heckeCoeff_qCoeff_of_eigenvector p N hc (p ^ (r + 1))
  rw [← eigenvalue_eq_qCoeff p N hc h1, ← h]
  have hdvd : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  have hdiv : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  simp only [heckeCoeff, hpN, hdvd, not_false_eq_true, and_self, ite_true, hdiv, ← pow_succ]
  ring

/-- For `p ∣ N`, an eigenvector of `U_p` with `a_1 = 1` satisfies `a_{p^(r+1)} = a_p a_{p^r}`. -/
theorem qCoeff_pow_succ_of_dvd [NeZero N] {f : CuspForm Γ₀ k} {c : ℂ}
    (hc : IsHeckeEigenvector p N f c) (h1 : qCoeff f 1 = 1) (hpN : p ∣ N) (r : ℕ) :
    qCoeff f (p ^ (r + 1)) = qCoeff f p * qCoeff f (p ^ r) := by
  have h := heckeCoeff_qCoeff_of_eigenvector p N hc (p ^ r)
  rw [← eigenvalue_eq_qCoeff p N hc h1, ← h]
  simp [heckeCoeff, hpN, pow_succ]

/-- A normalized Hecke eigenform satisfies the `good` field of `Langlands.IsNormalizedEigenform`. -/
theorem IsNormalizedHeckeEigenform.good [NeZero N] {f : CuspForm Γ₀ k}
    (hf : IsNormalizedHeckeEigenform N f) (ℓ r : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    qCoeff f (ℓ ^ (r + 2)) =
      qCoeff f ℓ * qCoeff f (ℓ ^ (r + 1)) - (ℓ : ℂ) ^ (k - 1) * qCoeff f (ℓ ^ r) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨c, hc⟩ := hf.eigen.2 ℓ
  exact qCoeff_pow_succ_succ_of_not_dvd ℓ N hc hf.one hℓN r

/-- A normalized Hecke eigenform satisfies the `bad` field of `Langlands.IsNormalizedEigenform`. -/
theorem IsNormalizedHeckeEigenform.bad [NeZero N] {f : CuspForm Γ₀ k}
    (hf : IsNormalizedHeckeEigenform N f) (ℓ r : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    qCoeff f (ℓ ^ (r + 1)) = qCoeff f ℓ * qCoeff f (ℓ ^ r) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨c, hc⟩ := hf.eigen.2 ℓ
  exact qCoeff_pow_succ_of_dvd ℓ N hc hf.one hℓN r

end Eigenform

end Langlands.Modular
