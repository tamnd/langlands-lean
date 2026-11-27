/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import Langlands.Statements.Modularity

/-!
# The Sturm bound

Let $\Gamma \subseteq \mathrm{GL}_2(\mathbb{R})$ be an arithmetic subgroup that contains the translation $\tau \mapsto \tau + 1$, and let $f$ be a modular form of weight $k$ for $\Gamma$ with $q$-expansion $f = \sum_n a_n(f) q^n$, $q = e^{2 \pi i \tau}$. This file proves the Sturm bound: if $a_n(f) = 0$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$, then $f = 0$. The main case is $\Gamma = \Gamma_0(N)$. A corollary is that two modular forms of weight $k$ for $\Gamma_0(N)$ are equal if their coefficients agree for $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] / 12$.

## Main results

* `Langlands.Modular.eq_zero_of_coeff_eq_zero_levelOne`: a modular form $f$ of weight $k$ for $\mathrm{SL}_2(\mathbb{Z})$ with $a_n(f) = 0$ for all $n \le k / 12$ is zero.
* `Langlands.Modular.eq_zero_of_coeff_eq_zero`: a modular form $f$ of weight $k$ for an arithmetic group $\Gamma$ with period $1$ and $a_n(f) = 0$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$ is zero.
* `Langlands.Modular.eq_zero_of_coeff_eq_zero_Gamma0`: the case $\Gamma = \Gamma_0(N)$.
* `Langlands.Modular.eq_of_coeff_eq_Gamma0`: two modular forms of weight $k$ for $\Gamma_0(N)$ are equal if $a_n(f) = a_n(g)$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] / 12$.
* `Langlands.Modular.eq_of_qCoeff_eq_Gamma0`: the same statement for cusp forms, with `Langlands.qCoeff`.

## Proof

The level one case is `ModularForm.sturm_bound_levelOne` of Mathlib, which divides by a power of the discriminant. This file changes the hypothesis on the order of the $q$-expansion into a hypothesis on the coefficients. For the general case let $m$ be the least integer with $m > k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$. If $a_n(f) = 0$ for all $n < m$, then the Taylor formula for the cusp function gives $f(\tau) = O(|q|^m)$ as $\mathrm{Im}\, \tau \to \infty$ (`isBigO_qParam_pow_of_coeff_eq_zero`). The norm $\mathrm{N}(f) = \prod_{\gamma} f \mid_k \gamma^{-1}$ over the cosets $\gamma$ of $\Gamma$ in $\mathrm{SL}_2(\mathbb{Z})$ is `ModularForm.norm` of Mathlib. It is a modular form of level one and weight $k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]$. The factor of the trivial coset is $f$. Each other factor is $f \mid_k g$ with $g \in \mathrm{SL}_2(\mathbb{Z})$, and it is bounded at infinity because $g \infty$ is a cusp of $\Gamma$ (`isBoundedAtImInfty_slash`). Thus $\mathrm{N}(f)(\tau) = O(|q|^m)$ (`isBigO_norm`). The integral formula $a_n = \int_0^1 q^{-n} F(u + it) \, du$ for the coefficients of a form $F$ with $F = O(|q|^m)$ gives $|a_n(F)| \le C e^{-2 \pi (m - n) t}$ for all large $t$, so $a_n(F) = 0$ for $n < m$ (`coeff_eq_zero_of_isBigO`). The level one case then gives $\mathrm{N}(f) = 0$, and `ModularForm.norm_eq_zero_iff` gives $f = 0$.

## Implementation notes

The bound is stated as $(n : \mathbb{Z}) \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$ with the integer division. For an integer $n$ this is the same as $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$ in $\mathbb{Q}$. For $k < 0$ the hypothesis is empty, and the form is zero by `ModularForm.isZero_of_neg_weight`. The index is the index in $\mathrm{SL}_2(\mathbb{Z})$, not in $\mathrm{PSL}_2(\mathbb{Z})$. The $q$-expansion is the expansion at $\infty$ with width $1$, that is `UpperHalfPlane.qExpansion 1`.

## References

* J. Sturm, On the congruence of modular forms, in Number theory (New York, 1984-1985), Lecture Notes in Math. 1240 (1987).
* W. Stein, Modular forms, a computational approach, chapter 9, theorem 9.18.
-/

namespace Langlands.Modular

open UpperHalfPlane ModularForm Filter Asymptotics Complex CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology Real

local notation "𝕢" => Function.Periodic.qParam

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]

/-- If the coefficients $a_n(f)$ vanish for $n < m$, then $f(\tau) = O(|q|^m)$ as $\mathrm{Im}\, \tau \to \infty$. -/
lemma isBigO_qParam_pow_of_coeff_eq_zero (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) {k : ℤ}
    (f : ModularForm 𝒢 k) {m : ℕ} (hm : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ ‖𝕢 1 (τ : ℂ)‖ ^ m := by
  have ha : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (Γ := 𝒢) (k := k) f one_pos h1
  have hs : ∀ τ : ℍ, HasSum (fun n ↦ (qExpansion 1 f).coeff n • 𝕢 1 (τ : ℂ) ^ n) (f τ) :=
    fun τ ↦ ModularForm.hasSum_qExpansion (Γ := 𝒢) (k := k) (f := f) one_pos h1 τ
  have hP : HasFPowerSeriesOnBall (cuspFunction 1 (f : ℍ → ℂ))
      (qExpansionFormalMultilinearSeries 1 f) 0 1 :=
    hasFPowerSeries_cuspFunction f one_pos ha hs
  have hO := hP.hasFPowerSeriesAt.isBigO_sub_partialSum_pow m
  have hps : (qExpansionFormalMultilinearSeries 1 f).partialSum m = fun _ ↦ 0 := by
    ext y
    simp only [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      qExpansionFormalMultilinearSeries_coeff]
    exact Finset.sum_eq_zero fun n hn ↦ by simp [hm n (Finset.mem_range.mp hn)]
  simp only [hps, zero_add, sub_zero] at hO
  have := hO.comp_tendsto (qParam_tendsto_atImInfty one_pos)
  refine this.congr_left fun τ ↦ ?_
  exact eq_cuspFunction τ one_ne_zero (SlashInvariantFormClass.periodic_comp_ofComplex f h1)

omit [𝒢.IsArithmetic] in
/-- If $f(\tau) = O(|q|^m)$ as $\mathrm{Im}\, \tau \to \infty$, then $a_n(f) = 0$ for $n < m$. -/
lemma coeff_eq_zero_of_isBigO (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) {k : ℤ}
    (f : ModularForm 𝒢 k) {m : ℕ} (hf : (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ ‖𝕢 1 (τ : ℂ)‖ ^ m)
    {n : ℕ} (hn : n < m) : (qExpansion 1 f).coeff n = 0 := by
  obtain ⟨C, hC, hCf⟩ := hf.exists_pos
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hCf.bound
  have key : ∀ t : ℝ, max A 1 ≤ t → ‖(qExpansion 1 f).coeff n‖ ≤ C * Real.exp (-2 * π * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos h1 n ht0]
    have hq : ∀ u : ℝ, ‖𝕢 1 ((u : ℂ) + t * Complex.I)‖ = Real.exp (-2 * π * t) := by
      intro u; rw [Function.Periodic.norm_qParam]; simp
    have hbd : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
        ‖1 / 𝕢 1 ((u : ℂ) + t * Complex.I) ^ n * f ⟨(u : ℂ) + t * Complex.I, by simpa using ht0⟩‖ ≤
          C * Real.exp (-2 * π * t) := by
      intro u _
      have hτ := hA ⟨(u : ℂ) + t * Complex.I, by simpa using ht0⟩
        (by simpa using (le_max_left _ _).trans ht)
      simp only [Set.mem_ofPred_eq, norm_pow, norm_norm] at hτ
      rw [hq] at hτ
      have hq0 : 0 < Real.exp (-2 * π * t) := Real.exp_pos _
      have hq1 : Real.exp (-2 * π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      rw [norm_mul, norm_div, norm_one, norm_pow, hq, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ (pow_pos hq0 n)]
      refine hτ.trans ?_
      set e := Real.exp (-2 * π * t)
      rw [show C * e * e ^ n = C * e ^ (n + 1) by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0.le hq1.le hn) hC.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    simpa using this
  have hlim : Tendsto (fun t : ℝ ↦ C * Real.exp (-2 * π * t)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] : -2 * π < 0)))
    simpa using this.const_mul C
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim (eventually_atTop.mpr ⟨max A 1, key⟩))

/-- For $g$ in the image of $\mathrm{SL}_2(\mathbb{Z})$, the function $f \mid_k g$ is bounded at infinity. -/
lemma isBoundedAtImInfty_slash {k : ℤ} (f : ModularForm 𝒢 k) {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒮ℒ) :
    IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] g) := by
  have hc : IsCusp (g • OnePoint.infty) 𝒢 := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact IsCusp.smul_of_mem Fact.out hg
  exact f.bdd_at_cusps' hc g rfl

/-- If $f(\tau) = O(|q|^m)$, then the norm of $f$ to level one is also $O(|q|^m)$. -/
lemma isBigO_norm {k : ℤ} (f : ModularForm 𝒢 k) {m : ℕ}
    (hf : (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ ‖𝕢 1 (τ : ℂ)‖ ^ m) :
    (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] fun τ ↦ ‖𝕢 1 (τ : ℂ)‖ ^ m := by
  classical
  let : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let q₀ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ := QuotientGroup.mk 1
  have h0 : SlashInvariantForm.quotientFunc f q₀ = f := by
    simp [q₀]
  have hb : ∀ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q =O[atImInfty]
      fun _ ↦ (1 : ℝ) := by
    intro q _
    induction q using QuotientGroup.induction_on with
    | H h => exact isBoundedAtImInfty_slash f (inv_mem h.2)
  have hP := hf.mul (IsBigO.finsetProd hb)
  simp only [Finset.prod_const_one, mul_one] at hP
  refine hP.congr_left fun τ ↦ ?_
  rw [ModularForm.coe_norm, Finset.prod_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀),
    h0]

/-- **The Sturm bound in level one.** A modular form $f$ of weight $k$ for $\mathrm{SL}_2(\mathbb{Z})$ with $a_n(f) = 0$ for all $n \le k / 12$ is zero. -/
theorem eq_zero_of_coeff_eq_zero_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (hf : ∀ n : ℕ, (n : ℤ) ≤ k / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact ModularForm.isZero_of_neg_weight hk f
  refine ModularForm.sturm_bound_levelOne ?_
  refine lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self _))
    (PowerSeries.nat_le_order _ _ ?_)
  intro n hn
  refine hf n ?_
  have : (k.toNat / 12 : ℕ) = ((k / 12).toNat : ℕ) := by omega
  omega

/-- **The Sturm bound.** Let $\Gamma$ be an arithmetic subgroup with period $1$. A modular form $f$ of weight $k$ for $\Gamma$ with $a_n(f) = 0$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma] / 12$ is zero. -/
theorem eq_zero_of_coeff_eq_zero (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) {k : ℤ} (f : ModularForm 𝒢 k)
    (hf : ∀ n : ℕ, (n : ℤ) ≤ k * 𝒢.relIndex 𝒮ℒ / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact ModularForm.isZero_of_neg_weight hk f
  set m := (k * 𝒢.relIndex 𝒮ℒ / 12).toNat + 1
  have hm : ∀ n < m, (qExpansion 1 f).coeff n = 0 := fun n hn ↦ hf n (by
    have : 0 ≤ k * 𝒢.relIndex 𝒮ℒ / 12 := Int.ediv_nonneg (by positivity) (by norm_num)
    omega)
  have hN := isBigO_norm f (isBigO_qParam_pow_of_coeff_eq_zero h1 f hm)
  have hN0 := eq_zero_of_coeff_eq_zero_levelOne (ModularForm.norm 𝒮ℒ f) fun n hn ↦
    coeff_eq_zero_of_isBigO one_mem_strictPeriods_SL _ hN (by
      have : 0 ≤ k * 𝒢.relIndex 𝒮ℒ / 12 := Int.ediv_nonneg (by positivity) (by norm_num)
      change (n : ℤ) ≤ k * (𝒢.relIndex 𝒮ℒ : ℕ) / 12 at hn
      omega)
  have := (ModularForm.norm_eq_zero_iff 𝒮ℒ (f := f)).mp hN0
  exact DFunLike.coe_injective this

/-- The index of the image of a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ in the image of $\mathrm{SL}_2(\mathbb{Z})$ is the index of $\Gamma$. -/
lemma relIndex_SL (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.relIndex_map_map_of_injective Γ ⊤
    Matrix.SpecialLinearGroup.mapGL_injective).trans (Subgroup.relIndex_top_right Γ)

/-- The translation $\tau \mapsto \tau + 1$ is in $\Gamma_0(N)$. -/
lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-- **The Sturm bound for $\Gamma_0(N)$.** A modular form $f$ of weight $k$ for $\Gamma_0(N)$ with $a_n(f) = 0$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] / 12$ is zero. -/
theorem eq_zero_of_coeff_eq_zero_Gamma0 {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, (n : ℤ) ≤ k * (Gamma0 N).index / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 :=
  eq_zero_of_coeff_eq_zero (one_mem_strictPeriods_Gamma0 N) f (by rwa [relIndex_SL])

/-- Two modular forms of weight $k$ for $\Gamma_0(N)$ are equal if $a_n(f) = a_n(g)$ for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] / 12$. -/
theorem eq_of_coeff_eq_Gamma0 {N : ℕ} [NeZero N] {k : ℤ}
    (f g : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hfg : ∀ n : ℕ, (n : ℤ) ≤ k * (Gamma0 N).index / 12 →
      (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_eq_zero_Gamma0 (f - g) fun n hn ↦ ?_
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma0 N) f g,
    map_sub, hfg n hn, sub_self]

/-- Two cusp forms of weight $k$ for $\Gamma_0(N)$ are equal if `qCoeff f n = qCoeff g n` for all $n \le k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] / 12$. -/
theorem eq_of_qCoeff_eq_Gamma0 {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hfg : ∀ n : ℕ, (n : ℤ) ≤ k * (Gamma0 N).index / 12 → qCoeff f n = qCoeff g n) : f = g := by
  let F : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k := ModularFormClass.modularForm f
  let G : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k := ModularFormClass.modularForm g
  have hF : (F : ℍ → ℂ) = f := rfl
  have hG : (G : ℍ → ℂ) = g := rfl
  have h := eq_of_coeff_eq_Gamma0 F G fun n hn ↦ by
    rw [hF, hG]
    exact hfg n hn
  ext τ
  rw [← congrFun hF τ, ← congrFun hG τ, h]

end Langlands.Modular
