/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMixedSignTheta
import Langlands.Tate.HeckeDualSum

/-!
# The functional equation of the partial Hecke sums with mixed signs

This file repeats the unfolding of `Langlands/Tate/HeckeUnfold.lean`, the functional equation pair of `Langlands/Tate/HeckeFEPair.lean` and the completed partial Hecke sums of `Langlands/Tate/HeckeDualSum.lean` for the weight with a sign $\varepsilon_w$ at each complex place, from `Langlands/Tate/HeckeMixedSignTheta.lean`. The proofs are the same. The lemmas that do not depend on the weight, such as the constants $C_{p, k}$, the unit cube lemmas and the root constant $\varepsilon_{\mathfrak{a}}$, are not repeated.

Let $p_v \le 1$, $(p, k) \neq 0$, and let $\chi^{\varepsilon, p, k}_\infty$ be trivial on all units. The completed partial Hecke sum $\Lambda_{\mathfrak{a}}$ of the signed weight is entire. For $\mathrm{Re}\, s > n / 2$ it is the series of $w_K \, \Gamma_{p, k}(2 s / n) \, \chi^{\varepsilon, p, k}_\infty(\alpha) \, |N(\alpha)|^{-2 s / n}$ over $\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. It satisfies $$\Lambda_{\mathfrak{a}}(n / 2 - s) = \varepsilon_{\mathfrak{a}} \, \lambda^{-s} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}.$$

## Main definitions

* `Langlands.Tate.signHeckeCubeTheta`, `Langlands.Tate.signHeckeCubeDualTheta`: the cube averages $F_{\mathfrak{a}}$ and $G_{\mathfrak{a}}$ of the signed theta series.
* `Langlands.Tate.signHeckeFEPair`: the functional equation pair of $F_{\mathfrak{a}}$ and $G_{\mathfrak{a}}$.
* `Langlands.Tate.signCompletedPartialHecke`: the completed partial Hecke sum $\Lambda_{\mathfrak{a}}$ of the signed weight.

## Main results

* `Langlands.Tate.hasSum_integral_signHeckeTheta`: the unfolding of the Mellin integral into the partial Hecke series.
* `Langlands.Tate.isStrongFEPair_signHeckeFEPair`: the pair has the constant terms zero.
* `Langlands.Tate.differentiable_signCompletedPartialHecke`: $\Lambda_{\mathfrak{a}}$ is entire.
* `Langlands.Tate.hasSum_signCompletedPartialHecke`: $\Lambda_{\mathfrak{a}}$ as a series for $\mathrm{Re}\, s > n / 2$.
* `Langlands.Tate.signCompletedPartialHecke_sub`: the functional equation of $\Lambda_{\mathfrak{a}}$.
-/

open MeasureTheory Module Filter Topology Set Complex Asymptotics ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical nonZeroDivisors ENNReal

namespace Langlands.Tate

section Zero

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- **The weight at $0$.** If $(p, k) \neq 0$, then $G_t^{p, k}(0) = 0$. -/
theorem signMixedGaussWeight_zero (h : p ≠ 0 ∨ k ≠ 0) (t : InfinitePlace K → ℝ) :
    signMixedGaussWeight ε p k t 0 = 0 := by
  simp only [signMixedGaussWeight, map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  rcases h with h | h
  · obtain ⟨v, hv⟩ := Function.ne_iff.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simpa [realGaussWeight] using hv), zero_mul]
  · obtain ⟨w, hw⟩ := Function.ne_iff.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simpa [gaussWeight, flipConj] using hw), mul_zero]

/-- **The term $\alpha = 0$.** If $(p, k) \neq 0$, then $h_t(0) = 0$. -/
theorem signHeckeTerm_zero (h : p ≠ 0 ∨ k ≠ 0) (t : InfinitePlace K → ℝ) :
    signHeckeTerm ε p k (0 : K) t = 0 := by
  rw [signHeckeTerm, map_zero, signMixedGaussWeight_zero h, mul_zero]

end Zero

section Bound

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

variable {ε p k}

omit [NumberField K] in
/-- The norm of the factor at one place: for $t \ge 0$, $|t^{q_w / 2} g_w(t, \alpha)| \le (1 + q_w!) e^{-\pi t |\alpha|_w^2 / 2}$. -/
theorem norm_signPlaceTerm_le {t : ℝ} (ht : 0 ≤ t) (α : K) (w : InfinitePlace K) :
    ‖signPlaceTerm ε p k t α w‖ ≤
      (1 + ((weightExp p k w).factorial : ℝ)) * Real.exp (-(π * (t * w α ^ 2)) / 2) := by
  have hst : √t ^ 2 = t := Real.sq_sqrt ht
  have hc : ‖(t : ℂ) ^ ((weightExp p k w : ℂ) / 2)‖ = √t ^ weightExp p k w := by
    rw [show ((weightExp p k w : ℂ) / 2) = (((weightExp p k w : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht]
    congr 1
    ring
  have key : ‖signPlaceTerm ε p k t α w‖ = (√t * w α) ^ weightExp p k w *
      Real.exp (-(π * (√t * w α) ^ 2)) := by
    rw [signPlaceTerm, norm_mul, hc, mul_pow, mul_pow, hst, mul_assoc]
    congr 1
    by_cases h : IsReal w
    · have hq : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
      simp only [signPlaceGauss, h, ↓reduceDIte, realGaussWeight, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp]
      rw [hq, ← Real.norm_eq_abs, norm_embedding_of_isReal]
      congr 2
      rw [← norm_embedding_of_isReal h α, Real.norm_eq_abs, sq_abs]
      ring
    · have hq : weightExp p k w = k ⟨w, not_isReal_iff_isComplex.1 h⟩ := by simp [weightExp, h]
      simp only [signPlaceGauss, h, ↓reduceDIte, gaussWeight, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp, RCLike.norm_conj, norm_signEmbedding]
      rw [hq]
      congr 2
      ring
  rw [key, show -(π * (t * w α ^ 2)) / 2 = -(π * (√t * w α) ^ 2) / 2 by rw [mul_pow, hst]]
  exact pow_mul_exp_le_factorial (by positivity) _

/-- **The bound of the normalized terms.** For $t_w \ge 0$, $$|h_t(\alpha)| \le C_{p, k} \, e^{-\pi \sum_w n_w (t_w / 4) |\alpha|_w^2}.$$ The right side is $C_{p, k}$ times the term of $\alpha$ in the theta function $\theta_{\mathfrak{a}}(t / 4)$ of weight $0$. -/
theorem norm_signHeckeTerm_le {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) (α : K) :
    ‖signHeckeTerm ε p k α t‖ ≤ heckeConst p k * thetaTerm α (fun w => t w / 4) := by
  rw [signHeckeTerm_eq_prod, norm_prod]
  calc ∏ w, ‖signPlaceTerm ε p k (t w) α w‖
      ≤ ∏ w, (1 + ((weightExp p k w).factorial : ℝ)) * Real.exp (-(π * (t w * w α ^ 2)) / 2) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun w _ => norm_signPlaceTerm_le (ht w) α w)
    _ = heckeConst p k * Real.exp (∑ w, -(π * (t w * w α ^ 2)) / 2) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum, heckeConst]
    _ ≤ heckeConst p k * thetaTerm α (fun w => t w / 4) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) heckeConst_pos.le
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun w _ => ?_
        have h1 := mult_le_two w
        have h2 : 0 ≤ t w * w α ^ 2 := mul_nonneg (ht w) (sq_nonneg _)
        have h3 := mul_nonneg (mul_nonneg Real.pi_pos.le h2) (sub_nonneg.2 h1)
        simp only
        nlinarith

end Bound

section Convergence

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {s : ℂ}

variable (ε p k a) in
/-- For $t_w > 0$, the family of the normalized terms $h_t(\alpha)$, $\alpha \in \mathfrak{a}$, is summable. -/
theorem summable_signHeckeTerm {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => signHeckeTerm ε p k (α : K) t :=
  Summable.of_norm_bounded (((summable_dedekindTheta a (t := fun w => t w / 4)
    fun w => by have := ht w; positivity)).mul_left (heckeConst p k))
    fun α => norm_signHeckeTerm_le (fun w => (ht w).le) (α : K)

/-- For $y > 0$, the sum over $\alpha \in \mathfrak{a} \setminus 0$ of the integrals of $|h_{t(y, c)}(\alpha)|$ over $c \in [0, 1)^r$ is at most $C_{p, k} (\Theta_{\mathfrak{a}}(y / 4) - 1)$, where $\Theta_{\mathfrak{a}}$ is the unit theta function of weight $0$. -/
theorem tsum_lintegral_signHeckeTerm_le {y : ℝ} (hy : 0 < y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ ≤
      ENNReal.ofReal (heckeConst p k) * ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1) := by
  have hy' : 0 < 4⁻¹ * y := by positivity
  have hint : IntegrableOn (fun c => dedekindTheta K a (unitScale K (4⁻¹ * y) c) - 1)
      (Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) :=
    (integrableOn_dedekindTheta_unitScale a hy').sub (integrableOn_const volume_unitCube_ne_top)
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ
      ≤ ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ENNReal.ofReal (heckeConst p k) *
            ENNReal.ofReal (thetaTerm (α : K) (unitScale K (4⁻¹ * y) c)) := by
        refine ENNReal.tsum_le_tsum fun α => lintegral_mono fun c => ?_
        rw [← ENNReal.ofReal_mul heckeConst_pos.le, ← ofReal_norm, ← unitScale_div_four]
        exact ENNReal.ofReal_le_ofReal
          (norm_signHeckeTerm_le (fun w => (unitScale_pos hy c w).le) (α : K))
    _ = ENNReal.ofReal (heckeConst p k) * ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ∑' α : NonzeroElt a, ENNReal.ofReal (thetaTerm (α : K) (unitScale K (4⁻¹ * y) c)) := by
        rw [lintegral_tsum fun α => (measurable_ofReal_thetaTerm _ _).aemeasurable,
          ← ENNReal.tsum_mul_left]
        exact tsum_congr fun α => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (heckeConst p k) * ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1) := by
        congr 1
        rw [← integral_unitCube_sub_one hy', ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun c => sub_nonneg.2 (one_le_dedekindTheta a (unitScale_pos hy' c)))]
        exact lintegral_congr fun c => (ofReal_dedekindTheta_sub_one (unitScale_pos hy' c)).symm

/-- The factor $|y^{s - 1}|$ comes out of the sum and the integrals. -/
theorem tsum_lintegral_enorm_mul_signHeckeTerm (y : ℝ) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖(y : ℂ) ^ (s - 1) * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ =
      ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun α => ?_
  simp_rw [enorm_mul]
  exact lintegral_const_mul' _ _ enorm_ne_top

variable (ε p k a) in
/-- The bound of `lintegral_tsum_signHeckeTerm_lt_top`, with the factor $|y^{s - 1}|$ outside the sum. -/
theorem lintegral_enorm_mul_tsum_signHeckeTerm_lt_top {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a,
      ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ <
        ⊤ := by
  have hM := ((MellinConvergent.comp_mul_left (by norm_num : (0 : ℝ) < 4⁻¹)).2
    ((unitThetaFEPair a).hasMellin (s := s) hs).1).hasFiniteIntegral
  refine lt_of_le_of_lt (setLIntegral_mono' (g := fun y : ℝ => ENNReal.ofReal (heckeConst p k) *
    ‖(y : ℂ) ^ (s - 1) • ((unitThetaFEPair a).f (4⁻¹ * y) - (unitThetaFEPair a).f₀)‖ₑ)
    measurableSet_Ioi fun y hy => ?_) ?_
  swap
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM
  have hy' : (0 : ℝ) < y := hy
  have hX : 0 ≤ unitTheta K a (4⁻¹ * y) - 1 :=
    sub_nonneg.2 (one_le_unitTheta a (by positivity)).1
  have e : ‖(y : ℂ) ^ (s - 1) • ((unitThetaFEPair a).f (4⁻¹ * y) - (unitThetaFEPair a).f₀)‖ₑ =
      ‖(y : ℂ) ^ (s - 1)‖ₑ * ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1) := by
    change ‖(y : ℂ) ^ (s - 1) • ((unitTheta K a (4⁻¹ * y) : ℂ) - 1)‖ₑ = _
    rw [enorm_smul]
    congr 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg hX]
  rw [e]
  calc ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ
      ≤ ‖(y : ℂ) ^ (s - 1)‖ₑ * (ENNReal.ofReal (heckeConst p k) *
          ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1)) := by
        gcongr
        exact tsum_lintegral_signHeckeTerm_le hy'
    _ = _ := by ring

variable (ε p k a) in
/-- **The absolute convergence.** For $\mathrm{Re}\, s > n / 2$, $$\int_0^\infty \sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |y^{s - 1} h_{t(y, c)}(\alpha)| \, dc \, dy < \infty.$$ The cube $[0, 1)^r$ is a fundamental domain of the unit lattice $\mathbb{Z}^r$ in the unit coordinates. -/
theorem lintegral_tsum_signHeckeTerm_lt_top {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖(y : ℂ) ^ (s - 1) * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ < ⊤ := by
  simp_rw [tsum_lintegral_enorm_mul_signHeckeTerm]
  exact lintegral_enorm_mul_tsum_signHeckeTerm_lt_top ε p k a hs

end Convergence

section Measurable

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- The factor of the normalized term at one place is measurable in $t$. -/
theorem measurable_signPlaceTerm (α : K) (w : InfinitePlace K) :
    Measurable fun t : ℝ => signPlaceTerm ε p k t α w := by
  refine (Complex.measurable_ofReal.pow_const _).mul (Continuous.measurable ?_)
  unfold signPlaceGauss realGaussWeight gaussWeight
  split_ifs <;> fun_prop

/-- The normalized term $h_t(\alpha)$ is measurable in $t$. -/
theorem measurable_signHeckeTerm (α : K) : Measurable fun t => signHeckeTerm ε p k α t := by
  simp_rw [signHeckeTerm_eq_prod]
  exact Finset.measurable_prod _ fun w _ => (measurable_signPlaceTerm α w).comp (measurable_pi_apply w)

/-- The normalized term $h_{t(y, c)}(\alpha)$ is measurable in $(y, c)$. -/
theorem measurable_signHeckeTerm_unitScale (α : K) :
    Measurable fun q : ℝ × (Fin (rank K) → ℝ) => signHeckeTerm ε p k α (unitScale K q.1 q.2) := by
  refine (measurable_signHeckeTerm α).comp (Continuous.measurable (continuous_pi fun w => ?_))
  unfold unitScale
  fun_prop

end Measurable

section Unfold

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The periodicity under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$. -/
theorem signHeckeTerm_unitsEquiv (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ) :
    signHeckeTerm ε p k ((unitsEquiv K q : K) * α) (unitScale K y c) =
      signHeckeTerm ε p k α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [signHeckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _) α, hχ, one_mul]
  congr 1
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- **The unfolding of the absolute values.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |h_{t(y, c)}(\alpha_I)| \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem tsum_lintegral_unitCube_signHeckeTerm (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ‖signHeckeTerm ε p k ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ),
          ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
            ‖signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, signHeckeTerm_unitsEquiv hχ _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

variable (a) in
/-- For $t_w > 0$, the normalized theta series minus its term $\alpha = 0$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem signHeckeTheta_sub_eq_tsum {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    signHeckeTheta K ε p k a t - signHeckeTerm ε p k 0 t = ∑' α : NonzeroElt a, signHeckeTerm ε p k (α : K) t := by
  let z : (a : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  rw [signHeckeTheta_eq_tsum, (summable_signHeckeTerm ε p k a ht).tsum_eq_add_tsum_ite z]
  rw [show ((z : (a : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from rfl, add_sub_cancel_left]
  refine Eq.trans ?_ (tsum_subtype {α : (a : FractionalIdeal (𝓞 K)⁰ K) | (α : K) ≠ 0}
    (fun α => signHeckeTerm ε p k (α : K) t)).symm
  refine tsum_congr fun α => ?_
  have hz : α = z ↔ (α : K) = 0 := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : (α : K) = 0
  · simp [hz.2 h, Set.indicator, z]
  · simp [mt hz.1 h, h]

/-- **The unfolding for a fixed $y$.** If $\chi_\infty$ is trivial on all units and $y > 0$, then $$\int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc = w_K \sum_I \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha_I) \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem hasSum_integral_unitCube_signHeckeTheta (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        ∫ c, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c))
      (∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (signHeckeTheta K ε p k a (unitScale K y c) - signHeckeTerm ε p k 0 (unitScale K y c))) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (tsum_lintegral_signHeckeTerm_le hy)
  have hm : ∀ x : K, Measurable fun c => signHeckeTerm ε p k x (unitScale K y c) := fun x =>
    (measurable_signHeckeTerm x).comp (continuous_unitScale y).measurable
  set g : NonzeroElt a → ℂ := fun α => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
    signHeckeTerm ε p k (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      (signHeckeTheta K ε p k a (unitScale K y c) - signHeckeTerm ε p k 0 (unitScale K y c)) = ∑' α, g α := by
    simp_rw [signHeckeTheta_sub_eq_tsum a (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_signHeckeTerm (a := a) hχ hy.le
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a, Integrable fun c => signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) * ∫⁻ c, ‖signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) * ∫ c, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y (c + fun i => (m i : ℝ))) with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, signHeckeTerm_unitsEquiv hχ _ _ hy.le]
    have hsG : Summable fun q : torsion K × (Fin (rank K) → ℤ) => G q.2 := by
      refine (((unitsEquiv K).trans (unitsEquivFiber I)).summable_iff.2
        (hsum.subtype (orbitOf a ⁻¹' {I}))).congr fun q => ?_
      exact hval q
    calc ∑' β : (orbitOf a ⁻¹' {I}), g β
        = ∑' q : torsion K × (Fin (rank K) → ℤ),
            g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) :=
          (((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq (fun β => g β)).symm
      _ = ∑' q : torsion K × (Fin (rank K) → ℤ), G q.2 := tsum_congr hval
      _ = ∑' _ : torsion K, ∑' m, G m := hsG.tsum_prod' fun ζ => hsG.prod_factor ζ
      _ = (torsionOrder K : ℂ) * ∑' m, G m := by
          have := Fintype.ofFinite (torsion K)
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
            Nat.card_eq_fintype_card]
      _ = _ := by rw [integral_eq_tsum_unitCube _ (hint I)]
  rw [h2]
  convert hsum.hasSum.tsum_fiberwise (orbitOf a) using 1
  exact funext fun I => (hfib I).symm

end Unfold

section Mellin

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- The integral $\int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc$ is measurable in $y$. -/
theorem measurable_integral_signHeckeTerm (x : K) :
    Measurable fun y : ℝ => ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k x (unitScale K y c) :=
  (StronglyMeasurable.integral_prod_right' (f := fun q : ℝ × (Fin (rank K) → ℝ) =>
    signHeckeTerm ε p k x (unitScale K q.1 q.2))
    (measurable_signHeckeTerm_unitScale x).stronglyMeasurable).measurable

/-- **The unfolding of the weighted Hecke theta function.** Let $\chi_\infty$ be trivial on all units of $K$, torsion included, let $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$. Then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal, that is over $(\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. The series converges. -/
theorem hasSum_integral_signHeckeTheta_sub (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          (signHeckeTheta K ε p k a (unitScale K y c) - signHeckeTerm ε p k 0 (unitScale K y c))) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (signHeckeTheta K ε p k a (unitScale K y c) - signHeckeTerm ε p k 0 (unitScale K y c))) :=
    fun y hy => (hasSum_integral_unitCube_signHeckeTheta hχ hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_integral_signHeckeTerm _))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_signHeckeTerm_lt_top ε p k a hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    rw [tsum_lintegral_unitCube_signHeckeTerm hχ (le_of_lt hy), ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun I => ?_
    simp only [hg]
    rw [enorm_mul, enorm_mul, ← ofReal_norm (x := (torsionOrder K : ℂ)), Complex.norm_natCast,
      ENNReal.ofReal_natCast]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  have hsum : Summable fun I => ∫ y in Ioi (0 : ℝ), g I y := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun I => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have heq := integral_tsum hmeas hfin
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).tsum_eq] at heq
  have hterm : ∀ I : Orbits a, ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), g I y =
      (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) := by
    intro I
    rw [← integral_unitScale_signHeckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c))) =
        fun y : ℝ => (torsionOrder K : ℂ) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

/-- **The unfolding for a nonzero weight.** If $(p, k) \neq 0$, the term $\alpha = 0$ vanishes, and under the hypotheses of `hasSum_integral_signHeckeTheta_sub`, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'}.$$ -/
theorem hasSum_integral_signHeckeTheta (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), signHeckeTheta K ε p k a (unitScale K y c)) := by
  simpa only [signHeckeTerm_zero h, sub_zero] using hasSum_integral_signHeckeTheta_sub (a := a) hχ hs

end Mellin

section Dual

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- The term of the dual theta series at $\beta$ is the complex conjugate of the normalized term of $\beta$ at the point $(n_w^2 t_w)_w$. Here $n_w$ is $1$ at a real place and $2$ at a complex place, and the conjugate embedding at a complex place gives the conjugate weight. -/
theorem signDualTerm_eq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) (β : K) :
    (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        signMixedGaussWeight ε p k t (globalConjEmbedding K (fun w => (mult w : ℝ)) β) =
      conj (signHeckeTerm ε p k β (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have hr : ∀ v : {w : InfinitePlace K // IsReal w}, weightExp p k v.1 = p v := fun v => by
    simp [weightExp, v.2]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, weightExp p k w.1 = k w := fun w => by
    simp [weightExp, not_isReal_iff_isComplex.2 w.2]
  rw [signHeckeTerm, signMixedGaussWeight_globalConjEmbedding, signMixedGaussWeight_globalEmbedding,
    prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun w => (((mult w : ℝ) ^ 2 * t w : ℝ) : ℂ) ^
      ((weightExp p k w : ℂ) / 2))]
  simp only [hr, hc, map_mul, map_prod]
  have HR : ∀ v : {w : InfinitePlace K // IsReal w},
      (t v.1 : ℂ) ^ ((p v : ℂ) / 2) *
          realGaussWeight (p v) (t v.1) ((mult v.1 : ℝ) * embedding_of_isReal v.2 β) =
        conj ((((mult v.1 : ℝ) ^ 2 * t v.1 : ℝ) : ℂ) ^ ((p v : ℂ) / 2)) *
          conj (realGaussWeight (p v) ((mult v.1 : ℝ) ^ 2 * t v.1)
            ((1 : ℝ) * embedding_of_isReal v.2 β)) := by
    intro v
    rw [mult_isReal v, Nat.cast_one, one_pow, one_mul, one_mul, conj_ofReal_cpow_half (ht _)]
    simp only [realGaussWeight, map_mul, map_pow, Complex.conj_ofReal]
  have HC : ∀ w : {w : InfinitePlace K // IsComplex w},
      (t w.1 : ℂ) ^ ((k w : ℂ) / 2) *
          gaussWeight (k w) (t w.1) (((mult w.1 : ℝ) : ℂ) * conj (signEmbedding ε w.1 β)) =
        conj ((((mult w.1 : ℝ) ^ 2 * t w.1 : ℝ) : ℂ) ^ ((k w : ℂ) / 2)) *
          conj (gaussWeight (k w) ((mult w.1 : ℝ) ^ 2 * t w.1)
            (((1 : ℝ) : ℂ) * signEmbedding ε w.1 β)) := by
    intro w
    rw [mult_isComplex w, conj_ofReal_cpow_half (by have := ht w.1; positivity),
      Complex.ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (ht _),
      ofReal_sq_cpow_half (by norm_num)]
    simp only [gaussWeight, map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal,
      Complex.ofReal_one, one_mul, norm_mul]
    norm_num
    ring_nf
  calc _ = (∏ v : {w : InfinitePlace K // IsReal w}, (t v.1 : ℂ) ^ ((p v : ℂ) / 2) *
          realGaussWeight (p v) (t v.1) ((mult v.1 : ℝ) * embedding_of_isReal v.2 β)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (t w.1 : ℂ) ^ ((k w : ℂ) / 2) *
          gaussWeight (k w) (t w.1) (((mult w.1 : ℝ) : ℂ) * conj (signEmbedding ε w.1 β)) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = _ := by
        simp only [HR, HC, Finset.prod_mul_distrib]
        ring

variable (ε p k) in
/-- The dual theta series of $\mathfrak{a}$ is the complex conjugate of the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ at the point $(n_w^2 t_w)_w$. So it is the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ for the conjugate weight, and the factor $n_w^2 = 4$ at a complex place is the only change of the variable. -/
theorem signHeckeDualTheta_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 ≤ t w) :
    signHeckeDualTheta K ε p k a t =
      conj (signHeckeTheta K ε p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have e : (dualIdeal K a : FractionalIdeal (𝓞 K)⁰ K) =
      ((dualUnit K a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
    (coe_dualUnit_eq K a).symm
  have hs : (fun w => (dualScale K 1 w : ℝ)) = fun w => (mult w : ℝ) := funext (coe_dualScale_one K)
  rw [signHeckeDualTheta, signIdealDualTheta, signHeckeTheta_eq_tsum, Complex.conj_tsum, ← tsum_mul_left]
  let E : {x : K // x ∈ dualIdeal K a} ≃ {x : K // x ∈ ((dualUnit K a :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)} :=
    Equiv.subtypeEquivRight fun x => by rw [e]
  refine Eq.trans ?_ (E.tsum_eq _)
  refine tsum_congr fun β => ?_
  simp only [hs, sub_zero, mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  exact signDualTerm_eq ht (β : K)

end Dual

section Bounds

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- If $s \ge 0$ and $t_w \ge s$ for all $w$, then $|h_t(\alpha)| \le C_{p, k}$ times the term of $\alpha$ in the theta function of weight $0$ at the constant point $s / 4$. -/
theorem norm_signHeckeTerm_le_const {s : ℝ} (hs : 0 ≤ s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) (α : K) :
    ‖signHeckeTerm ε p k α t‖ ≤ heckeConst p k * thetaTerm α (fun _ => s / 4) :=
  (norm_signHeckeTerm_le (fun w => hs.trans (hst w)) α).trans
    (mul_le_mul_of_nonneg_left (thetaTerm_anti α fun w => by have := hst w; linarith)
      heckeConst_pos.le)

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(t) - h_t(0)| \le C_{p, k} (\theta_{\mathfrak{b}}(s / 4) - 1)$. -/
theorem norm_signHeckeTheta_sub_le (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖signHeckeTheta K ε p k b t - signHeckeTerm ε p k 0 t‖ ≤
      heckeConst p k * (dedekindTheta K b (fun _ => s / 4) - 1) := by
  have ht : ∀ w, 0 < t w := fun w => hs.trans_le (hst w)
  let z : (b : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((b : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  have hθ : HasSum (fun α : (b : FractionalIdeal (𝓞 K)⁰ K) => thetaTerm (α : K) (fun _ => s / 4))
      (dedekindTheta K b (fun _ => s / 4)) :=
    (summable_dedekindTheta b (t := fun _ => s / 4) fun _ => by positivity).hasSum
  have hG := (hθ.sub (hasSum_ite_eq z (1 : ℝ))).mul_left (heckeConst p k)
  have hF : signHeckeTheta K ε p k b t - signHeckeTerm ε p k 0 t =
      ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
        (signHeckeTerm ε p k (α : K) t - if α = z then signHeckeTerm ε p k 0 t else 0) := by
    rw [Summable.tsum_sub (summable_signHeckeTerm ε p k b ht) ⟨_, hasSum_ite_eq z _⟩, tsum_ite_eq,
      signHeckeTheta_eq_tsum]
  rw [hF]
  refine tsum_of_norm_bounded hG fun α => ?_
  by_cases h : α = z
  · subst h
    simp [thetaTerm, z]
  · simp only [h, ↓reduceIte, sub_zero]
    exact norm_signHeckeTerm_le_const hs.le hst _

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(t)| \le C_{p, k} \, \theta_{\mathfrak{b}}(s / 4)$. -/
theorem norm_signHeckeTheta_le (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖signHeckeTheta K ε p k b t‖ ≤ heckeConst p k * dedekindTheta K b (fun _ => s / 4) := by
  have h1 := norm_signHeckeTheta_sub_le (ε := ε) (p := p) (k := k) b hs hst
  have h2 := norm_signHeckeTerm_le_const (ε := ε) (p := p) (k := k) hs.le hst 0
  have h3 : thetaTerm (0 : K) (fun _ => s / 4) = 1 := by simp [thetaTerm]
  rw [h3] at h2
  calc ‖signHeckeTheta K ε p k b t‖
      ≤ ‖signHeckeTheta K ε p k b t - signHeckeTerm ε p k 0 t‖ + ‖signHeckeTerm ε p k 0 t‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

/-- Each normalized term $h_t(\alpha)$ is continuous in $t$ on the set of $t$ with all coordinates positive. -/
theorem continuousOn_signHeckeTerm (α : K) :
    ContinuousOn (fun t => signHeckeTerm ε p k α t) {t : InfinitePlace K → ℝ | ∀ w, 0 < t w} := by
  simp_rw [signHeckeTerm_eq_prod]
  refine continuousOn_finsetProd _ fun w _ => ?_
  have hg : Continuous fun t : ℝ => signPlaceGauss ε p k t α w := by
    unfold signPlaceGauss realGaussWeight gaussWeight
    split_ifs <;> fun_prop
  refine ContinuousOn.mul ?_ (hg.comp (continuous_apply w)).continuousOn
  refine (Complex.continuous_ofReal.comp (continuous_apply w)).continuousOn.cpow_const ?_
  exact fun t ht => Complex.ofReal_mem_slitPlane.2 (ht w)

/-- The normalized theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_signHeckeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (signHeckeTheta K ε p k b) t := by
  obtain ⟨m, hm, hmt⟩ : ∃ m > 0, ∀ w, m ≤ t w := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty t, ?_, fun w => Finset.inf'_le _ (Finset.mem_univ w)⟩
    exact (Finset.lt_inf'_iff _).2 fun w _ => ht w
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | m / 2 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have htU : t ∈ U := mem_iInter.2 fun w => (half_lt_self hm).trans_le (hmt w)
  have hc : ContinuousOn (fun s => ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
      signHeckeTerm ε p k (α : K) s) U := by
    refine continuousOn_tsum (fun α => (continuousOn_signHeckeTerm (α : K)).mono fun s hs w =>
        (half_pos hm).trans (mem_iInter.1 hs w))
      ((summable_dedekindTheta b (t := fun _ => m / 2 / 4) fun _ => by positivity).mul_left
        (heckeConst p k)) ?_
    intro α s hs
    exact norm_signHeckeTerm_le_const (half_pos hm).le (fun w => (mem_iInter.1 hs w).le) _
  have he : signHeckeTheta K ε p k b = fun s => ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
      signHeckeTerm ε p k (α : K) s := funext (signHeckeTheta_eq_tsum K ε p k b)
  rw [he]
  exact hc.continuousAt (hU.mem_nhds htU)

/-- The dual theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_signHeckeDualTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (signHeckeDualTheta K ε p k a) t := by
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | 0 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have he : (fun s => conj (signHeckeTheta K ε p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * s w)))
      =ᶠ[𝓝 t] signHeckeDualTheta K ε p k a := by
    filter_upwards [hU.mem_nhds (mem_iInter.2 ht)] with s hs
    exact (signHeckeDualTheta_eq ε p k a fun w => (mem_iInter.1 hs w).le).symm
  refine ContinuousAt.congr ?_ he
  refine Complex.continuous_conj.continuousAt.comp ?_
  refine ContinuousAt.comp (g := signHeckeTheta K ε p k (dualUnit K a))
    (continuousAt_signHeckeTheta _ fun w => mul_pos (one_pos.trans_le (one_le_mult_sq w)) (ht w)) ?_
  exact (continuous_pi fun w => continuous_const.mul (continuous_apply w)).continuousAt

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series at $t$ has the absolute value at most $C_{p, k} \, \theta_{(\mathfrak{a} \mathfrak{d})^{-1}}(s / 4)$. -/
theorem norm_signHeckeDualTheta_le (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖signHeckeDualTheta K ε p k a t‖ ≤
      heckeConst p k * dedekindTheta K (dualUnit K a) (fun _ => s / 4) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [signHeckeDualTheta_eq ε p k a fun w => hs.le.trans (hst w), Complex.norm_conj]
  exact norm_signHeckeTheta_le _ hs hst'

/-- If the weight is not zero, $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series at $t$ has the absolute value at most $C_{p, k} (\theta_{(\mathfrak{a} \mathfrak{d})^{-1}}(s / 4) - 1)$. -/
theorem norm_signHeckeDualTheta_le_of_ne (h : p ≠ 0 ∨ k ≠ 0) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖signHeckeDualTheta K ε p k a t‖ ≤
      heckeConst p k * (dedekindTheta K (dualUnit K a) (fun _ => s / 4) - 1) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [signHeckeDualTheta_eq ε p k a fun w => hs.le.trans (hst w), Complex.norm_conj]
  have := norm_signHeckeTheta_sub_le (ε := ε) (p := p) (k := k) (dualUnit K a) hs hst'
  rwa [signHeckeTerm_zero h, sub_zero] at this

end Bounds

variable {K : Type*} [Field K] [NumberField K]

/-- The cube $[0, 1)^r$ of the unit coordinates. -/
local notation "cube" => Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1


section Pair

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The cube average $F(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) \, dc$ of the normalized theta series. -/
noncomputable def signHeckeCubeTheta (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), signHeckeTheta K ε p k a (unitScale K y c)

/-- The cube average $G(y) = \int_{[0, 1)^r} \widehat{\Theta}_{\mathfrak{a}}^{p, k}(t(y, -c)) \, dc$ of the dual theta series. -/
noncomputable def signHeckeCubeDualTheta (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    signHeckeDualTheta K ε p k a (unitScale K y (-c))

variable {K ε p k a}

/-- For $y \ge 0$ the dual cube average is the cube average of the complex conjugate of the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ at $(n_w^2 \, t(y, -c)_w)_w$. -/
theorem signHeckeCubeDualTheta_eq {y : ℝ} (hy : 0 ≤ y) :
    signHeckeCubeDualTheta K ε p k a y =
      ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
        conj (signHeckeTheta K ε p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w)) := by
  rw [signHeckeCubeDualTheta]
  congr 1
  funext c
  exact signHeckeDualTheta_eq ε p k a fun w => mul_nonneg hy (Real.exp_pos _).le

/-- The functional equation of the cube averages: if $p_v \le 1$ for all real $v$ and $x > 0$, then $F(1 / x) = \varepsilon \, x^{n / 2} \, G(x)$. -/
theorem signHeckeCubeTheta_one_div (hp : ∀ v, p v ≤ 1) {x : ℝ} (hx : 0 < x) :
    signHeckeCubeTheta K ε p k a (1 / x) =
      (heckeRootConst K p k a * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        signHeckeCubeDualTheta K ε p k a x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [signHeckeCubeTheta, signHeckeCubeDualTheta, smul_eq_mul]
  simp_rw [signHeckeTheta_unitScale a hp (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul, heckeRootConst]

/-- The cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_signHeckeCubeTheta : ContinuousOn (signHeckeCubeTheta K ε p k a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i) (fun _ ht => continuousAt_signHeckeTheta a ht)
    fun _ hs => ⟨_, fun _ hst => norm_signHeckeTheta_le a hs hst⟩

/-- The dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_signHeckeCubeDualTheta : ContinuousOn (signHeckeCubeDualTheta K ε p k a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_signHeckeDualTheta a ht)
    fun _ hs => ⟨_, fun _ hst => norm_signHeckeDualTheta_le a hs hst⟩

/-- If the weight is not zero, then $F(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_signHeckeCubeTheta (h : p ≠ 0 ∨ k ≠ 0) (r : ℝ) :
    signHeckeCubeTheta K ε p k a =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := id) _ (fun c hc i => abs_le_one_of_mem_unitCube hc i) a
    heckeConst_pos.le (fun s hs t hst => by
      have := norm_signHeckeTheta_sub_le (ε := ε) (p := p) (k := k) a hs hst
      rwa [signHeckeTerm_zero h, sub_zero] at this) r

/-- If the weight is not zero, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_signHeckeCubeDualTheta (h : p ≠ 0 ∨ k ≠ 0) (r : ℝ) :
    signHeckeCubeDualTheta K ε p k a =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := Neg.neg) _
    (fun c hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (dualUnit K a) heckeConst_pos.le (fun s hs t hst => norm_signHeckeDualTheta_le_of_ne h a hs hst) r

variable (ε a) in
/-- For $p_v \le 1$ and a nonzero weight, the cube averages $F$ and $G$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon$ and with both constant terms zero. -/
noncomputable def signHeckeFEPair (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) : WeakFEPair ℂ where
  f := signHeckeCubeTheta K ε p k a
  g := signHeckeCubeDualTheta K ε p k a
  k := finrank ℚ K / 2
  ε := heckeRootConst K p k a
  f₀ := 0
  g₀ := 0
  hf_int := continuousOn_signHeckeCubeTheta.locallyIntegrableOn measurableSet_Ioi
  hg_int := continuousOn_signHeckeCubeDualTheta.locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := heckeRootConst_ne_zero
  h_feq x hx := signHeckeCubeTheta_one_div hp hx
  hf_top r := by simpa only [sub_zero] using isBigO_signHeckeCubeTheta h r
  hg_top r := by simpa only [sub_zero] using isBigO_signHeckeCubeDualTheta h r

/-- The FE pair of the cube averages is a strong FE pair, because the constant terms are zero for a nonzero weight. -/
theorem isStrongFEPair_signHeckeFEPair (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) :
    IsStrongFEPair (signHeckeFEPair ε a hp h) :=
  ⟨rfl, rfl⟩

end Pair

section Completed

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
include hp h

/-- The completed function of the pair is the Mellin transform of $F$. -/
theorem Λ_signHeckeFEPair_eq : (signHeckeFEPair ε a hp h).Λ = mellin (signHeckeCubeTheta K ε p k a) :=
  (isStrongFEPair_signHeckeFEPair hp h).Λ_eq

/-- The completed function of the dual pair is the Mellin transform of $G$. -/
theorem symm_Λ_signHeckeFEPair_eq :
    (signHeckeFEPair ε a hp h).symm.Λ = mellin (signHeckeCubeDualTheta K ε p k a) :=
  (isStrongFEPair_signHeckeFEPair hp h).symm_Λ_eq

/-- The Mellin transform of $F$ continues to an entire function. -/
theorem differentiable_Λ_signHeckeFEPair : Differentiable ℂ (signHeckeFEPair ε a hp h).Λ :=
  (isStrongFEPair_signHeckeFEPair hp h).differentiable_Λ

/-- The Mellin transform of $G$ continues to an entire function. -/
theorem differentiable_mellin_signHeckeCubeDualTheta :
    Differentiable ℂ (mellin (signHeckeCubeDualTheta K ε p k a)) :=
  symm_Λ_signHeckeFEPair_eq hp h ▸ (isStrongFEPair_signHeckeFEPair hp h).symm.differentiable_Λ

/-- The functional equation $\Lambda(n / 2 - s) = \varepsilon \, \mathcal{M}G(s)$ for all complex $s$, where $\Lambda$ is the entire continuation of the Mellin transform of $F$. -/
theorem Λ_signHeckeFEPair_sub (s : ℂ) :
    (signHeckeFEPair ε a hp h).Λ (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * mellin (signHeckeCubeDualTheta K ε p k a) s := by
  have := (signHeckeFEPair ε a hp h).functional_equation s
  rw [symm_Λ_signHeckeFEPair_eq hp h, smul_eq_mul] at this
  convert this using 2
  · simp [signHeckeFEPair]
  · rfl

/-- If $\chi_\infty$ is trivial on the units and $\mathrm{Re}\, s > n / 2$, then $2^r c_K \Lambda(s)$ is the sum over the unit orbits of $\mathfrak{a} \setminus 0$ of $w_K \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}$ with $s' = 2 s / n$. Here $c_K$ is `Langlands.Tate.unitConst`. -/
theorem hasSum_Λ_signHeckeFEPair (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signHeckeFEPair ε a hp h).Λ s) := by
  rw [Λ_signHeckeFEPair_eq hp h, mellin]
  simp_rw [smul_eq_mul]
  exact hasSum_integral_signHeckeTheta h hχ hs

end Completed

section Periodic

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- **The periodicity under a unit.** If $u$ is a unit with $\chi_\infty(u) = 1$ and $t_w \ge 0$ for all $w$, then $\Theta_{\mathfrak{b}}^{p, k}((t_w |u|_w^2)_w) = \Theta_{\mathfrak{b}}^{p, k}(t)$. -/
theorem signHeckeTheta_unit (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : (𝓞 K)ˣ}
    (hu : signInfinityWeight ε p k (u : K) = 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) :
    signHeckeTheta K ε p k b (fun w => t w * w (u : K) ^ 2) = signHeckeTheta K ε p k b t := by
  rw [signHeckeTheta_eq_tsum, signHeckeTheta_eq_tsum]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) u).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [signHeckeTerm_mul ht (coe_ne_zero u), hu, one_mul]

/-- **The periodicity in the unit coordinates.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $\Theta_{\mathfrak{b}}^{p, k}(t(y, c + m)) = \Theta_{\mathfrak{b}}^{p, k}(t(y, c))$ for each integer vector $m$. -/
theorem signHeckeTheta_unitScale_add_int (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    signHeckeTheta K ε p k b (unitScale K y (c + fun i => (m i : ℝ))) =
      signHeckeTheta K ε p k b (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h]
  exact signHeckeTheta_unit (t := unitScale K y c) b (hχ _) fun w => mul_nonneg hy (Real.exp_pos _).le

end Periodic

variable {r : ℕ}


variable (K : Type*) [Field K] [NumberField K]

variable {K}


section Mellin

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The dual cube average.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $G_{\mathfrak{a}}(y) = \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$. -/
theorem signHeckeCubeDualTheta_eq_conj (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    signHeckeCubeDualTheta K ε p k a y =
      conj (signHeckeCubeTheta K ε p k (dualUnit K a) (heckeScale K * y)) := by
  have h : ∀ c : Fin (rank K) → ℝ,
      (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w) =
        unitScale K (heckeScale K * y) (heckeShift K - c) :=
    fun c => funext fun w => mult_sq_mul_unitScale_neg y c w
  rw [signHeckeCubeDualTheta_eq hy, signHeckeCubeTheta]
  simp_rw [h]
  rw [integral_conj, integral_unitCube_sub
    (fun c => signHeckeTheta K ε p k (dualUnit K a) (unitScale K (heckeScale K * y) c))
    (fun m c => signHeckeTheta_unitScale_add_int hχ _
      (mul_nonneg (heckeScale_pos K).le hy) c m) (heckeShift K)]

/-- **The Mellin transform of the dual cube average.** If $\chi_\infty$ is trivial on all units, then $\mathcal{M}G_{\mathfrak{a}}(s) = \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$ for all complex $s$. -/
theorem mellin_signHeckeCubeDualTheta (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) (s : ℂ) :
    mellin (signHeckeCubeDualTheta K ε p k a) s =
      (heckeScale K : ℂ) ^ (-s) * conj (mellin (signHeckeCubeTheta K ε p k (dualUnit K a)) (conj s)) := by
  have h : mellin (signHeckeCubeDualTheta K ε p k a) s =
      mellin (fun y => conj (signHeckeCubeTheta K ε p k (dualUnit K a) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [signHeckeCubeDualTheta_eq_conj hχ (le_of_lt hy)]
  rw [h, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul, map_mul,
    conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]

end Mellin

section Completed

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The completed partial Hecke sum $\Lambda_{\mathfrak{a}}(s) = 2^r c_K \, \mathcal{M}F_{\mathfrak{a}}(s)$ of the weight $(p, k)$, where $F_{\mathfrak{a}}$ is the cube average `Langlands.Tate.signHeckeCubeTheta` and $c_K$ is `Langlands.Tate.unitConst`. For $p_v \le 1$ and $(p, k) \neq 0$ the Mellin integral converges for all $s$, and the function is entire. -/
noncomputable def signCompletedPartialHecke (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * mellin (signHeckeCubeTheta K ε p k a) s

variable {K ε p k a}

/-- The completed partial Hecke sum is $2^r c_K$ times the completed function of the FE pair. -/
theorem signCompletedPartialHecke_eq (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) (s : ℂ) :
    signCompletedPartialHecke K ε p k a s =
      ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signHeckeFEPair ε a hp h).Λ s := by
  rw [Λ_signHeckeFEPair_eq hp h, signCompletedPartialHecke]

/-- **The completed partial Hecke sum is entire.** -/
theorem differentiable_signCompletedPartialHecke (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) :
    Differentiable ℂ (signCompletedPartialHecke K ε p k a) := by
  have e : signCompletedPartialHecke K ε p k a =
      fun s => ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signHeckeFEPair ε a hp h).Λ s :=
    funext (signCompletedPartialHecke_eq hp h)
  rw [e]
  exact (differentiable_Λ_signHeckeFEPair hp h).const_mul _

/-- **The completed partial Hecke sum as a series.** If $(p, k) \neq 0$, $\chi_\infty$ is trivial on all units and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_{\mathfrak{a}}(s) = \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} w_K \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_signCompletedPartialHecke (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (signCompletedPartialHecke K ε p k a s) := by
  rw [signCompletedPartialHecke, mellin]
  simp_rw [smul_eq_mul]
  exact hasSum_integral_signHeckeTheta h hχ hs

/-- **The functional equation of the completed partial Hecke sums.** Let $p_v \le 1$, $(p, k) \neq 0$, and let $\chi_\infty$ be trivial on all units. Then for all complex $s$, $$\Lambda_{\mathfrak{a}}(n / 2 - s) = \varepsilon_{\mathfrak{a}} \, \lambda^{-s} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})},$$ with $\lambda = 2^{4 r_2 / n}$ and $\varepsilon_{\mathfrak{a}} = (-i)^{\sum_v p_v + \sum_w k_w} (N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$. -/
theorem signCompletedPartialHecke_sub (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) (s : ℂ) :
    signCompletedPartialHecke K ε p k a (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (-s) *
        conj (signCompletedPartialHecke K ε p k (dualUnit K a) (conj s)) := by
  rw [signCompletedPartialHecke_eq hp h, Λ_signHeckeFEPair_sub hp h, mellin_signHeckeCubeDualTheta hχ,
    signCompletedPartialHecke, map_mul, Complex.conj_ofReal]
  ring

/-- **The functional equation, solved for $\Lambda_{\mathfrak{a}}(s)$.** Under the hypotheses of `signCompletedPartialHecke_sub`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(s) = \varepsilon_{\mathfrak{a}} \, \lambda^{s - n / 2} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(n / 2 - \bar{s})}.$$ -/
theorem signCompletedPartialHecke_eq_conj (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) (s : ℂ) :
    signCompletedPartialHecke K ε p k a s =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (s - finrank ℚ K / 2) *
        conj (signCompletedPartialHecke K ε p k (dualUnit K a) (finrank ℚ K / 2 - conj s)) := by
  have e := signCompletedPartialHecke_sub (a := a) hp h hχ (finrank ℚ K / 2 - s)
  rw [sub_sub_cancel, neg_sub] at e
  rw [e, map_sub, map_div₀, map_natCast, map_ofNat]

/-- **The dual series for $\mathrm{Re}\, s < 0$.** Under the hypotheses of `signCompletedPartialHecke_sub`, let $\mathrm{Re}\, s < 0$ and $s^* = 2 (n / 2 - \bar{s}) / n$. Then $\Lambda_{\mathfrak{a}}(s)$ is the sum over $\beta \in ((\mathfrak{a} \mathfrak{d})^{-1} \setminus 0) / \mathcal{O}_K^\times$ of $$\varepsilon_{\mathfrak{a}} \, \lambda^{s - n / 2} \, \overline{w_K \, \Gamma_{p, k}(s^*) \, \chi_\infty(\beta) \, |N(\beta)|^{-s^*}}.$$ -/
theorem hasSum_signCompletedPartialHecke_of_re_neg (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) {s : ℂ} (hs : s.re < 0) :
    HasSum (fun I : Orbits (dualUnit K a) =>
        heckeRootConst K p k a * (heckeScale K : ℂ) ^ (s - finrank ℚ K / 2) *
          conj ((torsionOrder K : ℂ) *
            (heckeGamma p k (2 * (finrank ℚ K / 2 - conj s) / finrank ℚ K) *
              signInfinityWeight ε p k (orbitRep (dualUnit K a) I : K) *
                ((|(Algebra.norm ℚ (orbitRep (dualUnit K a) I : K) : ℝ)| : ℝ) : ℂ) ^
                  (-(2 * (finrank ℚ K / 2 - conj s) / finrank ℚ K)))))
      (signCompletedPartialHecke K ε p k a s) := by
  have hre : (finrank ℚ K : ℝ) / 2 < (finrank ℚ K / 2 - conj s).re := by
    rw [Complex.sub_re, Complex.conj_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  rw [signCompletedPartialHecke_eq_conj hp h hχ]
  exact ((hasSum_signCompletedPartialHecke (a := dualUnit K a) h hχ hre).map (starRingEnd ℂ)
    (continuous_conj)).mul_left _

end Completed

end Langlands.Tate
