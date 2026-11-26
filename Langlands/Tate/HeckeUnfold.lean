/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMellinUnits

/-!
# The unfolding of the weighted Hecke theta function

Let $K$ be a number field of degree $n$ with $w_K$ roots of unity, unit rank $r$ and regulator $R_K$. Fix a weight $(p, k)$ and a nonzero fractional ideal $\mathfrak{a}$. Let $h_t(\alpha)$ be the normalized term and $\Theta_{\mathfrak{a}}^{p, k}(t) = \sum_{\alpha \in \mathfrak{a}} h_t(\alpha)$ the normalized theta series of `Langlands/Tate/HeckeMellinUnits.lean`, and let $t(y, c)$ be the unit coordinates of `Langlands.Tate.unitScale`. This file does the unfolding step of Hecke's proof for a general weight. If $\chi_\infty$ is trivial on all units of $K$ and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ The term $h_t(0)$ is zero when $(p, k) \neq 0$ and is $1$ when $(p, k) = 0$.

## Main definitions

* `Langlands.Tate.heckeConst`: the constant $C_{p, k} = \prod_w (1 + q_w!)$ of the bound of the normalized terms.

## Main results

* `Langlands.Tate.mixedGaussWeight_zero`, `Langlands.Tate.heckeTerm_zero`: the term $\alpha = 0$ is zero when $(p, k) \neq 0$.
* `Langlands.Tate.norm_heckeTerm_le`: $|h_t(\alpha)| \le C_{p, k} \, e^{-\pi \sum_w n_w (t_w / 4) |\alpha|_w^2}$.
* `Langlands.Tate.lintegral_tsum_heckeTerm_lt_top`: the absolute convergence of the sum over $\mathfrak{a} \setminus 0$ and the integrals over $y > 0$ and $c \in [0, 1)^r$, for $\mathrm{Re}\, s > n / 2$.
* `Langlands.Tate.heckeTerm_unitsEquiv`: the periodicity in $c$ under all units, when $\chi_\infty$ is trivial on the units.
* `Langlands.Tate.hasSum_integral_unitCube_heckeTheta`: the unfolding for a fixed $y > 0$.
* `Langlands.Tate.hasSum_integral_heckeTheta_sub`: the formula above, as a convergent series.
* `Langlands.Tate.hasSum_integral_heckeTheta`: the same formula for $(p, k) \neq 0$, with $\Theta_{\mathfrak{a}}^{p, k}$ itself.

## Proof

The method is the method of `Langlands/Tate/UnitUnfold.lean` for the weight $0$. With $a = \sqrt{t_w} |\alpha|_w$, the factor of $h_t(\alpha)$ at the place $w$ has the absolute value $a^{q_w} e^{-\pi a^2} \le (1 + q_w!) e^{-\pi a^2 / 2}$. So $|h_t(\alpha)|$ is at most $C_{p, k}$ times the term of $\alpha$ in the theta function of weight $0$ at $t / 4$. Since $t(y, c) / 4 = t(y / 4, c)$, the sum and the integrals of $|y^{s - 1} h_{t(y, c)}(\alpha)|$ are at most $C_{p, k}$ times the Mellin integral of $|y^{s - 1}| (\Theta_{\mathfrak{a}}(y / 4) - 1)$, which is finite for $\mathrm{Re}\, s > n / 2$. If $\chi_\infty(u) = 1$ for each unit $u = \zeta \prod_i \varepsilon_i^{m_i}$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$. With the absolute convergence, the sum over $\mathfrak{a} \setminus 0$ splits into the orbits of the units, the sum over $m \in \mathbb{Z}^r$ of the integrals over $[0, 1)^r$ is one integral over $\mathbb{R}^r$, and the sums and the integrals commute. The integral of each orbit is `Langlands.Tate.integral_unitScale_heckeTerm`.

## Open parts

This file does not yet prove the functional equation. The missing steps are these.
* The identification of the dual theta function with the normalized theta function of the dual ideal for the conjugate weight.
* The pair of theta functions as an FE pair, the analytic continuation and the symmetry $s \leftrightarrow 1 - s$.
* The sum over the orbits as the partial Hecke $L$-series of the ideal class of $\mathfrak{a}^{-1}$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped Real Classical nonZeroDivisors ENNReal

namespace Langlands.Tate

section Zero

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- **The weight at $0$.** If $(p, k) \neq 0$, then $G_t^{p, k}(0) = 0$. -/
theorem mixedGaussWeight_zero (h : p ≠ 0 ∨ k ≠ 0) (t : InfinitePlace K → ℝ) :
    mixedGaussWeight p k t 0 = 0 := by
  simp only [mixedGaussWeight, map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  rcases h with h | h
  · obtain ⟨v, hv⟩ := Function.ne_iff.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simpa [realGaussWeight] using hv), zero_mul]
  · obtain ⟨w, hw⟩ := Function.ne_iff.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simpa [gaussWeight] using hw), mul_zero]

/-- **The term $\alpha = 0$.** If $(p, k) \neq 0$, then $h_t(0) = 0$. -/
theorem heckeTerm_zero (h : p ≠ 0 ∨ k ≠ 0) (t : InfinitePlace K → ℝ) :
    heckeTerm p k (0 : K) t = 0 := by
  rw [heckeTerm, map_zero, mixedGaussWeight_zero h, mul_zero]

end Zero

section Bound

variable {K : Type*} [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The constant $C_{p, k} = \prod_w (1 + q_w!)$ of the bound of the normalized terms. -/
noncomputable def heckeConst : ℝ :=
  ∏ w : InfinitePlace K, (1 + ((weightExp p k w).factorial : ℝ))

variable {p k}

/-- The constant $C_{p, k}$ is positive. -/
theorem heckeConst_pos : 0 < heckeConst (K := K) p k :=
  Finset.prod_pos fun _ _ => by positivity

/-- For $a \ge 0$, $a^q e^{-\pi a^2} \le (1 + q!) e^{-\pi a^2 / 2}$. -/
theorem pow_mul_exp_le_factorial {a : ℝ} (ha : 0 ≤ a) (q : ℕ) :
    a ^ q * Real.exp (-(π * a ^ 2)) ≤ (1 + (q.factorial : ℝ)) * Real.exp (-(π * a ^ 2) / 2) := by
  have h1 : a ^ q ≤ 1 + (a ^ 2) ^ q := by
    rcases le_total a 1 with h | h
    · have := pow_le_one₀ ha h (n := q)
      have : 0 ≤ (a ^ 2) ^ q := by positivity
      linarith
    · have : a ^ q ≤ (a ^ 2) ^ q := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ h (by omega)
      linarith
  have h2 : (a ^ 2) ^ q ≤ q.factorial * Real.exp (π * a ^ 2 / 2) := by
    have h := Real.pow_div_factorial_le_exp (x := a ^ 2) (sq_nonneg a) q
    rw [div_le_iff₀ (by positivity)] at h
    have h3 : Real.exp (a ^ 2) ≤ Real.exp (π * a ^ 2 / 2) := by
      apply Real.exp_le_exp.2
      have := Real.pi_gt_three
      nlinarith [sq_nonneg a]
    calc (a ^ 2) ^ q ≤ Real.exp (a ^ 2) * q.factorial := h
      _ ≤ Real.exp (π * a ^ 2 / 2) * q.factorial := by gcongr
      _ = _ := mul_comm _ _
  have h4 : a ^ q ≤ (1 + (q.factorial : ℝ)) * Real.exp (π * a ^ 2 / 2) := by
    have : 1 ≤ Real.exp (π * a ^ 2 / 2) := Real.one_le_exp (by positivity)
    nlinarith
  calc a ^ q * Real.exp (-(π * a ^ 2))
      ≤ (1 + (q.factorial : ℝ)) * Real.exp (π * a ^ 2 / 2) * Real.exp (-(π * a ^ 2)) := by
        gcongr
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

omit [NumberField K] in
/-- The norm of the factor at one place: for $t \ge 0$, $|t^{q_w / 2} g_w(t, \alpha)| \le (1 + q_w!) e^{-\pi t |\alpha|_w^2 / 2}$. -/
theorem norm_placeTerm_le {t : ℝ} (ht : 0 ≤ t) (α : K) (w : InfinitePlace K) :
    ‖placeTerm p k t α w‖ ≤
      (1 + ((weightExp p k w).factorial : ℝ)) * Real.exp (-(π * (t * w α ^ 2)) / 2) := by
  have hst : √t ^ 2 = t := Real.sq_sqrt ht
  have hc : ‖(t : ℂ) ^ ((weightExp p k w : ℂ) / 2)‖ = √t ^ weightExp p k w := by
    rw [show ((weightExp p k w : ℂ) / 2) = (((weightExp p k w : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht]
    congr 1
    ring
  have key : ‖placeTerm p k t α w‖ = (√t * w α) ^ weightExp p k w *
      Real.exp (-(π * (√t * w α) ^ 2)) := by
    rw [placeTerm, norm_mul, hc, mul_pow, mul_pow, hst, mul_assoc]
    congr 1
    by_cases h : IsReal w
    · have hq : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
      simp only [placeGauss, h, ↓reduceDIte, realGaussWeight, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp]
      rw [hq, ← Real.norm_eq_abs, norm_embedding_of_isReal]
      congr 2
      rw [← norm_embedding_of_isReal h α, Real.norm_eq_abs, sq_abs]
      ring
    · have hq : weightExp p k w = k ⟨w, not_isReal_iff_isComplex.1 h⟩ := by simp [weightExp, h]
      simp only [placeGauss, h, ↓reduceDIte, gaussWeight, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp, RCLike.norm_conj, norm_embedding_eq]
      rw [hq]
      congr 2
      ring
  rw [key, show -(π * (t * w α ^ 2)) / 2 = -(π * (√t * w α) ^ 2) / 2 by rw [mul_pow, hst]]
  exact pow_mul_exp_le_factorial (by positivity) _

omit [NumberField K] in
/-- The multiplicity $n_w$ of a place is at most $2$. -/
theorem mult_le_two (w : InfinitePlace K) : (mult w : ℝ) ≤ 2 := by
  unfold mult
  split_ifs <;> norm_num

/-- **The bound of the normalized terms.** For $t_w \ge 0$, $$|h_t(\alpha)| \le C_{p, k} \, e^{-\pi \sum_w n_w (t_w / 4) |\alpha|_w^2}.$$ The right side is $C_{p, k}$ times the term of $\alpha$ in the theta function $\theta_{\mathfrak{a}}(t / 4)$ of weight $0$. -/
theorem norm_heckeTerm_le {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) (α : K) :
    ‖heckeTerm p k α t‖ ≤ heckeConst p k * thetaTerm α (fun w => t w / 4) := by
  rw [heckeTerm_eq_prod, norm_prod]
  calc ∏ w, ‖placeTerm p k (t w) α w‖
      ≤ ∏ w, (1 + ((weightExp p k w).factorial : ℝ)) * Real.exp (-(π * (t w * w α ^ 2)) / 2) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun w _ => norm_placeTerm_le (ht w) α w)
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
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {s : ℂ}

/-- The unit coordinates satisfy $t(y, c) / 4 = t(y / 4, c)$. -/
theorem unitScale_div_four (y : ℝ) (c : Fin (rank K) → ℝ) :
    (fun w => unitScale K y c w / 4) = unitScale K (4⁻¹ * y) c := by
  funext w
  simp only [unitScale]
  ring

variable (p k a) in
/-- For $t_w > 0$, the family of the normalized terms $h_t(\alpha)$, $\alpha \in \mathfrak{a}$, is summable. -/
theorem summable_heckeTerm {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => heckeTerm p k (α : K) t :=
  Summable.of_norm_bounded (((summable_dedekindTheta a (t := fun w => t w / 4)
    fun w => by have := ht w; positivity)).mul_left (heckeConst p k))
    fun α => norm_heckeTerm_le (fun w => (ht w).le) (α : K)

/-- For $y > 0$, the sum over $\alpha \in \mathfrak{a} \setminus 0$ of the integrals of $|h_{t(y, c)}(\alpha)|$ over $c \in [0, 1)^r$ is at most $C_{p, k} (\Theta_{\mathfrak{a}}(y / 4) - 1)$, where $\Theta_{\mathfrak{a}}$ is the unit theta function of weight $0$. -/
theorem tsum_lintegral_heckeTerm_le {y : ℝ} (hy : 0 < y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ ≤
      ENNReal.ofReal (heckeConst p k) * ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1) := by
  have hy' : 0 < 4⁻¹ * y := by positivity
  have hint : IntegrableOn (fun c => dedekindTheta K a (unitScale K (4⁻¹ * y) c) - 1)
      (Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) :=
    (integrableOn_dedekindTheta_unitScale a hy').sub (integrableOn_const volume_unitCube_ne_top)
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ
      ≤ ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ENNReal.ofReal (heckeConst p k) *
            ENNReal.ofReal (thetaTerm (α : K) (unitScale K (4⁻¹ * y) c)) := by
        refine ENNReal.tsum_le_tsum fun α => lintegral_mono fun c => ?_
        rw [← ENNReal.ofReal_mul heckeConst_pos.le, ← ofReal_norm, ← unitScale_div_four]
        exact ENNReal.ofReal_le_ofReal
          (norm_heckeTerm_le (fun w => (unitScale_pos hy c w).le) (α : K))
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
theorem tsum_lintegral_enorm_mul (y : ℝ) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖(y : ℂ) ^ (s - 1) * heckeTerm p k (α : K) (unitScale K y c)‖ₑ =
      ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun α => ?_
  simp_rw [enorm_mul]
  exact lintegral_const_mul' _ _ enorm_ne_top

variable (p k a) in
/-- The bound of `lintegral_tsum_heckeTerm_lt_top`, with the factor $|y^{s - 1}|$ outside the sum. -/
theorem lintegral_enorm_mul_tsum_lt_top {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a,
      ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ <
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
          ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ
      ≤ ‖(y : ℂ) ^ (s - 1)‖ₑ * (ENNReal.ofReal (heckeConst p k) *
          ENNReal.ofReal (unitTheta K a (4⁻¹ * y) - 1)) := by
        gcongr
        exact tsum_lintegral_heckeTerm_le hy'
    _ = _ := by ring

variable (p k a) in
/-- **The absolute convergence.** For $\mathrm{Re}\, s > n / 2$, $$\int_0^\infty \sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |y^{s - 1} h_{t(y, c)}(\alpha)| \, dc \, dy < \infty.$$ The cube $[0, 1)^r$ is a fundamental domain of the unit lattice $\mathbb{Z}^r$ in the unit coordinates. -/
theorem lintegral_tsum_heckeTerm_lt_top {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖(y : ℂ) ^ (s - 1) * heckeTerm p k (α : K) (unitScale K y c)‖ₑ < ⊤ := by
  simp_rw [tsum_lintegral_enorm_mul]
  exact lintegral_enorm_mul_tsum_lt_top p k a hs

end Convergence

section Measurable

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- The factor of the normalized term at one place is measurable in $t$. -/
theorem measurable_placeTerm (α : K) (w : InfinitePlace K) :
    Measurable fun t : ℝ => placeTerm p k t α w := by
  refine (Complex.measurable_ofReal.pow_const _).mul (Continuous.measurable ?_)
  unfold placeGauss realGaussWeight gaussWeight
  split_ifs <;> fun_prop

/-- The normalized term $h_t(\alpha)$ is measurable in $t$. -/
theorem measurable_heckeTerm (α : K) : Measurable fun t => heckeTerm p k α t := by
  simp_rw [heckeTerm_eq_prod]
  exact Finset.measurable_prod _ fun w _ => (measurable_placeTerm α w).comp (measurable_pi_apply w)

/-- The normalized term $h_{t(y, c)}(\alpha)$ is measurable in $(y, c)$. -/
theorem measurable_heckeTerm_unitScale (α : K) :
    Measurable fun q : ℝ × (Fin (rank K) → ℝ) => heckeTerm p k α (unitScale K q.1 q.2) := by
  refine (measurable_heckeTerm α).comp (Continuous.measurable (continuous_pi fun w => ?_))
  unfold unitScale
  fun_prop

end Measurable

section Unfold

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The periodicity under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$. -/
theorem heckeTerm_unitsEquiv (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ) :
    heckeTerm p k ((unitsEquiv K q : K) * α) (unitScale K y c) =
      heckeTerm p k α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [heckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _) α, hχ, one_mul]
  congr 1
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- The integral of an integrable function $F$ over $\mathbb{R}^r$ is the sum over $m \in \mathbb{Z}^r$ of the integrals of $F(c + m)$ over $[0, 1)^r$. -/
theorem integral_eq_tsum_unitCube {r : ℕ} (F : (Fin r → ℝ) → ℂ) (hF : Integrable F) :
    ∫ c, F c = ∑' m : Fin r → ℤ,
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), F (c + fun i => (m i : ℝ)) := by
  rw [← ZSpan.fundamentalDomain_pi_basisFun]
  set b := Pi.basisFun ℝ (Fin r)
  have hD := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin r → ℝ))
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hmem : ∀ m : Fin r → ℤ,
      (fun i => (m i : ℝ)) ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    intro m
    rw [Submodule.mem_toAddSubgroup, b.mem_span_iff_repr_mem ℤ]
    intro i
    rw [Pi.basisFun_repr]
    exact ⟨m i, rfl⟩
  let e : (Fin r → ℤ) ≃ (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    Equiv.ofBijective (fun m => ⟨fun i => (m i : ℝ), hmem m⟩)
      ⟨fun m l h => funext fun i => by
        exact Int.cast_injective (α := ℝ) (congrFun (congrArg Subtype.val h) i),
      fun g => by
        have hg : ∀ i, ∃ m : ℤ, (g : Fin r → ℝ) i = m := by
          intro i
          obtain ⟨m, hm⟩ := (b.mem_span_iff_repr_mem ℤ (g : Fin r → ℝ)).1 g.2 i
          exact ⟨m, by simpa [b] using hm.symm⟩
        choose m hm using hg
        exact ⟨m, Subtype.ext (funext fun i => (hm i).symm)⟩⟩
  rw [hD.integral_eq_tsum' F hF, ← (e.trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun m => ?_
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, e]
  rw [add_comm]
  rfl

/-- **The unfolding of the absolute values.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |h_{t(y, c)}(\alpha_I)| \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem tsum_lintegral_unitCube_heckeTerm (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ‖heckeTerm p k ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ),
          ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
            ‖heckeTerm p k (orbitRep a I : K) (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, heckeTerm_unitsEquiv hχ _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

variable (a) in
/-- For $t_w > 0$, the normalized theta series minus its term $\alpha = 0$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem heckeTheta_sub_eq_tsum {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    heckeTheta K p k a t - heckeTerm p k 0 t = ∑' α : NonzeroElt a, heckeTerm p k (α : K) t := by
  let z : (a : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  rw [heckeTheta_eq_tsum, (summable_heckeTerm p k a ht).tsum_eq_add_tsum_ite z]
  rw [show ((z : (a : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from rfl, add_sub_cancel_left]
  refine Eq.trans ?_ (tsum_subtype {α : (a : FractionalIdeal (𝓞 K)⁰ K) | (α : K) ≠ 0}
    (fun α => heckeTerm p k (α : K) t)).symm
  refine tsum_congr fun α => ?_
  have hz : α = z ↔ (α : K) = 0 := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : (α : K) = 0
  · simp [hz.2 h, Set.indicator, z]
  · simp [mt hz.1 h, h]

/-- **The unfolding for a fixed $y$.** If $\chi_\infty$ is trivial on all units and $y > 0$, then $$\int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc = w_K \sum_I \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha_I) \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem hasSum_integral_unitCube_heckeTheta (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        ∫ c, heckeTerm p k (orbitRep a I : K) (unitScale K y c))
      (∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (heckeTheta K p k a (unitScale K y c) - heckeTerm p k 0 (unitScale K y c))) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (tsum_lintegral_heckeTerm_le hy)
  have hm : ∀ x : K, Measurable fun c => heckeTerm p k x (unitScale K y c) := fun x =>
    (measurable_heckeTerm x).comp (continuous_unitScale y).measurable
  set g : NonzeroElt a → ℂ := fun α => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
    heckeTerm p k (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      (heckeTheta K p k a (unitScale K y c) - heckeTerm p k 0 (unitScale K y c)) = ∑' α, g α := by
    simp_rw [heckeTheta_sub_eq_tsum a (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_heckeTerm (a := a) hχ hy.le
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a, Integrable fun c => heckeTerm p k (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) * ∫⁻ c, ‖heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) * ∫ c, heckeTerm p k (orbitRep a I : K) (unitScale K y c) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      heckeTerm p k (orbitRep a I : K) (unitScale K y (c + fun i => (m i : ℝ))) with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, heckeTerm_unitsEquiv hχ _ _ hy.le]
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
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- The integral $\int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc$ is measurable in $y$. -/
theorem measurable_integral_heckeTerm (x : K) :
    Measurable fun y : ℝ => ∫ c : Fin (rank K) → ℝ, heckeTerm p k x (unitScale K y c) :=
  (StronglyMeasurable.integral_prod_right' (f := fun q : ℝ × (Fin (rank K) → ℝ) =>
    heckeTerm p k x (unitScale K q.1 q.2))
    (measurable_heckeTerm_unitScale x).stronglyMeasurable).measurable

/-- **The unfolding of the weighted Hecke theta function.** Let $\chi_\infty$ be trivial on all units of $K$, torsion included, let $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$. Then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal, that is over $(\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. The series converges. -/
theorem hasSum_integral_heckeTheta_sub (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          (heckeTheta K p k a (unitScale K y c) - heckeTerm p k 0 (unitScale K y c))) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K) (unitScale K y c)) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (heckeTheta K p k a (unitScale K y c) - heckeTerm p k 0 (unitScale K y c))) :=
    fun y hy => (hasSum_integral_unitCube_heckeTheta hχ hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_integral_heckeTerm _))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_lt_top p k a hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    rw [tsum_lintegral_unitCube_heckeTerm hχ (le_of_lt hy), ← ENNReal.tsum_mul_left]
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
        infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) := by
    intro I
    rw [← integral_unitScale_heckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K) (unitScale K y c))) =
        fun y : ℝ => (torsionOrder K : ℂ) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

/-- **The unfolding for a nonzero weight.** If $(p, k) \neq 0$, the term $\alpha = 0$ vanishes, and under the hypotheses of `hasSum_integral_heckeTheta_sub`, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'}.$$ -/
theorem hasSum_integral_heckeTheta (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), heckeTheta K p k a (unitScale K y c)) := by
  simpa only [heckeTerm_zero h, sub_zero] using hasSum_integral_heckeTheta_sub (a := a) hχ hs

end Mellin

end Langlands.Tate
