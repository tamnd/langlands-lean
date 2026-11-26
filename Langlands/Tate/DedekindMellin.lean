/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.DedekindTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Mellin transform of a term of the theta function

Let $K$ be a number field with $r_1$ real and $r_2$ complex places. We use the notation of `Langlands.Tate.DedekindTheta`: $|x|_w = |\sigma_w(x)|$ and $n_w \in \{1, 2\}$. Hecke's proof of the functional equation of the Dedekind zeta function takes the Mellin transform of the theta function $\theta_{\mathfrak{a}}(t) = \sum_{\alpha \in \mathfrak{a}} e^{-\pi \sum_w n_w t_w |\alpha|_w^2}$ in the variables $t = (t_w)_w \in (0, \infty)^{S_\infty}$. This file computes the Mellin transform of one term. For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$ it is $$\int_{(0, \infty)^{S_\infty}} e^{-\pi \sum_w n_w t_w |\alpha|_w^2} \prod_w t_w^{n_w s / 2} \, \frac{dt_w}{t_w} = \Gamma_K(s) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s},$$ where $$\Gamma_K(s) = \prod_w (\pi n_w)^{-n_w s / 2} \, \Gamma(n_w s / 2) = \Gamma_\mathbb{R}(s)^{r_1} \left(\frac{\Gamma_\mathbb{C}(s)}{2}\right)^{r_2}.$$

## Main results

* `Langlands.Tate.gammaK` and `Langlands.Tate.gammaK_eq`: the Gamma factor $\Gamma_K(s)$ and its expression through Deligne's factors `Complex.Gammaℝ` and `Complex.Gammaℂ`.
* `Langlands.Tate.integral_pi_cpow_mul_exp`: the Gamma integral in several variables.
* `Langlands.Tate.integral_exp_mul_prod_eq_gammaK`: the formula above.

## Proof

The integrand is a product of functions of one variable, so Fubini's theorem (`MeasureTheory.integral_fintype_prod_eq_prod`) reduces the integral to the Gamma integrals $\int_0^\infty t^{z - 1} e^{-r t} \, dt = r^{-z} \Gamma(z)$ with $z = n_w s / 2$ and $r = \pi n_w |\alpha|_w^2$. The factors $|\alpha|_w^{-n_w s}$ multiply to $|N_{K/\mathbb{Q}}(\alpha)|^{-s}$ by the product formula $\prod_w |\alpha|_w^{n_w} = |N_{K/\mathbb{Q}}(\alpha)|$.

## Conventions

The measure on $(0, \infty)^{S_\infty}$ is the product of the Lebesgue measures on the half lines, written as `Measure.pi fun _ => volume.restrict (Ioi 0)`. The factor $\prod_w t_w^{-1}$ of the Haar measure $\prod_w dt_w / t_w$ is part of the integrand. The Gamma factor $\Gamma_K$ differs from the usual $\Gamma_\mathbb{R}^{r_1} \Gamma_\mathbb{C}^{r_2}$ by the constant $2^{-r_2}$. This constant does not change a functional equation of the form $\Lambda(s) = \Lambda(1 - s)$.

## References

* E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, chapter VIII.
* J. Neukirch, Algebraic number theory, chapter VII, section 5.
-/

open MeasureTheory Module NumberField NumberField.InfinitePlace Set
open scoped Real

namespace Langlands.Tate

/-- For $x > 0$ and $z \in \mathbb{C}$, $x^z = e^{z \log x}$. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- For $x > 0$ and $z \in \mathbb{C}$, $(1/x)^z = e^{-z \log x}$. -/
theorem one_div_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (1 / x : ℂ) ^ z = Complex.exp (-(z * Real.log x)) := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, ofReal_cpow_eq_exp (one_div_pos.2 hx),
    one_div, Real.log_inv, Complex.ofReal_neg, mul_neg]

/-- The Gamma integral with a scaling: for $\mathrm{Re}\, z > 0$ and $r > 0$, $$\int_0^\infty t^{z - 1} e^{-r t} \, dt = e^{-z \log r} \, \Gamma(z) = r^{-z} \, \Gamma(z).$$ -/
theorem integral_Ioi_cpow_mul_exp {z : ℂ} (hz : 0 < z.re) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * (Real.exp (-(r * t)) : ℂ) =
      Complex.exp (-(z * Real.log r)) * Complex.Gamma z := by
  rw [← one_div_cpow_eq_exp hr, ← Complex.integral_cpow_mul_exp_neg_mul_Ioi hz hr]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Complex.ofReal_exp]
  push_cast
  rfl

/-- The Gamma integral in several variables: for $\mathrm{Re}\, z_i > 0$ and $r_i > 0$, $$\int_{(0, \infty)^\iota} \prod_i t_i^{z_i - 1} e^{-r_i t_i} \, dt = \prod_i r_i^{-z_i} \, \Gamma(z_i).$$ The measure is the Lebesgue measure on the product of the half lines. -/
theorem integral_pi_cpow_mul_exp {ι : Type*} [Fintype ι] {z : ι → ℂ} (hz : ∀ i, 0 < (z i).re)
    {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    ∫ t : ι → ℝ, ∏ i, (t i : ℂ) ^ (z i - 1) * (Real.exp (-(r i * t i)) : ℂ)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      ∏ i, Complex.exp (-(z i * Real.log (r i))) * Complex.Gamma (z i) := by
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) =>
    (t : ℂ) ^ (z i - 1) * (Real.exp (-(r i * t)) : ℂ))]
  exact Finset.prod_congr rfl fun i _ => integral_Ioi_cpow_mul_exp (hz i) (hr i)

open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The archimedean Gamma factor of $K$ in Hecke's normalization, $$\Gamma_K(s) = \prod_w (\pi n_w)^{-n_w s / 2} \, \Gamma(n_w s / 2).$$ -/
noncomputable def gammaK (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K, ((π * mult w : ℝ) : ℂ) ^ (-((mult w : ℂ) * s / 2)) *
    Complex.Gamma ((mult w : ℂ) * s / 2)

/-- The Gamma factor in terms of Deligne's factors: $\Gamma_K(s) = \Gamma_\mathbb{R}(s)^{r_1} (\Gamma_\mathbb{C}(s) / 2)^{r_2}$, where $\Gamma_\mathbb{R}(s) = \pi^{-s/2} \Gamma(s/2)$ and $\Gamma_\mathbb{C}(s) = 2 (2 \pi)^{-s} \Gamma(s)$. -/
theorem gammaK_eq (s : ℂ) :
    gammaK K s =
      Complex.Gammaℝ s ^ nrRealPlaces K * (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K := by
  rw [gammaK, prod_eq_prod_mul_prod]
  have hr : ∀ w : {w : InfinitePlace K // IsReal w},
      ((π * mult w.1 : ℝ) : ℂ) ^ (-((mult w.1 : ℂ) * s / 2)) *
        Complex.Gamma ((mult w.1 : ℂ) * s / 2) = Complex.Gammaℝ s := by
    intro w
    rw [mult_isReal w, Complex.Gammaℝ_def]
    push_cast
    rw [mul_one, one_mul, neg_div]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((π * mult w.1 : ℝ) : ℂ) ^ (-((mult w.1 : ℂ) * s / 2)) *
        Complex.Gamma ((mult w.1 : ℂ) * s / 2) = Complex.Gammaℂ s / 2 := by
    intro w
    rw [mult_isComplex w, Complex.Gammaℂ_def]
    push_cast
    rw [mul_div_cancel_left₀ s two_ne_zero, mul_comm (π : ℂ) 2]
    ring
  simp_rw [hr, hc, Finset.prod_const, Finset.card_univ]

variable {K}

omit [NumberField K] in
/-- If $\mathrm{Re}\, s > 0$, then $\mathrm{Re}(n_w s / 2) > 0$. -/
theorem mult_mul_re_pos {s : ℂ} (hs : 0 < s.re) (w : InfinitePlace K) :
    0 < ((mult w : ℂ) * s / 2).re := by
  have h : ((mult w : ℂ) * s).re = mult w * s.re := by simp [Complex.mul_re]
  rw [Complex.div_ofNat_re, h]
  exact div_pos (mul_pos (Nat.cast_pos.2 mult_pos) hs) two_pos

omit [NumberField K] in
/-- A computation for one place: for $\alpha \neq 0$ and $z = n_w s / 2$, $$(\pi n_w |\alpha|_w^2)^{-z} \, \Gamma(z) = (\pi n_w)^{-z} \, \Gamma(z) \, |\alpha|_w^{-n_w s}.$$ -/
theorem exp_log_mul (s : ℂ) {α : K} (hα : α ≠ 0) (w : InfinitePlace K) :
    Complex.exp (-((mult w : ℂ) * s / 2 * Real.log (π * mult w * w α ^ 2))) *
        Complex.Gamma ((mult w : ℂ) * s / 2) =
      ((π * mult w : ℝ) : ℂ) ^ (-((mult w : ℂ) * s / 2)) * Complex.Gamma ((mult w : ℂ) * s / 2) *
        Complex.exp (-(s * (mult w * Real.log (w α)))) := by
  have hπ : 0 < π * mult w := mul_pos Real.pi_pos (Nat.cast_pos.2 mult_pos)
  have hw : 0 < w α := InfinitePlace.pos_iff.2 hα
  rw [ofReal_cpow_eq_exp hπ, Real.log_mul hπ.ne' (pow_ne_zero 2 hw.ne'), Real.log_pow]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The product formula at the infinite places, in logarithmic form: for $\alpha \neq 0$, $\sum_w n_w \log |\alpha|_w = \log |N_{K/\mathbb{Q}}(\alpha)|$. -/
theorem sum_mult_log (α : K) (hα : α ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w α) = Real.log |(Algebra.norm ℚ α : ℝ)| := by
  rw [← Rat.cast_abs, ← prod_eq_abs_norm, Real.log_prod]
  · exact Finset.sum_congr rfl fun w _ => by rw [Real.log_pow]
  · exact fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.2 hα).ne'

/-- For $\alpha \neq 0$, $|N_{K/\mathbb{Q}}(\alpha)| > 0$. -/
theorem abs_norm_pos {α : K} (hα : α ≠ 0) : (0 : ℝ) < |(Algebra.norm ℚ α : ℝ)| := by
  rw [abs_pos, Rat.cast_ne_zero]
  exact (Algebra.norm_ne_zero_iff).2 hα

/-- The Mellin transform of one term of the theta function, as a product over the places: for $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} \prod_w t_w^{n_w s / 2 - 1} e^{-\pi n_w |\alpha|_w^2 t_w} \, dt = \Gamma_K(s) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s}.$$ -/
theorem integral_pi_prod_eq_gammaK {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) *
        (Real.exp (-((π * mult w * w α ^ 2) * t w)) : ℂ)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      gammaK K s * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [integral_pi_cpow_mul_exp (fun w => mult_mul_re_pos hs w)
    (fun w => mul_pos (mul_pos Real.pi_pos (Nat.cast_pos.2 mult_pos))
      (pow_pos (InfinitePlace.pos_iff.2 hα) 2))]
  simp_rw [exp_log_mul s hα]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, gammaK, ofReal_cpow_eq_exp (abs_norm_pos hα)]
  congr 2
  rw [← sum_mult_log α hα]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The product of the exponentials over the places is the term of the theta function: $\prod_w e^{-\pi n_w |\alpha|_w^2 t_w} = e^{-\pi \sum_w n_w t_w |\alpha|_w^2}$. -/
theorem prod_exp_eq_exp_sum (α : K) (t : InfinitePlace K → ℝ) :
    ∏ w, (Real.exp (-((π * mult w * w α ^ 2) * t w)) : ℂ) =
      (Real.exp (-π * ∑ w, (mult w : ℝ) * t w * w α ^ 2) : ℂ) := by
  rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The Mellin transform of one term of the theta function: for $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} e^{-\pi \sum_w n_w t_w |\alpha|_w^2} \prod_w t_w^{n_w s / 2} \, \frac{dt_w}{t_w} = \Gamma_K(s) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s}.$$ -/
theorem integral_exp_mul_prod_eq_gammaK {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, (Real.exp (-π * ∑ w, (mult w : ℝ) * t w * w α ^ 2) : ℂ) *
        ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      gammaK K s * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [← integral_pi_prod_eq_gammaK hs hα]
  congr 1
  funext t
  rw [Finset.prod_mul_distrib, prod_exp_eq_exp_sum, mul_comm]

end Langlands.Tate
