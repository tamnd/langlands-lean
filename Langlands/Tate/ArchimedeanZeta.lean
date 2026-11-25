/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local zeta integrals at the archimedean places

This file contains the first half of the archimedean local theory of Tate's thesis: the local zeta integrals at a real and at a complex place, their absolute convergence, and their values at the standard test functions.

## Conventions

A quasi-character of $\mathbb{R}^\times$ or $\mathbb{C}^\times$ is given by its parameters, in the form of `Langlands.HeckeCharacter.IsArchimedeanParameter`. For $m \in \{1, 2\}$, $n \in \mathbb{Z}$ and $t \in \mathbb{C}$ the function `Langlands.Tate.archChar m n t` is $z \mapsto (z / |z|)^n |z|^{m t}$ on $\mathbb{C}$. At a real place $m = 1$, the argument is real, and $n \in \{0, 1\}$, so the character is $\mathrm{sgn}(x)^n |x|^t$. At a complex place $m = 2$ and the character is $(z / |z|)^n |z|_\mathbb{C}^t$, where $|z|_\mathbb{C} = |z|^2$ is the normalized absolute value. So if $\chi$ has the parameters $(n, t)$ at an infinite place $v$, then $\chi_v$ is `archChar v.mult n t` composed with the embedding $K_v \to \mathbb{C}$, by definition.

The additive measure is the self-dual measure for the character $\psi$ of the file `Langlands.Tate.ArchimedeanFourier`: the Lebesgue measure $dx$ on $\mathbb{R}$, and twice the Lebesgue measure $2\, dx\, dy$ on $\mathbb{C}$. The multiplicative measure is $d^\times x = dx / |x|$, with the normalized absolute value. So on $\mathbb{C}$ it is $d^\times z = 2\, dx\, dy / |z|^2$.

The local zeta integral is $Z(f, \chi, s) = \int f(x) \chi(x) |x|^s \, d^\times x$:

* `Langlands.Tate.realZeta f n t s` is $\int_\mathbb{R} f(x) \, \mathrm{sgn}(x)^n |x|^t |x|^s \, dx / |x|$;
* `Langlands.Tate.complexZeta f n t s` is $\int_\mathbb{C} f(z) (z / |z|)^n |z|^{2t} |z|^{2s} \, 2\, dx\, dy / |z|^2$.

## Main results

* `Langlands.Tate.integrable_realZeta` and `Langlands.Tate.integrable_complexZeta`: for a Schwartz function $f$ the zeta integral converges absolutely when $\mathrm{Re}(s + t) > 0$.
* `Langlands.Tate.realZeta_realTest`: for the standard function $f_a(x) = x^a e^{-\pi x^2}$ with $a \in \{0, 1\}$, $Z(f_a, \mathrm{sgn}^a |\cdot|^t, s) = \Gamma_\mathbb{R}(s + t + a)$.
* `Langlands.Tate.complexZeta_complexTest`: for the standard function $f_n(z) = \bar z^n e^{-2 \pi |z|^2}$ if $n \geq 0$ and $f_n(z) = z^{|n|} e^{-2 \pi |z|^2}$ if $n < 0$, $Z(f_n, (z / |z|)^n |z|_\mathbb{C}^t, s) = \pi \, \Gamma_\mathbb{C}(s + t + |n| / 2)$.

## Proofs

Convergence: the absolute value of the integrand is $|x|^{r} |f(x)|$ with $r = \mathrm{Re}(s + t) - 1$ on $\mathbb{R}$ and twice $|z|^{r} |f(z)|$ with $r = 2 \mathrm{Re}(s + t) - 2$ on $\mathbb{C}$. On a space of dimension $d$ the function $|x|^r$ is integrable on the unit ball when $r > -d$ (integration in polar coordinates, `integrableOn_fun_norm_addHaar`). Outside the unit ball $|x|^r \leq |x|^N$ for an integer $N \geq r$, and $|x|^N |f(x)|$ is integrable because $f$ is a Schwartz function.

Standard functions: the product $f(x) \chi(x)$ depends only on $|x|$. Integration in polar coordinates (`integral_fun_norm_addHaar`) then turns the zeta integral into the Mellin transform of a Gaussian, $\int_0^\infty y^{w - 1} e^{-c y^2} \, dy = \frac{1}{2} c^{-w/2} \Gamma(w / 2)$ (`Langlands.Tate.integral_Ioi_cpow_mul_gaussian`).

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.5.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.1.
-/

namespace Langlands.Tate

open Complex MeasureTheory Set Module

/-- The quasi-character $z \mapsto (z / |z|)^n |z|^{m t}$ of $\mathbb{C}^\times$. This is the right side of `Langlands.HeckeCharacter.IsArchimedeanParameter`, where $m$ is the multiplicity of the place. -/
noncomputable def archChar (m : ℕ) (n : ℤ) (t : ℂ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ n * (‖z‖ : ℂ) ^ ((m : ℂ) * t)

@[fun_prop]
theorem measurable_archChar (m : ℕ) (n : ℤ) (t : ℂ) : Measurable (archChar m n t) := by
  unfold archChar
  fun_prop

/-- The absolute value of a quasi-character: $|\chi(z)| = |z|^{m \mathrm{Re}(t)}$ for $z \neq 0$. -/
theorem norm_archChar (m : ℕ) (n : ℤ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖archChar m n t z‖ = ‖z‖ ^ ((m : ℝ) * t.re) := by
  have h : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [archChar, norm_mul, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h, div_self h.ne', one_zpow, one_mul, norm_cpow_eq_rpow_re_of_pos h]
  simp

/-- The local zeta integral at a real place: $Z(f, \chi, s) = \int_\mathbb{R} f(x) \chi(x) |x|^s \, dx / |x|$ for the quasi-character $\chi(x) = \mathrm{sgn}(x)^n |x|^t$, written as `archChar 1 n t`. -/
noncomputable def realZeta (f : ℝ → ℂ) (n : ℤ) (t s : ℂ) : ℂ :=
  ∫ x : ℝ, f x * archChar 1 n t x * ((|x| : ℝ) : ℂ) ^ s / |x|

/-- The local zeta integral at a complex place: $Z(f, \chi, s) = \int_\mathbb{C} f(z) \chi(z) |z|_\mathbb{C}^s \, d^\times z$ for the quasi-character $\chi(z) = (z / |z|)^n |z|_\mathbb{C}^t$, written as `archChar 2 n t`. Here $|z|_\mathbb{C}^s = |z|^{2s}$ and $d^\times z = 2\, dx\, dy / |z|^2$. -/
noncomputable def complexZeta (f : ℂ → ℂ) (n : ℤ) (t s : ℂ) : ℂ :=
  ∫ z : ℂ, 2 * (f z * archChar 2 n t z * (‖z‖ : ℂ) ^ (2 * s) / (‖z‖ : ℂ) ^ 2)

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- On a real vector space of dimension $d$, the function $|x|^r$ is integrable on the unit ball when $r > -d$. -/
theorem integrableOn_ball_norm_rpow {r : ℝ} (hr : -(finrank ℝ E : ℝ) < r) :
    IntegrableOn (fun x : E => ‖x‖ ^ r) (Metric.ball 0 1) μ := by
  rw [integrableOn_fun_norm_addHaar μ (f := fun y : ℝ => y ^ r)]
  have hd : 1 ≤ finrank ℝ E := finrank_pos
  have hcast : ((finrank ℝ E - 1 : ℕ) : ℝ) = finrank ℝ E - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := r + (finrank ℝ E - 1 : ℕ)) (by rw [hcast]; linarith)
  refine (h.1.mono_set Ioo_subset_Ioc_self).congr_fun (fun y hy => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [Real.rpow_add hy.1, Real.rpow_natCast, mul_comm]

/-- For a Schwartz function $f$ on a real vector space of dimension $d$ and $r > -d$, the function $|x|^r |f(x)|$ is integrable. -/
theorem integrable_norm_rpow_mul_schwartz (f : SchwartzMap E ℂ) {r : ℝ}
    (hr : -(finrank ℝ E : ℝ) < r) : Integrable (fun x => ‖x‖ ^ r * ‖f x‖) μ := by
  have hb := (integrableOn_ball_norm_rpow μ hr).integrable_indicator measurableSet_ball
  have hN := f.integrable_pow_mul μ ⌈r⌉₊
  refine ((hb.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).add hN).mono' ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((measurable_norm.pow_const r).aestronglyMeasurable).mul
      f.continuous.norm.aestronglyMeasurable
  have h0 : 0 ≤ ‖x‖ ^ r := Real.rpow_nonneg (norm_nonneg x) r
  have hf := f.norm_le_seminorm ℝ x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (norm_nonneg _)), Pi.add_apply]
  by_cases hx : ‖x‖ < 1
  · rw [indicator_of_mem (by simpa using hx : x ∈ Metric.ball (0 : E) 1)]
    have : 0 ≤ ‖x‖ ^ ⌈r⌉₊ * ‖f x‖ := by positivity
    nlinarith
  · rw [indicator_of_notMem (by simpa using hx : x ∉ Metric.ball (0 : E) 1)]
    have : ‖x‖ ^ r ≤ ‖x‖ ^ ⌈r⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (not_lt.1 hx) (Nat.le_ceil r)
    simp only [zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

end Convergence

/-- The absolute value of the integrand of the real zeta integral. -/
theorem norm_realZeta_integrand_le (f : ℝ → ℂ) (n : ℤ) (t s : ℂ) (x : ℝ) :
    ‖f x * archChar 1 n t x * ((|x| : ℝ) : ℂ) ^ s / |x|‖ ≤ ‖x‖ ^ ((s + t).re - 1) * ‖f x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [abs_zero, ofReal_zero, div_zero, norm_zero]
    positivity
  have h : 0 < |x| := abs_pos.mpr hx
  rw [norm_div, norm_mul, norm_mul, norm_archChar 1 n t (ofReal_ne_zero.mpr hx),
    norm_cpow_eq_rpow_re_of_pos h]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_abs, Nat.cast_one, one_mul, add_re]
  rw [Real.rpow_sub_one h.ne', Real.rpow_add h]
  apply le_of_eq
  ring

/-- The local zeta integral at a real place converges absolutely for a Schwartz function $f$ when $\mathrm{Re}(s + t) > 0$. -/
theorem integrable_realZeta (f : SchwartzMap ℝ ℂ) (n : ℤ) {t s : ℂ} (h : 0 < (s + t).re) :
    Integrable (fun x : ℝ => f x * archChar 1 n t x * ((|x| : ℝ) : ℂ) ^ s / |x|) := by
  refine (integrable_norm_rpow_mul_schwartz volume f (r := (s + t).re - 1) ?_).mono' ?_
    (Filter.Eventually.of_forall (norm_realZeta_integrand_le f n t s))
  · simp only [finrank_self, Nat.cast_one]
    linarith
  · apply Measurable.aestronglyMeasurable
    have := f.continuous.measurable
    fun_prop

/-- The absolute value of the integrand of the complex zeta integral. -/
theorem norm_complexZeta_integrand_le (f : ℂ → ℂ) (n : ℤ) (t s : ℂ) (z : ℂ) :
    ‖2 * (f z * archChar 2 n t z * (‖z‖ : ℂ) ^ (2 * s) / (‖z‖ : ℂ) ^ 2)‖ ≤
      2 * (‖z‖ ^ (2 * (s + t).re - 2) * ‖f z‖) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [norm_zero, ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero, mul_zero]
    positivity
  have h : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_archChar 2 n t hz, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos h, norm_cpow_eq_rpow_re_of_pos h, add_re, Real.rpow_sub h,
    Real.rpow_two]
  apply le_of_eq
  have e1 : ((2 : ℂ) * s).re = 2 * s.re := by simp
  rw [e1, mul_add, Real.rpow_add h]
  simp only [Nat.cast_ofNat, Complex.norm_ofNat]
  ring

/-- The local zeta integral at a complex place converges absolutely for a Schwartz function $f$ when $\mathrm{Re}(s + t) > 0$. -/
theorem integrable_complexZeta (f : SchwartzMap ℂ ℂ) (n : ℤ) {t s : ℂ} (h : 0 < (s + t).re) :
    Integrable
      (fun z : ℂ => 2 * (f z * archChar 2 n t z * (‖z‖ : ℂ) ^ (2 * s) / (‖z‖ : ℂ) ^ 2)) := by
  refine ((integrable_norm_rpow_mul_schwartz volume f
    (r := 2 * (s + t).re - 2) ?_).const_mul 2).mono' ?_
    (Filter.Eventually.of_forall (norm_complexZeta_integrand_le f n t s))
  · simp only [Complex.finrank_real_complex, Nat.cast_ofNat]
    linarith
  · apply Measurable.aestronglyMeasurable
    have := f.continuous.measurable
    fun_prop

/-! ### Integrals of radial functions -/

/-- The Mellin transform of a Gaussian: $\int_0^\infty y^{w - 1} e^{-c y^2} \, dy = \frac{1}{2} c^{-w/2} \Gamma(w / 2)$ for $c > 0$ and $\mathrm{Re}(w) > 0$. -/
theorem integral_Ioi_cpow_mul_gaussian {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * cexp (-(c * (y : ℂ) ^ 2)) =
      (c : ℂ) ^ (-w / 2) * Gamma (w / 2) / 2 := by
  have h1 : (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * cexp (-(c * (y : ℂ) ^ 2))) =
      mellin (fun y : ℝ => (fun u : ℝ => cexp (-(c * (u : ℂ)))) (y ^ (2 : ℝ))) w := by
    simp only [mellin, smul_eq_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    simp only [Real.rpow_two, ofReal_pow]
  have hw2 : 0 < (w / 2).re := by
    rw [div_ofNat_re]
    linarith
  rw [h1]
  refine (mellin_comp_rpow (fun u : ℝ => cexp (-(c * (u : ℂ)))) w 2).trans ?_
  simp only [mellin, smul_eq_mul]
  have h2 : w / ((2 : ℝ) : ℂ) = w / 2 := by norm_num
  rw [h2, integral_cpow_mul_exp_neg_mul_Ioi hw2 hc, one_div,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hc.le]; exact Real.pi_ne_zero.symm), ← cpow_neg,
    abs_two, neg_div, Complex.real_smul]
  push_cast
  ring

/-- The integral of a radial function on $\mathbb{R}$: $\int_\mathbb{R} g(|x|) \, dx = 2 \int_0^\infty g(y) \, dy$. -/
theorem integral_real_radial (g : ℝ → ℂ) : ∫ x : ℝ, g |x| = 2 * ∫ y in Ioi (0 : ℝ), g y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) g
  simp only [Real.norm_eq_abs, finrank_self, tsub_self, pow_zero, one_smul] at h
  rw [h, measureReal_def, Real.volume_ball]
  simp

/-- The integral of a radial function on $\mathbb{C}$: $\int_\mathbb{C} g(|z|) \, dx\, dy = 2 \pi \int_0^\infty g(y) y \, dy$. -/
theorem integral_complex_radial (g : ℝ → ℂ) :
    ∫ z : ℂ, g ‖z‖ = 2 * Real.pi * ∫ y in Ioi (0 : ℝ), (y : ℂ) * g y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) g
  simp only [Complex.finrank_real_complex] at h
  rw [h, measureReal_def, Complex.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  simp only [Nat.add_one_sub_one, pow_one, Complex.real_smul, nsmul_eq_mul]
  push_cast
  ring

/-! ### The standard test functions -/

/-- The standard test function at a real place: $f_a(x) = x^a e^{-\pi x^2}$. It is used for $a \in \{0, 1\}$. -/
noncomputable def realTest (a : ℤ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ a.toNat * cexp (-(Real.pi * (x : ℂ) ^ 2))

/-- The standard test function at a complex place: $f_n(z) = \bar z^n e^{-2 \pi |z|^2}$ if $n \geq 0$ and $f_n(z) = z^{|n|} e^{-2 \pi |z|^2}$ if $n < 0$. The product $f_n(z) (z / |z|)^n$ is the radial function $|z|^{|n|} e^{-2 \pi |z|^2}$. -/
noncomputable def complexTest (n : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ n.natAbs) *
    cexp (-((2 * Real.pi : ℝ) * (‖z‖ : ℂ) ^ 2))

theorem realTest_mul_archChar {a : ℤ} (ha : a = 0 ∨ a = 1) (t : ℂ) (x : ℝ) :
    realTest a x * archChar 1 a t x =
      ((|x| : ℝ) : ℂ) ^ a.toNat * cexp (-(Real.pi * ((|x| : ℝ) : ℂ) ^ 2)) * ((|x| : ℝ) : ℂ) ^ t := by
  have hsq : (x : ℂ) ^ 2 = ((|x| : ℝ) : ℂ) ^ 2 := by rw [← ofReal_pow, ← ofReal_pow, sq_abs]
  simp only [realTest, archChar, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, one_mul, hsq]
  rcases ha with rfl | rfl
  · simp
  · simp only [Int.toNat_one, pow_one, zpow_one]
    have : (x : ℂ) * ((x : ℂ) / ((|x| : ℝ) : ℂ)) = |x| := by
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
        rw [← mul_div_assoc, ← sq, hsq]
        field_simp
    linear_combination (cexp (-(Real.pi * ((|x| : ℝ) : ℂ) ^ 2)) * ((|x| : ℝ) : ℂ) ^ t) * this

theorem complexTest_mul_archChar (n : ℤ) (t : ℂ) (z : ℂ) :
    complexTest n z * archChar 2 n t z =
      (‖z‖ : ℂ) ^ n.natAbs * cexp (-((2 * Real.pi : ℝ) * (‖z‖ : ℂ) ^ 2)) *
        (‖z‖ : ℂ) ^ ((2 : ℂ) * t) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [complexTest, archChar]
    · simp [complexTest, archChar, zero_zpow n hn, hn]
  have h0 : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hn : (starRingEnd ℂ z) * z = (‖z‖ : ℂ) ^ 2 := by rw [conj_mul']
  simp only [complexTest, archChar, Nat.cast_ofNat]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, zpow_natCast, Int.natAbs_natCast]
    have : (starRingEnd ℂ z) ^ k * (z / (‖z‖ : ℂ)) ^ k = (‖z‖ : ℂ) ^ k := by
      rw [← mul_pow, ← mul_div_assoc, hn, sq, mul_div_assoc, div_self h0, mul_one]
    rw [← this]
    ring
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp h))
    subst hk
    simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : z ^ k * ((z / (‖z‖ : ℂ)) ^ k)⁻¹ = (‖z‖ : ℂ) ^ k := by
      rw [← inv_pow, ← mul_pow, inv_div, mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hz, mul_one]
    rw [← this]
    ring

/-- The zeta integral of the standard test function at a real place: for $a \in \{0, 1\}$ and $\mathrm{Re}(s + t) > 0$, $Z(f_a, \mathrm{sgn}^a |\cdot|^t, s) = \Gamma_\mathbb{R}(s + t + a)$. -/
theorem realZeta_realTest {a : ℤ} (ha : a = 0 ∨ a = 1) {t s : ℂ} (h : 0 < (s + t).re) :
    realZeta (realTest a) a t s = Gammaℝ (s + t + a) := by
  have ha' : ((a.toNat : ℕ) : ℂ) = a := by
    rcases ha with rfl | rfl <;> simp
  have hpt : ∀ x : ℝ, realTest a x * archChar 1 a t x * ((|x| : ℝ) : ℂ) ^ s / |x| =
      ((|x| : ℝ) : ℂ) ^ a.toNat * cexp (-(Real.pi * ((|x| : ℝ) : ℂ) ^ 2)) *
        ((|x| : ℝ) : ℂ) ^ t * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) := by
    intro x
    rw [realTest_mul_archChar ha]
  rw [realZeta, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_real_radial (fun y : ℝ => (y : ℂ) ^ a.toNat * cexp (-(Real.pi * (y : ℂ) ^ 2)) *
      (y : ℂ) ^ t * (y : ℂ) ^ s / y)]
  have hw : 0 < (s + t + a).re := by
    rw [add_re] at h
    rcases ha with rfl | rfl <;> simp <;> linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    (y : ℂ) ^ (s + t + a - 1) * cexp (-((Real.pi : ℝ) * (y : ℂ) ^ 2))),
    integral_Ioi_cpow_mul_gaussian Real.pi_pos hw, Gammaℝ_def]
  · ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    simp only
    rw [cpow_sub _ _ hy0, cpow_one, cpow_add _ _ hy0, cpow_add _ _ hy0, ← ha', cpow_natCast]
    ring

/-- The zeta integral of the standard test function at a complex place: for $\mathrm{Re}(s + t) > 0$, $Z(f_n, (z / |z|)^n |z|_\mathbb{C}^t, s) = \pi \, \Gamma_\mathbb{C}(s + t + |n| / 2)$. -/
theorem complexZeta_complexTest (n : ℤ) {t s : ℂ} (h : 0 < (s + t).re) :
    complexZeta (complexTest n) n t s = Real.pi * Gammaℂ (s + t + ((|n| : ℤ) : ℂ) / 2) := by
  have hpt : ∀ z : ℂ, 2 * (complexTest n z * archChar 2 n t z * (‖z‖ : ℂ) ^ (2 * s) /
      (‖z‖ : ℂ) ^ 2) =
      2 * ((‖z‖ : ℂ) ^ n.natAbs * cexp (-((2 * Real.pi : ℝ) * (‖z‖ : ℂ) ^ 2)) *
        (‖z‖ : ℂ) ^ ((2 : ℂ) * t) * (‖z‖ : ℂ) ^ (2 * s) / (‖z‖ : ℂ) ^ 2) := by
    intro z
    rw [complexTest_mul_archChar]
  have habs : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [complexZeta, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_complex_radial (fun y : ℝ => 2 * ((y : ℂ) ^ n.natAbs *
      cexp (-((2 * Real.pi : ℝ) * (y : ℂ) ^ 2)) * (y : ℂ) ^ ((2 : ℂ) * t) * (y : ℂ) ^ (2 * s) /
        (y : ℂ) ^ 2))]
  have hw : 0 < (2 * (s + t) + n.natAbs).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, natCast_re]
    have : (0 : ℝ) ≤ n.natAbs := Nat.cast_nonneg _
    simp only [add_re, zero_mul, sub_zero] at h ⊢
    nlinarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    2 * ((y : ℂ) ^ (2 * (s + t) + n.natAbs - 1) * cexp (-((2 * Real.pi : ℝ) * (y : ℂ) ^ 2)))),
    integral_const_mul, integral_Ioi_cpow_mul_gaussian (by positivity) hw, Gammaℂ_def, habs]
  · have e : (2 * (s + t) + (n.natAbs : ℂ)) / 2 = s + t + (n.natAbs : ℂ) / 2 := by ring
    have e' : -(2 * (s + t) + (n.natAbs : ℂ)) / 2 = -(s + t + (n.natAbs : ℂ) / 2) := by ring
    rw [e, e']
    push_cast
    ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    simp only
    rw [cpow_sub _ _ hy0, cpow_one, cpow_add _ _ hy0, cpow_natCast, mul_add,
      cpow_add _ _ hy0]
    field_simp

end Langlands.Tate
