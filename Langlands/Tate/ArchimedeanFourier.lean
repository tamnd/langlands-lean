/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.ArchimedeanGamma
import Langlands.Tate.ArchimedeanZeta
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier transforms and the local functional equation at the archimedean places

This file contains the second half of the archimedean local theory of Tate's thesis: the Fourier transforms of the standard test functions and the local functional equation for them.

## Conventions

The additive character of $\mathbb{R}$ is $\psi_\mathbb{R}(x) = e^{-2 \pi i x}$ (`Langlands.Tate.psiReal`). This is the character of Tate's thesis at the real place, and it gives the Fourier transform of Mathlib. The additive character of $\mathbb{C}$ is $\psi_\mathbb{C}(z) = \psi_\mathbb{R}(2 \mathrm{Re}(z))$ (`Langlands.Tate.psiComplex`), that is $\psi_\mathbb{R} \circ \mathrm{Tr}_{\mathbb{C}/\mathbb{R}}$. The Fourier transform is $\hat f(y) = \int f(x) \psi(x y) \, dx$, with the self-dual measure: $dx$ on $\mathbb{R}$ and $2\, dx\, dy$ on $\mathbb{C}$ (`Langlands.Tate.realFourier` and `Langlands.Tate.complexFourier`). In terms of the Fourier transform $\mathcal{F}$ of Mathlib, $\hat f = \mathcal{F} f$ on $\mathbb{R}$ and $\hat f(w) = 2 \mathcal{F} f(2 \bar w)$ on $\mathbb{C}$.

## Main results

* `Langlands.Tate.realFourier_realTest`: $\hat f_a = (-i)^a f_a$ for $f_a(x) = x^a e^{-\pi x^2}$ and $a \in \{0, 1\}$.
* `Langlands.Tate.complexFourier_complexTest`: $\hat f_n = (-i)^{|n|} f_{-n}$, where $f_n(z) = \bar z^n e^{-2 \pi |z|^2}$ for $n \geq 0$ and $f_n(z) = z^{|n|} e^{-2 \pi |z|^2}$ for $n < 0$. So the Fourier transform of the standard function of $\chi$ is a multiple of the standard function of $\chi^{-1}$.
* `Langlands.Tate.real_local_functional_equation`: for $a \in \{0, 1\}$ and $0 < \mathrm{Re}(s + t) < 1$, $$Z(\hat f_a, \chi^{-1}, 1 - s) = \varepsilon \, \frac{\Gamma_\mathbb{R}(1 - s - t + a)}{\Gamma_\mathbb{R}(s + t + a)} \, Z(f_a, \chi, s), \qquad \chi = \mathrm{sgn}^a |\cdot|^t,$$ with the root number $\varepsilon = (-i)^a$ (`Langlands.Tate.realRootNumber`).
* `Langlands.Tate.complex_local_functional_equation`: for $n \in \mathbb{Z}$ and $0 < \mathrm{Re}(s + t) < 1$, $$Z(\hat f_n, \chi^{-1}, 1 - s) = \varepsilon \, \frac{\Gamma_\mathbb{C}(1 - s - t + |n| / 2)}{\Gamma_\mathbb{C}(s + t + |n| / 2)} \, Z(f_n, \chi, s), \qquad \chi = (z / |z|)^n |z|_\mathbb{C}^t,$$ with the root number $\varepsilon = (-i)^{|n|}$ (`Langlands.Tate.complexRootNumber`).
* `Langlands.Tate.norm_realRootNumber` and `Langlands.Tate.norm_complexRootNumber`: the root numbers have absolute value one.

## Proofs

The Fourier transform of a Gaussian is in Mathlib (`fourier_gaussian_pi` and `fourier_gaussian_innerProductSpace`). For the other functions we use that the Fourier transform turns multiplication by a coordinate into a derivative (`Real.hasDerivAt_fourier` and `Real.hasFDerivAt_fourier`). On $\mathbb{R}$, $\widehat{x f_0} = \frac{1}{-2 \pi i} (\hat f_0)'$, and this gives $\hat f_1 = -i f_1$. On $\mathbb{C}$ write $\bar z = \langle z, 1 \rangle - i \langle z, i \rangle$ with the real inner product. Then the transform of $\bar z g(z)$ is $\frac{1}{-2 \pi i}(\partial_1 - i \partial_2) \mathcal{F} g$. The operator $\partial_1 - i \partial_2$ kills the antiholomorphic factor $\bar v^k$ and multiplies the Gaussian $e^{-\pi |v|^2 / 2}$ by $-\pi \bar v$. An induction on $k$ gives $\mathcal{F}(\bar z^k e^{-2 \pi |z|^2})(v) = \frac{1}{2} (-i/2)^k \bar v^k e^{-\pi |v|^2 / 2}$ (`Langlands.Tate.fourier_gaussConj`). The case $z^k$ follows by complex conjugation.

The local functional equation then follows from the values of the zeta integrals in `Langlands.Tate.ArchimedeanZeta`. The quasi-character $\chi^{-1}$ has the parameters $(a, -t)$ at a real place and $(-n, -t)$ at a complex place.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.5.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.1.
-/

namespace Langlands.Tate

open Complex MeasureTheory Set Module FourierTransform

/-- The additive character $\psi_\mathbb{R}(x) = e^{-2 \pi i x}$ of $\mathbb{R}$. -/
noncomputable def psiReal (x : ℝ) : ℂ :=
  cexp (((-2 * Real.pi * x : ℝ) : ℂ) * I)

/-- The additive character $\psi_\mathbb{C}(z) = \psi_\mathbb{R}(2 \mathrm{Re}(z))$ of $\mathbb{C}$. -/
noncomputable def psiComplex (z : ℂ) : ℂ :=
  psiReal (2 * z.re)

/-- The Fourier transform at a real place: $\hat f(y) = \int_\mathbb{R} f(x) \psi_\mathbb{R}(x y) \, dx$. -/
noncomputable def realFourier (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f x * psiReal (x * y)

/-- The Fourier transform at a complex place: $\hat f(w) = \int_\mathbb{C} f(z) \psi_\mathbb{C}(z w) \, 2\, dx\, dy$. -/
noncomputable def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, 2 * (f z * psiComplex (z * w))

/-- The local root number at a real place, for $\chi = \mathrm{sgn}^a |\cdot|^t$: $\varepsilon = (-i)^a$. -/
noncomputable def realRootNumber (a : ℤ) : ℂ :=
  (-I) ^ a.toNat

/-- The local root number at a complex place, for $\chi = (z / |z|)^n |z|_\mathbb{C}^t$: $\varepsilon = (-i)^{|n|}$. -/
noncomputable def complexRootNumber (n : ℤ) : ℂ :=
  (-I) ^ n.natAbs

/-- The local root number at a real place has absolute value one. -/
theorem norm_realRootNumber (a : ℤ) : ‖realRootNumber a‖ = 1 := by
  simp [realRootNumber]

/-- The local root number at a complex place has absolute value one. -/
theorem norm_complexRootNumber (n : ℤ) : ‖complexRootNumber n‖ = 1 := by
  simp [complexRootNumber]

/-- The real Fourier transform is the Fourier transform of Mathlib. -/
theorem realFourier_eq_fourier (f : ℝ → ℂ) : realFourier f = 𝓕 f := by
  ext y
  rw [Real.fourier_real_eq_integral_exp_smul, realFourier]
  congr 1
  ext x
  simp only [psiReal, smul_eq_mul]
  ring_nf

/-- The complex Fourier transform in terms of the Fourier transform of Mathlib on the real inner product space $\mathbb{C}$: $\hat f(w) = 2 \mathcal{F} f(2 \bar w)$. -/
theorem complexFourier_eq_fourier (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = 2 * 𝓕 f (2 * starRingEnd ℂ w) := by
  have key (z : ℂ) : inner ℝ z (2 * starRingEnd ℂ w) = 2 * (z * w).re := by
    rw [Complex.inner]
    simp only [mul_re, re_ofNat, conj_re, im_ofNat, conj_im, zero_mul, sub_zero, mul_im]
    ring
  rw [Real.fourier_eq', complexFourier, ← integral_const_mul]
  congr 1
  ext z
  simp only [psiComplex, psiReal, smul_eq_mul, key]
  ring_nf

/-! ### Linearity -/

/-- The real zeta integral is linear in the test function. -/
theorem realZeta_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) (t s : ℂ) :
    realZeta (fun x => c * f x) n t s = c * realZeta f n t s := by
  rw [realZeta, realZeta, ← integral_const_mul]
  congr 1
  ext x
  ring

/-- The complex zeta integral is linear in the test function. -/
theorem complexZeta_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℤ) (t s : ℂ) :
    complexZeta (fun z => c * f z) n t s = c * complexZeta f n t s := by
  rw [complexZeta, complexZeta, ← integral_const_mul]
  congr 1
  ext z
  ring

/-- The Fourier transform of Mathlib on $\mathbb{C}$ is linear on integrable functions. -/
theorem fourier_add_mul {f g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g) (a b : ℂ) (v : ℂ) :
    𝓕 (fun x => a * f x + b * g x) v = a * 𝓕 f v + b * 𝓕 g v := by
  have hf' := (Real.fourierIntegral_convergent_iff (μ := volume) v).2 hf
  have hg' := (Real.fourierIntegral_convergent_iff (μ := volume) v).2 hg
  simp only [Real.fourier_eq]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hf'.const_mul a) (hg'.const_mul b)]
  congr 1
  ext x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-! ### The real place -/

/-- The function $f_0$ is the Gaussian $e^{-\pi x^2}$ in the form of Mathlib. -/
theorem realTest_zero_eq : realTest 0 = fun x : ℝ => cexp (-Real.pi * 1 * (x : ℂ) ^ 2) := by
  ext x
  simp [realTest]

/-- The Fourier transform of $f_0(x) = e^{-\pi x^2}$ is $f_0$. -/
theorem realFourier_realTest_zero : realFourier (realTest 0) = realTest 0 := by
  rw [realFourier_eq_fourier, realTest_zero_eq, fourier_gaussian_pi (by simp)]
  ext t
  simp

/-- The Fourier transform of $f_1(x) = x e^{-\pi x^2}$ is $-i f_1$. -/
theorem realFourier_realTest_one : realFourier (realTest 1) = fun y => -I * realTest 1 y := by
  have hg : Integrable (realTest 0) := by
    rw [realTest_zero_eq]
    simpa using integrable_cexp_neg_mul_sq (b := (Real.pi : ℂ)) (by simp [Real.pi_pos])
  have hg' : Integrable (fun x : ℝ => x • realTest 0 x) := by
    simpa [realTest, Complex.real_smul] using
      integrable_mul_cexp_neg_mul_sq (b := (Real.pi : ℂ)) (by simp [Real.pi_pos])
  ext y
  have hd := Real.hasDerivAt_fourier hg hg' y
  rw [← realFourier_eq_fourier (realTest 0), realFourier_realTest_zero] at hd
  have hd2 : HasDerivAt (realTest 0) (-(2 * Real.pi * y) * realTest 0 y) y := by
    have h1 := (((hasDerivAt_id' y).ofReal_comp.pow 2).const_mul (Real.pi : ℂ)).neg.cexp
    convert h1 using 1
    · ext x
      simp [realTest]
    · simp [realTest]
      ring
  have h3 := hd.unique hd2
  have hlin : 𝓕 (fun x : ℝ => (-2 * Real.pi * I * x) • realTest 0 x) y =
      (-2 * Real.pi * I) * realFourier (realTest 1) y := by
    rw [← realFourier_eq_fourier, realFourier, realFourier, ← integral_const_mul]
    congr 1
    ext x
    simp only [realTest, smul_eq_mul, Int.toNat_zero, pow_zero, one_mul, Int.toNat_one, pow_one]
    ring
  rw [hlin] at h3
  have hne : (-2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply mul_left_cancel₀ hne
  rw [h3]
  simp only [realTest, Int.toNat_zero, pow_zero, one_mul, Int.toNat_one, pow_one]
  linear_combination (-2 * Real.pi * y * cexp (-(Real.pi * (y : ℂ) ^ 2))) * I_sq

/-- The Fourier transform of the standard test function at a real place: $\hat f_a = (-i)^a f_a$ for $a \in \{0, 1\}$. -/
theorem realFourier_realTest {a : ℤ} (ha : a = 0 ∨ a = 1) :
    realFourier (realTest a) = fun y => realRootNumber a * realTest a y := by
  rcases ha with rfl | rfl
  · rw [realFourier_realTest_zero]
    ext y
    simp [realRootNumber]
  · rw [realFourier_realTest_one]
    ext y
    simp [realRootNumber]

/-- The zeta integral of $\hat f_a$ for the quasi-character $\chi^{-1} = \mathrm{sgn}^a |\cdot|^{-t}$ at $1 - s$, for $\mathrm{Re}(s + t) < 1$. -/
theorem realZeta_realFourier_realTest {a : ℤ} (ha : a = 0 ∨ a = 1) {t s : ℂ}
    (h : (s + t).re < 1) :
    realZeta (realFourier (realTest a)) a (-t) (1 - s) =
      realRootNumber a * Gammaℝ (1 - s - t + a) := by
  rw [realFourier_realTest ha, realZeta_const_mul,
    realZeta_realTest ha (by simp only [add_re, sub_re, one_re, neg_re] at h ⊢; linarith)]
  ring_nf

/-- The local functional equation at a real place for the standard test function: for $a \in \{0, 1\}$, $\chi = \mathrm{sgn}^a |\cdot|^t$ and $0 < \mathrm{Re}(s + t) < 1$, $$Z(\hat f_a, \chi^{-1}, 1 - s) = (-i)^a \frac{\Gamma_\mathbb{R}(1 - s - t + a)}{\Gamma_\mathbb{R}(s + t + a)} Z(f_a, \chi, s).$$ -/
theorem real_local_functional_equation {a : ℤ} (ha : a = 0 ∨ a = 1) {t s : ℂ}
    (h0 : 0 < (s + t).re) (h1 : (s + t).re < 1) :
    realZeta (realFourier (realTest a)) a (-t) (1 - s) =
      realRootNumber a * (Gammaℝ (1 - s - t + a) / Gammaℝ (s + t + a)) *
        realZeta (realTest a) a t s := by
  have hne : Gammaℝ (s + t + a) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [add_re] at h0 ⊢
    rcases ha with rfl | rfl <;> simp <;> linarith
  rw [realZeta_realFourier_realTest ha h1, realZeta_realTest ha h0]
  field_simp

/-! ### The complex place -/

/-- The function $\bar z^k e^{-2 \pi |z|^2}$ on $\mathbb{C}$. -/
noncomputable def gaussConj (k : ℕ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ z) ^ k * cexp (-((2 * Real.pi : ℝ) * (‖z‖ : ℂ) ^ 2))

/-- The function $z^k e^{-2 \pi |z|^2}$ on $\mathbb{C}$. -/
noncomputable def gaussHol (k : ℕ) (z : ℂ) : ℂ :=
  z ^ k * cexp (-((2 * Real.pi : ℝ) * (‖z‖ : ℂ) ^ 2))

/-- The Fourier transform of `gaussConj k` for the Fourier transform of Mathlib: $v \mapsto \frac{1}{2} (-i/2)^k \bar v^k e^{-\pi |v|^2 / 2}$. -/
noncomputable def fourierGaussConj (k : ℕ) (v : ℂ) : ℂ :=
  1 / 2 * (-I / 2) ^ k * (starRingEnd ℂ v) ^ k * cexp (((-(Real.pi / 2 * ‖v‖ ^ 2) : ℝ) : ℂ))

/-- The function $\bar z^k e^{-2 \pi |z|^2}$ is continuous. -/
theorem continuous_gaussConj (k : ℕ) : Continuous (gaussConj k) := by
  unfold gaussConj
  fun_prop

/-- The absolute value of $\bar z^k e^{-2 \pi |z|^2}$ is $|z|^k e^{-2 \pi |z|^2}$. -/
theorem norm_gaussConj (k : ℕ) (z : ℂ) :
    ‖gaussConj k z‖ = ‖z‖ ^ k * Real.exp (-(2 * Real.pi) * ‖z‖ ^ 2) := by
  rw [gaussConj, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp, ← ofReal_pow,
    ← ofReal_mul, ← ofReal_neg, ofReal_re]
  ring_nf

/-- The function $|z|^j e^{-2 \pi |z|^2}$ is integrable on $\mathbb{C}$. -/
theorem integrable_norm_pow_mul_gauss (j : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ j * Real.exp (-(2 * Real.pi) * ‖z‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar volume
    (f := fun y : ℝ => y ^ j * Real.exp (-(2 * Real.pi) * y ^ 2))]
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * Real.pi) (by positivity)
    (s := (j + 1 : ℝ)) (by have := j.cast_nonneg (α := ℝ); linarith)
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp only [Complex.finrank_real_complex, Nat.add_one_sub_one, pow_one, smul_eq_mul]
  rw [Real.rpow_add hy, Real.rpow_natCast, Real.rpow_one]
  ring

/-- The function $\bar z^k e^{-2 \pi |z|^2}$ is integrable on $\mathbb{C}$. -/
theorem integrable_gaussConj (k : ℕ) : Integrable (gaussConj k) :=
  (integrable_norm_pow_mul_gauss k).mono' (continuous_gaussConj k).aestronglyMeasurable
    (ae_of_all _ fun z => (norm_gaussConj k z).le)

/-- The function $|z| \cdot |\bar z^k e^{-2 \pi |z|^2}|$ is integrable on $\mathbb{C}$. -/
theorem integrable_norm_mul_gaussConj (k : ℕ) :
    Integrable (fun v : ℂ => ‖v‖ * ‖gaussConj k v‖) := by
  refine (integrable_norm_pow_mul_gauss (k + 1)).congr (ae_of_all _ fun z => ?_)
  simp only [norm_gaussConj, pow_succ]
  ring

/-- The function $c \langle z, u \rangle \bar z^k e^{-2 \pi |z|^2}$ is integrable on $\mathbb{C}$. -/
theorem integrable_inner_mul_gaussConj (k : ℕ) (c u : ℂ) :
    Integrable (fun x : ℂ => c * ((inner ℝ x u : ℝ) : ℂ) * gaussConj k x) := by
  refine ((integrable_norm_mul_gaussConj k).const_mul (‖c‖ * ‖u‖)).mono' ?_
    (ae_of_all _ fun x => ?_)
  · exact (by unfold gaussConj; fun_prop : Continuous _).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_real_inner_le_norm x u
    have h0 := norm_nonneg (gaussConj k x)
    have h1 := norm_nonneg c
    calc ‖c‖ * |inner ℝ x u| * ‖gaussConj k x‖ ≤ ‖c‖ * (‖x‖ * ‖u‖) * ‖gaussConj k x‖ := by
          gcongr
      _ = ‖c‖ * ‖u‖ * (‖x‖ * ‖gaussConj k x‖) := by ring

/-- The derivative of `fourierGaussConj k` along the line $\varepsilon \mapsto v + \varepsilon u$. -/
theorem hasDerivAt_fourierGaussConj_line (k : ℕ) (v u : ℂ) :
    HasDerivAt (fun ε : ℝ => fourierGaussConj k (v + ε • u))
      (1 / 2 * (-I / 2) ^ k * ((k : ℂ) * (starRingEnd ℂ v) ^ (k - 1) * starRingEnd ℂ u *
        cexp (((-(Real.pi / 2 * ‖v‖ ^ 2) : ℝ) : ℂ)) + (starRingEnd ℂ v) ^ k *
          (cexp (((-(Real.pi / 2 * ‖v‖ ^ 2) : ℝ) : ℂ)) *
            ((-(Real.pi / 2 * (2 * inner ℝ v u)) : ℝ) : ℂ)))) 0 := by
  have hl : HasDerivAt (fun ε : ℝ => v + ε • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add v
  have hc : HasDerivAt (fun ε : ℝ => starRingEnd ℂ (v + ε • u)) (starRingEnd ℂ u) 0 := hl.star
  have hn := ((hl.norm_sq.const_mul (Real.pi / 2)).neg).ofReal_comp.cexp
  have hp := ((hc.pow k).const_mul (1 / 2 * (-I / 2) ^ k)).mul hn
  convert hp using 1
  · ext ε
    simp only [fourierGaussConj, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply]
  · simp only [Pi.pow_apply, Pi.neg_apply, zero_smul, add_zero]
    ring

/-- The Fourier transform of $\bar z^k e^{-2 \pi |z|^2}$ for the Fourier transform of Mathlib is $\frac{1}{2} (-i/2)^k \bar v^k e^{-\pi |v|^2 / 2}$. -/
theorem fourier_gaussConj (k : ℕ) : 𝓕 (gaussConj k) = fourierGaussConj k := by
  induction k with
  | zero =>
    ext v
    have e : gaussConj 0 = fun z : ℂ => cexp (-((2 * Real.pi : ℝ) : ℂ) * (‖z‖ : ℂ) ^ 2) := by
      ext z
      simp [gaussConj]
    rw [e, fourier_gaussian_innerProductSpace (by simp [Real.pi_pos]), fourierGaussConj]
    simp only [Complex.finrank_real_complex, pow_zero, mul_one]
    have h1 : (Real.pi : ℂ) / ((2 * Real.pi : ℝ) : ℂ) = 1 / 2 := by
      push_cast
      field_simp
    have h2 : (((2 : ℕ) : ℂ) / 2) = 1 := by norm_num
    rw [h1, h2, cpow_one]
    congr 2
    push_cast
    field_simp
  | succ k ih =>
    ext v
    have hF := Real.hasFDerivAt_fourier (integrable_gaussConj k) (integrable_norm_mul_gaussConj k) v
    rw [ih] at hF
    have hl (u : ℂ) : HasDerivAt (fun ε : ℝ => v + ε • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add v
    have hD (u : ℂ) := (hF.comp_hasDerivAt_of_eq (0 : ℝ) (hl u) (by simp)).unique
      (hasDerivAt_fourierGaussConj_line k v u)
    have hint : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) (gaussConj k)) := by
      refine ((integrable_norm_mul_gaussConj k).const_mul
        (2 * Real.pi * ‖innerSL ℝ (E := ℂ)‖)).mono'
        (integrable_gaussConj k).1.fourierSMulRight (ae_of_all _ fun x => ?_)
      have := VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) (gaussConj k) x
      linarith
    have hD' (u : ℂ) : 𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) (gaussConj k)) v u =
        𝓕 (fun x => -(2 * Real.pi * I) * ((inner ℝ x u : ℝ) : ℂ) * gaussConj k x) v := by
      rw [Real.fourier_continuousLinearMap_apply hint]
      refine congrArg (fun F : ℂ → ℂ => 𝓕 F v) (funext fun x => ?_)
      simp only [VectorFourier.fourierSMulRight_apply, Complex.real_smul, smul_eq_mul]
      rw [show (innerSL ℝ x u : ℝ) = inner ℝ x u from rfl]
      ring
    have hfun : gaussConj (k + 1) = fun x => 1 / (-(2 * Real.pi * I)) *
        (-(2 * Real.pi * I) * ((inner ℝ x 1 : ℝ) : ℂ) * gaussConj k x) +
          (-I / (-(2 * Real.pi * I))) *
            (-(2 * Real.pi * I) * ((inner ℝ x I : ℝ) : ℂ) * gaussConj k x) := by
      ext x
      have hx : starRingEnd ℂ x = (x.re : ℂ) - I * x.im := by
        apply Complex.ext <;> simp
      have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      simp only [gaussConj, Complex.inner, pow_succ]
      simp only [mul_re, I_re, I_im, conj_re, conj_im, zero_mul, one_mul, mul_neg, neg_neg,
        zero_sub]
      rw [hx]
      field_simp
      ring
    rw [hfun, fourier_add_mul (integrable_inner_mul_gaussConj k _ _)
      (integrable_inner_mul_gaussConj k _ _), ← hD', ← hD', hD, hD]
    have hv : starRingEnd ℂ v = (v.re : ℂ) - I * v.im := by
      apply Complex.ext <;> simp
    have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simp only [fourierGaussConj, Complex.inner, mul_one, map_one, conj_I, pow_succ, mul_re,
      I_re, I_im, conj_re, conj_im, zero_mul, one_mul, mul_neg, neg_neg, zero_sub]
    rw [hv]
    push_cast
    field_simp
    linear_combination (-(k : ℂ) * ((v.re : ℂ) - I * v.im) ^ (k - 1) +
      Real.pi * ((v.re : ℂ) - I * v.im) ^ k * (v.re - I * v.im)) * I_sq

/-- The function $z^k e^{-2 \pi |z|^2}$ is the function $\bar z^k e^{-2 \pi |z|^2}$ composed with complex conjugation. -/
theorem gaussHol_eq_comp (k : ℕ) : gaussHol k = gaussConj k ∘ Complex.conjLIE := by
  ext z
  simp [gaussHol, gaussConj]

/-- The Fourier transform of $z^k e^{-2 \pi |z|^2}$ for the Fourier transform of Mathlib is $\frac{1}{2} (-i/2)^k v^k e^{-\pi |v|^2 / 2}$. -/
theorem fourier_gaussHol (k : ℕ) (v : ℂ) :
    𝓕 (gaussHol k) v =
      1 / 2 * (-I / 2) ^ k * v ^ k * cexp (((-(Real.pi / 2 * ‖v‖ ^ 2) : ℝ) : ℂ)) := by
  rw [gaussHol_eq_comp, Real.fourier_comp_linearIsometry, fourier_gaussConj, fourierGaussConj]
  simp

/-- The self-dual Fourier transform of $\bar z^k e^{-2 \pi |z|^2}$ is $(-i)^k z^k e^{-2 \pi |z|^2}$. -/
theorem complexFourier_gaussConj (k : ℕ) :
    complexFourier (gaussConj k) = fun w => (-I) ^ k * gaussHol k w := by
  ext w
  rw [complexFourier_eq_fourier, fourier_gaussConj, fourierGaussConj, gaussHol]
  have hn : ‖2 * starRingEnd ℂ w‖ = 2 * ‖w‖ := by simp
  rw [hn, map_mul, Complex.conj_conj, map_ofNat]
  push_cast
  rw [mul_pow, div_pow]
  field_simp

/-- The self-dual Fourier transform of $z^k e^{-2 \pi |z|^2}$ is $(-i)^k \bar z^k e^{-2 \pi |z|^2}$. -/
theorem complexFourier_gaussHol (k : ℕ) :
    complexFourier (gaussHol k) = fun w => (-I) ^ k * gaussConj k w := by
  ext w
  rw [complexFourier_eq_fourier, fourier_gaussHol, gaussConj]
  have hn : ‖2 * starRingEnd ℂ w‖ = 2 * ‖w‖ := by simp
  rw [hn]
  push_cast
  rw [mul_pow, div_pow]
  field_simp

/-- The standard test function at a complex place in terms of `gaussConj` and `gaussHol`. -/
theorem complexTest_eq (n : ℤ) :
    complexTest n = if 0 ≤ n then gaussConj n.natAbs else gaussHol n.natAbs := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    ext z
    simp [complexTest, gaussConj]
  · ext z
    simp [complexTest, gaussHol, h]

/-- The Fourier transform of the standard test function at a complex place: $\hat f_n = (-i)^{|n|} f_{-n}$. So it is the root number times the standard test function of $\chi^{-1}$. -/
theorem complexFourier_complexTest (n : ℤ) :
    complexFourier (complexTest n) = fun w => complexRootNumber n * complexTest (-n) w := by
  rw [complexTest_eq, complexTest_eq, complexRootNumber, Int.natAbs_neg]
  rcases lt_trichotomy n 0 with h | rfl | h
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), complexFourier_gaussHol]
  · ext w
    simp [complexFourier_gaussConj, gaussHol, gaussConj]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), complexFourier_gaussConj]

/-- The zeta integral of $\hat f_n$ for the quasi-character $\chi^{-1} = (z / |z|)^{-n} |z|_\mathbb{C}^{-t}$ at $1 - s$, for $\mathrm{Re}(s + t) < 1$. -/
theorem complexZeta_complexFourier_complexTest (n : ℤ) {t s : ℂ} (h : (s + t).re < 1) :
    complexZeta (complexFourier (complexTest n)) (-n) (-t) (1 - s) =
      complexRootNumber n * (Real.pi * Gammaℂ (1 - s - t + ((|n| : ℤ) : ℂ) / 2)) := by
  rw [complexFourier_complexTest, complexZeta_const_mul, complexZeta_complexTest (-n)
    (by simp only [add_re, sub_re, one_re, neg_re] at h ⊢; linarith), abs_neg]
  ring_nf

/-- The local functional equation at a complex place for the standard test function: for $n \in \mathbb{Z}$, $\chi = (z / |z|)^n |z|_\mathbb{C}^t$ and $0 < \mathrm{Re}(s + t) < 1$, $$Z(\hat f_n, \chi^{-1}, 1 - s) = (-i)^{|n|} \frac{\Gamma_\mathbb{C}(1 - s - t + |n| / 2)}{\Gamma_\mathbb{C}(s + t + |n| / 2)} Z(f_n, \chi, s).$$ -/
theorem complex_local_functional_equation (n : ℤ) {t s : ℂ} (h0 : 0 < (s + t).re)
    (h1 : (s + t).re < 1) :
    complexZeta (complexFourier (complexTest n)) (-n) (-t) (1 - s) =
      complexRootNumber n * (Gammaℂ (1 - s - t + ((|n| : ℤ) : ℂ) / 2) /
        Gammaℂ (s + t + ((|n| : ℤ) : ℂ) / 2)) * complexZeta (complexTest n) n t s := by
  have hne : Gammaℂ (s + t + ((|n| : ℤ) : ℂ) / 2) ≠ 0 := by
    apply Gammaℂ_ne_zero_of_re_pos
    rw [← Int.natCast_natAbs, Int.cast_natCast, add_re]
    have : (((n.natAbs : ℕ) : ℂ) / 2).re = (n.natAbs : ℝ) / 2 := by simp
    rw [this]
    positivity
  rw [complexZeta_complexFourier_complexTest n h1, complexZeta_complexTest n h0]
  generalize Gammaℂ (s + t + ((|n| : ℤ) : ℂ) / 2) = G at hne ⊢
  field_simp

end Langlands.Tate
