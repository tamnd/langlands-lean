/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.NonArchimedeanGauss

/-!
# The local functional equation at a finite place

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$, uniformizer $\varpi$ and residue field of size $q = N(v)$. We use the additive measure $dx$ with $\int_{\mathcal{O}_v} dx = 1$ and the multiplicative measure $d^\times x = (1 - q^{-1})^{-1} |x|_v^{-1} dx$, as in `Langlands.Tate.NonArchimedeanMeasure`. Let $\psi$ be an additive character of conductor exponent $d$, so $\psi$ is trivial on $\{|x|_v \leq q^d\}$ and not on $\{|x|_v \leq q^{d+1}\}$. The Fourier transform is $\hat{f}(y) = \int f(x) \psi(x y) \, dx$.

For a character $\chi$ of $K_v^\times$ and a test function $f$ the local zeta integral is
$$Z(f, \chi, s) = \int_{K_v^\times} f(x) \chi(x) |x|_v^s \, d^\times x.$$
Tate's local functional equation says that
$$Z(\hat{f}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) \frac{L(1 - s, \chi^{-1})}{L(s, \chi)} Z(f, \chi, s),$$
where $\varepsilon(s, \chi, \psi)$ does not depend on $f$. This file proves the equation for the standard test functions, and it computes $\varepsilon$.

## The unramified case

Let $\chi$ be trivial on $\mathcal{O}_v^\times$ and let $f = \mathbf{1}_{\mathcal{O}_v}$. Then $Z(f, \chi, s) = L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ by `zetaIntegral_unramified`. The transform is $\hat{f} = \mathbf{1}_{\{|y|_v \leq q^d\}}$. Put $c = \varpi^{-d}$, so $|c|_v = q^d$ and $\hat{f}(y) = f(c^{-1} y)$. The substitution $y = c x$ gives
$$Z(\hat{f}, \chi^{-1}, 1 - s) = \chi(c)^{-1} |c|_v^{1-s} L(1 - s, \chi^{-1}) = \chi(\varpi)^d q^{d(1-s)} L(1 - s, \chi^{-1}).$$
So $\varepsilon(s, \chi, \psi) = \chi(\varpi)^d q^{d(1-s)}$. We write this as $\chi(\varpi)^d q^{d(1/2 - s)} \cdot q^{d/2}$. The first two factors are the usual root number for the self dual measure $q^{-d/2} dx$. The last factor $q^{d/2}$ comes from our normalization of $dx$: with $\mu(\mathcal{O}_v) = 1$ the measure is $q^{d/2}$ times the self dual measure. If $d = 0$ the two measures agree and $\varepsilon = 1$.

## The ramified case

Let $\chi$ have conductor exponent $a = b + 1 \geq 1$, so $\chi$ is trivial on $1 + \mathfrak{p}_v^a$ but not on $1 + \mathfrak{p}_v^b$. Then $L(s, \chi) = 1$. We take Tate's test function $f = \mathbf{1}_{1 + \mathfrak{p}_v^a}$. On its support $\chi = 1$ and $|x|_v = 1$, so
$$Z(f, \chi, s) = \int_{1 + \mathfrak{p}_v^a} d^\times x = (1 - q^{-1})^{-1} q^{-a}.$$
The transform is $\hat{f}(y) = \psi(y) q^{-a} \mathbf{1}_{\{|y|_v \leq q^{d + a}\}}(y)$, because $1 + \mathfrak{p}_v^a$ is a translate of the ball $\mathfrak{p}_v^a$. Choose $c$ with $|c|_v = q^{d + a}$ and substitute $y = c x$. The integral over $|x|_v < 1$ vanishes: if $w \in 1 + \mathfrak{p}_v^b$ and $|x|_v < 1$, then $\psi(c w x) = \psi(c x)$, so the integrand $h$ satisfies $h(w x) = \chi(w)^{-1} h(x)$, and we can choose $w$ with $\chi(w) \neq 1$. On $|x|_v = 1$ the measure $d^\times x$ is $(1 - q^{-1})^{-1} dx$. The result is
$$Z(\hat{f}, \chi^{-1}, 1 - s) = \chi(c)^{-1} |c|_v^{1 - s} G(\chi^{-1}, \psi, c) \, Z(f, \chi, s),$$
with the Gauss sum $G(\chi^{-1}, \psi, c) = \int_{\mathcal{O}_v^\times} \chi^{-1}(u) \psi(c u) \, du$ of `Langlands.Tate.NonArchimedeanGauss`. So $\varepsilon(s, \chi, \psi) = \chi(c)^{-1} |c|_v^{1 - s} G(\chi^{-1}, \psi, c)$, and $|G(\chi^{-1}, \psi, c)|^2 = q^{-a}$.

The integral over $|x|_v < 1$ is split off with `setIntegral_sdiff`, so we need the integrand to be integrable there. This holds when $|\chi^{-1}(\varpi)| < q^{\mathrm{Re}(1 - s)}$, which is the usual region of convergence. Outside this region the Bochner integral is $0$ by convention, and the formula is not true as stated.

## Main results

* `zetaIntegral_fourier_integers`: the unramified computation of $Z(\hat{\mathbf{1}}_{\mathcal{O}_v}, \chi^{-1}, 1 - s)$.
* `localFunctionalEquation_unramified`: $Z(\hat{f}, \chi^{-1}, 1 - s) L(s, \chi) = \varepsilon L(1 - s, \chi^{-1}) Z(f, \chi, s)$ for $f = \mathbf{1}_{\mathcal{O}_v}$.
* `epsilonUnramified_eq`: $\varepsilon = \chi(\varpi)^d q^{d(1/2 - s)} q^{d/2}$.
* `zetaIntegral_testFunction`: $Z(\mathbf{1}_{1 + \mathfrak{p}_v^a}, \chi, s) = (1 - q^{-1})^{-1} q^{-a}$.
* `fourier_testFunction`: the Fourier transform of $\mathbf{1}_{1 + \mathfrak{p}_v^a}$.
* `localFunctionalEquation_ramified`: $Z(\hat{f}, \chi^{-1}, 1 - s) = \varepsilon Z(f, \chi, s)$ for $f = \mathbf{1}_{1 + \mathfrak{p}_v^a}$.
* `norm_gaussSum_inv_sq` and `epsilonRamified_ne_zero`: the Gauss sum in $\varepsilon$ has $|G|^2 = q^{-a}$, and $\varepsilon \neq 0$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.4.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, chapter 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-! ### Preliminaries -/

/-- If $\chi$ is trivial on $1 + \mathfrak{p}_v^m$, then so is $\chi^{-1}$. -/
theorem isTrivialOnHigherUnits_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) : IsTrivialOnHigherUnits v χ⁻¹ m := by
  intro u hu hu1
  rw [MonoidHom.inv_apply, hχ u hu hu1, inv_one]

/-- The character $\chi$ is trivial on $1 + \mathfrak{p}_v^m$ if and only if $\chi^{-1}$ is. -/
theorem isTrivialOnHigherUnits_inv_iff {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ} :
    IsTrivialOnHigherUnits v χ⁻¹ m ↔ IsTrivialOnHigherUnits v χ m := by
  refine ⟨fun h u hu hu1 => ?_, isTrivialOnHigherUnits_inv v⟩
  have h' := h u hu hu1
  rwa [MonoidHom.inv_apply, inv_eq_one] at h'

/-- On a set where $|x|_v = 1$, the measure $d^\times x$ is $(1 - q^{-1})^{-1} dx$. -/
theorem multHaar_restrict_sphere :
    (multHaar v).restrict (sphere 0 1) =
      ENNReal.ofReal (1 - (q v)⁻¹)⁻¹ • (haar v).restrict (sphere 0 1) := by
  ext E hE
  rw [Measure.restrict_apply hE, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul,
    multHaar_apply_of_subset_sphere v (hE.inter isClosed_sphere.measurableSet)
      Set.inter_subset_right, inv_one, mul_one]

/-- The constant $(1 - q^{-1})^{-1}$ is positive. -/
theorem inv_one_sub_inv_q_pos : 0 < (1 - (q v)⁻¹)⁻¹ :=
  inv_pos.2 (sub_pos.2 (inv_q_lt_one v))

/-- The integral over $\mathcal{O}_v^\times$ for $d^\times x$ is $(1 - q^{-1})^{-1}$ times the integral for $dx$. -/
theorem setIntegral_sphere_multHaar (g : v.adicCompletion K → ℂ) :
    ∫ x in sphere 0 1, g x ∂multHaar v =
      (((1 - (q v)⁻¹)⁻¹ : ℝ) : ℂ) * ∫ x in sphere 0 1, g x ∂haar v := by
  rw [multHaar_restrict_sphere, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_one_sub_inv_q_pos v).le, Complex.real_smul]

/-- If $w x \in S \iff x \in S$ and $g(w x) = c g(x)$ on $S$ with $c \neq 1$, then $\int_S g \, d^\times x = 0$. -/
theorem setIntegral_multHaar_eq_zero_of_comp_mul {S : Set (v.adicCompletion K)}
    (hS : MeasurableSet S) (g : v.adicCompletion K → ℂ) {w : v.adicCompletion K} (hw : w ≠ 0)
    (hSw : ∀ x, w * x ∈ S ↔ x ∈ S) {c : ℂ} (hc : c ≠ 1) (hg : ∀ x ∈ S, g (w * x) = c * g x) :
    ∫ x in S, g x ∂multHaar v = 0 := by
  rw [← integral_indicator hS]
  refine integral_eq_zero_of_comp_mul v _ hw hc fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem ((hSw x).2 hx), Set.indicator_of_mem hx, hg x hx]
  · rw [Set.indicator_of_notMem (fun h => hx ((hSw x).1 h)), Set.indicator_of_notMem hx, mul_zero]

/-- The point $\varpi^{-d}$ has $|\varpi^{-d}|_v = q^d$. -/
theorem norm_localUniformizer_zpow_neg (d : ℤ) :
    ‖(localUniformizer K v : v.adicCompletion K) ^ (-d)‖ = q v ^ d := by
  rw [norm_zpow, norm_localUniformizer, inv_zpow', neg_neg]

/-- If $|c|_v = r > 0$, then $|c x|_v \leq r$ if and only if $|x|_v \leq 1$. -/
theorem norm_mul_le_norm_iff {c : v.adicCompletion K} (hc : c ≠ 0) (x : v.adicCompletion K) :
    ‖c * x‖ ≤ ‖c‖ ↔ ‖x‖ ≤ 1 := by
  rw [norm_mul, mul_le_iff_le_one_right (norm_pos_iff.2 hc)]

/-! ### The unramified case -/

/-- The local factor $L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ of an unramified character. -/
noncomputable def localFactor (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  (1 - χ (localUniformizer K v) * (q v : ℂ) ^ (-s))⁻¹

/-- The epsilon factor $\varepsilon(s, \chi, \psi) = \chi(\varpi)^d q^{d(1 - s)}$ of an unramified character, for $\psi$ of conductor exponent $d$ and the measure $dx$ with $\mu(\mathcal{O}_v) = 1$. -/
noncomputable def epsilonUnramified (χ : (v.adicCompletion K)ˣ →* ℂˣ) (d : ℤ) (s : ℂ) : ℂ :=
  (χ (localUniformizer K v) : ℂ) ^ d * ((q v ^ d : ℝ) : ℂ) ^ (1 - s)

/-- For unramified $\chi$, the zeta integral of $\mathbf{1}_{\mathcal{O}_v}$ is $L(s, \chi)$. -/
theorem zetaIntegral_integers_eq_localFactor (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ u = 1) (s : ℂ)
    (hs : ‖(χ (localUniformizer K v) : ℂ)‖ < q v ^ s.re) :
    zetaIntegral v ((closedBall 0 1).indicator 1) χ s = localFactor v χ s :=
  zetaIntegral_unramified v χ hχ _ (norm_localUniformizer v) s hs

/-- The value $\chi^{-1}(\varpi^{-d}) = \chi(\varpi)^d$. -/
theorem inv_apply_localUniformizer_zpow_neg (χ : (v.adicCompletion K)ˣ →* ℂˣ) (d : ℤ)
    (h : (localUniformizer K v : v.adicCompletion K) ^ (-d) ≠ 0) :
    ((χ⁻¹ (Units.mk0 _ h) : ℂˣ) : ℂ) = (χ (localUniformizer K v) : ℂ) ^ d := by
  have h' : Units.mk0 _ h = localUniformizer K v ^ (-d) := by
    ext
    simp
  rw [h', MonoidHom.inv_apply, map_zpow, ← zpow_neg, neg_neg, Units.val_zpow_eq_zpow_val]

/-- The unramified computation: if $\chi$ is trivial on $\mathcal{O}_v^\times$, then $Z(\hat{\mathbf{1}}_{\mathcal{O}_v}, \chi^{-1}, 1 - s) = \chi(\varpi)^d q^{d(1-s)} L(1 - s, \chi^{-1})$. -/
theorem zetaIntegral_fourier_integers (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ u = 1)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (s : ℂ)
    (hs : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    zetaIntegral v (fourier v ψ ((closedBall 0 1).indicator 1)) χ⁻¹ (1 - s) =
      epsilonUnramified v χ d s * localFactor v χ⁻¹ (1 - s) := by
  have hc : (localUniformizer K v : v.adicCompletion K) ^ (-d) ≠ 0 :=
    zpow_ne_zero _ (Units.ne_zero _)
  have hf : (fun x => (closedBall 0 (q v ^ d)).indicator (1 : v.adicCompletion K → ℂ)
      ((localUniformizer K v : v.adicCompletion K) ^ (-d) * x)) = (closedBall 0 1).indicator 1 := by
    ext x
    simp only [Set.indicator, mem_closedBall_zero_iff, Pi.one_apply,
      ← norm_localUniformizer_zpow_neg v d, norm_mul_le_norm_iff v hc]
  have hχ' : ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ⁻¹ u = 1 := by
    intro u hu
    rw [MonoidHom.inv_apply, hχ u hu, inv_one]
  rw [fourier_indicator_integers v ψ d h1 h2, zetaIntegral_eq_mul_comp v _ _ _ hc, hf,
    zetaIntegral_integers_eq_localFactor v χ⁻¹ hχ' (1 - s) hs, norm_localUniformizer_zpow_neg,
    inv_apply_localUniformizer_zpow_neg, epsilonUnramified]

/-- The local functional equation at an unramified place, for $f = \mathbf{1}_{\mathcal{O}_v}$:
$$Z(\hat{f}, \chi^{-1}, 1 - s) L(s, \chi) = \varepsilon(s, \chi, \psi) L(1 - s, \chi^{-1}) Z(f, \chi, s).$$
We state it without division, so that no condition $L(s, \chi) \neq 0$ is needed. -/
theorem localFunctionalEquation_unramified (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ u = 1)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (s : ℂ)
    (hs : ‖(χ (localUniformizer K v) : ℂ)‖ < q v ^ s.re)
    (hs' : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    zetaIntegral v (fourier v ψ ((closedBall 0 1).indicator 1)) χ⁻¹ (1 - s) * localFactor v χ s =
      epsilonUnramified v χ d s * localFactor v χ⁻¹ (1 - s) *
        zetaIntegral v ((closedBall 0 1).indicator 1) χ s := by
  rw [zetaIntegral_fourier_integers v χ hχ ψ d h1 h2 s hs',
    zetaIntegral_integers_eq_localFactor v χ hχ s hs]

/-- The unramified epsilon factor in the classical form $\varepsilon(s, \chi, \psi) = \chi(\varpi)^d q^{d(1/2 - s)} \cdot q^{d/2}$. The factor $q^{d/2}$ is the ratio of $dx$ to the self dual measure $q^{-d/2} dx$. -/
theorem epsilonUnramified_eq (χ : (v.adicCompletion K)ˣ →* ℂˣ) (d : ℤ) (s : ℂ) :
    epsilonUnramified v χ d s = (χ (localUniformizer K v) : ℂ) ^ d *
      ((q v ^ d : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((q v ^ d : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
  have h0 : ((q v ^ d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (zpow_pos (q_pos v) d).ne'
  rw [epsilonUnramified, mul_assoc, ← Complex.cpow_add _ _ h0,
    show (1 : ℂ) / 2 - s + 1 / 2 = 1 - s by ring]

/-- If $\psi$ has conductor exponent $0$, then the unramified epsilon factor is $1$. -/
theorem epsilonUnramified_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    epsilonUnramified v χ 0 s = 1 := by
  simp [epsilonUnramified]

/-! ### The ramified case -/

/-- Tate's test function $\mathbf{1}_{1 + \mathfrak{p}_v^a}$ for a character of conductor exponent $a$. -/
noncomputable def testFunction (a : ℕ) : v.adicCompletion K → ℂ :=
  (closedBall 1 ((q v)⁻¹ ^ a)).indicator 1

/-- For $a \geq 1$ the radius $q^{-a}$ is less than $1$. -/
theorem inv_q_pow_lt_one {a : ℕ} (ha : a ≠ 0) : (q v)⁻¹ ^ a < 1 :=
  pow_lt_one₀ (inv_nonneg.2 (q_pos v).le) (inv_q_lt_one v) ha

/-- On the support of the test function the integrand of $Z(\mathbf{1}_{1 + \mathfrak{p}_v^a}, \chi, s)$ is $1$. -/
theorem testFunction_mul_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ a) (ha : a ≠ 0) (s : ℂ) (x : v.adicCompletion K) :
    testFunction v a x * charExt χ x * (‖x‖ : ℂ) ^ s = testFunction v a x := by
  by_cases hx : x ∈ closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ a)
  · have h1 : ‖x‖ = 1 :=
      mem_sphere_zero_iff_norm.1 (closedBall_one_subset_sphere v (inv_q_pow_lt_one v ha) hx)
    have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
    have hxu : x = (Units.mk0 x hx0 : v.adicCompletion K) := rfl
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [testFunction, Set.indicator_of_mem (by rwa [mem_closedBall, dist_eq_norm]), hxu,
      charExt_units, hχ _ (by rwa [Units.val_mk0]) (by rwa [Units.val_mk0]), ← hxu, h1]
    simp
  · rw [testFunction, Set.indicator_of_notMem hx]
    simp

/-- The zeta integral of the test function: $Z(\mathbf{1}_{1 + \mathfrak{p}_v^a}, \chi, s) = (1 - q^{-1})^{-1} q^{-a}$ if $\chi$ is trivial on $1 + \mathfrak{p}_v^a$ and $a \geq 1$. -/
theorem zetaIntegral_testFunction {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ a) (ha : a ≠ 0) (s : ℂ) :
    zetaIntegral v (testFunction v a) χ s = (((1 - (q v)⁻¹)⁻¹ * (q v)⁻¹ ^ a : ℝ) : ℂ) := by
  have hS : MeasurableSet (closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ a)) :=
    measurableSet_closedBall
  simp_rw [zetaIntegral, testFunction_mul_charExt v hχ ha s, testFunction, Pi.one_def,
    integral_indicator_const _ hS, measureReal_def,
    multHaar_apply_of_subset_sphere v hS (closedBall_one_subset_sphere v (inv_q_pow_lt_one v ha)),
    haar_closedBall_one_pow, inv_one, mul_one, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_one_sub_inv_q_pos v).le,
    ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.2 (q_pos v).le) a), Complex.real_smul, mul_one]

/-- The Fourier transform of a translate: $\widehat{f(\cdot - 1)}(y) = \psi(y) \hat{f}(y)$. -/
theorem fourier_comp_sub_one (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    (y : v.adicCompletion K) :
    fourier v ψ (fun x => f (x - 1)) y = ψ y * fourier v ψ f y := by
  have h := integral_add_right_eq_self (μ := haar v) (fun x => f (x - 1) * ψ (x * y)) 1
  simp only [add_sub_cancel_right] at h
  simp only [fourier]
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_mul, one_mul, AddChar.map_add_eq_mul]
  ring

/-- The Fourier transform of the test function: $\hat{\mathbf{1}}_{1 + \mathfrak{p}_v^a}(y) = \psi(y) q^{-a} \mathbf{1}_{\{|y|_v \leq q^{d + a}\}}(y)$. -/
theorem fourier_testFunction (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (a : ℕ)
    (y : v.adicCompletion K) :
    fourier v ψ (testFunction v a) y =
      ψ y * (closedBall 0 (q v ^ (d + a))).indicator (fun _ => (((q v)⁻¹ ^ a : ℝ) : ℂ)) y := by
  have ha : (localUniformizer K v : v.adicCompletion K) ^ a ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have hn : ‖(localUniformizer K v : v.adicCompletion K) ^ a‖ = (q v)⁻¹ ^ a := by
    rw [norm_pow, norm_localUniformizer]
  have hf : testFunction v a = fun x => (closedBall 0 ‖(localUniformizer K v :
      v.adicCompletion K) ^ a‖).indicator (1 : v.adicCompletion K → ℂ) (x - 1) := by
    ext x
    simp only [testFunction, Set.indicator, mem_closedBall, dist_eq_norm, sub_zero, hn,
      Pi.one_apply]
  have hr : q v ^ d / (q v)⁻¹ ^ a = q v ^ (d + a) := by
    rw [zpow_add₀ (q_pos v).ne', inv_pow, div_inv_eq_mul, zpow_natCast]
  rw [hf, fourier_comp_sub_one, fourier_indicator_closedBall_of_conductor v ψ d h1 h2 ha, hn, hr]

/-- The epsilon factor $\varepsilon(s, \chi, \psi) = \chi(c)^{-1} |c|_v^{1 - s} G(\chi^{-1}, \psi, c)$ of a ramified character, where $|c|_v = q^{d + a}$. -/
noncomputable def epsilonRamified (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (ψ : AddChar (v.adicCompletion K) ℂ) {c : v.adicCompletion K} (hc : c ≠ 0) (s : ℂ) : ℂ :=
  ((χ (Units.mk0 c hc) : ℂˣ) : ℂ)⁻¹ * (‖c‖ : ℂ) ^ (1 - s) * gaussSum v χ⁻¹ ψ c

/-- The integrand of $Z(\hat{f}(c \cdot), \chi^{-1}, 1 - s)$ on $\mathcal{O}_v$, for the test function $f = \mathbf{1}_{1 + \mathfrak{p}_v^a}$. -/
noncomputable def ramifiedIntegrand (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (ψ : AddChar (v.adicCompletion K) ℂ) (a : ℕ) (c : v.adicCompletion K) (s : ℂ)
    (x : v.adicCompletion K) : ℂ :=
  (((q v)⁻¹ ^ a : ℝ) : ℂ) * ψ (c * x) * charExt χ⁻¹ x * (‖x‖ : ℂ) ^ (1 - s)

/-- After the substitution $y = c x$, the zeta integral of $\hat{f}$ is an integral over $\mathcal{O}_v$. -/
theorem zetaIntegral_fourier_testFunction_comp (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (a : ℕ)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + a)) (s : ℂ) :
    zetaIntegral v (fun x => fourier v ψ (testFunction v a) (c * x)) χ⁻¹ (1 - s) =
      ∫ x in closedBall 0 1, ramifiedIntegrand v χ ψ a c s x ∂multHaar v := by
  rw [zetaIntegral, ← integral_indicator measurableSet_closedBall]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [fourier_testFunction v ψ d h1 h2, ← hc]
  by_cases hx : ‖x‖ ≤ 1
  · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 ((norm_mul_le_norm_iff v hc0 x).2 hx)),
      Set.indicator_of_mem (mem_closedBall_zero_iff.2 hx), ramifiedIntegrand]
    ring
  · rw [Set.indicator_of_notMem (fun h => hx ((norm_mul_le_norm_iff v hc0 x).1
      (mem_closedBall_zero_iff.1 h))), Set.indicator_of_notMem (fun h => hx
      (mem_closedBall_zero_iff.1 h))]
    ring

/-- The integrand is continuous on $K_v^\times$. -/
theorem continuousOn_ramifiedIntegrand {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) (a : ℕ) (c : v.adicCompletion K)
    (s : ℂ) : ContinuousOn (ramifiedIntegrand v χ ψ a c s) {0}ᶜ := by
  have hψ : ContinuousOn (fun x : v.adicCompletion K => ψ (c * x)) {0}ᶜ :=
    ((continuous_addChar v ψ d h1).comp (continuous_const_mul c)).continuousOn
  have hp : ContinuousOn (fun x : v.adicCompletion K => (‖x‖ : ℂ) ^ (1 - s)) {0}ᶜ := by
    intro x hx
    have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx
    have hn : ContinuousAt (fun y : v.adicCompletion K => ((‖y‖ : ℝ) : ℂ)) x :=
      (Complex.continuous_ofReal.comp continuous_norm).continuousAt
    exact (hn.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hx0))).continuousWithinAt
  exact ((continuousOn_const.mul hψ).mul
    (continuousOn_charExt v (isTrivialOnHigherUnits_inv v hχ))).mul hp

/-- The integrand is integrable on $\mathcal{O}_v$ for $d^\times x$ when $|\chi^{-1}(\varpi)| < q^{\mathrm{Re}(1 - s)}$. -/
theorem integrableOn_ramifiedIntegrand {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) (a : ℕ) (c : v.adicCompletion K)
    (s : ℂ) (hs : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    IntegrableOn (ramifiedIntegrand v χ ψ a c s) (closedBall 0 1) (multHaar v) := by
  have hχ' := isTrivialOnHigherUnits_inv v hχ
  obtain ⟨C, hC⟩ := exists_norm_charExt_le v hχ'
  refine integrableOn_closedBall_one_of_le v (C := (q v)⁻¹ ^ a * C)
    (aestronglyMeasurable_of_continuousOn v (continuousOn_ramifiedIntegrand v hχ ψ d h1 a c s))
    (neg_logb_add_pos v hs) fun x hx0 hx1 => ?_
  have hx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hqa : 0 ≤ (q v)⁻¹ ^ a := pow_nonneg (inv_nonneg.2 (q_pos v).le) a
  rw [ramifiedIntegrand, norm_mul, norm_mul, norm_mul, norm_addChar_eq_one v ψ d h1,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_of_nonneg hqa, mul_one,
    Real.rpow_add hx, ← mul_assoc, mul_assoc _ C]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC x hx0 hx1) hqa)
    (Real.rpow_nonneg hx.le _)

/-- The integral over $|x|_v < 1$ vanishes. If $w \in 1 + \mathfrak{p}_v^{a - 1}$ and $|x|_v < 1$, then $\psi(c w x) = \psi(c x)$, so the integrand $h$ satisfies $h(w x) = \chi(w)^{-1} h(x)$. -/
theorem setIntegral_ball_ramifiedIntegrand {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ' : ¬ IsTrivialOnHigherUnits v χ b) (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ) :
    ∫ x in ball 0 1, ramifiedIntegrand v χ ψ (b + 1) c s x ∂multHaar v = 0 := by
  rw [IsTrivialOnHigherUnits] at hχ'
  push Not at hχ'
  obtain ⟨w, hw1, hwb, hχw⟩ := hχ'
  have hw0 : (w : v.adicCompletion K) ≠ 0 := w.ne_zero
  refine setIntegral_multHaar_eq_zero_of_comp_mul v measurableSet_ball _ hw0 (c := χ⁻¹ w)
    (fun x => by rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_mul, hw1, one_mul]) ?_ ?_
  · intro h
    rw [MonoidHom.inv_apply, Units.val_eq_one, inv_eq_one] at h
    exact hχw h
  · intro x hx
    have hx' : ‖x‖ ≤ (q v)⁻¹ := (norm_lt_one_iff_le v).1 (mem_ball_zero_iff.1 hx)
    have hψ : ψ (c * (x * ((w : v.adicCompletion K) - 1))) = 1 := by
      refine h1 _ ?_
      have h := (norm_mul_le_zpow_iff v hc (x * ((w : v.adicCompletion K) - 1)) (k := 0)).2 ?_
      · rwa [add_zero] at h
      rw [zero_sub, zpow_neg_natCast, norm_mul, pow_succ']
      exact mul_le_mul hx' hwb (norm_nonneg _) (inv_nonneg.2 (q_pos v).le)
    have hcw : c * (w * x) = c * x + c * (x * ((w : v.adicCompletion K) - 1)) := by ring
    rw [ramifiedIntegrand, ramifiedIntegrand, hcw, AddChar.map_add_eq_mul, hψ, mul_one,
      charExt_mul χ⁻¹ hw0, Units.mk0_val, norm_mul, hw1, one_mul]
    ring

/-- The integral over $\mathcal{O}_v^\times$ is a Gauss sum: it is $(1 - q^{-1})^{-1} q^{-a} G(\chi^{-1}, \psi, c)$. -/
theorem setIntegral_sphere_ramifiedIntegrand (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (ψ : AddChar (v.adicCompletion K) ℂ) (a : ℕ) (c : v.adicCompletion K) (s : ℂ) :
    ∫ x in sphere 0 1, ramifiedIntegrand v χ ψ a c s x ∂multHaar v =
      (((1 - (q v)⁻¹)⁻¹ * (q v)⁻¹ ^ a : ℝ) : ℂ) * gaussSum v χ⁻¹ ψ c := by
  rw [setIntegral_sphere_multHaar, gaussSum, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_
  rw [ramifiedIntegrand, mem_sphere_zero_iff_norm.1 hx, Complex.ofReal_one, Complex.one_cpow,
    Complex.ofReal_mul]
  ring

/-- The ramified computation: $Z(\hat{\mathbf{1}}_{1 + \mathfrak{p}_v^a}, \chi^{-1}, 1 - s) = \chi(c)^{-1} |c|_v^{1 - s} (1 - q^{-1})^{-1} q^{-a} G(\chi^{-1}, \psi, c)$, where $a = b + 1$ is the conductor exponent of $\chi$ and $|c|_v = q^{d + a}$. -/
theorem zetaIntegral_fourier_testFunction {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ)
    (hs : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    zetaIntegral v (fourier v ψ (testFunction v (b + 1))) χ⁻¹ (1 - s) =
      epsilonRamified v χ ψ hc0 s * (((1 - (q v)⁻¹)⁻¹ * (q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) := by
  have hint := integrableOn_ramifiedIntegrand v hχ ψ d h1 (b + 1) c s hs
  have hsph : ∫ x in sphere 0 1, ramifiedIntegrand v χ ψ (b + 1) c s x ∂multHaar v =
      ∫ x in closedBall 0 1, ramifiedIntegrand v χ ψ (b + 1) c s x ∂multHaar v := by
    rw [← closedBall_sdiff_ball, setIntegral_sdiff measurableSet_ball hint ball_subset_closedBall,
      setIntegral_ball_ramifiedIntegrand v hχ' ψ d h1 hc s, sub_zero]
  rw [zetaIntegral_eq_mul_comp v _ _ _ hc0,
    zetaIntegral_fourier_testFunction_comp v χ ψ d h1 h2 (b + 1) hc0 hc s, ← hsph,
    setIntegral_sphere_ramifiedIntegrand, epsilonRamified, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val]
  ring

/-- The local functional equation at a ramified place, for Tate's test function $f = \mathbf{1}_{1 + \mathfrak{p}_v^a}$:
$$Z(\hat{f}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(f, \chi, s), \qquad \varepsilon(s, \chi, \psi) = \chi(c)^{-1} |c|_v^{1 - s} G(\chi^{-1}, \psi, c).$$
Here $a = b + 1$ is the conductor exponent of $\chi$, $d$ is the conductor exponent of $\psi$ and $|c|_v = q^{d + a}$. Both local factors $L(s, \chi)$ and $L(1 - s, \chi^{-1})$ are $1$. -/
theorem localFunctionalEquation_ramified {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ)
    (hs : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    zetaIntegral v (fourier v ψ (testFunction v (b + 1))) χ⁻¹ (1 - s) =
      epsilonRamified v χ ψ hc0 s * zetaIntegral v (testFunction v (b + 1)) χ s := by
  rw [zetaIntegral_fourier_testFunction v hχ hχ' ψ d h1 h2 hc0 hc s hs,
    zetaIntegral_testFunction v hχ (Nat.succ_ne_zero b)]

/-- The Gauss sum in the ramified epsilon factor has $|G(\chi^{-1}, \psi, c)|^2 = q^{-a}$. -/
theorem norm_gaussSum_inv_sq {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    ‖gaussSum v χ⁻¹ ψ c‖ ^ 2 = (q v)⁻¹ ^ (b + 1) :=
  norm_gaussSum_sq v (isTrivialOnHigherUnits_inv v hχ)
    (fun h => hχ' ((isTrivialOnHigherUnits_inv_iff v).1 h)) ψ d h1 h2 hc

/-- The ramified epsilon factor is not zero. -/
theorem epsilonRamified_ne_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ) :
    epsilonRamified v χ ψ hc0 s ≠ 0 := by
  have hG := gaussSum_ne_zero v (isTrivialOnHigherUnits_inv v hχ)
    (fun h => hχ' ((isTrivialOnHigherUnits_inv_iff v).1 h)) ψ d h1 h2 hc
  have hn : ((‖c‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc0)
  refine mul_ne_zero (mul_ne_zero (inv_ne_zero (Units.ne_zero _)) ?_) hG
  exact fun h => hn ((Complex.cpow_eq_zero_iff _ _).1 h).1

end Langlands.Tate.NonArchimedean
