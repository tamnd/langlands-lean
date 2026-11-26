/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassQuadratic
import Langlands.Tate.ArchimedeanFourier

/-!
# Theta series with a harmonic polynomial for a lattice in the complex plane

Let $M \subset \mathbb{C}$ be a lattice, with the real inner product $\langle z, w \rangle = \mathrm{Re}(z \bar w)$, and let $k \ge 0$. This file proves the transformation formula of the theta series with the harmonic polynomial $\bar z^k$, $$\theta_M^k(x, y; t) = \sum_{\mu \in M} \overline{(x + \mu)}^k e^{-\pi t |x + \mu|^2} e^{2 \pi i \langle x + \mu, y \rangle},$$ and the analytic continuation and the functional equation of the weighted Epstein zeta function $$Z_M^k(x, y; s) = \sum_{x + \mu \neq 0} \overline{(x + \mu)}^k e^{2 \pi i \langle x + \mu, y \rangle} |x + \mu|^{-s}.$$ These are the analytic steps of Hecke's proof for the Hecke characters of an imaginary quadratic field with the archimedean parameter $n \neq 0$, with $k = |n|$.

## Main definitions

* `Langlands.Tate.gaussWeight`: the function $\bar v^k e^{-\pi t |v|^2}$ on $\mathbb{C}$.
* `Langlands.Tate.weightTheta`: the theta series $\theta_M^k(x, y; t)$.
* `Langlands.Tate.weightConst`: the constant term of $\theta_M^k(x, y; t)$ at $t = \infty$. It is $0$ for $k \neq 0$.
* `Langlands.Tate.weightThetaFEPair`: the pair $(\theta_M^k(x, y; \cdot), \theta_{M^\vee}^k(-y, x; \cdot))$ as a `WeakFEPair` of weight $k + 1$.
* `Langlands.Tate.weightZeta`: the Dirichlet series $Z_M^k(x, y; s)$.
* `Langlands.Tate.completedWeightZeta`: the completed function $\Lambda_M^k(x, y; s)$, equal to $\Gamma_\mathbb{R}(s) Z_M^k(x, y; s)$ for $\mathrm{Re}\, s > k + 2$.

## Main results

* `fourier_gaussWeight`: Hecke's lemma for $\bar v^k$. For $t > 0$, $\mathcal{F}(\bar v^k e^{-\pi t |v|^2})(w) = (-i)^k t^{-(k + 1)} \bar w^k e^{-\pi |w|^2 / t}$.
* `weightTheta_eq`: the transformation formula $$\theta_M^k(x, y; t) = \frac{(-i)^k e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(M) \, t^{k + 1}} \, \theta_{M^\vee}^k(-y, x; 1/t).$$
* `hasSum_completedWeightZeta` and `completedWeightZeta_eq`: for $\mathrm{Re}\, s > k + 2$, $\Lambda_M^k(x, y; s) = \Gamma_\mathbb{R}(s) Z_M^k(x, y; s)$.
* `differentiable_completedWeightZeta`: for $k \neq 0$, $\Lambda_M^k(x, y; \cdot)$ is entire.
* `completedWeightZeta_sub`: for $k \neq 0$, $$\Lambda_M^k(x, y; 2k + 2 - s) = (-i)^k \, \mathrm{covol}(M)^{-1} \, e^{2 \pi i \langle x, y \rangle} \, \Lambda_{M^\vee}^k(-y, x; s).$$
* `completedWeightZeta_zero`: for $k = 0$ the function is `Langlands.Tate.completedShiftEpsteinZeta`.

## Proofs

The Fourier transform of $\bar v^k e^{-2 \pi |v|^2}$ is `Langlands.Tate.fourier_gaussConj`. The general $t$ follows by the substitution $v \mapsto a v$ with $a^2 = t / 2$ (`fourier_const_mul_comp_smul`). The transformation formula is the Poisson summation formula `Langlands.Tate.tsum_add_zlattice_eq_of_hasDecay` for the function $\bar v^k e^{-\pi t |v|^2} e^{2 \pi i \langle v, y \rangle}$, as in `Langlands.Tate.shiftTheta_eq`. The bound $r^k e^{-b r^2} \le k! \, e^{1 + 1 / (2 b)} e^{-(b/2) r^2}$ (`pow_mul_exp_le`) gives the convergence and the decay. For $k \neq 0$ the term at $x + \mu = 0$ is $0$, so both theta series decay exponentially at $t = \infty$ and the pair is a strong FE pair. The Dirichlet series comes from `hasSum_mellin_pi_mul_sq`.

With $s = 2u + k$, the term $\bar\alpha^k |\alpha|^{-s}$ is $(\bar\alpha / |\alpha|)^k |\alpha|^{-2u}$, and $\Gamma_\mathbb{C}(u + k/2) = 2^{1 - u - k/2} \Gamma_\mathbb{R}(2u + k)$. The functional equation $s \mapsto 2k + 2 - s$ is $u \mapsto 1 - u$. The factor $(-i)^k$ is the archimedean root number `Langlands.Tate.complexRootNumber`.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt K` for a Hecke character $\chi$ of an imaginary quadratic field with $n \neq 0$. These steps are still open. First, the transfer of the results of this file from $\mathbb{C}$ to the lattices `Langlands.Tate.globalLattice` in the euclidean mixed space of $K$, through an isometry of this space with $\mathbb{C}$ that sends the Minkowski embedding to a complex embedding $\sigma$ (with a factor $\sqrt 2$), and the identification of the dual lattice with $\sigma$ of the trace dual, with the complex conjugation of `Langlands.Tate.globalConjEmbedding`. Second, the weighted form of `Langlands.Tate.RayClassFE`: the coefficient $c_J(\alpha) = \chi_f((\alpha) J^{-1}) \, (\bar\sigma(\alpha) / |\sigma(\alpha)|)^{|n|}$ (or $\sigma(\alpha)$ for the other sign of $n$), its periodicity modulo $\mathfrak{f} J$ and its invariance under the units, which needs the comparison of $\chi$ on principal ideals with $\chi_\infty(\alpha) = (\alpha / |\alpha|)^n |\alpha|^{2t}$. A unit $\varepsilon \neq \pm 1$ multiplies $\bar\alpha^{|n|}$ by $\bar\varepsilon^{|n|}$, so the sum over the units does not vanish only because of the compatibility of $\chi_f$ and $\chi_\infty$ on the units. Third, the weighted Gauss sums, the sorting of the dual series by the ideals $(\beta) \mathfrak{f} J \mathfrak{d}$, the sum over the ideal classes, the comparison of $\Gamma_\mathbb{R}(2u + |n|)$ with `Langlands.gammaFactor` for the parameter $n$, and the root number $W = (-i)^{|n|} \tau(\chi) / \sqrt{N(\mathfrak{f})}$, as in `Langlands.Tate.RayClassHecke`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 7 and 8.
-/

open MeasureTheory Module Filter Topology Set Complex FourierTransform Asymptotics
open scoped RealInnerProductSpace

namespace Langlands.Tate

/-- The Fourier transform on $\mathbb{C}$ under a real dilation: for $a \neq 0$, $\mathcal{F}(g(a \cdot))(w) = a^{-2} \mathcal{F} g(w / a)$. -/
theorem fourier_comp_smul (g : ℂ → ℂ) {a : ℝ} (ha : a ≠ 0) (w : ℂ) :
    𝓕 (fun v => g (a • v)) w = ((a ^ 2)⁻¹ : ℝ) * 𝓕 g (a⁻¹ • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun u : ℂ => cexp (↑(-2 * Real.pi * ⟪u, a⁻¹ • w⟫) * I) • g u) a
  simp only [Complex.finrank_real_complex] at h
  have e : ∀ v : ℂ, cexp (↑(-2 * Real.pi * ⟪v, w⟫) * I) • g (a • v) =
      cexp (↑(-2 * Real.pi * ⟪a • v, a⁻¹ • w⟫) * I) • g (a • v) := fun v => by
    rw [inner_smul_left, inner_smul_right]
    simp [ha]
  simp only [e]
  rw [h, abs_of_nonneg (inv_nonneg.2 (sq_nonneg a)), Complex.real_smul]

/-- The Fourier transform of $c \, g(a v)$ on $\mathbb{C}$: for $a \neq 0$, it is $c \, a^{-2} \mathcal{F} g(w / a)$. -/
theorem fourier_const_mul_comp_smul (c : ℂ) (g : ℂ → ℂ) {a : ℝ} (ha : a ≠ 0) (w : ℂ) :
    𝓕 (fun v => c * g (a • v)) w = c * (((a ^ 2)⁻¹ : ℝ) * 𝓕 g (a⁻¹ • w)) := by
  rw [← fourier_comp_smul g ha, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  congr 1 with v
  simp only [smul_eq_mul]
  ring

/-- The Gaussian with the harmonic polynomial $\bar v^k$: the function $\bar v^k e^{-\pi t |v|^2}$ on $\mathbb{C}$. -/
noncomputable def gaussWeight (k : ℕ) (t : ℝ) (v : ℂ) : ℂ :=
  (starRingEnd ℂ v) ^ k * (Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) : ℂ)

/-- If $a > 0$ and $a^2 = t / 2$, then $\bar v^k e^{-\pi t |v|^2} = a^{-k} \, \overline{(a v)}^k e^{-2 \pi |a v|^2}$. -/
theorem gaussWeight_eq_smul (k : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a ^ 2 = t / 2) :
    gaussWeight k t = fun v => ((a : ℂ) ^ k)⁻¹ * gaussConj k (a • v) := by
  funext v
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [gaussWeight, gaussConj, Complex.real_smul, map_mul,
    Complex.conj_ofReal, mul_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [Complex.ofReal_exp]
  have : (-(Real.pi * t) * ‖v‖ ^ 2 : ℝ) = -((2 * Real.pi) * (a * ‖v‖) ^ 2) := by
    rw [mul_pow, hat]; ring
  rw [this]
  push_cast
  field_simp

/-- **Hecke's lemma for $\bar v^k$.** For $t > 0$, the Fourier transform of $\bar v^k e^{-\pi t |v|^2}$ is $(-i)^k t^{-(k + 1)} \bar w^k e^{-\pi |w|^2 / t}$. -/
theorem fourier_gaussWeight (k : ℕ) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    𝓕 (gaussWeight k t) w = (-I) ^ k * ((t ^ (k + 1))⁻¹ : ℝ) * gaussWeight k (1 / t) w := by
  set a := √(t / 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hat : a ^ 2 = t / 2 := Real.sq_sqrt (by positivity)
  rw [gaussWeight_eq_smul k ha hat, fourier_const_mul_comp_smul _ _ ha.ne',
    fourier_gaussConj, fourierGaussConj, gaussWeight]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hat' : (a : ℂ) ^ 2 = t / 2 := by exact_mod_cast hat
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 ha.le), Complex.ofReal_exp]
  have e : (-(Real.pi / 2 * (a⁻¹ * ‖w‖) ^ 2) : ℝ) = -(Real.pi * (1 / t)) * ‖w‖ ^ 2 := by
    rw [mul_pow, inv_pow, hat]; field_simp
  rw [e]
  have e2 : ((a : ℂ)⁻¹) ^ k * ((a : ℂ) ^ k)⁻¹ = (((a : ℂ) ^ 2) ^ k)⁻¹ := by
    rw [← pow_mul, mul_comm 2 k, pow_mul', inv_pow]
    rw [sq, mul_pow, mul_inv]
  push_cast
  rw [mul_pow]
  calc _ = (1 / 2 * (-I / 2) ^ k) * ((a : ℂ) ^ 2)⁻¹ * ((a : ℂ)⁻¹ ^ k * ((a : ℂ) ^ k)⁻¹) *
        (starRingEnd ℂ w) ^ k * cexp (-(Real.pi * (1 / t)) * ‖w‖ ^ 2) := by ring
    _ = _ := by
        rw [e2, hat', div_pow, ← inv_pow]
        field_simp
        rw [div_pow, pow_succ]
        field_simp

/-- The absolute value of $\bar v^k e^{-\pi t |v|^2}$ is $|v|^k e^{-\pi t |v|^2}$. -/
theorem norm_gaussWeight (k : ℕ) (t : ℝ) (v : ℂ) :
    ‖gaussWeight k t v‖ = ‖v‖ ^ k * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) := by
  rw [gaussWeight, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- For $b > 0$ and $r \ge 0$, $r^k e^{-b r^2} \le k! \, e^{1 + 1 / (2 b)} e^{-(b/2) r^2}$. -/
theorem pow_mul_exp_le (k : ℕ) {b : ℝ} (hb : 0 < b) {r : ℝ} (hr : 0 ≤ r) :
    r ^ k * Real.exp (-b * r ^ 2) ≤
      k.factorial * Real.exp (1 + 1 / (4 * (b / 2))) * Real.exp (-(b / 2) * r ^ 2) := by
  have h := one_add_pow_mul_exp_le (half_pos hb) k hr
  have h1 : r ^ k ≤ (1 + r) ^ k := pow_le_pow_left₀ hr (by linarith) k
  have e : Real.exp (-b * r ^ 2) = Real.exp (-(b / 2) * r ^ 2) * Real.exp (-(b / 2) * r ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans h) (Real.exp_pos _).le

/-- For $b > 0$ and $x \in \mathbb{C}$, the series $\sum_{\mu \in M} |x + \mu|^k e^{-b |x + \mu|^2}$ converges. -/
theorem summable_norm_pow_mul_exp (M : Submodule ℤ ℂ) [DiscreteTopology M] [IsZLattice ℝ M]
    (k : ℕ) {b : ℝ} (hb : 0 < b) (x : ℂ) :
    Summable fun μ : M => ‖x + μ‖ ^ k * Real.exp (-b * ‖x + μ‖ ^ 2) :=
  ((summable_exp_neg_mul_norm_add_sq M (half_pos hb) x).mul_left
    (k.factorial * Real.exp (1 + 1 / (4 * (b / 2))))).of_nonneg_of_le
    (fun _ => by positivity) fun μ => pow_mul_exp_le k hb (norm_nonneg _)

/-- For $t > 0$, the function $\bar v^k e^{-\pi t |v|^2} e^{2 \pi i \langle v, y \rangle}$ decays of each order $N$. -/
theorem hasDecay_gaussWeight_mul (k : ℕ) {t : ℝ} (ht : 0 < t) (y : ℂ) (N : ℕ) :
    HasDecay (fun v => gaussWeight k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)) N :=
  ⟨_, fun v => by
    rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one, norm_gaussWeight, ← mul_assoc]
    refine le_trans ?_ (one_add_pow_mul_exp_le (mul_pos Real.pi_pos ht) (N + k) (norm_nonneg v))
    rw [pow_add]
    gcongr
    · linarith [norm_nonneg v]⟩

variable (M : Submodule ℤ ℂ)

/-- The theta series of the lattice $M \subset \mathbb{C}$ with the harmonic polynomial $\bar z^k$, shifted by $x$ and twisted by $y$: $$\theta_M^k(x, y; t) = \sum_{\mu \in M} \overline{(x + \mu)}^k e^{-\pi t |x + \mu|^2} e^{2 \pi i \langle x + \mu, y \rangle}.$$ It is meaningful for $t > 0$. -/
noncomputable def weightTheta (k : ℕ) (x y : ℂ) (t : ℝ) : ℂ :=
  ∑' μ : M, gaussWeight k t (x + μ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫)

/-- The terms of the weighted theta series have absolute value $|x + \mu|^k e^{-\pi t |x + \mu|^2}$. -/
theorem norm_weightTheta_term (k : ℕ) (x y : ℂ) (t : ℝ) (μ : M) :
    ‖gaussWeight k t (x + μ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫)‖ =
      ‖x + μ‖ ^ k * Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) := by
  rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one, norm_gaussWeight]

variable [DiscreteTopology M] [IsZLattice ℝ M]

/-- The series of $\theta_M^k(x, y; t)$ converges for $t > 0$. -/
theorem summable_weightTheta (k : ℕ) (x y : ℂ) {t : ℝ} (ht : 0 < t) :
    Summable fun μ : M => gaussWeight k t (x + μ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫) :=
  Summable.of_norm_bounded (summable_norm_pow_mul_exp M k (mul_pos Real.pi_pos ht) x)
    fun μ => (norm_weightTheta_term M k x y t μ).le

/-- **The transformation formula of the weighted theta series.** For $t > 0$ and $x, y \in \mathbb{C}$, $$\theta_M^k(x, y; t) = \frac{(-i)^k e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(M) \, t^{k + 1}} \, \theta_{M^\vee}^k(-y, x; 1/t).$$ -/
theorem weightTheta_eq (k : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℂ) :
    weightTheta M k x y t =
      (-I) ^ k * ((ZLattice.covolume M)⁻¹ * (t ^ (k + 1))⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ⟪x, y⟫) * weightTheta (dualLattice M) k (-y) x (1 / t) := by
  set f : ℂ → ℂ := fun v => gaussWeight k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)
  have hc : Continuous f := by simp only [f, gaussWeight]; fun_prop
  have hN : finrank ℝ ℂ < finrank ℝ ℂ + 1 := Nat.lt_succ_self _
  have hFf : ∀ w, 𝓕 f w = (-I) ^ k * ((t ^ (k + 1))⁻¹ : ℝ) * gaussWeight k (1 / t) (-y + w) :=
    fun w => by
      rw [fourier_mul_cexp_inner, fourier_gaussWeight k ht, sub_eq_neg_add]
  have hF : Summable fun μ : dualLattice M => 𝓕 f μ := by
    simp only [hFf]
    refine Summable.mul_left _ (Summable.of_norm_bounded (summable_norm_pow_mul_exp
      (dualLattice M) k (mul_pos Real.pi_pos (one_div_pos.2 ht)) (-y)) fun μ => ?_)
    rw [norm_gaussWeight]
  have key := tsum_add_zlattice_eq_of_hasDecay M hc (hasDecay_gaussWeight_mul k ht y _) hN hF x
  rw [weightTheta, weightTheta, key]
  simp only [hFf]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun (μ : dualLattice M) => ?_
  have hinner : ⟪x, (μ : ℂ)⟫ = ⟪x, y⟫ + ⟪-y + μ, x⟫ := by
    rw [inner_add_left, inner_neg_left, real_inner_comm x y, real_inner_comm x μ]
    ring
  rw [hinner]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- The constant term of $\theta_M^k(x, y; t)$ at $t = \infty$: it is `Langlands.Tate.shiftConst` for $k = 0$ and $0$ for $k \neq 0$. -/
noncomputable def weightConst (k : ℕ) (x : ℂ) : ℂ :=
  if k = 0 then shiftConst M x else 0

omit [DiscreteTopology M] [IsZLattice ℝ M] in
/-- For $k = 0$ the weighted theta series is the theta series `Langlands.Tate.shiftTheta`. -/
theorem weightTheta_zero (x y : ℂ) (t : ℝ) : weightTheta M 0 x y t = shiftTheta M x y t := by
  simp [weightTheta, shiftTheta, gaussWeight]

/-- The weighted theta series without its constant term: $\sum_{x + \mu \neq 0} (\ldots) = \theta_M^k(x, y; t) - c_M^k(x)$. -/
theorem hasSum_weightTheta_sub (k : ℕ) (x y : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun μ : M => if x + (μ : ℂ) = 0 then 0 else
      gaussWeight k t (x + μ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫))
      (weightTheta M k x y t - weightConst M k x) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [weightTheta_zero]
    simp only [weightConst, ↓reduceIte]
    convert hasSum_shiftTheta_sub M x y ht using 3 with μ
    simp [gaussWeight]
  · simp only [weightConst, hk, ↓reduceIte, sub_zero]
    rw [weightTheta]
    convert (summable_weightTheta M k x y ht).hasSum using 2 with μ
    split_ifs with h
    · simp [h, gaussWeight, hk]
    · rfl

/-- The weighted theta series is continuous on $(0, \infty)$. -/
theorem continuousOn_weightTheta (k : ℕ) (x y : ℂ) :
    ContinuousOn (weightTheta M k x y) (Ioi 0) := by
  intro t₀ ht₀
  have hδ : (0 : ℝ) < t₀ / 2 := half_pos ht₀
  have hc : ContinuousOn (weightTheta M k x y) (Ioi (t₀ / 2)) := by
    refine continuousOn_tsum (fun μ => by simp only [gaussWeight]; fun_prop)
      (summable_norm_pow_mul_exp M k (mul_pos Real.pi_pos hδ) x) ?_
    intro μ t ht
    rw [norm_weightTheta_term]
    gcongr
    have h1 : t₀ / 2 ≤ t := le_of_lt ht
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg ‖x + (μ : ℂ)‖)) (sub_nonneg.2 h1)]
  exact (hc.continuousAt (Ioi_mem_nhds (half_lt_self ht₀))).continuousWithinAt

/-- The weighted theta series minus its constant term decays exponentially: for $t \ge 1$, $$|\theta_M^k(x, y; t) - c_M^k(x)| \le e^{-\pi c (t - 1)} \sum_{\mu \in M} |x + \mu|^k e^{-\pi |x + \mu|^2}.$$ -/
theorem norm_weightTheta_sub_le (k : ℕ) (x y : ℂ) {c : ℝ}
    (hc : ∀ μ : M, x + (μ : ℂ) ≠ 0 → c ≤ ‖x + μ‖ ^ 2) {t : ℝ} (ht : 1 ≤ t) :
    ‖weightTheta M k x y t - weightConst M k x‖ ≤
      Real.exp (-(Real.pi * c) * (t - 1)) *
        ∑' μ : M, ‖x + μ‖ ^ k * Real.exp (-(Real.pi * 1) * ‖x + μ‖ ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  refine (hasSum_weightTheta_sub M k x y ht0).norm_le_of_bounded
    ((summable_norm_pow_mul_exp M k (mul_pos Real.pi_pos one_pos) x).hasSum.mul_left
      (Real.exp (-(Real.pi * c) * (t - 1)))) fun μ => ?_
  split_ifs with hμ
  · rw [norm_zero]
    positivity
  · rw [norm_weightTheta_term, mul_left_comm, ← Real.exp_add]
    gcongr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 ht)) (sub_nonneg.2 (hc μ hμ))]

/-- The weighted theta series minus its constant term is $O(t^r)$ at infinity for each $r$. -/
theorem isBigO_weightTheta_sub (k : ℕ) (x y : ℂ) (r : ℝ) :
    (fun t => weightTheta M k x y t - weightConst M k x) =O[atTop] (· ^ r) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_add_sq M x
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop (mul_pos Real.pi_pos hc0) r).isBigO
  refine IsBigO.trans ?_ hexp
  set B := ∑' μ : M, ‖x + μ‖ ^ k * Real.exp (-(Real.pi * 1) * ‖x + μ‖ ^ 2)
  refine IsBigO.of_bound (Real.exp (Real.pi * c) * B) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc ‖weightTheta M k x y t - weightConst M k x‖
      ≤ Real.exp (-(Real.pi * c) * (t - 1)) * B := norm_weightTheta_sub_le M k x y hc ht
    _ = Real.exp (Real.pi * c) * B * Real.exp (-(Real.pi * c) * t) := by
        rw [mul_comm (Real.exp (Real.pi * c)), mul_assoc, ← Real.exp_add]
        ring_nf

/-- The pair $(\theta_M^k(x, y; \cdot), \theta_{M^\vee}^k(-y, x; \cdot))$ as a `WeakFEPair`, with weight $k + 1$ and root number $(-i)^k \mathrm{covol}(M)^{-1} e^{2 \pi i \langle x, y \rangle}$. -/
noncomputable def weightThetaFEPair (k : ℕ) (x y : ℂ) : WeakFEPair ℂ where
  f := weightTheta M k x y
  g := weightTheta (dualLattice M) k (-y) x
  k := ((k + 1 : ℕ) : ℝ)
  ε := (-I) ^ k * ((ZLattice.covolume M)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫)
  f₀ := weightConst M k x
  g₀ := weightConst (dualLattice M) k (-y)
  hf_int := (continuousOn_weightTheta M k x y).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_weightTheta (dualLattice M) k (-y) x).locallyIntegrableOn
    measurableSet_Ioi
  hk := by positivity
  hε := mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 I_ne_zero))
    (Complex.ofReal_ne_zero.2 (inv_ne_zero (ZLattice.covolume_pos M).ne')))
    (Complex.exp_ne_zero _)
  h_feq t ht := by
    have ht' : (0 : ℝ) < 1 / t := one_div_pos.2 ht
    rw [weightTheta_eq M k ht' x y, one_div_one_div, smul_eq_mul, Real.rpow_natCast, one_div,
      inv_pow, inv_inv]
    push_cast
    ring
  hf_top := isBigO_weightTheta_sub M k x y
  hg_top := isBigO_weightTheta_sub (dualLattice M) k (-y) x

/-- For $k \neq 0$ the pair of weighted theta series is a strong FE pair: both constant terms are $0$. -/
theorem isStrongFEPair_weightThetaFEPair {k : ℕ} (hk : k ≠ 0) (x y : ℂ) :
    IsStrongFEPair (weightThetaFEPair M k x y) where
  hf₀ := by simp [weightThetaFEPair, weightConst, hk]
  hg₀ := by simp [weightThetaFEPair, weightConst, hk]

/-- The weighted Epstein zeta function $$Z_M^k(x, y; s) = \sum_{\mu \in M, \, x + \mu \neq 0} \overline{(x + \mu)}^k e^{2 \pi i \langle x + \mu, y \rangle} |x + \mu|^{-s}.$$ The series converges for $\mathrm{Re}\, s > k + 2$. -/
noncomputable def weightZeta (k : ℕ) (x y : ℂ) (s : ℂ) : ℂ :=
  ∑' μ : M, if x + (μ : ℂ) = 0 then 0 else
    (starRingEnd ℂ (x + μ)) ^ k * cexp (2 * Real.pi * I * ⟪x + μ, y⟫) *
      ((‖x + (μ : ℂ)‖ : ℝ) : ℂ) ^ (-s)

/-- The completed weighted Epstein zeta function $\Lambda_M^k(x, y; s)$: the function $\Lambda$ of `Langlands.Tate.weightThetaFEPair` at $s / 2$. -/
noncomputable def completedWeightZeta (k : ℕ) (x y : ℂ) (s : ℂ) : ℂ :=
  (weightThetaFEPair M k x y).Λ (s / 2)

/-- The Dirichlet series of $\Lambda_M^k(x, y; s)$: for $\mathrm{Re}\, s > k + 2$, $$\Lambda_M^k(x, y; s) = \sum_{x + \mu \neq 0} \Gamma_\mathbb{R}(s) \overline{(x + \mu)}^k e^{2 \pi i \langle x + \mu, y \rangle} |x + \mu|^{-s}.$$ -/
theorem hasSum_completedWeightZeta (k : ℕ) (x y : ℂ) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun μ : M => if x + (μ : ℂ) = 0 then 0 else Complex.Gammaℝ s *
      ((starRingEnd ℂ (x + μ)) ^ k * cexp (2 * Real.pi * I * ⟪x + μ, y⟫) *
        ((‖x + (μ : ℂ)‖ : ℝ) : ℂ) ^ (-s)))
      (completedWeightZeta M k x y s) := by
  have hs0 : 0 < s.re := by have := k.cast_nonneg (α := ℝ); linarith
  have hM : mellin (fun t => weightTheta M k x y t - weightConst M k x) (s / 2) =
      (weightThetaFEPair M k x y).Λ (s / 2) := by
    rcases eq_or_ne k 0 with rfl | hk
    · have hk' : (weightThetaFEPair M 0 x y).k < (s / 2).re := by
        simp only [weightThetaFEPair, Complex.div_ofNat_re]
        push_cast at hs ⊢
        linarith
      exact ((weightThetaFEPair M 0 x y).hasMellin hk').2
    · have h := ((isStrongFEPair_weightThetaFEPair M hk x y).hasMellin (s / 2)).2
      simp only [weightConst, hk, ↓reduceIte, sub_zero]
      exact h
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun μ : M => if ‖x + (μ : ℂ)‖ = 0 then 0 else
      (starRingEnd ℂ (x + μ)) ^ k * cexp (2 * Real.pi * I * ⟪x + μ, y⟫) *
        (Real.exp (-Real.pi * ‖x + (μ : ℂ)‖ ^ 2 * t) : ℂ))
      (weightTheta M k x y t - weightConst M k x) := by
    intro t ht
    convert hasSum_weightTheta_sub M k x y ht using 2 with μ
    simp only [norm_eq_zero]
    split_ifs
    · rfl
    · rw [gaussWeight]
      have : (-Real.pi * ‖x + (μ : ℂ)‖ ^ 2 * t) = -(Real.pi * t) * ‖x + (μ : ℂ)‖ ^ 2 := by ring
      rw [this]
      ring
  have hsum : Summable fun μ : M =>
      ‖(starRingEnd ℂ (x + μ)) ^ k * cexp (2 * Real.pi * I * ⟪x + μ, y⟫)‖ /
        |‖x + (μ : ℂ)‖| ^ s.re := by
    have := ZLattice.summable_norm_sub_rpow M (k - s.re)
      (by rw [ZLattice.rank ℝ M, Complex.finrank_real_complex]; push_cast; linarith) (-x)
    refine this.of_nonneg_of_le (fun _ => by positivity) fun μ => ?_
    rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one, norm_pow, Complex.norm_conj, abs_norm,
      sub_neg_eq_add, add_comm (μ : ℂ) x]
    rcases eq_or_ne ‖x + (μ : ℂ)‖ 0 with h | h
    · rw [h, Real.zero_rpow hs0.ne', div_zero]
      exact Real.rpow_nonneg le_rfl _
    · rw [Real.rpow_sub (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)), Real.rpow_natCast]
  have := hasSum_mellin_pi_mul_sq hs0 hF hsum
  rw [hM] at this
  unfold completedWeightZeta
  convert this using 2 with μ
  split_ifs with hμ
  · simp [hμ, Complex.zero_cpow (Complex.ne_zero_of_re_pos hs0)]
  · rw [abs_norm, div_eq_mul_inv, Complex.cpow_neg]
    ring

/-- For $\mathrm{Re}\, s > k + 2$, $\Lambda_M^k(x, y; s) = \Gamma_\mathbb{R}(s) Z_M^k(x, y; s)$. -/
theorem completedWeightZeta_eq (k : ℕ) (x y : ℂ) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    completedWeightZeta M k x y s = Complex.Gammaℝ s * weightZeta M k x y s := by
  rw [weightZeta, ← tsum_mul_left, (hasSum_completedWeightZeta M k x y hs).tsum_eq.symm]
  refine tsum_congr fun μ => ?_
  split_ifs <;> simp

/-- For $k \neq 0$, the completed weighted Epstein zeta function is entire. -/
theorem differentiable_completedWeightZeta {k : ℕ} (hk : k ≠ 0) (x y : ℂ) :
    Differentiable ℂ (completedWeightZeta M k x y) :=
  ((isStrongFEPair_weightThetaFEPair M hk x y).differentiable_Λ).comp
    (differentiable_id.div_const 2)

/-- **The functional equation of the weighted Epstein zeta function.** For $k \neq 0$, $$\Lambda_M^k(x, y; 2k + 2 - s) = (-i)^k \, \mathrm{covol}(M)^{-1} \, e^{2 \pi i \langle x, y \rangle} \, \Lambda_{M^\vee}^k(-y, x; s).$$ -/
theorem completedWeightZeta_sub {k : ℕ} (hk : k ≠ 0) (x y : ℂ) (s : ℂ) :
    completedWeightZeta M k x y (2 * k + 2 - s) =
      (-I) ^ k * ((ZLattice.covolume M)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫) *
        completedWeightZeta (dualLattice M) k (-y) x s := by
  have h := (weightThetaFEPair M k x y).functional_equation (s / 2)
  have hs : (weightThetaFEPair M k x y).symm.Λ =
      (weightThetaFEPair (dualLattice M) k (-y) x).Λ := by
    rw [(isStrongFEPair_weightThetaFEPair M hk x y).symm_Λ_eq,
      (isStrongFEPair_weightThetaFEPair (dualLattice M) hk (-y) x).Λ_eq]
    rfl
  rw [hs] at h
  unfold completedWeightZeta
  have hk2 : ((2 * k + 2 : ℂ) - s) / 2 = ((weightThetaFEPair M k x y).k : ℂ) - s / 2 := by
    simp only [weightThetaFEPair]
    push_cast
    ring
  rw [hk2, h, smul_eq_mul]
  rfl

/-- For $k = 0$ the completed weighted Epstein zeta function is `Langlands.Tate.completedShiftEpsteinZeta`. -/
theorem completedWeightZeta_zero (x y : ℂ) :
    completedWeightZeta M 0 x y = completedShiftEpsteinZeta M x y := by
  have h : (weightThetaFEPair M 0 x y).Λ = (shiftThetaFEPair M x y).Λ := by
    refine weakFEPair_Λ_eq _ _ (funext fun t => weightTheta_zero M x y t) ?_ ?_ ?_ ?_
    · simp [weightThetaFEPair, shiftThetaFEPair, Complex.finrank_real_complex]
    · simp [weightThetaFEPair, shiftThetaFEPair]
    · simp [weightThetaFEPair, shiftThetaFEPair, weightConst]
    · simp [weightThetaFEPair, shiftThetaFEPair, weightConst]
  funext s
  rw [completedWeightZeta, completedShiftEpsteinZeta, h]

end Langlands.Tate
