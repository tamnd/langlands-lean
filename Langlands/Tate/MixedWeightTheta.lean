/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassHeckeWeight
import Langlands.Tate.GlobalLattice

/-!
# Theta series with a harmonic polynomial on the mixed space of a number field

Let $K$ be a number field with $r_1$ real places and $r_2$ complex places, and let $E = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ be the euclidean mixed space (`NumberField.mixedEmbedding.euclidean.mixedSpace`), with the inner product $\langle x, y \rangle = \sum_{v \text{ real}} x_v y_v + \sum_{w \text{ complex}} \mathrm{Re}(x_w \bar y_w)$ and its Lebesgue measure. This is the inner product of the dual lattices in `Langlands.Tate.GlobalLattice`. For $p_v \in \{0, 1\}$ at the real places, $k_w \in \mathbb{N}$ at the complex places and $t_w > 0$ at all places, let $$G_t^{p, k}(x) = \prod_{v \text{ real}} x_v^{p_v} e^{-\pi t_v x_v^2} \prod_{w \text{ complex}} \bar x_w^{k_w} e^{-\pi t_w |x_w|^2}.$$ This file proves Hecke's lemma $\mathcal{F} G_t^{p, k} = c_t^{p, k} G_{1/t}^{p, k}$ and the transformation formula of the theta series $$\theta_L^{p, k}(x, y; t) = \sum_{\ell \in L} G_t^{p, k}(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle}$$ of a full lattice $L \subset E$, with one variable $t_w$ for each place. This is the analytic engine of Hecke's proof of the functional equation of the Hecke $L$-functions of a general number field. It generalizes `Langlands.Tate.weightTheta_eq`, which is the case of the lattices in $\mathbb{C}$.

## Main definitions

* `Langlands.Tate.realGaussWeight`: the function $r^p e^{-\pi t r^2}$ on $\mathbb{R}$.
* `Langlands.Tate.mixedGaussWeight`: the function $G_t^{p, k}$ on $E$.
* `Langlands.Tate.mixedGaussConst`: the constant $c_t^{p, k} = \prod_v (-i)^{p_v} t_v^{-(2 p_v + 1)/2} \prod_w (-i)^{k_w} t_w^{-(k_w + 1)}$.
* `Langlands.Tate.mixedTheta`: the theta series $\theta_L^{p, k}(x, y; t)$.

## Main results

* `fourier_realGaussWeight`: Hecke's lemma at a real place. For $p \in \{0, 1\}$ and $t > 0$, $\mathcal{F}(r^p e^{-\pi t r^2})(\xi) = (-i)^p t^{-(2p + 1)/2} \xi^p e^{-\pi \xi^2 / t}$.
* `fourier_mixed_prod`: the Fourier transform on $E$ of a product $\prod_v f_v(x_v) \prod_w g_w(x_w)$ is the product of the Fourier transforms of the factors.
* `fourier_mixedGaussWeight`: Hecke's lemma on $E$, $\mathcal{F} G_t^{p, k} = c_t^{p, k} G_{1/t}^{p, k}$.
* `mixedGaussConst_eq` and `mixedGaussConst_const`: $c_t^{p, k} = (-i)^{|p| + |k|} (\prod_v t_v^{(2 p_v + 1)/2} \prod_w t_w^{k_w + 1})^{-1}$, and for a common variable $c_t^{p, k} = (-i)^{|p| + |k|} t^{-(r_1 + 2 r_2)/2 - |p| - |k|}$.
* `mixedTheta_eq`: the transformation formula $$\theta_L^{p, k}(x, y; t) = \frac{c_t^{p, k} e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(L)} \, \theta_{L^\vee}^{p, k}(-y, x; 1/t).$$
* `mixedTheta_eq_const`: the same formula for one common variable $t > 0$, with the factor $(-i)^{|p| + |k|} \mathrm{covol}(L)^{-1} t^{-(r_1 + 2 r_2)/2 - |p| - |k|}$.

## Proofs

The real case of Hecke's lemma is `Langlands.Tate.realFourier_realTest` with the dilation $r \mapsto \sqrt t \, r$ (`real_fourier_comp_mul`). The complex case is `Langlands.Tate.fourier_gaussWeight`. For the product formula we move the integral to Mathlib's mixed space $(\mathbb{R}^{r_1}) \times (\mathbb{C}^{r_2})$ with the measure preserving map `NumberField.mixedEmbedding.euclidean.toMixed`. There the character $e^{-2 \pi i \langle x, \xi \rangle}$ is a product over the places (`Langlands.Tate.inner_toMixed_symm`), and Fubini for products (`MeasureTheory.integral_prod_mul` and `MeasureTheory.integral_fintype_prod_volume_eq_prod`) splits the integral. The transformation formula is the Poisson summation formula `Langlands.Tate.tsum_add_zlattice_eq_of_hasDecay`, as in `Langlands.Tate.weightTheta_eq`. The bound $|G_t^{p, k}(x)| \le (1 + |x|)^{|p| + |k|} e^{-\pi m |x|^2}$ with $m = \min_w t_w$ (`norm_mixedGaussWeight_le`) gives the decay and the convergence.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt K` for a general number field. These steps are still open. First, the Mellin transform. For one common variable $t$, the Mellin transform of $\theta_L^{p, k}(x, y; t)$ gives a weighted Epstein zeta function $\sum_{x + \ell \neq 0} P(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle} |x + \ell|^{-s}$ as in `Langlands.Tate.completedWeightZeta`. This is not yet done here, and for $r_1 + r_2 > 1$ it is not the partial Hecke $L$-function, because $|x|$ is not the norm. Hecke's method needs the Mellin transform in the $r_1 + r_2$ variables $t_w$ together, restricted to $\prod_w t_w^{n_w} = $ const, with the exponents $s_w$ of the infinite part of $\chi$. Second, the integration over the unit group: the integral of the theta series over $\mathbb{R}_{>0}^{r_1 + r_2} / \mathcal{O}_K^\times$, a fundamental domain for the action of the units on the variables $t_w$, the compatibility of $\chi_f$ and $\chi_\infty$ on the units, and the regulator in the constant. Third, the transfer to the lattices `Langlands.Tate.globalLattice` with the scaling of the complex coordinates and the identification of the dual lattice with the trace dual. Fourth, the assembly: the weighted Gauss sums, the sum over the ideal classes, the comparison with `Langlands.gammaFactor` and the root number $W = (-i)^{|p| + |k|} \tau(\chi) / \sqrt{N(\mathfrak{f})}$, as in `Langlands.Tate.RayClassHecke`. The case $p_v \ge 2$ is not covered, since $x^p e^{-\pi x^2}$ is not an eigenfunction of the Fourier transform for $p \ge 2$, and the Hecke characters only need $p_v \in \{0, 1\}$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 7 and 8.
-/

open MeasureTheory Module Complex FourierTransform
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace

namespace Langlands.Tate

/-- The Fourier transform on $\mathbb{R}$ under a dilation: for $a \neq 0$, $\mathcal{F}(g(a \cdot))(\xi) = |a|^{-1} \mathcal{F} g(\xi / a)$. -/
theorem real_fourier_comp_mul (g : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (fun r => g (a * r)) ξ = ((|a|)⁻¹ : ℝ) * 𝓕 g (a⁻¹ * ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℝ))
    (fun u : ℝ => cexp (↑(-2 * Real.pi * ⟪u, a⁻¹ * ξ⟫) * I) • g u) a
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at h
  have e : ∀ v : ℝ, cexp (↑(-2 * Real.pi * ⟪v, ξ⟫) * I) • g (a * v) =
      cexp (↑(-2 * Real.pi * ⟪a * v, a⁻¹ * ξ⟫) * I) • g (a * v) := fun v => by
    simp only [RCLike.inner_apply, conj_trivial]
    congr 4
    field_simp
  simp only [smul_eq_mul] at e ⊢
  simp only [e]
  rw [h, abs_inv, Complex.real_smul]


/-- The Gaussian with the polynomial $r^p$ at a real place: the function $r^p e^{-\pi t r^2}$ on $\mathbb{R}$. It is used for $p \in \{0, 1\}$. -/
noncomputable def realGaussWeight (p : ℕ) (t r : ℝ) : ℂ :=
  (r : ℂ) ^ p * (Real.exp (-(Real.pi * t) * r ^ 2) : ℂ)

/-- If $a > 0$ and $a^2 = t$, then $r^p e^{-\pi t r^2} = a^{-p} f_p(a r)$, with the standard test function $f_p(r) = r^p e^{-\pi r^2}$ (`Langlands.Tate.realTest`). -/
theorem realGaussWeight_eq_mul (p : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a ^ 2 = t) :
    realGaussWeight p t = fun r => ((a : ℂ) ^ p)⁻¹ * realTest p (a * r) := by
  funext r
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [realGaussWeight, realTest, Int.toNat_natCast, Complex.ofReal_exp]
  push_cast
  rw [← hat]
  push_cast
  rw [mul_pow, mul_pow]
  field_simp

/-- **Hecke's lemma at a real place.** For $p \in \{0, 1\}$ and $t > 0$, the Fourier transform of $r^p e^{-\pi t r^2}$ is $(-i)^p t^{-(2p + 1)/2} \xi^p e^{-\pi \xi^2 / t}$. -/
theorem fourier_realGaussWeight {p : ℕ} (hp : p ≤ 1) {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (realGaussWeight p t) ξ =
      (-I) ^ p * ((√t ^ (2 * p + 1))⁻¹ : ℝ) * realGaussWeight p (1 / t) ξ := by
  set a := √t
  have ha : 0 < a := Real.sqrt_pos.2 ht
  have hat : a ^ 2 = t := Real.sq_sqrt ht.le
  have hF : 𝓕 (realTest p) = fun y => (-I) ^ p * realTest p y := by
    have h := realFourier_realTest (a := (p : ℤ)) (by omega)
    rw [realFourier_eq_fourier] at h
    rw [h]
    funext y
    interval_cases p <;> simp [realRootNumber]
  rw [realGaussWeight_eq_mul p ha hat]
  have : 𝓕 (fun r => ((a : ℂ) ^ p)⁻¹ * realTest p (a * r)) ξ =
      ((a : ℂ) ^ p)⁻¹ * 𝓕 (fun r => realTest p (a * r)) ξ := by
    rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
    congr 1 with v
    simp only [smul_eq_mul]
    ring
  rw [this, real_fourier_comp_mul _ ha.ne', hF, abs_of_pos ha]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [realGaussWeight, realTest, Int.toNat_natCast, Complex.ofReal_exp]
  push_cast
  have e : -(Real.pi * ((a : ℂ)⁻¹ * ξ) ^ 2) = -(Real.pi * (1 / t)) * ξ ^ 2 := by
    rw [← hat]; push_cast; field_simp
  rw [e, mul_pow, pow_succ (a : ℂ), pow_mul, inv_pow]
  field_simp
  ring


/-- The absolute value of $r^p e^{-\pi t r^2}$ is $|r|^p e^{-\pi t r^2}$. -/
theorem norm_realGaussWeight (p : ℕ) (t r : ℝ) :
    ‖realGaussWeight p t r‖ = |r| ^ p * Real.exp (-(Real.pi * t) * r ^ 2) := by
  rw [realGaussWeight, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

section Summable

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- For $b > 0$ and $r \ge 0$, $(1 + r)^D e^{-b r^2} \le D! \, e^{1 + 1 / (2 b)} e^{-(b/2) r^2}$. -/
theorem one_add_pow_mul_exp_le_half (D : ℕ) {b : ℝ} (hb : 0 < b) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ D * Real.exp (-b * r ^ 2) ≤
      D.factorial * Real.exp (1 + 1 / (4 * (b / 2))) * Real.exp (-(b / 2) * r ^ 2) := by
  have h := one_add_pow_mul_exp_le (half_pos hb) D hr
  have e : Real.exp (-b * r ^ 2) = Real.exp (-(b / 2) * r ^ 2) * Real.exp (-(b / 2) * r ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- For $b > 0$ and $x \in V$, the series $\sum_{\mu \in M} (1 + |x + \mu|)^D e^{-b |x + \mu|^2}$ converges. -/
theorem summable_one_add_pow_mul_exp (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M]
    (D : ℕ) {b : ℝ} (hb : 0 < b) (x : V) :
    Summable fun μ : M => (1 + ‖x + μ‖) ^ D * Real.exp (-b * ‖x + μ‖ ^ 2) :=
  ((summable_exp_neg_mul_norm_add_sq M (half_pos hb) x).mul_left
    (D.factorial * Real.exp (1 + 1 / (4 * (b / 2))))).of_nonneg_of_le
    (fun _ => by positivity) fun _ => one_add_pow_mul_exp_le_half D hb (norm_nonneg _)

end Summable

section Mixed

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The Fourier transform on $\mathbb{R}$ with the character written as a product: $\int_{\mathbb{R}} e^{-2 \pi i r s} h(r) \, dr = \mathcal{F} h(s)$. -/
theorem integral_exp_mul_smul_real (h : ℝ → ℂ) (s : ℝ) :
    ∫ r : ℝ, cexp (↑(-2 * Real.pi * r * s) * I) • h r = 𝓕 h s := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [RCLike.inner_apply, conj_trivial, mul_assoc, mul_comm s r]

/-- The Fourier transform on $\mathbb{C}$ with the real inner product: $\int_{\mathbb{C}} e^{-2 \pi i \langle z, s \rangle} h(z) \, dz = \mathcal{F} h(s)$. -/
theorem integral_exp_inner_smul_complex (h : ℂ → ℂ) (s : ℂ) :
    ∫ z : ℂ, cexp (↑(-2 * Real.pi * ⟪z, s⟫) * I) • h z = 𝓕 h s :=
  (Real.fourier_eq' h s).symm

/-- **The Fourier transform of a product function on the mixed space.** Let $f_v : \mathbb{R} \to \mathbb{C}$ for the real places $v$ and $g_w : \mathbb{C} \to \mathbb{C}$ for the complex places $w$. Then the Fourier transform of $x \mapsto \prod_v f_v(x_v) \prod_w g_w(x_w)$ on the euclidean mixed space is $\xi \mapsto \prod_v \mathcal{F} f_v(\xi_v) \prod_w \mathcal{F} g_w(\xi_w)$. No integrability is necessary: if one factor is not integrable, both sides are $0$ by the conventions of the Bochner integral. -/
theorem fourier_mixed_prod (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  simp only [integral_exp_mul_smul_real, integral_exp_inner_smul_complex]

variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The Gaussian with a harmonic polynomial on the mixed space: $$G_t^{p, k}(x) = \prod_{v \text{ real}} x_v^{p_v} e^{-\pi t_v x_v^2} \prod_{w \text{ complex}} \bar x_w^{k_w} e^{-\pi t_w |x_w|^2},$$ with one variable $t_w$ for each infinite place $w$. -/
noncomputable def mixedGaussWeight (t : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) : ℂ :=
  (∏ v, realGaussWeight (p v) (t v) ((euclidean.toMixed K x).1 v)) *
    ∏ w, gaussWeight (k w) (t w) ((euclidean.toMixed K x).2 w)

/-- The constant of the Fourier transform of $G_t^{p, k}$: $$c_t^{p, k} = \prod_{v \text{ real}} (-i)^{p_v} t_v^{-(2 p_v + 1)/2} \prod_{w \text{ complex}} (-i)^{k_w} t_w^{-(k_w + 1)}.$$ -/
noncomputable def mixedGaussConst (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ v, (-I) ^ p v * ((√(t v) ^ (2 * p v + 1))⁻¹ : ℝ)) *
    ∏ w, (-I) ^ k w * ((t w ^ (k w + 1))⁻¹ : ℝ)

/-- The constant $c_t^{p, k}$ is $(-i)^{|p| + |k|} \big(\prod_v t_v^{(2 p_v + 1)/2} \prod_w t_w^{k_w + 1}\big)^{-1}$, with $|p| = \sum_v p_v$ and $|k| = \sum_w k_w$. -/
theorem mixedGaussConst_eq (t : InfinitePlace K → ℝ) :
    mixedGaussConst p k t = (-I) ^ (∑ v, p v + ∑ w, k w) *
      (((∏ v : {w : InfinitePlace K // IsReal w}, √(t v) ^ (2 * p v + 1)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, t w ^ (k w + 1))⁻¹ : ℝ) := by
  simp only [mixedGaussConst, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add,
    mul_inv, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv, Finset.prod_inv_distrib]
  ring

/-- For one common variable $t \ge 0$, the constant is $c_t^{p, k} = (-i)^{|p| + |k|} t^{-(r_1 + 2 r_2 + 2|p| + 2|k|)/2}$. -/
theorem mixedGaussConst_const {t : ℝ} (ht : 0 ≤ t) :
    mixedGaussConst p k (fun _ => t) = (-I) ^ (∑ v, p v + ∑ w, k w) *
      ((√t ^ (Fintype.card {w : InfinitePlace K // IsReal w} +
        2 * Fintype.card {w : InfinitePlace K // IsComplex w} + 2 * (∑ v, p v + ∑ w, k w)))⁻¹ : ℝ) := by
  rw [mixedGaussConst_eq]
  congr 3
  have h : ∀ n : ℕ, t ^ n = √t ^ (2 * n) := fun n => by rw [pow_mul, Real.sq_sqrt ht]
  simp only [h, Finset.prod_pow_eq_pow_sum, ← pow_add]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]
  ring

/-- **Hecke's lemma on the mixed space.** Let $p_v \in \{0, 1\}$ for each real place and $t_w > 0$ for each place. Then $\mathcal{F} G_t^{p, k} = c_t^{p, k} \, G_{1/t}^{p, k}$. -/
theorem fourier_mixedGaussWeight (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) (ξ : euclidean.mixedSpace K) :
    𝓕 (mixedGaussWeight p k t) ξ =
      mixedGaussConst p k t * mixedGaussWeight p k (fun w => 1 / t w) ξ := by
  have h := fourier_mixed_prod (fun v => realGaussWeight (p v) (t v))
    (fun w => gaussWeight (k w) (t w)) ξ
  refine h.trans ?_
  simp only [fourier_realGaussWeight (hp _) (ht _), fourier_gaussWeight _ (ht _),
    Finset.prod_mul_distrib, mixedGaussConst, mixedGaussWeight]
  ring

/-- If $m \le t_w$ for each place $w$, then $|G_t^{p, k}(x)| \le (1 + |x|)^{|p| + |k|} e^{-\pi m |x|^2}$. -/
theorem norm_mixedGaussWeight_le {t : InfinitePlace K → ℝ} {m : ℝ} (hmt : ∀ w, m ≤ t w)
    (x : euclidean.mixedSpace K) :
    ‖mixedGaussWeight p k t x‖ ≤
      (1 + ‖x‖) ^ (∑ v, p v + ∑ w, k w) * Real.exp (-(Real.pi * m) * ‖x‖ ^ 2) := by
  set y := euclidean.toMixed K x
  have hx : ‖x‖ ^ 2 = ∑ v, y.1 v ^ 2 + ∑ w, ‖y.2 w‖ ^ 2 := by
    rw [← norm_toMixed_symm_sq]; simp [y]
  have h1 : ∀ v, |y.1 v| ≤ 1 + ‖x‖ := fun v => by
    have : |y.1 v| ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [sq_abs, hx]
      have := Finset.single_le_sum (f := fun v => y.1 v ^ 2) (fun i _ => sq_nonneg (y.1 i))
        (Finset.mem_univ v)
      have := Finset.sum_nonneg (s := Finset.univ) (fun w _ => sq_nonneg ‖y.2 w‖)
      linarith
    have := (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg x) two_ne_zero).1 this
    linarith
  have h2 : ∀ w, ‖y.2 w‖ ≤ 1 + ‖x‖ := fun w => by
    have : ‖y.2 w‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hx]
      have := Finset.single_le_sum (f := fun w => ‖y.2 w‖ ^ 2) (fun i _ => sq_nonneg ‖y.2 i‖)
        (Finset.mem_univ w)
      have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => sq_nonneg (y.1 v))
      linarith
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg x) two_ne_zero).1 this
    linarith
  have e : ‖mixedGaussWeight p k t x‖ =
      ((∏ v, |y.1 v| ^ p v) * ∏ w, ‖y.2 w‖ ^ k w) *
        Real.exp (∑ v : {w : InfinitePlace K // IsReal w}, -(Real.pi * t v) * y.1 v ^ 2 +
          ∑ w : {w : InfinitePlace K // IsComplex w}, -(Real.pi * t w) * ‖y.2 w‖ ^ 2) := by
    rw [mixedGaussWeight, norm_mul, norm_prod, norm_prod, Real.exp_add, Real.exp_sum,
      Real.exp_sum]
    simp only [norm_realGaussWeight, norm_gaussWeight, Finset.prod_mul_distrib]
    ring
  rw [e, pow_add]
  gcongr
  · calc ∏ v, |y.1 v| ^ p v ≤ ∏ v, (1 + ‖x‖) ^ p v :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun v _ => pow_le_pow_left₀
            (abs_nonneg _) (h1 v) _
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  · calc ∏ w, ‖y.2 w‖ ^ k w ≤ ∏ w, (1 + ‖x‖) ^ k w :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => pow_le_pow_left₀
            (norm_nonneg _) (h2 w) _
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  · rw [hx, mul_add, Finset.mul_sum, Finset.mul_sum]
    gcongr with v _ w _
    · have := hmt v
      have := sq_nonneg (y.1 v)
      have := Real.pi_pos
      nlinarith
    · have := hmt w
      have := sq_nonneg ‖y.2 w‖
      have := Real.pi_pos
      nlinarith

/-- If $t_w > 0$ for each place $w$, then there is $m > 0$ with $m \le t_w$ for each $w$. -/
theorem exists_pos_forall_le {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ∃ m : ℝ, 0 < m ∧ ∀ w, m ≤ t w := by
  rcases isEmpty_or_nonempty (InfinitePlace K) with h | h
  · exact ⟨1, one_pos, fun w => (IsEmpty.false w).elim⟩
  · obtain ⟨w₀, hw₀⟩ := Finite.exists_min t
    exact ⟨t w₀, ht w₀, hw₀⟩

/-- The function $G_t^{p, k}$ is continuous. -/
theorem continuous_mixedGaussWeight (t : InfinitePlace K → ℝ) :
    Continuous (mixedGaussWeight p k t) := by
  unfold mixedGaussWeight realGaussWeight gaussWeight
  fun_prop

/-- If $t_w > 0$ for each place $w$, then $G_t^{p, k}(v) e^{2 \pi i \langle v, y \rangle}$ decays of each order $N$. -/
theorem hasDecay_mixedGaussWeight_mul {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (y : euclidean.mixedSpace K) (N : ℕ) :
    HasDecay (fun v => mixedGaussWeight p k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)) N := by
  obtain ⟨m, hm, hmt⟩ := exists_pos_forall_le ht
  set D := ∑ v, p v + ∑ w, k w
  refine ⟨(N + D).factorial * Real.exp (1 + 1 / (4 * (Real.pi * m))), fun v => ?_⟩
  rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
  calc (1 + ‖v‖) ^ N * ‖mixedGaussWeight p k t v‖
      ≤ (1 + ‖v‖) ^ N * ((1 + ‖v‖) ^ D * Real.exp (-(Real.pi * m) * ‖v‖ ^ 2)) := by
        gcongr; exact norm_mixedGaussWeight_le p k hmt v
    _ = (1 + ‖v‖) ^ (N + D) * Real.exp (-(Real.pi * m) * ‖v‖ ^ 2) := by ring
    _ ≤ _ := one_add_pow_mul_exp_le (mul_pos Real.pi_pos hm) _ (norm_nonneg v)

/-- If $t_w > 0$ for each place $w$, then the series $\sum_{\ell \in L} G_t^{p, k}(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle}$ converges. -/
theorem summable_mixedGaussWeight (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x y : euclidean.mixedSpace K) :
    Summable fun ℓ : L => mixedGaussWeight p k t (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫) := by
  obtain ⟨m, hm, hmt⟩ := exists_pos_forall_le ht
  refine Summable.of_norm_bounded (summable_one_add_pow_mul_exp L (∑ v, p v + ∑ w, k w)
    (mul_pos Real.pi_pos hm) x) fun ℓ => ?_
  rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
  exact norm_mixedGaussWeight_le p k hmt _

variable (L : Submodule ℤ (euclidean.mixedSpace K))

/-- The theta series of the lattice $L$ in the mixed space with the harmonic polynomial of $(p, k)$, shifted by $x$ and twisted by $y$: $$\theta_L^{p, k}(x, y; t) = \sum_{\ell \in L} G_t^{p, k}(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle}.$$ It is meaningful for $t_w > 0$. -/
noncomputable def mixedTheta (t : InfinitePlace K → ℝ) (x y : euclidean.mixedSpace K) : ℂ :=
  ∑' ℓ : L, mixedGaussWeight p k t (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫)

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The transformation formula of the weighted theta series on the mixed space.** Let $p_v \in \{0, 1\}$ for each real place and $t_w > 0$ for each place. Then $$\theta_L^{p, k}(x, y; t) = \frac{c_t^{p, k} e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(L)} \, \theta_{L^\vee}^{p, k}(-y, x; 1/t).$$ -/
theorem mixedTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x y : euclidean.mixedSpace K) :
    mixedTheta p k L t x y =
      mixedGaussConst p k t * ((ZLattice.covolume L)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫) *
        mixedTheta p k (dualLattice L) (fun w => 1 / t w) (-y) x := by
  set f : euclidean.mixedSpace K → ℂ := fun v =>
    mixedGaussWeight p k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)
  have hc : Continuous f := by
    have := continuous_mixedGaussWeight p k t
    simp only [f]; fun_prop
  have hN : finrank ℝ (euclidean.mixedSpace K) < finrank ℝ (euclidean.mixedSpace K) + 1 :=
    Nat.lt_succ_self _
  have ht' : ∀ w, 0 < 1 / t w := fun w => one_div_pos.2 (ht w)
  have hFf : ∀ w, 𝓕 f w = mixedGaussConst p k t * mixedGaussWeight p k (fun w => 1 / t w) (-y + w) :=
    fun w => by
      rw [fourier_mul_cexp_inner, fourier_mixedGaussWeight p k hp ht, sub_eq_neg_add]
  have hF : Summable fun μ : dualLattice L => 𝓕 f μ := by
    simp only [hFf]
    exact ((summable_mixedGaussWeight p k (dualLattice L) ht' (-y) 0).congr
      fun μ => by simp).mul_left _
  have key := tsum_add_zlattice_eq_of_hasDecay L hc (hasDecay_mixedGaussWeight_mul p k ht y _) hN
    hF x
  rw [mixedTheta, mixedTheta, key]
  simp only [hFf]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun (μ : dualLattice L) => ?_
  have hinner : ⟪x, (μ : euclidean.mixedSpace K)⟫ = ⟪x, y⟫ + ⟪-y + μ, x⟫ := by
    rw [inner_add_left, inner_neg_left, real_inner_comm x y, real_inner_comm x μ]
    ring
  rw [hinner]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- **The transformation formula with one common variable.** For $p_v \in \{0, 1\}$ and $t > 0$, $$\theta_L^{p, k}(x, y; t) = \frac{(-i)^{|p| + |k|} e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(L) \, t^{(r_1 + 2 r_2)/2 + |p| + |k|}} \, \theta_{L^\vee}^{p, k}(-y, x; 1/t).$$ -/
theorem mixedTheta_eq_const (hp : ∀ v, p v ≤ 1) {t : ℝ} (ht : 0 < t)
    (x y : euclidean.mixedSpace K) :
    mixedTheta p k L (fun _ => t) x y =
      (-I) ^ (∑ v, p v + ∑ w, k w) * ((ZLattice.covolume L)⁻¹ *
        (√t ^ (Fintype.card {w : InfinitePlace K // IsReal w} +
          2 * Fintype.card {w : InfinitePlace K // IsComplex w} +
            2 * (∑ v, p v + ∑ w, k w)))⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫) *
        mixedTheta p k (dualLattice L) (fun _ => 1 / t) (-y) x := by
  rw [mixedTheta_eq p k L hp (fun _ => ht), mixedGaussConst_const p k ht.le]
  push_cast
  ring

end Mixed

end Langlands.Tate
