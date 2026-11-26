/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.IdealWeightTheta
import Langlands.Tate.UnitUnfold

/-!
# The Mellin transform of a weighted Hecke term in the unit coordinates

Let $K$ be a number field of degree $n$ with $r_2$ complex places, unit rank $r$ and regulator $R_K$. Fix a weight $(p, k)$, with $p_v \in \mathbb{N}$ at the real places and $k_w \in \mathbb{N}$ at the complex places, and let $q_w$ be $p_w$ or $k_w$. For $\alpha \in K$ and $t \in (0, \infty)^{S_\infty}$, the normalized term of the weighted theta function is $h_t(\alpha) = \prod_w t_w^{q_w / 2} \cdot G_t(\alpha)$, where $G_t$ is the mixed Gaussian weight of `Langlands/Tate/MixedWeightTheta.lean`. This file computes the Mellin transform of $h_t(\alpha)$ in the variables $t$ and in the unit coordinates $(y, c)$. For $\alpha \neq 0$ and $\mathrm{Re}\, s > 0$, with $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc \, dy = \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ Here $\Gamma_{p, k}(s) = \prod_w \pi^{-z_w} \Gamma(z_w)$ with $z_w = (n_w s + q_w) / 2$, and $\chi_\infty(\alpha) = \prod_v \mathrm{sgn}(\sigma_v \alpha)^{p_v} \prod_w (\overline{\sigma_w \alpha} / |\sigma_w \alpha|)^{k_w}$ is the infinity type. The file also proves that $h$ is equivariant under the multiplication by $K^\times$, that it is periodic in $c$ under the units on which $\chi_\infty$ is trivial, and that the normalized theta function satisfies the transformation formula in $t$ and in $(y, c)$.

## Main definitions

* `Langlands.Tate.weightExp`: the exponent $q_w$ at a place.
* `Langlands.Tate.heckeExp`: the Mellin exponent $z_w(s) = (n_w s + q_w) / 2$.
* `Langlands.Tate.heckeGamma`: the Gamma factor $\Gamma_{p, k}(s) = \prod_w \pi^{-z_w(s)} \Gamma(z_w(s))$.
* `Langlands.Tate.placePhase`, `Langlands.Tate.infinityWeight`: the phase at a place and the infinity type $\chi_\infty$.
* `Langlands.Tate.placeGauss`, `Langlands.Tate.placeTerm`: the weight at a place, without and with the factor $t^{q_w / 2}$.
* `Langlands.Tate.heckeTerm`: the normalized term $h_t(\alpha)$.
* `Langlands.Tate.heckeTheta`, `Langlands.Tate.heckeDualTheta`: the normalized theta functions $\sum_{\alpha \in \mathfrak{a}} h_t(\alpha)$ and its dual.

## Main results

* `Langlands.Tate.integral_cpow_mul_realGaussWeight`, `Langlands.Tate.integral_cpow_mul_gaussWeight`: the Gamma identity at one place.
* `Langlands.Tate.integral_prod_cpow_mul_mixedGaussWeight`: the Mellin transform of $G_t(\alpha)$ over $(0, \infty)^{S_\infty}$.
* `Langlands.Tate.integral_unitScale_eq`: the change of variables to $(y, c)$ for a general integrand.
* `Langlands.Tate.integral_unitScale_heckeTerm`: the formula above.
* `Langlands.Tate.infinityWeight_mul`: $\chi_\infty$ is multiplicative.
* `Langlands.Tate.heckeTerm_mul`: $h_t(\beta \alpha) = \chi_\infty(\beta) h_{t |\beta|^2}(\alpha)$.
* `Langlands.Tate.heckeTerm_unitOfInt_mul`: the periodicity in $c$ under a unit $\varepsilon$ with $\chi_\infty(\varepsilon) = 1$.
* `Langlands.Tate.heckeTheta_eq`, `Langlands.Tate.heckeTheta_unitScale`: the transformation formula of the normalized theta function.

## Proof

At one place the integral is Euler's integral for $\Gamma$ after the substitution $u = \pi r^2 t$. Fubini's theorem on the product measure gives the product over the places, and the product of the factors $|\alpha|_w^{-n_w s}$ is $|N(\alpha)|^{-s}$. The change of variables uses Mathlib's map `expMapBasis`, as in `Langlands/Tate/UnitMellin.lean`, but for any integrable integrand. The equivariance is a computation at each place. The transformation formula follows from `Langlands.Tate.idealTheta_eq`.

## Open parts

This file does not yet prove the functional equation. The missing steps are these.
* The unfolding of the sum over $(\mathfrak{a} \setminus 0) / U$ into one integral of the theta function, and the interchange of the sum and the integrals. This needs an absolute convergence bound for $\mathrm{Re}\, s > n / 2$, and $\chi_\infty$ trivial on all units, torsion included.
* The term $\alpha = 0$, which is zero when $(p, k) \neq 0$.
* The identification of the dual theta function with the normalized theta function of the dual ideal for the conjugate weight.
* The pair of theta functions as an FE pair, the analytic continuation and the symmetry $s \leftrightarrow 1 - s$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section OneVariable

/-- A computation for one place: for $r > 0$, $q \in \mathbb{N}$, $n \in \mathbb{N}$ and $z = (n s + q) / 2$, $$r^q (\pi r^2)^{-z} = \pi^{-z} e^{-s n \log r}.$$ -/
theorem ofReal_pow_mul_cpow_eq {r : ℝ} (hr : 0 < r) (q n : ℕ) (s : ℂ) :
    (r : ℂ) ^ q * ((π * r ^ 2 : ℝ) : ℂ) ^ (-(((n : ℂ) * s + q) / 2)) =
      (π : ℂ) ^ (-(((n : ℂ) * s + q) / 2)) * cexp (-(s * (n * Real.log r))) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg Real.pi_pos.le (by positivity),
    ofReal_cpow_eq_exp (pow_pos hr 2), Real.log_pow, ← cpow_natCast,
    ofReal_cpow_eq_exp hr, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The real weight times a power, as a constant times a Gamma integrand: $t^{z - 1} r^p e^{-\pi t r^2} = r^p \cdot t^{z - 1} e^{-\pi r^2 t}$. -/
theorem cpow_mul_realGaussWeight (p : ℕ) (z : ℂ) (t r : ℝ) :
    (t : ℂ) ^ (z - 1) * realGaussWeight p t r =
      (r : ℂ) ^ p * ((t : ℂ) ^ (z - 1) * (Real.exp (-((π * r ^ 2) * t)) : ℂ)) := by
  simp only [realGaussWeight]
  rw [show -(π * t) * r ^ 2 = -(π * r ^ 2 * t) by ring]
  ring

/-- The complex weight times a power, as a constant times a Gamma integrand: $t^{z - 1} \bar v^k e^{-\pi t |v|^2} = \bar v^k \cdot t^{z - 1} e^{-\pi |v|^2 t}$. -/
theorem cpow_mul_gaussWeight (k : ℕ) (z : ℂ) (t : ℝ) (v : ℂ) :
    (t : ℂ) ^ (z - 1) * gaussWeight k t v =
      (starRingEnd ℂ v) ^ k * ((t : ℂ) ^ (z - 1) * (Real.exp (-((π * ‖v‖ ^ 2) * t)) : ℂ)) := by
  simp only [gaussWeight]
  rw [show -(π * t) * ‖v‖ ^ 2 = -(π * ‖v‖ ^ 2 * t) by ring]
  ring

/-- **The Mellin transform of the real weight.** For $\mathrm{Re}\, z > 0$ and $r \neq 0$, $$\int_0^\infty t^{z - 1} r^p e^{-\pi t r^2} \, dt = r^p (\pi r^2)^{-z} \, \Gamma(z).$$ -/
theorem integral_cpow_mul_realGaussWeight (p : ℕ) {z : ℂ} (hz : 0 < z.re) {r : ℝ} (hr : r ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * realGaussWeight p t r =
      (r : ℂ) ^ p * ((π * r ^ 2 : ℝ) : ℂ) ^ (-z) * Complex.Gamma z := by
  have hpos : 0 < π * r ^ 2 := by positivity
  simp_rw [cpow_mul_realGaussWeight]
  rw [integral_const_mul, integral_Ioi_cpow_mul_exp hz hpos, ofReal_cpow_eq_exp hpos, neg_mul]
  ring

/-- **The Mellin transform of the complex weight.** For $\mathrm{Re}\, z > 0$ and $v \neq 0$, $$\int_0^\infty t^{z - 1} \bar v^k e^{-\pi t |v|^2} \, dt = \bar v^k (\pi |v|^2)^{-z} \, \Gamma(z).$$ -/
theorem integral_cpow_mul_gaussWeight (k : ℕ) {z : ℂ} (hz : 0 < z.re) {v : ℂ} (hv : v ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * gaussWeight k t v =
      (starRingEnd ℂ v) ^ k * ((π * ‖v‖ ^ 2 : ℝ) : ℂ) ^ (-z) * Complex.Gamma z := by
  have hpos : 0 < π * ‖v‖ ^ 2 := by positivity
  simp_rw [cpow_mul_gaussWeight]
  rw [integral_const_mul, integral_Ioi_cpow_mul_exp hz hpos, ofReal_cpow_eq_exp hpos, neg_mul]
  ring

/-- For $\mathrm{Re}\, z > 0$ and $r \neq 0$, the function $t^{z - 1} r^p e^{-\pi t r^2}$ is integrable on $(0, \infty)$. -/
theorem integrableOn_cpow_mul_realGaussWeight (p : ℕ) {z : ℂ} (hz : 0 < z.re) {r : ℝ}
    (hr : r ≠ 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * realGaussWeight p t r) (Ioi 0) := by
  simp_rw [cpow_mul_realGaussWeight]
  exact (integrableOn_cpow_mul_exp hz (by positivity)).const_mul _

/-- For $\mathrm{Re}\, z > 0$ and $v \neq 0$, the function $t^{z - 1} \bar v^k e^{-\pi t |v|^2}$ is integrable on $(0, \infty)$. -/
theorem integrableOn_cpow_mul_gaussWeight (k : ℕ) {z : ℂ} (hz : 0 < z.re) {v : ℂ}
    (hv : v ≠ 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * gaussWeight k t v) (Ioi 0) := by
  simp_rw [cpow_mul_gaussWeight]
  exact (integrableOn_cpow_mul_exp hz (by positivity)).const_mul _

end OneVariable

section Places

variable {K : Type*} [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The weight $q_w$ at a place: $q_v = p_v$ at a real place and $q_w = k_w$ at a complex place. -/
noncomputable def weightExp (w : InfinitePlace K) : ℕ :=
  if h : IsReal w then p ⟨w, h⟩ else k ⟨w, not_isReal_iff_isComplex.1 h⟩

/-- The exponent $z_w(s) = (n_w s + q_w) / 2$ of the Mellin transform at the place $w$. -/
noncomputable def heckeExp (s : ℂ) (w : InfinitePlace K) : ℂ :=
  ((mult w : ℂ) * s + weightExp p k w) / 2

/-- The Gamma factor of the weight $(p, k)$: $$\Gamma_{p, k}(s) = \prod_w \pi^{-z_w(s)} \, \Gamma(z_w(s)), \qquad z_w(s) = (n_w s + q_w) / 2.$$ -/
noncomputable def heckeGamma (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K, (π : ℂ) ^ (-heckeExp p k s w) * Complex.Gamma (heckeExp p k s w)

/-- The phase of $\alpha$ at a place: $(\sigma_v(\alpha) / |\sigma_v(\alpha)|)^{p_v}$ at a real place $v$ and $(\overline{\sigma_w(\alpha)} / |\sigma_w(\alpha)|)^{k_w}$ at a complex place $w$. -/
noncomputable def placePhase (α : K) (w : InfinitePlace K) : ℂ :=
  if h : IsReal w then ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩
  else (starRingEnd ℂ (w.embedding α) / (w α : ℂ)) ^ k ⟨w, not_isReal_iff_isComplex.1 h⟩

/-- The infinity type of the weight $(p, k)$ at $\alpha$: $$\chi_\infty(\alpha) = \prod_{v \text{ real}} \Big(\frac{\sigma_v(\alpha)}{|\sigma_v(\alpha)|}\Big)^{p_v} \prod_{w \text{ complex}} \Big(\frac{\overline{\sigma_w(\alpha)}}{|\sigma_w(\alpha)|}\Big)^{k_w}.$$ -/
noncomputable def infinityWeight (α : K) : ℂ :=
  ∏ w : InfinitePlace K, placePhase p k α w

/-- The factor of the weight at one place: $g_{p_v, t}(\sigma_v(\alpha))$ at a real place and $\overline{\sigma_w(\alpha)}^{k_w} e^{-\pi t |\sigma_w(\alpha)|^2}$ at a complex place. -/
noncomputable def placeGauss (t : ℝ) (α : K) (w : InfinitePlace K) : ℂ :=
  if h : IsReal w then realGaussWeight (p ⟨w, h⟩) t (embedding_of_isReal h α)
  else gaussWeight (k ⟨w, not_isReal_iff_isComplex.1 h⟩) t (w.embedding α)

/-- The infinity type as a product over the real places and the complex places. -/
theorem infinityWeight_eq (α : K) :
    infinityWeight p k α =
      (∏ v : {w : InfinitePlace K // IsReal w},
        ((embedding_of_isReal v.2 α / v.1 α : ℝ) : ℂ) ^ p v) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        (starRingEnd ℂ (w.1.embedding α) / (w.1 α : ℂ)) ^ k w := by
  rw [infinityWeight, prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by simp [placePhase, v.2]
  · exact Finset.prod_congr rfl fun w _ => by
      simp [placePhase, not_isReal_iff_isComplex.2 w.2]

/-- The weight $G_t^{p, k}$ at $\sigma(\alpha)$ is the product of the factors at the places. -/
theorem mixedGaussWeight_eq_prod (t : InfinitePlace K → ℝ) (α : K) :
    mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α) =
      ∏ w, placeGauss p k (t w) α w := by
  rw [mixedGaussWeight_globalEmbedding, prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by simp [placeGauss, v.2]
  · exact Finset.prod_congr rfl fun w _ => by
      simp [placeGauss, not_isReal_iff_isComplex.2 w.2]

variable {p k}

omit [NumberField K] in
/-- If $\mathrm{Re}\, s > 0$, then $\mathrm{Re}\, z_w(s) > 0$. -/
theorem heckeExp_re_pos {s : ℂ} (hs : 0 < s.re) (w : InfinitePlace K) :
    0 < (heckeExp p k s w).re := by
  have h : ((mult w : ℂ) * s + weightExp p k w).re = mult w * s.re + weightExp p k w := by
    simp [Complex.mul_re]
  rw [heckeExp, Complex.div_ofNat_re, h]
  have := mult_pos (w := w)
  positivity

omit [NumberField K] in
/-- **The Mellin transform at one place.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_0^\infty t^{z_w(s) - 1} g_w(t, \alpha) \, dt = \pi^{-z_w(s)} \Gamma(z_w(s)) \, \chi_w(\alpha) \, e^{-s n_w \log |\alpha|_w},$$ where $g_w$ is `placeGauss` and $\chi_w$ is `placePhase`. -/
theorem integral_placeGauss {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) (w : InfinitePlace K) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (heckeExp p k s w - 1) * placeGauss p k t α w =
      (π : ℂ) ^ (-heckeExp p k s w) * Complex.Gamma (heckeExp p k s w) * placePhase p k α w *
        cexp (-(s * (mult w * Real.log (w α)))) := by
  have ha : 0 < w α := InfinitePlace.pos_iff.2 hα
  have hz := heckeExp_re_pos (p := p) (k := k) hs w
  by_cases h : IsReal w
  · have hr : embedding_of_isReal h α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_of_isReal]; exact ha.ne'
    simp only [placeGauss, placePhase, h, ↓reduceDIte]
    rw [integral_cpow_mul_realGaussWeight _ hz hr]
    have habs : |embedding_of_isReal h α| = w α := by
      rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
    have h1 : (embedding_of_isReal h α : ℂ) ^ p ⟨w, h⟩ =
        ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩ * (w α : ℂ) ^ p ⟨w, h⟩ := by
      rw [← mul_pow, ← Complex.ofReal_mul, div_mul_cancel₀ _ ha.ne']
    have h2 : (embedding_of_isReal h α) ^ 2 = w α ^ 2 := by rw [← habs, sq_abs]
    have h3 : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
    have h4 := ofReal_pow_mul_cpow_eq ha (p ⟨w, h⟩) (mult w) s
    rw [h1, h2]
    simp only [heckeExp, h3] at h4 ⊢
    linear_combination ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩ *
      Complex.Gamma (((mult w : ℂ) * s + (p ⟨w, h⟩ : ℕ)) / 2) * h4
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 h
    have hv : w.embedding α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_eq]; exact ha.ne'
    simp only [placeGauss, placePhase, h, ↓reduceDIte]
    rw [integral_cpow_mul_gaussWeight _ hz hv, norm_embedding_eq]
    have h1 : (starRingEnd ℂ (w.embedding α)) ^ k ⟨w, hc⟩ =
        (starRingEnd ℂ (w.embedding α) / (w α : ℂ)) ^ k ⟨w, hc⟩ * (w α : ℂ) ^ k ⟨w, hc⟩ := by
      rw [← mul_pow, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 ha.ne')]
    have h3 : weightExp p k w = k ⟨w, hc⟩ := by simp [weightExp, h]
    have h4 := ofReal_pow_mul_cpow_eq ha (k ⟨w, hc⟩) (mult w) s
    rw [h1]
    simp only [heckeExp, h3] at h4 ⊢
    linear_combination (starRingEnd ℂ (w.embedding α) / (w α : ℂ)) ^ k ⟨w, hc⟩ *
      Complex.Gamma (((mult w : ℂ) * s + (k ⟨w, hc⟩ : ℕ)) / 2) * h4

omit [NumberField K] in
/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `integral_placeGauss` is integrable on $(0, \infty)$. -/
theorem integrableOn_placeGauss {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0)
    (w : InfinitePlace K) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (heckeExp p k s w - 1) * placeGauss p k t α w)
      (Ioi 0) := by
  have ha : 0 < w α := InfinitePlace.pos_iff.2 hα
  have hz := heckeExp_re_pos (p := p) (k := k) hs w
  by_cases h : IsReal w
  · have hr : embedding_of_isReal h α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_of_isReal]; exact ha.ne'
    simp only [placeGauss, h, ↓reduceDIte]
    exact integrableOn_cpow_mul_realGaussWeight _ hz hr
  · have hv : w.embedding α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_eq]; exact ha.ne'
    simp only [placeGauss, h, ↓reduceDIte]
    exact integrableOn_cpow_mul_gaussWeight _ hz hv

/-- **The Mellin transform of a weighted theta term.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} \prod_w t_w^{z_w(s) - 1} \, G_t^{p, k}(\sigma(\alpha)) \, dt = \Gamma_{p, k}(s) \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s},$$ with $z_w(s) = (n_w s + q_w) / 2$. -/
theorem integral_prod_cpow_mul_mixedGaussWeight {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      heckeGamma p k s * infinityWeight p k α * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  have h : (fun t : InfinitePlace K → ℝ => (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
      mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α)) =
      fun t => ∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1) * placeGauss p k (t w) α w := by
    funext t
    rw [mixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]
  rw [h, integral_fintype_prod_eq_prod (fun w (t : ℝ) =>
    (t : ℂ) ^ (heckeExp p k s w - 1) * placeGauss p k t α w)]
  simp_rw [integral_placeGauss hs hα]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, heckeGamma,
    infinityWeight, ofReal_cpow_eq_exp (abs_norm_pos hα)]
  congr 2
  rw [← sum_mult_log α hα]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `integral_prod_cpow_mul_mixedGaussWeight` is integrable. -/
theorem integrable_prod_cpow_mul_mixedGaussWeight {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ => (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have h := Integrable.fintype_prod (f := fun (w : InfinitePlace K) (t : ℝ) =>
    (t : ℂ) ^ (heckeExp p k s w - 1) * placeGauss p k t α w)
    (μ := fun _ => volume.restrict (Ioi (0 : ℝ))) (fun w => integrableOn_placeGauss hs hα w)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [mixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]

end Places

section Change

variable {K : Type*} [Field K] [NumberField K]

/-- **The change of variables $t = E(x)$ for a general integrand.** For every function $F$ on $\mathbb{R}^{S_\infty}$, $$2^{-r_2} n R_K \int_{\mathbb{R}^{S_\infty}} F(E(x)) \, e^{n s x_{w_0} / 2} \, dx = \int_{(0, \infty)^{S_\infty}} F(t) \prod_w t_w^{n_w s / 2 - 1} \, dt,$$ where $E$ is Mathlib's `expMapBasis`. -/
theorem unitConst_mul_integral_expMapBasis_eq (F : (InfinitePlace K → ℝ) → ℂ) (s : ℂ) :
    (unitConst K : ℂ) * ∫ x : realSpace K, F (expMapBasis x) *
        cexp ((finrank ℚ K : ℂ) * s / 2 * x w₀) =
      ∫ t : InfinitePlace K → ℝ, F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn
    (fun t : realSpace K => F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
  rw [image_expMapBasis, volume_pi, Measure.restrict_pi_pi, Measure.restrict_univ] at h
  refine Eq.trans ?_ h.symm
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul]
  linear_combination -F (expMapBasis x) * abs_det_mul_prod_cpow x s

/-- If $F(t) \prod_w t_w^{n_w s / 2 - 1}$ is integrable on $(0, \infty)^{S_\infty}$, then $F(E(x)) e^{n s x_{w_0} / 2}$ is integrable on $\mathbb{R}^{S_\infty}$. -/
theorem integrable_expMapBasis_of_integrable {F : (InfinitePlace K → ℝ) → ℂ} {s : ℂ}
    (hF : Integrable (fun t : InfinitePlace K → ℝ =>
        F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ)))) :
    Integrable fun x : realSpace K => F (expMapBasis x) *
      cexp ((finrank ℚ K : ℂ) * s / 2 * x w₀) := by
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn
    (fun t : realSpace K => F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))).1
  rw [image_expMapBasis, IntegrableOn, volume_pi, Measure.restrict_pi_pi, IntegrableOn,
    Measure.restrict_univ] at h
  have h' := (h hF).const_mul ((unitConst K : ℂ)⁻¹)
  refine h'.congr (Eventually.of_forall fun x => ?_)
  have hC : (unitConst K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (unitConst_pos K).ne'
  simp only [Complex.real_smul]
  rw [show ∀ a b c : ℂ, (unitConst K : ℂ)⁻¹ * (a * (b * c)) = (unitConst K : ℂ)⁻¹ * b * (a * c)
    from fun a b c => by ring, abs_det_mul_prod_cpow]
  field_simp

/-- **The change of variables to the norm and the unit coordinates.** Let $s' = 2 s / n$. If $F(t) \prod_w t_w^{n_w s' / 2 - 1}$ is integrable on $(0, \infty)^{S_\infty}$, then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} F(t(y, c)) \, dc \, dy = \int_{(0, \infty)^{S_\infty}} F(t) \prod_w t_w^{n_w s' / 2 - 1} \, dt,$$ with $t(y, c)_w = y \exp(2 \sum_i c_i \log |\varepsilon_i|_w)$ as in `Langlands.Tate.unitScale`. -/
theorem integral_unitScale_eq (F : (InfinitePlace K → ℝ) → ℂ) {s : ℂ}
    (hF : Integrable (fun t : InfinitePlace K → ℝ =>
        F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * (2 * s / finrank ℚ K) / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ)))) :
    ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, F (unitScale K y c) =
      ∫ t : InfinitePlace K → ℝ, F t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * (2 * s / finrank ℚ K) / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have key : (finrank ℚ K : ℂ) * (2 * s / finrank ℚ K) / 2 = s := by
    field_simp
  have hA := unitConst_mul_integral_expMapBasis_eq F (2 * s / finrank ℚ K)
  have hI := integrable_expMapBasis_of_integrable hF
  rw [key] at hA hI
  rw [← hA]
  set G : realSpace K → ℂ := fun x => F (expMapBasis x) * cexp (s * x w₀) with hG
  have hmp := (measurePreserving_unitCoord K).symm
  have h1 : ∫ x, G x = ∫ p : ℝ × (Fin (rank K) → ℝ), G ((unitCoord K).symm p) :=
    (hmp.integral_comp' G).symm
  have hI' : Integrable (fun p => G ((unitCoord K).symm p)) (volume.prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hI
  rw [h1, Measure.volume_eq_prod, integral_prod _ hI']
  have h2 : ∀ v : ℝ, ∫ u : Fin (rank K) → ℝ, G ((unitCoord K).symm (v, u)) =
      (2 ^ rank K : ℂ) * (cexp (s * v) * ∫ c, F (unitScale K (Real.exp v) c)) := by
    intro v
    have h := Measure.integral_comp_smul (μ := volume)
      (fun c : Fin (rank K) → ℝ => G ((unitCoord K).symm (v, (2 : ℝ) • c))) (2⁻¹ : ℝ)
    simp only [smul_smul, mul_inv_cancel₀ (two_ne_zero (α := ℝ)), one_smul,
      finrank_fin_fun] at h
    rw [h]
    simp only [hG, expMapBasis_unitCoord_symm, unitCoord_symm_w₀]
    rw [integral_mul_const, inv_pow, inv_inv, abs_of_pos (by positivity), Complex.real_smul]
    push_cast
    ring
  simp_rw [h2]
  rw [integral_const_mul]
  have h3 : ∫ v : ℝ, cexp (s * v) * ∫ c, F (unitScale K (Real.exp v) c) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * ∫ c, F (unitScale K y c) := by
    rw [← integral_comp_exp]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [Complex.real_smul, ofReal_cpow_eq_exp (Real.exp_pos v), Real.log_exp, ← mul_assoc,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    ring
  rw [h3]
  push_cast
  ring

end Change

section Weighted

variable {K : Type*} [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The normalized term of $\alpha$ in the weighted theta series: $$h_t(\alpha) = \prod_w t_w^{q_w / 2} \, G_t^{p, k}(\sigma(\alpha)).$$ At a real place the factor is $(\sqrt{t_v} \sigma_v(\alpha))^{p_v} e^{-\pi t_v \sigma_v(\alpha)^2}$, and at a complex place it is $(\sqrt{t_w} \overline{\sigma_w(\alpha)})^{k_w} e^{-\pi t_w |\sigma_w(\alpha)|^2}$. -/
noncomputable def heckeTerm (α : K) (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
    mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α)

variable {p k}

/-- On the measure of $(0, \infty)^{S_\infty}$, almost every point has all coordinates positive. -/
theorem ae_pi_Ioi_pos :
    ∀ᵐ t ∂(Measure.pi fun _ : InfinitePlace K => volume.restrict (Ioi (0 : ℝ))), ∀ w, 0 < t w := by
  rw [← Measure.restrict_pi_pi]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)] with t ht
  exact fun w => ht w (mem_univ w)

/-- For $t_w > 0$, $h_t(\alpha) \prod_w t_w^{n_w s / 2 - 1} = \prod_w t_w^{z_w(s) - 1} \, G_t^{p, k}(\sigma(\alpha))$. -/
theorem heckeTerm_mul_prod {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (α : K) (s : ℂ) :
    heckeTerm p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) =
      (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        mixedGaussWeight p k t (globalEmbedding K (fun _ => 1) α) := by
  have h : ∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1) =
      (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← cpow_add _ _ (Complex.ofReal_ne_zero.2 (ht w).ne'), heckeExp]
    congr 1
    ring
  rw [h, heckeTerm]
  ring

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the function $h_t(\alpha) \prod_w t_w^{n_w s / 2 - 1}$ is integrable on $(0, \infty)^{S_\infty}$. -/
theorem integrable_heckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ =>
        heckeTerm p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  refine (integrable_prod_cpow_mul_mixedGaussWeight (p := p) (k := k) hs hα).congr ?_
  filter_upwards [ae_pi_Ioi_pos] with t ht
  exact (heckeTerm_mul_prod ht α s).symm

/-- **The Mellin transform of a normalized weighted theta term.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} h_t(\alpha) \prod_w t_w^{n_w s / 2} \, \frac{dt_w}{t_w} = \Gamma_{p, k}(s) \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s}.$$ -/
theorem integral_heckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, heckeTerm p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      heckeGamma p k s * infinityWeight p k α * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [← integral_prod_cpow_mul_mixedGaussWeight (p := p) (k := k) hs hα]
  refine integral_congr_ae ?_
  filter_upwards [ae_pi_Ioi_pos] with t ht
  exact heckeTerm_mul_prod ht α s

/-- **The Mellin transform of a weighted theta term in the unit coordinates.** For $\mathrm{Re}\, s > 0$, $\alpha \neq 0$ and $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc \, dy = \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s'}.$$ -/
theorem integral_unitScale_heckeTerm {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, heckeTerm p k α (unitScale K y c) =
      heckeGamma p k (2 * s / finrank ℚ K) * infinityWeight p k α *
        ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)) := by
  have hre : 0 < (2 * s / finrank ℚ K).re := by
    rw [Complex.div_natCast_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    have := finrank_pos (R := ℚ) (M := K)
    positivity
  rw [integral_unitScale_eq _ (integrable_heckeTerm_mul_prod hre hα),
    integral_heckeTerm_mul_prod hre hα]

end Weighted

section Equivariance

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- For $a > 0$, $(a^2)^{q / 2} = a^q$. -/
theorem ofReal_sq_cpow_half {a : ℝ} (ha : 0 < a) (q : ℕ) :
    ((a ^ 2 : ℝ) : ℂ) ^ ((q : ℂ) / 2) = (a : ℂ) ^ q := by
  rw [ofReal_cpow_eq_exp (by positivity), Real.log_pow, ← cpow_natCast, ofReal_cpow_eq_exp ha]
  congr 1
  push_cast
  ring

omit [NumberField K] in
/-- The phase is multiplicative: $\chi_w(\alpha \beta) = \chi_w(\alpha) \chi_w(\beta)$. -/
theorem placePhase_mul (α β : K) (w : InfinitePlace K) :
    placePhase p k (α * β) w = placePhase p k α w * placePhase p k β w := by
  by_cases h : IsReal w
  · simp only [placePhase, h, ↓reduceDIte, map_mul, ← mul_pow, ← Complex.ofReal_mul,
      mul_div_mul_comm]
  · simp only [placePhase, h, ↓reduceDIte, map_mul, ← mul_pow, Complex.ofReal_mul,
      mul_div_mul_comm]

/-- **The infinity type is multiplicative.** $\chi_\infty(\alpha \beta) = \chi_\infty(\alpha) \chi_\infty(\beta)$. -/
theorem infinityWeight_mul (α β : K) :
    infinityWeight p k (α * β) = infinityWeight p k α * infinityWeight p k β := by
  simp only [infinityWeight, placePhase_mul, Finset.prod_mul_distrib]

variable (p k) in
/-- The factor of the normalized term at one place: $t^{q_w / 2} g_w(t, \alpha)$. -/
noncomputable def placeTerm (t : ℝ) (α : K) (w : InfinitePlace K) : ℂ :=
  (t : ℂ) ^ ((weightExp p k w : ℂ) / 2) * placeGauss p k t α w

/-- The normalized term is the product of the factors at the places. -/
theorem heckeTerm_eq_prod (α : K) (t : InfinitePlace K → ℝ) :
    heckeTerm p k α t = ∏ w, placeTerm p k (t w) α w := by
  rw [heckeTerm, mixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]
  rfl

omit [NumberField K] in
/-- The action of $\beta \neq 0$ at one place: for $t \ge 0$, $$t^{q_w / 2} g_w(t, \beta \alpha) = \chi_w(\beta) \, (t |\beta|_w^2)^{q_w / 2} g_w(t |\beta|_w^2, \alpha).$$ -/
theorem placeTerm_mul {t : ℝ} (ht : 0 ≤ t) {β : K} (hβ : β ≠ 0) (α : K) (w : InfinitePlace K) :
    placeTerm p k t (β * α) w = placePhase p k β w * placeTerm p k (t * w β ^ 2) α w := by
  have hb : 0 < w β := InfinitePlace.pos_iff.2 hβ
  have hb' : (w β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hc : ((t * w β ^ 2 : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2) =
      (t : ℂ) ^ ((weightExp p k w : ℂ) / 2) * (w β : ℂ) ^ weightExp p k w := by
    rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht (by positivity), ofReal_sq_cpow_half hb]
  by_cases h : IsReal w
  · have h3 : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
    have habs : (embedding_of_isReal h β) ^ 2 = w β ^ 2 := by
      rw [← norm_embedding_of_isReal h β, Real.norm_eq_abs, sq_abs]
    have he : -(π * t) * (embedding_of_isReal h (β * α)) ^ 2 =
        -(π * (t * w β ^ 2)) * (embedding_of_isReal h α) ^ 2 := by
      rw [map_mul, mul_pow, habs]
      ring
    simp only [placeTerm, placeGauss, placePhase, h, ↓reduceDIte, realGaussWeight] at hc ⊢
    rw [hc, he, h3, map_mul, Complex.ofReal_mul, Complex.ofReal_div]
    field_simp
    have key : ((embedding_of_isReal h β : ℂ) / (w β : ℂ)) ^ p ⟨w, h⟩ * (w β : ℂ) ^ p ⟨w, h⟩ =
        (embedding_of_isReal h β : ℂ) ^ p ⟨w, h⟩ := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hb')]
    linear_combination -((t : ℂ) ^ ((p ⟨w, h⟩ : ℂ) / 2) *
      (embedding_of_isReal h α : ℂ) ^ p ⟨w, h⟩) * key
  · have hcx : IsComplex w := not_isReal_iff_isComplex.1 h
    have h3 : weightExp p k w = k ⟨w, hcx⟩ := by simp [weightExp, h]
    have he : -(π * t) * ‖w.embedding (β * α)‖ ^ 2 =
        -(π * (t * w β ^ 2)) * ‖w.embedding α‖ ^ 2 := by
      rw [map_mul, norm_mul, norm_embedding_eq w β]
      ring
    simp only [placeTerm, placeGauss, placePhase, h, ↓reduceDIte, gaussWeight] at hc ⊢
    rw [hc, he, h3, map_mul, map_mul]
    field_simp
    have key : (starRingEnd ℂ (w.embedding β) / (w β : ℂ)) ^ k ⟨w, hcx⟩ *
        (w β : ℂ) ^ k ⟨w, hcx⟩ = (starRingEnd ℂ (w.embedding β)) ^ k ⟨w, hcx⟩ := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hb')]
    linear_combination -((t : ℂ) ^ ((k ⟨w, hcx⟩ : ℂ) / 2) *
      (starRingEnd ℂ (w.embedding α)) ^ k ⟨w, hcx⟩) * key

/-- **The action of $K^\times$ on the normalized terms.** For $\beta \neq 0$ and $t_w \ge 0$, $$h_t(\beta \alpha) = \chi_\infty(\beta) \, h_{t |\beta|^2}(\alpha),$$ where $(t |\beta|^2)_w = t_w |\beta|_w^2$. -/
theorem heckeTerm_mul {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) {β : K} (hβ : β ≠ 0)
    (α : K) :
    heckeTerm p k (β * α) t = infinityWeight p k β * heckeTerm p k α (fun w => t w * w β ^ 2) := by
  simp only [heckeTerm_eq_prod, infinityWeight, placeTerm_mul (ht _) hβ, Finset.prod_mul_distrib]

/-- **The periodicity in the unit coordinates.** Let $u = \prod_i \varepsilon_i^{m_i}$. If $\chi_\infty(u) = 1$ and $y \ge 0$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$. -/
theorem heckeTerm_unitOfInt_mul {m : Fin (rank K) → ℤ}
    (hu : infinityWeight p k (unitOfInt K m : K) = 1) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin (rank K) → ℝ) (α : K) :
    heckeTerm p k ((unitOfInt K m : K) * α) (unitScale K y c) =
      heckeTerm p k α (unitScale K y (c + fun i => (m i : ℝ))) := by
  rw [heckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le) (coe_ne_zero _), hu, one_mul]
  congr 1
  funext w
  rw [unitScale_add_int]

end Equivariance

section Theta

variable (K : Type*) [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The normalized weighted theta series of $\mathfrak{a}$: $\Theta_{\mathfrak{a}}^{p, k}(t) = \prod_w t_w^{q_w / 2} \, \theta_{\mathfrak{a}, 1}^{p, k}(0, 0; t)$. -/
noncomputable def heckeTheta (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * idealTheta K p k 1 a t 0 0

/-- The normalized dual theta series: $\Theta_{\mathfrak{a}}^{\vee, p, k}(t) = \prod_w t_w^{q_w / 2} \, \theta_{\mathfrak{a}, 1}^{\vee, p, k}(0, 0; t)$. It is a sum over $(\mathfrak{a} \mathfrak{d})^{-1}$ of the weight $G_t^{p, k}$ at $D_n \overline{\sigma(\beta)}$. -/
noncomputable def heckeDualTheta (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * idealDualTheta K p k 1 a t 0 0

/-- The normalized theta series is the sum of the normalized terms: $\Theta_{\mathfrak{a}}^{p, k}(t) = \sum_{\alpha \in \mathfrak{a}} h_t(\alpha)$. -/
theorem heckeTheta_eq_tsum (t : InfinitePlace K → ℝ) :
    heckeTheta K p k a t = ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), heckeTerm p k (α : K) t := by
  have h1 : (fun w => ((1 : InfinitePlace K → ℝˣ) w : ℝ)) = fun _ => 1 := by
    funext w
    simp
  rw [heckeTheta, idealTheta, ← tsum_mul_left]
  refine tsum_congr fun α => ?_
  simp only [h1, zero_add, mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero,
    Complex.exp_zero, mul_one, heckeTerm]

variable {K p k}

/-- The normalizing factor at the places: for $t_w > 0$, $$\prod_w t_w^{q_w / 2} \, c_t^{p, k} = (-i)^{|p| + |k|} \Big(\prod_w \sqrt{t_w}^{\,n_w}\Big)^{-1} \prod_w (1 / t_w)^{q_w / 2}.$$ -/
theorem prod_cpow_mul_mixedGaussConst {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * mixedGaussConst p k t =
      (-I) ^ (∑ v, p v + ∑ w, k w) * (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) *
        ∏ w, ((1 / t w : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2) := by
  have hs : ∀ w, 0 < √(t w) := fun w => Real.sqrt_pos.2 (ht w)
  have e1 : ∀ w, ((t w : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2) =
      (√(t w) : ℂ) ^ weightExp p k w := fun w => by
    rw [← ofReal_sq_cpow_half (hs w), Real.sq_sqrt (ht w).le]
  have e2 : ∀ w, ((1 / t w : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2) =
      ((1 / √(t w) : ℝ) : ℂ) ^ weightExp p k w := fun w => by
    rw [← ofReal_sq_cpow_half (one_div_pos.2 (hs w)), div_pow, one_pow, Real.sq_sqrt (ht w).le]
  simp_rw [e1, e2]
  rw [mixedGaussConst, prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun w => √(t w) ^ mult w),
    prod_eq_prod_mul_prod (fun w => ((1 / √(t w) : ℝ) : ℂ) ^ weightExp p k w)]
  have hr : ∀ v : {w : InfinitePlace K // IsReal w}, weightExp p k v.1 = p v := fun v => by
    simp [weightExp, v.2]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, weightExp p k w.1 = k w := fun w => by
    simp [weightExp, not_isReal_iff_isComplex.2 w.2]
  simp only [hr, hc, fun v : {w : InfinitePlace K // IsReal w} => mult_isReal v,
    fun w : {w : InfinitePlace K // IsComplex w} => mult_isComplex w]
  have HR : ∀ v : {w : InfinitePlace K // IsReal w},
      (√(t v.1) : ℂ) ^ p v * ((-I) ^ p v * (((√(t v.1) ^ (2 * p v + 1))⁻¹ : ℝ) : ℂ)) =
        (-I) ^ p v * (((√(t v.1) ^ 1)⁻¹ : ℝ) : ℂ) * ((1 / √(t v.1) : ℝ) : ℂ) ^ p v := by
    intro v
    have h' : (√(t v.1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hs v.1).ne'
    push_cast
    simp only [one_div, inv_pow]
    field_simp
    ring
  have HC : ∀ w : {w : InfinitePlace K // IsComplex w},
      (√(t w.1) : ℂ) ^ k w * ((-I) ^ k w * (((t w.1 ^ (k w + 1))⁻¹ : ℝ) : ℂ)) =
        (-I) ^ k w * (((√(t w.1) ^ 2)⁻¹ : ℝ) : ℂ) * ((1 / √(t w.1) : ℝ) : ℂ) ^ k w := by
    intro w
    have h' : (√(t w.1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hs w.1).ne'
    have h2 : ((t w.1 : ℝ) : ℂ) = (√(t w.1) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (ht w.1).le]
    push_cast
    rw [h2]
    simp only [one_div, inv_pow]
    field_simp
    ring
  calc _ = (∏ v : {w : InfinitePlace K // IsReal w},
          (√(t v.1) : ℂ) ^ p v * ((-I) ^ p v * (((√(t v.1) ^ (2 * p v + 1))⁻¹ : ℝ) : ℂ))) *
        ∏ w : {w : InfinitePlace K // IsComplex w},
          (√(t w.1) : ℂ) ^ k w * ((-I) ^ k w * (((t w.1 ^ (k w + 1))⁻¹ : ℝ) : ℂ)) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = (∏ v : {w : InfinitePlace K // IsReal w},
          (-I) ^ p v * (((√(t v.1) ^ 1)⁻¹ : ℝ) : ℂ) * ((1 / √(t v.1) : ℝ) : ℂ) ^ p v) *
        ∏ w : {w : InfinitePlace K // IsComplex w},
          (-I) ^ k w * (((√(t w.1) ^ 2)⁻¹ : ℝ) : ℂ) * ((1 / √(t w.1) : ℝ) : ℂ) ^ k w := by
        simp_rw [HR, HC]
    _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add, mul_inv,
          Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_prod, Finset.prod_inv_distrib]
        ring

/-- **The transformation formula of the normalized theta series.** Let $p_v \in \{0, 1\}$ and $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(t) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{a}}^{\vee, p, k}(1/t).$$ The weight of the Mellin transform changes from $\prod_w t_w^{n_w s / 2}$ to $\prod_w t_w^{n_w (1 - s) / 2}$ under $t \mapsto 1/t$. -/
theorem heckeTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    heckeTheta K p k a t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) * heckeDualTheta K p k a (fun w => 1 / t w) := by
  rw [heckeTheta, idealTheta_one_eq K p k a hp ht 0 0, heckeDualTheta]
  simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  linear_combination
    ((((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
      idealDualTheta K p k 1 a (fun w => 1 / t w) 0 0 * prod_cpow_mul_mixedGaussConst (p := p) (k := k) ht

/-- **The transformation formula in the unit coordinates.** Let $p_v \in \{0, 1\}$ and $y > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|} \, \sqrt{y}^{\,n}} \, \Theta_{\mathfrak{a}}^{\vee, p, k}(t(y^{-1}, -c)).$$ -/
theorem heckeTheta_unitScale (hp : ∀ v, p v ≤ 1) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    heckeTheta K p k a (unitScale K y c) =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) * heckeDualTheta K p k a (unitScale K y⁻¹ (-c)) := by
  have h : (fun w => 1 / unitScale K y c w) = unitScale K y⁻¹ (-c) := by
    funext w
    rw [one_div, unitScale_inv]
  rw [heckeTheta_eq a hp (unitScale_pos hy c), prod_sqrt_unitScale hy.le, h]

end Theta

end Langlands.Tate
