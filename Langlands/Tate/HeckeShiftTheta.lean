/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMixedSignFE

/-!
# The theta series twisted by a character of the norm one torus

Let $K$ be a number field and let $\theta = (\theta_w)_w$ be a real vector indexed by the infinite places. This file twists the signed theta series of `Langlands/Tate/HeckeMixedSignTheta.lean` by the character $$\tau_\theta(t) = \prod_w t_w^{i n_w \theta_w / 2}$$ of the torus $\prod_w \mathbb{R}_{>0}$. On the points $t = (|x|_w^2)_w$ the character is $\prod_w |x|_w^{i n_w \theta_w}$, so it gives the factor $|x|_w^{n_w t_w}$ with the shift $t_w = i \theta_w$ of a Hecke character. The shifts can be different at different places.

The factor has the absolute value $1$, so all the bounds of the signed theta series stay true. Under $t \mapsto 1 / t$ it changes to the factor of $-\theta$. The Mellin transform of a twisted term is a product over the places, and at the place $w$ the variable $s$ becomes $s + i \theta_w$. This gives the Gamma factor $\prod_w \pi^{-z_w} \Gamma(z_w)$ with $z_w = (n_w (s + i \theta_w) + q_w) / 2$, with a different shift at each place.

## Main definitions

* `Langlands.Tate.torusFactor`: the character $\tau_\theta(t) = \exp(i \sum_w n_w \theta_w \log(t_w) / 2)$.
* `Langlands.Tate.torusWeight`: the factor $\prod_w |\alpha|_w^{-i n_w \theta_w}$ of $\alpha \in K^\times$.
* `Langlands.Tate.torusConst`: the constant $\tau_\theta((n_w^2)_w)$.
* `Langlands.Tate.shiftGamma`: the Gamma factor with the shifts $i \theta_w$.
* `Langlands.Tate.shiftHeckeTerm`, `Langlands.Tate.shiftHeckeTheta`, `Langlands.Tate.shiftHeckeDualTheta`: the twisted terms, theta series and dual theta series.

## Main results

* `Langlands.Tate.integral_shiftHeckeTerm_mul_prod`: the Mellin transform of a twisted term over $(0, \infty)^{S_\infty}$.
* `Langlands.Tate.integral_unitScale_shiftHeckeTerm`: the same Mellin transform in the unit coordinates.
* `Langlands.Tate.shiftHeckeTerm_mul`: the action of $K^\times$ on the twisted terms.
* `Langlands.Tate.shiftHeckeTheta_unit`: the periodicity under a unit $u$ with $\chi_\infty(u) \tau(u) = 1$.
* `Langlands.Tate.shiftHeckeTheta_unitScale`: the transformation formula of the twisted theta series.
* `Langlands.Tate.shiftHeckeDualTheta_eq`: the twisted dual theta series as a conjugate twisted theta series.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Torus

variable {K : Type*} [Field K] [NumberField K]

/-- The character of the torus with the shifts $i \theta_w$: $$\tau_\theta(t) = \exp\Big(i \sum_w \frac{n_w \theta_w}{2} \log t_w\Big).$$ For $t_w > 0$ this is $\prod_w t_w^{i n_w \theta_w / 2}$. -/
noncomputable def torusFactor (θ t : InfinitePlace K → ℝ) : ℂ :=
  cexp ((∑ w, (mult w : ℝ) * θ w / 2 * Real.log (t w) : ℝ) * I)

/-- The factor of $\alpha$ for the shifts $i \theta_w$: $$\tau_\theta(\alpha) = \exp\Big(-i \sum_w n_w \theta_w \log |\alpha|_w\Big).$$ For $\alpha \neq 0$ this is $\prod_w |\alpha|_w^{-i n_w \theta_w}$. -/
noncomputable def torusWeight (θ : InfinitePlace K → ℝ) (α : K) : ℂ :=
  cexp (-((∑ w, (mult w : ℝ) * θ w * Real.log (w α) : ℝ) * I))

/-- The constant $\tau_\theta((n_w^2)_w)$ of the change of variable to the dual theta series. -/
noncomputable def torusConst (θ : InfinitePlace K → ℝ) : ℂ :=
  torusFactor θ fun w => (mult w : ℝ) ^ 2

/-- The character of the torus has the absolute value $1$. -/
theorem norm_torusFactor (θ t : InfinitePlace K → ℝ) : ‖torusFactor θ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The factor $\tau_\theta(\alpha)$ has the absolute value $1$. -/
theorem norm_torusWeight (θ : InfinitePlace K → ℝ) (α : K) : ‖torusWeight θ α‖ = 1 := by
  rw [torusWeight, ← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The factor $\tau_\theta(\alpha)$ is not zero. -/
theorem torusWeight_ne_zero (θ : InfinitePlace K → ℝ) (α : K) : torusWeight θ α ≠ 0 :=
  Complex.exp_ne_zero _

/-- The constant $\tau_\theta((n_w^2)_w)$ has the absolute value $1$. -/
theorem norm_torusConst (θ : InfinitePlace K → ℝ) : ‖torusConst θ‖ = 1 :=
  norm_torusFactor _ _

/-- The character at $1 / t$ is the character of $-\theta$ at $t$. -/
theorem torusFactor_inv (θ t : InfinitePlace K → ℝ) :
    torusFactor θ (fun w => (t w)⁻¹) = torusFactor (-θ) t := by
  rw [torusFactor, torusFactor]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.log_inv, Pi.neg_apply]
  ring

/-- The complex conjugate of the character of $\theta$ is the character of $-\theta$. -/
theorem conj_torusFactor (θ t : InfinitePlace K → ℝ) :
    conj (torusFactor θ t) = torusFactor (-θ) t := by
  rw [torusFactor, torusFactor, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  rw [mul_neg, ← neg_mul, ← Complex.ofReal_neg, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Pi.neg_apply]
  ring

/-- The complex conjugate of $\tau_\theta(\alpha)$ is $\tau_{-\theta}(\alpha)$. -/
theorem conj_torusWeight (θ : InfinitePlace K → ℝ) (α : K) :
    conj (torusWeight θ α) = torusWeight (-θ) α := by
  rw [torusWeight, torusWeight, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  rw [mul_neg, neg_neg, ← neg_mul, ← Complex.ofReal_neg, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Pi.neg_apply]
  ring

/-- The characters of $\theta$ and $-\theta$ are inverse to each other. -/
theorem torusFactor_mul_neg (θ t : InfinitePlace K → ℝ) :
    torusFactor θ t * torusFactor (-θ) t = 1 := by
  rw [← conj_torusFactor, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_torusFactor]
  norm_num

/-- The character is multiplicative on the points with positive coordinates. -/
theorem torusFactor_mul (θ : InfinitePlace K → ℝ) {t u : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) (hu : ∀ w, 0 < u w) :
    torusFactor θ (fun w => t w * u w) = torusFactor θ t * torusFactor θ u := by
  rw [torusFactor, torusFactor, torusFactor, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
    ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.log_mul (ht w).ne' (hu w).ne']
  ring

/-- **The action of $K^\times$ on the character.** For $t_w > 0$ and $\beta \neq 0$, $\tau_\theta((t_w |\beta|_w^2)_w) = \tau_\theta(t) \, \tau_\theta(\beta)^{-1}$. -/
theorem torusFactor_mul_sq (θ : InfinitePlace K → ℝ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) {β : K} (hβ : β ≠ 0) :
    torusFactor θ (fun w => t w * w β ^ 2) = torusFactor θ t * (torusWeight θ β)⁻¹ := by
  rw [torusWeight, Complex.exp_neg, inv_inv, torusFactor, torusFactor, ← Complex.exp_add,
    ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  have hb : 0 < w β := InfinitePlace.pos_iff.2 hβ
  rw [Real.log_mul (ht w).ne' (pow_ne_zero _ hb.ne'), Real.log_pow]
  push_cast
  ring

/-- The factor $\tau_\theta$ is multiplicative on $K^\times$. -/
theorem torusWeight_mul (θ : InfinitePlace K → ℝ) {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    torusWeight θ (α * β) = torusWeight θ α * torusWeight θ β := by
  rw [torusWeight, torusWeight, torusWeight, ← Complex.exp_add, ← neg_add, ← add_mul,
    ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 4
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, Real.log_mul (InfinitePlace.pos_iff.2 hα).ne' (InfinitePlace.pos_iff.2 hβ).ne']
  ring

/-- **The character at $(n_w^2 t_w)_w$.** For $t_w > 0$, $\tau_{-\theta}(t) = \tau_\theta((n_w^2)_w) \, \overline{\tau_\theta((n_w^2 t_w)_w)}$. -/
theorem torusFactor_neg_eq (θ : InfinitePlace K → ℝ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    torusFactor (-θ) t = torusConst θ * conj (torusFactor θ fun w => (mult w : ℝ) ^ 2 * t w) := by
  have hm : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) ^ 2 := fun w => by
    have := one_le_mult_sq w
    linarith
  rw [conj_torusFactor, torusFactor_mul (-θ) hm ht, torusConst, ← mul_assoc,
    torusFactor_mul_neg, one_mul]

/-- The factor $\tau_\theta$ of a root of unity is $1$. -/
theorem torusWeight_torsion (θ : InfinitePlace K → ℝ) (ζ : torsion K) :
    torusWeight θ (((ζ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
  rw [torusWeight]
  simp [(mem_torsion K).1 ζ.2]

/-- The character as a product over the places, for $t_w > 0$. -/
theorem torusFactor_eq_prod (θ : InfinitePlace K → ℝ) (t : InfinitePlace K → ℝ) :
    torusFactor θ t = ∏ w, cexp (((mult w : ℝ) * θ w / 2 * Real.log (t w) : ℝ) * I) := by
  rw [torusFactor, ← Complex.exp_sum, Complex.ofReal_sum, Finset.sum_mul]

end Torus

section Gamma

variable {K : Type*} [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The Gamma factor of the weight $(p, k)$ with the shifts $i \theta_w$: $$\Gamma_{p, k}^\theta(s) = \prod_w \pi^{-z_w} \, \Gamma(z_w), \qquad z_w = (n_w (s + i \theta_w) + q_w) / 2.$$ -/
noncomputable def shiftGamma (θ : InfinitePlace K → ℝ) (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K, (π : ℂ) ^ (-heckeExp p k (s + θ w * I) w) *
    Complex.Gamma (heckeExp p k (s + θ w * I) w)

variable {p k}

/-- The conjugate of the shifted Gamma factor: $\overline{\Gamma_{p, k}^\theta(\bar{s})} = \Gamma_{p, k}^{-\theta}(s)$. -/
theorem conj_shiftGamma (θ : InfinitePlace K → ℝ) (s : ℂ) :
    conj (shiftGamma p k θ (conj s)) = shiftGamma p k (-θ) s := by
  have he : ∀ w, heckeExp p k (conj s + θ w * I) w =
      conj (heckeExp p k (s + ((-θ) w : ℝ) * I) w) := fun w => by
    simp only [heckeExp, map_div₀, map_add, map_mul, map_natCast, map_ofNat, Pi.neg_apply,
      Complex.ofReal_neg, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  simp only [shiftGamma, map_prod, map_mul, he, ← map_neg, conj_ofReal_cpow Real.pi_pos.le,
    Complex.Gamma_conj, Complex.conj_conj]

/-- For $\theta = 0$ the shifted Gamma factor is the Gamma factor of the weight. -/
theorem shiftGamma_zero (s : ℂ) : shiftGamma p k (0 : InfinitePlace K → ℝ) s = heckeGamma p k s := by
  simp [shiftGamma, heckeGamma]

end Gamma

section Weighted

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (θ : InfinitePlace K → ℝ)

/-- The twisted term $\tau_\theta(t) \, h_t(\alpha)$ of $\alpha$, where $h_t(\alpha)$ is `Langlands.Tate.signHeckeTerm`. -/
noncomputable def shiftHeckeTerm (α : K) (t : InfinitePlace K → ℝ) : ℂ :=
  torusFactor θ t * signHeckeTerm ε p k α t

variable {ε p k θ}

/-- The twisted term has the absolute value of the term. -/
theorem norm_shiftHeckeTerm (α : K) (t : InfinitePlace K → ℝ) :
    ‖shiftHeckeTerm ε p k θ α t‖ = ‖signHeckeTerm ε p k α t‖ := by
  rw [shiftHeckeTerm, norm_mul, norm_torusFactor, one_mul]

/-- The twisted term has the extended absolute value of the term. -/
theorem enorm_shiftHeckeTerm (α : K) (t : InfinitePlace K → ℝ) :
    ‖shiftHeckeTerm ε p k θ α t‖ₑ = ‖signHeckeTerm ε p k α t‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_shiftHeckeTerm]

/-- For $t_w > 0$, the twisted term times $\prod_w t_w^{n_w s / 2 - 1}$ is the product over the places of $t_w^{z_w(s + i \theta_w) - 1} g_w(t_w, \alpha)$. -/
theorem shiftHeckeTerm_mul_prod {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (α : K) (s : ℂ) :
    shiftHeckeTerm ε p k θ α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) =
      ∏ w, (t w : ℂ) ^ (heckeExp p k (s + θ w * I) w - 1) * signPlaceGauss ε p k (t w) α w := by
  rw [shiftHeckeTerm, mul_assoc, signHeckeTerm_mul_prod ht, signMixedGaussWeight_eq_prod,
    torusFactor_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : (t w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ht w).ne'
  have e : heckeExp p k (s + θ w * I) w - 1 =
      (heckeExp p k s w - 1) + (((mult w : ℝ) * θ w / 2 : ℝ) : ℂ) * I := by
    simp only [heckeExp]
    push_cast
    ring
  have e2 : (t w : ℂ) ^ ((((mult w : ℝ) * θ w / 2 : ℝ) : ℂ) * I) =
      cexp (((mult w : ℝ) * θ w / 2 * Real.log (t w) : ℝ) * I) := by
    rw [ofReal_cpow_eq_exp (ht w)]
    push_cast
    ring_nf
  rw [e, cpow_add _ _ hne, e2]
  ring

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the twisted term times $\prod_w t_w^{n_w s / 2 - 1}$ is integrable on $(0, \infty)^{S_\infty}$. -/
theorem integrable_shiftHeckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ =>
        shiftHeckeTerm ε p k θ α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have hs' : ∀ w, 0 < (s + θ w * I).re := fun w => by simpa using hs
  have h := Integrable.fintype_prod (f := fun (w : InfinitePlace K) (t : ℝ) =>
    (t : ℂ) ^ (heckeExp p k (s + θ w * I) w - 1) * signPlaceGauss ε p k t α w)
    (μ := fun _ => volume.restrict (Ioi (0 : ℝ))) (fun w => integrableOn_signPlaceGauss (hs' w) hα w)
  refine h.congr ?_
  filter_upwards [ae_pi_Ioi_pos] with t ht
  exact (shiftHeckeTerm_mul_prod ht α s).symm

/-- **The Mellin transform of a twisted term.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} \tau_\theta(t) \, h_t(\alpha) \prod_w t_w^{n_w s / 2} \, \frac{dt_w}{t_w} = \Gamma_{p, k}^\theta(s) \, \chi_\infty(\alpha) \, \tau_\theta(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s}.$$ -/
theorem integral_shiftHeckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, shiftHeckeTerm ε p k θ α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      shiftGamma p k θ s * signInfinityWeight ε p k α * torusWeight θ α *
        ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  have hs' : ∀ w, 0 < (s + θ w * I).re := fun w => by simpa using hs
  rw [integral_congr_ae (g := fun t : InfinitePlace K → ℝ => ∏ w,
      (t w : ℂ) ^ (heckeExp p k (s + θ w * I) w - 1) * signPlaceGauss ε p k (t w) α w)
      (by filter_upwards [ae_pi_Ioi_pos] with t ht; exact shiftHeckeTerm_mul_prod ht α s),
    integral_fintype_prod_eq_prod (fun w (t : ℝ) =>
      (t : ℂ) ^ (heckeExp p k (s + θ w * I) w - 1) * signPlaceGauss ε p k t α w),
    Finset.prod_congr rfl fun w _ => integral_signPlaceGauss (hs' w) hα w]
  have hD : ∀ w : InfinitePlace K, cexp (-((s + θ w * I) * (mult w * Real.log (w α)))) =
      cexp (-(s * (mult w * Real.log (w α)))) *
        cexp (-(((mult w : ℝ) * θ w * Real.log (w α) : ℝ) * I)) := fun w => by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h1 : ∏ w : InfinitePlace K, cexp (-(s * (mult w * Real.log (w α)))) =
      ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
    rw [← Complex.exp_sum, ofReal_cpow_eq_exp (abs_norm_pos hα), ← sum_mult_log α hα]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h2 : ∏ w : InfinitePlace K, cexp (-(((mult w : ℝ) * θ w * Real.log (w α) : ℝ) * I)) =
      torusWeight θ α := by
    rw [← Complex.exp_sum, torusWeight]
    congr 1
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  simp_rw [hD]
  simp only [shiftGamma, signInfinityWeight, Finset.prod_mul_distrib]
  rw [h1, h2]
  ring

/-- **The Mellin transform of a twisted term in the unit coordinates.** For $\mathrm{Re}\, s > 0$, $\alpha \neq 0$ and $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} \tau_\theta(t(y, c)) \, h_{t(y, c)}(\alpha) \, dc \, dy = \Gamma_{p, k}^\theta(s') \, \chi_\infty(\alpha) \, \tau_\theta(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s'}.$$ -/
theorem integral_unitScale_shiftHeckeTerm {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ α (unitScale K y c) =
      shiftGamma p k θ (2 * s / finrank ℚ K) * signInfinityWeight ε p k α * torusWeight θ α *
        ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)) := by
  have hre : 0 < (2 * s / finrank ℚ K).re := by
    rw [Complex.div_natCast_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    have := finrank_pos (R := ℚ) (M := K)
    positivity
  rw [integral_unitScale_eq (fun t => shiftHeckeTerm ε p k θ α t)
      (integrable_shiftHeckeTerm_mul_prod hre hα),
    integral_shiftHeckeTerm_mul_prod hre hα]

/-- **The action of $K^\times$ on the twisted terms.** For $\beta \neq 0$ and $t_w > 0$, $$\tau_\theta(t) \, h_t(\beta \alpha) = \chi_\infty(\beta) \, \tau_\theta(\beta) \, \tau_\theta(t |\beta|^2) \, h_{t |\beta|^2}(\alpha).$$ -/
theorem shiftHeckeTerm_mul {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) {β : K} (hβ : β ≠ 0)
    (α : K) :
    shiftHeckeTerm ε p k θ (β * α) t = signInfinityWeight ε p k β * torusWeight θ β *
      shiftHeckeTerm ε p k θ α (fun w => t w * w β ^ 2) := by
  have hw := torusWeight_ne_zero θ β
  rw [shiftHeckeTerm, signHeckeTerm_mul (fun w => (ht w).le) hβ, shiftHeckeTerm,
    torusFactor_mul_sq θ ht hβ]
  field_simp

end Weighted

section Theta

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (θ : InfinitePlace K → ℝ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The twisted theta series $\tau_\theta(t) \, \Theta_{\mathfrak{a}}^{p, k}(t)$ of $\mathfrak{a}$. -/
noncomputable def shiftHeckeTheta (t : InfinitePlace K → ℝ) : ℂ :=
  torusFactor θ t * signHeckeTheta K ε p k a t

/-- The twisted dual theta series $\tau_{-\theta}(t) \, \Theta_{\mathfrak{a}}^{\vee, p, k}(t)$. The shifts change sign. -/
noncomputable def shiftHeckeDualTheta (t : InfinitePlace K → ℝ) : ℂ :=
  torusFactor (-θ) t * signHeckeDualTheta K ε p k a t

/-- The twisted theta series is the sum of the twisted terms. -/
theorem shiftHeckeTheta_eq_tsum (t : InfinitePlace K → ℝ) :
    shiftHeckeTheta K ε p k θ a t =
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), shiftHeckeTerm ε p k θ (α : K) t := by
  rw [shiftHeckeTheta, signHeckeTheta_eq_tsum, ← tsum_mul_left]
  rfl

variable {K ε p k θ}

/-- The twisted theta series has the absolute value of the theta series. -/
theorem norm_shiftHeckeTheta (t : InfinitePlace K → ℝ) :
    ‖shiftHeckeTheta K ε p k θ a t‖ = ‖signHeckeTheta K ε p k a t‖ := by
  rw [shiftHeckeTheta, norm_mul, norm_torusFactor, one_mul]

/-- The twisted dual theta series has the absolute value of the dual theta series. -/
theorem norm_shiftHeckeDualTheta (t : InfinitePlace K → ℝ) :
    ‖shiftHeckeDualTheta K ε p k θ a t‖ = ‖signHeckeDualTheta K ε p k a t‖ := by
  rw [shiftHeckeDualTheta, norm_mul, norm_torusFactor, one_mul]

/-- **The periodicity under a unit.** If $u$ is a unit with $\chi_\infty(u) \tau_\theta(u) = 1$ and $t_w > 0$ for all $w$, then the twisted theta series takes the same value at $(t_w |u|_w^2)_w$ and at $t$. -/
theorem shiftHeckeTheta_unit (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : (𝓞 K)ˣ}
    (hu : signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    shiftHeckeTheta K ε p k θ b (fun w => t w * w (u : K) ^ 2) = shiftHeckeTheta K ε p k θ b t := by
  rw [shiftHeckeTheta_eq_tsum, shiftHeckeTheta_eq_tsum]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) u).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [shiftHeckeTerm_mul ht (coe_ne_zero u), hu, one_mul]

/-- **The transformation formula of the twisted theta series in the unit coordinates.** Let $p_v \in \{0, 1\}$ and $y > 0$. Then $$\tau_\theta(t(y, c)) \, \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|} \, \sqrt{y}^{\,n}} \, \tau_{-\theta}(t(y^{-1}, -c)) \, \Theta_{\mathfrak{a}}^{\vee, p, k}(t(y^{-1}, -c)).$$ -/
theorem shiftHeckeTheta_unitScale (hp : ∀ v, p v ≤ 1) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    shiftHeckeTheta K ε p k θ a (unitScale K y c) =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) * shiftHeckeDualTheta K ε p k θ a (unitScale K y⁻¹ (-c)) := by
  have h : torusFactor θ (unitScale K y c) = torusFactor (-θ) (unitScale K y⁻¹ (-c)) := by
    rw [← torusFactor_inv]
    congr 1
    funext w
    rw [unitScale_inv, inv_inv, neg_neg]
  rw [shiftHeckeTheta, signHeckeTheta_unitScale a hp hy c, shiftHeckeDualTheta, h]
  ring

/-- **The twisted dual theta series.** For $t_w > 0$, the twisted dual theta series of $\mathfrak{a}$ at $t$ is $\tau_\theta((n_w^2)_w)$ times the complex conjugate of the twisted theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ at $(n_w^2 t_w)_w$. -/
theorem shiftHeckeDualTheta_eq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    shiftHeckeDualTheta K ε p k θ a t =
      torusConst θ * conj (shiftHeckeTheta K ε p k θ (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  rw [shiftHeckeDualTheta, signHeckeDualTheta_eq ε p k a (fun w => (ht w).le), shiftHeckeTheta,
    map_mul, torusFactor_neg_eq θ ht]
  ring

end Theta

end Langlands.Tate
