/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.UnitTheta
import Langlands.Tate.DedekindMellin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# The Mellin transform of a theta term in the unit coordinates

Let $K$ be a number field of degree $n$ with $r_2$ complex places, unit rank $r$ and regulator $R_K$. The unit theta function $\Theta_{\mathfrak{a}}$ of `Langlands/Tate/UnitTheta.lean` is an integral over $c \in [0, 1)^r$ of the theta function at the point $t(y, c)_w = y \exp(2 \sum_i c_i \log |\varepsilon_i|_w)$. In Hecke's proof, the sum over the units and the integral over $[0, 1)^r$ together give an integral over all $c \in \mathbb{R}^r$ for each orbit of the units. This file computes that integral for one term. For $\alpha \neq 0$, $\mathrm{Re}\, s > 0$ and $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} e^{-\pi \sum_w n_w t(y, c)_w |\alpha|_w^2} \, dc \, dy = \Gamma_K(s') \, |N(\alpha)|^{-s'}.$$

## Main definitions

* `Langlands.Tate.thetaTerm`: the term $e^{-\pi \sum_w n_w t_w |\alpha|_w^2}$ of the theta function.
* `Langlands.Tate.unitConst`: the constant $2^{-r_2} n R_K$.
* `Langlands.Tate.unitCoord`: the coordinates $(x_{w_0}, x_{w_1}, \dots, x_{w_r})$ of $\mathbb{R}^{S_\infty}$.

## Main results

* `Langlands.Tate.unitConst_mul_integral_expMapBasis`: the formula in the coordinates of Mathlib's `expMapBasis`.
* `Langlands.Tate.integrable_thetaTerm_expMapBasis`: the integrand is integrable.
* `Langlands.Tate.integral_unitScale`: the formula above.

## Proof

Mathlib's map `expMapBasis` sends $x \in \mathbb{R}^{S_\infty}$ to $E(x)_w = e^{x_{w_0}} \prod_i |\varepsilon_i|_w^{x_{w_i}}$. It is a diffeomorphism onto $(0, \infty)^{S_\infty}$, and its Jacobian is $2^{-r_2} n R_K e^{n x_{w_0}} \prod_{w \text{ complex}} E(x)_w^{-1}$. The product formula gives $\prod_w E(x)_w^{n_w} = e^{n x_{w_0}}$. So the change of variables $t = E(x)$ in the integral of `Langlands/Tate/DedekindMellin.lean` gives $$\Gamma_K(s') |N(\alpha)|^{-s'} = 2^{-r_2} n R_K \int_{\mathbb{R}^{S_\infty}} e^{-\pi \sum_w n_w E(x)_w |\alpha|_w^2} e^{n s' x_{w_0} / 2} \, dx.$$ In the coordinates $x_{w_0} = \log y$ and $x_{w_i} = 2 c_i$ the point $E(x)$ is $t(y, c)$, and Fubini's theorem gives the formula. The substitution $c \mapsto 2c$ gives the factor $2^r$, and $y = e^{x_{w_0}}$ gives the measure $dy / y$.

## References

* E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, chapter VIII.
* J. Neukirch, Algebraic number theory, chapter VII, section 5.
-/

namespace Langlands.Tate

open Module Filter Topology MeasureTheory Set NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone

open scoped Real Classical

variable {K : Type*} [Field K] [NumberField K]

section Change

/-- The term of $\alpha$ in the theta function, $e^{-\pi \sum_w n_w t_w |\alpha|_w^2}$. -/
noncomputable def thetaTerm (α : K) (t : InfinitePlace K → ℝ) : ℝ :=
  Real.exp (-π * ∑ w, (mult w : ℝ) * t w * w α ^ 2)

variable (K) in
/-- The constant $2^{-r_2} n R_K$ of the change of variables, where $R_K$ is the regulator. -/
noncomputable def unitConst : ℝ :=
  2⁻¹ ^ nrComplexPlaces K * finrank ℚ K * regulator K

variable (K) in
theorem unitConst_pos : 0 < unitConst K := by
  have := finrank_pos (R := ℚ) (M := K)
  have := regulator_pos K
  unfold unitConst
  positivity

variable (K) in
/-- The map `expMapBasis` takes all of the real space onto $(0, \infty)^{S_\infty}$. -/
theorem image_expMapBasis :
    expMapBasis '' (univ : Set (realSpace K)) = univ.pi fun _ => Ioi 0 := by
  rw [← expMapBasis_source K, expMapBasis.image_source_eq_target]
  simp [expMapBasis, expMap_target]

/-- The product formula for `expMapBasis`, in logarithmic form: $\sum_w n_w \log E(x)_w = n x_{w_0}$. -/
theorem sum_mult_log_expMapBasis (x : realSpace K) :
    ∑ w, (mult w : ℝ) * Real.log (expMapBasis x w) = finrank ℚ K * x w₀ := by
  have h := congrArg Real.log (prod_expMapBasis_pow x)
  rw [Real.log_prod (fun w _ => pow_ne_zero _ (expMapBasis_pos x w).ne'), Real.log_pow,
    Real.log_exp] at h
  rw [← h]
  exact Finset.sum_congr rfl fun w _ => by rw [Real.log_pow]

/-- The product $\prod_w E_w^{n_w}$ is $\prod_w E_w$ times the product over the complex places. -/
theorem prod_pow_mult_eq (E : InfinitePlace K → ℝ) :
    ∏ w, E w ^ mult w = (∏ w, E w) * ∏ w : {w // IsComplex w}, E w.1 := by
  rw [prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun w => E w)]
  have hr : ∀ w : {w : InfinitePlace K // IsReal w}, E w.1 ^ mult w.1 = E w.1 := fun w => by
    rw [mult_isReal w, pow_one]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, E w.1 ^ mult w.1 = E w.1 * E w.1 :=
    fun w => by rw [mult_isComplex w, pow_two]
  simp_rw [hr, hc, Finset.prod_mul_distrib]
  ring

/-- The Jacobian of `expMapBasis` times the weight $\prod_w E_w^{n_w s / 2 - 1}$ is $2^{-r_2} n R_K e^{n s x_{w_0} / 2}$. -/
theorem abs_det_mul_prod_cpow (x : realSpace K) (s : ℂ) :
    ((|(fderiv_expMapBasis K x).det| : ℝ) : ℂ) *
        ∏ w, (expMapBasis x w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) =
      (unitConst K : ℂ) * Complex.exp ((finrank ℚ K : ℂ) * s / 2 * x w₀) := by
  set E := expMapBasis x with hE
  have hpos : ∀ w, 0 < E w := expMapBasis_pos x
  have h1 : ∀ w, (E w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) =
      Complex.exp ((mult w : ℂ) * s / 2 * Real.log (E w)) / (E w : ℂ) := fun w => by
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (hpos w).ne'), Complex.cpow_one,
      ofReal_cpow_eq_exp (hpos w)]
  have h2 : ∏ w, Complex.exp ((mult w : ℂ) * s / 2 * Real.log (E w)) =
      Complex.exp ((finrank ℚ K : ℂ) * s / 2 * x w₀) := by
    rw [← Complex.exp_sum]
    congr 1
    have := congrArg (fun r : ℝ => (r : ℂ) * s / 2) (sum_mult_log_expMapBasis x)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] at this
    rw [← hE] at this
    rw [show (finrank ℚ K : ℂ) * s / 2 * x w₀ = (finrank ℚ K : ℂ) * (x w₀ : ℂ) * s / 2 by ring,
      ← this, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h3 : Real.exp (x w₀ * finrank ℚ K) = (∏ w, E w) * ∏ w : {w // IsComplex w}, E w.1 := by
    rw [← prod_pow_mult_eq, hE, prod_expMapBasis_pow, ← Real.exp_nat_mul, mul_comm]
  have hP : (∏ w, E w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => (hpos w).ne'
  have hC : (∏ w : {w // IsComplex w}, E w.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => (hpos w.1).ne'
  have hP' : (∏ w, (E w : ℂ)) ≠ 0 := by exact_mod_cast hP
  have hC' : (∏ w : {w // IsComplex w}, (E w.1 : ℂ)) ≠ 0 := by exact_mod_cast hC
  rw [abs_det_fderiv_expMapBasis, ← hE]
  simp_rw [h1]
  rw [Finset.prod_div_distrib, h2, h3, unitConst]
  push_cast
  field_simp

/-- **The change of variables to the unit coordinates.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$2^{-r_2} n R_K \int_{\mathbb{R}^{S_\infty}} e^{-\pi \sum_w n_w E(x)_w |\alpha|_w^2} e^{n s x_{w_0} / 2} \, dx = \Gamma_K(s) \, |N(\alpha)|^{-s}.$$ -/
theorem unitConst_mul_integral_expMapBasis {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    (unitConst K : ℂ) * ∫ x : realSpace K, (thetaTerm α (expMapBasis x) : ℂ) *
        Complex.exp ((finrank ℚ K : ℂ) * s / 2 * x w₀) =
      gammaK K s * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn
    (fun t : realSpace K => (thetaTerm α t : ℂ) * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
  rw [image_expMapBasis, volume_pi, Measure.restrict_pi_pi, Measure.restrict_univ] at h
  refine Eq.trans ?_ (h.symm.trans (integral_exp_mul_prod_eq_gammaK hs hα))
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul]
  linear_combination -(thetaTerm α (expMapBasis x) : ℂ) * abs_det_mul_prod_cpow x s

end Change

section Integrable

/-- For $\mathrm{Re}\, z > 0$ and $r > 0$, the function $t^{z - 1} e^{-r t}$ is integrable on $(0, \infty)$. -/
theorem integrableOn_cpow_mul_exp {z : ℂ} (hz : 0 < z.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (Real.exp (-(r * t)) : ℂ)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := z.re - 1) (b := r)
    (by linarith) one_pos hr
  refine h.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne')
    · exact Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_exp.continuousAt.comp ((continuous_const.mul continuous_id).neg.continuousAt))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.rpow_one]
    simp

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `integral_exp_mul_prod_eq_gammaK` is integrable. -/
theorem integrable_thetaTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ =>
        (thetaTerm α t : ℂ) * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have h := Integrable.fintype_prod (f := fun (w : InfinitePlace K) (t : ℝ) =>
    (t : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) * (Real.exp (-((π * mult w * w α ^ 2) * t)) : ℂ))
    (μ := fun _ => volume.restrict (Ioi (0 : ℝ))) (fun w => integrableOn_cpow_mul_exp
      (mult_mul_re_pos hs w) (mul_pos (mul_pos Real.pi_pos (Nat.cast_pos.2 mult_pos))
        (pow_pos (InfinitePlace.pos_iff.2 hα) 2)))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [Finset.prod_mul_distrib, prod_exp_eq_exp_sum, mul_comm]
  rfl

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `unitConst_mul_integral_expMapBasis` is integrable. -/
theorem integrable_thetaTerm_expMapBasis {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable fun x : realSpace K => (thetaTerm α (expMapBasis x) : ℂ) *
      Complex.exp ((finrank ℚ K : ℂ) * s / 2 * x w₀) := by
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn
    (fun t : realSpace K => (thetaTerm α t : ℂ) * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))).1
  rw [image_expMapBasis, IntegrableOn, volume_pi, Measure.restrict_pi_pi, IntegrableOn,
    Measure.restrict_univ] at h
  have h' := (h (integrable_thetaTerm_mul_prod hs hα)).const_mul ((unitConst K : ℂ)⁻¹)
  refine h'.congr (Eventually.of_forall fun x => ?_)
  have hC : (unitConst K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (unitConst_pos K).ne'
  simp only [Complex.real_smul]
  rw [show ∀ a b c : ℂ, (unitConst K : ℂ)⁻¹ * (a * (b * c)) = (unitConst K : ℂ)⁻¹ * b * (a * c)
    from fun a b c => by ring, abs_det_mul_prod_cpow]
  field_simp

end Integrable

section Coordinates

noncomputable instance : Unique {w : InfinitePlace K // w = w₀} :=
  ⟨⟨⟨w₀, rfl⟩⟩, fun w => Subtype.ext w.2⟩

variable (K) in
/-- The coordinates $(x_{w_0}, (x_{w_i})_i)$ of the real space, with the places $w \neq w_0$ numbered by `equivFinRank`. -/
noncomputable def unitCoord : realSpace K ≃ᵐ ℝ × (Fin (rank K) → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique {w : InfinitePlace K // w = w₀} ℝ)
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) fundamentalCone.equivFinRank).symm)

variable (K) in
theorem measurePreserving_unitCoord : MeasurePreserving (unitCoord K) := by
  refine (volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ)
    (· = (w₀ : InfinitePlace K))).trans ?_
  convert (volume_preserving_funUnique {w : InfinitePlace K // w = w₀} ℝ).prod
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (fundamentalCone.equivFinRank (K := K))).symm
  · rfl
  · rw [Measure.volume_eq_prod]
    congr
    exact Subsingleton.elim _ _

theorem unitCoord_apply_fst (x : realSpace K) : (unitCoord K x).1 = x (w₀ : InfinitePlace K) := rfl

theorem unitCoord_apply_snd (x : realSpace K) (i : Fin (rank K)) :
    (unitCoord K x).2 i = x (fundamentalCone.equivFinRank i) := rfl

theorem unitCoord_symm_w₀ (p : ℝ × (Fin (rank K) → ℝ)) : (unitCoord K).symm p w₀ = p.1 := by
  conv_rhs => rw [← (unitCoord K).apply_symm_apply p]
  rfl

theorem unitCoord_symm_ne (p : ℝ × (Fin (rank K) → ℝ)) (i : Fin (rank K)) :
    (unitCoord K).symm p (fundamentalCone.equivFinRank i) = p.2 i := by
  conv_rhs => rw [← (unitCoord K).apply_symm_apply p]
  rw [unitCoord_apply_snd]

/-- In the coordinates $(v, 2c)$, the map `expMapBasis` is $t(e^v, c)$. -/
theorem expMapBasis_unitCoord_symm (v : ℝ) (c : Fin (rank K) → ℝ) :
    expMapBasis ((unitCoord K).symm (v, (2 : ℝ) • c)) = unitScale K (Real.exp v) c := by
  funext w
  rw [expMapBasis_apply', Pi.smul_apply, smul_eq_mul, unitCoord_symm_w₀, unitScale]
  congr 1
  rw [← Equiv.prod_comp fundamentalCone.equivFinRank, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Equiv.symm_apply_apply, unitCoord_symm_ne,
    Real.rpow_def_of_pos (InfinitePlace.pos_iff.2 (coe_ne_zero _)), unitLog, placeLog]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Pi.smul_apply, smul_eq_mul]
  ring_nf

end Coordinates

section Mellin

/-- **The Mellin transform of one term in the unit coordinates.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, with $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} e^{-\pi \sum_w n_w t(y, c)_w |\alpha|_w^2} \, dc \, dy = \Gamma_K(s') \, |N(\alpha)|^{-s'}.$$ -/
theorem integral_unitScale {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, (thetaTerm α (unitScale K y c) : ℂ) =
      gammaK K (2 * s / finrank ℚ K) *
        ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)) := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hre : 0 < (2 * s / finrank ℚ K).re := by
    rw [Complex.div_natCast_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    have := finrank_pos (R := ℚ) (M := K)
    positivity
  have key : (finrank ℚ K : ℂ) * (2 * s / finrank ℚ K) / 2 = s := by
    field_simp
  have hA := unitConst_mul_integral_expMapBasis hre hα
  have hI := integrable_thetaTerm_expMapBasis hre hα
  rw [key] at hA hI
  rw [← hA]
  set G : realSpace K → ℂ := fun x => (thetaTerm α (expMapBasis x) : ℂ) *
    Complex.exp (s * x w₀) with hG
  have hmp := (measurePreserving_unitCoord K).symm
  have h1 : ∫ x, G x = ∫ p : ℝ × (Fin (rank K) → ℝ), G ((unitCoord K).symm p) :=
    (hmp.integral_comp' G).symm
  have hI' : Integrable (fun p => G ((unitCoord K).symm p)) (volume.prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hI
  rw [h1, Measure.volume_eq_prod, integral_prod _ hI']
  have h2 : ∀ v : ℝ, ∫ u : Fin (rank K) → ℝ, G ((unitCoord K).symm (v, u)) =
      (2 ^ rank K : ℂ) * (Complex.exp (s * v) *
        ∫ c, (thetaTerm α (unitScale K (Real.exp v) c) : ℂ)) := by
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
  have h3 : ∫ v : ℝ, Complex.exp (s * v) *
        ∫ c, (thetaTerm α (unitScale K (Real.exp v) c) : ℂ) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * ∫ c, (thetaTerm α (unitScale K y c) : ℂ) := by
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

end Mellin

end Langlands.Tate
