/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeShiftFE
import Langlands.Tate.HeckeMixedSign

/-!
# Hecke's functional equation for the unramified characters with arbitrary shifts

Let $K$ be a number field of degree $n$ and let $\xi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n_v, t_v)$. The file `Langlands/Tate/HeckeMixedSign.lean` proves Hecke's functional equation if $t_v = t_0$ for all $v$. Here the shifts $t_v$ are arbitrary.

The character $\xi_\infty$ is trivial on the units, so $\sum_w n_w \mathrm{Re}(t_w) \log |u|_w = 0$ for each unit $u$. By the theorem of Dirichlet the logarithms of the units span the hyperplane $\sum_w x_w = 0$, so $\mathrm{Re}(t_w) = \mathrm{Re}(t_{w_0})$ for all $w$ (`Langlands.Tate.re_eq_of_isArchimedeanParameter`). The twist by $\|\cdot\|^{-\mathrm{Re}(t_{w_0})}$ gives a unitary character $\chi$ with the parameters $(n_w, i \theta_w)$, where $\theta_w = \mathrm{Im}(t_w)$. Reciprocity gives $\chi_{\mathrm{id}}((x)) = \chi^{\varepsilon, p, k}_\infty(x) \, \tau_\theta(x)$ with the torus factor $\tau_\theta$ of `Langlands/Tate/HeckeShiftTheta.lean`. The completed partial Hecke sums of `Langlands/Tate/HeckeShiftFE.lean` then give the functional equation of each class sum. The archimedean factor of $(n_w, i \theta_w)$ is the shifted Gamma factor times $A(s) \prod_{w \text{ complex}} 2^{-i \theta_w}$, and the constant $\tau_\theta((n_w^2)_w)$ of the change of variable changes $\prod_{w \text{ complex}} 2^{-i \theta_w}$ to $\prod_{w \text{ complex}} 2^{i \theta_w}$.

For $n = 0$ and $\theta$ not constant, the term $\alpha = 0$ of the theta series has the mean value $0$ over the unit cube. The reason is that some $L_i = \sum_w n_w \theta_w \log |\varepsilon_i|_w$ is not zero, and $e^{i L_i} = 1$ since $\tau_\theta$ is trivial on the units. So in this case the completed $L$-function is entire.

## Main definitions

* `Langlands.Tate.torusArch`: the factor $\prod_{w \text{ complex}} 2^{-i \theta_w}$.
* `Langlands.Tate.shiftCompletedPartialHeckeConj`: the conjugate completed partial Hecke sum with the shifts.
* `Langlands.Tate.ShiftMeanZero`: the condition that the term $\alpha = 0$ has the mean value $0$ over the unit cube.
* `Langlands.Tate.shiftHeckeClassCompleted`, `Langlands.Tate.shiftHeckeClassCompletedConj`: the completed class sums of $\chi$ and $\chi^{-1}$.
* `Langlands.Tate.shiftHeckeCompleted`, `Langlands.Tate.shiftHeckeCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$.

## Main results

* `Langlands.Tate.eq_of_sum_mult_log_unit_eq_zero`: a vector that is orthogonal to the logarithms of all units is constant.
* `Langlands.Tate.re_eq_of_isArchimedeanParameter`: the real parts of the shifts of an unramified character are equal.
* `Langlands.Tate.idealChar_toPrincipalIdeal_eq_shift`: reciprocity for the parameters $(n_w, i \theta_w)$.
* `Langlands.Tate.gammaFactor_imagShift`: the archimedean factor of $(n_w, i \theta_w)$.
* `Langlands.Tate.shiftMeanZero_of_not_const`: the mean value $0$ for $n = 0$ and $\theta$ not constant.
* `Langlands.Tate.entireFunctionalEquation_unramified_shift`: the entire functional equation for the parameters $(n_w, i \theta_w)$.
* `Langlands.Tate.heckeFunctionalEquation_of_unramified_general`: Hecke's functional equation for the unramified characters with arbitrary shifts and signs.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem IsDedekindDomain
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Dirichlet

variable {K : Type*} [Field K] [NumberField K]

/-- **The shifts that are trivial on the units are constant.** Let $r$ be a real vector indexed by the infinite places, with $\sum_w n_w r_w \log |u|_w = 0$ for each unit $u$ of $\mathcal{O}_K$. Then $r_w = r_{w_0}$ for each infinite place $w$. This follows from the theorem of Dirichlet that the logarithms of the units span the hyperplane $\sum_w x_w = 0$. -/
theorem eq_of_sum_mult_log_unit_eq_zero (r : InfinitePlace K → ℝ)
    (h : ∀ u : (𝓞 K)ˣ, ∑ w, (mult w : ℝ) * r w * Real.log (w (u : K)) = 0) (w : InfinitePlace K) :
    r w = r w₀ := by
  let L : logSpace K →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ w' : {w : InfinitePlace K // w ≠ w₀}, (r w'.1 - r w₀) * x w'
      map_add' := fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hL : L = 0 := by
    refine LinearMap.ext_on (unitLattice_span_eq_top K) fun x hx => ?_
    obtain ⟨u, -, rfl⟩ := hx
    change ∑ w' : {w : InfinitePlace K // w ≠ w₀}, (r w'.1 - r w₀) *
      ((mult w'.1 : ℝ) * Real.log (w'.1 ((Additive.toMul u : (𝓞 K)ˣ) : K))) = 0
    have h1 := h (Additive.toMul u)
    have h2 := sum_mult_mul_log (Additive.toMul u)
    have e : ∑ w : InfinitePlace K, (r w - r w₀) * ((mult w : ℝ) *
        Real.log (w ((Additive.toMul u : (𝓞 K)ˣ) : K))) = 0 := by
      have e1 : ∑ w : InfinitePlace K, (r w - r w₀) * ((mult w : ℝ) *
          Real.log (w ((Additive.toMul u : (𝓞 K)ˣ) : K))) =
          ∑ w : InfinitePlace K, (mult w : ℝ) * r w *
            Real.log (w ((Additive.toMul u : (𝓞 K)ˣ) : K)) -
          r w₀ * ∑ w : InfinitePlace K, (mult w : ℝ) *
            Real.log (w ((Additive.toMul u : (𝓞 K)ˣ) : K)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, h1, h2, mul_zero, sub_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, sub_self, zero_mul, zero_add] at e
    exact e
  by_cases hw : w = w₀
  · rw [hw]
  · have e := LinearMap.congr_fun hL (Pi.single ⟨w, hw⟩ 1)
    change ∑ w' : {w : InfinitePlace K // w ≠ w₀}, (r w'.1 - r w₀) *
      (Pi.single ⟨w, hw⟩ (1 : ℝ) : logSpace K) w' = 0 at e
    rw [Finset.sum_eq_single ⟨w, hw⟩ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one] at e
    linarith

/-- **The fundamental units are enough.** If $\sum_w n_w r_w \log |\varepsilon_i|_w = 0$ for each fundamental unit $\varepsilon_i$, then $\sum_w n_w r_w \log |u|_w = 0$ for each unit $u$ of $\mathcal{O}_K$. -/
theorem sum_mult_log_unit_eq_zero (r : InfinitePlace K → ℝ)
    (h : ∀ i, ∑ w, (mult w : ℝ) * r w * unitLog K i w = 0) (u : (𝓞 K)ˣ) :
    ∑ w, (mult w : ℝ) * r w * Real.log (w (u : K)) = 0 := by
  let f : Additive (𝓞 K)ˣ →+ ℝ := ∑ w, ((mult w : ℝ) * r w) • placeLog K w
  have hf : ∀ v : (𝓞 K)ˣ, f (Additive.ofMul v) =
      ∑ w, (mult w : ℝ) * r w * Real.log (w (v : K)) := fun v => by
    simp only [f, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := exist_unique_eq_mul_prod K u
  have hζ : f (Additive.ofMul (ζ : (𝓞 K)ˣ)) = 0 := by
    rw [hf]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [(mem_torsion K).1 ζ.2 w, Real.log_one, mul_zero]
  have hi : ∀ i, f (Additive.ofMul (fundSystem K i)) = 0 := fun i => by
    rw [hf]
    exact h i
  rw [← hf, hu, ofMul_mul, map_add, hζ, zero_add, ofMul_prod, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, hi, smul_zero]

end Dirichlet

section Character

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The factor $\tau_\theta(\alpha)$ as a product over the infinite places. -/
theorem torusWeight_eq_prod (θ : InfinitePlace K → ℝ) (α : K) :
    torusWeight θ α = ∏ w, cexp (-(((mult w : ℝ) * θ w * Real.log (w α) : ℝ) * I)) := by
  rw [torusWeight, ← Complex.exp_sum, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_neg_distrib]

/-- **The characters with imaginary shifts are unitary at the infinite places.** If $\chi$ has the parameters $(n_w, i \theta_w)$ with real $\theta_w$, then $|\chi_w(y)| = 1$ for each infinite place $w$. -/
theorem norm_infiniteComponent_of_shift {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I)) (w : InfinitePlace K)
    (y : w.Completionˣ) : ‖(χ.infiniteComponent w y : ℂ)‖ = 1 := by
  have h0 : InfinitePlace.Completion.extensionEmbedding w y ≠ 0 := (y.isUnit.map _).ne_zero
  rw [(hn w).eq y, norm_mul, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.2 h0), one_zpow, one_mul,
    norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 h0)]
  simp

omit [NumberField K] in
/-- **The phase of $\chi_w$ and the signed phase.** If $n_w \in \{0, 1\}$ at a real place $w$, then $(\sigma_w(x) / |\sigma_w(x)|)^{n_w}$ times the signed phase of $|n|$ at $w$ is $1$ for each $x \neq 0$. -/
theorem phase_mul_signPlacePhase {n : InfinitePlace K → ℤ} {w : InfinitePlace K}
    (hr : IsReal w → n w = 0 ∨ n w = 1) {x : K} (hx0 : x ≠ 0) :
    (w.embedding x / ((w x : ℝ) : ℂ)) ^ n w * signPlacePhase (paramSign K n)
      (realWeight K (absParam K n)) (complexWeight K (absParam K n)) x w = 1 := by
  have hx : w x ≠ 0 := (map_ne_zero w).2 hx0
  have hx' : ((w x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  unfold signPlacePhase
  split_ifs with hw
  · rcases hr hw with h | h
    · have e : realWeight K (absParam K n) ⟨w, hw⟩ = 0 := by
        simp only [realWeight, absParam, h, abs_zero, Int.toNat_zero]
      rw [h, e, zpow_zero, pow_zero, one_mul]
    · have e : realWeight K (absParam K n) ⟨w, hw⟩ = 1 := by
        simp only [realWeight, absParam, h, abs_one, Int.toNat_one]
      rw [h, e, zpow_one, pow_one, ← embedding_of_isReal_apply hw]
      have h2 : (embedding_of_isReal hw x) ^ 2 = w x ^ 2 := by
        rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, sq_abs]
      have h2' : ((embedding_of_isReal hw x : ℝ) : ℂ) ^ 2 = ((w x : ℝ) : ℂ) ^ 2 := by
        exact_mod_cast h2
      rw [Complex.ofReal_div, div_mul_div_comm, ← sq, ← sq, h2', div_self (pow_ne_zero _ hx')]
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 hw
    have hs : signEmbedding (paramSign K n) w x =
        flipConj (paramSign K n ⟨w, hc⟩) (w.embedding x) :=
      signEmbedding_apply (paramSign K n) ⟨w, hc⟩ x
    have hk : ((complexWeight K (absParam K n) ⟨w, hc⟩ : ℕ) : ℤ) = |n w| :=
      Int.toNat_of_nonneg (abs_nonneg (n w))
    have huv : (w.embedding x / ((w x : ℝ) : ℂ)) * (conj (w.embedding x) / ((w x : ℝ) : ℂ)) = 1 := by
      rw [div_mul_div_comm, Complex.mul_conj', norm_embedding_eq, ← sq,
        div_self (pow_ne_zero _ hx')]
    rw [hs]
    generalize complexWeight K (absParam K n) ⟨w, hc⟩ = m at hk
    by_cases hneg : n w < 0
    · have e : paramSign K n ⟨w, hc⟩ = true := decide_eq_true hneg
      have hm : n w = -(m : ℤ) := by rw [hk, abs_of_neg hneg, neg_neg]
      rw [e, flipConj_true, Complex.conj_conj, hm, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ (left_ne_zero_of_mul_eq_one huv))]
    · have e : paramSign K n ⟨w, hc⟩ = false := decide_eq_false hneg
      have hm : n w = (m : ℤ) := by rw [hk, abs_of_nonneg (not_lt.1 hneg)]
      rw [e, flipConj_false, hm, zpow_natCast, ← mul_pow, huv, one_pow]

/-- **The infinite type, the signed infinity type and the torus factor.** Let $\chi$ have the parameters $(n_w, i \theta_w)$ at each infinite place, with real $\theta_w$ and arbitrary signs of the $n_w$. Then $\chi_\infty(x) \, \chi^{\varepsilon, p, k}_\infty(x) \, \tau_\theta(x) = 1$ for each $x \in K^\times$, where $p$ and $k$ are the weights of $|n|$ and $\varepsilon$ is the sign of $n$. -/
theorem infChar_mul_signInfinityWeight_mul_torusWeight {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (x : Kˣ) :
    (infChar χ x : ℂ) * signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) (x : K) * torusWeight θ (x : K) = 1 := by
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Units.coe_prod, signInfinityWeight,
    torusWeight_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  have hx : w (x : K) ≠ 0 := (map_ne_zero w).2 x.ne_zero
  have hx' : 0 < w (x : K) := lt_of_le_of_ne (apply_nonneg w _) hx.symm
  rw [(hn w).eq, extensionEmbedding_ideleInf_unitEmbedding, norm_embedding_eq]
  have hm : ((w (x : K) : ℝ) : ℂ) ^ ((mult w : ℂ) * ((θ w : ℂ) * I)) *
      cexp (-(((mult w : ℝ) * θ w * Real.log (w (x : K)) : ℝ) * I)) = 1 := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hx), ← Complex.ofReal_log hx'.le,
      ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  have hp := phase_mul_signPlacePhase (hn w).isReal x.ne_zero
  linear_combination (((w (x : K) : ℝ) : ℂ) ^ ((mult w : ℂ) * ((θ w : ℂ) * I)) *
      cexp (-(((mult w : ℝ) * θ w * Real.log (w (x : K)) : ℝ) * I))) * hp + hm

/-- **The ideal character on principal ideals.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, i \theta_w)$ at each infinite place. Then $\chi_{\mathrm{id}}((x)) = \chi^{\varepsilon, p, k}_\infty(x) \, \tau_\theta(x)$ for each $x \in K^\times$. -/
theorem idealChar_toPrincipalIdeal_eq_shift (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (x : Kˣ) :
    (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) =
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) (x : K) * torusWeight θ (x : K) := by
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) x (by simp [h0])
  rw [h0, Finset.prod_empty, mul_one, periodicChar_apply] at e
  have e' := congrArg (fun z : ℂˣ => (z : ℂ)) e
  simp only [Units.val_mul, Units.val_one] at e'
  have hr := infChar_mul_signInfinityWeight_mul_torusWeight hn x
  linear_combination (signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) (x : K) * torusWeight θ (x : K)) * e' -
    (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) * hr

/-- A unit generates the unit fractional ideal. -/
theorem toPrincipalIdeal_unit (u : (𝓞 K)ˣ) :
    toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) = 1 := by
  rw [toPrincipalIdeal_eq_iff, Units.coe_map, Units.val_one]
  change FractionalIdeal.spanSingleton _ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
  rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit,
    FractionalIdeal.coeIdeal_top]

/-- **The twisted infinity type is trivial on the units.** Under the hypotheses of `Langlands.Tate.idealChar_toPrincipalIdeal_eq_shift`, $\chi^{\varepsilon, p, k}_\infty(u) \, \tau_\theta(u) = 1$ for each unit $u$ of $\mathcal{O}_K$. -/
theorem signInfinityWeight_mul_torusWeight_unit (h0 : ramifiedSet χ = ∅)
    {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I)) (u : (𝓞 K)ˣ) :
    signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) (u : K) * torusWeight θ (u : K) = 1 := by
  have e := idealChar_toPrincipalIdeal_eq_shift h0 hn (Units.map (algebraMap (𝓞 K) K) u)
  rw [toPrincipalIdeal_unit, map_one, Units.val_one] at e
  exact e.symm

/-- **The real parts of the shifts are equal.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, t_w)$ at each infinite place. Then $\mathrm{Re}\, t_w = \mathrm{Re}\, t_{w_0}$ for each infinite place $w$. -/
theorem re_eq_of_isArchimedeanParameter (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {t : InfinitePlace K → ℂ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w))
    (w : InfinitePlace K) : (t w).re = (t w₀).re := by
  refine eq_of_sum_mult_log_unit_eq_zero (fun w => (t w).re) (fun u => ?_) w
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) (Units.map (algebraMap (𝓞 K) K) u)
    (by simp [h0])
  rw [h0, Finset.prod_empty, mul_one, periodicChar_apply, toPrincipalIdeal_unit, map_one,
    one_mul] at e
  have e' := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) e
  simp only [Units.val_one, norm_one] at e'
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Units.coe_prod, norm_prod] at e'
  have hw : ∀ w : InfinitePlace K, ‖(χ.infiniteComponent w (ideleInf w
      (IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u))) : ℂ)‖ =
      w (u : K) ^ ((mult w : ℝ) * (t w).re) := fun w => by
    have hx : (0 : ℝ) < w ((Units.map (algebraMap (𝓞 K) K) u : Kˣ) : K) := pos_at_place u w
    have hx0 : w.embedding ((Units.map (algebraMap (𝓞 K) K) u : Kˣ) : K) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    rw [(hn w).eq, extensionEmbedding_ideleInf_unitEmbedding, norm_mul, norm_zpow, norm_div,
      Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hx0), one_zpow, one_mul,
      norm_embedding_eq, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  rw [Finset.prod_congr rfl fun w _ => hw w] at e'
  have e2 := congrArg Real.log e'
  rw [Real.log_one, Real.log_prod (fun w _ => (Real.rpow_pos_of_pos (pos_at_place u w) _).ne')]
    at e2
  rw [← e2]
  exact Finset.sum_congr rfl fun w _ => by rw [Real.log_rpow (pos_at_place u w)]

end Character

section Gamma

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The archimedean correction of the shifts: $\prod_{w \text{ complex}} 2^{-i \theta_w}$. -/
noncomputable def torusArch (θ : InfinitePlace K → ℝ) : ℂ :=
  ∏ w : InfinitePlace K, if IsReal w then 1 else (2 : ℂ) ^ (-((θ w : ℂ) * I))

/-- **The archimedean factor with imaginary shifts.** If $n_w \in \{0, 1\}$ at the real places, then the archimedean factor of the parameters $(n_w, i \theta_w)$ is $$L_\infty(s) = A(s) \prod_{w \text{ complex}} 2^{-i \theta_w} \cdot \Gamma_{p, k}^\theta(s),$$ where $A$ is `Langlands.Tate.archRatio` of $|n|$ and $(p, k)$ is the weight of $|n|$. -/
theorem gammaFactor_imagShift {n : InfinitePlace K → ℤ} (hr : ∀ w, IsReal w → n w = 0 ∨ n w = 1)
    (θ : InfinitePlace K → ℝ) (s : ℂ) :
    gammaFactor K n (fun w => (θ w : ℂ) * I) s =
      archRatio K (absParam K n) s * torusArch K θ *
        shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ s := by
  rw [gammaFactor, archRatio, torusArch, shiftGamma, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hq : ((weightExp (realWeight K (absParam K n)) (complexWeight K (absParam K n)) w : ℕ) :
      ℂ) = ((|n w| : ℤ) : ℂ) := by
    rw [weightExp_realWeight]
    exact_mod_cast Int.toNat_of_nonneg (abs_nonneg (n w))
  simp only [heckeExp, hq, absParam]
  by_cases hw : IsReal w
  · have e : ((|n w| : ℤ) : ℂ) = (n w : ℂ) := by
      rcases hr w hw with h | h <;> simp [h]
    have hm : (mult w : ℂ) = 1 := by rw [mult, ite_eq_left hw, Nat.cast_one]
    rw [ite_eq_left hw, ite_eq_left hw, ite_eq_left hw, hm, e, one_mul, one_mul, one_mul, Gammaℝ_def, neg_div]
  · have hm : (mult w : ℂ) = 2 := by rw [mult, ite_eq_right hw, Nat.cast_ofNat]
    rw [ite_eq_right hw, ite_eq_right hw, ite_eq_right hw, hm, gammaℂ_eq_two_cpow_mul, Gammaℝ_def,
      ← cpow_add _ _ two_ne_zero]
    have e1 : 2 * (s + (θ w : ℂ) * I + ((|n w| : ℤ) : ℂ) / 2) / 2 =
        (2 * (s + (θ w : ℂ) * I) + ((|n w| : ℤ) : ℂ)) / 2 := by ring
    have e2 : 1 - (s + (θ w : ℂ) * I + ((|n w| : ℤ) : ℂ) / 2) =
        1 - (s + ((|n w| : ℤ) : ℂ) / 2) + -((θ w : ℂ) * I) := by ring
    rw [neg_div, e1, e2]

/-- The archimedean factors of the parameters $(n'_w, t'_w)$ of $\chi^{-1}$ are the archimedean factors of the parameters $(n_w, -i \theta_w)$. -/
theorem gammaFactor_imagShift_inv {n n' : InfinitePlace K → ℤ} {t' : InfinitePlace K → ℂ}
    {θ : InfinitePlace K → ℝ} (hn' : ∀ w, n' w = if IsReal w then n w else -n w)
    (ht' : ∀ w, t' w = ((-θ) w : ℂ) * I) (s : ℂ) :
    gammaFactor K n' t' s = gammaFactor K n (fun w => ((-θ) w : ℂ) * I) s := by
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [hn', ht']
  by_cases hw : IsReal w
  · simp only [hw, ite_true]
  · simp only [hw, ite_false, abs_neg]

/-- **The archimedean correction and the change of variable.** $\prod_{w \text{ complex}} 2^{-i \theta_w} \cdot \tau_\theta((n_w^2)_w) = \prod_{w \text{ complex}} 2^{i \theta_w}$. -/
theorem torusArch_mul_torusConst (θ : InfinitePlace K → ℝ) :
    torusArch K θ * torusConst θ = torusArch K (-θ) := by
  rw [torusArch, torusArch, torusConst, torusFactor_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : IsReal w
  · rw [ite_eq_left hw, ite_eq_left hw, mult, ite_eq_left hw, Nat.cast_one, one_pow, Real.log_one, mul_zero,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  · rw [ite_eq_right hw, ite_eq_right hw, mult, ite_eq_right hw, cpow_def_of_ne_zero two_ne_zero,
      cpow_def_of_ne_zero two_ne_zero, ← Complex.exp_add]
    have h2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num), Complex.ofReal_ofNat]
    rw [h2]
    congr 1
    rw [Real.log_pow, Pi.neg_apply]
    push_cast
    ring

end Gamma

section Conj

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ}

variable (K ε p k θ) in
/-- The conjugate completed partial Hecke sum $\Lambda^*_{\mathfrak{a}}(s) = \overline{\Lambda_{\mathfrak{a}}(\bar{s})}$ with the shifts $i \theta_w$. -/
noncomputable def shiftCompletedPartialHeckeConj (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  conj (shiftCompletedPartialHecke K ε p k θ a (conj s))

/-- **The conjugate completed partial Hecke sum with the shifts is entire.** -/
theorem differentiable_shiftCompletedPartialHeckeConj (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
      shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (shiftCompletedPartialHeckeConj K ε p k θ a) := fun s => by
  have e := (differentiable_shiftCompletedPartialHecke (a := a) hp hχ h0 (conj s)).conj_conj
  rw [Complex.conj_conj] at e
  exact e

/-- **The conjugate completed partial Hecke sum as a series.** Under the hypotheses of `Langlands.Tate.hasSum_shiftCompletedPartialHecke`, with $s' = 2 s / n$, $$\Lambda^*_{\mathfrak{a}}(s) = \sum_{\alpha} w_K \, \Gamma_{p, k}^{-\theta}(s') \, \overline{\chi_\infty(\alpha) \tau_\theta(\alpha)} \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_shiftCompletedPartialHeckeConj
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
      shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (shiftGamma p k (-θ) (2 * s / finrank ℚ K) *
        conj (signInfinityWeight ε p k (orbitRep a I : K) * torusWeight θ (orbitRep a I : K)) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (shiftCompletedPartialHeckeConj K ε p k θ a s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have e := (hasSum_shiftCompletedPartialHecke (a := a) hχ h0 hs').map (starRingEnd ℂ)
    continuous_conj
  have hc : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hc, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_shiftGamma]
  ring

/-- **The functional equation in the variable of the $L$-function.** Under the hypotheses of `Langlands.Tate.shiftCompletedPartialHecke_sub`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(n s / 2) = \varepsilon_{\mathfrak{a}} \, \tau_\theta((n_w^2)_w) \, \lambda^{-n (1 - s) / 2} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(n (1 - s) / 2).$$ -/
theorem shiftCompletedPartialHecke_one_sub (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
      shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    shiftCompletedPartialHecke K ε p k θ a ((finrank ℚ K : ℂ) * s / 2) =
      heckeRootConst K p k a * torusConst θ *
        (heckeScale K : ℂ) ^ (-((finrank ℚ K : ℂ) * (1 - s) / 2)) *
        shiftCompletedPartialHeckeConj K ε p k θ (dualUnit K a)
          ((finrank ℚ K : ℂ) * (1 - s) / 2) := by
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring]
  exact shiftCompletedPartialHecke_sub hp hχ h0 _

end Conj

section Classes

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (K) in
/-- The condition that the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube for each $y > 0$, for the signed weight of $n$ and the shifts $i \theta_w$. It holds if $n \neq 0$ (`Langlands.Tate.shiftMeanZero_of_ne_zero`) or if $\theta$ is not constant (`Langlands.Tate.shiftMeanZero_of_not_const`). -/
def ShiftMeanZero (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    shiftHeckeTerm (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ 0 (unitScale K y c) = 0

variable (χ) in
/-- The completed class sum $\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{a})^{-1} N(\mathfrak{a})^s \Lambda_{\mathfrak{a}}(n s / 2)$ with the signed weight of $n$ and the shifts $i \theta_w$. -/
noncomputable def shiftHeckeClassCompleted (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (idealChar χ a : ℂ)⁻¹ * ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    shiftCompletedPartialHecke K (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ a ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1}) = \chi^{-1}_{\mathrm{id}}(\mathfrak{b})^{-1} N(\mathfrak{b})^s \Lambda^*_{\mathfrak{b}}(n s / 2)$ with the signed weight of $n$ and the shifts $i \theta_w$. -/
noncomputable def shiftHeckeClassCompletedConj (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (idealChar χ⁻¹ b : ℂ)⁻¹ * ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    shiftCompletedPartialHeckeConj K (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ b ((finrank ℚ K : ℂ) * s / 2)

/-- **The class sum as a Dirichlet series.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, i \theta_w)$ at each infinite place, and let `Langlands.Tate.ShiftMeanZero` hold. For $\mathrm{Re}\, s > 1$, $\Lambda_{\mathfrak{a}}(s, \chi)$ is the sum over the integral ideals $I$ in the class $[\mathfrak{a}]^{-1}$ of $w_K \, \Gamma_{p, k}^\theta(s) \, \chi_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_shiftHeckeClassCompleted (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then
        (torsionOrder K : ℂ) * shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ s * rayWeight χ s I else 0)
      (shiftHeckeClassCompleted χ n θ a s) := by
  have h := hasSum_shiftCompletedPartialHecke (a := a)
    (signInfinityWeight_mul_torusWeight_unit h0 hn) hz (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [shiftHeckeClassCompleted]
  refine hasSum_rayWeight_class h0
    (f := fun x => signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) x * torusWeight θ x)
    (fun x => (idealChar_toPrincipalIdeal_eq_shift h0 hn x).symm) a ?_
  exact h.congr_fun fun I => by ring

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_shiftHeckeClassCompleted`, $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[\mathfrak{b}]^{-1}$ of $w_K \, \Gamma_{p, k}^{-\theta}(s) \, \chi^{-1}_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_shiftHeckeClassCompletedConj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K b)⁻¹ then
        (torsionOrder K : ℂ) * shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (-θ) s * rayWeight χ⁻¹ s I else 0)
      (shiftHeckeClassCompletedConj χ n θ b s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have h := hasSum_shiftCompletedPartialHeckeConj
    (signInfinityWeight_mul_torusWeight_unit h0 hn) hz b (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [shiftHeckeClassCompletedConj]
  refine hasSum_rayWeight_class (ψ := χ⁻¹)
    (f := fun x => conj (signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) x * torusWeight θ x))
    (by rw [ramifiedSet_inv, h0]) (fun x => ?_) b h
  rw [← idealChar_toPrincipalIdeal_eq_shift h0 hn x, idealChar_inv, Units.val_inv_eq_inv_val,
    Complex.inv_eq_conj (norm_idealChar_of_unitary hu _)]

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The $L$-function as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.hasSum_shiftHeckeClassCompleted`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}^\theta(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi).$$ -/
theorem shiftGamma_mul_finiteLFunction (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ s * χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), shiftHeckeClassCompleted χ n θ (classRepUnit K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_shiftHeckeClassCompleted h0 hn hz (classRepUnit K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (classRepUnit K C))⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_classRepUnit]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.hasSum_shiftHeckeClassCompleted`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}^{-\theta}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1}).$$ -/
theorem shiftGamma_mul_finiteLFunction_inv (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (-θ) s * χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K),
        shiftHeckeClassCompletedConj χ n θ (dualUnit K (classRepUnit K C)) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_shift hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_shiftHeckeClassCompletedConj h0 hn hz (dualUnit K (classRepUnit K C)) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (dualUnit K (classRepUnit K C)))⁻¹) ↔
        ((dualClass K).symm (ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_dualUnit_classRepUnit, Equiv.symm_apply_eq]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end LFunction

section ClassFE

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The functional equation of one class sum.** Under the hypotheses of `Langlands.Tate.hasSum_shiftHeckeClassCompleted`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_v p_v + \sum_w k_w} \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, \tau_\theta((n_w^2)_w) \, |d_K|^{1/2 - s} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(1 - s, \chi^{-1}).$$ -/
theorem shiftHeckeClassCompleted_eq_conj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    shiftHeckeClassCompleted χ n θ a s = (idealChar χ (differentUnit K) : ℂ) *
      (-I) ^ (∑ v, realWeight K (absParam K n) v + ∑ w, complexWeight K (absParam K n) w) *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      torusConst θ * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (1 / 2 - s) *
      shiftHeckeClassCompletedConj χ n θ (dualUnit K a) (1 - s) := by
  have hc : (idealChar χ (dualUnit K a) : ℂ) =
      ((idealChar χ a : ℂ) * idealChar χ (differentUnit K))⁻¹ := by
    rw [dualUnit_eq, map_inv, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
  unfold shiftHeckeClassCompleted shiftHeckeClassCompletedConj
  rw [shiftCompletedPartialHecke_one_sub (realWeight_absParam_le_one hn)
    (signInfinityWeight_mul_torusWeight_unit h0 hn) hz a s, heckeScale_cpow, heckeRootConst,
    absNorm_dualUnit, idealChar_inv, Units.val_inv_eq_inv_val, inv_inv, hc]
  set A : ℝ := (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  set D : ℝ := |(discr K : ℝ)|
  have hA : 0 < A := absNorm_pos K a
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hA0 : (A : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  have hD0 : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD.ne'
  have hB : (((A * D)⁻¹ : ℝ) : ℂ) ^ (1 - s) = ((A : ℂ) / A ^ s * ((D : ℂ) / D ^ s))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_ne_zero.symm), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hA.le hD.le, cpow_sub _ _ hA0, cpow_sub _ _ hD0, cpow_one,
      cpow_one]
  have hsq : ((√D : ℝ) : ℂ) = (D : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hD.le]
    push_cast
    rfl
  have hsq2 : (D : ℂ) ^ (1 / 2 : ℂ) * (D : ℂ) ^ (1 / 2 : ℂ) = D := by
    rw [← cpow_add _ _ hD0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, cpow_one]
  have hX : (D : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hAs : (A : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hA0)
  have hDs : (D : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hχa : (idealChar χ a : ℂ) ≠ 0 := Units.ne_zero _
  have hχd : (idealChar χ (differentUnit K) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hB, cpow_sub _ _ hD0, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_mul, hsq,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [inv_pow]
  field_simp
  rw [sq, hsq2]
  ring

end ClassFE

section Entire

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \prod_{w \text{ complex}} 2^{-i \theta_w} \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, i \theta_w)$, with $A$ = `Langlands.Tate.archRatio`. -/
noncomputable def shiftHeckeCompleted (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s * torusArch K θ *
    ∑ C : ClassGroup (𝓞 K), shiftHeckeClassCompleted χ n θ (classRepUnit K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \prod_{w \text{ complex}} 2^{i \theta_w} \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1})$ of the parameters $(n_w, i \theta_w)$. -/
noncomputable def shiftHeckeCompletedConj (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s * torusArch K (-θ) *
    ∑ C : ClassGroup (𝓞 K), shiftHeckeClassCompletedConj χ n θ (dualUnit K (classRepUnit K C)) s

/-- **The completed $L$-functions with the shifts are entire.** -/
theorem differentiable_shiftHeckeCompleted (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (hz : ShiftMeanZero K n θ) :
    Differentiable ℂ (shiftHeckeCompleted χ n θ) ∧
      Differentiable ℂ (shiftHeckeCompletedConj χ n θ) := by
  have hp := realWeight_absParam_le_one hn
  have hχ := signInfinityWeight_mul_torusWeight_unit h0 hn
  have hb : ∀ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Differentiable ℂ fun s : ℂ =>
        ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := fun b =>
    differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 (absNorm_pos K b).ne'))
  have hm : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2 :=
    (differentiable_id.const_mul _).div_const 2
  refine ⟨(((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (differentiable_const _)).mul (Differentiable.fun_sum fun C _ => ?_),
    (((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (differentiable_const _)).mul (Differentiable.fun_sum fun C _ => ?_)⟩
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_shiftCompletedPartialHecke hp hχ hz).comp hm)
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_shiftCompletedPartialHeckeConj hp hχ hz _).comp hm)

/-- **The entire functional equation for unramified characters with imaginary shifts.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, i \theta_w)$ at each infinite place, where the $\theta_w$ are real and the signs of the $n_w$ are arbitrary, and let `Langlands.Tate.ShiftMeanZero` hold. Let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w |n_w|}$. -/
theorem entireFunctionalEquation_unramified_shift (h0 : ramifiedSet χ = ∅)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = (θ v : ℂ) * I) (hz : ShiftMeanZero K n θ) :
    EntireFunctionalEquation χ n n' t t' := by
  have ht0 : t = fun v => (θ v : ℂ) * I := funext ht
  subst ht0
  have hθ : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I) := hn
  have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w = ((-θ) w : ℂ) * I :=
    fun w => by
      have e := isArchimedeanParameter_unique (hn' w) (hθ w).inv
      refine ⟨e.1, ?_⟩
      rw [e.2, Pi.neg_apply, Complex.ofReal_neg, neg_mul]
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hθ)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hc : Ideal.absNorm χ.conductor = 1 := by
    rw [conductor_eq_prod, h0, Finset.prod_empty, Ideal.one_eq_top, Ideal.absNorm_top]
  obtain ⟨hd, hd'⟩ := differentiable_shiftHeckeCompleted h0 hθ hz
  refine ⟨shiftHeckeCompleted χ n θ, shiftHeckeCompletedConj χ n θ,
    (idealChar χ (differentUnit K) : ℂ) *
      (-I) ^ (∑ v, realWeight K (absParam K n) v + ∑ w, complexWeight K (absParam K n) w),
    hd, hd', fun s hs => ?_, fun s hs => ?_, ?_, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_imagShift (fun w => (hθ w).isReal) θ s,
      shiftHeckeCompleted, ← shiftGamma_mul_finiteLFunction h0 hθ hz hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_imagShift_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      gammaFactor_imagShift (fun w => (hθ w).isReal) (-θ) s, shiftHeckeCompletedConj,
      ← shiftGamma_mul_finiteLFunction_inv h0 hθ hz hs]
    field_simp
  · rw [norm_mul, norm_idealChar_of_unitary hu, norm_pow, norm_neg, Complex.norm_I, one_pow,
      mul_one]
  · have hD : (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) =
        ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [hc, Nat.cast_one, mul_one, ← Complex.ofReal_intCast, Int.cast_abs]
    rw [hD, shiftHeckeCompletedConj, ← archRatio_mul (absParam K n) s,
      ← torusArch_mul_torusConst, shiftHeckeCompleted]
    simp_rw [shiftHeckeClassCompleted_eq_conj h0 hθ hz]
    rw [← Finset.mul_sum]
    ring

end Entire

section MeanZero

variable {K : Type*} [Field K] [NumberField K]

/-- For $n \neq 0$ the condition `Langlands.Tate.ShiftMeanZero` holds, since the twisted term of $\alpha = 0$ is zero. -/
theorem shiftMeanZero_of_ne_zero {n : InfinitePlace K → ℤ} (hne : ∃ w, n w ≠ 0)
    (θ : InfinitePlace K → ℝ) : ShiftMeanZero K n θ := fun y _ =>
  integral_shiftHeckeTerm_zero (weight_ne_zero (absParam_nonneg n) (absParam_ne_zero hne)) y

omit [NumberField K] in
/-- The integral of $e^{i L x}$ over $[0, 1)$ is $0$ if $L \neq 0$ and $e^{i L} = 1$. -/
theorem integral_Ico_exp_mul_I {L : ℝ} (hL : L ≠ 0) (h1 : cexp ((L : ℂ) * I) = 1) :
    ∫ x in Ico (0 : ℝ) 1, cexp (((L * x : ℝ) : ℂ) * I) = 0 := by
  have hc : (L : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hL) I_ne_zero
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have e : (fun x : ℝ => cexp (((L * x : ℝ) : ℂ) * I)) = fun x : ℝ => cexp ((L : ℂ) * I * x) :=
    funext fun x => by push_cast; ring_nf
  rw [e, integral_exp_mul_complex hc, Complex.ofReal_one, mul_one, h1, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, sub_self, zero_div]

/-- The torus factor in the unit coordinates: $\tau_\theta(y e^{2 \sum_i c_i \log |\varepsilon_i|}) = \tau_\theta((y)_w) \prod_i e^{i L_i c_i}$, with $L_i = \sum_w n_w \theta_w \log |\varepsilon_i|_w$. -/
theorem torusFactor_unitScale (θ : InfinitePlace K → ℝ) {y : ℝ} (hy : 0 < y)
    (c : Fin (rank K) → ℝ) :
    torusFactor θ (unitScale K y c) =
      cexp (((∑ w, (mult w : ℝ) * θ w / 2 * Real.log y : ℝ) : ℂ) * I) *
        ∏ i, cexp ((((∑ w, (mult w : ℝ) * θ w * unitLog K i w) * c i : ℝ) : ℂ) * I) := by
  have hl : ∀ w, Real.log (unitScale K y c w) = Real.log y + 2 * ∑ i, c i * unitLog K i w :=
    fun w => by
      rw [unitScale, Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hs : ∑ w, (mult w : ℝ) * θ w / 2 * Real.log (unitScale K y c w) =
      ∑ w, (mult w : ℝ) * θ w / 2 * Real.log y +
        ∑ i, (∑ w, (mult w : ℝ) * θ w * unitLog K i w) * c i := by
    simp only [hl, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring
  rw [torusFactor, hs, Complex.ofReal_add, add_mul, Complex.exp_add]
  congr 1
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- **The mean value $0$ for the weight $0$.** Let $n = 0$, let $\tau_\theta$ be trivial on the units, and let $\theta$ be not constant. Then `Langlands.Tate.ShiftMeanZero` holds. The reason is that some $L_i = \sum_w n_w \theta_w \log |\varepsilon_i|_w$ is not zero by `Langlands.Tate.eq_of_sum_mult_log_unit_eq_zero`, and $\int_0^1 e^{i L_i c} \, dc = 0$ since $e^{i L_i} = 1$. -/
theorem shiftMeanZero_of_not_const {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn0 : ∀ w, n w = 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (u : K) * torusWeight θ (u : K) = 1)
    (hθ : ∃ w, θ w ≠ θ w₀) : ShiftMeanZero K n θ := by
  have hp : realWeight K (absParam K n) = 0 := funext fun v => by
    simp [realWeight, absParam, hn0]
  have hk : complexWeight K (absParam K n) = 0 := funext fun v => by
    simp [complexWeight, absParam, hn0]
  have hS : ∀ α : K, signInfinityWeight (paramSign K n) 0 0 α = 1 := fun α => by
    simp [signInfinityWeight, signPlacePhase]
  have hT : ∀ t, shiftHeckeTerm (paramSign K n) 0 0 θ 0 t = torusFactor θ t := fun t => by
    simp [shiftHeckeTerm, signHeckeTerm, signMixedGaussWeight, realGaussWeight, gaussWeight,
      weightExp, norm_flipConj]
  set L : Fin (rank K) → ℝ := fun i => ∑ w, (mult w : ℝ) * θ w * unitLog K i w with hL
  have hL1 : ∀ i, cexp ((L i : ℂ) * I) = 1 := fun i => by
    have e := hχ (fundSystem K i)
    rw [hp, hk, hS, one_mul, torusWeight, Complex.exp_neg, inv_eq_one] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i, L i ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨w, hw⟩ := hθ
    exact hw (eq_of_sum_mult_log_unit_eq_zero θ (sum_mult_log_unit_eq_zero θ h) w)
  unfold ShiftMeanZero
  intro y hy
  rw [hp, hk]
  simp_rw [hT, torusFactor_unitScale θ hy]
  rw [integral_const_mul]
  refine mul_eq_zero_of_right _ ?_
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i x => cexp (((L i * x : ℝ) : ℂ) * I))]
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (integral_Ico_exp_mul_I hi₀ (hL1 i₀))

end MeanZero

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the unramified characters with arbitrary shifts.** Let $\xi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n_v, t_v)$ at the infinite places. The shifts $t_v$ can be different at different places, and the integers $n_w$ at the complex places can have arbitrary signs. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. -/
theorem heckeFunctionalEquation_of_unramified_general (ξ : HeckeCharacter K)
    (hu : ∀ v, ξ.IsUnramifiedAt v) (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(ξ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = ξ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = ξ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm ξ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  by_cases hc : ∃ t₀, ∀ v, t v = t₀
  · obtain ⟨t₀, ht⟩ := hc
    exact heckeFunctionalEquation_of_unramified_const_shift ξ hu n n' t t' hn hn' t₀ ht
  have h0ξ : ramifiedSet ξ = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun v hv =>
    mem_ramifiedSet.1 hv (hu v)
  have hre := re_eq_of_isArchimedeanParameter h0ξ hn
  set t₀ : ℂ := (((t w₀).re : ℝ) : ℂ) with ht₀
  obtain ⟨χ, hξ⟩ : ∃ χ : HeckeCharacter K, ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ t₀ :=
    ⟨ξ * normPowerChar K (-t₀), fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]⟩
  have hξ' := inv_of_twist hξ
  set θ : InfinitePlace K → ℝ := fun v => (t v).im with hθdef
  have htθ : ∀ v, t v - t₀ = (θ v : ℂ) * I := fun v => by
    apply Complex.ext
    · simp [ht₀, hre v]
    · simp [ht₀, hθdef]
  have hp : ∀ v, χ.IsArchimedeanParameter v (n v) (t v - t₀) := fun v =>
    isArchimedeanParameter_of_twist hξ (hn v)
  have hp' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v + t₀) := fun v => by
    have h := isArchimedeanParameter_of_twist hξ' (hn' v)
    rwa [sub_neg_eq_add] at h
  have hθ : ∀ v, χ.IsArchimedeanParameter v (n v) ((θ v : ℂ) * I) := fun v => by
    rw [← htθ v]
    exact hp v
  have hχu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hθ)
  have h0χ : ramifiedSet χ = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun v hv =>
    mem_ramifiedSet.1 hv ((isUnramifiedAt_twist_iff hξ v).1 (hu v))
  have hz : ShiftMeanZero K n θ := by
    by_cases hne : ∃ w, n w ≠ 0
    · exact shiftMeanZero_of_ne_zero hne θ
    · push Not at hne
      refine shiftMeanZero_of_not_const hne (signInfinityWeight_mul_torusWeight_unit h0χ hθ) ?_
      by_contra hθc
      push Not at hθc
      exact hc ⟨t w₀, fun v => Complex.ext (hre v) (hθc v)⟩
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) :=
    entireFunctionalEquation_unramified_shift h0χ hp hp' htθ hz
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

end Assembly

end Langlands.Tate
