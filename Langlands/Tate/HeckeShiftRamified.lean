/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeShiftRamifiedFE
import Langlands.Tate.HeckeShift

/-!
# The entire functional equation for the ramified characters with unequal shifts

Let $\chi$ be a Hecke character that is ramified at one finite place, with the parameters $(n_w, i \theta_w)$ at each infinite place. The $\theta_w$ are real and can be different at different places, and the signs of the $n_w$ are arbitrary. This file proves `Langlands.Tate.EntireFunctionalEquation` for $\chi$.

The proof is that of `Langlands/Tate/HeckeRamifiedSign.lean`, with the twisted partial sums of `Langlands/Tate/HeckeShiftRamifiedFE.lean`. The unit condition of the coefficients $c_J$ now contains the torus factor $\tau_\theta$. The archimedean factor of $(n_w, i \theta_w)$ is `Langlands.Tate.gammaFactor_imagShift`, and the constant $\tau_\theta((n_w^2)_w)$ of the change of variable changes $\prod_{w \text{ complex}} 2^{-i \theta_w}$ to $\prod_{w \text{ complex}} 2^{i \theta_w}$ (`Langlands.Tate.torusArch_mul_torusConst`).

## Main definitions

* `Langlands.Tate.shiftRamifiedClassCompleted`, `Langlands.Tate.shiftRamifiedClassCompletedConj`: the completed class sums of $\chi$ and $\chi^{-1}$.
* `Langlands.Tate.shiftRamifiedCompleted`, `Langlands.Tate.shiftRamifiedCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$.

## Main results

* `Langlands.Tate.periodicCoeff_unit_mul_shift`: the unit condition of $c_J$ with the torus factor.
* `Langlands.Tate.shiftRamifiedClassCompleted_eq_conj`: the functional equation of one class sum.
* `Langlands.Tate.shiftGamma_mul_finiteLFunction_ramified`: the $L$-function as a sum of the class sums.
* `Langlands.Tate.entireFunctionalEquation_ramified_shift`: the entire functional equation.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem IsDedekindDomain
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Unit

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The unit condition for the periodic coefficient with the shifts.** Let $\chi$ have the parameters $(n_w, i \theta_w)$ at each infinite place, with real $\theta_w$ and arbitrary signs of the $n_w$. Then $c_J(u \alpha) \chi^{\varepsilon, p, k}_\infty(u) \tau_\theta(u) = c_J(\alpha)$ for each unit $u$ of $\mathcal{O}_K$, each $\alpha \in K$ and each nonzero fractional ideal $J$. -/
theorem periodicCoeff_unit_mul_shift {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (α : K) :
    periodicCoeff χ J ((u : K) * α) * signInfinityWeight (paramSign K n)
        (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (u : K) *
        torusWeight θ (u : K) =
      periodicCoeff χ J α := by
  have h : (infChar χ (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℂ) *
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) (u : K) * torusWeight θ (u : K) = 1 :=
    infChar_mul_signInfinityWeight_mul_torusWeight hn _
  rw [periodicCoeff_unit_mul]
  linear_combination (periodicCoeff χ J α) * h

/-- **The periodic coefficient and the coefficient of the $L$-series with the shifts.** If $\chi$ has the parameters $(n_w, i \theta_w)$ and $\alpha \neq 0$, then $c_J(\alpha) \chi^{\varepsilon, p, k}_\infty(\alpha) \tau_\theta(\alpha) = \chi((\alpha) J^{-1})$, where the right side is `Langlands.Tate.rayCoeff`. -/
theorem periodicCoeff_mul_shift {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K} (hα : α ≠ 0) :
    periodicCoeff χ J α * signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) α * torusWeight θ α =
      rayCoeff χ J α := by
  have h := infChar_mul_signInfinityWeight_mul_torusWeight hn (Units.mk0 α hα)
  rw [Units.val_mk0] at h
  rw [periodicCoeff, dite_eq_left hα]
  linear_combination (rayCoeff χ J α) * h

end Unit

section Classes

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

variable (χ) in
/-- The completed class sum $\Lambda_J(s, \chi) = N(J)^s \Lambda_J(n s / 2)$ of the weight $(p, k)$ of $|n|$, the sign $\varepsilon$ of $n$ and the shifts $i \theta_w$. Here $\Lambda_J$ on the right is `Langlands.Tate.shiftRamifiedPartial`. -/
noncomputable def shiftRamifiedClassCompleted (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm 𝔣[J] : ℝ) : ℂ) ^ s *
    shiftRamifiedPartial χ (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) θ J ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_D(s, \chi^{-1}) = N(D)^s \Lambda^*_D(n s / 2)$ with $D = (\mathfrak{f} J)^\vee$, of the weight $(p, k)$ of $|n|$, the sign $\varepsilon$ of $n$ and the shifts $i \theta_w$. -/
noncomputable def shiftRamifiedClassCompletedConj (n : InfinitePlace K → ℤ)
    (θ : InfinitePlace K → ℝ) (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    shiftRamifiedPartialConj χ (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) θ J ((finrank ℚ K : ℂ) * s / 2)

/-- **The class sum as a Dirichlet series.** Let $\chi$ have the parameters $(n_w, i \theta_w)$ with real $\theta_w$, and let $\mathrm{Re}\, s > 1$. Then $\Lambda_J(s, \chi)$ is the sum over the integral ideals $I$ in the class $[J]^{-1}$ of $w_K \, \Gamma_{p, k}^\theta(s) \, \chi(I) N(I)^{-s}$, where $\chi(I) = 0$ if $I$ is not prime to $\mathfrak{f}$. -/
theorem hasSum_shiftRamifiedClassCompleted {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (FractionalIdeal.mk0 K J))⁻¹ then
          (torsionOrder K : ℂ) *
            shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ s *
            rayWeight χ s I else 0)
      (shiftRamifiedClassCompleted χ n θ J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have h := hasSum_shiftRamifiedPartial hu J (periodicCoeff_unit_mul_shift hn _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [shiftRamifiedClassCompleted]
  refine hasSum_rayCoeff_class χ _ (f := fun α => periodicCoeff χ (FractionalIdeal.mk0 K J) α *
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) α * torusWeight θ α)
    (fun α hα => periodicCoeff_mul_shift hn _ hα) ?_
  convert h using 1
  funext I
  ring

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_shiftRamifiedClassCompleted`, $\Lambda^*_D(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[D]^{-1}$ of $w_K \, \Gamma_{p, k}^{-\theta}(s) \, \chi^{-1}(I) N(I)^{-s}$. -/
theorem hasSum_shiftRamifiedClassCompletedConj {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (gaussDual χ J))⁻¹ then
          (torsionOrder K : ℂ) *
            shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (-θ) s *
            rayWeight χ⁻¹ s I else 0)
      (shiftRamifiedClassCompletedConj χ n θ J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have h := hasSum_shiftRamifiedPartialConj hu J (periodicCoeff_unit_mul_shift hn _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [shiftRamifiedClassCompletedConj]
  refine hasSum_rayCoeff_class χ⁻¹ _ (f := fun β => conj (periodicCoeff χ (gaussDual χ J) β) *
      conj (signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) β) * torusWeight (-θ) β)
    (fun β hβ => by
      rw [← conj_torusWeight, ← map_mul, ← map_mul, periodicCoeff_mul_shift hn _ hβ,
        conj_rayCoeff hu]) ?_
  convert h using 1
  funext I
  ring

/-- **The functional equation of one class sum.** Let $\chi$ be ramified at one place, with the parameters $(n_w, i \theta_w)$ at each infinite place. Then for all complex $s$, $$\Lambda_J(s, \chi) = W \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, \tau_\theta((n_w^2)_w) \, (|d_K| N(\mathfrak{f}))^{1/2 - s} \, \Lambda^*_D(1 - s, \chi^{-1}),$$ with $D = (\mathfrak{f} J)^\vee$ and $W$ = `Langlands.Tate.ramifiedRootNumber` of $|n|$. -/
theorem shiftRamifiedClassCompleted_eq_conj (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    shiftRamifiedClassCompleted χ n θ J s = ramifiedRootNumber χ (absParam K n) *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      torusConst θ *
      (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
      shiftRamifiedClassCompletedConj χ n θ J (1 - s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have hc := periodicCoeff_unit_mul_shift hn (gaussDual χ J)
  set A : ℝ := (FractionalIdeal.absNorm 𝔣[J] : ℝ)
  set F : ℝ := (Ideal.absNorm χ.conductor : ℝ)
  set D : ℝ := |(discr K : ℝ)|
  have hA : 0 < A := absNorm_pos K _
  have hF : 0 < F := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 =>
    conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hNf : (FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℝ) = F * A := by
    rw [coe_mk0_conductorNZ_mul, map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul,
      Rat.cast_natCast]
  have hNG : (FractionalIdeal.absNorm (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      (F * A * D)⁻¹ := by
    rw [← hNf]
    exact absNorm_dualUnit (K := K) _
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) = ((D * F : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.ofReal_intCast, Int.cast_abs, Complex.ofReal_natCast]
  have key := cpow_mul_inv_eq hA hF hD (nrComplexPlaces K) s
  unfold shiftRamifiedClassCompleted shiftRamifiedClassCompletedConj
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring,
    shiftRamifiedPartial_sub hS hu (realWeight_absParam_le_one hn) J hc, heckeScale_cpow,
    ramifiedRootConst, heckeRootConst, periodicGaussSum_eq_one hS hu J, hNG, hX, hNf,
    ramifiedRootNumber]
  linear_combination ((-I) ^ (∑ v, realWeight K (absParam K n) v +
      ∑ w, complexWeight K (absParam K n) w) *
    periodicGaussSum χ 1 * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s))) * torusConst θ *
    shiftRamifiedPartialConj χ (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) θ J ((finrank ℚ K : ℂ) * (1 - s) / 2)) * key

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The $L$-function as a sum over the ideal classes.** Let $\chi$ have the parameters $(n_w, i \theta_w)$ at each infinite place. For $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}^\theta(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi),$$ where $\mathfrak{a}_C$ is the chosen integral ideal of the class $C$. -/
theorem shiftGamma_mul_finiteLFunction_ramified {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) *
        shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) θ s *
        χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), shiftRamifiedClassCompleted χ n θ (classIdeal K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_shiftRamifiedClassCompleted hn (classIdeal K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (FractionalIdeal.mk0 K (classIdeal K C)))⁻¹) ↔
        ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [← classRepUnit, mk_classRepUnit]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.shiftGamma_mul_finiteLFunction_ramified`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}^{-\theta}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1}).$$ -/
theorem shiftGamma_mul_finiteLFunction_inv_ramified {n : InfinitePlace K → ℤ}
    {θ : InfinitePlace K → ℝ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I))
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) *
        shiftGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (-θ) s *
        χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), shiftRamifiedClassCompletedConj χ n θ (classIdeal K C) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_shift hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_shiftRamifiedClassCompletedConj hn (classIdeal K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (gaussDual χ (classIdeal K C)))⁻¹) ↔
        ((ramifiedDualClass χ).symm (ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_gaussDual_classIdeal, Equiv.symm_apply_eq]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end LFunction

section Entire

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \prod_{w \text{ complex}} 2^{-i \theta_w} \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, i \theta_w)$, with $A$ = `Langlands.Tate.archRatio` of $|n|$. -/
noncomputable def shiftRamifiedCompleted (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s * torusArch K θ *
    ∑ C : ClassGroup (𝓞 K), shiftRamifiedClassCompleted χ n θ (classIdeal K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \prod_{w \text{ complex}} 2^{i \theta_w} \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1})$ of the parameters $(n_w, i \theta_w)$. -/
noncomputable def shiftRamifiedCompletedConj (n : InfinitePlace K → ℤ) (θ : InfinitePlace K → ℝ)
    (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s * torusArch K (-θ) *
    ∑ C : ClassGroup (𝓞 K), shiftRamifiedClassCompletedConj χ n θ (classIdeal K C) s

/-- **The completed $L$-functions of a ramified character with the shifts are entire.** -/
theorem differentiable_shiftRamifiedCompleted (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) ((θ w : ℂ) * I)) :
    Differentiable ℂ (shiftRamifiedCompleted χ n θ) ∧
      Differentiable ℂ (shiftRamifiedCompletedConj χ n θ) := by
  have hp := realWeight_absParam_le_one hn
  have hu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hn)
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
  · exact (hb _).mul ((differentiable_shiftRamifiedPartial hS hu hp _).comp hm)
  · exact (hb _).mul ((differentiable_shiftRamifiedPartialConj hS hu hp _
      (periodicCoeff_unit_mul_shift hn _)).comp hm)

/-- The root number of a ramified character is of norm $1$, if $\chi$ is unitary. -/
theorem norm_ramifiedRootNumber_of_unitary (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (q : InfinitePlace K → ℤ) :
    ‖ramifiedRootNumber χ q‖ = 1 := by
  have h2 := norm_periodicGaussSum_sq hS hu 1
  have hF : 0 < (Ideal.absNorm χ.conductor : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 =>
    conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hτ : ‖periodicGaussSum χ 1‖ = √(Ideal.absNorm χ.conductor : ℝ) := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [ramifiedRootNumber, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow,
    one_mul, hτ, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_inv_cancel₀ (Real.sqrt_pos.2 hF).ne']

/-- **The entire functional equation for the ramified characters with imaginary shifts.** Let $\chi$ be ramified at one finite place, with the parameters $(n_w, i \theta_w)$ at each infinite place, where the $\theta_w$ are real and the signs of the $n_w$ are arbitrary. Let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W$ = `Langlands.Tate.ramifiedRootNumber` of $|n|$. -/
theorem entireFunctionalEquation_ramified_shift (hS : (ramifiedSet χ).Nonempty)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ} {θ : InfinitePlace K → ℝ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = (θ v : ℂ) * I) :
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
  obtain ⟨hd, hd'⟩ := differentiable_shiftRamifiedCompleted hS hθ
  refine ⟨shiftRamifiedCompleted χ n θ, shiftRamifiedCompletedConj χ n θ,
    ramifiedRootNumber χ (absParam K n), hd, hd', fun s hs => ?_, fun s hs => ?_,
    norm_ramifiedRootNumber_of_unitary hS hu _, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_imagShift (fun w => (hθ w).isReal) θ s,
      shiftRamifiedCompleted, ← shiftGamma_mul_finiteLFunction_ramified hθ hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_imagShift_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      gammaFactor_imagShift (fun w => (hθ w).isReal) (-θ) s, shiftRamifiedCompletedConj,
      ← shiftGamma_mul_finiteLFunction_inv_ramified hθ hs]
    field_simp
  · rw [shiftRamifiedCompletedConj, ← archRatio_mul (absParam K n) s,
      ← torusArch_mul_torusConst, shiftRamifiedCompleted]
    simp_rw [shiftRamifiedClassCompleted_eq_conj hS hθ]
    rw [← Finset.mul_sum]
    ring

end Entire

end Langlands.Tate
