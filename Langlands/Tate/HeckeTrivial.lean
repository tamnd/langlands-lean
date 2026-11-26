/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.DedekindEuler

/-!
# Hecke's theorem for the trivial character

Let $K$ be a number field with $r_2$ complex places and discriminant $d_K$. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for the trivial Hecke character. The completed $L$-function of the trivial character is $$\Lambda(s) = 2^{r_2} \Gamma_K(s) \zeta_K(s) = 2^{r_2} |d_K|^{-s/2} \xi_K(s),$$ where $\xi_K$ is the completed Dedekind zeta function of `Langlands/Tate/DedekindFE.lean`. The constants are $\sigma = 0$, $W = 1$ and $s_0 = 0$, and the conductor is $(1)$.

The proof writes $\xi_K$ in the form $E(u) + F_0(u) / u + F_1(u) / (u - 1)$ with $E$, $F_0$ and $F_1$ entire. This comes from the formula $\Lambda(s) = \Lambda_0(s) - 1/s - \varepsilon / (k - s)$ of each theta pair. The values are $F_0(0) = -2 h_K c / n$ and $F_1(1) = 2 h_K c / n$, with $c = 2^{r - r_2} R_K / w_K$ and $h_K$ the class number. These values are not zero, so $\xi_K$ has simple poles at $0$ and $1$ and no other poles.

## Main results

* `Langlands.Tate.meromorphicOn_poleShape`, `Langlands.Tate.meromorphicOrderAt_poleShape_zero` and `Langlands.Tate.meromorphicOrderAt_poleShape_one`: a function $E(u) + F_0(u)/u + F_1(u)/(u-1)$ is meromorphic, with simple poles at $0$ and $1$ when $F_0(0) \neq 0$ and $F_1(1) \neq 0$.
* `Langlands.Tate.dedekindXi_eq_poleShape`: the decomposition of $\xi_K$.
* `Langlands.Tate.meromorphicOrderAt_dedekindXi_zero` and `Langlands.Tate.meromorphicOrderAt_dedekindXi_one`: $\xi_K$ has simple poles at $0$ and $1$.
* `Langlands.Tate.heckeFunctionalEquationAt_one`: the conclusion of `HeckeFunctionalEquationAt K` for the trivial character.
-/

namespace Langlands.Tate

open Filter Topology Module NumberField NumberField.InfinitePlace NumberField.Units

open scoped Classical nonZeroDivisors

section PoleShape

variable {E F₀ F₁ : ℂ → ℂ}

/-- A function of the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$ with $E$, $F_0$, $F_1$ entire is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_poleShape (hE : Differentiable ℂ E) (h₀ : Differentiable ℂ F₀)
    (h₁ : Differentiable ℂ F₁) :
    MeromorphicOn (fun u => E u + F₀ u / u + F₁ u / (u - 1)) Set.univ := by
  intro u _
  exact (((hE.analyticAt u).meromorphicAt).add
    (((h₀.analyticAt u).meromorphicAt).div (analyticAt_id.meromorphicAt))).add
    (((h₁.analyticAt u).meromorphicAt).div
      ((analyticAt_id.sub analyticAt_const).meromorphicAt))

/-- A function of the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$ is analytic outside $0$ and $1$. -/
theorem analyticAt_poleShape (hE : Differentiable ℂ E) (h₀ : Differentiable ℂ F₀)
    (h₁ : Differentiable ℂ F₁) {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    AnalyticAt ℂ (fun u => E u + F₀ u / u + F₁ u / (u - 1)) u :=
  ((hE.analyticAt u).add ((h₀.analyticAt u).div analyticAt_id hu0)).add
    ((h₁.analyticAt u).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hu1))

/-- If $F_0(0) \neq 0$, then $E(u) + F_0(u)/u + F_1(u)/(u-1)$ has a simple pole at $0$. -/
theorem meromorphicOrderAt_poleShape_zero (hE : Differentiable ℂ E) (h₀ : Differentiable ℂ F₀)
    (h₁ : Differentiable ℂ F₁) (hne : F₀ 0 ≠ 0) :
    meromorphicOrderAt (fun u => E u + F₀ u / u + F₁ u / (u - 1)) 0 = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl,
    meromorphicOrderAt_eq_int_iff (meromorphicOn_poleShape hE h₀ h₁ 0 trivial)]
  refine ⟨fun u => u * E u + F₀ u + u * F₁ u / (u - 1), ?_, ?_, ?_⟩
  · exact ((analyticAt_id.mul (hE.analyticAt 0)).add (h₀.analyticAt 0)).add
      ((analyticAt_id.mul (h₁.analyticAt 0)).div (analyticAt_id.sub analyticAt_const)
        (by norm_num))
  · simpa using hne
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u ≠ 0 := hu
    simp only [sub_zero, zpow_neg, zpow_one, smul_eq_mul]
    field_simp

/-- If $F_1(1) \neq 0$, then $E(u) + F_0(u)/u + F_1(u)/(u-1)$ has a simple pole at $1$. -/
theorem meromorphicOrderAt_poleShape_one (hE : Differentiable ℂ E) (h₀ : Differentiable ℂ F₀)
    (h₁ : Differentiable ℂ F₁) (hne : F₁ 1 ≠ 0) :
    meromorphicOrderAt (fun u => E u + F₀ u / u + F₁ u / (u - 1)) 1 = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl,
    meromorphicOrderAt_eq_int_iff (meromorphicOn_poleShape hE h₀ h₁ 1 trivial)]
  refine ⟨fun u => (u - 1) * E u + (u - 1) * F₀ u / u + F₁ u, ?_, ?_, ?_⟩
  · exact (((analyticAt_id.sub analyticAt_const).mul (hE.analyticAt 1)).add
      (((analyticAt_id.sub analyticAt_const).mul (h₀.analyticAt 1)).div analyticAt_id
        one_ne_zero)).add (h₁.analyticAt 1)
  · simpa using hne
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u - 1 ≠ 0 := sub_ne_zero.2 hu
    simp only [zpow_neg, zpow_one, smul_eq_mul]
    field_simp

/-- The product of an entire function $G$ and a function of the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$ has the same form. -/
theorem mul_poleShape (G : ℂ → ℂ) (u : ℂ) :
    G u * (E u + F₀ u / u + F₁ u / (u - 1)) =
      G u * E u + G u * F₀ u / u + G u * F₁ u / (u - 1) := by
  ring

/-- The reflection $u \mapsto 1 - u$ of a function of the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$ has the same form, with $F_0$ and $F_1$ exchanged. -/
theorem poleShape_one_sub (u : ℂ) :
    E (1 - u) + F₀ (1 - u) / (1 - u) + F₁ (1 - u) / (1 - u - 1) =
      E (1 - u) + (-F₁ (1 - u)) / u + (-F₀ (1 - u)) / (u - 1) := by
  have h1 : 1 - u = -(u - 1) := by ring
  have h2 : 1 - u - 1 = -u := by ring
  rw [h2, div_neg, neg_div, h1, div_neg, neg_div]
  ring

end PoleShape

section Decomposition

variable {K : Type*} [Field K] [NumberField K]

/-- The constant terms of the theta pair are $1$, so $\Lambda(s) = \Lambda_0(s) - 1/s - \varepsilon/(n/2 - s)$. -/
theorem Λ_unitThetaFEPair_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (unitThetaFEPair a).Λ s = (unitThetaFEPair a).Λ₀ s - 1 / s -
      (unitThetaFEPair a).ε / ((finrank ℚ K : ℂ) / 2 - s) := by
  have hk : ((unitThetaFEPair a).k : ℂ) = (finrank ℚ K : ℂ) / 2 := by
    change (((finrank ℚ K : ℝ) / 2 : ℝ) : ℂ) = _
    push_cast
    rfl
  rw [WeakFEPair.Λ, hk]
  change _ - (1 / s) • (1 : ℂ) - (_ / _) • (1 : ℂ) = _
  simp only [smul_eq_mul, mul_one]

/-- The factor $B_{\mathfrak{a}}(u) = |d_K|^{u/2} N(\mathfrak{a})^u$ of $\psi_{\mathfrak{a}}$. -/
noncomputable def classFactor (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℂ) : ℂ :=
  ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
    ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ u

theorem differentiable_classFactor (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (classFactor a) := by
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'
  have hN : ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (absNorm_pos K a).ne'
  exact (differentiable_id.const_cpow (Or.inl hA)).mul (differentiable_id.const_cpow (Or.inl hN))

theorem classFactor_zero (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : classFactor a 0 = 1 := by
  simp [classFactor]

/-- The root number of the theta pair of $\mathfrak{a}$ is the inverse of $B_{\mathfrak{a}}(1)$. -/
theorem ε_mul_classFactor_one (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (unitThetaFEPair a).ε * classFactor a 1 = 1 := by
  have hA : (√|(discr K : ℝ)| : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'
  have hN : (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 :=
    (absNorm_pos K a).ne'
  have hε : (unitThetaFEPair a).ε = ((((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) :
      ℝ) * Real.sqrt (abs (discr K : ℝ)))⁻¹ : ℝ) : ℂ) := rfl
  rw [hε, classFactor, Complex.cpow_one, Complex.cpow_one, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_one]
  congr 1
  field_simp

/-- The function $\psi_{\mathfrak{a}}$ in the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$. -/
theorem classXi_eq_poleShape (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℂ) :
    classXi a u = classFactor a u * (unitThetaFEPair a).Λ₀ ((finrank ℚ K : ℂ) * u / 2) +
      (-(2 / (finrank ℚ K : ℂ)) * classFactor a u) / u +
      (2 * (unitThetaFEPair a).ε / (finrank ℚ K : ℂ) * classFactor a u) / (u - 1) := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  rw [classXi, Λ_unitThetaFEPair_eq, ← classFactor]
  rcases eq_or_ne u 0 with rfl | hu0
  · simp only [mul_zero, zero_div, div_zero, sub_zero, zero_sub, div_neg, div_one]
    field_simp
    ring
  rcases eq_or_ne u 1 with rfl | hu1
  · simp only [mul_one, sub_self, div_zero, sub_zero, add_zero]
    field_simp
    ring
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.2 hu1
  have h2 : (finrank ℚ K : ℂ) / 2 - (finrank ℚ K : ℂ) * u / 2 ≠ 0 := by
    rw [show (finrank ℚ K : ℂ) / 2 - (finrank ℚ K : ℂ) * u / 2 =
      -((finrank ℚ K : ℂ) / 2) * (u - 1) by ring]
    exact mul_ne_zero (neg_ne_zero.2 (div_ne_zero hn two_ne_zero)) hu1'
  field_simp
  ring

variable (K) in
/-- The constant $c_K = 2^{r - r_2} n R_K / w_K$ in front of $\xi_K$. -/
noncomputable def xiConst : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) / torsionOrder K

theorem xiConst_ne_zero : xiConst K ≠ 0 := by
  have hw : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
  exact div_ne_zero hC hw

variable (K) in
/-- The entire part $E$ of $\xi_K$. -/
noncomputable def xiE (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), classFactor (classRepUnit K C) u *
    (unitThetaFEPair (classRepUnit K C)).Λ₀ ((finrank ℚ K : ℂ) * u / 2)

variable (K) in
/-- The numerator $F_0$ of the pole of $\xi_K$ at $0$. -/
noncomputable def xiF₀ (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), -(2 / (finrank ℚ K : ℂ)) * classFactor (classRepUnit K C) u

variable (K) in
/-- The numerator $F_1$ of the pole of $\xi_K$ at $1$. -/
noncomputable def xiF₁ (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), 2 * (unitThetaFEPair (classRepUnit K C)).ε /
    (finrank ℚ K : ℂ) * classFactor (classRepUnit K C) u

variable (K) in
/-- The completed Dedekind zeta function in the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$. -/
theorem dedekindXi_eq_poleShape (u : ℂ) :
    dedekindXi K u = xiE K u + xiF₀ K u / u + xiF₁ K u / (u - 1) := by
  rw [dedekindXi, ← xiConst]
  simp_rw [classXi_eq_poleShape]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, xiE,
    xiF₀, xiF₁]
  ring

variable (K) in
theorem differentiable_xiE : Differentiable ℂ (xiE K) := by
  refine Differentiable.const_mul (Differentiable.fun_sum fun C _ => ?_) _
  exact (differentiable_classFactor _).mul ((unitThetaFEPair _).differentiable_Λ₀.comp
    (by fun_prop : Differentiable ℂ fun u : ℂ => (finrank ℚ K : ℂ) * u / 2))

variable (K) in
theorem differentiable_xiF₀ : Differentiable ℂ (xiF₀ K) :=
  Differentiable.const_mul (Differentiable.fun_sum fun _ _ =>
    (differentiable_classFactor _).const_mul _) _

variable (K) in
theorem differentiable_xiF₁ : Differentiable ℂ (xiF₁ K) :=
  Differentiable.const_mul (Differentiable.fun_sum fun _ _ =>
    (differentiable_classFactor _).const_mul _) _

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 K)) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

variable (K) in
/-- $F_0(0) = -2 h_K c_K / n \neq 0$. -/
theorem xiF₀_zero_ne_zero : xiF₀ K 0 ≠ 0 := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  simp only [xiF₀, classFactor_zero, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_ne_zero xiConst_ne_zero (mul_ne_zero card_classGroup_ne_zero
    (neg_ne_zero.2 (div_ne_zero two_ne_zero hn)))

variable (K) in
/-- $F_1(1) = 2 h_K c_K / n \neq 0$. -/
theorem xiF₁_one_ne_zero : xiF₁ K 1 ≠ 0 := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  have h : ∀ C : ClassGroup (𝓞 K), 2 * (unitThetaFEPair (classRepUnit K C)).ε /
      (finrank ℚ K : ℂ) * classFactor (classRepUnit K C) 1 = 2 / (finrank ℚ K : ℂ) := by
    intro C
    rw [div_mul_eq_mul_div, mul_assoc, ε_mul_classFactor_one, mul_one]
  simp only [xiF₁, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_ne_zero xiConst_ne_zero (mul_ne_zero card_classGroup_ne_zero
    (div_ne_zero two_ne_zero hn))

variable (K) in
/-- The completed Dedekind zeta function is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_dedekindXi : MeromorphicOn (dedekindXi K) Set.univ := by
  rw [show dedekindXi K = fun u => xiE K u + xiF₀ K u / u + xiF₁ K u / (u - 1) from
    funext (dedekindXi_eq_poleShape K)]
  exact meromorphicOn_poleShape (differentiable_xiE K) (differentiable_xiF₀ K)
    (differentiable_xiF₁ K)

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at $0$. -/
theorem meromorphicOrderAt_dedekindXi_zero : meromorphicOrderAt (dedekindXi K) 0 = -1 := by
  rw [show dedekindXi K = fun u => xiE K u + xiF₀ K u / u + xiF₁ K u / (u - 1) from
    funext (dedekindXi_eq_poleShape K)]
  exact meromorphicOrderAt_poleShape_zero (differentiable_xiE K) (differentiable_xiF₀ K)
    (differentiable_xiF₁ K) (xiF₀_zero_ne_zero K)

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at $1$. -/
theorem meromorphicOrderAt_dedekindXi_one : meromorphicOrderAt (dedekindXi K) 1 = -1 := by
  rw [show dedekindXi K = fun u => xiE K u + xiF₀ K u / u + xiF₁ K u / (u - 1) from
    funext (dedekindXi_eq_poleShape K)]
  exact meromorphicOrderAt_poleShape_one (differentiable_xiE K) (differentiable_xiF₀ K)
    (differentiable_xiF₁ K) (xiF₁_one_ne_zero K)

end Decomposition

section Hecke

variable {K : Type*} [Field K] [NumberField K]

/-- For $\delta = \sqrt{|d_K|}$, $|d_K|^{1/2 - s} \delta^{s - 1} \delta^s = 1$. -/
theorem discr_cpow_mul_sqrt_cpow (s : ℂ) :
    (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - s) * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(1 - s)) *
      ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s = 1 := by
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hD : (((|discr K| : ℤ) : ℂ)) = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs]
  rw [hD, ofReal_cpow_eq_exp hd, ofReal_cpow_eq_exp (Real.sqrt_pos.2 hd),
    ofReal_cpow_eq_exp (Real.sqrt_pos.2 hd), ← Complex.exp_add, ← Complex.exp_add,
    Real.log_sqrt hd.le, ← Complex.exp_zero]
  congr 1
  push_cast
  ring

variable (K) in
/-- The completed $L$-function $\Lambda(s) = 2^{r_2} |d_K|^{-s/2} \xi_K(s)$ of the trivial Hecke character. -/
noncomputable def heckeLambdaOne (s : ℂ) : ℂ :=
  2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * dedekindXi K s

variable (K) in
/-- The function $\Lambda'(u) = |d_K|^{1/2 - u} \Lambda(1 - u)$. -/
noncomputable def heckeLambdaOne' (u : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - u) * heckeLambdaOne K (1 - u)

variable (K) in
theorem differentiable_heckeFactor :
    Differentiable ℂ (fun s : ℂ => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'
  exact (differentiable_neg.const_cpow (Or.inl hA)).const_mul _

variable (K) in
theorem heckeLambdaOne_eq_poleShape :
    heckeLambdaOne K = fun u =>
      2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiE K u +
      2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₀ K u / u +
      2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₁ K u / (u - 1) := by
  funext u
  rw [heckeLambdaOne, dedekindXi_eq_poleShape, mul_poleShape
    (fun u => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u))]

variable (K) in
theorem differentiable_heckeE : Differentiable ℂ (fun u =>
    2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiE K u) :=
  (differentiable_heckeFactor K).mul (differentiable_xiE K)

variable (K) in
theorem differentiable_heckeF₀ : Differentiable ℂ (fun u =>
    2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₀ K u) :=
  (differentiable_heckeFactor K).mul (differentiable_xiF₀ K)

variable (K) in
theorem differentiable_heckeF₁ : Differentiable ℂ (fun u =>
    2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₁ K u) :=
  (differentiable_heckeFactor K).mul (differentiable_xiF₁ K)

variable (K) in
theorem meromorphicOn_heckeLambdaOne : MeromorphicOn (heckeLambdaOne K) Set.univ := by
  rw [heckeLambdaOne_eq_poleShape]
  exact meromorphicOn_poleShape (differentiable_heckeE K) (differentiable_heckeF₀ K)
    (differentiable_heckeF₁ K)

variable (K) in
theorem analyticAt_heckeLambdaOne {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (heckeLambdaOne K) s := by
  rw [heckeLambdaOne_eq_poleShape]
  exact analyticAt_poleShape (differentiable_heckeE K) (differentiable_heckeF₀ K)
    (differentiable_heckeF₁ K) h0 h1

variable (K) in
theorem meromorphicOrderAt_heckeLambdaOne_zero : meromorphicOrderAt (heckeLambdaOne K) 0 = -1 := by
  rw [heckeLambdaOne_eq_poleShape]
  refine meromorphicOrderAt_poleShape_zero (differentiable_heckeE K) (differentiable_heckeF₀ K)
    (differentiable_heckeF₁ K) ?_
  simpa using xiF₀_zero_ne_zero K

variable (K) in
theorem meromorphicOrderAt_heckeLambdaOne_one : meromorphicOrderAt (heckeLambdaOne K) 1 = -1 := by
  rw [heckeLambdaOne_eq_poleShape]
  refine meromorphicOrderAt_poleShape_one (differentiable_heckeE K) (differentiable_heckeF₀ K)
    (differentiable_heckeF₁ K) ?_
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (Complex.cpow_ne_zero_iff.2 (Or.inl hA))) (xiF₁_one_ne_zero K)

variable (K) in
theorem meromorphicOn_heckeLambdaOne' : MeromorphicOn (heckeLambdaOne' K) Set.univ := by
  have hD : (((|discr K| : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast abs_ne_zero.2 (discr_ne_zero K)
  have hH : Differentiable ℂ (fun u : ℂ => (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - u)) :=
    (differentiable_const _ |>.sub differentiable_id).const_cpow (Or.inl hD)
  have hr : Differentiable ℂ (fun u : ℂ => 1 - u) := (differentiable_const _).sub differentiable_id
  have h : heckeLambdaOne' K = fun u =>
      (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - u) *
          (2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(1 - u)) * xiE K (1 - u)) +
        (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - u) * -(2 ^ nrComplexPlaces K *
          ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(1 - u)) * xiF₁ K (1 - u)) / u +
        (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - u) * -(2 ^ nrComplexPlaces K *
          ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(1 - u)) * xiF₀ K (1 - u)) / (u - 1) := by
    funext u
    rw [heckeLambdaOne', heckeLambdaOne_eq_poleShape]
    dsimp only
    rw [poleShape_one_sub (E := fun u =>
        2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiE K u)
      (F₀ := fun u => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₀ K u)
      (F₁ := fun u => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-u) * xiF₁ K u)]
    ring
  rw [h]
  exact meromorphicOn_poleShape (hH.mul ((differentiable_heckeE K).comp hr))
    (hH.mul ((differentiable_heckeF₁ K).comp hr).neg)
    (hH.mul ((differentiable_heckeF₀ K).comp hr).neg)

variable (K) in
/-- For $\mathrm{Re}\, s > 1$, $\Lambda(s) = 2^{r_2} \Gamma_K(s) \zeta_K(s)$. -/
theorem heckeLambdaOne_eq {s : ℂ} (hs : 1 < s.re) :
    heckeLambdaOne K s = 2 ^ nrComplexPlaces K * gammaK K s * dedekindZeta K s := by
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  rw [heckeLambdaOne, dedekindXi_eq K hs, Complex.cpow_neg]
  field_simp

variable (K) in
/-- For $\mathrm{Re}\, u > 1$, $\Lambda'(u) = 2^{r_2} \Gamma_K(u) \zeta_K(u)$. -/
theorem heckeLambdaOne'_eq {u : ℂ} (hu : 1 < u.re) :
    heckeLambdaOne' K u = 2 ^ nrComplexPlaces K * gammaK K u * dedekindZeta K u := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu; linarith
  have hu1 : u ≠ 1 := fun h => by simp [h] at hu
  rw [heckeLambdaOne', heckeLambdaOne, dedekindXi_one_sub K hu0 hu1, dedekindXi_eq K hu]
  have h := discr_cpow_mul_sqrt_cpow (K := K) u
  linear_combination (2 ^ nrComplexPlaces K * gammaK K u * dedekindZeta K u) * h

variable (K) in
/-- The functional equation $\Lambda(s) = |d_K|^{1/2 - s} \Lambda'(1 - s)$. -/
theorem heckeLambdaOne_eq_discr_cpow_mul (s : ℂ) :
    heckeLambdaOne K s = (((|discr K| : ℤ) : ℂ)) ^ (1 / 2 - s) * heckeLambdaOne' K (1 - s) := by
  have hD : (((|discr K| : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast abs_ne_zero.2 (discr_ne_zero K)
  rw [heckeLambdaOne', sub_sub_cancel, ← mul_assoc, ← Complex.cpow_add _ _ hD,
    show 1 / 2 - s + (1 / 2 - (1 - s)) = 0 by ring, Complex.cpow_zero, one_mul]

variable (K) in
/-- **Hecke's theorem for the trivial character.** This is the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi = 1$, with $\sigma = 0$, $W = 1$ and $s_0 = 0$. -/
theorem heckeFunctionalEquationAt_one (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, (1 : HeckeCharacter K).IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, (1 : HeckeCharacter K)⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K,
      ‖(((1 : HeckeCharacter K) x : ℂˣ) : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = (1 : HeckeCharacter K).completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = (1 : HeckeCharacter K)⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) *
          (Ideal.absNorm (1 : HeckeCharacter K).conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K,
            (((1 : HeckeCharacter K) x : ℂˣ) : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  have h0 : n = 0 ∧ t = 0 := ⟨funext fun v => ((isArchimedeanParameter_one_iff v _ _).1 (hn v)).1,
    funext fun v => ((isArchimedeanParameter_one_iff v _ _).1 (hn v)).2⟩
  have hinv : (1 : HeckeCharacter K)⁻¹ = 1 := by
    ext x
    exact congrArg Units.val (inv_one (G := ℂˣ))
  rw [hinv] at hn' ⊢
  have h0' : n' = 0 ∧ t' = 0 :=
    ⟨funext fun v => ((isArchimedeanParameter_one_iff v _ _).1 (hn' v)).1,
      funext fun v => ((isArchimedeanParameter_one_iff v _ _).1 (hn' v)).2⟩
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨rfl, rfl⟩ := h0'
  refine ⟨0, fun x => by simp, heckeLambdaOne K, heckeLambdaOne' K, 1,
    meromorphicOn_heckeLambdaOne K, meromorphicOn_heckeLambdaOne' K, fun s hs => ?_,
    fun s hs => ?_, norm_one, fun s => ?_, Or.inr ⟨0, fun x => by simp, fun s hs0 hs1 => ?_, ?_, ?_⟩⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_zero, finiteLFunction_one K (by simpa using hs),
      heckeLambdaOne_eq K (by simpa using hs)]
  · rw [HeckeCharacter.completedLFunction, gammaFactor_zero, finiteLFunction_one K (by simpa using hs),
      heckeLambdaOne'_eq K (by simpa using hs)]
  · rw [HeckeCharacter.conductor_one, map_one, Nat.cast_one, mul_one, Complex.ofReal_zero, sub_zero, one_mul]
    exact heckeLambdaOne_eq_discr_cpow_mul K s
  · exact analyticAt_heckeLambdaOne K (by simpa using hs0) (by simpa using hs1)
  · simpa using meromorphicOrderAt_heckeLambdaOne_zero K
  · simpa using meromorphicOrderAt_heckeLambdaOne_one K

end Hecke

end Langlands.Tate
