/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.UnitClass
import Langlands.Tate.ImaginaryQuadratic
import Langlands.Tate.QuadraticDedekind

/-!
# The functional equation of the Dedekind zeta function

Let $K$ be a number field of degree $n$ with discriminant $d_K$, $w_K$ roots of unity, $r_2$ complex places, unit rank $r$ and regulator $R_K$. This file proves the functional equation of the Dedekind zeta function $\zeta_K$ of Mathlib, with the method of Hecke. For a nonzero fractional ideal $\mathfrak{a}$ let $$\psi_{\mathfrak{a}}(u) = |d_K|^{u/2} N(\mathfrak{a})^u \Lambda_{\mathfrak{a}}(n u / 2),$$ where $\Lambda_{\mathfrak{a}}$ is the Mellin transform of the unit theta function of `Langlands/Tate/UnitTheta.lean`. Choose an ideal $\mathfrak{a}_C$ in each ideal class $C$ and put $$\xi_K(u) = \frac{2^{r - r_2} n R_K}{w_K} \sum_C \psi_{\mathfrak{a}_C}(u).$$ Then $\xi_K$ is holomorphic on $\mathbb{C} \setminus \{0, 1\}$, $\xi_K(u) = |d_K|^{u/2} \Gamma_K(u) \zeta_K(u)$ for $\mathrm{Re}\, u > 1$, and $\xi_K(1 - u) = \xi_K(u)$.

## Main definitions

* `Langlands.Tate.classXi`: the function $\psi_{\mathfrak{a}}$.
* `Langlands.Tate.dedekindXi`: the completed Dedekind zeta function $\xi_K$.

## Main results

* `Langlands.Tate.classXi_one_sub`: the functional equation $\psi_{\mathfrak{a}}(1 - u) = \psi_{\mathfrak{a}^\vee}(u)$.
* `Langlands.Tate.hasSum_classXi`: the Dirichlet series of $\psi_{\mathfrak{a}}$ for $\mathrm{Re}\, u > 1$.
* `Langlands.Tate.classXi_eq_of_mk_eq`: $\psi_{\mathfrak{a}}$ depends only on the class of $\mathfrak{a}$.
* `Langlands.Tate.dedekindXi_eq`: $\xi_K(u) = |d_K|^{u/2} \Gamma_K(u) \zeta_K(u)$ for $\mathrm{Re}\, u > 1$.
* `Langlands.Tate.differentiableAt_dedekindXi`: $\xi_K$ is holomorphic on $\mathbb{C} \setminus \{0, 1\}$.
* `Langlands.Tate.dedekindXi_one_sub`: the functional equation $\xi_K(1 - u) = \xi_K(u)$.

## Proof

The functional equation of the theta pair gives $\Lambda_{\mathfrak{a}}(n/2 - s) = (N(\mathfrak{a}) \sqrt{|d_K|})^{-1} \Lambda_{\mathfrak{a}^\vee}(s)$. With $N(\mathfrak{a}^\vee) = (N(\mathfrak{a}) |d_K|)^{-1}$ this is $\psi_{\mathfrak{a}}(1 - u) = \psi_{\mathfrak{a}^\vee}(u)$. For $\mathrm{Re}\, u > 1$, the file `Langlands/Tate/UnitClass.lean` gives $$\psi_{\mathfrak{a}}(u) = \frac{w_K}{2^{r - r_2} n R_K} |d_K|^{u/2} \Gamma_K(u) \sum_{[I] = [\mathfrak{a}]^{-1}} N(I)^{-u}.$$ The right side depends only on the class of $\mathfrak{a}$, so by the identity theorem $\psi_{\mathfrak{a}}$ depends only on the class of $\mathfrak{a}$ on $\mathbb{C} \setminus \{0, 1\}$. The sum over all classes gives $\zeta_K$. The class of $\mathfrak{a}_C^\vee = (\mathfrak{a}_C \mathfrak{d})^{-1}$ is $(C [\mathfrak{d}])^{-1}$, and $C \mapsto (C [\mathfrak{d}])^{-1}$ is a bijection of the class group. So the sum of the functional equations over $C$ is the functional equation of $\xi_K$.

## References

* E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, chapter VIII.
* J. Neukirch, Algebraic number theory, chapter VII, section 5.
-/

namespace Langlands.Tate

open Module Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

open scoped Real Classical nonZeroDivisors

section Congr

/-- The function `Λ` of a `WeakFEPair` depends only on `f`, `f₀`, `g₀`, `k` and `ε`. -/
theorem _root_.WeakFEPair.Λ_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Q : WeakFEPair E} (hf : P.f = Q.f) (hf₀ : P.f₀ = Q.f₀) (hg₀ : P.g₀ = Q.g₀)
    (hk : P.k = Q.k) (hε : P.ε = Q.ε) : P.Λ = Q.Λ := by
  funext s
  simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, WeakFEPair.f_modif, hf, hf₀, hg₀, hk, hε]

end Congr

variable {K : Type*} [Field K] [NumberField K]

/-- The function $\psi_{\mathfrak{a}}(u) = |d_K|^{u/2} N(\mathfrak{a})^u \Lambda_{\mathfrak{a}}(n u / 2)$. -/
noncomputable def classXi (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℂ) : ℂ :=
  ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
    ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ u *
      (unitThetaFEPair a).Λ (finrank ℚ K * u / 2)

/-- The symmetric pair of $(\Theta_{\mathfrak{a}}, \Theta_{\mathfrak{a}^\vee})$ has the same function $\Lambda$ as the pair of $\mathfrak{a}^\vee$, because the root numbers agree. -/
theorem symm_Λ_unitThetaFEPair (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (unitThetaFEPair a).symm.Λ = (unitThetaFEPair (dualUnit K a)).Λ := by
  refine WeakFEPair.Λ_congr rfl rfl rfl rfl ?_
  simp only [WeakFEPair.symm, unitThetaFEPair]
  rw [absNorm_dualUnit]
  have hd : 0 < |(discr K : ℝ)| := by
    have := discr_ne_zero K
    positivity
  have hN := absNorm_pos K a
  have hs := Real.sq_sqrt hd.le
  push_cast
  field_simp
  rw [eq_div_iff (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hd).ne'), ← Complex.ofReal_mul,
    Real.mul_self_sqrt hd.le]

/-- The functional equation $\psi_{\mathfrak{a}}(1 - u) = \psi_{\mathfrak{a}^\vee}(u)$. -/
theorem classXi_one_sub (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℂ) :
    classXi a (1 - u) = classXi (dualUnit K a) u := by
  have hfe := (unitThetaFEPair a).functional_equation (finrank ℚ K * u / 2)
  rw [symm_Λ_unitThetaFEPair] at hfe
  have hk : (unitThetaFEPair a).k = finrank ℚ K / 2 := rfl
  rw [hk] at hfe
  rw [classXi, classXi, show (finrank ℚ K : ℂ) * (1 - u) / 2 =
    ((finrank ℚ K / 2 : ℝ) : ℂ) - finrank ℚ K * u / 2 by push_cast; ring, hfe, absNorm_dualUnit]
  have hε : (unitThetaFEPair a).ε = (((FractionalIdeal.absNorm
      (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|)⁻¹ : ℝ) := rfl
  rw [hε, smul_eq_mul]
  generalize (unitThetaFEPair (dualUnit K a)).Λ (finrank ℚ K * u / 2) = L
  have hd : 0 < |(discr K : ℝ)| := by
    have := discr_ne_zero K
    positivity
  have hA := Real.sqrt_pos.2 hd
  have hN := absNorm_pos K a
  have hd' : |(discr K : ℝ)| = √|(discr K : ℝ)| * √|(discr K : ℝ)| :=
    (Real.mul_self_sqrt hd.le).symm
  set A := √|(discr K : ℝ)|
  set N := (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA.ne'
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
  rw [Complex.ofReal_inv (N * |(discr K : ℝ)|), Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm), Complex.ofReal_mul N, hd',
    Complex.mul_cpow_ofReal_nonneg hN.le (by positivity), Complex.ofReal_mul A,
    Complex.mul_cpow_ofReal_nonneg hA.le hA.le, Complex.cpow_sub _ _ hA0,
    Complex.cpow_sub _ _ hN0, Complex.cpow_one, Complex.cpow_one, Complex.ofReal_inv,
    Complex.ofReal_mul]
  have hAu : (A : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hA0)
  have hNu : (N : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hN0)
  field_simp

/-- If $\mathrm{Re}\, u > 1$, then $\mathrm{Re}(n u / 2) > n / 2$. -/
theorem lt_re_of_one_lt_re {u : ℂ} (hu : 1 < u.re) :
    (finrank ℚ K : ℝ) / 2 < ((finrank ℚ K : ℂ) * u / 2).re := by
  have hn : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos (R := ℚ) (M := K)
  have : ((finrank ℚ K : ℂ) * u / 2).re = finrank ℚ K * u.re / 2 := by
    simp [Complex.mul_re, Complex.div_ofNat_re]
  rw [this]
  nlinarith

/-- The variable $s = n u / 2$ of the theta pair gives $s' = 2 s / n = u$. -/
theorem two_mul_div_finrank (u : ℂ) :
    2 * ((finrank ℚ K : ℂ) * u / 2) / finrank ℚ K = u := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  field_simp

/-- The term of the Dirichlet series of $\psi_{\mathfrak{a}}$. -/
noncomputable def xiTerm (u : ℂ) (I : (Ideal (𝓞 K))⁰) : ℂ :=
  (torsionOrder K : ℂ) * (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u *
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u)) / ((unitConst K * 2 ^ rank K : ℝ) : ℂ)

/-- For $\mathrm{Re}\, u > 1$, $\psi_{\mathfrak{a}}(u)$ is $w_K |d_K|^{u/2} \Gamma_K(u) \zeta(u, [\mathfrak{a}]^{-1})$ divided by $2^{r - r_2} n R_K$. -/
theorem hasSum_classXi (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then xiTerm u I else 0) (classXi a u) := by
  have h := (hasSum_Λ_unitThetaFEPair_class a (lt_re_of_one_lt_re hu)).mul_left
    (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ u)
  rw [two_mul_div_finrank] at h
  rw [classXi]
  convert h using 1
  funext I
  have hN : ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (absNorm_pos K a).ne'))
  split_ifs
  · simp only [xiTerm, Complex.cpow_neg]
    field_simp
  · rw [mul_zero]

/-- The function $\psi_{\mathfrak{a}}$ is holomorphic on $\mathbb{C} \setminus \{0, 1\}$. -/
theorem differentiableAt_classXi (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : ℂ} (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) : DifferentiableAt ℂ (classXi a) u := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  have hΛ : DifferentiableAt ℂ (unitThetaFEPair a).Λ (finrank ℚ K * u / 2) := by
    refine (unitThetaFEPair a).differentiableAt_Λ (Or.inl ?_) (Or.inl ?_)
    · exact div_ne_zero (mul_ne_zero hn hu0) two_ne_zero
    · change _ ≠ (((finrank ℚ K : ℝ) / 2 : ℝ) : ℂ)
      push_cast
      intro h
      field_simp at h
      exact hu1 h
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'
  have hN : ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (absNorm_pos K a).ne'
  refine ((DifferentiableAt.const_cpow differentiableAt_id (Or.inl hA)).mul
    (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hN))).mul ?_
  exact hΛ.comp u (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => (finrank ℚ K : ℂ) * v / 2) u)

/-- The function $\psi_{\mathfrak{a}}$ depends only on the class of $\mathfrak{a}$. -/
theorem classXi_eq_of_mk_eq {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K a = ClassGroup.mk K b) {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    classXi a u = classXi b u :=
  eq_of_eq_of_lt_re (p := 0) (q := 1) (r := 1)
    (fun _ h0 h1 => differentiableAt_classXi a h0 h1)
    (fun _ h0 h1 => differentiableAt_classXi b h0 h1)
    (fun v hv => (hasSum_classXi a hv).unique (by rw [h]; exact hasSum_classXi b hv)) hu0 hu1

/-- The Gamma factor $\Gamma_K(u)$ has no zero for $\mathrm{Re}\, u > 0$. -/
theorem gammaK_ne_zero {u : ℂ} (hu : 0 < u.re) : gammaK K u ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun w _ => mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos ?_)
  · refine Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 ?_))
    have : (0 : ℝ) < mult w := by exact_mod_cast mult_pos
    positivity
  · have : (0 : ℝ) < mult w := by exact_mod_cast mult_pos
    have h : ((mult w : ℂ) * u / 2).re = mult w * u.re / 2 := by
      simp [Complex.mul_re, Complex.div_ofNat_re]
    rw [h]
    positivity

variable (K) in
/-- The fractional ideal of the chosen integral ideal in a class. -/
noncomputable def classRepUnit (C : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (classIdeal K C)

/-- The chosen fractional ideal of a class $C$ is in $C$. -/
theorem mk_classRepUnit (C : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRepUnit K C) = C := by
  rw [classRepUnit, ClassGroup.mk_mk0, mk0_classIdeal]

variable (K) in
/-- The completed Dedekind zeta function $\xi_K(u) = \frac{2^{r - r_2} n R_K}{w_K} \sum_C \psi_{\mathfrak{a}_C}(u)$, with one fractional ideal $\mathfrak{a}_C$ in each ideal class $C$. -/
noncomputable def dedekindXi (u : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) / torsionOrder K *
    ∑ C : ClassGroup (𝓞 K), classXi (classRepUnit K C) u

variable (K) in
/-- For $\mathrm{Re}\, u > 1$, $\xi_K(u) = |d_K|^{u/2} \Gamma_K(u) \zeta_K(u)$. -/
theorem dedekindXi_eq {u : ℂ} (hu : 1 < u.re) :
    dedekindXi K u = ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u * dedekindZeta K u := by
  have hs : HasSum (fun I : (Ideal (𝓞 K))⁰ => xiTerm u I)
      (∑ C : ClassGroup (𝓞 K), classXi (classRepUnit K C) u) := by
    have h := hasSum_sum (s := Finset.univ) fun C _ => hasSum_classXi (classRepUnit K C) hu
    convert h using 1
    funext I
    simp only [mk_classRepUnit]
    rw [Finset.sum_eq_single (ClassGroup.mk0 I)⁻¹ (fun C _ hC => ite_eq_right (fun h =>
      hC (by rw [h, inv_inv]))) (fun h => absurd (Finset.mem_univ _) h), inv_inv, ite_eq_left rfl]
  have hw : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  have hΓ : gammaK K u ≠ 0 := gammaK_ne_zero (by linarith)
  have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
  have hz := dedekindZeta_eq_of_hasSum K (u := u) (by
    have := hs.div_const ((torsionOrder K : ℂ) * (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
      gammaK K u) / ((unitConst K * 2 ^ rank K : ℝ) : ℂ))
    convert this using 1
    funext I
    rw [xiTerm, Complex.ofReal_natCast]
    field_simp)
  rw [hz, dedekindXi]
  field_simp

variable (K) in
/-- The map $C \mapsto [\mathfrak{a}_C^\vee] = (C [\mathfrak{d}])^{-1}$ of the class group. -/
noncomputable def dualClass : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.mulRight (ClassGroup.mk K (differentUnit K))).trans (Equiv.inv _)

/-- The dual of the chosen fractional ideal of $C$ is in the class `dualClass K C`. -/
theorem mk_dualUnit_classRepUnit (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (dualUnit K (classRepUnit K C)) = dualClass K C := by
  rw [dualUnit_eq, map_inv, map_mul, mk_classRepUnit]
  rfl

variable (K) in
/-- The completed Dedekind zeta function is holomorphic on $\mathbb{C} \setminus \{0, 1\}$. -/
theorem differentiableAt_dedekindXi {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    DifferentiableAt ℂ (dedekindXi K) u := by
  have h : DifferentiableAt ℂ (fun v => ∑ C : ClassGroup (𝓞 K), classXi (classRepUnit K C) v) u :=
    DifferentiableAt.fun_sum fun C _ => differentiableAt_classXi _ hu0 hu1
  exact h.const_mul _

variable (K) in
/-- **The functional equation of the Dedekind zeta function.** For $u \neq 0, 1$, $\xi_K(1 - u) = \xi_K(u)$. -/
theorem dedekindXi_one_sub {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    dedekindXi K (1 - u) = dedekindXi K u := by
  rw [dedekindXi, dedekindXi]
  congr 1
  simp_rw [classXi_one_sub]
  rw [← (dualClass K).sum_comp (fun C => classXi (classRepUnit K C) u)]
  refine Finset.sum_congr rfl fun C _ => classXi_eq_of_mk_eq ?_ hu0 hu1
  rw [mk_dualUnit_classRepUnit, mk_classRepUnit]

end Langlands.Tate
