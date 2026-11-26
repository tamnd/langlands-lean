/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeWeightFE

/-!
# Hecke's functional equation for unramified characters of weight $n \neq 0$ of an imaginary quadratic field

Let $K$ be an imaginary quadratic field, let $\sigma$ be the embedding of its complex place, and let $\chi$ be a Hecke character with the archimedean parameters $(n, t)$ at the complex place. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each $\chi$ with $n \neq 0$ that is unramified at each finite place. With `Langlands.Tate.HeckeWeightFE` and the case $n = 0$ of `Langlands.Tate.RayClassHecke`, it then holds for each Hecke character of $K$, so `Langlands.HeckeFunctionalEquationAt K` holds.

## Main definitions

* `Langlands.Tate.unramifiedWeightCompleted`: the function $\Lambda^k_J(s) = \chi_{\mathrm{id}}(J)^{-1} \Lambda^k_{\sqrt 2 \sigma(\mathfrak{f} J)}(0, 0; s)$, one weighted Epstein zeta function with no shift.

## Main results

* `periodicChar_eq_one_of_ramifiedSet_eq_empty`: for an unramified $\chi$, $\chi_{\mathrm{id}}((x)) \chi_\infty(x) = 1$ for each $x \in K^\times$.
* `periodicCoeff_of_ramifiedSet_eq_empty`: for an unramified $\chi$ and $\alpha \neq 0$, the periodic coefficient is $c_J(\alpha) = \chi_{\mathrm{id}}(J)^{-1}$.
* `gammaℝ_mul_finiteLFunction_unramifiedWeight`: for a unitary unramified $\chi$ with the parameters $(k, 0)$ and $\mathrm{Re}\, u > 1$, $\Gamma_\mathbb{R}(2u + k) L(u, \chi) = \frac{1}{w} \sum_C (2 N(J_C))^u \Lambda^k_{J_C}(2u + k)$.
* `hasSum_unramifiedWeightCompleted_sub`: for $\mathrm{Re}\, u > 1$, the value $\Lambda^k_J(2 (1 - u) + k)$ is a sum over the ideals $I$ in the class of $J \mathfrak{d}$ of the terms of the $L$-series of $\chi^{-1}$.
* `unramifiedWeight_dual_eq_completed`: the dual side gives $2^{1 - u} \Gamma_\mathbb{R}(2u + k) L(u, \chi^{-1})$, with the root number $W = (-i)^k \chi_{\mathrm{id}}(\mathfrak{d}^{-1})^{-1}$.
* `entireFunctionalEquation_unramifiedWeight`: the functional equation with entire functions for a unitary unramified $\chi$ with the parameters $(k, 0)$, $k \neq 0$.
* `heckeFunctionalEquation_of_isQuadratic_of_unramified_weight`: the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each Hecke character that is unramified at each finite place and has $n \neq 0$.
* `heckeFunctionalEquation_of_isQuadratic`: the same for each Hecke character of $K$.
* `heckeFunctionalEquationAt_of_isQuadratic`: `Langlands.HeckeFunctionalEquationAt K` for each imaginary quadratic field $K$.

## Proofs

Let $\chi$ be unitary and unramified at each finite place, with the parameters $(k, 0)$ at the complex place and $k \neq 0$. Then $\mathfrak{f} = (1)$, and the reciprocity law `periodicChar_mul_prod_finiteComponent` has an empty product, so $\chi_{\mathrm{id}}((x)) \chi_\infty(x) = 1$ for each $x \in K^\times$. Thus the periodic coefficient is the constant $\chi_{\mathrm{id}}(J)^{-1}$ on $J \setminus \{0\}$. The residues modulo $\mathfrak{f} J$ of `Langlands.Tate.HeckeWeightFE` are not used: the class $0$ contains $0$, where the coefficient is $0$, so the coefficient is not periodic. Instead, the series over $J$ is one weighted Epstein zeta function with no shift. The direct side then follows as in `Langlands.Tate.HeckeWeightFE`.

For the dual side, `completedWeightZeta_quadLattice_sub` with $\xi = 0$ gives $(-i)^k (N(J) \sqrt{|d_K|})^{-1}$ times the series over the nonzero $\beta \in J^\vee$ of $\Gamma_\mathbb{R}(s) \gamma^k |\gamma|^{-s}$, with $\gamma = \sqrt 2 \sigma(\beta)$. There is no Gauss sum. With $I = (\beta) J \mathfrak{d}$, the identity $\gamma^k = |\gamma|^k \chi_\infty(\beta)$ and $\chi_\infty(\beta) = \chi_{\mathrm{id}}((\beta))^{-1} = \chi_{\mathrm{id}}(I)^{-1} \chi_{\mathrm{id}}(J^\vee)^{-1}$ give the term $\chi_{\mathrm{id}}(\mathfrak{d}^{-1})^{-1} \chi^{-1}(I) |\gamma|^{-2u}$, because $J J^\vee = \mathfrak{d}^{-1}$. The constants combine as in `scalar_mul_eq`, with $\tau = \chi_{\mathrm{id}}(\mathfrak{d}^{-1})^{-1}$ in place of the Gauss sum and $N(\mathfrak{f}) = 1$. Then $|W| = |\tau| = 1$. The reduction of a general $\xi$ to a unitary $\chi$ with $t = 0$ and $n > 0$ is as in `Langlands.Tate.HeckeWeightFE`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open Module Filter Topology Set Complex
open NumberField IsDedekindDomain InfinitePlace NumberField.Units NumberField.mixedEmbedding
open scoped nonZeroDivisors Classical ComplexConjugate

namespace Langlands.Tate

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

section Unramified

/-- If $\chi$ is unramified at each finite place, then its conductor is $(1)$. -/
theorem conductor_eq_top_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅) : χ.conductor = ⊤ := by
  rw [conductor_eq_prod, h, Finset.prod_empty, Ideal.one_eq_top]

/-- If $\chi$ is unramified at each finite place, then the conductor is $1$ as a nonzero ideal. -/
theorem conductorNZ_eq_one_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅) :
    conductorNZ χ = 1 :=
  Subtype.ext ((conductor_eq_top_of_ramifiedSet_eq_empty h).trans Ideal.one_eq_top.symm)

/-- If $\chi$ is unramified at each finite place, then $N(\mathfrak{f}) = 1$. -/
theorem absNorm_conductor_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅) :
    Ideal.absNorm χ.conductor = 1 := by
  rw [conductor_eq_top_of_ramifiedSet_eq_empty h, Ideal.absNorm_top]

/-- **Reciprocity for an unramified character.** If $\chi$ is unramified at each finite place, then $\chi_{\mathrm{id}}((x)) \chi_\infty(x) = 1$ for each $x \in K^\times$. -/
theorem periodicChar_eq_one_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅) (x : Kˣ) :
    periodicChar χ x = 1 := by
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) x (by simp [h])
  rwa [h, Finset.prod_empty, mul_one] at e

/-- If $\chi$ is unramified at each finite place, then $\chi_\infty(x) = \chi_{\mathrm{id}}((x))^{-1}$ for each $x \in K^\times$. -/
theorem infChar_eq_inv_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅) (x : Kˣ) :
    infChar χ x = (idealChar χ (toPrincipalIdeal (𝓞 K) K x))⁻¹ :=
  eq_inv_of_mul_eq_one_right (periodicChar_eq_one_of_ramifiedSet_eq_empty h x)

/-- **The periodic coefficient of an unramified character is constant.** If $\chi$ is unramified at each finite place and $\alpha \neq 0$, then $c_J(\alpha) = \chi_{\mathrm{id}}(J)^{-1}$. -/
theorem periodicCoeff_of_ramifiedSet_eq_empty (h : ramifiedSet χ = ∅)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K} (hα : α ≠ 0) :
    periodicCoeff χ J α = (((idealChar χ J)⁻¹ : ℂˣ) : ℂ) := by
  rw [periodicCoeff_of_cond J ⟨hα, by simp [h]⟩, ← periodicChar_apply,
    periodicChar_eq_one_of_ramifiedSet_eq_empty h, one_mul]

end Unramified

section Direct

variable [IsTotallyComplex K]

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- **The completed partial $L$-function of weight $k$ of an unramified character.** For a nonzero integral ideal $J$, $$\Lambda^k_J(s) = \chi_{\mathrm{id}}(J)^{-1} \Lambda^k_{\sqrt 2 \sigma(\mathfrak{f} J)}(0, 0; s),$$ a weighted Epstein zeta function of the lattice $\sqrt 2 \sigma(\mathfrak{f} J)$ with no shift. For an unramified $\chi$ the ideal $\mathfrak{f} J$ is $J$. -/
noncomputable def unramifiedWeightCompleted (χ : HeckeCharacter K) (hK : finrank ℚ K = 2)
    (k : ℕ) (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ) *
    completedWeightZeta (quadLattice K hK (FractionalIdeal.mk0 K (conductorNZ χ * J))) k 0 0 s

/-- For $k \neq 0$, the function $\Lambda^k_J$ of an unramified character is entire. -/
theorem differentiable_unramifiedWeightCompleted (hK : finrank ℚ K = 2) {k : ℕ} (hk : k ≠ 0)
    (J : (Ideal (𝓞 K))⁰) : Differentiable ℂ (unramifiedWeightCompleted χ hK k J) :=
  (differentiable_completedWeightZeta _ hk _ _).const_mul _

/-- **The completed partial $L$-function of weight $k$ as a series.** Let $\chi$ be unramified at each finite place. For $\mathrm{Re}\, s > k + 2$, $$\Lambda^k_J(s) = \sum_{\beta \in J} c_J(\beta) T_k(\beta; s).$$ -/
theorem hasSum_unramifiedWeightCompleted (h0 : ramifiedSet χ = ∅) (hK : finrank ℚ K = 2)
    (k : ℕ) (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun β : 𝔣[J] =>
        periodicCoeff χ (FractionalIdeal.mk0 K J) β * weightTerm hK k s β)
      (unramifiedWeightCompleted χ hK k J s) := by
  have h := hasSum_completedWeightZeta_quadLattice K hK k (FractionalIdeal.mk0 K J) 0 hs
  rw [map_zero] at h
  have e : ∀ a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ, a = b →
      completedWeightZeta (quadLattice K hK a) k 0 0 s =
        completedWeightZeta (quadLattice K hK b) k 0 0 s := by
    rintro a b rfl
    rfl
  rw [unramifiedWeightCompleted, e _ (FractionalIdeal.mk0 K J)
    (by rw [conductorNZ_eq_one_of_ramifiedSet_eq_empty h0, one_mul])]
  convert h.mul_left (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ) using 1
  funext β
  by_cases hβ : (β : K) = 0
  · simp [hβ, weightTerm]
  · rw [periodicCoeff_of_ramifiedSet_eq_empty h0 _ hβ, weightTerm, ite_eq_right hβ, zero_add,
      ite_eq_right hβ]

/-- **The partial $L$-series of weight $k$ of an unramified character.** Let $\chi$ be unitary, unramified at each finite place, with the parameters $(k, 0)$ at the complex place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u + k) \sum_{[I] = [J]^{-1}} \chi(I) N(I)^{-u} = \frac{(2 N(J))^u}{w} \Lambda^k_J(2u + k).$$ -/
theorem hasSum_unramifiedWeight_partialLSeries (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) (J : (Ideal (𝓞 K))⁰)
    {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then
        Complex.Gammaℝ (2 * u + k) * rayWeight χ u I else 0)
      ((torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        unramifiedWeightCompleted χ hK k J (2 * u + k)) := by
  have hs : (k + 2 : ℝ) < (2 * u + k).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re]
    linarith
  have h1 := hasSum_unramifiedWeightCompleted h0 hK k J hs
  have e : (fun β : 𝔣[J] =>
      periodicCoeff χ (FractionalIdeal.mk0 K J) β * weightTerm hK k (2 * u + k) β) =
      fun β : 𝔣[J] =>
        Complex.Gammaℝ (2 * u + k) * (rayCoeff χ (FractionalIdeal.mk0 K J) (β : K) *
        if (β : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u))) := by
    funext β
    by_cases hβ : (β : K) = 0
    · simp [hβ, weightTerm]
    · rw [periodicCoeff_mul_weightTerm hK h _ hβ, ite_eq_right hβ]
  rw [e] at h1
  have h2 := hasSum_rayCoeff_ideals_of_unitary hχ hK J hu
  have h3 : unramifiedWeightCompleted χ hK k J (2 * u + k) = Complex.Gammaℝ (2 * u + k) *
      ∑' β : 𝔣[J], rayCoeff χ (FractionalIdeal.mk0 K J) β * if (β : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u)) := by
    rw [← h1.tsum_eq, tsum_mul_left]
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hN : (0 : ℝ) < 2 * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    have : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := Nat.cast_pos.2 (Nat.pos_of_ne_zero
      fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    positivity
  have hA : ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hN.ne'))
  rw [h3]
  have h4 := h2.mul_left ((torsionOrder K : ℂ)⁻¹ *
    ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u * Complex.Gammaℝ (2 * u + k))
  rw [show (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
      Complex.Gammaℝ (2 * u + k) * _ = _ from (mul_assoc _ _ _)] at h4
  refine h4.congr_fun fun I => ?_
  rw [Complex.cpow_neg]
  split_ifs
  · field_simp
  · ring

/-- **The $L$-series of weight $k$ of an unramified character as a sum over the ideal classes.** Let $\chi$ be unitary, unramified at each finite place, with the parameters $(k, 0)$ at the complex place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u + k) L(u, \chi) = \frac{1}{w} \sum_{C} (2 N(J_C))^u \Lambda^k_{J_C}(2u + k),$$ where $J_C$ is an integral ideal of the class $C$. -/
theorem gammaℝ_mul_finiteLFunction_unramifiedWeight (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {u : ℂ} (hu : 1 < u.re) :
    Complex.Gammaℝ (2 * u + k) * χ.finiteLFunction u = ∑ C : ClassGroup (𝓞 K),
      (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        unramifiedWeightCompleted χ hK k (classIdeal K C) (2 * u + k) := by
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_unramifiedWeight_partialLSeries h0 hχ hK h (classIdeal K C) hu)
  rw [finiteLFunction_eq_of_unitary hχ hu, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk0 (classIdeal K C))⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk0_classIdeal]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end Direct

section Dual

variable [IsTotallyComplex K]

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- **The terms of the dual series of an unramified character.** Let $\chi$ be unitary, unramified at each finite place, with the parameters $(k, 0)$ at the complex place, and let $I = (\beta) \mathfrak{f} J \mathfrak{d}$. Then $$\gamma^k \chi_{\mathrm{id}}(J)^{-1} |\gamma|^{-(2u + k)} = \chi_{\mathrm{id}}(\mathfrak{f}^\vee)^{-1} \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u},$$ with $\gamma = \sqrt 2 \, \sigma(\beta)$. Here $\mathfrak{f}^\vee = \mathfrak{d}^{-1}$. -/
theorem unramifiedWeight_mul_cpow (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {J I : (Ideal (𝓞 K))⁰}
    (β : DualFiber χ J I) (u : ℂ) :
    quadEmbed K hK β ^ k * (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ) *
        ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k)) =
      (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) * ((2 / ((Ideal.absNorm χ.conductor : ℝ) *
        Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
          rayWeight χ⁻¹ u I := by
  have hq0 : quadEmbed K hK β ≠ 0 := mt (quadEmbed_eq_zero_iff K hK).1 β.ne_zero
  have hn0 : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hq0
  have hc := conductor_mul_absNorm_mul_discr_pos χ J
  have hn : 2 * |(Algebra.norm ℚ (β : K) : ℝ)| = 2 / ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) * Ideal.absNorm (I : Ideal (𝓞 K)) := by
    rw [← β.abs_norm_mul, div_mul_eq_mul_div, eq_div_iff hc.ne']
    ring
  have hpow : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k)) =
      ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u)) * (((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k)⁻¹ := by
    rw [show -(2 * u + k) = -(2 * u) + -(k : ℂ) by ring, cpow_add _ _ hn0, cpow_neg _ (k : ℂ),
      cpow_natCast]
  have hnorm : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u)) =
      ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
        |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u) := by
    rw [norm_quadEmbed K hK, show -(2 * u) = 2 * -u by ring, sqrt_cpow_two_mul (by positivity), hn,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_natCast]
  have hγ : quadEmbed K hK β ^ k = ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k *
      (infChar χ (Units.mk0 (β : K) β.ne_zero) : ℂ) := by
    rw [← quadEmbed_pow_mul_conj_infChar hK h β.ne_zero, mul_assoc,
      conj_mul_self_of_norm_eq_one (norm_infChar_of_unitary hχ _), mul_one]
  have hinf : (infChar χ (Units.mk0 (β : K) β.ne_zero) : ℂ) *
      (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ) =
      (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) *
        (idealChar χ⁻¹ (FractionalIdeal.mk0 K I) : ℂ) := by
    rw [infChar_eq_inv_of_ramifiedSet_eq_empty h0, toPrincipalIdeal_dualFiber, idealChar_inv,
      ← mk0_mul_gaussDual J, map_mul, map_mul, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [mul_inv, mul_comm, mul_left_comm]
    rw [mul_assoc]
  have hk : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ hn0
  rw [hpow, hnorm, rayWeight_apply, ramifiedSet_inv, h0, ite_eq_left (by simp), one_mul, hγ]
  calc _ = ((((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k) * (((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k)⁻¹) *
        ((infChar χ (Units.mk0 (β : K) β.ne_zero) : ℂ) *
          (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ)) *
        (((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
          |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u)) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hk, one_mul, hinf]
      ring

/-- **The dual side of weight $k$ of an unramified character.** Let $\chi$ be unitary, unramified at each finite place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$, and let $\mathrm{Re}\, u > 1$. Then $\Lambda^k_J(2 (1 - u) + k)$ is the sum over the integral ideals $I$ in the class of $\mathfrak{f} J \mathfrak{d}$ of $$\frac{(-i)^k}{N(\mathfrak{f}) N(J) \sqrt{|d_K|}} w \, \Gamma_\mathbb{R}(2u + k) \chi_{\mathrm{id}}(\mathfrak{f}^\vee)^{-1} \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u}.$$ -/
theorem hasSum_unramifiedWeightCompleted_sub (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0)
    (J : (Ideal (𝓞 K))⁰) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun A : (Ideal (𝓞 K))⁰ => ((-Complex.I) ^ k *
        ((((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
          √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ)) *
        if ClassGroup.mk0 (conductorNZ χ * J * differentNZ K) = ClassGroup.mk0 A then
          (torsionOrder K : ℂ) * (Complex.Gammaℝ (2 * u + k) *
            ((((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) *
            ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
              |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * rayWeight χ⁻¹ u A))
        else 0)
      (unramifiedWeightCompleted χ hK k J (2 * (1 - u) + k)) := by
  have hs : (k + 2 : ℝ) < (2 * u + k).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re]
    linarith
  set c : ℂ := (((idealChar χ (FractionalIdeal.mk0 K J))⁻¹ : ℂˣ) : ℂ) with hcdef
  have h1 := hasSum_completedWeightZeta_dual_quadLattice K hK k
    (FractionalIdeal.mk0 K (conductorNZ χ * J)) 0 hs
  simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero,
    mul_one] at h1
  replace h1 : HasSum (fun β : FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] =>
      if (β : K) = 0 then (0 : ℂ) else Complex.Gammaℝ (2 * u + k) *
        ((quadEmbed K hK β) ^ k * c * ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k))))
      (c * completedWeightZeta (dualLattice (quadLattice K hK
        (FractionalIdeal.mk0 K (conductorNZ χ * J)))) k 0 0 (2 * u + k)) := by
    convert h1.mul_left c using 1
    funext β
    split_ifs
    · simp
    · ring
  rw [← hasSum_subtype_iff_of_support_subset (s := {β : FractionalIdeal.dual ℤ ℚ
      𝔣[conductorNZ χ * J] | (β : K) ≠ 0}) fun β hβ h0 => hβ (ite_eq_left h0)] at h1
  replace h1 := ((dualEquiv χ J).symm.hasSum_iff (f := fun β : {β : FractionalIdeal.dual ℤ ℚ
      𝔣[conductorNZ χ * J] // (β : K) ≠ 0} => if (β : K) = 0 then (0 : ℂ) else
      Complex.Gammaℝ (2 * u + k) * ((quadEmbed K hK β) ^ k * c *
        ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k))))).2 h1
  have hN : ((FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℚ) : ℝ) =
      (Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Submonoid.coe_mul, map_mul]
    push_cast
    rfl
  have e : unramifiedWeightCompleted χ hK k J (2 * (1 - u) + k) = ((-Complex.I) ^ k *
      ((((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
        √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ)) * (c * completedWeightZeta (dualLattice (quadLattice K hK
          (FractionalIdeal.mk0 K (conductorNZ χ * J)))) k 0 0 (2 * u + k)) := by
    have h2 := completedWeightZeta_quadLattice_sub K hK hk
      (FractionalIdeal.mk0 K (conductorNZ χ * J)) 0 (2 * u + k)
    rw [map_zero] at h2
    rw [unramifiedWeightCompleted, show 2 * (1 - u) + (k : ℂ) = 2 * k + 2 - (2 * u + k) by ring,
      h2, hN]
    ring
  rw [e]
  refine HasSum.mul_left _ (h1.sigma fun A => ?_)
  have := finite_dualFiber (χ := χ) hK J A
  have := Fintype.ofFinite (DualFiber χ J A)
  convert hasSum_fintype fun _ : DualFiber χ J A => Complex.Gammaℝ (2 * u + k) *
    ((((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) * ((2 / ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
        rayWeight χ⁻¹ u A) using 1
  · funext b
    exact (ite_eq_right b.ne_zero).trans
      (congrArg _ (unramifiedWeight_mul_cpow h0 hχ hK h b u))
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_dualFiber hK,
      nsmul_eq_mul]
    split_ifs <;> simp

/-- **The functional equation of weight $k$ of an unramified character on the half plane.** Let $\chi$ be unitary, unramified at each finite place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$, and let $W = (-i)^k \chi_{\mathrm{id}}(\mathfrak{f}^\vee)^{-1} / \sqrt{N(\mathfrak{f})}$. For $\mathrm{Re}\, u > 1$, $$W^{-1} (|d_K| N(\mathfrak{f}))^{1/2 - u} 2^{u} \frac{1}{w} \sum_C (2 N(J_C))^{1 - u} \Lambda^k_{J_C}(2 (1 - u) + k) = 2^{1 - u} \Gamma_\mathbb{R}(2u + k) L(u, \chi^{-1}).$$ -/
theorem unramifiedWeight_dual_eq_completed (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {u : ℂ}
    (hu : 1 < u.re) :
    ((-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
        ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
        (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - u) *
          ((2 : ℂ) ^ (1 - (1 - u)) * ∑ C : ClassGroup (𝓞 K), (torsionOrder K : ℂ)⁻¹ *
            ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u) *
              unramifiedWeightCompleted χ hK k (classIdeal K C) (2 * (1 - u) + k)) =
      (2 : ℂ) ^ (1 - u) * Complex.Gammaℝ (2 * u + k) * χ⁻¹.finiteLFunction u := by
  have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hτ : (-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (Units.ne_zero _)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) =
      ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [finiteLFunction_eq_of_unitary (norm_ideleChar_inv hχ) hu, ← tsum_mul_left, hX]
  have h1 := hasSum_sum fun C (_ : C ∈ Finset.univ) =>
    (hasSum_unramifiedWeightCompleted_sub h0 hχ hK hk h (classIdeal K C) hu).mul_left
      ((torsionOrder K : ℂ)⁻¹ *
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u))
  refine (HasSum.tsum_eq ?_).symm
  convert h1.mul_left (((-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
    ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ^ (1 / 2 - u) *
      (2 : ℂ) ^ (1 - (1 - u))) using 1
  · funext A
    simp only [mul_ite, mul_zero]
    simp_rw [mk0_conductor_mul_classIdeal_iff]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    have hb : ∀ J : (Ideal (𝓞 K))⁰, (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := fun J =>
      Nat.cast_pos.2 (Nat.pos_of_ne_zero
        fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
    rw [← scalar_mul_eq hc (hb (classIdeal K (ClassGroup.mk0 A *
      (ClassGroup.mk0 (conductorNZ χ) * ClassGroup.mk0 (differentNZ K))⁻¹))) hd hτ hw u
        (Complex.Gammaℝ (2 * u + k)) (rayWeight χ⁻¹ u A)]
    ring
  · ring

end Dual

section Assembly

variable [IsTotallyComplex K]

/-- **Hecke's functional equation of weight $k$ for an unramified character.** Let $K$ be imaginary quadratic and let $\chi$ be a unitary Hecke character that is unramified at each finite place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$. Then the functional equation with entire functions holds for $\chi$, with $W = (-i)^k \chi_{\mathrm{id}}(\mathfrak{f}^\vee)^{-1} / \sqrt{N(\mathfrak{f})}$, where $\mathfrak{f} = (1)$ and $\mathfrak{f}^\vee = \mathfrak{d}^{-1}$. -/
theorem entireFunctionalEquation_unramifiedWeight (h0 : ramifiedSet χ = ∅)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (hq : n (quadPlace K hK).1 = k) (ht : t (quadPlace K hK).1 = 0) :
    EntireFunctionalEquation χ n n' t t' := by
  have hnr : ¬ (quadPlace K hK).1.IsReal := not_isReal_iff_isComplex.2 (quadPlace K hK).2
  have h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0 := by
    rw [← hq, ← ht]
    exact hn _
  obtain ⟨hq', ht'⟩ := eq_of_isArchimedeanParameter hnr (hn' (quadPlace K hK).1) h.inv
  rw [ite_eq_right hnr, neg_zero] at *
  have hg : |n (quadPlace K hK).1| = (k : ℤ) := by rw [hq, Nat.abs_cast]
  have hg' : |n' (quadPlace K hK).1| = (k : ℤ) := by rw [hq', abs_neg, Nat.abs_cast]
  have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.2 (abs_ne_zero.2 (discr_ne_zero K)))
      (Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hW : (-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
      ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (Units.ne_zero _))
      (ofReal_ne_zero.2 (Real.sqrt_pos.2 hc).ne')
  let Λ : ℂ → ℂ := fun z => (2 : ℂ) ^ (1 - z) * ((2 : ℂ) ^ (-(k : ℂ) / 2) *
    ∑ C : ClassGroup (𝓞 K), (torsionOrder K : ℂ)⁻¹ *
      ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ z *
        unramifiedWeightCompleted χ hK k (classIdeal K C) (2 * z + k))
  have hd : Differentiable ℂ Λ := by
    have hb : ∀ C : ClassGroup (𝓞 K),
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := fun C =>
      ofReal_ne_zero.2 (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 fun h0 =>
        nonZeroDivisors.coe_ne_zero _ (Ideal.absNorm_eq_zero_iff.1 h0)))
    refine ((differentiable_id.const_sub 1).const_cpow (Or.inl two_ne_zero)).mul
      ((differentiable_const _).mul (Differentiable.fun_sum fun C _ => ?_))
    exact ((differentiable_const _).mul (differentiable_id.const_cpow (Or.inl (hb C)))).mul
      ((differentiable_unramifiedWeightCompleted hK hk (classIdeal K C)).comp
        ((differentiable_id.const_mul 2).add_const _))
  let Λ' : ℂ → ℂ := fun z => ((-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
      (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - z) * Λ (1 - z)
  have hd' : Differentiable ℂ Λ' :=
    ((differentiable_const _).mul ((differentiable_id.const_sub _).const_cpow (Or.inl hX))).mul
      (hd.comp (differentiable_id.const_sub 1))
  refine ⟨Λ, Λ', (-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ), hd, hd', fun s hs => ?_, fun s hs => ?_, ?_,
    fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_weight hK hg ht, mul_assoc, mul_assoc,
      gammaℝ_mul_finiteLFunction_unramifiedWeight h0 hχ hK h hs]
  · rw [HeckeCharacter.completedLFunction, gammaFactor_weight hK hg' ht',
      show (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (-(k : ℂ) / 2) * Complex.Gammaℝ (2 * s + k)) *
        χ⁻¹.finiteLFunction s = (2 : ℂ) ^ (-(k : ℂ) / 2) * ((2 : ℂ) ^ (1 - s) *
          Complex.Gammaℝ (2 * s + k) * χ⁻¹.finiteLFunction s) by ring,
      ← unramifiedWeight_dual_eq_completed h0 hχ hK hk h hs]
    simp only [Λ', Λ]
    ring
  · rw [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
      Units.val_inv_eq_inv_val, norm_inv, norm_idealChar_of_unitary hχ, inv_one,
      absNorm_conductor_of_ramifiedSet_eq_empty h0, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, norm_one, div_one]
  · simp only [Λ', sub_sub_cancel]
    calc Λ s = (((-Complex.I) ^ k * (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
          ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ)) * ((-Complex.I) ^ k *
            (((idealChar χ (gaussDual χ 1))⁻¹ : ℂˣ) : ℂ) /
              ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹) *
        ((((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
          (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - (1 - s))) *
            Λ s := by
          rw [mul_inv_cancel₀ hW, ← cpow_add _ _ hX, show 1 / 2 - s + (1 / 2 - (1 - s)) = 0 by ring,
            cpow_zero, one_mul, one_mul]
      _ = _ := by ring

/-- **Hecke's functional equation for unramified characters of weight $n \neq 0$ of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\xi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n, t)$, where $n \neq 0$ at the complex place. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. The function $\Lambda$ is entire. -/
theorem heckeFunctionalEquation_of_isQuadratic_of_unramified_weight (hK : finrank ℚ K = 2)
    (ξ : HeckeCharacter K) (h0 : ramifiedSet ξ = ∅)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (hn0 : n (quadPlace K hK).1 ≠ 0) :
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
  have hnr : ¬ (quadPlace K hK).1.IsReal := not_isReal_iff_isComplex.2 (quadPlace K hK).2
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℂ, t (quadPlace K hK).1 = t₀ := ⟨_, rfl⟩
  obtain ⟨χ, hξ⟩ : ∃ χ : HeckeCharacter K, ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ t₀ :=
    ⟨ξ * normPowerChar K (-t₀), fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]⟩
  have hξ' := inv_of_twist hξ
  have hp : ∀ v, χ.IsArchimedeanParameter v (n v) (t v - t₀) := fun v =>
    isArchimedeanParameter_of_twist hξ (hn v)
  have hp' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v + t₀) := fun v => by
    have h := isArchimedeanParameter_of_twist hξ' (hn' v)
    rwa [sub_neg_eq_add] at h
  have hq0 : t (quadPlace K hK).1 - t₀ = 0 := by rw [ht₀, sub_self]
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := fun w => by
    rw [eq_quadPlace K hK w, ← hq0]
    exact hp _
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hp0)
  have h0χ : ramifiedSet χ = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun v hv =>
    mem_ramifiedSet.1 hv ((isUnramifiedAt_twist_iff hξ v).1 (not_not.1 fun h => by
      simpa [h0] using (mem_ramifiedSet.2 h : v ∈ ramifiedSet ξ)))
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) := by
    rcases lt_or_gt_of_ne hn0 with hlt | hgt
    · obtain ⟨hq', ht'⟩ := eq_of_isArchimedeanParameter hnr (hp' (quadPlace K hK).1)
        (hp (quadPlace K hK).1).inv
      rw [ite_eq_right hnr, hq0, neg_zero] at *
      have hpi : ∀ v, χ⁻¹⁻¹.IsArchimedeanParameter v (n v) (t v - t₀) := by
        rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
        exact hp
      refine EntireFunctionalEquation.of_inv (entireFunctionalEquation_unramifiedWeight
        (ramifiedSet_inv χ ▸ h0χ) (norm_ideleChar_inv hu) hK (k := (-n (quadPlace K hK).1).toNat)
        (by omega) hp' hpi (by rw [hq']; omega) ht')
    · exact entireFunctionalEquation_unramifiedWeight h0χ hu hK
        (k := (n (quadPlace K hK).1).toNat) (by omega) hp hp' (by omega) hq0
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hu)

/-- **Hecke's functional equation for the Hecke characters of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\xi$ be a Hecke character with the archimedean parameters $(n, t)$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. If $\xi$ is ramified at one finite place, this is `Langlands.Tate.heckeFunctionalEquation_of_isQuadratic_of_ramified`. If $\xi$ is unramified at each finite place, the case $n = 0$ is `Langlands.Tate.heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent`, and the case $n \neq 0$ is `Langlands.Tate.heckeFunctionalEquation_of_isQuadratic_of_unramified_weight`. -/
theorem heckeFunctionalEquation_of_isQuadratic (hK : finrank ℚ K = 2) (ξ : HeckeCharacter K)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
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
  by_cases hS : (ramifiedSet ξ).Nonempty
  · exact heckeFunctionalEquation_of_isQuadratic_of_ramified hK ξ hS n n' t t' hn hn'
  by_cases hn0 : n (quadPlace K hK).1 = 0
  · refine heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent hK ξ
      (t (quadPlace K hK).1) (fun w y => ?_) n n' t t' hn hn'
    obtain rfl := eq_quadPlace K hK w
    rw [(hn _).eq y, hn0, zpow_zero, one_mul]
  · exact heckeFunctionalEquation_of_isQuadratic_of_unramified_weight hK ξ
      (Finset.not_nonempty_iff_eq_empty.1 hS) n n' t t' hn hn' hn0

/-- **Hecke's theorem for an imaginary quadratic field.** If $K$ is imaginary quadratic, then `Langlands.HeckeFunctionalEquationAt K` holds. -/
theorem heckeFunctionalEquationAt_of_isQuadratic (hK : finrank ℚ K = 2) :
    HeckeFunctionalEquationAt K :=
  fun ξ n n' t t' hn hn' => heckeFunctionalEquation_of_isQuadratic hK ξ n n' t t' hn hn'

end Assembly

end Langlands.Tate
