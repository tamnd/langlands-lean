/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.UnitUnfold

/-!
# The orbits of the units and the ideal class

Let $\mathfrak{a}$ be a nonzero fractional ideal of a number field $K$. The file `Langlands/Tate/UnitUnfold.lean` writes the Mellin transform $\Lambda_{\mathfrak{a}}(s)$ of the unit theta function as a Dirichlet series over the set `Orbits a` of the integral ideals $I$ such that $\mathfrak{a} I$ is principal, with the terms $|N(\alpha_I)|^{-s'}$ for a generator $\alpha_I$ of $\mathfrak{a} I$. This file identifies the set and the terms. The ideal $I$ is in `Orbits a` if and only if its class is $[\mathfrak{a}]^{-1}$, and $|N(\alpha_I)| = N(\mathfrak{a}) N(I)$. So for $\mathrm{Re}\, s > n/2$ and $s' = 2s/n$, $$\Lambda_{\mathfrak{a}}(s) = \frac{w_K}{2^{r - r_2} n R_K} \, \Gamma_K(s') \, N(\mathfrak{a})^{-s'} \sum_{[I] = [\mathfrak{a}]^{-1}} N(I)^{-s'}.$$

## Main results

* `Langlands.Tate.mem_orbits_iff`: the ideal $I$ is in `Orbits a` if and only if $[I] = [\mathfrak{a}]^{-1}$.
* `Langlands.Tate.abs_norm_orbitRep`: the equality $|N(\alpha_I)| = N(\mathfrak{a}) N(I)$.
* `Langlands.Tate.hasSum_Λ_unitThetaFEPair_absNorm`: the Dirichlet series with the norms of the ideals.
* `Langlands.Tate.hasSum_Λ_unitThetaFEPair_class`: the same series as a sum over all nonzero integral ideals.

## Proof

The class $[\mathfrak{a} I]$ is $1$ if and only if $\mathfrak{a} I$ is principal. If $\mathfrak{a} I = (x)$, then $x \in \mathfrak{a}$ because $I \le 1$, and $x \ne 0$ because $\mathfrak{a} I \ne 0$. Since $\mathfrak{a}$ is invertible, the ideal $I$ with $(x) = \mathfrak{a} I$ is unique. The norm identity is the multiplicativity of the absolute norm of fractional ideals, with $N((\alpha)) = |N_{K/\mathbb{Q}}(\alpha)|$.

## References

* J. Neukirch, Algebraic number theory, chapter VII, section 5.
-/

namespace Langlands.Tate

open Module Filter Topology MeasureTheory Set NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Real Classical nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- An integral ideal $I$ is in `Orbits a`, that is $\mathfrak{a} I$ is principal, if and only if $[I] = [\mathfrak{a}]^{-1}$ in the class group. -/
theorem mem_orbits_iff (I : (Ideal (𝓞 K))⁰) :
    I ∈ Orbits a ↔ ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ := by
  rw [← ClassGroup.mk_mk0 K, eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk_eq_one_iff,
    Units.val_mul, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨α, rfl⟩
    rw [mul_comm, ← spanSingleton_eq_mul_idealOf]
    exact ⟨⟨(α : K), FractionalIdeal.coe_spanSingleton _ _⟩⟩
  · rintro ⟨x, hx⟩
    have hx' : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (a : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
      rw [← FractionalIdeal.coe_spanSingleton (𝓞 K)⁰ x] at hx
      exact FractionalIdeal.coeToSubmodule_injective hx
    have hxa : x ∈ (a : FractionalIdeal (𝓞 K)⁰ K) := by
      have hmem : x ∈ ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (a : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [hx']
        exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ x
      exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one hmem
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, mul_eq_zero] at hx'
      rcases hx' with h | h
      · exact FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero I) h
      · exact Units.ne_zero _ h
    refine ⟨⟨⟨x, hxa⟩, hx0⟩, Subtype.ext (FractionalIdeal.coeIdeal_injective (K := K) ?_)⟩
    have h := spanSingleton_eq_mul_idealOf (a := a) ⟨⟨x, hxa⟩, hx0⟩
    rw [← hx', mul_comm] at h
    exact ((Units.isUnit a).mul_left_cancel h).symm

/-- For $I$ in `Orbits a` the generator $\alpha_I$ of $\mathfrak{a} I$ has $|N_{K/\mathbb{Q}}(\alpha_I)| = N(\mathfrak{a}) N(I)$. -/
theorem abs_norm_orbitRep (I : Orbits a) :
    |(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
  have h := congrArg FractionalIdeal.absNorm (spanSingleton_eq_mul_idealOf (orbitRep a I))
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm,
    idealOf_orbitRep] at h
  rw [← Rat.cast_abs]
  exact_mod_cast h

/-- For $\mathrm{Re}\, s > n/2$ and $s' = 2s/n$, the Mellin transform $\Lambda_{\mathfrak{a}}(s)$ is $w_K \Gamma_K(s') N(\mathfrak{a})^{-s'} \sum_I N(I)^{-s'}$ divided by $2^{r - r_2} n R_K$, where $I$ runs over the integral ideals with $\mathfrak{a} I$ principal. -/
theorem hasSum_Λ_unitThetaFEPair_absNorm {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (gammaK K (2 * s / finrank ℚ K) *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
          (-(2 * s / finrank ℚ K)) *
        ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) : ℂ) ^
          (-(2 * s / finrank ℚ K))) / ((unitConst K * 2 ^ rank K : ℝ) : ℂ))
      ((unitThetaFEPair a).Λ s) := by
  convert hasSum_Λ_unitThetaFEPair (a := a) hs using 3 with I
  rw [abs_norm_orbitRep, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Rat.cast_nonneg.2 (FractionalIdeal.absNorm_nonneg _))
      (Nat.cast_nonneg _), mul_assoc]

/-- The Dirichlet series of `hasSum_Λ_unitThetaFEPair_absNorm` as a sum over all nonzero integral ideals, with the terms outside the class $[\mathfrak{a}]^{-1}$ equal to $0$. -/
theorem hasSum_Λ_unitThetaFEPair_class {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then
        (torsionOrder K : ℂ) * (gammaK K (2 * s / finrank ℚ K) *
          ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)) *
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) /
          ((unitConst K * 2 ^ rank K : ℝ) : ℂ) else 0)
      ((unitThetaFEPair a).Λ s) := by
  set s' := 2 * s / finrank ℚ K
  set F : (Ideal (𝓞 K))⁰ → ℂ := fun I => (torsionOrder K : ℂ) * (gammaK K s' *
    ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s') *
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-s')) /
        ((unitConst K * 2 ^ rank K : ℝ) : ℂ) with hF
  have h0 : HasSum (F ∘ ((↑) : Orbits a → (Ideal (𝓞 K))⁰)) ((unitThetaFEPair a).Λ s) :=
    hasSum_Λ_unitThetaFEPair_absNorm a hs
  have h := (hasSum_subtype_iff_indicator (s := Orbits a)).1 h0
  convert h using 1
  funext I
  by_cases hI : I ∈ Orbits a
  · rw [Set.indicator_of_mem hI, ite_eq_left ((mem_orbits_iff a I).1 hI)]
  · rw [Set.indicator_of_notMem hI, ite_eq_right (fun h => hI ((mem_orbits_iff a I).2 h))]

end Langlands.Tate
