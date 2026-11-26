/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassGaussNorm
import Langlands.Tate.HeckeClassTwist

/-!
# Hecke's functional equation for ray class characters of an imaginary quadratic field

Let $K$ be an imaginary quadratic field and let $\chi$ be a Hecke character of ray class type, that is, trivial at the infinite place, with conductor $\mathfrak{f}$. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi$, and then for each Hecke character $\xi$ of $K$ with $\xi_\infty = |\cdot|^{s_0}$, that is, with the archimedean parameter $n = 0$. The ramification at the finite places is arbitrary.

## Main definitions

* `Langlands.Tate.differentNZ`: the different ideal $\mathfrak{d}$ of $K$, as a nonzero integral ideal.
* `Langlands.Tate.DualFiber`: the elements $\beta \in K$ with $(\beta) \mathfrak{f} J \mathfrak{d} = I$, for nonzero integral ideals $J$ and $I$.
* `Langlands.Tate.dualEquiv`: the nonzero elements of $(\mathfrak{f} J)^\vee$ are in bijection with the pairs $(I, \beta)$ with $\beta$ in `DualFiber χ J I`.

## Main results

* `natCard_dualFiber`: the fiber `DualFiber χ J I` has $w$ elements if $I$ is in the class of $\mathfrak{f} J \mathfrak{d}$, and no element if not. Here $w$ is the number of roots of unity in $K$.
* `IsRayClassType.rayGaussCoeff_mul_cpow`: the term of the dual series at $\beta$ is $\tau(\chi) (2 / (N(\mathfrak{f}) N(J) |d_K|))^{-u} \chi^{-1}(I) N(I)^{-u}$ with $I = (\beta) \mathfrak{f} J \mathfrak{d}$.
* `IsRayClassType.hasSum_rayClassCompleted_two_sub`: for $\mathrm{Re}\, u > 1$, the value $\Lambda_J(2 - 2u)$ is a sum over the ideals $I$ in the class of $\mathfrak{f} J \mathfrak{d}$ of the terms of the partial L-series of $\chi^{-1}$.
* `IsRayClassType.dual_eq_completed`: the sum over the ideal classes of the values $\Lambda_{J_C}(2 - 2u)$ gives $\Gamma_\mathbb{C}(u) L(u, \chi^{-1})$, with the root number $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$.
* `IsRayClassType.heckeFunctionalEquation_of_ramified`: the conclusion of `Langlands.HeckeFunctionalEquationAt K` for a character of ray class type that is ramified at one finite place.
* `IsRayClassType.heckeFunctionalEquation_of_isQuadratic`: the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each character of ray class type.
* `IsRayClassType.heckeFunctionalEquation_twist`: the same for the twists $\chi \|\cdot\|^{s_0}$.
* `heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent`: the same for each Hecke character $\xi$ with $\xi_\infty = |\cdot|^{s_0}$.

## Proofs

Let $\chi$ be ramified at one place, let $w$ be the number of roots of unity in $K$, let $J_C$ be an integral ideal in the class $C$, and let $\tau = \tau(\chi)$ be the Gauss sum `Langlands.Tate.rayGaussSum`. We use $$\Lambda(s) = \frac{2^{1 - s}}{w} \sum_C (2 N(J_C))^s \Lambda_{J_C}(2s),$$ which is entire by `IsRayClassType.differentiable_rayClassCompleted_of_nonempty`. By `IsRayClassType.gammaℝ_mul_finiteLFunction` and $\Gamma_\mathbb{C}(s) = 2^{1 - s} \Gamma_\mathbb{R}(2s)$, it is equal to $\Gamma_\mathbb{C}(s) L(s, \chi)$ for $\mathrm{Re}\, s > 1$. We put $W = \tau / \sqrt{N(\mathfrak{f})}$ and $\Lambda'(s) = W^{-1} (|d_K| N(\mathfrak{f}))^{1/2 - s} \Lambda(1 - s)$. Then the functional equation holds by definition, and $|W| = 1$ by `IsRayClassType.norm_rayGaussSum_sq`. It remains to show that $\Lambda'(u) = \Gamma_\mathbb{C}(u) L(u, \chi^{-1})$ for $\mathrm{Re}\, u > 1$. The theta relation `rayClassCompleted_two_sub` and `hasSum_rayClass_dual` write $\Lambda_J(2 - 2u)$ as a series over the nonzero $\beta \in (\mathfrak{f} J)^\vee$. We sort the terms by the integral ideal $I = (\beta) \mathfrak{f} J \mathfrak{d}$. Each fiber is a torsor under the units, and all its terms are equal by `IsRayClassType.rayGaussCoeff_eq_rayGaussSum_mul` and `IsRayClassType.rayGaussCoeff_eq_zero`. For a fixed $I$, exactly one class $C$ satisfies $[I] = [\mathfrak{f} J_C \mathfrak{d}]$. The constants then combine to $2^{1 - u}$.

The characters of ray class type that are unramified at all finite places are of class group type, and the result for them is `IsClassType.heckeFunctionalEquation`. The twists follow with `heckeFunctionalEquation_of_twist`. A character $\xi$ with $\xi_\infty = |\cdot|^{s_0}$ is the twist of the character $\xi \|\cdot\|^{-s_0}$ of ray class type.

## Open parts

`Langlands.HeckeFunctionalEquation` is still open for these characters. For an imaginary quadratic field, the characters with an archimedean parameter $n \neq 0$ at the complex place are not covered. They need theta series with the harmonic polynomial $\bar{z}^{|n|}$. For the other number fields of degree more than $2$, and for the real quadratic fields, only the characters of class group type and their twists are covered, by `IsClassType.heckeFunctionalEquation_twist`. The ramified characters of these fields need the theta relation for a general lattice with a Gauss sum, and the characters that are not trivial at the infinite places need the theta series with signs and harmonic polynomials. For $K = \mathbb{Q}$ the theorem is `Langlands.heckeFunctionalEquationAt_rat`. The existence of the archimedean parameters is the separate statement `Langlands.ArchimedeanParametersExist`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open NumberField IsDedekindDomain InfinitePlace NumberField.Units Complex
open scoped nonZeroDivisors Classical

namespace Langlands.Tate

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

section Fiber

variable (K) in
/-- The different ideal $\mathfrak{d}$ of $K$ as a nonzero ideal. -/
noncomputable def differentNZ : (Ideal (𝓞 K))⁰ :=
  ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero (by
    rw [Submodule.zero_eq_bot]; exact differentIdeal_ne_bot)⟩

/-- The fractional ideal $\mathfrak{f} J \mathfrak{d}$ is the integral ideal $\mathfrak{f} J \mathfrak{d}$. -/
theorem coe_mk0_mul_differentIdeal (J : (Ideal (𝓞 K))⁰) :
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) =
      (((conductorNZ χ * J * differentNZ K : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [FractionalIdeal.coe_mk0, Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul]
  rfl

/-- The fibre of the ideal $I$: the elements $\beta \in K$ with $I = (\beta) \mathfrak{f} J \mathfrak{d}$. -/
abbrev DualFiber (χ : HeckeCharacter K) (J I : (Ideal (𝓞 K))⁰) : Type _ :=
  {β : K // ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)}

/-- The product of $(\mathfrak{f} J)^\vee$ and $\mathfrak{f} J \mathfrak{d}$ is $1$. -/
theorem dual_mul_eq_one (J : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) *
      (((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) = 1 := by
  rw [← inv_dual_conductor_mul]
  exact mul_inv_cancel₀ (dual_conductor_mul_ne_zero J)

/-- The fractional ideal $\mathfrak{f} J \mathfrak{d}$ is not zero. -/
theorem mk0_mul_differentIdeal_ne_zero (J : (Ideal (𝓞 K))⁰) :
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [coe_mk0_mul_differentIdeal]
  exact FractionalIdeal.coeIdeal_ne_zero.2 (by
    rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero _)

/-- An element of a fibre is not zero. -/
theorem DualFiber.ne_zero {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) : (β : K) ≠ 0 := by
  intro h0
  have h := β.2
  rw [h0, map_zero, zero_mul, zero_mul] at h
  exact nonZeroDivisors.coe_ne_zero I (FractionalIdeal.coeIdeal_eq_zero.1 h)

/-- An element of a fibre is in the dual $(\mathfrak{f} J)^\vee$. -/
theorem DualFiber.mem_dual {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) :
    (β : K) ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  have h := spanSingleton_eq_coeIdeal_mul_dual J β.2
  have hle := FractionalIdeal.spanSingleton_le_iff_mem.1
    (h ▸ mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one)
  exact hle

/-- Each nonzero $\beta \in (\mathfrak{f} J)^\vee$ is in the fibre of one nonzero integral ideal. -/
theorem exists_dualFiber (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) (h0 : β ≠ 0) :
    ∃ I : (Ideal (𝓞 K))⁰, ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
    rw [← dual_mul_eq_one (χ := χ) J, mul_assoc]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hβ) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  refine ⟨⟨I, mem_nonZeroDivisors_of_ne_zero fun hI0 => ?_⟩, hI⟩
  rw [hI0, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, mul_assoc] at hI
  exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 h0)
    (mk0_mul_differentIdeal_ne_zero J) hI.symm

/-- The ideal of a fibre is unique. -/
theorem DualFiber.unique {J I I' : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) (β' : DualFiber χ J I')
    (h : (β : K) = β') : I = I' := by
  have h1 := β.2
  have h2 := β'.2
  rw [← h] at h2
  exact Subtype.ext (FractionalIdeal.coeIdeal_injective (h1.trans h2.symm))

/-- The nonzero elements of $(\mathfrak{f} J)^\vee$, sorted by the ideal $I = (\beta) \mathfrak{f} J \mathfrak{d}$. -/
noncomputable def dualEquiv (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    {β : FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) // (β : K) ≠ 0} ≃ Σ I : (Ideal (𝓞 K))⁰, DualFiber χ J I where
  toFun β := ⟨(exists_dualFiber J β.1.2 β.2).choose, β.1.1,
    (exists_dualFiber J β.1.2 β.2).choose_spec⟩
  invFun p := ⟨⟨p.2.1, p.2.mem_dual⟩, p.2.ne_zero⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨I, β⟩ := p
    exact Sigma.subtype_ext (DualFiber.unique
      ⟨β.1, (exists_dualFiber J β.mem_dual β.ne_zero).choose_spec⟩ β rfl) rfl

/-- A nonempty fibre is in bijection with the units of $\mathcal{O}_K$. -/
noncomputable def dualFiberEquiv {J I : (Ideal (𝓞 K))⁰} (β₀ : DualFiber χ J I) :
    (𝓞 K)ˣ ≃ DualFiber χ J I :=
  Equiv.ofBijective (fun u => ⟨((u : 𝓞 K) : K) * β₀, by
      refine β₀.2.trans ?_
      congr 2
      exact FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨u, by
        rw [Units.smul_def, Algebra.smul_def]⟩⟩)
    ⟨fun u v huv => Units.ext (RingOfIntegers.coe_injective
      (mul_right_cancel₀ β₀.ne_zero (congrArg Subtype.val huv))), fun β => by
      have h : FractionalIdeal.spanSingleton (𝓞 K)⁰ (β₀ : K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) := by
        have h1 := β₀.2.symm.trans β.2
        rw [mul_assoc, mul_assoc] at h1
        exact mul_right_cancel₀ (mk0_mul_differentIdeal_ne_zero J) h1
      obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h
      refine ⟨u, Subtype.ext ?_⟩
      rw [← hu, Units.smul_def, Algebra.smul_def]⟩

/-- A fibre is nonempty if and only if $[I] = [\mathfrak{f} J \mathfrak{d}]$. -/
theorem nonempty_dualFiber_iff (J I : (Ideal (𝓞 K))⁰) :
    Nonempty (DualFiber χ J I) ↔
      ClassGroup.mk0 (conductorNZ χ * J * differentNZ K) = ClassGroup.mk0 I := by
  rw [ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K]
  constructor
  · rintro ⟨β⟩
    refine ⟨β, β.ne_zero, ?_⟩
    rw [← coe_mk0_mul_differentIdeal, ← mul_assoc]
    exact β.2.symm
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨x, ?_⟩⟩
    rw [← h, ← coe_mk0_mul_differentIdeal, ← mul_assoc]

variable [IsTotallyComplex K]

/-- A fibre is finite. -/
theorem finite_dualFiber (hK : Module.finrank ℚ K = 2) (J I : (Ideal (𝓞 K))⁰) :
    Finite (DualFiber χ J I) := by
  by_cases h : Nonempty (DualFiber χ J I)
  · have := finite_units_of_isQuadratic K hK
    exact Finite.of_equiv _ (dualFiberEquiv h.some)
  · have : IsEmpty (DualFiber χ J I) := not_nonempty_iff.1 h
    infer_instance

/-- The number of elements of a fibre is $w$ if $[I] = [\mathfrak{f} J \mathfrak{d}]$, and $0$ if not. -/
theorem natCard_dualFiber (hK : Module.finrank ℚ K = 2) (J I : (Ideal (𝓞 K))⁰) :
    Nat.card (DualFiber χ J I) =
      if ClassGroup.mk0 (conductorNZ χ * J * differentNZ K) = ClassGroup.mk0 I then
        torsionOrder K else 0 := by
  split_ifs with h
  · rw [← natCard_units_of_isQuadratic K hK]
    exact (Nat.card_congr (dualFiberEquiv ((nonempty_dualFiber_iff J I).2 h).some)).symm
  · have : IsEmpty (DualFiber χ J I) := not_nonempty_iff.1 (mt (nonempty_dualFiber_iff J I).1 h)
    exact Nat.card_of_isEmpty

end Fiber

section Character

/-- The character $\chi^{-1}$ is ramified at the same places as $\chi$. -/
theorem ramifiedSet_inv (χ : HeckeCharacter K) : ramifiedSet χ⁻¹ = ramifiedSet χ := by
  ext v
  rw [mem_ramifiedSet, mem_ramifiedSet]
  exact not_congr isTrivialOnHigherUnits_inv_iff

/-- The ideal character of $\chi^{-1}$ is the inverse of the ideal character of $\chi$. -/
theorem idealChar_inv (χ : HeckeCharacter K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealChar χ⁻¹ I = (idealChar χ I)⁻¹ := by
  rw [idealChar_apply, idealChar_apply, ← finprod_inv_distrib]
  refine finprod_congr fun v => ?_
  rw [primeValue_inv, inv_zpow]

/-- For a character of ray class type, $\overline{\chi(I)} = \chi^{-1}(I)$. -/
theorem IsRayClassType.conj_idealChar (hχ : IsRayClassType χ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    starRingEnd ℂ (idealChar χ I : ℂ) = (idealChar χ⁻¹ I : ℂ) := by
  have hc : (idealChar χ I : ℂ) * starRingEnd ℂ (idealChar χ I : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_idealChar, one_pow,
      Complex.ofReal_one]
  rw [idealChar_inv, Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_right hc

/-- A nonzero ideal $I$ is prime to $\mathfrak{f}$ if and only if no ramified prime divides $I$. -/
theorem sup_conductor_eq_top_iff (I : (Ideal (𝓞 K))⁰) :
    (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤ ↔
      ∀ v ∈ ramifiedSet χ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
  constructor
  · intro h v hv
    rw [← count_eq_zero_iff_not_dvd]
    exact count_eq_zero_of_sup_conductor_eq_top h hv
  · intro h
    rw [← Ideal.isCoprime_iff_sup_eq, conductor_eq_prod]
    refine IsCoprime.prod_right fun v hv => IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have he := v.isMaximal.eq_of_le hne le_sup_right
    exact h v hv (Ideal.dvd_iff_le.2 (he ▸ le_sup_left))

/-- If $I = (\beta) \mathfrak{f} J \mathfrak{d}$, then $|N(\beta)| N(\mathfrak{f}) N(J) |d_K| = N(I)$. -/
theorem DualFiber.abs_norm_mul {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) :
    |(Algebra.norm ℚ (β : K) : ℝ)| * ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) = Ideal.absNorm (I : Ideal (𝓞 K)) := by
  have h := congrArg FractionalIdeal.absNorm β.2
  rw [mul_assoc, coe_mk0_mul_differentIdeal, map_mul, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton] at h
  simp only [Submonoid.coe_mul, map_mul] at h
  have hd : Ideal.absNorm ((differentNZ K : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = (discr K).natAbs :=
    absNorm_differentIdeal K (𝓞 K)
  rw [hd] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', Nat.cast_natAbs, Int.cast_abs]
  rfl

end Character

section Value

/-- The constant $N(\mathfrak{f}) N(J) |d_K|$ is positive. -/
theorem conductor_mul_absNorm_mul_discr_pos (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    0 < (Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)| := by
  have hf : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hJ : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  positivity

/-- **The terms of the dual series.** Let $\chi$ be of ray class type and ramified at one place, and let $I = (\beta) \mathfrak{f} J \mathfrak{d}$. Then $$G_J(\beta) (2 |N(\beta)|)^{-u} = \tau(\chi) \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u},$$ where $\chi^{-1}(I) = 0$ if $I$ is not prime to $\mathfrak{f}$, and $\tau(\chi) = \tau_1(\chi)$ is the Gauss sum `Langlands.Tate.rayGaussSum`. -/
theorem IsRayClassType.rayGaussCoeff_mul_cpow (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) (u : ℂ) :
    rayGaussCoeff χ J β * ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u)) =
      rayGaussSum χ 1 * ((2 / ((Ideal.absNorm χ.conductor : ℝ) *
        Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
          rayWeight χ⁻¹ u I := by
  have hc := conductor_mul_absNorm_mul_discr_pos χ J
  have hn : 2 * |(Algebra.norm ℚ (β : K) : ℝ)| = 2 / ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) * Ideal.absNorm (I : Ideal (𝓞 K)) := by
    rw [← β.abs_norm_mul, div_mul_eq_mul_div, eq_div_iff hc.ne']
    ring
  rw [show -(2 * u) = 2 * -u by ring, sqrt_cpow_two_mul (by positivity), hn, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), rayWeight_apply,
    ramifiedSet_inv, Complex.ofReal_natCast]
  by_cases hI : (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤
  · rw [hχ.rayGaussCoeff_eq_rayGaussSum_mul hS ⟨β.2, hI⟩, hχ.rayGaussSum_eq_rayGaussSum_one hS J,
      hχ.conj_idealChar, ite_eq_left ((sup_conductor_eq_top_iff I).1 hI)]
    ring
  · rw [hχ.rayGaussCoeff_eq_zero J (I : Ideal (𝓞 K)) β.2 hI,
      ite_eq_right (mt (sup_conductor_eq_top_iff I).2 hI)]
    ring

end Value

section Dual

variable [IsTotallyComplex K]

/-- **The dual side of the theta relation.** Let $\chi$ be of ray class type and ramified at one place, and let $\mathrm{Re}\, u > 1$. Then $$\Lambda_J(2 - 2u) = \frac{1}{N(\mathfrak{f}) N(J) \sqrt{|d_K|}} \sum_{I \sim \mathfrak{f} J \mathfrak{d}} w \, \Gamma_\mathbb{R}(2u) \tau(\chi) \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u}.$$ The sum is over the integral ideals $I$ in the class of $\mathfrak{f} J \mathfrak{d}$, and $w$ is the number of roots of unity in $K$. -/
theorem IsRayClassType.hasSum_rayClassCompleted_two_sub (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : Module.finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰)
    {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => (((ZLattice.covolume (rayLattice χ J))⁻¹ : ℝ) : ℂ) *
        if ClassGroup.mk0 (conductorNZ χ * J * differentNZ K) = ClassGroup.mk0 I then
          (torsionOrder K : ℂ) * (Complex.Gammaℝ (2 * u) * (rayGaussSum χ 1 *
            ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
              |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * rayWeight χ⁻¹ u I))
        else 0)
      (rayClassCompleted χ J (2 - 2 * u)) := by
  have h := hasSum_rayClass_dual hK χ J (two_lt_re_two_mul hu)
  rw [← hasSum_subtype_iff_of_support_subset (s := {β : FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) | (β : K) ≠ 0}) fun β hβ h0 =>
    hβ (ite_eq_left h0)] at h
  replace h := ((dualEquiv χ J).symm.hasSum_iff (f := fun β : {β : FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) // (β : K) ≠ 0} => if (β : K) = 0 then (0 : ℂ) else
      Complex.Gammaℝ (2 * u) * (rayGaussCoeff χ J (β : K) *
        ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u))))).2 h
  rw [rayClassCompleted_two_sub hK]
  refine HasSum.mul_left _ (h.sigma fun I => ?_)
  have := finite_dualFiber (χ := χ) hK J I
  have := Fintype.ofFinite (DualFiber χ J I)
  convert hasSum_fintype fun _ : DualFiber χ J I => Complex.Gammaℝ (2 * u) * (rayGaussSum χ 1 *
    ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
      |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * rayWeight χ⁻¹ u I) using 1
  · funext c
    exact (ite_eq_right c.ne_zero).trans (congrArg _ (hχ.rayGaussCoeff_mul_cpow hS c u))
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_dualFiber hK,
      nsmul_eq_mul]
    split_ifs <;> simp

end Dual

section Scalar

/-- **The constant of the functional equation.** For $c, b, d > 0$, $$\sqrt{c} \, (d c)^{1/2 - u} 2^u (2 b)^{1 - u} \frac{1}{c b \sqrt{d}} \Big(\frac{2}{c b d}\Big)^{-u} = 2^{1 - u}.$$ -/
theorem scalar_eq_two_cpow {c b d : ℝ} (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) (u : ℂ) :
    ((√c : ℝ) : ℂ) * ((d * c : ℝ) : ℂ) ^ (1 / 2 - u) * ((2 : ℝ) : ℂ) ^ u *
        ((2 * b : ℝ) : ℂ) ^ (1 - u) * (((c * b * √d)⁻¹ : ℝ) : ℂ) *
          ((2 / (c * b * d) : ℝ) : ℂ) ^ (-u) =
      ((2 : ℝ) : ℂ) ^ (1 - u) := by
  have hs : ∀ x : ℝ, 0 < x → ((√x : ℝ) : ℂ) = cexp (Real.log x / 2 : ℝ) := fun x hx => by
    rw [← Complex.ofReal_exp, ← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.2 hx)]
  have hi : (((c * b * √d)⁻¹ : ℝ) : ℂ) = cexp (-(Real.log c + Real.log b + Real.log d / 2) : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_neg, ← Real.log_sqrt hd.le, ← Real.log_mul hc.ne' hb.ne',
      ← Real.log_mul (by positivity) (Real.sqrt_pos.2 hd).ne', Real.exp_log (by positivity)]
  rw [hs c hc, hi, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
    ofReal_cpow_eq_exp (by positivity), Real.log_mul hd.ne' hc.ne', Real.log_mul two_ne_zero hb.ne',
    Real.log_div two_ne_zero (by positivity), Real.log_mul (by positivity) hd.ne',
    Real.log_mul hc.ne' hb.ne']
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The scalar identity of the dual side, with the Gauss sum $\tau$ and the number $w$ of roots of unity. -/
theorem scalar_mul_eq {c b d : ℝ} (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) {τ w : ℂ} (hτ : τ ≠ 0)
    (hw : w ≠ 0) (u G r : ℂ) :
    (τ / ((√c : ℝ) : ℂ))⁻¹ * ((d * c : ℝ) : ℂ) ^ (1 / 2 - u) * (2 : ℂ) ^ (1 - (1 - u)) *
        (w⁻¹ * ((2 * b : ℝ) : ℂ) ^ (1 - u) * ((((c * b * √d)⁻¹ : ℝ) : ℂ) *
          (w * (G * (τ * ((2 / (c * b * d) : ℝ) : ℂ) ^ (-u) * r))))) =
      (2 : ℂ) ^ (1 - u) * G * r := by
  have h := scalar_eq_two_cpow hc hb hd u
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num] at h
  rw [show (1 : ℂ) - (1 - u) = u by ring, ← h, div_eq_mul_inv, mul_inv, inv_inv]
  calc _ = (τ * τ⁻¹) * (w * w⁻¹) * (((√c : ℝ) : ℂ) * ((d * c : ℝ) : ℂ) ^ (1 / 2 - u) * 2 ^ u *
        ((2 * b : ℝ) : ℂ) ^ (1 - u) * (((c * b * √d)⁻¹ : ℝ) : ℂ) *
          ((2 / (c * b * d) : ℝ) : ℂ) ^ (-u)) * G * r := by ring
    _ = _ := by rw [mul_inv_cancel₀ hτ, mul_inv_cancel₀ hw, one_mul, one_mul]

/-- $\Gamma_\mathbb{C}(u) = 2^{1 - u} \Gamma_\mathbb{R}(2u)$. -/
theorem gammaℂ_eq_two_cpow_mul (u : ℂ) :
    Complex.Gammaℂ u = (2 : ℂ) ^ (1 - u) * Complex.Gammaℝ (2 * u) := by
  rw [Complex.Gammaℂ_def, Complex.Gammaℝ_def, show -(2 * u) / 2 = -u by ring,
    show 2 * u / 2 = u by ring]
  have e := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le (-u)
  push_cast at e
  rw [e, sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
  ring

/-- For an imaginary quadratic field, the archimedean factor for the parameters $0$ is $\Gamma_\mathbb{C}(s)$. -/
theorem gammaFactor_zero_of_isQuadratic [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (s : ℂ) : gammaFactor K 0 0 s = Complex.Gammaℂ s := by
  obtain ⟨w₀, hw₀⟩ := Fintype.card_eq_one_iff.1 (card_infinitePlace_of_isQuadratic K hK)
  rw [gammaFactor, Fintype.prod_eq_single w₀ fun w hw => absurd (hw₀ w) hw,
    ite_eq_right (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w₀))]
  simp

end Scalar

section Assembly

variable [IsTotallyComplex K]

omit [IsTotallyComplex K] in
/-- The Gauss sum of a character of ray class type that is ramified at one place is not zero. -/
theorem IsRayClassType.rayGaussSum_one_ne_zero (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) : rayGaussSum χ 1 ≠ 0 := by
  intro h0
  have h := hχ.norm_rayGaussSum_sq hS 1
  rw [h0, norm_zero, zero_pow two_ne_zero, eq_comm, Nat.cast_eq_zero,
    Ideal.absNorm_eq_zero_iff] at h
  exact conductor_ne_zero χ h

omit [IsTotallyComplex K] in
/-- The ideal classes $C$ with $C \sim \mathfrak{f} J_C \mathfrak{d}$ for a fixed integral ideal $I$: there is exactly one, namely $[I] [\mathfrak{f}]^{-1} [\mathfrak{d}]^{-1}$. -/
theorem mk0_conductor_mul_classIdeal_iff (χ : HeckeCharacter K) (I : (Ideal (𝓞 K))⁰)
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (conductorNZ χ * classIdeal K C * differentNZ K) = ClassGroup.mk0 I ↔
      C = ClassGroup.mk0 I * (ClassGroup.mk0 (conductorNZ χ) * ClassGroup.mk0 (differentNZ K))⁻¹ := by
  rw [map_mul, map_mul, mk0_classIdeal, eq_mul_inv_iff_mul_eq,
    mul_comm (ClassGroup.mk0 (conductorNZ χ)) C, mul_assoc]

/-- **The functional equation on the half plane.** Let $\chi$ be a Hecke character of ray class type of an imaginary quadratic field, ramified at one place, and let $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$. For $\mathrm{Re}\, u > 1$, $$W^{-1} (|d_K| N(\mathfrak{f}))^{1/2 - u} 2^{u} \frac{1}{w} \sum_C (2 N(J_C))^{1 - u} \Lambda_{J_C}(2 (1 - u)) = \Gamma_\mathbb{C}(u) L(u, \chi^{-1}).$$ The left side is the value at $1 - u$ of the entire function that gives $\Gamma_\mathbb{C}(s) L(s, \chi)$ for $\mathrm{Re}\, s > 1$. -/
theorem IsRayClassType.dual_eq_completed (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : Module.finrank ℚ K = 2) {u : ℂ} (hu : 1 < u.re) :
    (rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
        (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - u) *
          ((2 : ℂ) ^ (1 - (1 - u)) * ∑ C : ClassGroup (𝓞 K), (torsionOrder K : ℂ)⁻¹ *
            ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u) *
              rayClassCompleted χ (classIdeal K C) (2 * (1 - u))) =
      Complex.Gammaℂ u * χ⁻¹.finiteLFunction u := by
  have hτ := hχ.rayGaussSum_one_ne_zero hS
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) =
      ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [hχ.inv.finiteLFunction_eq hu, ← tsum_mul_left, hX]
  simp_rw [show 2 * (1 - u) = 2 - 2 * u by ring]
  have h := hasSum_sum fun C (_ : C ∈ Finset.univ) =>
    (hχ.hasSum_rayClassCompleted_two_sub hS hK (classIdeal K C) hu).mul_left
      ((torsionOrder K : ℂ)⁻¹ *
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u))
  refine (HasSum.tsum_eq ?_).symm
  convert h.mul_left ((rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
    ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ^ (1 / 2 - u) *
      (2 : ℂ) ^ (1 - (1 - u))) using 1
  · funext I
    simp only [mul_ite, mul_zero]
    simp_rw [mk0_conductor_mul_classIdeal_iff]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), covolume_rayLattice,
      gammaℂ_eq_two_cpow_mul]
    have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
      fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
    have hb : ∀ J : (Ideal (𝓞 K))⁰, (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := fun J =>
      Nat.cast_pos.2 (Nat.pos_of_ne_zero
        fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
    rw [← scalar_mul_eq hc (hb (classIdeal K (ClassGroup.mk0 I *
      (ClassGroup.mk0 (conductorNZ χ) * ClassGroup.mk0 (differentNZ K))⁻¹))) hd hτ hw u
        (Complex.Gammaℝ (2 * u)) (rayWeight χ⁻¹ u I)]
  · ring

/-- **Hecke's functional equation for ramified characters of ray class type of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\chi$ be a Hecke character of ray class type that is ramified at one finite place. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\chi$, with $\sigma = 0$, the root number $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$ and an entire function $\Lambda$. -/
theorem IsRayClassType.heckeFunctionalEquation_of_ramified (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : Module.finrank ℚ K = 2)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(χ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = χ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = χ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  obtain rfl : n = 0 := funext fun v => (hχ.isArchimedeanParameter (hn v)).1
  obtain rfl : t = 0 := funext fun v => (hχ.isArchimedeanParameter (hn v)).2
  obtain rfl : n' = 0 := funext fun v => (hχ.inv.isArchimedeanParameter (hn' v)).1
  obtain rfl : t' = 0 := funext fun v => (hχ.inv.isArchimedeanParameter (hn' v)).2
  have hτ := hχ.rayGaussSum_one_ne_zero hS
  have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.2 (abs_ne_zero.2 (discr_ne_zero K)))
      (Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hW : rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hτ (ofReal_ne_zero.2 (Real.sqrt_pos.2 hc).ne')
  set Λ : ℂ → ℂ := fun z => (2 : ℂ) ^ (1 - z) * ∑ C : ClassGroup (𝓞 K),
    (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ z *
      rayClassCompleted χ (classIdeal K C) (2 * z) with hΛ
  have hd : Differentiable ℂ Λ := by
    have hR := fun C : ClassGroup (𝓞 K) =>
      hχ.differentiable_rayClassCompleted_of_nonempty hS (classIdeal K C)
    have hb : ∀ C : ClassGroup (𝓞 K),
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := fun C =>
      ofReal_ne_zero.2 (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 fun h0 =>
        nonZeroDivisors.coe_ne_zero _ (Ideal.absNorm_eq_zero_iff.1 h0)))
    refine ((differentiable_id.const_sub 1).const_cpow (Or.inl two_ne_zero)).mul
      (Differentiable.fun_sum fun C _ => ?_)
    exact ((differentiable_const _).mul (differentiable_id.const_cpow (Or.inl (hb C)))).mul
      ((hR C).comp (differentiable_id.const_mul 2))
  set Λ' : ℂ → ℂ := fun z => (rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
    (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - z) * Λ (1 - z) with hΛ'
  have hd' : Differentiable ℂ Λ' :=
    ((differentiable_const _).mul ((differentiable_id.const_sub _).const_cpow (Or.inl hX))).mul
      (hd.comp (differentiable_id.const_sub 1))
  refine ⟨0, hχ.norm_eq_ideleNorm_rpow, Λ, Λ',
    rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ),
    fun s _ => (hd.analyticAt s).meromorphicAt, fun s _ => (hd'.analyticAt s).meromorphicAt,
    fun s hs => ?_, fun s hs => ?_, ?_, fun s => ?_, Or.inl fun s => hd.analyticAt s⟩
  · rw [sub_zero] at hs
    rw [HeckeCharacter.completedLFunction, gammaFactor_zero_of_isQuadratic hK,
      gammaℂ_eq_two_cpow_mul, mul_assoc, hχ.gammaℝ_mul_finiteLFunction hS hK hs]
  · rw [add_zero] at hs
    rw [HeckeCharacter.completedLFunction, gammaFactor_zero_of_isQuadratic hK,
      ← hχ.dual_eq_completed hS hK hs]
  · have h := hχ.norm_rayGaussSum_sq hS 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← h,
      Real.sqrt_sq (norm_nonneg _), div_self (norm_ne_zero_iff.2 hτ)]
  · simp only [hΛ', sub_sub_cancel, ofReal_zero, sub_zero]
    calc Λ s = (rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) *
          (rayGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹) *
        ((((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
          (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - (1 - s))) *
            Λ s := by
          rw [mul_inv_cancel₀ hW, ← cpow_add _ _ hX, show 1 / 2 - s + (1 / 2 - (1 - s)) = 0 by ring,
            cpow_zero, one_mul, one_mul]
      _ = _ := by ring

/-- **Hecke's functional equation for characters of ray class type of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\chi$ be a Hecke character of ray class type, that is, trivial at the infinite places. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\chi$. The unramified case is `Langlands.Tate.IsClassType.heckeFunctionalEquation`. -/
theorem IsRayClassType.heckeFunctionalEquation_of_isQuadratic (hχ : IsRayClassType χ)
    (hK : Module.finrank ℚ K = 2)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(χ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = χ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = χ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  by_cases hS : (ramifiedSet χ).Nonempty
  · exact hχ.heckeFunctionalEquation_of_ramified hS hK n n' t t' hn hn'
  · refine (hχ.isClassType fun v => ?_).heckeFunctionalEquation n n' t t' hn hn'
    by_contra h
    exact hS ⟨v, mem_ramifiedSet.2 h⟩

/-- **Hecke's functional equation for the twists $\chi \|\cdot\|^{s_0}$.** Let $K$ be imaginary quadratic, let $\chi$ be a Hecke character of ray class type and let $\xi = \chi \|\cdot\|^{s_0}$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. -/
theorem IsRayClassType.heckeFunctionalEquation_twist (hχ : IsRayClassType χ)
    (hK : Module.finrank ℚ K = 2) {ξ : HeckeCharacter K} {s₀ : ℂ}
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
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
  have hξ' := inv_of_twist hξ
  refine heckeFunctionalEquation_of_twist hξ n n' t t' (hχ.heckeFunctionalEquation_of_isQuadratic hK
    n n' _ _ (fun v => isArchimedeanParameter_of_twist hξ (hn v)) (fun v => ?_))
  have h := isArchimedeanParameter_of_twist hξ' (hn' v)
  rwa [sub_neg_eq_add] at h

/-- **Hecke's functional equation for the characters with $n = 0$.** Let $K$ be imaginary quadratic and let $\xi$ be a Hecke character with $\xi_w(y) = |\iota(y)|^{m_w s_0}$ at each infinite place $w$, for one $s_0 \in \mathbb{C}$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. The ramification of $\xi$ at the finite places is arbitrary. -/
theorem heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent (hK : Module.finrank ℚ K = 2)
    (ξ : HeckeCharacter K) (s₀ : ℂ)
    (hinf : ∀ (w : InfinitePlace K) (y : w.Completionˣ), (ξ.infiniteComponent w y : ℂ) =
      (‖Completion.extensionEmbedding w y‖ : ℂ) ^ ((w.mult : ℂ) * s₀))
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
  have hξ : ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = ((ξ * normPowerChar K (-s₀)) x : ℂ) * (ideleNorm K x : ℂ) ^ s₀ := fun x => by
    rw [mul_normPowerChar_apply, mul_assoc,
      ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
      mul_one]
  have hχ : IsRayClassType (ξ * normPowerChar K (-s₀)) := ⟨fun w y => Units.ext (by
    have hc : (‖Completion.extensionEmbedding w y‖ : ℂ) ^ ((w.mult : ℂ) * s₀) ≠ 0 :=
      Complex.cpow_ne_zero_iff.2
        (Or.inl (ofReal_ne_zero.2 (norm_ne_zero_iff.2 ((map_ne_zero _).2 y.ne_zero))))
    have h := infiniteComponent_of_twist hξ w y
    rw [hinf] at h
    rw [Units.val_one]
    exact mul_right_cancel₀ hc (h.symm.trans (one_mul _).symm))⟩
  exact hχ.heckeFunctionalEquation_twist hK hξ n n' t t' hn hn'

end Assembly

end Langlands.Tate
