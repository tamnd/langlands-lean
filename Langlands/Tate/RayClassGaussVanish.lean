/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassGauss

/-!
# The vanishing of the Gauss sum of a ray class character

Let $\chi$ be a Hecke character of ray class type of a number field $K$, with conductor $\mathfrak{f}$, and let $J$ be a nonzero integral ideal. Let $\mathfrak{d}$ be the different ideal of $K$. This file proves that the Gauss sum $G_J(\beta)$ of `Langlands.Tate.rayGaussCoeff` is $0$ if the ideal $(\beta) \mathfrak{f} J \mathfrak{d}$ is not prime to $\mathfrak{f}$. This is the first open part of the file `Langlands.Tate.RayClassGauss`.

## Main results

* `IsRayClassType.exists_idealChar_ne_one_of_mem`: for a ramified place with prime ideal $\mathfrak{p}$, there is an integer $u$, prime to the ramified places, with $(u - 1) \mathfrak{p} \subseteq \mathfrak{f}$ and $\chi((u)) \neq 1$.
* `rayGaussCoeff_add_of_mem_dual`: $G_J(\beta + \gamma) = G_J(\beta)$ for $\gamma \in J^\vee$.
* `mul_dual_mul_le`: $I (I J)^\vee \subseteq J^\vee$ for nonzero fractional ideals $I$ and $J$.
* `inv_dual_eq_mul_differentIdeal`: $((\mathfrak{f} J)^\vee)^{-1} = \mathfrak{f} J \mathfrak{d}$.
* `IsRayClassType.rayGaussCoeff_eq_zero_of_mem`: $G_J(\beta) = 0$ for $\beta \in \mathfrak{p} (\mathfrak{f} J)^\vee$, where $\mathfrak{p}$ is the prime ideal of a ramified place.
* `IsRayClassType.rayGaussCoeff_eq_zero`: $G_J(\beta) = 0$ if $(\beta) \mathfrak{f} J \mathfrak{d}$ is an integral ideal $I$ with $I + \mathfrak{f} \neq \mathcal{O}_K$.

## Proofs

Let $v$ be a ramified place with prime ideal $\mathfrak{p}$ and conductor exponent $a \geq 1$. By the minimality of $a$, the local component $\chi_v$ is not trivial on $1 + \mathfrak{p}^{a - 1}$. So there is a unit $y$ of $K_v$ with $v(y - 1) \geq a - 1$ and $\chi_v(y) \neq 1$. The approximation lemma `IsRayClassType.exists_integer_idealChar` gives an integer $u$ with $v(u - y) \geq a$, $w(u - 1) \geq a_w$ at the other ramified places $w$, and $\chi((u)) = \chi_v(y)^{-1} \neq 1$. Then $v(u - 1) \geq a - 1$, so $(u - 1) \mathfrak{p} \subseteq \mathfrak{f}$. Let $\beta \in \mathfrak{p} (\mathfrak{f} J)^\vee$. Then $(u - 1) \beta \in \mathfrak{f} (\mathfrak{f} J)^\vee \subseteq J^\vee$, and thus $G_J(u \beta) = G_J(\beta)$. The twist relation `IsRayClassType.rayGaussCoeff_eq_mul` gives $G_J(\beta) = \chi((u)) G_J(\beta)$, so $G_J(\beta) = 0$. If $I = (\beta) \mathfrak{f} J \mathfrak{d}$ is not prime to $\mathfrak{f}$, a maximal ideal that contains $I + \mathfrak{f}$ is the prime ideal $\mathfrak{p}$ of a ramified place, and $\beta \in I (\mathfrak{f} J)^\vee \subseteq \mathfrak{p} (\mathfrak{f} J)^\vee$.

## Open parts

These steps are still open. First, the evaluation $G_J(\beta) = \tau(\chi) \overline{\chi}((\beta) \mathfrak{f} J \mathfrak{d})$ for $\beta \in (\mathfrak{f} J)^\vee$ with $(\beta) \mathfrak{f} J \mathfrak{d}$ prime to $\mathfrak{f}$. This needs that $(\mathfrak{f} J)^\vee / \mathfrak{d}^{-1} J^{-1}$ is a cyclic module over $\mathcal{O}_K / \mathfrak{f}$. Second, the identity $|\tau(\chi)|^2 = N(\mathfrak{f})$ for a primitive $\chi$. Third, the assembly into `Langlands.HeckeFunctionalEquationAt` for an imaginary quadratic field, as in the file `Langlands.Tate.RayClassGauss`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open Module Filter Topology Set Complex
open scoped Classical

namespace Langlands.Tate

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **An integer congruent to $1$ modulo $\mathfrak{f} \mathfrak{p}^{-1}$ with a nontrivial character value.** Let $\chi$ be of ray class type and let $v_0$ be a ramified place, with prime ideal $\mathfrak{p}$. There is a nonzero $u \in \mathcal{O}_K$ that is a unit at each ramified place, with $(u - 1) \mathfrak{p} \subseteq \mathfrak{f}$ and $\chi((u)) \neq 1$. -/
theorem IsRayClassType.exists_idealChar_ne_one_of_mem (hχ : IsRayClassType χ)
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ ramifiedSet χ) :
    ∃ (u : 𝓞 K) (hu : (u : K) ≠ 0),
      (∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) ∧
      Ideal.span {u - 1} * v₀.asIdeal ≤ χ.conductor ∧
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu)) ≠ 1 := by
  have ha₀ := conductorExponent_ne_zero_of_mem hv₀
  have hnt : ¬ χ.IsTrivialOnHigherUnits v₀ (χ.conductorExponent v₀ - 1) :=
    Nat.notMem_of_lt_sInf (Nat.sub_lt (Nat.pos_of_ne_zero ha₀) one_pos)
  simp only [HeckeCharacter.IsTrivialOnHigherUnits, not_forall] at hnt
  obtain ⟨y, hy, hy1, hχy⟩ := hnt
  obtain ⟨u, hu0, hu1, hu2, hcount, he⟩ := hχ.exists_integer_idealChar hv₀ y hy
  refine ⟨u, hu0, hcount, ?_, by rw [he]; exact inv_ne_one.2 hχy⟩
  have hmem : ∀ w ∈ ramifiedSet χ, w ≠ v₀ → u - 1 ∈ w.asIdeal ^ χ.conductorExponent w :=
    fun w hw hne => by
      have h := hu2 w hw hne
      rw [show (u : K) - 1 = algebraMap (𝓞 K) K (u - 1) by simp,
        HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_mem] at h
      exact h
  have hmem₀ : u - 1 ∈ v₀.asIdeal ^ (χ.conductorExponent v₀ - 1) := by
    have h : Valued.v (algebraMap K (v₀.adicCompletion K) ((u : K) - 1)) ≤
        WithZero.exp (-((χ.conductorExponent v₀ - 1 : ℕ) : ℤ)) := by
      rw [show algebraMap K (v₀.adicCompletion K) ((u : K) - 1) =
        (algebraMap K (v₀.adicCompletion K) (u : K) - y) + ((y : v₀.adicCompletion K) - 1) by
          rw [map_sub, map_one]; ring]
      refine (Valuation.map_add _ _ _).trans (max_le (hu1.trans ?_) hy1)
      rw [WithZero.exp_le_exp]
      omega
    rw [valued_algebraMap, show (u : K) - 1 = algebraMap (𝓞 K) K (u - 1) by simp,
      HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_le_pow_iff_mem] at h
    exact h
  rw [Ideal.span_singleton_mul_le_iff]
  intro x hx
  have hinf := HeightOneSpectrum.inf_pow_eq_prod (ramifiedSet χ) χ.conductorExponent
    (fun v => v) (fun i _ j _ h => h)
  rw [conductor_eq_prod, ← hinf, Submodule.mem_finsetInf]
  intro w hw
  by_cases hne : w = v₀
  · subst hne
    rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero ha₀), pow_succ]
    exact Ideal.mul_mem_mul hmem₀ hx
  · exact Ideal.mul_mem_right _ _ (hmem w hw hne)

/-- **The Gauss sum is periodic modulo the dual of $J$.** If $\gamma \in J^\vee$, that is $\mathrm{Tr}(\gamma \xi) \in \mathbb{Z}$ for each $\xi \in J$, then $G_J(\beta + \gamma) = G_J(\beta)$. -/
theorem rayGaussCoeff_add_of_mem_dual (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K)
    {γ : K} (hγ : γ ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    rayGaussCoeff χ J (β + γ) = rayGaussCoeff χ J β := by
  rw [rayGaussCoeff, rayGaussCoeff]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual (Units.ne_zero _)).1 hγ _
    ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm q.out).2
  rw [Algebra.traceForm_apply, eq_intCast] at hn
  rw [add_mul, map_add, ← hn, Rat.cast_add, Rat.cast_intCast, Complex.ofReal_add, mul_add,
    Complex.exp_add, Complex.ofReal_intCast, mul_comm _ (n : ℂ), Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

/-- For nonzero fractional ideals $I$ and $J$, $I (I J)^\vee \subseteq J^\vee$. -/
theorem mul_dual_mul_le {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I * FractionalIdeal.dual ℤ ℚ (I * J) ≤ FractionalIdeal.dual ℤ ℚ J := by
  rw [FractionalIdeal.le_dual_iff ℤ ℚ hJ, mul_comm I, mul_assoc,
    FractionalIdeal.dual_mul_self ℤ ℚ (mul_ne_zero hI hJ)]

/-- The fractional ideal of $\mathfrak{f} J$ is the product of the fractional ideals $\mathfrak{f}$ and $J$. -/
theorem coe_mk0_conductorNZ_mul (J : (Ideal (𝓞 K))⁰) :
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) *
        ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0, Submonoid.coe_mul,
    FractionalIdeal.coeIdeal_mul]
  rfl

/-- **The vanishing of the Gauss sum at one prime.** Let $\chi$ be of ray class type, let $v$ be a ramified place with prime ideal $\mathfrak{p}$, and let $\beta \in \mathfrak{p} (\mathfrak{f} J)^\vee$. Then $G_J(\beta) = 0$. For $\beta \neq 0$ the condition means that $\mathfrak{p}$ divides the integral ideal $(\beta) \mathfrak{f} J \mathfrak{d}$, because $((\mathfrak{f} J)^\vee)^{-1} = \mathfrak{f} J \mathfrak{d}$. -/
theorem IsRayClassType.rayGaussCoeff_eq_zero_of_mem (hχ : IsRayClassType χ) (J : (Ideal (𝓞 K))⁰)
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ ramifiedSet χ) {β : K}
    (hβ : β ∈ (v₀.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) :
    rayGaussCoeff χ J β = 0 := by
  obtain ⟨u, hu0, hcount, hle, hne⟩ := hχ.exists_idealChar_ne_one_of_mem hv₀
  have hβD : β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) :=
    mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one hβ
  have hmem : ((u : K) - 1) * β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : ((u : K) - 1) * β ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) - 1) *
        ((v₀.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
          ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
            FractionalIdeal (𝓞 K)⁰ K)) :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hβ
    have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) - 1) *
        (v₀.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≤ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) - 1) =
          ((Ideal.span {u - 1} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) by
        rw [FractionalIdeal.coeIdeal_span_singleton]; simp, ← FractionalIdeal.coeIdeal_mul]
      exact (FractionalIdeal.coeIdeal_le_coeIdeal K).2 hle
    rw [← mul_assoc] at h1
    have h3 := (FractionalIdeal.mul_le.2 fun a ha b hb => FractionalIdeal.mul_mem_mul (h2 ha) hb) h1
    rw [coe_mk0_conductorNZ_mul] at h3
    exact mul_dual_mul_le (coeIdeal_conductor_ne_zero χ) (Units.ne_zero _) h3
  have h := hχ.rayGaussCoeff_eq_mul ⟨v₀, hv₀⟩ J hu0 hcount hβD
  rw [show (u : K) * β = β + ((u : K) - 1) * β by ring, rayGaussCoeff_add_of_mem_dual χ J β hmem]
    at h
  have h4 : ((idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) : ℂ) - 1) *
      rayGaussCoeff χ J β = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 fun h0 => hne (Units.ext h0))

/-- The inverse of $(\mathfrak{f} J)^\vee$ is $\mathfrak{f} J \mathfrak{d}$, where $\mathfrak{d}$ is the different ideal of $K$. -/
theorem inv_dual_eq_mul_differentIdeal (J : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K))⁻¹ =
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.dual_eq_mul_inv, mul_inv, inv_inv, coeIdeal_differentIdeal ℤ ℚ K, mul_comm]

/-- **The vanishing of the Gauss sum.** Let $\chi$ be of ray class type, let $\beta \in K$, and let $I$ be an integral ideal with $I = (\beta) \mathfrak{f} J \mathfrak{d}$, where $\mathfrak{d}$ is the different ideal. If $I$ is not prime to $\mathfrak{f}$, that is $I + \mathfrak{f} \neq \mathcal{O}_K$, then $G_J(\beta) = 0$. The case $\beta = 0$, $I = 0$ is included. -/
theorem IsRayClassType.rayGaussCoeff_eq_zero (hχ : IsRayClassType χ) (J : (Ideal (𝓞 K))⁰)
    {β : K} (I : Ideal (𝓞 K))
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))
    (hIf : I ⊔ χ.conductor ≠ ⊤) :
    rayGaussCoeff χ J β = 0 := by
  have hD0 : FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero _)
  have hspan : (I : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    rw [hI, mul_assoc (FractionalIdeal.spanSingleton (𝓞 K)⁰ β),
      ← inv_dual_eq_mul_differentIdeal J, mul_assoc, inv_mul_cancel₀ hD0, mul_one]
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIf
  have hfM : χ.conductor ≤ M := le_sup_right.trans hIM
  rw [conductor_eq_prod] at hfM
  obtain ⟨v, hv, hvM⟩ := (hM.isPrime.prod_le).1 hfM
  have hvM' : v.asIdeal = M := by
    have := hM.isPrime
    exact v.isMaximal.eq_of_le hM.ne_top (Ideal.IsPrime.le_of_pow_le hvM)
  have hIv : I ≤ v.asIdeal := hvM' ▸ le_sup_left.trans hIM
  refine hχ.rayGaussCoeff_eq_zero_of_mem J hv ?_
  have hb := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ β
  rw [← hspan] at hb
  exact (FractionalIdeal.mul_le.2 fun a ha b hb => FractionalIdeal.mul_mem_mul
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 hIv ha) hb) hb

end Langlands.Tate
