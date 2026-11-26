/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassGauss

/-!
# The evaluation of the Gauss sum of a ray class character

Let $\chi$ be a Hecke character of ray class type of a number field $K$, with conductor $\mathfrak{f}$, and suppose that $\chi$ is ramified at one place at least. Let $J$ be a nonzero integral ideal, let $\mathfrak{d}$ be the different ideal of $K$, and let $D = (\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$. For $\beta \in K$ let $I_\beta = (\beta) \mathfrak{f} J \mathfrak{d}$. This file proves that $G_J(\beta) \chi(I_\beta)$ has the same value $\tau_J(\chi)$ for each $\beta$ with $I_\beta$ an integral ideal prime to $\mathfrak{f}$, where $G_J$ is the Gauss sum `Langlands.Tate.rayGaussCoeff`. Thus $G_J(\beta) = \tau_J(\chi) \overline{\chi}(I_\beta)$ for these $\beta$.

## Main definitions

* `Langlands.Tate.IsRayGaussPair`: the condition that $I$ is the integral ideal $(\beta) \mathfrak{f} J \mathfrak{d}$ and that $I + \mathfrak{f} = \mathcal{O}_K$.
* `Langlands.Tate.rayGaussSum`: the Gauss sum $\tau_J(\chi) = G_J(\beta_0) \chi(I_{\beta_0})$ for a chosen pair $(\beta_0, I_{\beta_0})$.

## Main results

* `spanSingleton_eq_coeIdeal_mul_dual`: $(\beta) = I_\beta D$.
* `IsRayGaussPair.dual_eq_add`: $D = (\beta) + \mathfrak{f} D$ if $I_\beta$ is prime to $\mathfrak{f}$. So $D / \mathfrak{f} D$ is a cyclic $\mathcal{O}_K / \mathfrak{f}$ module with the generator $\beta$.
* `IsRayGaussPair.exists_eq_mul_add`: each $\beta' \in D$ is $u \beta + z$ with $u \in \mathcal{O}_K$ and $z \in \mathfrak{f} D$.
* `IsRayGaussPair.notMem_of_eq_mul_add`: if moreover $I_{\beta'}$ is prime to $\mathfrak{f}$, then $u$ is a unit at each ramified place.
* `IsRayClassType.idealChar_eq_mul_of_eq_mul_add`: in this case $\chi(I_{\beta'}) = \chi((u)) \chi(I_\beta)$.
* `IsRayClassType.rayGaussCoeff_mul_idealChar_eq`: $G_J(\beta) \chi(I_\beta) = G_J(\beta') \chi(I_{\beta'})$.
* `exists_isRayGaussPair`: there is $\beta \in K$ with $I_\beta$ integral and prime to $\mathfrak{f}$.
* `IsRayClassType.rayGaussSum_eq`: $\tau_J(\chi) = G_J(\beta) \chi(I_\beta)$ for each such $\beta$.
* `IsRayClassType.rayGaussCoeff_eq_rayGaussSum_mul`: $G_J(\beta) = \tau_J(\chi) \overline{\chi(I_\beta)}$ if $I_\beta$ is integral and prime to $\mathfrak{f}$.

## Proofs

Since $I_\beta + \mathfrak{f} = \mathcal{O}_K$ and $(\beta) = I_\beta D$, we have $D = (I_\beta + \mathfrak{f}) D = (\beta) + \mathfrak{f} D$. So $\beta' = u \beta + z$ with $u \in \mathcal{O}_K$ and $z \in \mathfrak{f} D$. If $u \in \mathfrak{p}$ for a prime $\mathfrak{p} \mid \mathfrak{f}$, then $\beta' \in \mathfrak{p} D$, so $\mathfrak{p} \mid I_{\beta'}$, and this is false. At a ramified place $v$ we have $v(z) \geq a_v + v(D)$ and $v(u \beta) = v(D)$. So $\beta' / (u \beta) \equiv 1 \bmod \mathfrak{p}_v^{a_v}$, and $\chi((\beta')) = \chi((u \beta))$. This gives $\chi(I_{\beta'}) = \chi((u)) \chi(I_\beta)$. Since $z \in \mathfrak{f} D \subseteq J^\vee$, the Gauss sum gives $G_J(\beta') = G_J(u \beta)$, and the twist relation `IsRayClassType.rayGaussCoeff_eq_mul` gives $G_J(\beta) = \chi((u)) G_J(u \beta)$. The existence of $\beta$ is `IsDedekindDomain.exists_add_spanSingleton_mul_eq` applied to $\mathfrak{f} D \subseteq D$.

## Open parts

These steps are still open. First, $\tau_J(\chi)$ does not depend on $J$. This needs an element $t \in J$ with $(t) J^{-1}$ prime to $\mathfrak{f}$ and the bijection $\mathcal{O}_K / \mathfrak{f} \to J / \mathfrak{f} J$, $x \mapsto t x$, on the lattice quotient of `Langlands.Tate.rayGaussCoeff`. Second, the identity $|\tau_J(\chi)|^2 = N(\mathfrak{f})$. This needs the orthogonality of the characters $\xi \mapsto e^{2 \pi i \mathrm{Tr}(u \beta \xi)}$ of $J / \mathfrak{f} J$ for $u \in \mathcal{O}_K / \mathfrak{f}$, as a sum over a finite quotient of $\mathcal{O}_K$, and the count $N(\mathfrak{f})$ of `natCard_rayQuotient`. Third, the assembly into `Langlands.HeckeFunctionalEquationAt` for an imaginary quadratic field, as in the file `Langlands.Tate.RayClassGauss`. The file `Langlands.Tate.RayClassGaussVanish` was not built in the main checkout when this file was written, so this file does not import it. The three short lemmas of it that are necessary here are private in this file.

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

/-- The fractional ideal of $\mathfrak{f} J$ is the product of the fractional ideals $\mathfrak{f}$ and $J$. -/
private theorem coe_mk0_conductorNZ_mul_aux (J : (Ideal (𝓞 K))⁰) :
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) *
        ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0, Submonoid.coe_mul,
    FractionalIdeal.coeIdeal_mul]
  rfl

/-- The fractional ideal $\mathfrak{f} (\mathfrak{f} J)^\vee$ is contained in $J^\vee$. -/
private theorem conductor_mul_dual_le_aux (J : (Ideal (𝓞 K))⁰) :
    (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ≤ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hJ : ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero _
  rw [coe_mk0_conductorNZ_mul_aux, FractionalIdeal.le_dual_iff ℤ ℚ hJ,
    mul_comm (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.dual ℤ ℚ _),
    mul_assoc, FractionalIdeal.dual_mul_self ℤ ℚ (mul_ne_zero (coeIdeal_conductor_ne_zero χ) hJ)]

/-- The Gauss sum is periodic modulo $J^\vee$. -/
private theorem rayGaussCoeff_add_aux (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K)
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

/-- The conductor is contained in the prime ideal of each ramified place. -/
theorem conductor_le_asIdeal {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ ramifiedSet χ) :
    χ.conductor ≤ v.asIdeal := by
  rw [conductor_eq_prod]
  exact (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)).trans
    (Ideal.pow_le_self (conductorExponent_ne_zero_of_mem hv))

/-- **The condition on $\beta$ for the evaluation of the Gauss sum.** The pair $(\beta, I)$ satisfies the condition if $I$ is the integral ideal $(\beta) \mathfrak{f} J \mathfrak{d}$, where $\mathfrak{d}$ is the different ideal, and $I + \mathfrak{f} = \mathcal{O}_K$. -/
def IsRayGaussPair (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) (I : (Ideal (𝓞 K))⁰) :
    Prop :=
  (((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) ∧
    (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤

/-- The dual $(\mathfrak{f} J)^\vee$ is not zero. -/
theorem dual_conductor_mul_ne_zero (J : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero _)

/-- The inverse of $(\mathfrak{f} J)^\vee$ is $\mathfrak{f} J \mathfrak{d}$. -/
theorem inv_dual_conductor_mul (J : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K))⁻¹ =
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.dual_eq_mul_inv, mul_inv, inv_inv, coeIdeal_differentIdeal ℤ ℚ K, mul_comm]

/-- If $I = (\beta) \mathfrak{f} J \mathfrak{d}$, then $(\beta) = I (\mathfrak{f} J)^\vee$. -/
theorem spanSingleton_eq_coeIdeal_mul_dual (J : (Ideal (𝓞 K))⁰) {β : K} {I : Ideal (𝓞 K)}
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ β = (I : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  rw [hI, mul_assoc (FractionalIdeal.spanSingleton (𝓞 K)⁰ β), ← inv_dual_conductor_mul J,
    mul_assoc, inv_mul_cancel₀ (dual_conductor_mul_ne_zero J), mul_one]

/-- If $(\beta, I)$ satisfies the condition, then $\beta \in (\mathfrak{f} J)^\vee$. -/
theorem IsRayGaussPair.mem_dual {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) :
    β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  have hb := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ β
  rw [spanSingleton_eq_coeIdeal_mul_dual J h.1] at hb
  exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one hb

/-- If $(\beta, I)$ satisfies the condition, then $\beta \neq 0$. -/
theorem IsRayGaussPair.ne_zero {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) : β ≠ 0 := by
  intro h0
  have hs := spanSingleton_eq_coeIdeal_mul_dual J h.1
  rw [h0, map_zero] at hs
  have hI0 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero I)
  exact mul_ne_zero hI0 (dual_conductor_mul_ne_zero J) hs.symm

/-- **The cyclic module.** If $(\beta, I)$ satisfies the condition, then $(\mathfrak{f} J)^\vee = (\beta) + \mathfrak{f} (\mathfrak{f} J)^\vee$. Thus $(\mathfrak{f} J)^\vee / \mathfrak{d}^{-1} J^{-1}$ is a cyclic module over $\mathcal{O}_K / \mathfrak{f}$, with the generator $\beta$. -/
theorem IsRayGaussPair.dual_eq_add {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) :
    FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β +
      (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  conv_lhs => rw [← one_mul (FractionalIdeal.dual ℤ ℚ _), ← FractionalIdeal.coeIdeal_top, ← h.2,
    FractionalIdeal.coeIdeal_sup, add_mul]
  rw [spanSingleton_eq_coeIdeal_mul_dual J h.1]

/-- If $(\beta, I)$ satisfies the condition, then each $\beta' \in (\mathfrak{f} J)^\vee$ is $u \beta + z$ with $u \in \mathcal{O}_K$ and $z \in \mathfrak{f} (\mathfrak{f} J)^\vee$. -/
theorem IsRayGaussPair.exists_eq_mul_add {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) {β' : K}
    (hβ' : β' ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ u : 𝓞 K, ∃ z ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K), β' = (u : K) * β + z := by
  rw [h.dual_eq_add, FractionalIdeal.mem_add] at hβ'
  obtain ⟨y, hy, z, hz, rfl⟩ := hβ'
  obtain ⟨u, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 hy
  exact ⟨u, z, hz, by rw [Algebra.smul_def]⟩

/-- **The coefficient $u$ is prime to the conductor.** Let $(\beta, I)$ and $(\beta', I')$ satisfy the condition, and let $\beta' = u \beta + z$ with $u \in \mathcal{O}_K$ and $z \in \mathfrak{f} (\mathfrak{f} J)^\vee$. Then $u$ is not in the prime ideal of a ramified place. -/
theorem IsRayGaussPair.notMem_of_eq_mul_add {J : (Ideal (𝓞 K))⁰} {β β' : K}
    {I I' : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) (h' : IsRayGaussPair χ J β' I')
    {u : 𝓞 K} {z : K}
    (hz : z ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K))
    (he : β' = (u : K) * β + z) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ ramifiedSet χ) :
    u ∉ v.asIdeal := by
  intro hu
  have hfv := conductor_le_asIdeal hv
  have hmem : β' ∈ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    rw [he]
    refine FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨u, hu, rfl⟩) h.mem_dual))
      (FractionalIdeal.mem_coe.2 ?_))
    exact mul_le_mul_left ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 hfv) _ hz
  have hle := (FractionalIdeal.spanSingleton_le_iff_mem).2 hmem
  rw [spanSingleton_eq_coeIdeal_mul_dual J h'.1] at hle
  have hle' := mul_le_mul_left hle
    (FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K))⁻¹
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ (dual_conductor_mul_ne_zero J), mul_one, mul_one,
    FractionalIdeal.coeIdeal_le_coeIdeal] at hle'
  have htop := h'.2
  rw [eq_top_iff] at htop
  exact v.isPrime.ne_top (top_le_iff.1 (htop.trans (sup_le hle' hfv)))

/-- If $u \in \mathcal{O}_K$ is not in the prime ideal of $v$, then the exponent of $\mathfrak{p}_v$ in $(u)$ is $0$. -/
theorem count_spanSingleton_eq_zero_of_notMem {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    {v : HeightOneSpectrum (𝓞 K)} (hu : u ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 := by
  refine count_eq_zero_of_valuation_eq_one v (Units.mk0 _ hu0) ?_
  rw [Units.val_mk0, show (u : K) = algebraMap (𝓞 K) K u from rfl,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (v.intValuation_le_one u)
    (not_lt.1 fun h => hu ((v.intValuation_lt_one_iff_mem u).1 h))

/-- If $I + \mathfrak{f} = \mathcal{O}_K$, then the exponent of $\mathfrak{p}_v$ in $I$ is $0$ at each ramified place $v$. -/
theorem count_eq_zero_of_sup_conductor_eq_top {I : (Ideal (𝓞 K))⁰}
    (hI : (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ ramifiedSet χ) :
    FractionalIdeal.count K v ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [count_eq_zero_iff_not_dvd, Ideal.dvd_iff_le]
  intro hle
  rw [eq_top_iff] at hI
  exact v.isPrime.ne_top (top_le_iff.1 (hI.trans (sup_le hle (conductor_le_asIdeal hv))))

/-- **The character values of the ideals.** Let $\chi$ be of ray class type, let $(\beta, I)$ and $(\beta', I')$ satisfy the condition, and let $\beta' = u \beta + z$ with $u \in \mathcal{O}_K$ nonzero and $z \in \mathfrak{f} (\mathfrak{f} J)^\vee$. Then $\chi(I') = \chi((u)) \chi(I)$. -/
theorem IsRayClassType.idealChar_eq_mul_of_eq_mul_add (hχ : IsRayClassType χ)
    {J : (Ideal (𝓞 K))⁰} {β β' : K} {I I' : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I)
    (h' : IsRayGaussPair χ J β' I') {u : 𝓞 K} (hu0 : (u : K) ≠ 0) {z : K}
    (hz : z ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K))
    (he : β' = (u : K) * β + z) :
    idealChar χ (FractionalIdeal.mk0 K I') =
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) *
        idealChar χ (FractionalIdeal.mk0 K I) := by
  set D := FractionalIdeal.dual ℤ ℚ
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) with hD
  have hD0 : D ≠ 0 := dual_conductor_mul_ne_zero J
  have hβ0 := h.ne_zero
  have hβ0' := h'.ne_zero
  have hprin : ∀ {γ : K} {I₀ : (Ideal (𝓞 K))⁰} (hγ : IsRayGaussPair χ J γ I₀),
      toPrincipalIdeal (𝓞 K) K (Units.mk0 γ hγ.ne_zero) =
        FractionalIdeal.mk0 K I₀ * Units.mk0 D hD0 := fun {γ I₀} hγ => by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_mk0, Units.val_mk0]
    exact spanSingleton_eq_coeIdeal_mul_dual J hγ.1
  have huβ : (u : K) * β ≠ 0 := mul_ne_zero hu0 hβ0
  have hval : ∀ v ∈ ramifiedSet χ, v.valuation K (((Units.mk0 β' hβ0' : Kˣ) : K) -
      ((Units.mk0 ((u : K) * β) huβ : Kˣ) : K)) ≤ WithZero.exp (-(χ.conductorExponent v : ℤ)) *
        v.valuation K ((Units.mk0 ((u : K) * β) huβ : Kˣ) : K) := fun v hv => by
    rw [Units.val_mk0, Units.val_mk0, he, add_sub_cancel_left]
    have h1 := valuation_sub_le χ (Units.mk0 D hD0) (α := z) (β := 0)
      (by rw [sub_zero, Units.val_mk0]; exact hz) v
    rw [sub_zero, Units.val_mk0] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    have h2 := valuation_eq_exp_neg_count v (Units.mk0 _ huβ)
    rw [Units.val_mk0] at h2
    rw [h2, map_mul, FractionalIdeal.count_mul K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hu0)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hβ0),
      count_spanSingleton_eq_zero_of_notMem hu0 (h.notMem_of_eq_mul_add h' hz he hv),
      spanSingleton_eq_coeIdeal_mul_dual J h.1, FractionalIdeal.count_mul K v
      (FractionalIdeal.coeIdeal_ne_zero.2 (by
        rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero I)) hD0,
      count_eq_zero_of_sup_conductor_eq_top h.2 hv, zero_add, zero_add]
  have hχe := hχ.idealChar_toPrincipalIdeal_eq _ _ hval
  have hm : Units.mk0 ((u : K) * β) huβ = Units.mk0 (u : K) hu0 * Units.mk0 β hβ0 :=
    Units.ext rfl
  rw [hprin h', hm, map_mul, map_mul, hprin h] at hχe
  simp only [map_mul] at hχe
  rw [← mul_assoc] at hχe
  exact mul_right_cancel hχe

/-- **The Gauss sum times the character value is constant.** Let $\chi$ be of ray class type and ramified at one place. Let $(\beta, I)$ and $(\beta', I')$ satisfy the condition `Langlands.Tate.IsRayGaussPair`, that is $I = (\beta) \mathfrak{f} J \mathfrak{d}$ and $I' = (\beta') \mathfrak{f} J \mathfrak{d}$ are integral ideals prime to $\mathfrak{f}$. Then $G_J(\beta) \chi(I) = G_J(\beta') \chi(I')$. -/
theorem IsRayClassType.rayGaussCoeff_mul_idealChar_eq (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) {J : (Ideal (𝓞 K))⁰} {β β' : K} {I I' : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) (h' : IsRayGaussPair χ J β' I') :
    rayGaussCoeff χ J β * idealChar χ (FractionalIdeal.mk0 K I) =
      rayGaussCoeff χ J β' * idealChar χ (FractionalIdeal.mk0 K I') := by
  obtain ⟨u, z, hz, he⟩ := h.exists_eq_mul_add h'.mem_dual
  have hu : ∀ v ∈ ramifiedSet χ, u ∉ v.asIdeal := fun v hv => h.notMem_of_eq_mul_add h' hz he hv
  have hu0 : (u : K) ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h0
    exact hu v hv (by rw [show u = 0 from by exact_mod_cast h0]; exact zero_mem _)
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_notMem hu0 (hu v hv)
  have h1 := hχ.rayGaussCoeff_eq_mul hS J hu0 hcount h.mem_dual
  have h2 : rayGaussCoeff χ J β' = rayGaussCoeff χ J ((u : K) * β) := by
    rw [he]
    exact rayGaussCoeff_add_aux χ J _ (conductor_mul_dual_le_aux J hz)
  rw [hχ.idealChar_eq_mul_of_eq_mul_add h h' hu0 hz he, h1, h2, Units.val_mul]
  ring

/-- **The existence of $\beta$.** Let $\chi$ be ramified at one place. There are $\beta \in K$ and a nonzero integral ideal $I$ such that $(\beta, I)$ satisfies the condition `Langlands.Tate.IsRayGaussPair`. -/
theorem exists_isRayGaussPair (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    ∃ (β : K) (I : (Ideal (𝓞 K))⁰), IsRayGaussPair χ J β I := by
  set D := FractionalIdeal.dual ℤ ℚ
    ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) with hD
  have hD0 : D ≠ 0 := dual_conductor_mul_ne_zero J
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * D) (b := 1) (c := D)
    (mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one)
    (mul_ne_zero (coeIdeal_conductor_ne_zero χ) hD0) one_ne_zero
  rw [mul_one] at hx
  have hxD : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ D := by
    rw [← hx, ← FractionalIdeal.sup_eq_add]
    exact le_sup_right
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * D⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hD0]
    exact mul_le_mul_left hxD _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hID : (I : FractionalIdeal (𝓞 K)⁰ K) * D = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    rw [hI, mul_assoc, inv_mul_cancel₀ hD0, mul_one]
  have htop : I ⊔ χ.conductor = ⊤ := by
    refine FractionalIdeal.coeIdeal_injective (K := K) ?_
    change ((I ⊔ χ.conductor : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_sup]
    refine mul_right_cancel₀ hD0 ?_
    rw [add_mul, hID, one_mul, add_comm, hx]
  have hI0 : I ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hS
    rw [Submodule.zero_eq_bot, bot_sup_eq] at htop
    exact v.isPrime.ne_top (top_le_iff.1 (htop ▸ conductor_le_asIdeal hv))
  refine ⟨x, ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_, htop⟩
  change (I : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [hI, inv_dual_conductor_mul J, mul_assoc]

/-- **The Gauss sum of a ray class character for the ideal $J$.** It is $\tau_J(\chi) = G_J(\beta) \chi(I)$ for a chosen pair $(\beta, I)$ with $I = (\beta) \mathfrak{f} J \mathfrak{d}$ integral and prime to $\mathfrak{f}$. By `IsRayClassType.rayGaussCoeff_mul_idealChar_eq` the value does not depend on the choice. It is $0$ if there is no such pair. -/
noncomputable def rayGaussSum (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) : ℂ :=
  if h : ∃ (β : K) (I : (Ideal (𝓞 K))⁰), IsRayGaussPair χ J β I then
    rayGaussCoeff χ J h.choose * idealChar χ (FractionalIdeal.mk0 K h.choose_spec.choose)
  else 0

/-- The Gauss sum $\tau_J(\chi)$ is $G_J(\beta) \chi(I)$ for each pair $(\beta, I)$ that satisfies the condition. -/
theorem IsRayClassType.rayGaussSum_eq (hχ : IsRayClassType χ) (hS : (ramifiedSet χ).Nonempty)
    {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) :
    rayGaussSum χ J = rayGaussCoeff χ J β * idealChar χ (FractionalIdeal.mk0 K I) := by
  have hex : ∃ (β : K) (I : (Ideal (𝓞 K))⁰), IsRayGaussPair χ J β I := ⟨β, I, h⟩
  rw [rayGaussSum, dite_eq_left hex]
  exact hχ.rayGaussCoeff_mul_idealChar_eq hS hex.choose_spec.choose_spec h

/-- **The evaluation of the Gauss sum.** Let $\chi$ be of ray class type and ramified at one place, and let $\beta \in K$ such that $I = (\beta) \mathfrak{f} J \mathfrak{d}$ is an integral ideal prime to $\mathfrak{f}$. Then $G_J(\beta) = \tau_J(\chi) \overline{\chi(I)}$. -/
theorem IsRayClassType.rayGaussCoeff_eq_rayGaussSum_mul (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) :
    rayGaussCoeff χ J β =
      rayGaussSum χ J * starRingEnd ℂ (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) := by
  have hn := hχ.norm_idealChar (FractionalIdeal.mk0 K I)
  have hc : (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) *
      starRingEnd ℂ (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow, Complex.ofReal_one]
  rw [hχ.rayGaussSum_eq hS h, mul_assoc, hc, mul_one]

end Langlands.Tate
