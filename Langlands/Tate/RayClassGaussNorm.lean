/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassGaussVanish
import Langlands.Tate.RayClassGaussEval

/-!
# The absolute value of the Gauss sum of a ray class character

Let $\chi$ be a Hecke character of ray class type of a number field $K$, with conductor $\mathfrak{f}$, and suppose that $\chi$ is ramified at one place at least. Let $J$ be a nonzero integral ideal and let $G_J$ be the Gauss sum `Langlands.Tate.rayGaussCoeff`, a sum over the finite quotient $J / \mathfrak{f} J$. This file proves that the Gauss sum $\tau_J(\chi)$ of `Langlands.Tate.rayGaussSum` does not depend on $J$, and that $|\tau_J(\chi)|^2 = N(\mathfrak{f})$.

## Main definitions

* `Langlands.Tate.traceExp`: the additive character $e(r) = e^{2 \pi i \mathrm{Tr}(r)}$ of $K$.

## Main results

* `sum_out_eq_zero_of_ne_one`: the sum of a nontrivial character over a finite quotient group is zero.
* `sum_traceExp_eq`: for $\gamma \in (\mathfrak{f} J)^\vee$, the sum of $e(\gamma \xi)$ over $\xi \in J / \mathfrak{f} J$ is $N(\mathfrak{f})$ if $\gamma \in J^\vee$, and $0$ if not.
* `IsRayClassType.rayGaussCoeff_mul_eq`: $G_J(\nu \beta) = \overline{c(\nu)} G_J(\beta)$ for each $\nu \in \mathcal{O}_K$, where $c$ is the coefficient `Langlands.Tate.rayCoeff` for the ideal $\mathcal{O}_K$.
* `IsRayGaussPair.mul_mem_dual_one_iff`: if $I_\beta = (\beta) \mathfrak{f} J \mathfrak{d}$ is integral and prime to $\mathfrak{f}$, then $\beta \zeta \in \mathcal{O}_K^\vee$ if and only if $\zeta \in \mathfrak{f} J$, for $\zeta \in J$.
* `IsRayClassType.mul_rayCoeff_eq`: $N(\mathfrak{f}) c_J(\xi) = G_J(\beta) \overline{G_1(\beta \xi)}$ for each $\xi \in J$ and each such $\beta$.
* `IsRayClassType.rayGaussCoeff_mul_conj`: $G_1(\beta) \overline{G_1(\beta)} = N(\mathfrak{f})$ for each such $\beta$ with $J = \mathcal{O}_K$.
* `IsRayClassType.rayGaussSum_eq_rayGaussSum_one`: $\tau_J(\chi) = \tau_1(\chi)$.
* `IsRayClassType.rayGaussSum_mul_conj`: $\tau_J(\chi) \overline{\tau_J(\chi)} = N(\mathfrak{f})$.
* `IsRayClassType.norm_rayGaussSum_sq`: $|\tau_J(\chi)|^2 = N(\mathfrak{f})$.

## Proofs

The proof does not count units modulo $\mathfrak{f}$. First, the twist relation `IsRayClassType.rayGaussCoeff_eq_mul` and the vanishing `IsRayClassType.rayGaussCoeff_eq_zero_of_mem` give $G_J(\nu \beta) = \overline{c(\nu)} G_J(\beta)$ for all $\nu \in \mathcal{O}_K$. We expand $G_J(\beta) \overline{G_1(\beta \xi)}$ as a double sum over $x \in J / \mathfrak{f} J$ and $n \in \mathcal{O}_K / \mathfrak{f}$. The inner sum over $n$ is a character sum of $e(\beta (x - \xi) n)$. By orthogonality it is $N(\mathfrak{f})$ if $\beta (x - \xi) \in \mathcal{O}_K^\vee$, and $0$ if not. The first condition holds if and only if $x \equiv \xi$ modulo $\mathfrak{f} J$. This gives $N(\mathfrak{f}) c_J(\xi) = G_J(\beta) \overline{G_1(\beta \xi)}$. For $J = \mathcal{O}_K$ and $\xi = 1$ this is $|G_1(\beta)|^2 = N(\mathfrak{f})$. For a general $J$, choose $t$ with $(t) = T J$ and $T + \mathfrak{f} = \mathcal{O}_K$. Then $(\beta t, I_\beta T)$ is a pair for $\mathcal{O}_K$, and the identity at $\xi = t$ gives $G_J(\beta) \chi(I_\beta) = G_1(\beta t) \chi(I_\beta T)$. Thus $\tau_J(\chi) = \tau_1(\chi)$.

## Open parts

The Gauss sum $\tau(\chi) = \tau_J(\chi)$ now does not depend on $J$, and the root number $W(\chi) = \tau(\chi) / \sqrt{N(\mathfrak{f})}$ has absolute value $1$. The assembly into `Langlands.HeckeFunctionalEquationAt` for an imaginary quadratic field is still open. It needs these steps: the identification of the dual theta series with the partial L-series of $\chi^{-1}$, the sum over the ideal classes, the root number $W(\chi) = \tau(\chi) / \sqrt{N(\mathfrak{f})}$ in the functional equation, and the comparison of the gamma factors.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open Module Filter Topology Set Complex
open scoped Classical

namespace Langlands.Tate

section Finite

/-- If $F$ is constant on the cosets of $H$, then $F$ of the chosen representative of the class of $g$ is $F(g)$. -/
theorem out_mk_eq {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (F : G → ℂ)
    (hF : ∀ g h, h ∈ H → F (g + h) = F g) (g : G) :
    F (QuotientAddGroup.mk (s := H) g).out = F g := by
  have h : -g + (QuotientAddGroup.mk (s := H) g).out ∈ H :=
    QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
  have := hF g _ h
  rwa [add_neg_cancel_left] at this

/-- If $F$ is constant on the cosets of $H$, takes sums to products, and $F(g_0) \neq 1$ for some $g_0$, then the sum of $F$ over the representatives of $G / H$ is zero. -/
theorem sum_out_eq_zero_of_ne_one {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    [Fintype (G ⧸ H)] (F : G → ℂ) (hF : ∀ g h, h ∈ H → F (g + h) = F g)
    (hadd : ∀ a b, F (a + b) = F a * F b) {g₀ : G} (hg₀ : F g₀ ≠ 1) :
    ∑ q : G ⧸ H, F q.out = 0 := by
  have h1 : ∑ q : G ⧸ H, F q.out = ∑ q : G ⧸ H, F (q + (g₀ : G ⧸ H)).out :=
    (Fintype.sum_equiv (Equiv.addRight (g₀ : G ⧸ H)) _ _ fun q => rfl).symm
  have h2 : ∀ q : G ⧸ H, F (q + (g₀ : G ⧸ H)).out = F q.out * F g₀ := fun q => by
    have : q + (g₀ : G ⧸ H) = ((q.out + g₀ : G) : G ⧸ H) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [this, out_mk_eq H F hF, hadd]
  rw [Finset.sum_congr rfl fun q _ => h2 q, ← Finset.sum_mul] at h1
  have h3 : (F g₀ - 1) * ∑ q : G ⧸ H, F q.out = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hg₀)

end Finite

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (K) in
/-- The additive character $e(r) = e^{2 \pi i \mathrm{Tr}_{K/\mathbb{Q}}(r)}$ of $K$. -/
noncomputable def traceExp (r : K) : ℂ :=
  cexp (2 * Real.pi * I * ((Algebra.trace ℚ K r : ℚ) : ℝ))

/-- The function `traceExp` takes sums to products. -/
theorem traceExp_add (a b : K) : traceExp K (a + b) = traceExp K a * traceExp K b := by
  rw [traceExp, traceExp, traceExp, map_add, Rat.cast_add, Complex.ofReal_add, mul_add,
    Complex.exp_add]

/-- The complex conjugate of $e(a)$ is $e(-a)$. -/
theorem conj_traceExp (a : K) : starRingEnd ℂ (traceExp K a) = traceExp K (-a) := by
  rw [traceExp, traceExp, ← Complex.exp_conj, map_neg, Rat.cast_neg, Complex.ofReal_neg]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- The value $e(a)$ is $1$ if and only if the trace of $a$ is an integer. -/
theorem traceExp_eq_one_iff (a : K) :
    traceExp K a = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ K a = n := by
  rw [traceExp, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : (((Algebra.trace ℚ K a : ℚ) : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h2; rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩

/-- The Gauss sum `rayGaussCoeff` written with `traceExp`. -/
theorem rayGaussCoeff_eq_sum (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) :
    rayGaussCoeff χ J β = ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
    rayLatticeCoeff χ J q.out * traceExp K (β *
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm q.out : K)) := rfl

set_option hygiene false in
/-- The bijection $J \to \varphi(J)$. -/
local notation "𝔢[" J "]" => globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

set_option hygiene false in
/-- The finite quotient $\varphi(J) / \varphi(\mathfrak{f} J)$. -/
local notation "𝔔[" χ ", " J "]" => traceLattice K (FractionalIdeal.mk0 K J) ⧸
  subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)

/-- The unit ideal as a fractional ideal is $1$. -/
theorem coe_mk0_one : 𝔣[(1 : (Ideal (𝓞 K))⁰)] = 1 := by
  rw [map_one, Units.val_one]

/-- The inverse of the lattice bijection takes $-a + b$ to the difference of the images. -/
theorem symm_globalLatticeEquiv_neg_add (J : (Ideal (𝓞 K))⁰)
    (a b : traceLattice K (FractionalIdeal.mk0 K J)) :
    ((𝔢[J].symm (-a + b) : _) : K) = (𝔢[J].symm b : K) - (𝔢[J].symm a : K) := by
  have h := symm_globalLatticeEquiv_add J a (-a + b)
  rw [add_neg_cancel_left] at h
  rw [h]
  ring

omit [NumberField K] in
/-- A fractional ideal contains the difference of two of its elements. -/
theorem sub_mem_fi {I : FractionalIdeal (𝓞 K)⁰ K} {a b : K} (ha : a ∈ I) (hb : b ∈ I) :
    a - b ∈ I :=
  FractionalIdeal.mem_coe.1 (Submodule.sub_mem _ (FractionalIdeal.mem_coe.2 ha)
    (FractionalIdeal.mem_coe.2 hb))

omit [NumberField K] in
/-- A fractional ideal contains the negative of each of its elements. -/
theorem neg_mem_fi {I : FractionalIdeal (𝓞 K)⁰ K} {a : K} (ha : a ∈ I) : -a ∈ I :=
  FractionalIdeal.mem_coe.1 (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ha))

/-- Orthogonality on $J / \mathfrak{f} J$. For $\gamma \in (\mathfrak{f} J)^\vee$, the sum of $e(\gamma \xi)$ over the classes $\xi$ is $N(\mathfrak{f})$ if $\gamma \in J^\vee$, and $0$ if not. -/
theorem sum_traceExp_eq (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) {γ : K}
    (hγ : γ ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) :
    ∑ q : 𝔔[χ, J], traceExp K (γ * (𝔢[J].symm q.out : K)) =
      if γ ∈ FractionalIdeal.dual ℤ ℚ 𝔣[J] then (Ideal.absNorm χ.conductor : ℂ) else 0 := by
  split_ifs with h
  · have h1 : ∀ q : 𝔔[χ, J], traceExp K (γ * (𝔢[J].symm q.out : K)) = 1 := fun q => by
      obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual (Units.ne_zero _)).1 h _ (𝔢[J].symm q.out).2
      rw [Algebra.traceForm_apply, eq_intCast] at hn
      exact (traceExp_eq_one_iff _).2 ⟨n, hn.symm⟩
    rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, natCard_rayQuotient, nsmul_eq_mul, mul_one]
  · rw [FractionalIdeal.mem_dual (Units.ne_zero _)] at h
    push Not at h
    obtain ⟨a, ha, hna⟩ := h
    refine sum_out_eq_zero_of_ne_one _ (fun ℓ => traceExp K (γ * (𝔢[J].symm ℓ : K)))
      (fun ℓ h hh => cexp_trace_add J hγ ℓ h hh) (fun a b => ?_) (g₀ := 𝔢[J] ⟨a, ha⟩) ?_
    · rw [symm_globalLatticeEquiv_add, mul_add, traceExp_add]
    · simp only [Equiv.symm_apply_apply]
      intro h1
      obtain ⟨n, hn⟩ := (traceExp_eq_one_iff _).1 h1
      exact hna ⟨n, by rw [Algebra.traceForm_apply, hn, eq_intCast]⟩

/-- For $\beta \in (\mathfrak{f} J)^\vee$ and $\nu \in \mathcal{O}_K$, $G_J(\nu \beta) = \overline{c(\nu)} G_J(\beta)$, where $c$ is `rayCoeff` for the unit ideal. If $\nu$ is in a ramified prime, both sides are zero. -/
theorem IsRayClassType.rayGaussCoeff_mul_eq (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) {ν : K}
    (hν : ν ∈ 𝔣[(1 : (Ideal (𝓞 K))⁰)]) :
    rayGaussCoeff χ J (ν * β) =
      starRingEnd ℂ (rayCoeff χ (FractionalIdeal.mk0 K 1) ν) * rayGaussCoeff χ J β := by
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hν
  obtain ⟨u, -, rfl⟩ := hν
  rw [show algebraMap (𝓞 K) K u = (u : K) from rfl]
  have hcnt1 : ∀ v, FractionalIdeal.count K v 𝔣[(1 : (Ideal (𝓞 K))⁰)] = 0 := fun v => by
    rw [coe_mk0_one, FractionalIdeal.count_one]
  rw [rayCoeff]
  split_ifs with h
  · have hcount : ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
      fun v hv => (h.2 v hv).trans (hcnt1 v)
    have ht := hχ.rayGaussCoeff_eq_mul hS J h.1 hcount hβ
    have hc : starRingEnd ℂ (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) h.1)) : ℂ) *
        (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) h.1)) : ℂ) = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_idealChar, one_pow,
        Complex.ofReal_one]
    have h1 : idealChar χ (FractionalIdeal.mk0 K 1) = 1 := by rw [map_one, map_one]
    rw [h1, inv_one, mul_one, ht, ← mul_assoc, hc, one_mul]
  · rw [map_zero, zero_mul]
    have hv : ∃ v ∈ ramifiedSet χ, u ∈ v.asIdeal := by
      by_cases hu0 : (u : K) = 0
      · obtain ⟨v, hv⟩ := hS
        refine ⟨v, hv, ?_⟩
        rw [show u = 0 from by exact_mod_cast hu0]
        exact zero_mem _
      · push Not at h
        obtain ⟨v, hv, hne⟩ := h hu0
        refine ⟨v, hv, ?_⟩
        by_contra hn
        exact hne ((count_spanSingleton_eq_zero_of_notMem hu0 hn).trans (hcnt1 v).symm)
    obtain ⟨v, hv, hu⟩ := hv
    exact hχ.rayGaussCoeff_eq_zero_of_mem J hv
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨u, hu, rfl⟩) hβ)

/-- If $(\beta, I)$ is a pair for $J$ and $\zeta \in J$, then $\beta \zeta \in \mathcal{O}_K^\vee$ if and only if $\zeta \in \mathfrak{f} J$. -/
theorem IsRayGaussPair.mul_mem_dual_one_iff {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) {ζ : K} (hζ : ζ ∈ 𝔣[J]) :
    β * ζ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ζ ∈ 𝔣[conductorNZ χ * J] := by
  have hF0 : 𝔣[conductorNZ χ * J] ≠ 0 := Units.ne_zero _
  have hD0 : FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ hF0
  have hI1 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
    FractionalIdeal.coeIdeal_le_one
  have h2 : (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ ≤
      𝔣[conductorNZ χ * J] := by
    rw [coe_mk0_conductorNZ_mul]
    exact mul_le_mul_right ((FractionalIdeal.spanSingleton_le_iff_mem).2 hζ) _
  have h3 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ =
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ +
        (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ := by
    rw [← add_mul, ← FractionalIdeal.coeIdeal_sup, h.2, FractionalIdeal.coeIdeal_top, one_mul]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.spanSingleton_le_iff_mem,
    map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰) β ζ, spanSingleton_eq_coeIdeal_mul_dual J h.1,
    ← FractionalIdeal.dual_mul_self ℤ ℚ hF0]
  constructor
  · intro hle
    have h1 := mul_le_mul_right hle (FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J])⁻¹
    rw [mul_comm ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K), mul_assoc, ← mul_assoc _⁻¹,
      ← mul_assoc _⁻¹, inv_mul_cancel₀ hD0, one_mul, one_mul] at h1
    rw [h3, ← FractionalIdeal.sup_eq_add]
    exact sup_le h1 h2
  · intro hle
    rw [mul_assoc]
    exact (mul_le_of_le_one_left' hI1).trans (mul_le_mul_right hle _)

/-- If $\beta \in (\mathfrak{f} J)^\vee$ and $\zeta \in J$, then $\beta \zeta \in \mathfrak{f}^\vee$. -/
theorem mul_mem_dual_conductor {J : (Ideal (𝓞 K))⁰} {β ζ : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) (hζ : ζ ∈ 𝔣[J]) :
    β * ζ ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * 1] := by
  have h := mul_dual_mul_le (I := 𝔣[J]) (J := (χ.conductor : FractionalIdeal (𝓞 K)⁰ K))
    (Units.ne_zero _) (coeIdeal_conductor_ne_zero χ)
  rw [mul_comm 𝔣[J] (χ.conductor : FractionalIdeal (𝓞 K)⁰ K), ← coe_mk0_conductorNZ_mul] at h
  rw [coe_mk0_conductorNZ_mul, coe_mk0_one, mul_one, mul_comm β ζ]
  exact h (FractionalIdeal.mul_mem_mul hζ hβ)

/-- The product $G_J(\beta) \overline{G_1(\beta \xi)}$ as a double sum over $J / \mathfrak{f} J$ and $\mathcal{O}_K / \mathfrak{f}$. -/
theorem IsRayClassType.rayGaussCoeff_mul_conj_eq_sum (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) (ξ : K) :
    rayGaussCoeff χ J β * starRingEnd ℂ (rayGaussCoeff χ 1 (β * ξ)) =
      ∑ x : 𝔔[χ, J], rayLatticeCoeff χ J x.out * ∑ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)],
        traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) := by
  rw [rayGaussCoeff_eq_sum χ 1, map_sum, Finset.mul_sum]
  have h1 : ∀ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)], rayGaussCoeff χ J β *
      starRingEnd ℂ (rayLatticeCoeff χ 1 n.out * traceExp K (β * ξ * (𝔢[1].symm n.out : K))) =
      ∑ x : 𝔔[χ, J], rayLatticeCoeff χ J x.out *
        traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) := fun n => by
    rw [map_mul, conj_traceExp, ← mul_assoc, mul_comm (rayGaussCoeff χ J β),
      show rayLatticeCoeff χ 1 n.out =
        rayCoeff χ (FractionalIdeal.mk0 K 1) (𝔢[1].symm n.out : K) from rfl,
      ← hχ.rayGaussCoeff_mul_eq hS J hβ (𝔢[1].symm n.out).2, rayGaussCoeff_eq_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, ← traceExp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun n _ => h1 n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- If $(\beta, I)$ is a pair for $J$ and $\xi \in J$, then $\beta (x - \xi) \in \mathcal{O}_K^\vee$ if and only if the class $x$ is the class of $\xi$. -/
theorem IsRayGaussPair.mul_sub_mem_dual_iff {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) {ξ : K} (hξ : ξ ∈ 𝔣[J]) (x : 𝔔[χ, J]) :
    β * ((𝔢[J].symm x.out : K) - ξ) ∈ FractionalIdeal.dual ℤ ℚ 𝔣[(1 : (Ideal (𝓞 K))⁰)] ↔
      x = QuotientAddGroup.mk (𝔢[J] ⟨ξ, hξ⟩) := by
  rw [coe_mk0_one, h.mul_mem_dual_one_iff (sub_mem_fi (𝔢[J].symm x.out).2 hξ)]
  constructor
  · intro hm
    rw [← QuotientAddGroup.out_eq' x, QuotientAddGroup.eq, mem_subLattice_rayLattice_iff,
      symm_globalLatticeEquiv_neg_add, Equiv.symm_apply_apply, ← neg_sub]
    exact neg_mem_fi hm
  · intro hx
    have hm := QuotientAddGroup.eq.1 ((QuotientAddGroup.out_eq' x).trans hx)
    rw [mem_subLattice_rayLattice_iff, symm_globalLatticeEquiv_neg_add,
      Equiv.symm_apply_apply, ← neg_sub] at hm
    rw [← neg_neg ((𝔢[J].symm x.out : K) - ξ)]
    exact neg_mem_fi hm

/-- If $(\beta, I)$ is a pair for $J$ and $\xi \in J$, then $N(\mathfrak{f}) c_J(\xi) = G_J(\beta) \overline{G_1(\beta \xi)}$. -/
theorem IsRayClassType.mul_rayCoeff_eq (hχ : IsRayClassType χ) (hS : (ramifiedSet χ).Nonempty)
    {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) {ξ : K}
    (hξ : ξ ∈ 𝔣[J]) :
    (Ideal.absNorm χ.conductor : ℂ) * rayCoeff χ (FractionalIdeal.mk0 K J) ξ =
      rayGaussCoeff χ J β * starRingEnd ℂ (rayGaussCoeff χ 1 (β * ξ)) := by
  have hβ := h.mem_dual
  have step2 : ∀ x : 𝔔[χ, J], rayLatticeCoeff χ J x.out * ∑ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)],
      traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) =
        if x = QuotientAddGroup.mk (𝔢[J] ⟨ξ, hξ⟩) then
          rayLatticeCoeff χ J x.out * (Ideal.absNorm χ.conductor : ℂ) else 0 := fun x => by
    rw [sum_traceExp_eq χ 1 (mul_mem_dual_conductor hβ (sub_mem_fi (𝔢[J].symm x.out).2 hξ)),
      ← mul_ite_zero]
    congr 1
    exact if_congr (h.mul_sub_mem_dual_iff hξ x) rfl rfl
  rw [hχ.rayGaussCoeff_mul_conj_eq_sum hS J hβ ξ, Finset.sum_congr rfl fun x _ => step2 x,
    Fintype.sum_eq_single _ fun x hx => ite_eq_right hx, ite_eq_left rfl, mul_comm,
    out_mk_eq _ (rayLatticeCoeff χ J)
      (fun g h hh => hχ.rayLatticeCoeff_add hS J g ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩)]
  rw [rayLatticeCoeff, Equiv.symm_apply_apply]

/-- The coefficient `rayCoeff` of the unit ideal at $1$ is $1$. -/
theorem rayCoeff_one_one : rayCoeff χ (FractionalIdeal.mk0 K 1) 1 = 1 := by
  have hc : (1 : K) ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K)) =
        FractionalIdeal.count K v 𝔣[(1 : (Ideal (𝓞 K))⁰)] :=
    ⟨one_ne_zero, fun v _ => by rw [map_one, coe_mk0_one]⟩
  rw [rayCoeff, dite_eq_left hc, show Units.mk0 (1 : K) hc.1 = 1 from Units.ext rfl, map_one,
    map_one, map_one (FractionalIdeal.mk0 K), map_one, inv_one, mul_one, Units.val_one]

/-- If $(\beta, I)$ is a pair for the unit ideal, then $G_1(\beta) \overline{G_1(\beta)} = N(\mathfrak{f})$. -/
theorem IsRayClassType.rayGaussCoeff_mul_conj (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ 1 β I) :
    rayGaussCoeff χ 1 β * starRingEnd ℂ (rayGaussCoeff χ 1 β) = Ideal.absNorm χ.conductor := by
  have h1 := hχ.mul_rayCoeff_eq hS h (ξ := 1)
    (by rw [coe_mk0_one]; exact FractionalIdeal.one_mem_one _)
  rw [rayCoeff_one_one, mul_one, mul_one] at h1
  exact h1.symm

/-- There are $t \in K$ and a nonzero integral ideal $T$ with $(t) = T J$ and $T + \mathfrak{f} = \mathcal{O}_K$. -/
theorem exists_spanSingleton_eq_coeIdeal_mul (hS : (ramifiedSet χ).Nonempty)
    (J : (Ideal (𝓞 K))⁰) :
    ∃ (t : K) (T : (Ideal (𝓞 K))⁰), FractionalIdeal.spanSingleton (𝓞 K)⁰ t =
      ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J] ∧
        (T : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤ := by
  have hD0 : 𝔣[J] ≠ 0 := Units.ne_zero _
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J]) (b := 1) (c := 𝔣[J])
    (mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one)
    (mul_ne_zero (coeIdeal_conductor_ne_zero χ) hD0) one_ne_zero
  rw [mul_one] at hx
  have hxD : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ 𝔣[J] := by
    rw [← hx, ← FractionalIdeal.sup_eq_add]
    exact le_sup_right
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * 𝔣[J]⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hD0]
    exact mul_le_mul_left hxD _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hID : (I : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J] = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
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
  exact ⟨x, ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, hID.symm, htop⟩

/-- If $(t) = T J$ and $T + \mathfrak{f} = \mathcal{O}_K$, then $c_J(t) = \chi(T)$. -/
theorem rayCoeff_eq_of_spanSingleton_eq {J : (Ideal (𝓞 K))⁰} {t : K} {T : (Ideal (𝓞 K))⁰}
    (hT : FractionalIdeal.spanSingleton (𝓞 K)⁰ t =
      ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J])
    (hTf : (T : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤) :
    rayCoeff χ (FractionalIdeal.mk0 K J) t = idealChar χ (FractionalIdeal.mk0 K T) := by
  have hT0 : ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero (FractionalIdeal.mk0 K T)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hT
    exact mul_ne_zero hT0 (Units.ne_zero _) hT.symm
  have hu : toPrincipalIdeal (𝓞 K) K (Units.mk0 t ht0) =
      FractionalIdeal.mk0 K T * FractionalIdeal.mk0 K J := Units.ext (by
    rw [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact hT)
  have hc : t ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ t) =
        FractionalIdeal.count K v 𝔣[J] := ⟨ht0, fun v hv => by
    rw [hT, FractionalIdeal.count_mul K v hT0 (Units.ne_zero _),
      count_eq_zero_of_sup_conductor_eq_top hTf hv, zero_add]⟩
  rw [rayCoeff, dite_eq_left hc, hu, map_mul, mul_inv_cancel_right]

/-- The identity $\tau_1(\chi) \overline{\tau_1(\chi)} = N(\mathfrak{f})$. -/
theorem IsRayClassType.rayGaussSum_mul_conj_one (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) :
    rayGaussSum χ 1 * starRingEnd ℂ (rayGaussSum χ 1) = Ideal.absNorm χ.conductor := by
  obtain ⟨β, I, h⟩ := exists_isRayGaussPair hS (1 : (Ideal (𝓞 K))⁰)
  have hc : (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) *
      starRingEnd ℂ (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_idealChar, one_pow,
      Complex.ofReal_one]
  rw [hχ.rayGaussSum_eq hS h, map_mul, ← hχ.rayGaussCoeff_mul_conj hS h]
  linear_combination (rayGaussCoeff χ 1 β * starRingEnd ℂ (rayGaussCoeff χ 1 β)) * hc

/-- The Gauss sum $\tau_J(\chi)$ does not depend on $J$: it is equal to $\tau_1(\chi)$. -/
theorem IsRayClassType.rayGaussSum_eq_rayGaussSum_one (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    rayGaussSum χ J = rayGaussSum χ 1 := by
  obtain ⟨β, I, h⟩ := exists_isRayGaussPair hS J
  obtain ⟨t, T, hT, hTf⟩ := exists_spanSingleton_eq_coeIdeal_mul (χ := χ) hS J
  have ht : t ∈ 𝔣[J] := (FractionalIdeal.spanSingleton_le_iff_mem).1
    (hT ▸ mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one)
  have h' : IsRayGaussPair χ 1 (β * t) (I * T) := by
    refine ⟨?_, ?_⟩
    · rw [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul, h.1,
        map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰) β t, hT, coe_mk0_conductorNZ_mul,
        coe_mk0_conductorNZ_mul, coe_mk0_one]
      ring
    · rw [Submonoid.coe_mul, ← Ideal.isCoprime_iff_sup_eq]
      exact (Ideal.isCoprime_iff_sup_eq.2 h.2).mul_left (Ideal.isCoprime_iff_sup_eq.2 hTf)
  have hstar := hχ.mul_rayCoeff_eq hS h ht
  rw [rayCoeff_eq_of_spanSingleton_eq hT hTf] at hstar
  have hnorm := hχ.rayGaussCoeff_mul_conj hS h'
  have hN : (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0)
  have hb : starRingEnd ℂ (rayGaussCoeff χ 1 (β * t)) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hnorm
    exact hN hnorm.symm
  have ha : rayGaussCoeff χ J β = rayGaussCoeff χ 1 (β * t) *
      (idealChar χ (FractionalIdeal.mk0 K T) : ℂ) := by
    refine mul_right_cancel₀ hb ?_
    rw [← hstar]
    linear_combination (idealChar χ (FractionalIdeal.mk0 K T) : ℂ) * hnorm.symm
  have hm : FractionalIdeal.mk0 K (I * T) = FractionalIdeal.mk0 K I * FractionalIdeal.mk0 K T :=
    map_mul _ _ _
  rw [hχ.rayGaussSum_eq hS h, hχ.rayGaussSum_eq hS h', hm, map_mul, Units.val_mul, ha]
  ring

/-- The identity $\tau_J(\chi) \overline{\tau_J(\chi)} = N(\mathfrak{f})$. -/
theorem IsRayClassType.rayGaussSum_mul_conj (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    rayGaussSum χ J * starRingEnd ℂ (rayGaussSum χ J) = Ideal.absNorm χ.conductor := by
  rw [hχ.rayGaussSum_eq_rayGaussSum_one hS J]
  exact hχ.rayGaussSum_mul_conj_one hS

/-- The identity $|\tau_J(\chi)|^2 = N(\mathfrak{f})$. -/
theorem IsRayClassType.norm_rayGaussSum_sq (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    ‖rayGaussSum χ J‖ ^ 2 = Ideal.absNorm χ.conductor := by
  have h := hχ.rayGaussSum_mul_conj hS J
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

end Langlands.Tate
