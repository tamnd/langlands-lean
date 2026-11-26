/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassHeckeWeightFE
import Langlands.Tate.RayClassGaussNorm

/-!
# The Gauss sum of the periodic coefficient of a Hecke character

Let $\chi$ be a Hecke character of a number field $K$, with conductor $\mathfrak{f}$, and suppose that $\chi$ is ramified at one place at least. The character $\chi$ need not be of ray class type. Let $J$ be a nonzero integral ideal and let $c_J$ be the periodic coefficient `Langlands.Tate.periodicCoeff`, that is $c_J(\alpha) = c^{\mathrm{ray}}_J(\alpha) \chi_\infty(\alpha)$. This file redoes the chain of the ray class Gauss sum for $c_J$. The character $x \mapsto \chi((x))$ of the ray class case is replaced by $x \mapsto \chi_{\mathrm{id}}((x)) \chi_\infty(x)$. We prove the vanishing of the Gauss sum $G_J(\beta)$, the evaluation $G_J(\beta) = \tau_J(\chi) \overline{c_D(\beta)}$, and $|\tau_J(\chi)|^2 = N(\mathfrak{f})$.

## Main definitions

* `Langlands.Tate.periodicChar`: the character $x \mapsto \chi_{\mathrm{id}}((x)) \chi_\infty(x)$ of $K^\times$.
* `Langlands.Tate.periodicLatticeCoeff`: the coefficient $c_J$ as a function on the lattice $\varphi(J)$.
* `Langlands.Tate.periodicGaussCoeff`: the Gauss sum $G_J(\beta)$ of $c_J$ over $J / \mathfrak{f} J$.
* `Langlands.Tate.gaussDual`: the fractional ideal $D = (\mathfrak{f} J)^\vee$ as a unit.
* `Langlands.Tate.periodicGaussSum`: the Gauss sum $\tau_J(\chi) = G_J(\beta) c_D(\beta)$ for a chosen pair $(\beta, I)$.

## Main results

* `periodicChar_mul_prod_finiteComponent`: reciprocity, $\chi_{\mathrm{id}}((x)) \chi_\infty(x) \prod_{v \in R} \chi_v(x) = 1$ if $x$ is a unit at each ramified place $v$.
* `exists_periodicChar_ne_one_of_mem`: for a ramified place $v_0$ there is $u \in \mathcal{O}_K$ with $u \equiv 1$ modulo $\mathfrak{f} v_0^{-1}$, a unit at each ramified place, with $\chi_{\mathrm{id}}((u)) \chi_\infty(u) \neq 1$.
* `periodicCoeff_coe_mul`: $c_J(u \xi) = \chi_{\mathrm{id}}((u)) \chi_\infty(u) c_J(\xi)$ if $u$ is a unit at each ramified place.
* `sum_periodicLatticeCoeff_eq_zero`: the sum of $c_J$ over $J / \mathfrak{f} J$ is zero.
* `periodicGaussCoeff_eq_mul`: $G_J(\beta) = \chi_{\mathrm{id}}((u)) \chi_\infty(u) G_J(u \beta)$.
* `periodicGaussCoeff_eq_zero`: the vanishing, $G_J(\beta) = 0$ if $(\beta) \mathfrak{f} J \mathfrak{d}$ is integral and not prime to $\mathfrak{f}$.
* `periodicGaussCoeff_mul_periodicCoeff_eq`: $G_J(\beta) c_D(\beta)$ does not depend on the pair $(\beta, I)$.
* `periodicGaussSum_eq`: $\tau_J(\chi) = G_J(\beta) c_D(\beta)$ for each pair $(\beta, I)$.
* `periodicGaussCoeff_eq_periodicGaussSum_mul`: the evaluation, $G_J(\beta) = \tau_J(\chi) \overline{c_D(\beta)}$ for each $\beta \in D$, if $\chi$ is unitary.
* `mul_periodicCoeff_eq`: the inversion formula, $N(\mathfrak{f}) c_J(\xi) = G_J(\beta) \overline{G_1(\beta \xi)}$, if $\chi$ is unitary.
* `periodicGaussCoeff_mul_conj`: $G_1(\beta) \overline{G_1(\beta)} = N(\mathfrak{f})$, if $\chi$ is unitary.
* `IsRayGaussPair.periodicGaussCoeff_eq_mul_one`: $G_J(\beta) = G_1(\beta t) c_J(t)$ if $(t) = T J$ and $T + \mathfrak{f} = \mathcal{O}_K$.
* `norm_periodicGaussSum_sq`: the norm, $|\tau_J(\chi)|^2 = N(\mathfrak{f})$, if $\chi$ is unitary.

## Proofs

The proofs follow the files `Langlands.Tate.RayClassGauss`, `Langlands.Tate.RayClassGaussVanish`, `Langlands.Tate.RayClassGaussEval` and `Langlands.Tate.RayClassGaussNorm`. The ray class proofs use the condition `Langlands.Tate.IsRayClassType` only through the value $\chi((u))$ for $u \equiv 1$ modulo $\mathfrak{f} v_0^{-1}$. Here the reciprocity law `Langlands.Tate.ideleChar_eq_infinitePart_mul_prod` gives the same relation for $\chi_{\mathrm{id}}((u)) \chi_\infty(u)$, with no condition at the infinite places. The vanishing and the relation between two pairs need no other change. The evaluation, the inversion formula and the norm use $|\chi_{\mathrm{id}}((u)) \chi_\infty(u)| = 1$ and $\overline{z} z = 1$ for $|z| = 1$. For this reason these results have the hypothesis that $\chi$ is unitary, that is $|\chi(x)| = 1$ for each idele $x$.

## Open parts

The results on the conjugate, the inversion formula and the norm need the hypothesis that $\chi$ is unitary. A general Hecke character is $|\cdot|^{s} \chi_0$ with $\chi_0$ unitary, and the reduction to the unitary case is not done here. The identity $\tau_J(\chi) = \tau_1(\chi)$ is not proved here. The assembly into `Langlands.HeckeFunctionalEquationAt` for a character with a nonzero weight at the infinite places is still open.

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

section Local

/-- The character $x \mapsto \chi_{\mathrm{id}}((x)) \chi_\infty(x)$ of $K^\times$. It replaces $x \mapsto \chi((x))$ of a character of ray class type. -/
noncomputable def periodicChar (χ : HeckeCharacter K) : Kˣ →* ℂˣ :=
  (idealChar χ).comp (toPrincipalIdeal (𝓞 K) K) * infChar χ

/-- The value of `periodicChar χ` at $x$ is $\chi_{\mathrm{id}}((x)) \chi_\infty(x)$. -/
theorem periodicChar_apply (x : Kˣ) :
    periodicChar χ x = idealChar χ (toPrincipalIdeal (𝓞 K) K x) * infChar χ x := rfl

/-- **Reciprocity and the local components.** Let $R$ be the ramified set of $\chi$. If $x \in K^\times$ is a unit at each $v \in R$, then $\chi_{\mathrm{id}}((x)) \chi_\infty(x) \prod_{v \in R} \chi_v(x) = 1$. There is no condition on $\chi$ at the infinite places. -/
theorem periodicChar_mul_prod_finiteComponent (x : Kˣ)
    (hx : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0) :
    periodicChar χ x * ∏ v ∈ ramifiedSet χ,
      χ.finiteComponent v (ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x)) = 1 := by
  have hfin := Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = WithZero.exp
          (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) :=
    fun v => by rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count]
  set S := hfin.toFinset ∪ ramifiedSet χ with hSdef
  have hS : ∀ v ∉ S,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    rw [hval, show FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0
      by simpa using fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h)),
      neg_zero, WithZero.exp_zero]
  have hR : ∀ v ∉ S, χ.IsUnramifiedAt v := fun v hv =>
    not_not.1 fun h => hv (Finset.mem_union_right _ (mem_ramifiedSet.2 h))
  have h := ideleChar_eq_infinitePart_mul_prod χ _ S hS hR
  rw [ideleChar_unitEmbedding, ← infChar_apply] at h
  rw [periodicChar_apply, idealChar_apply, coe_toPrincipalIdeal,
    finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · have hRS : S ∩ ramifiedSet χ = ramifiedSet χ :=
      Finset.inter_eq_right.2 Finset.subset_union_right
    rw [h, mul_right_comm, mul_comm _ (infChar χ x)]
    congr 1
    rw [← hRS, ← Finset.prod_ite_mem, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v ∈ ramifiedSet χ
    · rw [hx v hv, zpow_zero, one_mul, ite_eq_left hv]
    · rw [ite_eq_right hv, mul_one, finiteComponent_eq_zpow_of_isUnramifiedAt
        (not_not.1 (mt mem_ramifiedSet.2 hv)), hval, WithZero.log_exp, neg_neg]
  · intro v hv
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl fun h0 => hv (by simp only [h0, zpow_zero])

/-- **An integer with a prescribed local component.** Let $v_0$ be a ramified place and let $y \in \mathcal{O}_{v_0}^\times$. There is a nonzero $u \in \mathcal{O}_K$ with $v_0(u - y) \geq a_{v_0}$ and $w(u - 1) \geq a_w$ for the other ramified places $w$. Such a $u$ is a unit at each ramified place, and $\chi_{\mathrm{id}}((u)) \chi_\infty(u) = \chi_{v_0}(y)^{-1}$. -/
theorem exists_integer_periodicChar {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ ramifiedSet χ)
    (y : (v₀.adicCompletion K)ˣ) (hy : Valued.v (y : v₀.adicCompletion K) = 1) :
    ∃ (u : 𝓞 K) (hu : (u : K) ≠ 0),
      Valued.v (algebraMap K (v₀.adicCompletion K) (u : K) - y) ≤
        WithZero.exp (-(χ.conductorExponent v₀ : ℤ)) ∧
      (∀ w ∈ ramifiedSet χ, w ≠ v₀ →
        w.valuation K ((u : K) - 1) ≤ WithZero.exp (-(χ.conductorExponent w : ℤ))) ∧
      (∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) ∧
      periodicChar χ (Units.mk0 (u : K) hu) = (χ.finiteComponent v₀ y)⁻¹ := by
  obtain ⟨u, hu1, hu2⟩ := exists_integer_approx (ramifiedSet χ) χ.conductorExponent hv₀
    (y : v₀.adicCompletion K) hy.le
  have ha₀ := conductorExponent_ne_zero_of_mem hv₀
  have hv₀u : v₀.valuation K (u : K) = 1 := by
    have hlt : Valued.v (algebraMap K (v₀.adicCompletion K) (u : K) - y) <
        Valued.v (y : v₀.adicCompletion K) :=
      hu1.trans_lt (by rw [hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have := Valuation.map_add_eq_of_lt_left Valued.v hlt
    rwa [add_sub_cancel, hy, valued_algebraMap] at this
  have hu0 : (u : K) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv₀u
    exact zero_ne_one hv₀u
  have hval : ∀ v ∈ ramifiedSet χ, v.valuation K (u : K) = 1 := fun v hv => by
    by_cases hv' : v = v₀
    · rw [hv']
      exact hv₀u
    · exact valuation_eq_one_of_sub_one_le v (conductorExponent_ne_zero_of_mem hv) (hu2 v hv hv')
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
    fun v hv => count_eq_zero_of_valuation_eq_one v (Units.mk0 _ hu0) (hval v hv)
  refine ⟨u, hu0, hu1, hu2, hcount, ?_⟩
  have h := periodicChar_mul_prod_finiteComponent (χ := χ) (Units.mk0 _ hu0) hcount
  rw [Finset.prod_eq_single v₀ (fun w hw hne => ?_) (fun h => absurd hv₀ h)] at h
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← h]
    congr 1
    exact (finiteComponent_eq_of_valued_sub_le χ ha₀ hy (by
      rw [ideleFin_unitEmbedding, Units.val_mk0]
      exact hu1)).symm
  · rw [finiteComponent_eq_of_valued_sub_le χ (conductorExponent_ne_zero_of_mem hw)
      (y := 1) (by simp) (by
        rw [ideleFin_unitEmbedding, Units.val_mk0, Units.val_one, ← map_one (algebraMap K _),
          ← map_sub, valued_algebraMap]
        exact hu2 w hw hne), map_one]

/-- **An integer congruent to $1$ modulo $\mathfrak{f} \mathfrak{p}^{-1}$ with a nontrivial character value.** Let $v_0$ be a ramified place, with prime ideal $\mathfrak{p}$. There is a nonzero $u \in \mathcal{O}_K$ that is a unit at each ramified place, with $(u - 1) \mathfrak{p} \subseteq \mathfrak{f}$ and $\chi_{\mathrm{id}}((u)) \chi_\infty(u) \neq 1$. -/
theorem exists_periodicChar_ne_one_of_mem {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∈ ramifiedSet χ) :
    ∃ (u : 𝓞 K) (hu : (u : K) ≠ 0),
      (∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) ∧
      Ideal.span {u - 1} * v₀.asIdeal ≤ χ.conductor ∧
      periodicChar χ (Units.mk0 (u : K) hu) ≠ 1 := by
  have ha₀ := conductorExponent_ne_zero_of_mem hv₀
  have hnt : ¬ χ.IsTrivialOnHigherUnits v₀ (χ.conductorExponent v₀ - 1) :=
    Nat.notMem_of_lt_sInf (Nat.sub_lt (Nat.pos_of_ne_zero ha₀) one_pos)
  simp only [HeckeCharacter.IsTrivialOnHigherUnits, not_forall] at hnt
  obtain ⟨y, hy, hy1, hχy⟩ := hnt
  obtain ⟨u, hu0, hu1, hu2, hcount, he⟩ := exists_integer_periodicChar hv₀ y hy
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

end Local

section Coefficient

/-- **The periodic coefficient under a multiplication.** If $u \in \mathcal{O}_K$ is a unit at each ramified place, then $c_J(u \xi) = \chi_{\mathrm{id}}((u)) \chi_\infty(u) c_J(\xi)$. -/
theorem periodicCoeff_coe_mul {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ξ : K) :
    periodicCoeff χ J ((u : K) * ξ) = (periodicChar χ (Units.mk0 (u : K) hu0) : ℂ) *
      periodicCoeff χ J ξ := by
  by_cases hξ : ξ = 0
  · rw [hξ, mul_zero, periodicCoeff, dite_eq_right (fun h => h rfl), mul_zero]
  · have huξ : (u : K) * ξ ≠ 0 := mul_ne_zero hu0 hξ
    rw [periodicCoeff, periodicCoeff, dite_eq_left huξ, dite_eq_left hξ, rayCoeff_coe_mul hu0 hu,
      show Units.mk0 ((u : K) * ξ) huξ = Units.mk0 (u : K) hu0 * Units.mk0 ξ hξ from Units.ext rfl,
      map_mul, periodicChar_apply]
    push_cast
    ring

/-- The periodic coefficient `Langlands.Tate.periodicCoeff` as a function on the lattice $\varphi(J)$. -/
noncomputable def periodicLatticeCoeff (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) : ℂ :=
  periodicCoeff χ (FractionalIdeal.mk0 K J)
    ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K)

/-- The periodic coefficient on the lattice $\varphi(J)$ is periodic modulo $\varphi(\mathfrak{f} J)$, if $\chi$ is ramified at one place. -/
theorem periodicLatticeCoeff_add (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) (μ : rayLattice χ J) :
    periodicLatticeCoeff χ J (ℓ + ⟨μ, rayLattice_le χ J μ.2⟩) = periodicLatticeCoeff χ J ℓ := by
  obtain ⟨γ, hγ, hμ⟩ := (mem_globalLattice K _ _).1 μ.2
  set e := globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J) with he
  have hγ' := mem_of_mem_conductor_mul J hγ
  have hs : e.symm (ℓ + ⟨μ, rayLattice_le χ J μ.2⟩) = ⟨((e.symm ℓ : _) : K) + γ,
      add_mem (e.symm ℓ).2 hγ'⟩ := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [he, coe_globalLatticeEquiv, map_add, hμ]
    change (ℓ : euclidean.mixedSpace K) + μ = _ + μ
    congr 1
    rw [← coe_globalLatticeEquiv, ← he]
    congr 1
    exact (e.apply_symm_apply ℓ).symm
  rw [periodicLatticeCoeff, periodicLatticeCoeff, ← he, hs]
  refine periodicCoeff_eq_of_sub_mem hS _ ?_
  rw [add_sub_cancel_left]
  exact mem_conductor_mul_of_mem J hγ

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, then $c_J(u \ell) = \chi_{\mathrm{id}}((u)) \chi_\infty(u) c_J(\ell)$ on the lattice $\varphi(J)$. -/
theorem periodicLatticeCoeff_rayMulMap {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (Ideal (𝓞 K))⁰) (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    periodicLatticeCoeff χ J (rayMulMap J u ℓ) =
      (periodicChar χ (Units.mk0 (u : K) hu0) : ℂ) * periodicLatticeCoeff χ J ℓ := by
  rw [periodicLatticeCoeff, periodicLatticeCoeff, coe_symm_rayMulMap]
  exact periodicCoeff_coe_mul hu0 hu _ _

/-- **The periodic coefficients have sum $0$.** Let $\chi$ be ramified at one place. Then $\sum_{x \in J / \mathfrak{f} J} c_J(x) = 0$. There is no condition on $\chi$ at the infinite places. -/
theorem sum_periodicLatticeCoeff_eq_zero (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        periodicLatticeCoeff χ J q.out = 0 := by
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨u, hu0, hcount, -, hne⟩ := exists_periodicChar_ne_one_of_mem hv₀
  exact sum_out_eq_zero_of_map _ (periodicLatticeCoeff χ J)
    (fun g h hh => periodicLatticeCoeff_add ⟨v₀, hv₀⟩ J g
      ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩)
    (rayMulMap J u) (subLattice_le_comap_rayMulMap J u) (comap_rayMulMap_le hu0 hcount J)
    (z := (periodicChar χ (Units.mk0 (u : K) hu0) : ℂ))
    (fun h => hne (Units.ext h)) (periodicLatticeCoeff_rayMulMap hu0 hcount J)

end Coefficient

section Gauss

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

/-- **The periodic Gauss sum.** For $\beta \in K$, $$G_J(\beta) = \sum_{x \in J / \mathfrak{f} J} c_J(\xi_x) e^{2 \pi i \mathrm{Tr}(\beta \xi_x)},$$ where $c_J$ is the periodic coefficient `Langlands.Tate.periodicCoeff` and $\xi_x \in J$ is the representative of the class $x$. -/
noncomputable def periodicGaussCoeff (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) : ℂ :=
  ∑ q : 𝔔[χ, J], periodicLatticeCoeff χ J q.out * traceExp K (β * (𝔢[J].symm q.out : K))

/-- **The periodic Gauss sum under a twist.** Let $\chi$ be ramified at one place, let $\beta \in (\mathfrak{f} J)^\vee$, and let $u \in \mathcal{O}_K$ be a unit at each ramified place. Then $G_J(\beta) = \chi_{\mathrm{id}}((u)) \chi_\infty(u) G_J(u \beta)$. -/
theorem periodicGaussCoeff_eq_mul (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰)
    {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) :
    periodicGaussCoeff χ J β =
      (periodicChar χ (Units.mk0 (u : K) hu0) : ℂ) * periodicGaussCoeff χ J ((u : K) * β) := by
  rw [periodicGaussCoeff, periodicGaussCoeff, Finset.mul_sum]
  refine (sum_out_map_eq _ (fun ℓ => periodicLatticeCoeff χ J ℓ *
      traceExp K (β * (𝔢[J].symm ℓ : K))) (fun g h hh => ?_) (rayMulMap J u)
      (subLattice_le_comap_rayMulMap J u)
      (comap_rayMulMap_le hu0 hu J)).symm.trans (Finset.sum_congr rfl fun q _ => ?_)
  · beta_reduce
    rw [periodicLatticeCoeff_add hS J g ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩]
    exact congrArg _ (cexp_trace_add J hβ g h hh)
  · beta_reduce
    rw [periodicLatticeCoeff_rayMulMap hu0 hu, coe_symm_rayMulMap, mul_left_comm β,
      mul_assoc (u : K) β]
    exact mul_assoc _ _ _

/-- **The periodic Gauss sum is periodic modulo the dual of $J$.** If $\gamma \in J^\vee$, then $G_J(\beta + \gamma) = G_J(\beta)$. -/
theorem periodicGaussCoeff_add_of_mem_dual (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K)
    {γ : K} (hγ : γ ∈ FractionalIdeal.dual ℤ ℚ 𝔣[J]) :
    periodicGaussCoeff χ J (β + γ) = periodicGaussCoeff χ J β := by
  rw [periodicGaussCoeff, periodicGaussCoeff]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual (Units.ne_zero _)).1 hγ _ (𝔢[J].symm q.out).2
  rw [Algebra.traceForm_apply, eq_intCast] at hn
  rw [add_mul, traceExp_add, (traceExp_eq_one_iff _).2 ⟨n, hn.symm⟩, mul_one]

/-- **The vanishing of the periodic Gauss sum at one prime.** Let $v$ be a ramified place with prime ideal $\mathfrak{p}$, and let $\beta \in \mathfrak{p} (\mathfrak{f} J)^\vee$. Then $G_J(\beta) = 0$. -/
theorem periodicGaussCoeff_eq_zero_of_mem (J : (Ideal (𝓞 K))⁰) {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∈ ramifiedSet χ) {β : K}
    (hβ : β ∈ (v₀.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) :
    periodicGaussCoeff χ J β = 0 := by
  obtain ⟨u, hu0, hcount, hle, hne⟩ := exists_periodicChar_ne_one_of_mem hv₀
  have hβD : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] :=
    mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one hβ
  have hmem : ((u : K) - 1) * β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[J] := by
    have h1 : ((u : K) - 1) * β ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) - 1) *
        ((v₀.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) :=
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
  have h := periodicGaussCoeff_eq_mul ⟨v₀, hv₀⟩ J hu0 hcount hβD
  rw [show (u : K) * β = β + ((u : K) - 1) * β by ring,
    periodicGaussCoeff_add_of_mem_dual χ J β hmem] at h
  have h4 : ((periodicChar χ (Units.mk0 (u : K) hu0) : ℂ) - 1) * periodicGaussCoeff χ J β = 0 := by
    linear_combination -h
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 fun h0 => hne (Units.ext h0))

/-- If an ideal $I$ is not prime to $\mathfrak{f}$, that is $I + \mathfrak{f} \neq \mathcal{O}_K$, then $I$ is contained in the prime ideal of a ramified place. -/
theorem exists_ramified_le_of_sup_ne_top {I : Ideal (𝓞 K)} (hIf : I ⊔ χ.conductor ≠ ⊤) :
    ∃ v ∈ ramifiedSet χ, I ≤ v.asIdeal := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIf
  have hfM : χ.conductor ≤ M := le_sup_right.trans hIM
  rw [conductor_eq_prod] at hfM
  obtain ⟨v, hv, hvM⟩ := (hM.isPrime.prod_le).1 hfM
  have hvM' : v.asIdeal = M := by
    have := hM.isPrime
    exact v.isMaximal.eq_of_le hM.ne_top (Ideal.IsPrime.le_of_pow_le hvM)
  exact ⟨v, hv, hvM' ▸ le_sup_left.trans hIM⟩

/-- **The vanishing of the periodic Gauss sum.** Let $\beta \in K$, and let $I$ be an integral ideal with $I = (\beta) \mathfrak{f} J \mathfrak{d}$, where $\mathfrak{d}$ is the different ideal. If $I$ is not prime to $\mathfrak{f}$, that is $I + \mathfrak{f} \neq \mathcal{O}_K$, then $G_J(\beta) = 0$. There is no condition on $\chi$ at the infinite places. -/
theorem periodicGaussCoeff_eq_zero (J : (Ideal (𝓞 K))⁰) {β : K} (I : Ideal (𝓞 K))
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      𝔣[conductorNZ χ * J] * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))
    (hIf : I ⊔ χ.conductor ≠ ⊤) :
    periodicGaussCoeff χ J β = 0 := by
  have hspan : (I : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ β := (spanSingleton_eq_coeIdeal_mul_dual J hI).symm
  obtain ⟨v, hv, hIv⟩ := exists_ramified_le_of_sup_ne_top hIf
  refine periodicGaussCoeff_eq_zero_of_mem J hv ?_
  have hb := FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ β
  rw [← hspan] at hb
  exact (FractionalIdeal.mul_le.2 fun a ha b hb => FractionalIdeal.mul_mem_mul
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 hIv ha) hb) hb

/-- The fractional ideal $\mathfrak{f} (\mathfrak{f} J)^\vee$ is contained in $J^\vee$. -/
theorem conductor_mul_dual_le (J : (Ideal (𝓞 K))⁰) :
    (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] ≤
      FractionalIdeal.dual ℤ ℚ 𝔣[J] := by
  have h := mul_dual_mul_le (I := (χ.conductor : FractionalIdeal (𝓞 K)⁰ K)) (J := 𝔣[J])
    (coeIdeal_conductor_ne_zero χ) (Units.ne_zero _)
  rwa [← coe_mk0_conductorNZ_mul] at h

/-- **The character values of the generators.** Let $(\beta, I)$ and $(\beta', I')$ satisfy the condition `Langlands.Tate.IsRayGaussPair`, and let $\beta' = u \beta + z$ with $u \in \mathcal{O}_K$ nonzero and $z \in \mathfrak{f} (\mathfrak{f} J)^\vee$. Then $\chi_{\mathrm{id}}((\beta')) \chi_\infty(\beta') = \chi_{\mathrm{id}}((u)) \chi_\infty(u) \chi_{\mathrm{id}}((\beta)) \chi_\infty(\beta)$. -/
theorem periodicChar_eq_mul_of_eq_mul_add {J : (Ideal (𝓞 K))⁰} {β β' : K}
    {I I' : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) (h' : IsRayGaussPair χ J β' I')
    {u : 𝓞 K} (hu0 : (u : K) ≠ 0) {z : K}
    (hz : z ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J])
    (he : β' = (u : K) * β + z) :
    periodicChar χ (Units.mk0 β' h'.ne_zero) =
      periodicChar χ (Units.mk0 (u : K) hu0) * periodicChar χ (Units.mk0 β h.ne_zero) := by
  set D := FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] with hD
  have hD0 : D ≠ 0 := dual_conductor_mul_ne_zero J
  have hβ0 := h.ne_zero
  have hβ0' := h'.ne_zero
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
  have hχe := idealChar_mul_infChar_eq χ _ _ hval
  rw [← periodicChar_apply, ← periodicChar_apply] at hχe
  rw [hχe, show Units.mk0 ((u : K) * β) huβ = Units.mk0 (u : K) hu0 * Units.mk0 β hβ0 from
    Units.ext rfl, map_mul]

/-- The dual $(\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$ as a unit of the fractional ideals. -/
noncomputable def gaussDual (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) (dual_conductor_mul_ne_zero J)

/-- The fractional ideal of `gaussDual χ J` is $(\mathfrak{f} J)^\vee$. -/
theorem coe_gaussDual (J : (Ideal (𝓞 K))⁰) :
    (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] := rfl

/-- If $(\beta, I)$ satisfies the condition, then $\beta$ satisfies the condition of `Langlands.Tate.rayCoeff` for the ideal $(\mathfrak{f} J)^\vee$: $v((\beta)) = v((\mathfrak{f} J)^\vee)$ at each ramified place $v$. -/
theorem IsRayGaussPair.cond_gaussDual {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ J β I) :
    β ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) =
        FractionalIdeal.count K v (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨h.ne_zero, fun v hv => ?_⟩
  rw [spanSingleton_eq_coeIdeal_mul_dual J h.1, FractionalIdeal.count_mul K v
    (FractionalIdeal.coeIdeal_ne_zero.2 (by
      rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero I))
    (dual_conductor_mul_ne_zero J), count_eq_zero_of_sup_conductor_eq_top h.2 hv, zero_add,
    coe_gaussDual]

/-- If $(\beta, I)$ satisfies the condition, then the periodic coefficient of $\beta$ for the ideal $D = (\mathfrak{f} J)^\vee$ is $c_D(\beta) = \chi_{\mathrm{id}}((\beta)) \chi_\infty(\beta) \chi_{\mathrm{id}}(D)^{-1} = \chi_{\mathrm{id}}(I) \chi_\infty(\beta)$. -/
theorem IsRayGaussPair.periodicCoeff_gaussDual {J : (Ideal (𝓞 K))⁰} {β : K}
    {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) :
    periodicCoeff χ (gaussDual χ J) β =
      ((periodicChar χ (Units.mk0 β h.ne_zero) * (idealChar χ (gaussDual χ J))⁻¹ : ℂˣ) : ℂ) :=
  periodicCoeff_of_cond _ h.cond_gaussDual

/-- **The periodic Gauss sum times the coefficient is constant.** Let $\chi$ be ramified at one place, and let $(\beta, I)$ and $(\beta', I')$ satisfy the condition `Langlands.Tate.IsRayGaussPair`, that is $I = (\beta) \mathfrak{f} J \mathfrak{d}$ and $I' = (\beta') \mathfrak{f} J \mathfrak{d}$ are integral ideals prime to $\mathfrak{f}$. Let $D = (\mathfrak{f} J)^\vee$. Then $G_J(\beta) c_D(\beta) = G_J(\beta') c_D(\beta')$. -/
theorem periodicGaussCoeff_mul_periodicCoeff_eq (hS : (ramifiedSet χ).Nonempty)
    {J : (Ideal (𝓞 K))⁰} {β β' : K} {I I' : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I)
    (h' : IsRayGaussPair χ J β' I') :
    periodicGaussCoeff χ J β * periodicCoeff χ (gaussDual χ J) β =
      periodicGaussCoeff χ J β' * periodicCoeff χ (gaussDual χ J) β' := by
  obtain ⟨u, z, hz, he⟩ := h.exists_eq_mul_add h'.mem_dual
  have hu : ∀ v ∈ ramifiedSet χ, u ∉ v.asIdeal := fun v hv => h.notMem_of_eq_mul_add h' hz he hv
  have hu0 : (u : K) ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h0
    exact hu v hv (by rw [show u = 0 from by exact_mod_cast h0]; exact zero_mem _)
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_notMem hu0 (hu v hv)
  have h1 := periodicGaussCoeff_eq_mul hS J hu0 hcount h.mem_dual
  have h2 : periodicGaussCoeff χ J β' = periodicGaussCoeff χ J ((u : K) * β) := by
    rw [he]
    exact periodicGaussCoeff_add_of_mem_dual χ J _ (conductor_mul_dual_le J hz)
  rw [h.periodicCoeff_gaussDual, h'.periodicCoeff_gaussDual,
    periodicChar_eq_mul_of_eq_mul_add h h' hu0 hz he, h1, h2]
  push_cast
  ring

end Gauss

section Evaluation

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- **The periodic Gauss sum of $\chi$ for the ideal $J$.** It is $\tau_J(\chi) = G_J(\beta) c_D(\beta)$, with $D = (\mathfrak{f} J)^\vee$, for a chosen pair $(\beta, I)$ with $I = (\beta) \mathfrak{f} J \mathfrak{d}$ integral and prime to $\mathfrak{f}$. By `periodicGaussCoeff_mul_periodicCoeff_eq` the value does not depend on the choice. It is $0$ if there is no such pair. -/
noncomputable def periodicGaussSum (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) : ℂ :=
  if h : ∃ (β : K) (I : (Ideal (𝓞 K))⁰), IsRayGaussPair χ J β I then
    periodicGaussCoeff χ J h.choose * periodicCoeff χ (gaussDual χ J) h.choose
  else 0

/-- The periodic Gauss sum $\tau_J(\chi)$ is $G_J(\beta) c_D(\beta)$ for each pair $(\beta, I)$ that satisfies the condition. -/
theorem periodicGaussSum_eq (hS : (ramifiedSet χ).Nonempty) {J : (Ideal (𝓞 K))⁰} {β : K}
    {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) :
    periodicGaussSum χ J = periodicGaussCoeff χ J β * periodicCoeff χ (gaussDual χ J) β := by
  have hex : ∃ (β : K) (I : (Ideal (𝓞 K))⁰), IsRayGaussPair χ J β I := ⟨β, I, h⟩
  rw [periodicGaussSum, dite_eq_left hex]
  exact periodicGaussCoeff_mul_periodicCoeff_eq hS hex.choose_spec.choose_spec h

end Evaluation

section Unitary

/-- If $|z| = 1$, then $\overline{z} z = 1$. -/
theorem conj_mul_self_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : starRingEnd ℂ z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow, Complex.ofReal_one]

/-- If $\chi$ is unitary, the ideal character has absolute value $1$. -/
theorem norm_idealChar_of_unitary (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ‖(idealChar χ I : ℂ)‖ = 1 := by
  rw [idealChar_apply, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_mulSupport_zpow_count (primeValue χ) (I : FractionalIdeal (𝓞 K)⁰ K)).toFinset)
    (by simp), Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val, norm_zpow,
    show ‖(primeValue χ v : ℂ)‖ = 1 from hu (IdeleGroup.ofAdicCompletion (𝓞 K) K v
      (localUniformizer K v)), one_zpow]

/-- If $\chi$ is unitary, the infinite type has absolute value $1$. -/
theorem norm_infChar_of_unitary (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (x : Kˣ) : ‖(infChar χ x : ℂ)‖ = 1 := by
  rw [infChar_apply]
  exact hu _

/-- If $\chi$ is unitary, then $|\chi_{\mathrm{id}}((x)) \chi_\infty(x)| = 1$. -/
theorem norm_periodicChar_of_unitary (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (x : Kˣ) : ‖(periodicChar χ x : ℂ)‖ = 1 := by
  rw [periodicChar_apply, Units.val_mul, norm_mul, norm_idealChar_of_unitary hu,
    norm_infChar_of_unitary hu, mul_one]

/-- If $\chi$ is unitary and $\alpha$ satisfies the condition of `Langlands.Tate.rayCoeff`, then the periodic coefficient has absolute value $1$. -/
theorem norm_periodicCoeff_of_cond (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K}
    (hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ‖periodicCoeff χ J α‖ = 1 := by
  rw [periodicCoeff_of_cond J hα, Units.val_mul, Units.val_mul, norm_mul, norm_mul,
    norm_idealChar_of_unitary hu, norm_infChar_of_unitary hu, Units.val_inv_eq_inv_val, norm_inv,
    norm_idealChar_of_unitary hu, inv_one, mul_one, mul_one]

/-- **The evaluation of the periodic Gauss sum at a generator.** Let $\chi$ be unitary and ramified at one place, and let $(\beta, I)$ satisfy the condition `Langlands.Tate.IsRayGaussPair`. Then $G_J(\beta) = \tau_J(\chi) \overline{c_D(\beta)}$, where $D = (\mathfrak{f} J)^\vee$. -/
theorem IsRayGaussPair.periodicGaussCoeff_eq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) {J : (Ideal (𝓞 K))⁰} {β : K}
    {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) :
    periodicGaussCoeff χ J β =
      periodicGaussSum χ J * starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β) := by
  have hc := conj_mul_self_of_norm_eq_one (norm_periodicCoeff_of_cond hu _ h.cond_gaussDual)
  rw [periodicGaussSum_eq hS h, mul_assoc, mul_comm (periodicCoeff χ _ β), hc, mul_one]

/-- **The evaluation of the periodic Gauss sum.** Let $\chi$ be unitary and ramified at one place, let $D = (\mathfrak{f} J)^\vee$ and let $\beta \in D$. Then $G_J(\beta) = \tau_J(\chi) \overline{c_D(\beta)}$, where $c_D$ is the periodic coefficient for the ideal $D$. If $(\beta) \mathfrak{f} J \mathfrak{d}$ is not prime to $\mathfrak{f}$, both sides are $0$. There is no other condition on $\chi$ at the infinite places. -/
theorem periodicGaussCoeff_eq_periodicGaussSum_mul (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K)) :
    periodicGaussCoeff χ J β =
      periodicGaussSum χ J * starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β) := by
  by_cases hβ0 : β = 0
  · subst hβ0
    rw [periodicCoeff, dite_eq_right (fun h => h rfl), map_zero, mul_zero, periodicGaussCoeff]
    simp only [zero_mul, traceExp, map_zero, Rat.cast_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, mul_one]
    exact sum_periodicLatticeCoeff_eq_zero hS J
  set D := (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) with hD
  have hD0 : D ≠ 0 := Units.ne_zero _
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ β * D⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hD0]
    exact mul_le_mul_left ((FractionalIdeal.spanSingleton_le_iff_mem).2 hβ) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hID : (I : FractionalIdeal (𝓞 K)⁰ K) * D = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    rw [hI, mul_assoc, inv_mul_cancel₀ hD0, mul_one]
  have hI0 : I ≠ 0 := by
    rintro rfl
    rw [Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, zero_mul] at hID
    exact hβ0 ((FractionalIdeal.spanSingleton_eq_zero_iff).1 hID.symm)
  have hIeq : (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ β *
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hI, hD, coe_gaussDual, inv_dual_conductor_mul J, mul_assoc]
  by_cases htop : I ⊔ χ.conductor = ⊤
  · exact IsRayGaussPair.periodicGaussCoeff_eq (I := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩) hS
      hu ⟨hIeq, htop⟩
  · rw [periodicGaussCoeff_eq_zero J I hIeq htop, periodicCoeff_eq_zero_of_not, map_zero,
      mul_zero]
    rintro ⟨-, hc⟩
    obtain ⟨v, hv, hIv⟩ := exists_ramified_le_of_sup_ne_top htop
    have h1 := hc v hv
    rw [← hID, FractionalIdeal.count_mul K v (FractionalIdeal.coeIdeal_ne_zero.2 (by
      rw [← Submodule.zero_eq_bot]; exact hI0)) hD0] at h1
    have h2 := (count_eq_zero_iff_not_dvd v ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩).1
      (by rw [← hD] at h1; simpa using h1)
    exact h2 (Ideal.dvd_iff_le.2 hIv)

end Unitary

section Norm

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

/-- The periodic Gauss sum as a sum over the finite quotient. -/
theorem periodicGaussCoeff_def (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) :
    periodicGaussCoeff χ J β = ∑ q : 𝔔[χ, J], periodicLatticeCoeff χ J q.out *
      traceExp K (β * (𝔢[J].symm q.out : K)) := rfl

/-- The periodic coefficient of the unit ideal at $1$ is $1$. -/
theorem periodicCoeff_one_one : periodicCoeff χ (FractionalIdeal.mk0 K 1) 1 = 1 := by
  rw [periodicCoeff, dite_eq_left one_ne_zero, rayCoeff_one_one, one_mul,
    show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext rfl, map_one, Units.val_one]

/-- For a unitary $\chi$ ramified at one place, $\beta \in (\mathfrak{f} J)^\vee$ and $\nu \in \mathcal{O}_K$, $G_J(\nu \beta) = \overline{c(\nu)} G_J(\beta)$, where $c$ is the periodic coefficient for the unit ideal. If $\nu$ is in a ramified prime, both sides are zero. -/
theorem periodicGaussCoeff_mul_eq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) {ν : K}
    (hν : ν ∈ 𝔣[(1 : (Ideal (𝓞 K))⁰)]) :
    periodicGaussCoeff χ J (ν * β) =
      starRingEnd ℂ (periodicCoeff χ (FractionalIdeal.mk0 K 1) ν) * periodicGaussCoeff χ J β := by
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hν
  obtain ⟨u, -, rfl⟩ := hν
  rw [show algebraMap (𝓞 K) K u = (u : K) from rfl]
  have hcnt1 : ∀ v, FractionalIdeal.count K v 𝔣[(1 : (Ideal (𝓞 K))⁰)] = 0 := fun v => by
    rw [coe_mk0_one, FractionalIdeal.count_one]
  by_cases h : (u : K) ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) =
        FractionalIdeal.count K v 𝔣[(1 : (Ideal (𝓞 K))⁰)]
  · have hcount : ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
      fun v hv => (h.2 v hv).trans (hcnt1 v)
    have ht := periodicGaussCoeff_eq_mul hS J h.1 hcount hβ
    have hc := conj_mul_self_of_norm_eq_one
      (norm_periodicChar_of_unitary hu (Units.mk0 (u : K) h.1))
    have h1 : periodicCoeff χ (FractionalIdeal.mk0 K 1) (u : K) =
        (periodicChar χ (Units.mk0 (u : K) h.1) : ℂ) := by
      have h1' : idealChar χ (FractionalIdeal.mk0 K 1) = 1 := by
        rw [map_one (FractionalIdeal.mk0 K), map_one]
      rw [periodicCoeff_of_cond _ h, h1', inv_one, mul_one, ← periodicChar_apply]
    rw [h1, ht, ← mul_assoc, hc, one_mul]
  · rw [periodicCoeff_eq_zero_of_not _ h, map_zero, zero_mul]
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
    obtain ⟨v, hv, hu'⟩ := hv
    exact periodicGaussCoeff_eq_zero_of_mem J hv
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨u, hu', rfl⟩) hβ)

/-- The product $G_J(\beta) \overline{G_1(\beta \xi)}$ as a double sum over $J / \mathfrak{f} J$ and $\mathcal{O}_K / \mathfrak{f}$. -/
theorem periodicGaussCoeff_mul_conj_eq_sum (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]) (ξ : K) :
    periodicGaussCoeff χ J β * starRingEnd ℂ (periodicGaussCoeff χ 1 (β * ξ)) =
      ∑ x : 𝔔[χ, J], periodicLatticeCoeff χ J x.out * ∑ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)],
        traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) := by
  rw [periodicGaussCoeff_def χ 1, map_sum, Finset.mul_sum]
  have h1 : ∀ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)], periodicGaussCoeff χ J β *
      starRingEnd ℂ (periodicLatticeCoeff χ 1 n.out *
        traceExp K (β * ξ * (𝔢[1].symm n.out : K))) =
      ∑ x : 𝔔[χ, J], periodicLatticeCoeff χ J x.out *
        traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) := fun n => by
    rw [map_mul, conj_traceExp, ← mul_assoc, mul_comm (periodicGaussCoeff χ J β),
      show periodicLatticeCoeff χ 1 n.out =
        periodicCoeff χ (FractionalIdeal.mk0 K 1) (𝔢[1].symm n.out : K) from rfl,
      ← periodicGaussCoeff_mul_eq hS hu J hβ (𝔢[1].symm n.out).2, periodicGaussCoeff_def,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, ← traceExp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun n _ => h1 n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- **The inversion formula.** Let $\chi$ be unitary and ramified at one place. If $(\beta, I)$ is a pair for $J$ and $\xi \in J$, then $N(\mathfrak{f}) c_J(\xi) = G_J(\beta) \overline{G_1(\beta \xi)}$. -/
theorem mul_periodicCoeff_eq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I) {ξ : K}
    (hξ : ξ ∈ 𝔣[J]) :
    (Ideal.absNorm χ.conductor : ℂ) * periodicCoeff χ (FractionalIdeal.mk0 K J) ξ =
      periodicGaussCoeff χ J β * starRingEnd ℂ (periodicGaussCoeff χ 1 (β * ξ)) := by
  have hβ := h.mem_dual
  have step2 : ∀ x : 𝔔[χ, J], periodicLatticeCoeff χ J x.out *
      ∑ n : 𝔔[χ, (1 : (Ideal (𝓞 K))⁰)],
        traceExp K (β * ((𝔢[J].symm x.out : K) - ξ) * (𝔢[1].symm n.out : K)) =
        if x = QuotientAddGroup.mk (𝔢[J] ⟨ξ, hξ⟩) then
          periodicLatticeCoeff χ J x.out * (Ideal.absNorm χ.conductor : ℂ) else 0 := fun x => by
    rw [sum_traceExp_eq χ 1 (mul_mem_dual_conductor hβ (sub_mem_fi (𝔢[J].symm x.out).2 hξ)),
      ← mul_ite_zero]
    congr 1
    exact if_congr (h.mul_sub_mem_dual_iff hξ x) rfl rfl
  rw [periodicGaussCoeff_mul_conj_eq_sum hS hu J hβ ξ, Finset.sum_congr rfl fun x _ => step2 x,
    Fintype.sum_eq_single _ fun x hx => ite_eq_right hx, ite_eq_left rfl, mul_comm,
    out_mk_eq _ (periodicLatticeCoeff χ J)
      (fun g h hh => periodicLatticeCoeff_add hS J g ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩)]
  rw [periodicLatticeCoeff, Equiv.symm_apply_apply]

/-- If $\chi$ is unitary and ramified at one place, and $(\beta, I)$ is a pair for the unit ideal, then $G_1(\beta) \overline{G_1(\beta)} = N(\mathfrak{f})$. -/
theorem periodicGaussCoeff_mul_conj (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) {β : K} {I : (Ideal (𝓞 K))⁰}
    (h : IsRayGaussPair χ 1 β I) :
    periodicGaussCoeff χ 1 β * starRingEnd ℂ (periodicGaussCoeff χ 1 β) =
      Ideal.absNorm χ.conductor := by
  have h1 := mul_periodicCoeff_eq hS hu h (ξ := 1)
    (by rw [coe_mk0_one]; exact FractionalIdeal.one_mem_one _)
  rw [periodicCoeff_one_one, mul_one, mul_one] at h1
  exact h1.symm

/-- If $(t) = T J$ and $T + \mathfrak{f} = \mathcal{O}_K$, then $t$ satisfies the condition of `Langlands.Tate.rayCoeff` for $J$. -/
theorem cond_of_spanSingleton_eq {J : (Ideal (𝓞 K))⁰} {t : K} {T : (Ideal (𝓞 K))⁰}
    (hT : FractionalIdeal.spanSingleton (𝓞 K)⁰ t =
      ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J])
    (hTf : (T : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤) :
    t ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ t) =
        FractionalIdeal.count K v 𝔣[J] := by
  have hT0 : ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero (FractionalIdeal.mk0 K T)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hT
    exact mul_ne_zero hT0 (Units.ne_zero _) hT.symm
  exact ⟨ht0, fun v hv => by
    rw [hT, FractionalIdeal.count_mul K v hT0 (Units.ne_zero _),
      count_eq_zero_of_sup_conductor_eq_top hTf hv, zero_add]⟩

/-- **The change of the ideal.** Let $\chi$ be unitary and ramified at one place, let $(\beta, I)$ be a pair for $J$, and let $(t) = T J$ with $T + \mathfrak{f} = \mathcal{O}_K$. Then $(\beta t, I T)$ is a pair for the unit ideal and $G_J(\beta) = G_1(\beta t) c_J(t)$. -/
theorem IsRayGaussPair.periodicGaussCoeff_eq_mul_one (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    {J : (Ideal (𝓞 K))⁰} {β : K} {I : (Ideal (𝓞 K))⁰} (h : IsRayGaussPair χ J β I)
    {t : K} {T : (Ideal (𝓞 K))⁰}
    (hT : FractionalIdeal.spanSingleton (𝓞 K)⁰ t =
      ((T : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J])
    (hTf : (T : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤) :
    IsRayGaussPair χ 1 (β * t) (I * T) ∧
      periodicGaussCoeff χ J β = periodicGaussCoeff χ 1 (β * t) *
        periodicCoeff χ (FractionalIdeal.mk0 K J) t := by
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
  refine ⟨h', ?_⟩
  have hstar := mul_periodicCoeff_eq hS hu h ht
  have hnorm := periodicGaussCoeff_mul_conj hS hu h'
  have hN : (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0)
  have hb : starRingEnd ℂ (periodicGaussCoeff χ 1 (β * t)) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hnorm
    exact hN hnorm.symm
  refine mul_right_cancel₀ hb ?_
  rw [← hstar]
  linear_combination (periodicCoeff χ (FractionalIdeal.mk0 K J) t) * hnorm.symm

/-- **The absolute value of the periodic Gauss sum.** Let $\chi$ be unitary and ramified at one place. Then $|\tau_J(\chi)|^2 = N(\mathfrak{f})$ for each nonzero integral ideal $J$. There is no other condition on $\chi$ at the infinite places. -/
theorem norm_periodicGaussSum_sq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) :
    ‖periodicGaussSum χ J‖ ^ 2 = Ideal.absNorm χ.conductor := by
  obtain ⟨β, I, h⟩ := exists_isRayGaussPair hS J
  obtain ⟨t, T, hT, hTf⟩ := exists_spanSingleton_eq_coeIdeal_mul (χ := χ) hS J
  obtain ⟨h', ha⟩ := h.periodicGaussCoeff_eq_mul_one hS hu hT hTf
  have hnorm := periodicGaussCoeff_mul_conj hS hu h'
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hnorm
  rw [periodicGaussSum_eq hS h, ha, norm_mul, norm_mul,
    norm_periodicCoeff_of_cond hu _ (cond_of_spanSingleton_eq hT hTf),
    norm_periodicCoeff_of_cond hu _ h.cond_gaussDual, mul_one, mul_one]
  exact_mod_cast hnorm

end Norm

end Langlands.Tate
