/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.Hecke
import Langlands.Tate.HeckeShiftRamified

/-!
# Hecke's functional equation for every Hecke character

This file proves `Langlands.HeckeFunctionalEquation`: the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for each Hecke character of each number field, with arbitrary archimedean parameters $(n_v, t_v)$.

The unramified case is `Langlands.Tate.heckeFunctionalEquation_of_unramified_general`. Let $\xi$ be ramified at one finite place. The character $\xi_\infty$ times the finite components at the ramified places is trivial on the units, and these finite components have norm $1$ on the units. Thus $\sum_w n_w \mathrm{Re}(t_w) \log |u|_w = 0$ for each unit $u$, and by the theorem of Dirichlet $\mathrm{Re}(t_w) = \mathrm{Re}(t_{w_0})$ for all $w$. The twist by $\|\cdot\|^{-\mathrm{Re}(t_{w_0})}$ gives a unitary character with the parameters $(n_w, i \theta_w)$, and `Langlands.Tate.entireFunctionalEquation_ramified_shift` applies to it.

## Main definitions

There are no new definitions in this file.

## Main results

* `Langlands.Tate.re_eq_of_isArchimedeanParameter_general`: the real parts of the shifts are equal, with no condition on the ramification.
* `Langlands.Tate.heckeFunctionalEquation_of_ramified_general`: the ramified case.
* `Langlands.Tate.heckeFunctionalEquation_general`: the conclusion of `Langlands.HeckeFunctionalEquationAt` for each Hecke character.
* `Langlands.heckeFunctionalEquation`: Hecke's theorem `Langlands.HeckeFunctionalEquation`.
-/

universe u

open Complex
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
  IsDedekindDomain
open scoped Classical nonZeroDivisors

namespace Langlands.Tate

section Character

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- A unit of $\mathcal{O}_K$ generates the unit fractional ideal, as a `FractionalIdeal.spanSingleton`. -/
theorem spanSingleton_unit (u : (𝓞 K)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
      (((Units.map (algebraMap (𝓞 K) K) u : Kˣ)) : K) = 1 := by
  rw [Units.coe_map]
  change FractionalIdeal.spanSingleton _ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
  rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit,
    FractionalIdeal.coeIdeal_top]

/-- **The real parts of the shifts are equal.** Let $\chi$ be a Hecke character with the parameters $(n_w, t_w)$ at each infinite place. There is no condition on the ramification. Then $\mathrm{Re}\, t_w = \mathrm{Re}\, t_{w_0}$ for each infinite place $w$. -/
theorem re_eq_of_isArchimedeanParameter_general {n : InfinitePlace K → ℤ}
    {t : InfinitePlace K → ℂ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w))
    (w : InfinitePlace K) : (t w).re = (t w₀).re := by
  refine eq_of_sum_mult_log_unit_eq_zero (fun w => (t w).re) (fun u => ?_) w
  set x : Kˣ := Units.map (algebraMap (𝓞 K) K) u with hxdef
  have hsp := spanSingleton_unit (K := K) u
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) x
    (fun v _ => by rw [hxdef, hsp, FractionalIdeal.count_one])
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v => by
    rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count, hxdef, hsp,
      FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rw [periodicChar_apply, toPrincipalIdeal_unit, map_one, one_mul] at e
  have e' := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) e
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, Units.val_one, norm_one] at e'
  rw [Finset.prod_congr rfl fun v _ => norm_finiteComponent_of_valued_eq_one χ v _ (hv1 v),
    Finset.prod_const_one, mul_one] at e'
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Units.coe_prod, norm_prod] at e'
  have hw : ∀ w : InfinitePlace K, ‖(χ.infiniteComponent w (ideleInf w
      (IdeleGroup.unitEmbedding (𝓞 K) K x)) : ℂ)‖ =
      w (u : K) ^ ((mult w : ℝ) * (t w).re) := fun w => by
    have hx : (0 : ℝ) < w ((x : Kˣ) : K) := pos_at_place u w
    have hx0 : w.embedding ((x : Kˣ) : K) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    rw [(hn w).eq, extensionEmbedding_ideleInf_unitEmbedding, norm_mul, norm_zpow, norm_div,
      Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hx0), one_zpow, one_mul,
      norm_embedding_eq, norm_cpow_eq_rpow_re_of_pos hx]
    simp [hxdef]
  rw [Finset.prod_congr rfl fun w _ => hw w] at e'
  have e2 := congrArg Real.log e'
  rw [Real.log_one, Real.log_prod (fun w _ => (Real.rpow_pos_of_pos (pos_at_place u w) _).ne')]
    at e2
  rw [← e2]
  exact Finset.sum_congr rfl fun w _ => by rw [Real.log_rpow (pos_at_place u w)]

end Character

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the ramified characters with arbitrary shifts.** Let $\xi$ be a Hecke character that is ramified at one finite place, with the archimedean parameters $(n_v, t_v)$ at the infinite places. The shifts $t_v$ can be different at different places, and the integers $n_w$ at the complex places can have arbitrary signs. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$, and $\Lambda$ is entire. -/
theorem heckeFunctionalEquation_of_ramified_general (ξ : HeckeCharacter K)
    (hr : ∃ v, ¬ ξ.IsUnramifiedAt v) (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
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
  obtain ⟨v₀, hv₀⟩ := hr
  have hre := re_eq_of_isArchimedeanParameter_general hn
  set t₀ : ℂ := (((t w₀).re : ℝ) : ℂ) with ht₀
  obtain ⟨χ, hξ⟩ : ∃ χ : HeckeCharacter K, ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ t₀ :=
    ⟨ξ * normPowerChar K (-t₀), fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]⟩
  have hξ' := inv_of_twist hξ
  set θ : InfinitePlace K → ℝ := fun v => (t v).im with hθdef
  have htθ : ∀ v, t v - t₀ = (θ v : ℂ) * I := fun v => by
    apply Complex.ext
    · simp [ht₀, hre v]
    · simp [ht₀, hθdef]
  have hp : ∀ v, χ.IsArchimedeanParameter v (n v) (t v - t₀) := fun v =>
    isArchimedeanParameter_of_twist hξ (hn v)
  have hp' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v + t₀) := fun v => by
    have h := isArchimedeanParameter_of_twist hξ' (hn' v)
    rwa [sub_neg_eq_add] at h
  have hθ : ∀ v, χ.IsArchimedeanParameter v (n v) ((θ v : ℂ) * I) := fun v => by
    rw [← htθ v]
    exact hp v
  have hχu := norm_ideleChar_of_norm_infiniteComponent (norm_infiniteComponent_of_shift hθ)
  have hS : (ramifiedSet χ).Nonempty :=
    ⟨v₀, mem_ramifiedSet.2 fun h => hv₀ ((isUnramifiedAt_twist_iff hξ v₀).2 h)⟩
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) :=
    entireFunctionalEquation_ramified_shift hS hp hp' htθ
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

/-- **Hecke's functional equation for every Hecke character.** Let $\xi$ be a Hecke character of $K$ with the archimedean parameters $(n_v, t_v)$, and let $(n', t')$ be archimedean parameters of $\xi^{-1}$. There is no condition on the shifts, on the signs of the $n_w$ or on the ramification. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. -/
theorem heckeFunctionalEquation_general (ξ : HeckeCharacter K)
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
  by_cases hu : ∀ v, ξ.IsUnramifiedAt v
  · exact heckeFunctionalEquation_of_unramified_general ξ hu n n' t t' hn hn'
  push Not at hu
  exact heckeFunctionalEquation_of_ramified_general ξ hu n n' t t' hn hn'

end Assembly

end Langlands.Tate

/-- **Hecke's theorem.** For each number field $K$, each Hecke character of $K$ satisfies the functional equation of `Langlands.HeckeFunctionalEquationAt`. This is `Langlands.HeckeFunctionalEquation`. -/
theorem Langlands.heckeFunctionalEquation : Langlands.HeckeFunctionalEquation.{u} :=
  fun _ _ _ χ n n' t t' hn hn' =>
    Langlands.Tate.heckeFunctionalEquation_general χ n n' t t' hn hn'
