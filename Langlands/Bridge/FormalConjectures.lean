/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.FormalConjectures.Wikipedia
import Langlands.Statements.Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Langlands.Fidelity.Modularity

/-!
# Bridges to formal-conjectures

This file compares the statements of the project with the statements of formal-conjectures (spec 06.4). The statements of formal-conjectures are in `Langlands/Ported/FormalConjectures/Wikipedia.lean`.

* `Langlands.Bridge.hasseWeil_rat_of_hasseWeilEllipticQ`: `HasseWeilEllipticQ` implies the statement `exists_hasAnalyticContinuation_rat` of formal-conjectures. The proof divides the completed L-function by the gamma factor. The function $1/\Gamma$ is entire, so the quotient is entire.
* `Langlands.Bridge.not_modularityConjecture`: the statement `modularityConjecture` of formal-conjectures is false for every elliptic curve over $\mathbb{Q}$.

## The statement of modularity in formal-conjectures

The coefficient `modularFormAn n f` of formal-conjectures is the coefficient of the $q$-expansion `qExpansion N f`, with the parameter $q_N = e^{2 \pi i \tau / N}$. The width of the cusp $\infty$ of $\Gamma_0(N)$ is 1, so a form $f = \sum a_n e^{2 \pi i n \tau}$ has the expansion $\sum a_n q_N^{nN}$ in this parameter. For $N \ge 2$ the coefficient of $q_N$ is 0 (`coeff_one_qExpansion_eq_zero`), so no form satisfies the condition `modularFormAn 1 f = 1`. For $N = 1$ there is no nonzero cusp form of weight 2. So no curve satisfies `modularityConjecture`, and the theorem `modularity_conjecture` of formal-conjectures is false as stated.

The repair is to use the width 1: `qExpansion 1 f`. The project statement `Langlands.ModularityEllipticQ` uses this parameter. The report to formal-conjectures is a decision of the owner.
-/

namespace Langlands.Bridge

open UpperHalfPlane Function.Periodic Complex
open scoped MatrixGroups Real

section HasseWeil

/-- `HasseWeilEllipticQ` implies the Hasse-Weil statement over $\mathbb{Q}$ of formal-conjectures. -/
theorem hasseWeil_rat_of_hasseWeilEllipticQ (h : HasseWeilEllipticQ) :
    Ported.FormalConjectures.HasseWeil.exists_hasAnalyticContinuation_rat := by
  intro E _
  obtain ⟨N, ε, Λ, hN, -, hΛ, hL, -⟩ := h E
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2pi : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  refine ⟨fun s => Λ s * (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ =>
        Λ s * (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹ := by
      have h1 : Differentiable ℂ fun s : ℂ => (Complex.Gamma s)⁻¹ := by
        simpa [one_div] using Complex.differentiable_one_div_Gamma
      have h2 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(s / 2)) := fun s =>
        ((differentiableAt_id.div_const 2).neg).const_cpow (Or.inl hN0)
      have h3 : Differentiable ℂ fun s : ℂ => (2 * π : ℂ) ^ s := fun s =>
        differentiableAt_id.const_cpow (Or.inl h2pi)
      exact ((hΛ.mul h2).mul h3).mul h1
    exact fun z => hd.analyticAt z
  · intro s hs
    beta_reduce
    rw [hL s hs]
    have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have e1 : (N : ℂ) ^ (s / 2) * (N : ℂ) ^ (-(s / 2)) = 1 := by
      rw [← Complex.cpow_add _ _ hN0]; simp
    have e2 : (2 * π : ℂ) ^ (-s) * (2 * π : ℂ) ^ s = 1 := by
      rw [← Complex.cpow_add _ _ h2pi]; simp
    calc (N : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Complex.Gamma s * E.LSeries s *
          (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹
        = ((N : ℂ) ^ (s / 2) * (N : ℂ) ^ (-(s / 2))) * ((2 * π : ℂ) ^ (-s) * (2 * π : ℂ) ^ s) *
            (Complex.Gamma s * (Complex.Gamma s)⁻¹) * E.LSeries s := by ring
      _ = E.LSeries s := by rw [e1, e2, mul_inv_cancel₀ hG]; ring

end HasseWeil

section Modularity

variable {N : ℕ} {k : ℤ}

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem natCast_mem_strictPeriods_Gamma0 (N : ℕ) :
    (N : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp only [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨N, by simp⟩

/-- In the parameter $q_N$, the cusp function of a form on $\Gamma_0(N)$ is the cusp function in the parameter $q_1$, composed with $q \mapsto q^N$. -/
theorem cuspFunction_natCast_eq (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.cuspFunction (N : ℝ) f = UpperHalfPlane.cuspFunction 1 f ∘ fun q => q ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma0 N)
  funext q
  by_cases hq : q = 0
  · subst hq
    rw [Function.comp_apply, zero_pow hN.ne', CuspFormClass.cuspFunction_apply_zero f hNpos
      (natCast_mem_strictPeriods_Gamma0 N), CuspFormClass.cuspFunction_apply_zero f one_pos
      (one_mem_strictPeriods_Gamma0 N)]
  · have hqN : q ^ N ≠ 0 := pow_ne_zero _ hq
    simp only [Function.comp_apply, UpperHalfPlane.cuspFunction,
      Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.Periodic.cuspFunction_eq_of_nonzero _ _ hqN]
    have hinv : invQParam (N : ℝ) q = (N : ℂ) * invQParam 1 q := by
      simp only [invQParam]; push_cast; ring
    have hexp : qParam 1 (invQParam (N : ℝ) q) = qParam 1 (invQParam 1 (q ^ N)) := by
      rw [qParam_right_inv one_ne_zero hqN, hinv]
      calc qParam 1 ((N : ℂ) * invQParam 1 q) = (qParam 1 (invQParam 1 q)) ^ N := by
            simp only [qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
        _ = q ^ N := by rw [qParam_right_inv one_ne_zero hq]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hw : invQParam (N : ℝ) q = invQParam 1 (q ^ N) + n := by
      simp only [Complex.ofReal_one, div_one] at hn
      exact mul_left_cancel₀ h2pi (by rw [hn]; ring)
    rw [hw]
    simpa using (hper.int_mul n) (invQParam 1 (q ^ N))

/-- For $N \ge 2$, the coefficient of $q_N$ in the expansion `qExpansion N f` of a cusp form on $\Gamma_0(N)$ is 0. -/
theorem coeff_one_qExpansion_eq_zero (hN : 2 ≤ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (qExpansion (N : ℝ) f).coeff 1 = 0 := by
  have hG : DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 :=
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0 N)).differentiableAt
  have hG' : HasDerivAt (UpperHalfPlane.cuspFunction 1 f)
      (deriv (UpperHalfPlane.cuspFunction 1 f) 0) ((fun q : ℂ => q ^ N) 0) := by
    simpa [zero_pow (by omega : N ≠ 0)] using hG.hasDerivAt
  have hcomp : HasDerivAt (UpperHalfPlane.cuspFunction 1 f ∘ fun q : ℂ => q ^ N)
      (deriv (UpperHalfPlane.cuspFunction 1 f) 0 * ((N : ℂ) * 0 ^ (N - 1))) 0 :=
    hG'.comp (0 : ℂ) (hasDerivAt_pow N 0)
  rw [qExpansion_coeff, cuspFunction_natCast_eq (by omega) f]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedDeriv_one]
  rw [hcomp.deriv, zero_pow (by omega : N - 1 ≠ 0)]
  simp

theorem gamma0_one_eq : (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  have h : CongruenceSubgroup.Gamma0 1 = ⊤ := by
    ext A; simp [CongruenceSubgroup.Gamma0_mem, Subsingleton.elim _ (0 : ZMod 1)]
  change Subgroup.map _ (CongruenceSubgroup.Gamma0 1) = _
  rw [h, MonoidHom.range_eq_map]

theorem cuspForm_weight_two_eq_zero_of_eq {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ = 𝒮ℒ)
    (f : CuspForm Γ 2) : f = 0 := by
  subst hΓ
  exact rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) f

/-- For each $N \ge 1$, the coefficient `modularFormAn 1 f` of formal-conjectures is 0 for each cusp form of weight 2 on $\Gamma_0(N)$. -/
theorem modularFormAn_one_eq_zero (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Ported.FormalConjectures.ModularityConjecture.modularFormAn 1 f = 0 := by
  unfold Ported.FormalConjectures.ModularityConjecture.modularFormAn
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    rw [cuspForm_weight_two_eq_zero_of_eq gamma0_one_eq f]
    simp [qExpansion_coeff, UpperHalfPlane.cuspFunction]
  · exact coeff_one_qExpansion_eq_zero h f

/-- **The statement of modularity in formal-conjectures is false.** No elliptic curve over $\mathbb{Q}$ satisfies `modularityConjecture`, because the condition `modularFormAn 1 f = 1` fails for every cusp form of weight 2. -/
theorem not_modularityConjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ Ported.FormalConjectures.ModularityConjecture.modularityConjecture E := by
  rintro ⟨N, f, ⟨h1, -⟩, -⟩
  rw [modularFormAn_one_eq_zero N.pos f] at h1
  exact zero_ne_one h1

/-- The theorem `modularity_conjecture` of formal-conjectures is false as stated. -/
theorem not_modularity_conjecture :
    ¬ Ported.FormalConjectures.ModularityConjecture.modularity_conjecture := fun h =>
  not_modularityConjecture Fidelity.congruentNumberCurve (h _)

end Modularity

end Langlands.Bridge
