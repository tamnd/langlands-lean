/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Maass

/-!
# Fidelity checks for the statements of Maass forms

This file has the fidelity checks of spec 06.3 for the statements of `Langlands.Statements.Maass`.

* `Langlands.Fidelity.integrableOn_fd`: the standard fundamental domain has finite hyperbolic area.
* `Langlands.Fidelity.isL2Eigenfunction_one` (F2): the constant function 1 is a square integrable eigenfunction with eigenvalue 0 for each subgroup. So the conditions of `IsL2Eigenfunction` are not contradictory.
* `Langlands.Fidelity.not_selbergEigenvalue_of_eigenvalue_zero` (F3): without the condition $\lambda \ne 0$, `SelbergEigenvalue` is false.
* `Langlands.Fidelity.heckeOperator_one`: $T_p 1 = (p^{1/2} + p^{-1/2}) \cdot 1$ in level 1. This shows the normalization of `heckeOperator`.
* `Langlands.Fidelity.two_lt_heckeEigenvalue_one` (F3): the constant function satisfies all the conditions of `RamanujanMaass` except the cuspidal condition, and its eigenvalue is larger than 2. So the cuspidal condition is necessary.
-/

namespace Langlands.Fidelity

open Langlands UpperHalfPlane CongruenceSubgroup MeasureTheory

open scoped MatrixGroups ContDiff Laplacian

/-- The full modular group is a congruence subgroup. -/
theorem isCongruenceSubgroup_top : IsCongruenceSubgroup (⊤ : Subgroup SL(2, ℤ)) :=
  ⟨1, one_ne_zero, le_top⟩

/-- The function $1 / y^2$ is integrable on the standard fundamental domain. So the fundamental domain has finite hyperbolic area. -/
theorem integrableOn_fd : IntegrableOn (fun z : ℂ => 1 / z.im ^ 2) ((↑) '' ModularGroup.fd) := by
  have hS : IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) * (1 / p.2 ^ 2))
      (Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioi (1 / 4)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Icc (-1 / 2 : ℝ) (1 / 2))) :=
      integrable_const _
    have h2 : Integrable (fun y : ℝ => 1 / y ^ 2) (volume.restrict (Set.Ioi (1 / 4 : ℝ))) := by
      have := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4)
      refine IntegrableOn.congr_fun this (fun y hy => ?_) measurableSet_Ioi
      have hy : 0 < y := lt_trans (by norm_num) (Set.mem_Ioi.1 hy)
      rw [Real.rpow_neg hy.le, one_div]
      norm_cast
    exact h1.mul_prod h2
  rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)] at hS
  have he : ((fun p : ℝ × ℝ => (1 : ℝ) * (1 / p.2 ^ 2)) ∘ Complex.measurableEquivRealProd) =
      fun z : ℂ => 1 / z.im ^ 2 := by
    funext z
    exact one_mul _
  rw [he] at hS
  refine hS.mono_set ?_
  rintro _ ⟨τ, ⟨h1, h2⟩, rfl⟩
  have hre := abs_le.1 h2
  have him := τ.im_pos
  rw [Complex.normSq_apply] at h1
  change ((τ : ℂ).re, (τ : ℂ).im) ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioi (1 / 4)
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1 ⊢
  refine ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ?_⟩
  show (1 / 4 : ℝ) < τ.im
  nlinarith

/-- The constant function 1 is a square integrable eigenfunction of the Laplacian with eigenvalue 0 for each subgroup. -/
theorem isL2Eigenfunction_one (Γ : Subgroup SL(2, ℤ)) : IsL2Eigenfunction Γ (fun _ => 1) 0 where
  smooth := contDiffOn_const
  invariant _ _ _ := rfl
  eigen τ := by
    have h : onPlane (fun _ : ℍ => (1 : ℂ)) = fun _ : ℂ => (1 : ℂ) := rfl
    simp [hyperbolicLaplacian, h]
  squareIntegrable _ := by simpa using integrableOn_fd

/-- F3 for `SelbergEigenvalue`: without the condition $\lambda \ne 0$ the statement is false, because of the constant functions. -/
theorem not_selbergEigenvalue_of_eigenvalue_zero :
    ¬ ∀ (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (ev : ℝ), IsCongruenceSubgroup Γ → f ≠ 0 →
      IsL2Eigenfunction Γ f ev → 1 / 4 ≤ ev := by
  intro h
  have := h ⊤ (fun _ => 1) 0 isCongruenceSubgroup_top
    (fun h1 => one_ne_zero (congrFun h1 UpperHalfPlane.I)) (isL2Eigenfunction_one ⊤)
  norm_num at this

/-- The Hecke operator $T_p$ of level 1 sends the constant function 1 to $(p^{1/2} + p^{-1/2}) \cdot 1$. This shows the normalization of `heckeOperator`. -/
theorem heckeOperator_one (p : ℕ) (hp : 0 < p) :
    heckeOperator (1 : DirichletCharacter ℂ 1) p (fun _ => 1) =
      ((Real.sqrt p + (Real.sqrt p)⁻¹ : ℝ) : ℂ) • fun _ => 1 := by
  funext τ
  have hχ : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
    rw [Subsingleton.elim (p : ZMod 1) 1, map_one]
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  have hp' : (p : ℂ) = ((Real.sqrt p : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
  have hs' : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [heckeOperator, hχ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_inv]
  rw [hp']
  field_simp
  ring

/-- F3 for `RamanujanMaass`: the constant function 1 of level 1 satisfies all the conditions of a Maass cusp form except the cuspidal condition, and its eigenvalue $p^{1/2} + p^{-1/2}$ for $T_p$ is larger than 2. So the cuspidal condition is necessary. -/
theorem two_lt_heckeEigenvalue_one (p : ℕ) (hp : p.Prime) :
    IsL2Eigenfunction (Gamma1 1) (fun _ => 1) 0 ∧
      (∀ γ ∈ Gamma0 1, ∀ τ : ℍ, (fun _ : ℍ => (1 : ℂ)) (γ • τ) =
        (1 : DirichletCharacter ℂ 1) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod 1) * 1) ∧
      heckeOperator (1 : DirichletCharacter ℂ 1) p (fun _ => 1) =
        ((Real.sqrt p + (Real.sqrt p)⁻¹ : ℝ) : ℂ) • (fun _ => 1) ∧
      2 < ‖((Real.sqrt p + (Real.sqrt p)⁻¹ : ℝ) : ℂ)‖ := by
  refine ⟨isL2Eigenfunction_one _, fun γ _ τ => ?_, heckeOperator_one p hp.pos, ?_⟩
  · rw [Subsingleton.elim (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod 1) 1, map_one, mul_one]
  · have h1 : 1 < Real.sqrt p := by
      rw [Real.lt_sqrt zero_le_one]
      exact_mod_cast (by simpa using hp.one_lt : 1 ^ 2 < p)
    have hs : 0 < Real.sqrt p := lt_trans one_pos h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← sub_pos]
    have : Real.sqrt p + (Real.sqrt p)⁻¹ - 2 = (Real.sqrt p - 1) ^ 2 / Real.sqrt p := by
      field_simp
      ring
    rw [this]
    exact div_pos (pow_pos (sub_pos.2 h1) 2) hs

end Langlands.Fidelity

