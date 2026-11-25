/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The archimedean Gamma factors

This file records the facts about $\Gamma_\mathbb{R}(s) = \pi^{-s/2} \Gamma(s / 2)$ and $\Gamma_\mathbb{C}(s) = 2 (2 \pi)^{-s} \Gamma(s)$ that the global part of Tate's thesis needs. The functions are `Complex.Gammaℝ` and `Complex.Gammaℂ` of Mathlib.

Mathematically $\Gamma_\mathbb{R}$ and $\Gamma_\mathbb{C}$ are meromorphic on $\mathbb{C}$ and have no zeros. The poles of $\Gamma_\mathbb{R}$ are the points $-2m$ and the poles of $\Gamma_\mathbb{C}$ are the points $-m$, for $m \in \mathbb{N}$. They are all simple. Mathlib gives the Gamma function the value $0$ at its poles. So the Lean functions vanish exactly at the poles (`Langlands.Tate.Gammaℝ_ne_zero_iff` and `Langlands.Tate.Gammaℂ_ne_zero_iff`), and they are analytic at every point where they do not vanish.

## Main results

* `Langlands.Tate.Gammaℂ_ne_zero_of_re_pos`: $\Gamma_\mathbb{C}(s) \neq 0$ for $\mathrm{Re}(s) > 0$. The same fact for $\Gamma_\mathbb{R}$ is `Complex.Gammaℝ_ne_zero_of_re_pos`.
* `Langlands.Tate.meromorphicOn_Gammaℝ` and `Langlands.Tate.meromorphicOn_Gammaℂ`: the functions are meromorphic on $\mathbb{C}$.
* `Langlands.Tate.analyticAt_Gammaℝ` and `Langlands.Tate.analyticAt_Gammaℂ`: the functions are analytic at each point where they are not zero, that is, away from the poles.
* The inverses $1 / \Gamma_\mathbb{R}$ and $1 / \Gamma_\mathbb{C}$ are entire. This is `Complex.differentiable_Gammaℝ_inv` and `Complex.differentiable_Gammaℂ_inv` of Mathlib.

The proofs use that $1 / \Gamma$ is entire: a function whose inverse is entire is meromorphic, and it is analytic where it does not vanish.
-/

namespace Langlands.Tate

open Complex

/-- $\Gamma_\mathbb{C}(s) \neq 0$ for $\mathrm{Re}(s) > 0$. -/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))

/-- The value of $\Gamma_\mathbb{R}$ is zero exactly at the poles $-2m$, $m \in \mathbb{N}$, where Mathlib gives it the value $0$. -/
theorem Gammaℝ_ne_zero_iff {s : ℂ} : Gammaℝ s ≠ 0 ↔ ∀ m : ℕ, s ≠ -(2 * m) := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  push Not
  rfl

/-- $\Gamma_\mathbb{C}(s) = 0$ exactly at the poles $-m$, $m \in \mathbb{N}$, where Mathlib gives it the value $0$. -/
theorem Gammaℂ_eq_zero_iff {s : ℂ} : Gammaℂ s = 0 ↔ ∃ m : ℕ, s = -m := by
  rw [Gammaℂ_def, ← Gamma_eq_zero_iff]
  have h : (2 : ℂ) * (2 * Real.pi : ℂ) ^ (-s) ≠ 0 :=
    mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.two_pi_pos.ne')))
  exact ⟨fun h' => (mul_eq_zero.mp h').resolve_left h, fun h' => by rw [h', mul_zero]⟩

/-- The value of $\Gamma_\mathbb{C}$ is not zero away from the poles $-m$, $m \in \mathbb{N}$. -/
theorem Gammaℂ_ne_zero_iff {s : ℂ} : Gammaℂ s ≠ 0 ↔ ∀ m : ℕ, s ≠ -m := by
  rw [Ne, Gammaℂ_eq_zero_iff]
  push Not
  rfl

/-- A function whose inverse is entire is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_of_differentiable_inv {f : ℂ → ℂ} (hf : Differentiable ℂ (fun s => (f s)⁻¹))
    (U : Set ℂ) : MeromorphicOn f U := by
  intro s _
  have h := ((hf.analyticAt s).meromorphicAt).inv
  convert h using 1
  ext z
  simp

/-- A function whose inverse is entire is analytic at each point where it does not vanish. -/
theorem analyticAt_of_differentiable_inv {f : ℂ → ℂ} (hf : Differentiable ℂ (fun s => (f s)⁻¹))
    {s : ℂ} (hs : f s ≠ 0) : AnalyticAt ℂ f s := by
  have h := (hf.analyticAt s).inv (inv_ne_zero hs)
  convert h using 1
  ext z
  simp

/-- $\Gamma_\mathbb{R}$ is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_Gammaℝ (U : Set ℂ) : MeromorphicOn Gammaℝ U :=
  meromorphicOn_of_differentiable_inv differentiable_Gammaℝ_inv U

/-- $\Gamma_\mathbb{C}$ is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_Gammaℂ (U : Set ℂ) : MeromorphicOn Gammaℂ U :=
  meromorphicOn_of_differentiable_inv differentiable_Gammaℂ_inv U

/-- $\Gamma_\mathbb{R}$ is analytic away from its poles. -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : Gammaℝ s ≠ 0) : AnalyticAt ℂ Gammaℝ s :=
  analyticAt_of_differentiable_inv differentiable_Gammaℝ_inv hs

/-- $\Gamma_\mathbb{C}$ is analytic away from its poles. -/
theorem analyticAt_Gammaℂ {s : ℂ} (hs : Gammaℂ s ≠ 0) : AnalyticAt ℂ Gammaℂ s :=
  analyticAt_of_differentiable_inv differentiable_Gammaℂ_inv hs

end Langlands.Tate
