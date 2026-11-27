/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Modularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fidelity checks for the statements of modularity

This file has checks F2 and F3 of spec 06.3 for the statements of `Langlands.Statements.Modularity`.

* `Langlands.Fidelity.satoTate_total_mass`: the Sato-Tate measure $\frac{2}{\pi} \sin^2 \theta \, d\theta$ has total mass 1 on $[0, \pi]$. A wrong constant in `SatoTate` makes the statement false for $\alpha = 0$ and $\beta = \pi$, and this lemma rules that out.
* `Langlands.Fidelity.hasCMOverQ_congruentNumber`: the curve $y^2 = x^3 - x$ has $j = 1728$, so it has complex multiplication by $\mathbb{Z}[i]$ in the sense of `HasCMOverQ`.
* `Langlands.Fidelity.not_hasCMOverQ_X0_11`: the curve $X_0(11)$, $y^2 + y = x^3 - x^2 - 10x - 20$, has $j = -122023936/161051$ and no complex multiplication. So the hypothesis of `SatoTate` is not empty.
* `Langlands.Fidelity.satoTate_full` (F2): the conclusion of `SatoTate` holds for the interval $[0, \pi]$ and each elliptic curve.
* `Langlands.Fidelity.not_satoTateUniform` (F3): `SatoTate` contradicts the variant with the uniform measure $d\theta / \pi$. The two limits differ on $[0, \pi/4]$ for $X_0(11)$. So the measure in the statement does work.
* `Langlands.Fidelity.modularitySemistableQ_of_modularityEllipticQ` (F2): `ModularityEllipticQ` implies `ModularitySemistableQ`, as the published theorems do.
-/

namespace Langlands.Fidelity

open Real Filter Topology

/-- The Sato-Tate measure is a probability measure on $[0, \pi]$. -/
theorem satoTate_total_mass : (2 / π) * ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 2 = 1 := by
  rw [integral_sin_sq]
  simp

/-- The curve $y^2 = x^3 - x$ over $\mathbb{Q}$. -/
def congruentNumberCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

theorem congruentNumberCurve_Δ : congruentNumberCurve.Δ = 64 := by
  norm_num [congruentNumberCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : congruentNumberCurve.IsElliptic :=
  ⟨by rw [congruentNumberCurve_Δ]; norm_num⟩

theorem congruentNumberCurve_j : congruentNumberCurve.j = 1728 := by
  rw [WeierstrassCurve.j_eq, congruentNumberCurve_Δ]
  norm_num [congruentNumberCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

/-- The curve $y^2 = x^3 - x$ has complex multiplication. -/
theorem hasCMOverQ_congruentNumber : HasCMOverQ congruentNumberCurve := by
  rw [HasCMOverQ, congruentNumberCurve_j]
  simp [cmJInvariants]

/-- The curve $X_0(11)$: $y^2 + y = x^3 - x^2 - 10x - 20$, of conductor 11. -/
def X0_11 : WeierstrassCurve ℚ := ⟨0, -1, 1, -10, -20⟩

theorem X0_11_Δ : X0_11.Δ = -161051 := by
  norm_num [X0_11, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : X0_11.IsElliptic :=
  ⟨by rw [X0_11_Δ]; norm_num⟩

theorem X0_11_j : X0_11.j = -122023936 / 161051 := by
  rw [WeierstrassCurve.j_eq, X0_11_Δ]
  norm_num [X0_11, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

/-- The curve $X_0(11)$ has no complex multiplication, so it is an instance of the hypothesis of `SatoTate`. -/
theorem not_hasCMOverQ_X0_11 : ¬ HasCMOverQ X0_11 := by
  rw [HasCMOverQ, X0_11_j]
  simp only [cmJInvariants, Set.mem_insert_iff, Set.mem_singleton_iff]
  norm_num

/-- **F2 for `SatoTate`.** For the interval $[0, \pi]$ the conclusion of `SatoTate` holds for each elliptic curve, because each angle is in $[0, \pi]$ and the measure has total mass 1. -/
theorem satoTate_full (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Tendsto
      (fun x : ℕ =>
        (Nat.card {p : ℕ // p.Prime ∧ p ≤ x ∧ satoTateAngle E p ∈ Set.Icc 0 π} : ℝ) /
          Nat.card {p : ℕ // p.Prime ∧ p ≤ x})
      atTop (𝓝 ((2 / π) * ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 2)) := by
  rw [satoTate_total_mass]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hset : {p : ℕ // p.Prime ∧ p ≤ x ∧ satoTateAngle E p ∈ Set.Icc 0 π} =
      {p : ℕ // p.Prime ∧ p ≤ x} := by
    congr 1
    ext p
    simp only [satoTateAngle, Set.mem_Icc, Real.arccos_nonneg, Real.arccos_le_pi, and_true]
  have hfin : Finite {p : ℕ // p.Prime ∧ p ≤ x} :=
    ((Set.finite_Iic x).subset (t := {p : ℕ | p.Prime ∧ p ≤ x}) fun p hp => hp.2).to_subtype
  have hpos : 0 < Nat.card {p : ℕ // p.Prime ∧ p ≤ x} :=
    have : Nonempty {p : ℕ // p.Prime ∧ p ≤ x} := ⟨⟨2, Nat.prime_two, hx⟩⟩
    Nat.card_pos
  rw [hset, div_self]
  exact_mod_cast hpos.ne'

/-- The variant of `SatoTate` with the uniform measure $d\theta / \pi$ in place of the Sato-Tate measure. -/
def SatoTateUniform : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ¬ HasCMOverQ E →
    ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ π →
      Tendsto
        (fun x : ℕ =>
          (Nat.card {p : ℕ // p.Prime ∧ p ≤ x ∧ satoTateAngle E p ∈ Set.Icc α β} : ℝ) /
            Nat.card {p : ℕ // p.Prime ∧ p ≤ x})
        atTop (𝓝 ((β - α) / π))

/-- The Sato-Tate measure of $[0, \pi/4]$ is $1/4 - 1/(2\pi)$. -/
theorem satoTate_mass_quarter : (2 / π) * ∫ θ in (0 : ℝ)..(π / 4), Real.sin θ ^ 2 = 1 / 4 - 1 / (2 * π) := by
  rw [integral_sin_sq, sin_pi_div_four, cos_pi_div_four]
  have hπ : π ≠ 0 := pi_ne_zero
  have h2 : (√2 / 2) * (√2 / 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  simp only [sin_zero, cos_zero, zero_mul, h2]
  field_simp
  ring

/-- **F3 for `SatoTate`.** The statement fixes the measure: with `SatoTate`, the variant with the uniform measure is false, for the curve $X_0(11)$ and the interval $[0, \pi/4]$. -/
theorem not_satoTateUniform (h : SatoTate) : ¬ SatoTateUniform := by
  intro hu
  have h1 := h X0_11 not_hasCMOverQ_X0_11 0 (π / 4) le_rfl (by positivity) (by linarith [pi_pos])
  have h2 := hu X0_11 not_hasCMOverQ_X0_11 0 (π / 4) le_rfl (by positivity) (by linarith [pi_pos])
  have := tendsto_nhds_unique h1 h2
  rw [satoTate_mass_quarter] at this
  have hπ : 0 < π := pi_pos
  field_simp at this
  nlinarith [pi_pos]

/-- **F2 for `ModularityEllipticQ`.** The statement implies the semistable case of Wiles and Taylor-Wiles. -/
theorem modularitySemistableQ_of_modularityEllipticQ (h : ModularityEllipticQ) :
    ModularitySemistableQ :=
  fun E _ _ => h E

end Langlands.Fidelity
