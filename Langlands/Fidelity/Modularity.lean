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
-/

namespace Langlands.Fidelity

open Real

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

end Langlands.Fidelity
