/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.NonArchimedeanMeasure

/-!
# Fourier transforms of balls on a nonarchimedean completion

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$ and norm $q = N(v)$. Let $dx$ be the Haar measure `haar v` with $\int_{\mathcal{O}_v} dx = 1$, as in `Langlands.Tate.NonArchimedeanMeasure`. Let $\psi : K_v \to \mathbb{C}$ be an additive character. The Fourier transform of a function $f$ on $K_v$ is
$$\hat{f}(y) = \int_{K_v} f(x) \psi(x y) \, dx.$$
This is the convention of Tate's thesis: there is no minus sign in $\psi(xy)$.

This file computes the Fourier transform of the indicator function of a ball for any additive character $\psi$. It does not construct a particular character.

## Conventions

We say that $\psi$ has conductor exponent $d \in \mathbb{Z}$ when $\psi$ is trivial on the ball $\{x : |x|_v \leq q^d\}$ but not on the ball $\{x : |x|_v \leq q^{d+1}\}$. In terms of ideals, $\psi$ is trivial on $\mathfrak{p}_v^{-d}$ and not on $\mathfrak{p}_v^{-d-1}$. For the standard character $\psi_v = \psi_p \circ \mathrm{Tr}_{K_v / \mathbb{Q}_p}$ the largest fractional ideal on which $\psi_v$ is trivial is the inverse different $\mathfrak{d}_v^{-1}$, so $d$ is the valuation of the different and $q^d = N(\mathfrak{d}_v)$.

## Main results

* `setIntegral_closedBall_addChar_of_ne_one`: if $\psi(a) \neq 1$ for some $a$ in a ball $B$ around $0$, then $\int_B \psi(x) \, dx = 0$.
* `setIntegral_closedBall_addChar_of_forall`: if $\psi$ is trivial on $B$, then $\int_B \psi(x) \, dx = \mu(B)$.
* `fourier_indicator_closedBall`: for any $\psi$ and $a \neq 0$, the Fourier transform of $\mathbf{1}_{a \mathcal{O}_v}$ at $y$ is $|a|_v$ if $\psi$ is trivial on $a y \mathcal{O}_v$ and $0$ otherwise.
* `fourier_indicator_closedBall_of_conductor`: if $\psi$ has conductor exponent $d$, then the Fourier transform of $\mathbf{1}_{a \mathcal{O}_v}$ is $|a|_v \mathbf{1}_{\{|y|_v \leq q^d / |a|_v\}}$.
* `fourier_indicator_integers`: if $\psi$ has conductor exponent $d$, then $\hat{\mathbf{1}}_{\mathcal{O}_v} = \mathbf{1}_{\{|y|_v \leq q^d\}}$. For the standard character this is $\mu(\mathcal{O}_v) \mathbf{1}_{\mathfrak{d}_v^{-1}}$.
* `fourier_fourier_indicator_integers`: if $\psi$ has conductor exponent $d$, then the double transform of $\mathbf{1}_{\mathcal{O}_v}$ is $q^d \mathbf{1}_{\mathcal{O}_v}$. So the Fourier inversion formula $\hat{\hat{f}}(x) = f(-x)$ holds for $f = \mathbf{1}_{\mathcal{O}_v}$ exactly for the measure $q^{-d/2} dx$. This identifies the self dual measure.

## Proofs

The key fact is the orthogonality of characters on a compact group. A ball $B$ around $0$ is an additive subgroup, because the norm is ultrametric. If $a \in B$, then the translation $x \mapsto x + a$ maps $B$ to $B$, and it preserves $dx$. So $I = \int_B \psi(x) \, dx$ satisfies $I = \int_B \psi(x + a) \, dx = \psi(a) I$. If $\psi(a) \neq 1$, then $I = 0$. This argument does not need integrability, because both sides are Bochner integrals of the same kind.

For the transform of $\mathbf{1}_{a \mathcal{O}_v}$ we apply orthogonality to the character $x \mapsto \psi(xy)$ on the ball $a \mathcal{O}_v$. Its image under multiplication by $y$ is the ball $a y \mathcal{O}_v$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.2.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, chapter 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- A ball $B$ around $0$ in $K_v$ is stable under translation by an element $a \in B$: $x + a \in B$ if and only if $x \in B$. -/
theorem add_mem_closedBall_iff {r : ℝ} {a : v.adicCompletion K} (ha : a ∈ closedBall 0 r)
    (x : v.adicCompletion K) : x + a ∈ closedBall 0 r ↔ x ∈ closedBall 0 r := by
  rw [mem_closedBall_zero_iff] at ha ⊢
  rw [mem_closedBall_zero_iff]
  constructor
  · intro h
    calc ‖x‖ = ‖(x + a) + -a‖ := by rw [add_neg_cancel_right]
      _ ≤ max ‖x + a‖ ‖-a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le h (by rwa [norm_neg])
  · intro h
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h ha)

/-- Translation by an element $a$ of a ball $B$ around $0$ multiplies the function $\mathbf{1}_B \psi$ by $\psi(a)$. -/
theorem indicator_addChar_add {r : ℝ} {a : v.adicCompletion K} (ha : a ∈ closedBall 0 r)
    (ψ : AddChar (v.adicCompletion K) ℂ) (x : v.adicCompletion K) :
    (closedBall 0 r).indicator ψ (x + a) = (closedBall 0 r).indicator ψ x * ψ a := by
  by_cases hx : x ∈ closedBall 0 r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_mem_closedBall_iff v ha x).2 hx),
      AddChar.map_add_eq_mul]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((add_mem_closedBall_iff v ha x).1 h)), zero_mul]

/-- Orthogonality: if an additive character $\psi$ is not trivial on a ball $B$ around $0$, then $\int_B \psi(x) \, dx = 0$. -/
theorem setIntegral_closedBall_addChar_of_ne_one (ψ : AddChar (v.adicCompletion K) ℂ) {r : ℝ}
    {a : v.adicCompletion K} (ha : a ∈ closedBall 0 r) (hψ : ψ a ≠ 1) :
    ∫ x in closedBall 0 r, ψ x ∂haar v = 0 := by
  rw [← integral_indicator measurableSet_closedBall]
  have h : ∫ x, (closedBall 0 r).indicator ψ x ∂haar v =
      (∫ x, (closedBall 0 r).indicator ψ x ∂haar v) * ψ a :=
    calc ∫ x, (closedBall 0 r).indicator ψ x ∂haar v
        = ∫ x, (closedBall 0 r).indicator ψ (x + a) ∂haar v :=
          (integral_add_right_eq_self _ a).symm
      _ = ∫ x, (closedBall 0 r).indicator ψ x * ψ a ∂haar v :=
          integral_congr_ae (Filter.Eventually.of_forall (indicator_addChar_add v ha ψ))
      _ = (∫ x, (closedBall 0 r).indicator ψ x ∂haar v) * ψ a := integral_mul_const _ _
  have h1 : (∫ x, (closedBall 0 r).indicator ψ x ∂haar v) * (1 - ψ a) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 (Ne.symm hψ))

/-- If an additive character $\psi$ is trivial on a ball $B$ around $0$, then $\int_B \psi(x) \, dx = \mu(B)$. -/
theorem setIntegral_closedBall_addChar_of_forall (ψ : AddChar (v.adicCompletion K) ℂ) {r : ℝ}
    (hψ : ∀ x ∈ closedBall (0 : v.adicCompletion K) r, ψ x = 1) :
    ∫ x in closedBall 0 r, ψ x ∂haar v = (haar v).real (closedBall 0 r) := by
  rw [setIntegral_congr_fun measurableSet_closedBall hψ, setIntegral_const, Complex.real_smul,
    mul_one]

/-- The Fourier transform $\hat{f}(y) = \int_{K_v} f(x) \psi(x y) \, dx$ of a function $f$ on $K_v$ with respect to an additive character $\psi$ and the Haar measure with $\mu(\mathcal{O}_v) = 1$. -/
noncomputable def fourier (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    (y : v.adicCompletion K) : ℂ :=
  ∫ x, f x * ψ (x * y) ∂haar v

/-- The Fourier transform of $\mathbf{1}_B$ for a ball $B$ around $0$ is $\hat{\mathbf{1}}_B(y) = \int_B \psi(y x) \, dx$. -/
theorem fourier_indicator_eq_setIntegral (ψ : AddChar (v.adicCompletion K) ℂ) (r : ℝ)
    (y : v.adicCompletion K) :
    fourier v ψ ((closedBall 0 r).indicator 1) y = ∫ x in closedBall 0 r, ψ.mulShift y x ∂haar v := by
  rw [fourier, ← integral_indicator measurableSet_closedBall]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall 0 r
  · simp [Set.indicator_of_mem hx, mul_comm x y]
  · simp [Set.indicator_of_notMem hx]

open Classical in
/-- For $a \neq 0$ and any additive character $\psi$, the Fourier transform of $\mathbf{1}_{a \mathcal{O}_v}$ at $y$ is $|a|_v$ if $\psi$ is trivial on the ball $\{x : |x|_v \leq |a|_v |y|_v\} = a y \mathcal{O}_v$, and $0$ otherwise. -/
theorem fourier_indicator_closedBall (ψ : AddChar (v.adicCompletion K) ℂ)
    {a : v.adicCompletion K} (ha : a ≠ 0) (y : v.adicCompletion K) :
    fourier v ψ ((closedBall 0 ‖a‖).indicator 1) y =
      if ∀ x ∈ closedBall (0 : v.adicCompletion K) (‖a‖ * ‖y‖), ψ x = 1 then (‖a‖ : ℂ)
      else 0 := by
  rw [fourier_indicator_eq_setIntegral]
  split_ifs with h
  · rw [setIntegral_closedBall_addChar_of_forall v _ fun x hx => ?_, Measure.real,
      haar_closedBall_norm v ha, ENNReal.toReal_ofReal (norm_nonneg a)]
    rw [AddChar.mulShift_apply]
    refine h _ ?_
    rw [mem_closedBall_zero_iff] at hx ⊢
    rw [norm_mul, mul_comm ‖a‖]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg y)
  · push Not at h
    obtain ⟨z, hz, hψz⟩ := h
    have hy : y ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, mem_closedBall_zero_iff, norm_le_zero_iff] at hz
      exact hψz (hz ▸ AddChar.map_zero_eq_one ψ)
    refine setIntegral_closedBall_addChar_of_ne_one v _ (a := z / y) ?_ ?_
    · rw [mem_closedBall_zero_iff] at hz ⊢
      rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hy)]
      exact hz
    · rwa [AddChar.mulShift_apply, mul_div_cancel₀ z hy]

/-- If $\psi$ is trivial on the ball of radius $q^d$ and not on the ball of radius $q^{d+1}$, then $\psi$ is trivial on the ball of radius $|b|_v$ if and only if $|b|_v \leq q^d$. -/
theorem forall_closedBall_norm_iff (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (b : v.adicCompletion K) :
    (∀ x ∈ closedBall (0 : v.adicCompletion K) ‖b‖, ψ x = 1) ↔ ‖b‖ ≤ q v ^ d := by
  constructor
  · intro h
    by_contra hb
    rw [not_le] at hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hb
      exact (zpow_pos (q_pos v) d).not_gt hb
    obtain ⟨k, hk⟩ := exists_norm_eq_zpow v hb0
    rw [hk, zpow_lt_zpow_iff_right₀ (one_lt_q v)] at hb
    obtain ⟨x, hx, hψx⟩ := h2
    refine hψx (h x ?_)
    rw [mem_closedBall_zero_iff, hk]
    exact hx.trans (zpow_le_zpow_right₀ (one_lt_q v).le (by omega))
  · intro hb x hx
    rw [mem_closedBall_zero_iff] at hx
    exact h1 x (hx.trans hb)

/-- If $\psi$ has conductor exponent $d$, then for $a \neq 0$ the Fourier transform of $\mathbf{1}_{a \mathcal{O}_v}$ is $|a|_v \mathbf{1}_{\{y : |y|_v \leq q^d / |a|_v\}}$. -/
theorem fourier_indicator_closedBall_of_conductor (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {a : v.adicCompletion K} (ha : a ≠ 0) :
    fourier v ψ ((closedBall 0 ‖a‖).indicator 1) =
      (closedBall 0 (q v ^ d / ‖a‖)).indicator fun _ => (‖a‖ : ℂ) := by
  funext y
  have key : (∀ x ∈ closedBall (0 : v.adicCompletion K) (‖a‖ * ‖y‖), ψ x = 1) ↔
      y ∈ closedBall 0 (q v ^ d / ‖a‖) := by
    rw [← norm_mul, forall_closedBall_norm_iff v ψ d h1 h2, mem_closedBall_zero_iff,
      le_div_iff₀ (norm_pos_iff.2 ha), norm_mul, mul_comm ‖a‖]
  classical
  rw [fourier_indicator_closedBall v ψ ha, Set.indicator_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (key.1 h₁) h₂
  · exact absurd (key.2 h₂) h₁
  · rfl

/-- If $\psi$ has conductor exponent $d$, then $\hat{\mathbf{1}}_{\mathcal{O}_v} = \mathbf{1}_{\{y : |y|_v \leq q^d\}}$. For the standard character this says $\hat{\mathbf{1}}_{\mathcal{O}_v} = \mu(\mathcal{O}_v) \mathbf{1}_{\mathfrak{d}_v^{-1}}$. -/
theorem fourier_indicator_integers (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) :
    fourier v ψ ((closedBall 0 1).indicator 1) = (closedBall 0 (q v ^ d)).indicator 1 := by
  have h := fourier_indicator_closedBall_of_conductor v ψ d h1 h2 (one_ne_zero)
  rw [norm_one, div_one, Complex.ofReal_one] at h
  exact h

/-- Every integral power $q^k$ is the absolute value of an element of $K_v$, namely $\varpi^{-k}$. -/
theorem exists_norm_eq_q_zpow (k : ℤ) : ∃ a : v.adicCompletion K, a ≠ 0 ∧ ‖a‖ = q v ^ k := by
  refine ⟨(localUniformizer K v : v.adicCompletion K) ^ (-k), ?_, ?_⟩
  · exact zpow_ne_zero _ (Units.ne_zero _)
  · rw [norm_zpow, norm_localUniformizer, inv_zpow', neg_neg]

/-- If $\psi$ has conductor exponent $d$, then the double Fourier transform of $\mathbf{1}_{\mathcal{O}_v}$ is $q^d \mathbf{1}_{\mathcal{O}_v}$. So the self dual Haar measure for $\psi$ is $q^{-d/2} dx$. -/
theorem fourier_fourier_indicator_integers (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) :
    fourier v ψ (fourier v ψ ((closedBall 0 1).indicator 1)) =
      (closedBall 0 1).indicator fun _ => ((q v ^ d : ℝ) : ℂ) := by
  obtain ⟨a, ha, hna⟩ := exists_norm_eq_q_zpow v d
  rw [fourier_indicator_integers v ψ d h1 h2, ← hna,
    fourier_indicator_closedBall_of_conductor v ψ d h1 h2 ha, hna,
    div_self (zpow_pos (q_pos v) d).ne']

end Langlands.Tate.NonArchimedean
