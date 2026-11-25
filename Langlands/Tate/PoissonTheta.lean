/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.PoissonLattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform


/-!
# The theta transformation formula

Let $V$ be a real inner product space of dimension $n$ and let $L \subset V$ be a full lattice. The theta function of $L$ is $\theta_L(t) = \sum_{\ell \in L} e^{-\pi t |\ell|^2}$ for $t > 0$. This file proves the transformation formula $$\theta_L(t) = \frac{1}{\mathrm{covol}(L) \, t^{n/2}} \, \theta_{L^\vee}(1/t),$$ where $L^\vee$ is the dual lattice for the inner product of $V$.

## Main results

* `Langlands.Tate.tsum_zlattice_gaussian`: the transformation formula above.
* `Langlands.Tate.tsum_add_zlattice_gaussian`: the version with a shift $x \in V$, $$\sum_{\ell \in L} e^{-\pi t |x + \ell|^2} = \frac{1}{\mathrm{covol}(L) \, t^{n/2}} \sum_{\mu \in L^\vee} e^{-\pi |\mu|^2 / t} e^{2 \pi i \langle x, \mu \rangle}.$$
* `Langlands.Tate.fourier_gaussian`: $\mathcal{F}(e^{-\pi t |v|^2})(w) = t^{-n/2} e^{-\pi |w|^2 / t}$.
* `Langlands.Tate.hasDecay_gaussian`: a Gaussian decays faster than each power of $|v|$.

## Proof

Apply the Poisson summation formula `Langlands.Tate.tsum_add_zlattice_eq_of_hasDecay` to the Gaussian $f(v) = e^{-\pi t |v|^2}$. Its Fourier transform comes from `fourier_gaussian_innerProductSpace` in Mathlib. The decay hypotheses follow from the explicit bound $(1 + r)^N e^{-a r^2} \le N! \, e^{1 + 1 / (4 a)}$ (`Langlands.Tate.one_add_pow_mul_exp_le`). The Fourier transform is again a Gaussian, so it is summable on $L^\vee$.

The conventions for the covolume, the dual lattice and the Fourier transform are those of `Langlands.Tate.PoissonLattice`.

## References

* J. Neukirch, Algebraic number theory, chapter VII, section 8.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.2.
-/

open MeasureTheory Complex FourierTransform Module
open scoped RealInnerProductSpace

namespace Langlands.Tate

/-- An explicit bound for a Gaussian: for $a > 0$ and $r \ge 0$, $(1 + r)^N e^{-a r^2} \le N! \, e^{1 + 1 / (4 a)}$. The proof uses $(1 + r)^N \le N! \, e^{1 + r}$ and $r - a r^2 \le 1 / (4 a)$. -/
theorem one_add_pow_mul_exp_le {a : ℝ} (ha : 0 < a) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-a * r ^ 2) ≤ N.factorial * Real.exp (1 + 1 / (4 * a)) := by
  have h1 : (1 + r) ^ N ≤ N.factorial * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : r - a * r ^ 2 ≤ 1 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * r - 1)]
  calc (1 + r) ^ N * Real.exp (-a * r ^ 2)
      ≤ N.factorial * Real.exp (1 + r) * Real.exp (-a * r ^ 2) := by gcongr
    _ = N.factorial * Real.exp (1 + (r - a * r ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ N.factorial * Real.exp (1 + 1 / (4 * a)) := by gcongr

/-- For $a > 0$, the Gaussian $v \mapsto e^{-a |v|^2}$ decays of each order $N$. -/
theorem hasDecay_gaussian {E : Type*} [NormedAddCommGroup E] {a : ℝ} (ha : 0 < a) (N : ℕ) :
    HasDecay (fun v : E => (Real.exp (-a * ‖v‖ ^ 2) : ℂ)) N :=
  ⟨_, fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact one_add_pow_mul_exp_le ha N (norm_nonneg v)⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of a Gaussian on an inner product space $V$ of dimension $n$: for $t > 0$, $$\mathcal{F}\left(e^{-\pi t |v|^2}\right)(w) = t^{-n/2} e^{-\pi |w|^2 / t}.$$ -/
theorem fourier_gaussian {t : ℝ} (ht : 0 < t) (w : V) :
    𝓕 (fun v : V => (Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) : ℂ)) w =
      ((t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ : ℝ) * (Real.exp (-(Real.pi / t) * ‖w‖ ^ 2) : ℂ) := by
  have hb : 0 < ((Real.pi * t : ℝ) : ℂ).re := by simpa using mul_pos Real.pi_pos ht
  have h := fourier_gaussian_innerProductSpace hb w
  have hfun : (fun v : V => (Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) : ℂ)) =
      fun v : V => cexp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2) := by
    funext v; rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [hfun, h]
  have h1 : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast; field_simp
  have h2 : ((finrank ℝ V : ℂ) / 2) = (((finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2, ← Complex.ofReal_cpow (inv_nonneg.2 ht.le), Real.inv_rpow ht.le, Complex.ofReal_exp]
  congr 2
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast; field_simp

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The theta transformation formula with a shift.** For $t > 0$ and $x \in V$, $$\sum_{\ell \in L} e^{-\pi t |x + \ell|^2} = \frac{1}{\mathrm{covol}(L) \, t^{n/2}} \sum_{\mu \in L^\vee} e^{-\pi |\mu|^2 / t} e^{2 \pi i \langle x, \mu \rangle}.$$ -/
theorem tsum_add_zlattice_gaussian {t : ℝ} (ht : 0 < t) (x : V) :
    ∑' ℓ : L, (Real.exp (-(Real.pi * t) * ‖x + ℓ‖ ^ 2) : ℂ) =
      ((ZLattice.covolume L)⁻¹ * (t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ : ℝ) *
        ∑' μ : dualLattice L, (Real.exp (-(Real.pi / t) * ‖(μ : V)‖ ^ 2) : ℂ) *
          cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) := by
  set g : V → ℂ := fun v => (Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) : ℂ)
  have hc : Continuous g := by fun_prop
  have hN : finrank ℝ V < finrank ℝ V + 1 := Nat.lt_succ_self _
  have hF : Summable fun μ : dualLattice L => 𝓕 g μ := by
    simp only [g, fourier_gaussian ht]
    exact (summable_dualLattice_of_hasDecay L
      (hasDecay_gaussian (div_pos Real.pi_pos ht) _) hN).mul_left _
  have := tsum_add_zlattice_eq_of_hasDecay L hc
    (hasDecay_gaussian (mul_pos Real.pi_pos ht) _) hN hF x
  simp only [g, fourier_gaussian ht, mul_assoc] at this
  rw [this, tsum_mul_left]
  push_cast
  ring_nf

/-- **The theta transformation formula.** For $t > 0$, $$\sum_{\ell \in L} e^{-\pi t |\ell|^2} = \frac{1}{\mathrm{covol}(L) \, t^{n/2}} \sum_{\mu \in L^\vee} e^{-\pi |\mu|^2 / t},$$ where $n = \dim V$. In terms of $\theta_L(t) = \sum_{\ell \in L} e^{-\pi t |\ell|^2}$ this is $\theta_L(t) = \mathrm{covol}(L)^{-1} t^{-n/2} \theta_{L^\vee}(1/t)$. -/
theorem tsum_zlattice_gaussian {t : ℝ} (ht : 0 < t) :
    ∑' ℓ : L, Real.exp (-(Real.pi * t) * ‖(ℓ : V)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * (t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ *
        ∑' μ : dualLattice L, Real.exp (-(Real.pi / t) * ‖(μ : V)‖ ^ 2) := by
  apply Complex.ofReal_injective
  push_cast [Complex.ofReal_tsum]
  simpa using tsum_add_zlattice_gaussian L ht 0

end Langlands.Tate
