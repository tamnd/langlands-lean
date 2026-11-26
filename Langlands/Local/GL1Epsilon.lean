/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1LFactor

/-!
# Tate's local functional equation for $GL_1$

Let $K$ be a nonarchimedean local field with residue field of size $q$, uniformizer $\varpi$ and Haar measure $\mu$. Let $\chi$ be a smooth character of $K^\times$ and let $\psi$ be an additive character of $K$ with conductor exponent $n$, so that $\psi$ is trivial on $\varpi^{-n} \mathcal{O}_K$ and not trivial on $\varpi^{-n-1} \mathcal{O}_K$. This file proves Tate's local functional equation $$\frac{Z(\hat{\varphi}, \chi^{-1}, 1 - s)}{L(1 - s, \chi^{-1})} = \varepsilon(s, \chi, \psi) \frac{Z(\varphi, \chi, s)}{L(s, \chi)}$$ for the standard test functions. For unramified $\chi$ the test function is $\varphi = \mathbf{1}_{\mathcal{O}_K}$. For $\chi$ of conductor exponent $a \ge 1$ the test function is $\varphi = \mathbf{1}_{1 + \mathfrak{p}^a}$. In both cases $\varepsilon(s, \chi, \psi) = c q^{-(a + n) s}$, with $a = 0$ in the unramified case. The file also computes the Fourier transform of translated balls and proves self-duality of the Haar measure on them.

## Main definitions

* `Langlands.LocalGL1.fourier`: the Fourier transform $\hat{\varphi}(\xi) = \int_K \varphi(x) \psi(x \xi) \, d\mu(x)$.
* `Langlands.LocalGL1.IsConductor`: the additive character $\psi$ has conductor exponent $n$.
* `Langlands.LocalGL1.IsRamifiedConductor`: the smooth character $\chi$ has conductor exponent $a \ge 1$.
* `Langlands.LocalGL1.oneAddBall`: the set $1 + \varpi^a \mathcal{O}_K$.
* `Langlands.LocalGL1.ballIndicator`: the indicator function of $b + \varpi^N \mathcal{O}_K$.
* `Langlands.LocalGL1.epsilonUnramified`: the factor $\mu(\mathcal{O}_K) \chi(\varpi)^n q^n q^{-ns}$.
* `Langlands.LocalGL1.gaussInt`: the Gauss integral $\int_{\varpi^k \mathcal{O}_K^\times} \psi(y) \chi^{-1}(y) \, dy$.

## Main results

* `Langlands.LocalGL1.integrable_indicator_zetaFn_of_lt`: the zeta integrand $\chi(y) |y|^{s - 1}$ is integrable on each bounded measurable set when $|\chi(\varpi) q^{-s}| < 1$.
* `Langlands.LocalGL1.fourier_indicator_ordBall`: the Fourier transform of $\mathbf{1}_{\varpi^N \mathcal{O}_K}$ is $\mu(\varpi^N \mathcal{O}_K) \mathbf{1}_{\varpi^{-n-N} \mathcal{O}_K}$.
* `Langlands.LocalGL1.fourier_fourier_ballIndicator`: Fourier inversion $\hat{\hat{\varphi}}(x) = \mu(\mathcal{O}_K)^2 q^n \varphi(-x)$ on translated balls.
* `Langlands.LocalGL1.existsUnique_selfDual`: there is a unique multiple $\nu$ of $\mu$ with $\nu(\mathcal{O}_K)^2 q^n = 1$. For $\nu$ the Fourier transform is self-dual on translated balls by `fourier_fourier_ballIndicator_of_selfDual`.
* `Langlands.LocalGL1.localFunctionalEquation_unramified`: the functional equation for unramified $\chi$ and $\varphi = \mathbf{1}_{\mathcal{O}_K}$, with $\varepsilon = \mu(\mathcal{O}_K) \chi(\varpi)^n q^n q^{-ns}$.
* `Langlands.LocalGL1.epsilonUnramified_eq`: this factor has the form $c q^{-ns}$ with $c \ne 0$.
* `Langlands.LocalGL1.localFunctionalEquation_ramified`: the functional equation for $\chi$ of conductor exponent $a \ge 1$ and $\varphi = \mathbf{1}_{1 + \mathfrak{p}^a}$, with $\varepsilon = G(\chi, \psi) q^{-(a + n) s}$ and $L(s, \chi) = L(1 - s, \chi^{-1}) = 1$.

## Proof

The Fourier transform of a ball follows from orthogonality: the integral of a nontrivial character over a ball is zero. The zeta integrals split into shells $\varpi^k \mathcal{O}_K^\times$, as in `Langlands.Local.GL1LFactor`, but with the sharp convergence condition $|\chi(\varpi) q^{-s}| < 1$ in place of a bounded integrand. Thus the two sides converge together on the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, which is not empty. In the unramified case both sides are geometric series. In the ramified case the shells of $\hat{\varphi}$ above $\varpi^{-n-a} \mathcal{O}_K^\times$ give zero: the change of variables $y \mapsto u y$ for a unit $u \in 1 + \mathfrak{p}^{a - 1}$ with $\chi(u) \ne 1$ fixes the integrand up to the factor $\chi^{-1}(u)$. Only the Gauss integral on the shell $\varpi^{-n-a} \mathcal{O}_K^\times$ is left.

## Open parts

* The Gauss integral is not zero: $G(\chi, \psi) \ne 0$, so that $c \ne 0$ also in the ramified case. The usual proof computes $|G(\chi, \psi)|^2$ with Fubini's theorem on $K \times K$. This needs product measurability, which needs a second countable topology on $K$, and the library has no such instance for `IsNonarchimedeanLocalField`.
* The functional equation for all Schwartz-Bruhat functions $\varphi$. This needs the fact that each Schwartz-Bruhat function is a finite linear combination of functions $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$, and the functional equation for each of these functions.
* Fourier inversion for all Schwartz-Bruhat functions. It follows from `fourier_fourier_ballIndicator` and the same decomposition.
* The existence of a conductor exponent for each continuous nontrivial additive character. Here it is a hypothesis.
* The independence of $\varepsilon(s, \chi, \psi)$ from the choice of test function.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis, Princeton 1950, §2.4 and §2.5.
* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, §23.
-/


namespace Langlands.LocalGL1

universe u

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise

section Additive

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Each ball $\varpi^N \mathcal{O}_K$ is closed under addition. -/
theorem add_mem_ordBall {N : ℤ} {x y : K} (hx : x ∈ ordBall K N) (hy : y ∈ ordBall K N) :
    x + y ∈ ordBall K N := by
  rw [ordBall_eq] at hx hy ⊢
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  exact (ValuativeRel.valuation K).map_add_le hx hy

/-- Each ball $\varpi^N \mathcal{O}_K$ is closed under negation. -/
theorem neg_mem_ordBall {N : ℤ} {x : K} (hx : x ∈ ordBall K N) : -x ∈ ordBall K N := by
  rw [ordBall_eq] at hx ⊢
  simpa only [Set.mem_ofPred_eq, Valuation.map_neg] using hx

/-- For $a$ in a ball, $x + a$ is in the ball exactly when $x$ is in the ball. -/
theorem add_mem_ordBall_iff {N : ℤ} {a : K} (ha : a ∈ ordBall K N) (x : K) :
    x + a ∈ ordBall K N ↔ x ∈ ordBall K N := by
  refine ⟨fun h => ?_, fun h => add_mem_ordBall h ha⟩
  simpa using add_mem_ordBall h (neg_mem_ordBall ha)

/-- For $a \ne 0$ and $\mathrm{ord}(a) \ge N$, the element $a$ is in the ball $\mathrm{ord} \ge N$. -/
theorem mem_ordBall_of_le {N : ℤ} {a : K} (ha : a ≠ 0) (h : N ≤ ord K a) : a ∈ ordBall K N :=
  (mem_ordBall_of_ne_zero ha).2 h

/-- The product of an element of $\varpi^M \mathcal{O}_K$ and an element of $\varpi^N \mathcal{O}_K$ is in $\varpi^{M + N} \mathcal{O}_K$. -/
theorem mul_mem_ordBall_add {M N : ℤ} {x y : K} (hx : x ∈ ordBall K M) (hy : y ∈ ordBall K N) :
    x * y ∈ ordBall K (M + N) := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_mul]
    exact zero_mem_ordBall _
  by_cases hy0 : y = 0
  · rw [hy0, mul_zero]
    exact zero_mem_ordBall _
  rw [mem_ordBall_of_ne_zero hx0] at hx
  rw [mem_ordBall_of_ne_zero hy0] at hy
  refine mem_ordBall_of_le (mul_ne_zero hx0 hy0) ?_
  rw [ord_mul hx0 hy0]
  omega

end Additive

section Fourier

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [MeasurableSpace K] [BorelSpace K] in
/-- Translation by an element $a$ of a ball $B$ multiplies the function $\mathbf{1}_B \psi$ by $\psi(a)$. -/
theorem indicator_addChar_add {N : ℤ} {a : K} (ha : a ∈ ordBall K N) (ψ : AddChar K ℂ) (x : K) :
    (ordBall K N).indicator ψ (x + a) = (ordBall K N).indicator ψ x * ψ a := by
  by_cases hx : x ∈ ordBall K N
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_mem_ordBall_iff ha x).2 hx),
      AddChar.map_add_eq_mul]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((add_mem_ordBall_iff ha x).1 h)), zero_mul]

/-- **Orthogonality.** If an additive character $\psi$ is not trivial on a ball $B$, then $\int_B \psi = 0$. -/
theorem integral_indicator_addChar_of_ne_one (ψ : AddChar K ℂ) {N : ℤ} {a : K}
    (ha : a ∈ ordBall K N) (hψ : ψ a ≠ 1) :
    ∫ x, (ordBall K N).indicator ψ x ∂μ = 0 := by
  have h : ∫ x, (ordBall K N).indicator ψ x ∂μ = (∫ x, (ordBall K N).indicator ψ x ∂μ) * ψ a :=
    calc ∫ x, (ordBall K N).indicator ψ x ∂μ
        = ∫ x, (ordBall K N).indicator ψ (x + a) ∂μ := (integral_add_right_eq_self _ a).symm
      _ = ∫ x, (ordBall K N).indicator ψ x * ψ a ∂μ :=
          integral_congr_ae (Eventually.of_forall (indicator_addChar_add ha ψ))
      _ = (∫ x, (ordBall K N).indicator ψ x ∂μ) * ψ a := integral_mul_const _ _
  have h1 : (∫ x, (ordBall K N).indicator ψ x ∂μ) * (1 - ψ a) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 (Ne.symm hψ))

omit [μ.IsAddHaarMeasure] in
/-- If $\psi$ is trivial on a ball $B$, then $\int_B \psi = \mu(B)$. -/
theorem integral_indicator_addChar_of_forall (ψ : AddChar K ℂ) {N : ℤ}
    (hψ : ∀ x ∈ ordBall K N, ψ x = 1) :
    ∫ x, (ordBall K N).indicator ψ x ∂μ = μ.real (ordBall K N) := by
  have : (ordBall K N).indicator ψ = (ordBall K N).indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : x ∈ ordBall K N
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hψ x hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [this, integral_indicator_const _ (isClosed_ordBall N).measurableSet, Complex.real_smul,
    mul_one]

/-- The Fourier transform $\hat{\varphi}(\xi) = \int_K \varphi(x) \psi(x \xi) \, d\mu(x)$ for an additive character $\psi$ and a Haar measure $\mu$. -/
noncomputable def fourier (ψ : AddChar K ℂ) (φ : K → ℂ) (ξ : K) : ℂ :=
  ∫ x, φ x * ψ (x * ξ) ∂μ

/-- The additive character $\psi$ has conductor exponent $n$: it is trivial on $\varpi^{-n} \mathcal{O}_K$ and not trivial on $\varpi^{-n-1} \mathcal{O}_K$. In terms of ideals, $\mathfrak{p}^{-n}$ is the largest fractional ideal on which $\psi$ is trivial. -/
structure IsConductor (ψ : AddChar K ℂ) (n : ℤ) : Prop where
  /-- The character is trivial on $\varpi^{-n} \mathcal{O}_K$. -/
  trivial : ∀ x ∈ ordBall K (-n), ψ x = 1
  /-- The character is not trivial on $\varpi^{-n-1} \mathcal{O}_K$. -/
  nontrivial : ∃ x ∈ ordBall K (-n - 1), ψ x ≠ 1

omit [MeasurableSpace K] [BorelSpace K] in
/-- If $\psi$ has conductor exponent $n$, then $\psi$ is trivial on the ball $\xi \varpi^N \mathcal{O}_K$ exactly when $\mathrm{ord}(\xi) \ge -n - N$. -/
theorem IsConductor.forall_mul_iff {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) (N : ℤ)
    (ξ : K) : (∀ x ∈ ordBall K N, ψ (x * ξ) = 1) ↔ ξ ∈ ordBall K (-n - N) := by
  constructor
  · intro h
    by_contra hξ
    have hξ0 : ξ ≠ 0 := fun h0 => hξ (h0 ▸ zero_mem_ordBall _)
    rw [mem_ordBall_of_ne_zero hξ0, not_le] at hξ
    obtain ⟨y, hy, hψy⟩ := hψ.nontrivial
    have hy0 : y ≠ 0 := fun h0 => hψy (h0 ▸ AddChar.map_zero_eq_one ψ)
    refine hψy ?_
    have := h (y / ξ) ?_
    · rwa [div_mul_cancel₀ y hξ0] at this
    · rw [mem_ordBall_of_ne_zero hy0] at hy
      refine mem_ordBall_of_le (div_ne_zero hy0 hξ0) ?_
      rw [div_eq_mul_inv, ord_mul hy0 (inv_ne_zero hξ0), ord_inv hξ0]
      omega
  · intro hξ x hx
    refine hψ.trivial _ ?_
    by_cases hx0 : x = 0
    · rw [hx0, zero_mul]
      exact zero_mem_ordBall _
    by_cases hξ0 : ξ = 0
    · rw [hξ0, mul_zero]
      exact zero_mem_ordBall _
    rw [mem_ordBall_of_ne_zero hx0] at hx
    rw [mem_ordBall_of_ne_zero hξ0] at hξ
    refine mem_ordBall_of_le (mul_ne_zero hx0 hξ0) ?_
    rw [ord_mul hx0 hξ0]
    omega

/-- **The Fourier transform of a ball.** If $\psi$ has conductor exponent $n$, then the Fourier transform of $\mathbf{1}_{\varpi^N \mathcal{O}_K}$ is $\mu(\varpi^N \mathcal{O}_K) \mathbf{1}_{\varpi^{-n-N} \mathcal{O}_K}$. -/
theorem fourier_indicator_ordBall {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) (N : ℤ) :
    fourier μ ψ ((ordBall K N).indicator 1) =
      (ordBall K (-n - N)).indicator fun _ => (μ.real (ordBall K N) : ℂ) := by
  funext ξ
  have h1 : fourier μ ψ ((ordBall K N).indicator 1) ξ =
      ∫ x, (ordBall K N).indicator (ψ.mulShift ξ) x ∂μ := by
    unfold fourier
    congr 1
    funext x
    by_cases hx : x ∈ ordBall K N
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul,
        AddChar.mulShift_apply, mul_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [h1]
  by_cases hξ : ξ ∈ ordBall K (-n - N)
  · rw [Set.indicator_of_mem hξ, integral_indicator_addChar_of_forall μ _ fun x hx => ?_]
    rw [AddChar.mulShift_apply, mul_comm]
    exact (hψ.forall_mul_iff N ξ).2 hξ x hx
  · rw [Set.indicator_of_notMem hξ]
    have h := mt (hψ.forall_mul_iff N ξ).1 hξ
    push Not at h
    obtain ⟨x, hx, hψx⟩ := h
    refine integral_indicator_addChar_of_ne_one μ _ hx ?_
    rwa [AddChar.mulShift_apply, mul_comm]

/-- The set $1 + \varpi^a \mathcal{O}_K$. -/
def oneAddBall (a : ℤ) : Set K :=
  {y | y - 1 ∈ ordBall K a}

/-- **The Fourier transform of $1 + \varpi^a \mathcal{O}_K$.** If $\psi$ has conductor exponent $n$, then the Fourier transform of $\mathbf{1}_{1 + \varpi^a \mathcal{O}_K}$ is $\xi \mapsto \psi(\xi) \mu(\varpi^a \mathcal{O}_K) \mathbf{1}_{\varpi^{-n-a} \mathcal{O}_K}(\xi)$. -/
theorem fourier_indicator_oneAddBall {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) (a : ℤ)
    (ξ : K) : fourier μ ψ ((oneAddBall a).indicator 1) ξ =
      ψ ξ * (ordBall K (-n - a)).indicator (fun _ => (μ.real (ordBall K a) : ℂ)) ξ := by
  rw [← fourier_indicator_ordBall μ hψ a, fourier, fourier, ← integral_const_mul,
    ← integral_add_right_eq_self _ 1]
  congr 1
  funext x
  have hm : x + 1 ∈ oneAddBall a ↔ x ∈ ordBall K a := by
    simp [oneAddBall]
  by_cases hx : x ∈ ordBall K a
  · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx, add_mul, one_mul,
      AddChar.map_add_eq_mul]
    simp only [Pi.one_apply, one_mul]
    ring
  · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx]
    simp

end Fourier

section Convergence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The inverse of a smooth character is smooth. -/
theorem isSmoothChar_inv (hχ : IsSmoothChar K χ) : IsSmoothChar K χ⁻¹ := by
  have : (χ⁻¹).ker = χ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rwa [this]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The value of $\chi^{-1}$ is the inverse of the value of $\chi$. -/
theorem inv_apply_coe (x : Kˣ) : ((χ⁻¹ x : ℂˣ) : ℂ) = (χ x : ℂ)⁻¹ := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

/-- The number $q^{-s}$ is not zero. -/
theorem cpow_neg_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 :=
  Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne'))

/-- The number $q^{-(1 - s)}$ is $q^{-1} (q^{-s})^{-1}$. -/
theorem cpow_neg_one_sub (s : ℂ) :
    (residueCard K : ℂ) ^ (-(1 - s)) = (residueCard K : ℂ)⁻¹ * ((residueCard K : ℂ) ^ (-s))⁻¹ := by
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  rw [show -(1 - s) = -1 + s by ring, Complex.cpow_add _ _ hq, Complex.cpow_neg, Complex.cpow_neg,
    Complex.cpow_one, inv_inv]

/-- The number $|\chi(\varpi) q^{1 - s}|$ is $|\chi(\varpi) q^{-s}| \cdot q$. -/
theorem norm_zetaRatio (s : ℂ) :
    ‖zetaRatio χ s‖ = ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ * residueCard K := by
  rw [zetaRatio, ← mul_assoc, norm_mul, Complex.norm_natCast]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

omit χ in
/-- The volume of a ball is $\mu(\varpi^N \mathcal{O}_K) = q^{-N} \mu(\mathcal{O}_K)$. -/
theorem measureReal_ordBall (N : ℤ) :
    μ.real (ordBall K N) = (residueCard K : ℝ) ^ (-N) * μ.real (ordBall K 0) := by
  have h := distribHaarChar_mul μ (unif K ^ N) (ordBall K 0)
  rw [units_smul_ordBall, distribHaarChar_eq μ, Units.val_zpow_eq_zpow_val, ord_zpow, ord_unif,
    mul_one, zero_add] at h
  rw [measureReal_def, measureReal_def, ← h, ENNReal.toReal_mul]
  simp

omit [μ.Regular] in
/-- On the shell $\mathrm{ord} = k$, the function $\chi(y) |y|^{s - 1}$ is integrable. -/
theorem integrableOn_ordShell_zetaFn (hχ : IsSmoothChar K χ) (s : ℂ) {C : ℝ}
    (hC : ∀ y ∈ ordShell K 0, ‖extChar χ y‖ ≤ C) (k : ℤ) :
    IntegrableOn (zetaFn χ s) (ordShell K k) μ ∧
      ∫ y in ordShell K k, ‖zetaFn χ s y‖ ∂μ ≤
        ‖zetaRatio χ s‖ ^ k * C * μ.real (ordBall K k) := by
  have hbound : ∀ y ∈ ordShell K k, ‖zetaFn χ s y‖ ≤ ‖zetaRatio χ s‖ ^ k * C := by
    intro y hy
    rw [zetaFn_eq_zetaRatio χ hy.1, norm_mul, norm_zpow]
    exact mul_le_mul (le_of_eq (by rw [hy.2])) (hC _ (mem_ordShell_zero_div hy.1))
      (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _)
  have hint : IntegrableOn (zetaFn χ s) (ordShell K k) μ :=
    Measure.integrableOn_of_bounded (M := ‖zetaRatio χ s‖ ^ k * C) (measure_ordShell_ne_top μ k)
      (aestronglyMeasurable_of_continuousOn μ (continuousOn_zetaFn χ hχ s))
      ((ae_restrict_iff' (isClosed_ordShell k).measurableSet).2 (Eventually.of_forall hbound))
  refine ⟨hint, ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 one_mem_ordShell_zero)
  calc ∫ y in ordShell K k, ‖zetaFn χ s y‖ ∂μ
      ≤ ∫ _ in ordShell K k, ‖zetaRatio χ s‖ ^ k * C ∂μ :=
        setIntegral_mono_on hint.norm (integrableOn_const (measure_ordShell_ne_top μ k))
          (isClosed_ordShell k).measurableSet hbound
    _ = μ.real (ordShell K k) * (‖zetaRatio χ s‖ ^ k * C) := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ μ.real (ordBall K k) * (‖zetaRatio χ s‖ ^ k * C) :=
        mul_le_mul_of_nonneg_right (measureReal_mono (ordShell_subset_ordBall k)
          (measure_ordBall_ne_top μ k)) (mul_nonneg (zpow_nonneg (norm_nonneg _) _) hC0)
    _ = ‖zetaRatio χ s‖ ^ k * C * μ.real (ordBall K k) := by ring

/-- **Convergence of the zeta integral.** If $|\chi(\varpi) q^{-s}| < 1$, then $\chi(y) |y|^{s - 1}$ is integrable on each measurable subset of a ball. This is the exact domain of convergence of Tate's zeta integrals. -/
theorem integrable_indicator_zetaFn_of_lt (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) {S : Set K} (hS : MeasurableSet S)
    {N : ℤ} (hSN : S ⊆ ordBall K N) : Integrable (S.indicator (zetaFn χ s)) μ := by
  obtain ⟨C, hC⟩ := exists_bound_extChar χ hχ
  set ρ := ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ with hρ
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast residueCard_pos'
  have hρ0 : 0 < ρ := norm_pos_iff.2 (mul_ne_zero (Units.ne_zero _) (cpow_neg_ne_zero s))
  have hU : ordBall K N ⊆ {0} ∪ ⋃ i : ℕ, ordShell K (N + i) := by
    intro y hy
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    refine Or.inr (Set.mem_iUnion.2 ⟨(ord K y - N).toNat, hy0, ?_⟩)
    have := (mem_ordBall_of_ne_zero hy0).1 hy
    omega
  have hterm : ∀ i : ℕ, ‖zetaRatio χ s‖ ^ (N + i : ℤ) * C * μ.real (ordBall K (N + i)) =
      C * μ.real (ordBall K 0) * ρ ^ N * ρ ^ i := by
    intro i
    rw [measureReal_ordBall μ, norm_zetaRatio, ← hρ, mul_zpow, zpow_add₀ hρ0.ne', zpow_natCast]
    have : (residueCard K : ℝ) ^ (N + i : ℤ) * (residueCard K : ℝ) ^ (-(N + i : ℤ)) = 1 := by
      rw [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero]
    linear_combination (C * ρ ^ N * ρ ^ i * μ.real (ordBall K 0)) * this
  have hsum : Summable fun i : ℕ => ∫ y in ordShell K (N + i), ‖zetaFn χ s y‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ((integrableOn_ordShell_zetaFn χ μ hχ s hC (N + i)).2).trans_eq (hterm i)) ?_
    exact (summable_geometric_of_lt_one hρ0.le hs).mul_left _
  have hI : IntegrableOn (zetaFn χ s) (ordBall K N) μ :=
    (integrableOn_union.2 ⟨IntegrableOn.of_measure_zero (measure_zero_singleton μ),
      integrableOn_iUnion_of_summable_integral_norm (s := fun i : ℕ => ordShell K (N + i))
        (fun i => (integrableOn_ordShell_zetaFn χ μ hχ s hC (N + i)).1) hsum⟩).mono_set hU
  exact (integrable_indicator_iff hS).2 (hI.mono_set hSN)

/-- If $|\chi(\varpi) q^{-s}| < 1$, then $T_0 (1 - \chi(\varpi) q^{-s}) = c_0$, with $T_0 = Z(\mathbf{1}_{\mathcal{O}_K}, \chi, s)$ and $c_0 = \int_{\mathcal{O}_K^\times} \chi$. -/
theorem ballZeta_one_zero_of_lt (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) :
    ballZeta χ μ (fun _ => 1) s 0 * (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) =
      shellCoeff χ μ (fun _ => 1) 0 := by
  have hint : ∀ S, MeasurableSet S → S ⊆ ordBall K 0 →
      Integrable (S.indicator (fun y => (fun _ => (1 : ℂ)) y * zetaFn χ s y)) μ := by
    intro S hS hSm
    simp only [one_mul]
    exact integrable_indicator_zetaFn_of_lt χ μ hχ hs hS hSm
  have hshell : ∀ y, (ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * zetaFn χ s y) y =
      (ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * extChar χ y) y := by
    intro y
    by_cases hy : y ∈ ordShell K 0
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, zetaFn_eq χ hy.1, hy.2, zpow_zero,
        mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have h : ballZeta χ μ (fun _ => 1) s 0 =
      ballZeta χ μ (fun _ => 1) s (0 + 1) + shellCoeff χ μ (fun _ => 1) 0 := by
    unfold ballZeta shellCoeff
    simp_rw [indicator_ordBall_eq 0]
    rw [integral_add (hint _ (isClosed_ordBall _).measurableSet (ordBall_anti (by omega)))
      (hint _ (isClosed_ordShell 0).measurableSet (ordShell_subset_ordBall 0))]
    simp_rw [hshell]
  rw [ballZeta_one_succ] at h
  linear_combination h

/-- The step $T_m = T_{m + 1} + c_m (q^{1 - s})^m$ of `ballZeta_eq_succ`, for each $s$ with $|\chi(\varpi) q^{-s}| < 1$. -/
theorem ballZeta_eq_succ_of_lt (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    {φ : K → ℂ} (hφm : AEStronglyMeasurable φ μ) {C : ℝ} (hφC : ∀ y, ‖φ y‖ ≤ C) (m : ℤ) :
    ballZeta χ μ φ s m = ballZeta χ μ φ s (m + 1) +
      shellCoeff χ μ φ m * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ m := by
  have hint : ∀ S, MeasurableSet S → S ⊆ ordBall K m →
      Integrable (S.indicator (fun y => φ y * zetaFn χ s y)) μ := by
    intro S hS hSm
    have : S.indicator (fun y => φ y * zetaFn χ s y) = fun y => φ y * S.indicator (zetaFn χ s) y :=
      funext fun y => Set.indicator_mul_right S φ (zetaFn χ s)
    rw [this]
    exact (integrable_indicator_zetaFn_of_lt χ μ hχ hs hS hSm).bdd_mul hφm
      (Eventually.of_forall hφC)
  have hshell : ∀ y, (ordShell K m).indicator (fun y => φ y * zetaFn χ s y) y =
      (ordShell K m).indicator (fun y => φ y * extChar χ y) y *
        ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ m := by
    intro y
    by_cases hy : y ∈ ordShell K m
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, zetaFn_eq χ hy.1, hy.2, mul_assoc]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold ballZeta shellCoeff
  simp_rw [indicator_ordBall_eq m]
  rw [integral_add (hint _ (isClosed_ordBall _).measurableSet (ordBall_anti (by omega)))
    (hint _ (isClosed_ordShell m).measurableSet (ordShell_subset_ordBall m))]
  simp_rw [hshell]
  rw [integral_mul_const]

omit [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The zeta integral of $c \mathbf{1}_{\varpi^N \mathcal{O}_K}$ is $c T_N$. -/
theorem zeta_indicator_ordBall_const (c : ℂ) (s : ℂ) (N : ℤ) :
    zeta χ μ ((ordBall K N).indicator fun _ => c) s = c * ballZeta χ μ (fun _ => 1) s N := by
  unfold zeta ballZeta
  rw [← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ ordBall K N
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul, mul_zero]

/-- The formula $T_N = (\chi(\varpi) q^{-s})^N T_0$ for each integer $N$. -/
theorem ballZeta_one_zpow (s : ℂ) (N : ℤ) :
    ballZeta χ μ (fun _ => 1) s N =
      ((χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N * ballZeta χ μ (fun _ => 1) s 0 := by
  have hc : (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (cpow_neg_ne_zero s)
  induction N using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [ballZeta_one_succ, ih, zpow_add_one₀ hc]
    ring
  | pred i ih =>
    have h := ballZeta_one_succ χ μ s (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at h
    rw [zpow_sub_one₀ hc]
    refine mul_left_cancel₀ hc ?_
    rw [← h]
    have hX := cpow_neg_ne_zero (K := K) s
    field_simp

/-- For $\chi$ trivial on $\mathcal{O}_K^\times$ and $|\chi(\varpi) q^{-s}| < 1$, the zeta integral of $\mathbf{1}_{\varpi^N \mathcal{O}_K}$ is $(\chi(\varpi) q^{-s})^N \mu(\mathcal{O}_K^\times) L(s, \chi)$. -/
theorem zeta_indicator_ordBall_of_unramified (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) (c : ℂ) (N : ℤ) :
    zeta χ μ ((ordBall K N).indicator fun _ => c) s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) =
      c * ((χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N * μ.real (ordShell K 0) := by
  rw [zeta_indicator_ordBall_const, ballZeta_one_zpow, mul_assoc, mul_assoc,
    ballZeta_one_zero_of_lt χ μ hχ hs, shellCoeff_one_of_unramified χ μ hχ1]
  ring

end Convergence

section Unramified

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ) [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- The ε-factor $\varepsilon(s, \chi, \psi, \mu) = \mu(\mathcal{O}_K) q^n \chi(\varpi)^n (q^{-s})^n$ of an unramified character $\chi$, for an additive character $\psi$ of conductor exponent $n$. For the self dual measure, $\mu(\mathcal{O}_K) = q^{-n/2}$, this is $\chi(\varpi)^n q^{n (1/2 - s)}$. -/
noncomputable def epsilonUnramified (n : ℤ) (s : ℂ) : ℂ :=
  (μ.real (ordBall K 0) : ℂ) * (χ (unif K) : ℂ) ^ n * (residueCard K : ℂ) ^ n *
    ((residueCard K : ℂ) ^ (-s)) ^ n

omit [BorelSpace K] in
/-- The ε-factor of an unramified character has the form $c (q^{-s})^n$ with $c \ne 0$. -/
theorem epsilonUnramified_eq (n : ℤ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ s, epsilonUnramified χ μ n s = c * ((residueCard K : ℂ) ^ (-s)) ^ n := by
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hμ : (μ.real (ordBall K 0) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨measure_ordBall_ne_zero μ 0, measure_ordBall_ne_top μ 0⟩
  exact ⟨_, mul_ne_zero (mul_ne_zero hμ (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ hq),
    fun s => rfl⟩

variable [μ.Regular]

/-- **Tate's local functional equation, unramified case.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$, let $\psi$ be an additive character of conductor exponent $n$, and let $\varphi = \mathbf{1}_{\mathcal{O}_K}$. For each $s$ in the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, where both zeta integrals converge, $$\frac{Z(\hat{\varphi}, \chi^{-1}, 1 - s)}{L(1 - s, \chi^{-1})} = \varepsilon(s, \chi, \psi) \frac{Z(\varphi, \chi, s)}{L(s, \chi)},$$ with $L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ and $\varepsilon = $ `epsilonUnramified`. -/
theorem localFunctionalEquation_unramified (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    {s : ℂ} (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ ((ordBall K 0).indicator 1)) (1 - s) *
        (1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))) =
      epsilonUnramified χ μ n s * (zeta χ μ ((ordBall K 0).indicator 1) s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))) := by
  have hχ1' : ∀ x : Kˣ, normAbs K x = 1 → χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, hχ1 x hx, inv_one]
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  have h1 := zeta_indicator_ordBall_of_unramified χ μ hχ hχ1 hs 1 0
  have h2 := zeta_indicator_ordBall_of_unramified χ⁻¹ μ (isSmoothChar_inv χ hχ) hχ1' hs2
    (μ.real (ordBall K 0)) (-n - 0)
  rw [inv_apply_coe] at h2
  have he : ((ordBall K 0).indicator 1 : K → ℂ) = (ordBall K 0).indicator fun _ => (1 : ℂ) := rfl
  rw [fourier_indicator_ordBall μ hψ 0, h2, he, h1, epsilonUnramified, sub_zero, zpow_zero,
    cpow_neg_one_sub, mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow', neg_neg]
  ring

end Unramified

section Ramified

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

/-- The character $\chi$ is ramified with conductor exponent $a \ge 1$: it is trivial on $1 + \mathfrak{p}^a$ and not trivial on $(1 + \mathfrak{p}^{a - 1}) \cap \mathcal{O}_K^\times$. -/
structure IsRamifiedConductor (a : ℕ) : Prop where
  /-- The exponent is at least $1$. -/
  one_le : 1 ≤ a
  /-- The character is trivial on $1 + \mathfrak{p}^a$. -/
  trivial : ∀ x : Kˣ, (x : K) ∈ oneAddBall (a : ℤ) → χ x = 1
  /-- The character is not trivial on $(1 + \mathfrak{p}^{a - 1}) \cap \mathcal{O}_K^\times$. -/
  nontrivial : ∃ u : Kˣ, ord K (u : K) = 0 ∧ (u : K) ∈ oneAddBall ((a : ℤ) - 1) ∧ χ u ≠ 1

/-- An element of $1 + \mathfrak{p}^a$ with $a \ge 1$ is a unit of $\mathcal{O}_K$: it is not $0$ and has order $0$. -/
theorem ne_zero_and_ord_eq_zero_of_mem_oneAddBall {a : ℤ} (ha : 1 ≤ a) {y : K}
    (hy : y ∈ oneAddBall a) : y ≠ 0 ∧ ord K y = 0 := by
  have h1 : y - 1 ∈ ordBall K 1 := ordBall_anti ha hy
  have hone : (1 : K) ∉ ordBall K 1 := by
    rw [mem_ordBall_of_ne_zero one_ne_zero, ord_one]
    omega
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hone (by simpa using neg_mem_ordBall h1)
  refine ⟨hy0, ?_⟩
  have hO : y ∈ ordBall K 0 := by
    have h1' : y - 1 ∈ ordBall K 0 := ordBall_anti zero_le_one h1
    have hone0 : (1 : K) ∈ ordBall K 0 := (mem_ordBall_of_ne_zero one_ne_zero).2 (by rw [ord_one])
    simpa using add_mem_ordBall h1' hone0
  have h0 := (mem_ordBall_of_ne_zero hy0).1 hO
  by_contra hne
  have hy1 : y ∈ ordBall K 1 := (mem_ordBall_of_ne_zero hy0).2 (by omega)
  exact hone (by simpa using add_mem_ordBall hy1 (neg_mem_ordBall h1))

omit χ in
/-- The set $1 + \varpi^a \mathcal{O}_K$ is the translate of $\varpi^a \mathcal{O}_K$ by $1$. -/
theorem oneAddBall_eq_preimage (a : ℤ) :
    oneAddBall a = (fun y : K => y + -1) ⁻¹' ordBall K a := by
  ext y
  simp [oneAddBall, sub_eq_add_neg]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
/-- The set $1 + \varpi^a \mathcal{O}_K$ is measurable. -/
theorem measurableSet_oneAddBall (a : ℤ) : MeasurableSet (oneAddBall a : Set K) := by
  rw [oneAddBall_eq_preimage]
  exact (measurable_add_const _) (isClosed_ordBall a).measurableSet

/-- The volume of $1 + \varpi^a \mathcal{O}_K$ is the volume of $\varpi^a \mathcal{O}_K$. -/
theorem measureReal_oneAddBall (a : ℤ) : μ.real (oneAddBall a) = μ.real (ordBall K a) := by
  rw [oneAddBall_eq_preimage, measureReal_def, measureReal_def, measure_preimage_add_right]

/-- The Gauss integral $G(\chi, \psi) = \int_{\mathrm{ord}(y) = k} \psi(y) \chi^{-1}(y) \, d\mu(y)$ over the shell $\varpi^k \mathcal{O}_K^\times$. -/
noncomputable def gaussInt (ψ : AddChar K ℂ) (k : ℤ) : ℂ :=
  ∫ y, (ordShell K k).indicator (fun y => ψ y * extChar χ⁻¹ y) y ∂μ

/-- **The zeta integral of the test function.** If $\chi$ has conductor exponent $a \ge 1$, then $Z(\mathbf{1}_{1 + \mathfrak{p}^a}, \chi, s) = \mu(\mathfrak{p}^a)$ for each $s$. -/
theorem zeta_indicator_oneAddBall {a : ℕ} (hχ : IsRamifiedConductor χ a) (s : ℂ) :
    zeta χ μ ((oneAddBall (a : ℤ)).indicator 1) s = μ.real (ordBall K a) := by
  have ha : (1 : ℤ) ≤ a := by exact_mod_cast hχ.one_le
  have : ∀ y, (oneAddBall (a : ℤ)).indicator (1 : K → ℂ) y * zetaFn χ s y =
      (oneAddBall (a : ℤ)).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    by_cases hy : y ∈ oneAddBall (a : ℤ)
    · obtain ⟨hy0, hord⟩ := ne_zero_and_ord_eq_zero_of_mem_oneAddBall ha hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, one_mul, zetaFn,
        extChar_of_ne_zero χ hy0, hχ.trivial _ (by simpa using hy), (normAbs_eq_one_iff hy0).2 hord]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold zeta
  simp_rw [this]
  rw [integral_indicator_const _ (measurableSet_oneAddBall _), Complex.real_smul, mul_one,
    measureReal_oneAddBall]

variable [μ.Regular]

/-- **Vanishing below the conductor.** Let $\chi$ have conductor exponent $a \ge 1$ and $\psi$ conductor exponent $n$. If $\varphi = \psi$ on $\varpi^{-n-a+1} \mathcal{O}_K$, then $\int_{\varpi^{-n-a+1} \mathcal{O}_K} \varphi(y) \chi^{-1}(y) |y|^{s - 1} \, dy = 0$. The proof is the change of variables $y \mapsto u y$ for a unit $u \in 1 + \mathfrak{p}^{a-1}$ with $\chi(u) \ne 1$: it fixes $\psi(y)$ and $|y|$, and it multiplies $\chi^{-1}(y)$ by $\chi^{-1}(u)$. -/
theorem ballZeta_addChar_eq_zero {a : ℕ} (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ} {n : ℤ}
    (hψ : IsConductor ψ n) (s : ℂ) {φ : K → ℂ} (hφ : ∀ y ∈ ordBall K (-n - a + 1), φ y = ψ y) :
    ballZeta χ⁻¹ μ φ s (-n - a + 1) = 0 := by
  obtain ⟨u, hu0, hu1, hχu⟩ := hχ.nontrivial
  set B := ordBall K (-n - a + 1) with hB
  set F := B.indicator (fun y => φ y * zetaFn χ⁻¹ s y) with hF
  have h := integral_comp_mul_left μ u.ne_zero F
  have hfun : (fun x => F ((u : K) * x)) = fun x => (χ⁻¹ u : ℂ) * F x := by
    funext x
    have hm : (u : K) * x ∈ B ↔ x ∈ B := by
      rw [hB, mul_mem_ordBall_iff u.ne_zero, hu0, sub_zero]
    by_cases hx : x ∈ B
    · rw [hF, Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx, hφ _ (hm.2 hx), hφ _ hx,
        zetaFn_mul χ⁻¹ u.ne_zero, hu0, zpow_zero, mul_one, Units.mk0_val]
      have hψu : ψ ((u : K) * x) = ψ x := by
        have hmem : ((u : K) - 1) * x ∈ ordBall K (-n) := by
          have := mul_mem_ordBall_add hu1 hx
          rwa [show (a : ℤ) - 1 + (-n - a + 1) = -n by ring] at this
        rw [show (u : K) * x = x + ((u : K) - 1) * x by ring, AddChar.map_add_eq_mul,
          hψ.trivial _ hmem, mul_one]
      rw [hψu]
      ring
    · rw [hF, Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx, mul_zero]
  rw [hfun, integral_const_mul, hu0, zpow_zero, one_smul] at h
  have h1 : ((χ⁻¹ u : ℂˣ) : ℂ) - 1 ≠ 0 := by
    rw [inv_apply_coe, sub_ne_zero]
    intro h'
    exact hχu (Units.val_eq_one.1 (inv_eq_one.1 h'))
  unfold ballZeta
  refine (mul_eq_zero.1 (?_ : (((χ⁻¹ u : ℂˣ) : ℂ) - 1) * ∫ y, F y ∂μ = 0)).resolve_left h1
  rw [sub_mul, one_mul, h, sub_self]

/-- **Tate's local functional equation, ramified case.** Let $\chi$ be a smooth character of conductor exponent $a \ge 1$, let $\psi$ be a continuous additive character of conductor exponent $n$, and let $\varphi = \mathbf{1}_{1 + \mathfrak{p}^a}$. For each $s$ with $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, where $Z(\hat{\varphi}, \chi^{-1}, 1 - s)$ converges, $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s), \quad \varepsilon(s, \chi, \psi) = G(\chi, \psi) (q^{-s})^{a + n},$$ with the Gauss integral $G(\chi, \psi) = \int_{\varpi^{-n-a} \mathcal{O}_K^\times} \psi(y) \chi^{-1}(y) \, dy$. Here $L(s, \chi) = L(1 - s, \chi^{-1}) = 1$. -/
theorem localFunctionalEquation_ramified (hχs : IsSmoothChar K χ) {a : ℕ}
    (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ} (hψc : Continuous ψ) {n : ℤ}
    (hψ : IsConductor ψ n) {s : ℂ}
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ ((oneAddBall (a : ℤ)).indicator 1)) (1 - s) =
      gaussInt χ μ ψ (-n - a) * ((residueCard K : ℂ) ^ (-s)) ^ ((a : ℤ) + n) *
        zeta χ μ ((oneAddBall (a : ℤ)).indicator 1) s := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  set B := ordBall K (-n - a) with hB
  set g := B.indicator (⇑ψ) with hg
  set μa : ℂ := (μ.real (ordBall K a) : ℂ) with hμa
  have hfour : fourier μ ψ ((oneAddBall (a : ℤ)).indicator 1) = fun ξ => μa * g ξ := by
    funext ξ
    rw [fourier_indicator_oneAddBall μ hψ]
    by_cases hξ : ξ ∈ B
    · rw [hg, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      ring
    · rw [hg, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero, mul_zero]
  have hzeta : zeta χ⁻¹ μ (fun ξ => μa * g ξ) (1 - s) = μa * ballZeta χ⁻¹ μ g (1 - s) (-n - a) := by
    unfold zeta ballZeta
    rw [← integral_const_mul]
    congr 1
    funext y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, mul_assoc]
    · rw [Set.indicator_of_notMem hy]
      simp only [hg, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  obtain ⟨C, hC⟩ := (isCompact_ordBall (K := K) (-n - a)).exists_bound_of_continuousOn
    hψc.continuousOn
  have hgC : ∀ y, ‖g y‖ ≤ max C 0 := by
    intro y
    by_cases hy : y ∈ B
    · rw [hg, Set.indicator_of_mem hy]
      exact (hC y hy).trans (le_max_left _ _)
    · rw [hg, Set.indicator_of_notMem hy, norm_zero]
      exact le_max_right _ _
  have hgm : AEStronglyMeasurable g μ :=
    hψc.aestronglyMeasurable.indicator (isClosed_ordBall _).measurableSet
  have hstep := ballZeta_eq_succ_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχs) hs2 hgm hgC (-n - a)
  rw [ballZeta_addChar_eq_zero χ μ hχ hψ (1 - s) (φ := g) fun y hy => by
    rw [hg, Set.indicator_of_mem (ordBall_anti (by omega) hy)], zero_add] at hstep
  have hshell : shellCoeff χ⁻¹ μ g (-n - a) = gaussInt χ μ ψ (-n - a) := by
    unfold shellCoeff gaussInt
    congr 1
    funext y
    by_cases hy : y ∈ ordShell K (-n - a)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hg,
        Set.indicator_of_mem (ordShell_subset_ordBall _ hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hX := cpow_neg_ne_zero (K := K) s
  rw [hfour, hzeta, hstep, hshell, zeta_indicator_oneAddBall χ μ hχ, cpow_neg_one_sub,
    show (residueCard K : ℂ)⁻¹ * ((residueCard K : ℂ) ^ (-s))⁻¹ * residueCard K =
      ((residueCard K : ℂ) ^ (-s))⁻¹ by field_simp, inv_zpow', neg_sub, sub_neg_eq_add, hμa]
  ring

end Ramified

section SelfDual

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]
  [μ.IsAddHaarMeasure] in
/-- The Fourier transform is linear: $\widehat{c \varphi} = c \hat{\varphi}$. -/
theorem fourier_const_mul (ψ : AddChar K ℂ) (c : ℂ) (φ : K → ℂ) (ξ : K) :
    fourier μ ψ (fun x => c * φ x) ξ = c * fourier μ ψ φ ξ := by
  unfold fourier
  rw [← integral_const_mul]
  simp_rw [mul_assoc]

/-- Translation by $b$ multiplies the Fourier transform by $\xi \mapsto \psi(b \xi)$. -/
theorem fourier_comp_sub (ψ : AddChar K ℂ) (φ : K → ℂ) (b ξ : K) :
    fourier μ ψ (fun x => φ (x - b)) ξ = ψ (b * ξ) * fourier μ ψ φ ξ := by
  unfold fourier
  rw [← integral_add_right_eq_self _ b, ← integral_const_mul]
  congr 1
  funext x
  simp only [add_sub_cancel_right]
  rw [add_mul, AddChar.map_add_eq_mul]
  ring

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]
  [μ.IsAddHaarMeasure] in
/-- Multiplication by $\xi \mapsto \psi(b \xi)$ translates the Fourier transform by $-b$. -/
theorem fourier_addChar_mul (ψ : AddChar K ℂ) (φ : K → ℂ) (b x : K) :
    fourier μ ψ (fun ξ => ψ (b * ξ) * φ ξ) x = fourier μ ψ φ (x + b) := by
  unfold fourier
  congr 1
  funext ξ
  rw [mul_add, AddChar.map_add_eq_mul, mul_comm ξ b]
  ring

/-- The indicator function $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ of a translate of a ball. -/
noncomputable def ballIndicator (b : K) (N : ℤ) (x : K) : ℂ :=
  (ordBall K N).indicator 1 (x - b)

/-- **The Fourier transform of a translated ball.** If $\psi$ has conductor exponent $n$, then the Fourier transform of $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ is $\xi \mapsto \psi(b \xi) \mu(\varpi^N \mathcal{O}_K) \mathbf{1}_{\varpi^{-n-N} \mathcal{O}_K}(\xi)$. -/
theorem fourier_ballIndicator {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) (b : K) (N : ℤ)
    (ξ : K) : fourier μ ψ (ballIndicator b N) ξ =
      ψ (b * ξ) * (ordBall K (-n - N)).indicator (fun _ => (μ.real (ordBall K N) : ℂ)) ξ := by
  change fourier μ ψ (fun x => (ordBall K N).indicator 1 (x - b)) ξ = _
  rw [fourier_comp_sub μ ψ ((ordBall K N).indicator 1), fourier_indicator_ordBall μ hψ]

variable [μ.Regular]

/-- **Fourier inversion on translated balls.** If $\psi$ has conductor exponent $n$, then $\hat{\hat{\varphi}}(x) = \mu(\mathcal{O}_K)^2 q^n \varphi(-x)$ for $\varphi = \mathbf{1}_{b + \varpi^N \mathcal{O}_K}$. -/
theorem fourier_fourier_ballIndicator {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) (b : K)
    (N : ℤ) (x : K) : fourier μ ψ (fourier μ ψ (ballIndicator b N)) x =
      ((μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n : ℝ) : ℂ) * ballIndicator b N (-x) := by
  have h1 : fourier μ ψ (ballIndicator b N) = fun ξ => ψ (b * ξ) *
      ((μ.real (ordBall K N) : ℂ) * (ordBall K (-n - N)).indicator 1 ξ) := by
    funext ξ
    rw [fourier_ballIndicator μ hψ]
    by_cases hξ : ξ ∈ ordBall K (-n - N)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero, mul_zero, mul_zero]
  rw [h1, fourier_addChar_mul, fourier_const_mul, fourier_indicator_ordBall μ hψ,
    show -n - (-n - N) = N by ring]
  have hm : x + b ∈ ordBall K N ↔ -x - b ∈ ordBall K N := by
    rw [show -x - b = -(x + b) by ring]
    exact ⟨neg_mem_ordBall, fun h => by simpa using neg_mem_ordBall h⟩
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast residueCard_pos'
  have hμ : μ.real (ordBall K N) * μ.real (ordBall K (-n - N)) =
      μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n := by
    rw [measureReal_ordBall μ N, measureReal_ordBall μ (-n - N), neg_sub, sub_neg_eq_add]
    have : (residueCard K : ℝ) ^ (-N) * (residueCard K : ℝ) ^ (N + n) =
        (residueCard K : ℝ) ^ n := by
      rw [← zpow_add₀ hq.ne']
      congr 1
      ring
    rw [← this]
    ring
  unfold ballIndicator
  by_cases hx : x + b ∈ ordBall K N
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.1 hx), Pi.one_apply, mul_one, ← hμ]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hm.2 h)), mul_zero,
      mul_zero]

/-- **Self-duality on translated balls.** If $\psi$ has conductor exponent $n$ and the Haar measure $\mu$ satisfies $\mu(\mathcal{O}_K)^2 q^n = 1$, then $\hat{\hat{\varphi}}(x) = \varphi(-x)$ for each $\varphi = \mathbf{1}_{b + \varpi^N \mathcal{O}_K}$. -/
theorem fourier_fourier_ballIndicator_of_selfDual {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    (hμ : μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n = 1) (b : K) (N : ℤ) (x : K) :
    fourier μ ψ (fourier μ ψ (ballIndicator b N)) x = ballIndicator b N (-x) := by
  rw [fourier_fourier_ballIndicator μ hψ, hμ, Complex.ofReal_one, one_mul]

omit [BorelSpace K] [μ.Regular] in
/-- **The self-dual measure.** For each $n$ there is a unique $c \ge 0$ such that the multiple $\nu = c \mu$ of the Haar measure $\mu$ satisfies $\nu(\mathcal{O}_K)^2 q^n = 1$. For this $\nu$ and an additive character of conductor exponent $n$, the Fourier transform is self-dual on translated balls. -/
theorem existsUnique_selfDual (n : ℤ) :
    ∃! c : ℝ≥0, (c • μ).real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n = 1 := by
  have hm : 0 < μ.real (ordBall K 0) :=
    ENNReal.toReal_pos (measure_ordBall_ne_zero μ 0) (measure_ordBall_ne_top μ 0)
  have hQ : 0 < (residueCard K : ℝ) ^ n := zpow_pos (by exact_mod_cast residueCard_pos') n
  have hsq := Real.sqrt_pos.2 hQ
  have hsq2 := Real.sq_sqrt hQ.le
  set m := μ.real (ordBall K 0)
  set Q := (residueCard K : ℝ) ^ n
  have hr : 0 ≤ 1 / (m * Real.sqrt Q) := by positivity
  refine ⟨(1 / (m * Real.sqrt Q)).toNNReal, ?_, fun c hc => ?_⟩
  · beta_reduce
    rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hr]
    field_simp
    rw [hsq2]
  · beta_reduce at hc
    rw [measureReal_nnreal_smul_apply] at hc
    have h2 : ((c : ℝ) * m) ^ 2 = (1 / Real.sqrt Q) ^ 2 := by
      rw [div_pow, one_pow, hsq2, eq_div_iff hQ.ne']
      exact hc
    rw [pow_left_inj₀ (by positivity) (by positivity) two_ne_zero] at h2
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hr, one_div, mul_inv, ← one_div (Real.sqrt Q), ← h2]
    field_simp

end SelfDual

end Langlands.LocalGL1
