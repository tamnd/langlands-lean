/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1EpsilonRamified

/-!
# Tate's local functional equation for an unramified character

Let $K$ be a nonarchimedean local field, let $\chi$ be a smooth character of $K^\times$ that is trivial on $\mathcal{O}_K^\times$, and let $\psi$ be an additive character of conductor exponent $n$. This module proves Tate's local functional equation $$\frac{Z(\hat{\varphi}, \chi^{-1}, 1 - s)}{L(1 - s, \chi^{-1})} = \varepsilon(s, \chi, \psi) \frac{Z(\varphi, \chi, s)}{L(s, \chi)}$$ for each locally constant function $\varphi$ with compact support and each $s$ in the strip where both zeta integrals converge. Here $L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ and $\varepsilon = $ `epsilonUnramified`. The equation is stated in the multiplied form of `localFunctionalEquation_unramified`.

## Main results

* `Langlands.LocalGL1.extChar_eq_zpow_of_unramified`: $\chi(y) = \chi(\varpi)^{\mathrm{ord}(y)}$ for $y \ne 0$.
* `Langlands.LocalGL1.zeta_indicator_oneAddBall_of_unramified`: $Z(\mathbf{1}_{1 + \mathfrak{p}^M}, \chi, s) = \mu(\mathfrak{p}^M)$ for $M \ge 1$.
* `Langlands.LocalGL1.localFunctionalEquation_unramified_ordBall`: the functional equation for $\mathbf{1}_{\varpi^N \mathcal{O}_K}$.
* `Langlands.LocalGL1.localFunctionalEquation_unramified_oneAddBall`: the functional equation for $\mathbf{1}_{1 + \mathfrak{p}^M}$ with $M \ge 1$.
* `Langlands.LocalGL1.integral_indicator_ordShell_addChar_of_lt` and `Langlands.LocalGL1.integral_indicator_ordShell_addChar`: $\int_{\mathrm{ord}(y) = m} \psi$ is $0$ for $m < -n - 1$ and $-\mu(\mathfrak{p}^{-n})$ for $m = -n - 1$.
* `Langlands.LocalGL1.localFunctionalEquation_unramified_comp_inv_mul`: the functional equation is stable under the dilations $\varphi \mapsto \varphi(b^{-1} \cdot)$.
* `Langlands.LocalGL1.localFunctionalEquation_unramified_ballIndicator`: the functional equation for each translated ball $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$.
* `Langlands.LocalGL1.localFunctionalEquation_unramified_of_isLocallyConstant`: the functional equation for each locally constant function with compact support.
* `Langlands.LocalGL1.zeta_fourier_mul_zeta_eq_of_unramified` and `Langlands.LocalGL1.zeta_fourier_div_zeta_eq_of_unramified`: the ratio $Z(\hat{\varphi}, \chi^{-1}, 1 - s) / Z(\varphi, \chi, s)$ does not depend on $\varphi$.

## Proof

A ball $b + \varpi^N \mathcal{O}_K$ with $b \in \varpi^N \mathcal{O}_K$ is the ball $\varpi^N \mathcal{O}_K$. Its Fourier transform is $\mu(\mathfrak{p}^N) \mathbf{1}_{\varpi^{-n-N} \mathcal{O}_K}$, and both zeta integrals are geometric series. A ball $b + \varpi^N \mathcal{O}_K$ with $\mathrm{ord}(b) < N$ is the dilation of $\mathbf{1}_{1 + \mathfrak{p}^M}$ by $b$, with $M = N - \mathrm{ord}(b) \ge 1$, and a dilation multiplies both sides by $\chi(b) (q^{-s})^{\mathrm{ord}(b)}$. For $\varphi = \mathbf{1}_{1 + \mathfrak{p}^M}$, the zeta integral is $\mu(\mathfrak{p}^M)$, because $\chi$ and $|\cdot|$ are $1$ on $1 + \mathfrak{p}^M$. The Fourier transform is $\mu(\mathfrak{p}^M) \psi \mathbf{1}_{\varpi^{-n-M} \mathcal{O}_K}$. Its zeta integral is a sum over the shells $\mathrm{ord}(y) = j$. On a shell $\chi^{-1}$ is constant, so the shell gives $\chi(\varpi)^{-j} (q^{s})^{j} \int_{\mathrm{ord}(y) = j} \psi$. By orthogonality this integral is $0$ for $j < -n - 1$ and $-\mu(\mathfrak{p}^{-n})$ for $j = -n - 1$. On $\varpi^{-n} \mathcal{O}_K$ the character $\psi$ is $1$, and the integral is a geometric series. The general case follows from the decomposition `exists_eq_sum_ballIndicator` and the linearity results `fourier_sum` and `zeta_sum`.

## Open parts

* The independence of the ratio for a ramified character is not stated here. It follows from `localFunctionalEquation_of_isLocallyConstant` in the same way.
-/

namespace Langlands.LocalGL1

universe u

open MeasureTheory

section Dilation

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ) [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- Dilation of the dual zeta integral: $Z(\widehat{\varphi(b^{-1} \cdot)}, \chi^{-1}, 1 - s) = \chi(b) (q^{-s})^{\mathrm{ord}(b)} Z(\hat{\varphi}, \chi^{-1}, 1 - s)$. -/
private theorem zeta_fourier_comp_inv_mul (ψ : AddChar K ℂ) (φ : K → ℂ) {b : K} (hb : b ≠ 0)
    (s : ℂ) : zeta χ⁻¹ μ (fourier μ ψ fun x => φ (b⁻¹ * x)) (1 - s) =
      χ (Units.mk0 b hb) * ((residueCard K : ℂ) ^ (-s)) ^ ord K b *
        zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) := by
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hX := cpow_neg_ne_zero (K := K) s
  have hf : fourier μ ψ (fun x => φ (b⁻¹ * x)) =
      fun ξ => ((residueCard K : ℂ) ^ ord K b)⁻¹ * fourier μ ψ φ ((b⁻¹)⁻¹ * ξ) := by
    funext ξ; rw [fourier_comp_inv_mul μ ψ φ hb, inv_inv]
  have hz : zeta χ⁻¹ μ (fun ξ => ((residueCard K : ℂ) ^ ord K b)⁻¹ *
      fourier μ ψ φ ((b⁻¹)⁻¹ * ξ)) (1 - s) = ((residueCard K : ℂ) ^ ord K b)⁻¹ *
        zeta χ⁻¹ μ (fun ξ => fourier μ ψ φ ((b⁻¹)⁻¹ * ξ)) (1 - s) := by
    unfold zeta; rw [← integral_const_mul]; congr 1; funext x; ring
  have hu : (Units.mk0 b⁻¹ (inv_ne_zero hb)) = (Units.mk0 b hb)⁻¹ := by ext; simp
  rw [hf, hz, zeta_comp_inv_mul χ⁻¹ μ _ (inv_ne_zero hb), hu, map_inv, ord_inv hb,
    cpow_neg_one_sub]
  simp only [MonoidHom.inv_apply, inv_inv]
  rw [mul_zpow, inv_zpow', inv_zpow', zpow_neg, neg_neg]
  field_simp
  rw [← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_mul]

end Dilation

section Unramified

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

/-- The inverse of a character that is trivial on $\mathcal{O}_K^\times$ is trivial on $\mathcal{O}_K^\times$. -/
theorem inv_apply_of_unramified (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) :
    ∀ x : Kˣ, normAbs K x = 1 → χ⁻¹ x = 1 := fun x hx => by
  rw [MonoidHom.inv_apply, hχ1 x hx, inv_one]

/-- If $\chi$ is trivial on $\mathcal{O}_K^\times$, then $\chi(y) = \chi(\varpi)^{\mathrm{ord}(y)}$ for each $y \ne 0$. -/
theorem extChar_eq_zpow_of_unramified (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {y : K}
    (hy : y ≠ 0) : extChar χ y = (χ (unif K) : ℂ) ^ ord K y := by
  have ha : (unif K : K) ^ ord K y ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have hu := mem_ordShell_zero_div hy
  have hyu : y = (unif K : K) ^ ord K y * (y * ((unif K : K) ^ ord K y)⁻¹) := by field_simp
  conv_lhs => rw [hyu]
  rw [extChar_mul χ ha, extChar_of_ne_zero χ hu.1,
    hχ1 (Units.mk0 _ hu.1) (by rw [Units.val_mk0]; exact (normAbs_eq_one_iff hu.1).2 hu.2),
    Units.val_one, mul_one]
  have : Units.mk0 ((unif K : K) ^ ord K y) ha = unif K ^ ord K y := by
    ext
    simp
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K)

omit [BorelSpace K] in
/-- If $\chi$ is trivial on $\mathcal{O}_K^\times$, then $\int_{\mathrm{ord}(y) = m} \varphi(y) \chi(y) \, dy = \chi(\varpi)^m \int_{\mathrm{ord}(y) = m} \varphi$. -/
theorem shellCoeff_of_unramified (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) (φ : K → ℂ)
    (m : ℤ) : shellCoeff χ μ φ m = (χ (unif K) : ℂ) ^ m * ∫ y, (ordShell K m).indicator φ y ∂μ := by
  unfold shellCoeff
  rw [← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ ordShell K m
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, extChar_eq_zpow_of_unramified χ hχ1 hy.1,
      hy.2]
    ring
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

variable [μ.IsAddHaarMeasure]

omit χ in
/-- For a continuous function $f$, $\int_{\mathrm{ord} = m} f = \int_{\varpi^m \mathcal{O}_K} f - \int_{\varpi^{m + 1} \mathcal{O}_K} f$. -/
theorem integral_indicator_ordShell {f : K → ℂ} (hf : Continuous f) (m : ℤ) :
    ∫ y, (ordShell K m).indicator f y ∂μ =
      ∫ y, (ordBall K m).indicator f y ∂μ - ∫ y, (ordBall K (m + 1)).indicator f y ∂μ := by
  have hS : Integrable ((ordShell K m).indicator f) μ :=
    (integrable_indicator_iff (isClosed_ordShell m).measurableSet).2
      (hf.continuousOn.integrableOn_compact (isCompact_ordShell m))
  simp_rw [indicator_ordBall_eq m f]
  rw [integral_add (integrable_indicator_of_continuous μ hf (m + 1)) hS]
  ring

omit χ in
/-- The volume of $\mathcal{O}_K^\times$ is $\mu(\mathcal{O}_K) - \mu(\mathfrak{p})$. -/
theorem measureReal_ordShell_zero :
    μ.real (ordShell K 0) = μ.real (ordBall K 0) - μ.real (ordBall K 1) := by
  have h := integral_indicator_ordShell μ (f := fun _ => (1 : ℂ)) continuous_const 0
  rw [integral_indicator_const _ (isClosed_ordShell 0).measurableSet,
    integral_indicator_const _ (isClosed_ordBall 0).measurableSet,
    integral_indicator_const _ (isClosed_ordBall _).measurableSet, zero_add] at h
  simp only [Complex.real_smul, mul_one] at h
  exact_mod_cast h

omit χ in
/-- If $\psi$ has conductor exponent $n$ and $m < -n - 1$, then $\int_{\mathrm{ord}(y) = m} \psi = 0$. -/
theorem integral_indicator_ordShell_addChar_of_lt {ψ : AddChar K ℂ} {n : ℤ}
    (hψ : IsConductor ψ n) {m : ℤ} (hm : m < -n - 1) :
    ∫ y, (ordShell K m).indicator (⇑ψ) y ∂μ = 0 := by
  obtain ⟨t, ht, hψt⟩ := hψ.nontrivial
  rw [integral_indicator_ordShell μ hψ.continuous m,
    integral_indicator_addChar_of_ne_one μ ψ (ordBall_anti (by omega) ht) hψt,
    integral_indicator_addChar_of_ne_one μ ψ (ordBall_anti (by omega) ht) hψt, sub_zero]

omit χ in
/-- If $\psi$ has conductor exponent $n$, then $\int_{\mathrm{ord}(y) = -n - 1} \psi = -\mu(\mathfrak{p}^{-n})$. -/
theorem integral_indicator_ordShell_addChar {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) :
    ∫ y, (ordShell K (-n - 1)).indicator (⇑ψ) y ∂μ = -(μ.real (ordBall K (-n)) : ℂ) := by
  obtain ⟨t, ht, hψt⟩ := hψ.nontrivial
  rw [integral_indicator_ordShell μ hψ.continuous, integral_indicator_addChar_of_ne_one μ ψ ht hψt,
    show -n - 1 + 1 = -n by ring, integral_indicator_addChar_of_forall μ ψ hψ.trivial, zero_sub]

/-- If $\chi$ is trivial on $\mathcal{O}_K^\times$ and $M \ge 1$, then $Z(\mathbf{1}_{1 + \mathfrak{p}^M}, \chi, s) = \mu(\mathfrak{p}^M)$, because $\chi$ and $|\cdot|$ are $1$ on $1 + \mathfrak{p}^M$. -/
theorem zeta_indicator_oneAddBall_of_unramified (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {M : ℤ} (hM : 1 ≤ M) (s : ℂ) :
    zeta χ μ ((oneAddBall M).indicator 1) s = μ.real (ordBall K M) := by
  have : ∀ y, (oneAddBall M).indicator (1 : K → ℂ) y * zetaFn χ s y =
      (oneAddBall M).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    by_cases hy : y ∈ oneAddBall M
    · obtain ⟨hy0, hord⟩ := ne_zero_and_ord_eq_zero_of_mem_oneAddBall hM hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, one_mul, zetaFn,
        extChar_of_ne_zero χ hy0,
        hχ1 (Units.mk0 y hy0) (by rw [Units.val_mk0]; exact (normAbs_eq_one_iff hy0).2 hord),
        (normAbs_eq_one_iff hy0).2 hord]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold zeta
  simp_rw [this]
  rw [integral_indicator_const _ (measurableSet_oneAddBall _), Complex.real_smul, mul_one,
    measureReal_oneAddBall]

variable [μ.Regular]

/-- **The local functional equation for $\mathbf{1}_{\varpi^N \mathcal{O}_K}$.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$ and let $\psi$ have conductor exponent $n$. For each $N$ and each $s$ in the strip of convergence, the function $\varphi = \mathbf{1}_{\varpi^N \mathcal{O}_K}$ satisfies the functional equation of `localFunctionalEquation_unramified`. -/
theorem localFunctionalEquation_unramified_ordBall (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    (N : ℤ) {s : ℂ} (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ ((ordBall K N).indicator 1)) (1 - s) *
        (1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))) =
      epsilonUnramified χ μ n s * (zeta χ μ ((ordBall K N).indicator 1) s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))) := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  have h1 := zeta_indicator_ordBall_of_unramified χ μ hχ hχ1 hs 1 N
  have h2 := zeta_indicator_ordBall_of_unramified χ⁻¹ μ (isSmoothChar_inv χ hχ)
    (inv_apply_of_unramified χ hχ1) hs2 (μ.real (ordBall K N)) (-n - N)
  rw [inv_apply_coe] at h2
  have he : ((ordBall K N).indicator 1 : K → ℂ) = (ordBall K N).indicator fun _ => (1 : ℂ) := rfl
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hx : (χ (unif K) : ℂ) ≠ 0 := Units.ne_zero _
  have hX := cpow_neg_ne_zero (K := K) s
  rw [fourier_indicator_ordBall μ hψ N, h2, he, h1, epsilonUnramified, measureReal_ordBall μ N,
    cpow_neg_one_sub, mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow',
    show -(-n - N) = n + N by ring, zpow_add₀ hx, zpow_add₀ hq, zpow_add₀ hX, mul_zpow]
  push_cast
  rw [zpow_neg]
  field_simp

/-- **The local functional equation for $\mathbf{1}_{1 + \mathfrak{p}^M}$.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$ and let $\psi$ have conductor exponent $n$. For each $M \ge 1$ and each $s$ with $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, the function $\varphi = \mathbf{1}_{1 + \mathfrak{p}^M}$ satisfies the functional equation of `localFunctionalEquation_unramified`. The shells $\mathrm{ord} = j$ with $-n - M \le j < -n - 1$ give $0$, the shell $\mathrm{ord} = -n - 1$ gives $-\chi(\varpi)^{n + 1} (q^{-s})^{n + 1} \mu(\mathfrak{p}^{-n})$, and the ball $\varpi^{-n} \mathcal{O}_K$ gives a geometric series. -/
theorem localFunctionalEquation_unramified_oneAddBall (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    {M : ℤ} (hM : 1 ≤ M) {s : ℂ}
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ ((oneAddBall M).indicator 1)) (1 - s) *
        (1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))) =
      epsilonUnramified χ μ n s * (zeta χ μ ((oneAddBall M).indicator 1) s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))) := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  have hχ1' := inv_apply_of_unramified χ hχ1
  have hψc := hψ.continuous
  set B := ordBall K (-n - M) with hB
  set g := B.indicator (⇑ψ) with hg
  set μa : ℂ := (μ.real (ordBall K M) : ℂ) with hμa
  have hgB : ∀ y ∈ B, g y = ψ y := fun y hy => by rw [hg, Set.indicator_of_mem hy]
  have hfour : fourier μ ψ ((oneAddBall M).indicator 1) = fun ξ => μa * g ξ := by
    funext ξ
    rw [fourier_indicator_oneAddBall μ hψ]
    by_cases hξ : ξ ∈ B
    · rw [hg, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      ring
    · rw [hg, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero, mul_zero]
  have hzeta : zeta χ⁻¹ μ (fun ξ => μa * g ξ) (1 - s) = μa * ballZeta χ⁻¹ μ g (1 - s) (-n - M) := by
    unfold zeta ballZeta
    rw [← integral_const_mul]
    congr 1
    funext y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, mul_assoc]
    · rw [Set.indicator_of_notMem hy]
      simp only [hg, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  obtain ⟨C, hC⟩ := (isCompact_ordBall (K := K) (-n - M)).exists_bound_of_continuousOn
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
  have hsh : ∀ m : ℤ, -n - M ≤ m → shellCoeff χ⁻¹ μ g m =
      ((χ⁻¹ (unif K) : ℂˣ) : ℂ) ^ m * ∫ y, (ordShell K m).indicator (⇑ψ) y ∂μ := by
    intro m hm
    rw [shellCoeff_of_unramified χ⁻¹ μ hχ1' g m]
    congr 2
    funext y
    by_cases hy : y ∈ ordShell K m
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
        hgB y (ordBall_anti hm (ordShell_subset_ordBall _ hy))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hdesc : ∀ k : ℕ, (k : ℤ) ≤ M - 1 →
      ballZeta χ⁻¹ μ g (1 - s) (-n - 1 - k) = ballZeta χ⁻¹ μ g (1 - s) (-n - 1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h0 := ballZeta_eq_succ_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχ) hs2 hgm hgC
        (-n - 1 - (k + 1 : ℕ))
      rw [hsh _ (by push_cast; omega), integral_indicator_ordShell_addChar_of_lt μ hψ
        (by push_cast; omega), mul_zero, zero_mul, add_zero,
        show -n - 1 - ((k + 1 : ℕ) : ℤ) + 1 = -n - 1 - k by push_cast; ring] at h0
      rw [h0, ih (by omega)]
  have hMk : -n - M = -n - 1 - ((M - 1).toNat : ℕ) := by omega
  have hstep := ballZeta_eq_succ_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχ) hs2 hgm hgC (-n - 1)
  rw [hsh _ (by omega), integral_indicator_ordShell_addChar μ hψ,
    show -n - 1 + 1 = -n by ring] at hstep
  have hT : ballZeta χ⁻¹ μ g (1 - s) (-n) = ballZeta χ⁻¹ μ (fun _ => 1) (1 - s) (-n) := by
    unfold ballZeta
    congr 1
    funext y
    by_cases hy : y ∈ ordBall K (-n)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hgB y (ordBall_anti (by omega) hy),
        hψ.trivial y hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hT0 := ballZeta_one_zero_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχ) hs2
  rw [shellCoeff_one_of_unramified χ⁻¹ μ hχ1', measureReal_ordShell_zero, measureReal_ordBall μ 1,
    inv_apply_coe] at hT0
  rw [hfour, hzeta, hMk, hdesc _ (by omega), hstep, hT, ballZeta_one_zpow,
    zeta_indicator_oneAddBall_of_unramified χ μ hχ1 hM, measureReal_ordBall μ (-n), inv_apply_coe,
    epsilonUnramified, ← hμa]
  set T0 := ballZeta χ⁻¹ μ (fun _ => 1) (1 - s) 0
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hx : (χ (unif K) : ℂ) ≠ 0 := Units.ne_zero _
  have hX := cpow_neg_ne_zero (K := K) s
  rw [cpow_neg_one_sub] at hT0 ⊢
  push_cast at hT0 ⊢
  set x : ℂ := (χ (unif K) : ℂ)
  set q : ℂ := (residueCard K : ℂ)
  set t : ℂ := q ^ (-s)
  set m0 : ℂ := (μ.real (ordBall K 0) : ℂ)
  rw [show q⁻¹ * t⁻¹ * q = t⁻¹ by field_simp, mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow',
    inv_zpow', inv_zpow', neg_neg, show -(-n - 1) = n + 1 by ring, zpow_add_one₀ hx,
    zpow_add_one₀ hX]
  rw [zpow_neg_one] at hT0
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ hX
  linear_combination (μa * x ^ n * q ^ n * t ^ n) * hT0 +
    (μa * x ^ n * q ^ n * t ^ n * m0 * q⁻¹ * t * t⁻¹) * hxx +
    (μa * x ^ n * q ^ n * t ^ n * m0 * q⁻¹) * htt

omit [μ.Regular] in
/-- If the functional equation of `localFunctionalEquation_unramified` holds for $\varphi$, then it holds for $\varphi(b^{-1} \cdot)$ for each $b \ne 0$. Both sides are multiplied by $\chi(b) (q^{-s})^{\mathrm{ord}(b)}$. -/
theorem localFunctionalEquation_unramified_comp_inv_mul (ψ : AddChar K ℂ) {φ : K → ℂ} {b : K}
    (hb : b ≠ 0) {s A B ε : ℂ}
    (h : zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) * A = ε * (zeta χ μ φ s * B)) :
    zeta χ⁻¹ μ (fourier μ ψ fun x => φ (b⁻¹ * x)) (1 - s) * A =
      ε * (zeta χ μ (fun x => φ (b⁻¹ * x)) s * B) := by
  rw [zeta_fourier_comp_inv_mul χ μ ψ φ hb, zeta_comp_inv_mul χ μ φ hb]
  linear_combination ((χ (Units.mk0 b hb) : ℂ) * ((residueCard K : ℂ) ^ (-s)) ^ ord K b) * h

/-- **The local functional equation for a translated ball.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$ and let $\psi$ have conductor exponent $n$. For each $b$ and $N$ and each $s$ in the strip of convergence, the function $\varphi = \mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ satisfies the functional equation of `localFunctionalEquation_unramified`. For $b \in \varpi^N \mathcal{O}_K$ the function is $\mathbf{1}_{\varpi^N \mathcal{O}_K}$. For $\mathrm{ord}(b) < N$ it is a dilation of $\mathbf{1}_{1 + \mathfrak{p}^{N - \mathrm{ord}(b)}}$. -/
theorem localFunctionalEquation_unramified_ballIndicator (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    (b : K) (N : ℤ) {s : ℂ} (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ (ballIndicator b N)) (1 - s) *
        (1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))) =
      epsilonUnramified χ μ n s * (zeta χ μ (ballIndicator b N) s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))) := by
  by_cases hbN : b ∈ ordBall K N
  · have he : ballIndicator b N = (ordBall K N).indicator 1 := by
      funext x
      unfold ballIndicator
      have hm : x - b ∈ ordBall K N ↔ x ∈ ordBall K N := by
        rw [sub_eq_add_neg]
        exact add_mem_ordBall_iff (neg_mem_ordBall hbN) x
      by_cases hx : x ∈ ordBall K N
      · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx]
        rfl
      · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx]
    rw [he]
    exact localFunctionalEquation_unramified_ordBall χ μ hχ hχ1 hψ N hs hs'
  have hb : b ≠ 0 := fun h => hbN (h ▸ zero_mem_ordBall N)
  have hlt : ord K b < N := by
    rw [mem_ordBall_of_ne_zero hb, not_le] at hbN
    exact hbN
  rw [ballIndicator_eq_comp hb]
  exact localFunctionalEquation_unramified_comp_inv_mul χ μ ψ hb
    (localFunctionalEquation_unramified_oneAddBall χ μ hχ hχ1 hψ (by omega) hs')

/-- **Tate's local functional equation for an unramified character.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$ and let $\psi$ be an additive character of conductor exponent $n$. For each locally constant function $\varphi$ with compact support and each $s$ in the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, where both zeta integrals converge, $$\frac{Z(\hat{\varphi}, \chi^{-1}, 1 - s)}{L(1 - s, \chi^{-1})} = \varepsilon(s, \chi, \psi) \frac{Z(\varphi, \chi, s)}{L(s, \chi)},$$ with $L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ and $\varepsilon = $ `epsilonUnramified`. The proof writes $\varphi$ as a finite combination of translated balls by `exists_eq_sum_ballIndicator` and uses `localFunctionalEquation_unramified_ballIndicator` on each ball. -/
theorem localFunctionalEquation_unramified_of_isLocallyConstant (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    {φ : K → ℂ} (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) *
        (1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))) =
      epsilonUnramified χ μ n s * (zeta χ μ φ s *
        (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))) := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  have hψc := hψ.continuous
  obtain ⟨N, T, hT⟩ := exists_eq_sum_ballIndicator hφ hφs
  have hφe : φ = fun x => ∑ b ∈ T, φ b * ballIndicator b N x := funext hT
  have hbb : ∀ b ∈ T, IsBallBounded μ (ballIndicator b N) := fun b _ =>
    isBallBounded_of_isLocallyConstant μ (isLocallyConstant_ballIndicator b N)
      (hasCompactSupport_ballIndicator b N)
  have hfb : ∀ b ∈ T, IsBallBounded μ (fourier μ ψ (ballIndicator b N)) := by
    intro b _
    have : fourier μ ψ (ballIndicator b N) = (ordBall K (-n - N)).indicator
        fun ξ => ψ (b * ξ) * (μ.real (ordBall K N) : ℂ) := by
      funext ξ
      rw [fourier_ballIndicator μ hψ]
      by_cases hξ : ξ ∈ ordBall K (-n - N)
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero]
    rw [this]
    exact isBallBounded_indicator μ
      ((hψc.comp (continuous_const.mul continuous_id)).mul continuous_const) _
  rw [hφe, fourier_sum μ hψc T _ _ hbb,
    zeta_sum μ χ⁻¹ (isSmoothChar_inv χ hχ) hs2 T _ _ hfb, zeta_sum μ χ hχ hs T _ _ hbb,
    Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  linear_combination φ b * localFunctionalEquation_unramified_ballIndicator χ μ hχ hχ1 hψ b N hs hs'

/-- **Independence of the test function, unramified case.** Let $\chi$ be a smooth character that is trivial on $\mathcal{O}_K^\times$ and let $\psi$ have conductor exponent $n$. For locally constant functions $\varphi_1, \varphi_2$ with compact support and each $s$ in the strip of convergence, $Z(\hat{\varphi}_1, \chi^{-1}, 1 - s) Z(\varphi_2, \chi, s) = Z(\hat{\varphi}_2, \chi^{-1}, 1 - s) Z(\varphi_1, \chi, s)$. -/
theorem zeta_fourier_mul_zeta_eq_of_unramified (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    {φ₁ φ₂ : K → ℂ} (hφ₁ : IsLocallyConstant φ₁) (hφ₁s : HasCompactSupport φ₁)
    (hφ₂ : IsLocallyConstant φ₂) (hφ₂s : HasCompactSupport φ₂) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ φ₁) (1 - s) * zeta χ μ φ₂ s =
      zeta χ⁻¹ μ (fourier μ ψ φ₂) (1 - s) * zeta χ μ φ₁ s := by
  have hA : 1 - (χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s)) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hs'
    exact lt_irrefl _ hs'
  have h₁ := localFunctionalEquation_unramified_of_isLocallyConstant χ μ hχ hχ1 hψ hφ₁ hφ₁s hs hs'
  have h₂ := localFunctionalEquation_unramified_of_isLocallyConstant χ μ hχ hχ1 hψ hφ₂ hφ₂s hs hs'
  refine mul_right_cancel₀ hA ?_
  linear_combination zeta χ μ φ₂ s * h₁ - zeta χ μ φ₁ s * h₂

/-- **The ratio does not depend on the test function, unramified case.** Under the hypotheses of `zeta_fourier_mul_zeta_eq_of_unramified`, if $Z(\varphi_1, \chi, s) \ne 0$ and $Z(\varphi_2, \chi, s) \ne 0$, then $Z(\hat{\varphi}_1, \chi^{-1}, 1 - s) / Z(\varphi_1, \chi, s) = Z(\hat{\varphi}_2, \chi^{-1}, 1 - s) / Z(\varphi_2, \chi, s)$. -/
theorem zeta_fourier_div_zeta_eq_of_unramified (hχ : IsSmoothChar K χ)
    (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n)
    {φ₁ φ₂ : K → ℂ} (hφ₁ : IsLocallyConstant φ₁) (hφ₁s : HasCompactSupport φ₁)
    (hφ₂ : IsLocallyConstant φ₂) (hφ₂s : HasCompactSupport φ₂) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1)
    (h₁ : zeta χ μ φ₁ s ≠ 0) (h₂ : zeta χ μ φ₂ s ≠ 0) :
    zeta χ⁻¹ μ (fourier μ ψ φ₁) (1 - s) / zeta χ μ φ₁ s =
      zeta χ⁻¹ μ (fourier μ ψ φ₂) (1 - s) / zeta χ μ φ₂ s := by
  rw [div_eq_div_iff h₁ h₂]
  exact zeta_fourier_mul_zeta_eq_of_unramified χ μ hχ hχ1 hψ hφ₁ hφ₁s hφ₂ hφ₂s hs hs'

end Unramified

end Langlands.LocalGL1
