/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1EpsilonFull

/-!
# Tate's local functional equation for a ramified character

Let $K$ be a nonarchimedean local field, let $\chi$ be a smooth character of $K^\times$ of conductor exponent $a \ge 1$, and let $\psi$ be a continuous additive character of conductor exponent $n$. This module proves Tate's local functional equation $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s), \quad \varepsilon(s, \chi, \psi) = G(\chi, \psi) (q^{-s})^{a + n},$$ for each locally constant function $\varphi$ with compact support and each $s$ in the strip of convergence. It also proves that the Gauss integral $G(\chi, \psi)$ is not zero. Thus $\varepsilon(s, \chi, \psi)$ is a unit of $\mathbb{C}[q^{-s}, q^{s}]$, as Tate's theory says.

## Main definitions

* `Langlands.LocalGL1.epsilonRamified`: the ε-factor $G(\chi, \psi) (q^{-s})^{a + n}$.

## Main results

* `shellCoeff_addChar_eq_zero_of_lt`: $\int_{\mathrm{ord}(y) = j} \psi(y) \chi^{-1}(y) \, dy = 0$ for $j < -n - a$.
* `ballZeta_addChar_eq_zero_of_le`: the integral of $\psi \chi^{-1} |\cdot|^{s - 1}$ on $\varpi^L \mathcal{O}_K$ is $0$ for $L > -n - a$.
* `zeta_indicator_ordBall_eq_zero`, `zeta_indicator_oneAddBall_of_lt` and `zeta_indicator_oneAddBall_of_le`: the zeta integrals of $\mathbf{1}_{\varpi^L \mathcal{O}_K}$ and $\mathbf{1}_{1 + \mathfrak{p}^M}$.
* `localFunctionalEquation_oneAddBall`: the functional equation for $\mathbf{1}_{1 + \mathfrak{p}^M}$ and each $M \in \mathbb{Z}$.
* `zeta_comp_inv_mul`, `fourier_comp_inv_mul` and `localFunctionalEquation_comp_inv_mul`: the functional equation is stable under the dilations $\varphi \mapsto \varphi(b^{-1} \cdot)$.
* `localFunctionalEquation_ballIndicator`: the functional equation for each translated ball $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$.
* `localFunctionalEquation_of_isLocallyConstant`: the functional equation for each locally constant function with compact support.
* `exists_mem_strip`: the strip of convergence is not empty.
* `gaussInt_ne_zero`: $G(\chi, \psi) \ne 0$.

## Proofs

The Fourier transform of $\mathbf{1}_{1 + \mathfrak{p}^M}$ is $\mu(\mathfrak{p}^M) \psi \mathbf{1}_{\varpi^{-n-M} \mathcal{O}_K}$. Its zeta integral is a sum over the shells $\mathrm{ord}(y) = j$ with $j \ge -n - M$. A shell with $j < -n - a$ gives $0$: a translation $y \mapsto y + t$ with $t \in \varpi^{j + a} \mathcal{O}_K$ and $\psi(t) \ne 1$ keeps the shell and $\chi^{-1}(y)$, and it multiplies $\psi(y)$ by $\psi(t)$. The ball $\varpi^{-n-a+1} \mathcal{O}_K$ gives $0$: a multiplication $y \mapsto u y$ with $u \in 1 + \mathfrak{p}^{a-1}$ and $\chi(u) \ne 1$ keeps $\psi(y)$ there. So only the shell $j = -n - a$ remains, and it gives the Gauss integral. For $M < a$ both sides are $0$. A translated ball $b + \varpi^N \mathcal{O}_K$ with $b \ne 0$ is the dilation of $1 + \mathfrak{p}^{N - \mathrm{ord}(b)}$ by $b$, and a dilation multiplies both sides by $\chi(b) (q^{-s})^{\mathrm{ord}(b)}$. The ball around $0$ gives $0$ on both sides. The general case follows from the decomposition `exists_eq_sum_ballIndicator` and the linearity results `fourier_sum` and `zeta_sum`. For the Gauss integral, apply the functional equation to $\varphi = \mathbf{1}_{1 + \mathfrak{p}^a}$ for $\chi$ and then to $\hat{\varphi}$ for $\chi^{-1}$. Fourier inversion gives $\hat{\hat{\varphi}}(x) = c \varphi(-x)$ with $c \ne 0$, and $Z(\varphi, \chi, s) = \mu(\mathfrak{p}^a) \ne 0$. If $G(\chi, \psi) = 0$, the two equations give $c \chi(-1) \mu(\mathfrak{p}^a) = 0$, which is false.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta functions*, section 2.4.
* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 6.
-/

namespace Langlands.LocalGL1

universe u

open MeasureTheory

section Balls

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ) [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [MeasurableSpace K] [BorelSpace K] in
/-- If $\mathrm{ord}(y) = j$ and $t \in \varpi^{j + a} \mathcal{O}_K$ with $a \ge 1$, then $y + t = (1 + y^{-1} t) y$ with $1 + y^{-1} t \in 1 + \mathfrak{p}^a$. -/
theorem one_add_inv_mul_mem_oneAddBall {j a : ℤ} {y t : K} (hy : y ∈ ordShell K j)
    (ht : t ∈ ordBall K (j + a)) : 1 + y⁻¹ * t ∈ oneAddBall a ∧ y + t = (1 + y⁻¹ * t) * y := by
  have hy0 : y ≠ 0 := hy.1
  refine ⟨?_, by field_simp⟩
  change 1 + y⁻¹ * t - 1 ∈ ordBall K a
  rw [add_sub_cancel_left, mul_mem_ordBall_iff (inv_ne_zero hy0), ord_inv hy0, hy.2]
  simpa [add_comm] using ht

omit [MeasurableSpace K] [BorelSpace K] in
/-- A translation by $t \in \varpi^{j + 1} \mathcal{O}_K$ keeps the shell $\mathrm{ord} = j$. -/
theorem add_mem_ordShell {j : ℤ} {y t : K} (hy : y ∈ ordShell K j) (ht : t ∈ ordBall K (j + 1)) :
    y + t ∈ ordShell K j := by
  obtain ⟨h1, h2⟩ := one_add_inv_mul_mem_oneAddBall hy ht
  obtain ⟨hu0, hu⟩ := ne_zero_and_ord_eq_zero_of_mem_oneAddBall le_rfl h1
  rw [h2]
  exact ⟨mul_ne_zero hu0 hy.1, by rw [ord_mul hu0 hy.1, hu, hy.2, zero_add]⟩

omit [MeasurableSpace K] [BorelSpace K] in
/-- A translation by $t \in \varpi^{j + 1} \mathcal{O}_K$ keeps the shell $\mathrm{ord} = j$ and its complement. -/
theorem add_mem_ordShell_iff {j : ℤ} {t : K} (ht : t ∈ ordBall K (j + 1)) (y : K) :
    y + t ∈ ordShell K j ↔ y ∈ ordShell K j := by
  refine ⟨fun h => ?_, fun h => add_mem_ordShell h ht⟩
  simpa using add_mem_ordShell h (neg_mem_ordBall ht)

variable {χ}

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- If $\chi$ is trivial on $1 + \mathfrak{p}^a$, $\mathrm{ord}(y) = j$ and $t \in \varpi^{j + a} \mathcal{O}_K$, then $\chi(y + t) = \chi(y)$. -/
theorem extChar_add_eq {a : ℕ} (hχ : IsRamifiedConductor χ a) {j : ℤ} {y t : K}
    (hy : y ∈ ordShell K j) (ht : t ∈ ordBall K (j + a)) : extChar χ (y + t) = extChar χ y := by
  obtain ⟨h1, h2⟩ := one_add_inv_mul_mem_oneAddBall hy ht
  have ha : (1 : ℤ) ≤ a := by exact_mod_cast hχ.one_le
  obtain ⟨hu0, -⟩ := ne_zero_and_ord_eq_zero_of_mem_oneAddBall ha h1
  rw [h2, extChar_mul χ hu0, hχ.trivial _ (by simpa using h1), Units.val_one, one_mul]

/-- **The shells below the conductor.** Let $\chi$ have conductor exponent $a \ge 1$ and $\psi$ conductor exponent $n$. If $j < -n - a$ and $\varphi = \psi$ on the shell $\mathrm{ord} = j$, then $\int_{\mathrm{ord}(y) = j} \varphi(y) \chi^{-1}(y) \, dy = 0$. The proof is the translation $y \mapsto y + t$ for some $t \in \varpi^{j + a} \mathcal{O}_K$ with $\psi(t) \ne 1$: it keeps the shell and $\chi^{-1}(y)$, and it multiplies $\psi(y)$ by $\psi(t)$. -/
theorem shellCoeff_addChar_eq_zero_of_lt {a : ℕ} (hχ : IsRamifiedConductor χ a)
    {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) {j : ℤ} (hj : j < -n - a) {φ : K → ℂ}
    (hφ : ∀ y ∈ ordShell K j, φ y = ψ y) : shellCoeff χ⁻¹ μ φ j = 0 := by
  have hχ' : IsRamifiedConductor χ⁻¹ a :=
    ⟨hχ.one_le, fun x hx => by rw [MonoidHom.inv_apply, hχ.trivial x hx, inv_one],
      by
        obtain ⟨u, h0, h1, h2⟩ := hχ.nontrivial
        exact ⟨u, h0, h1, fun h => h2 (inv_eq_one.1 (by rwa [MonoidHom.inv_apply] at h))⟩⟩
  obtain ⟨t, ht, hψt⟩ := hψ.nontrivial
  have ht' : t ∈ ordBall K (j + a) := ordBall_anti (by omega) ht
  have ht1 : t ∈ ordBall K (j + 1) := ordBall_anti (by have := hχ.one_le; omega) ht'
  set F := (ordShell K j).indicator (fun y => φ y * extChar χ⁻¹ y) with hF
  have hshift : (fun y => F (y + t)) = fun y => ψ t * F y := by
    funext y
    by_cases hy : y ∈ ordShell K j
    · rw [hF, Set.indicator_of_mem ((add_mem_ordShell_iff ht1 y).2 hy), Set.indicator_of_mem hy,
        hφ _ ((add_mem_ordShell_iff ht1 y).2 hy), hφ _ hy, extChar_add_eq hχ' hy ht',
        AddChar.map_add_eq_mul]
      ring
    · rw [hF, Set.indicator_of_notMem (fun h => hy ((add_mem_ordShell_iff ht1 y).1 h)),
        Set.indicator_of_notMem hy, mul_zero]
  have h := integral_add_right_eq_self (μ := μ) F t
  rw [hshift, integral_const_mul] at h
  have h1 : ψ t - 1 ≠ 0 := sub_ne_zero.2 hψt
  unfold shellCoeff
  refine (mul_eq_zero.1 (?_ : (ψ t - 1) * ∫ y, F y ∂μ = 0)).resolve_left h1
  rw [sub_mul, one_mul, h, sub_self]

/-- If $\mathrm{ord}(u) = 0$ and $F(u x) = z F(x)$ for each $x$ with $z \ne 1$, then $\int F \, d\mu = 0$. -/
theorem integral_eq_zero_of_mul {u : K} (hu : u ≠ 0) (hu0 : ord K u = 0) {F : K → ℂ} {z : ℂ}
    (hz : z ≠ 1) (h : ∀ x, F (u * x) = z * F x) : ∫ x, F x ∂μ = 0 := by
  have h' := integral_comp_mul_left μ hu F
  simp_rw [h] at h'
  rw [integral_const_mul, hu0, zpow_zero, one_smul] at h'
  have h1 : z - 1 ≠ 0 := sub_ne_zero.2 hz
  refine (mul_eq_zero.1 (?_ : (z - 1) * ∫ x, F x ∂μ = 0)).resolve_left h1
  rw [sub_mul, one_mul, h', sub_self]

omit [MeasurableSpace K] [BorelSpace K] in
/-- The ball $1 + \mathfrak{p}^M$ is stable under multiplication by a unit $u \in 1 + \mathfrak{p}^M$. -/
theorem mul_mem_oneAddBall_iff {M : ℤ} {u : K} (hu : u ∈ oneAddBall M)
    (hu0 : ord K u = 0) (huz : u ≠ 0) (y : K) : u * y ∈ oneAddBall M ↔ y ∈ oneAddBall M := by
  have key : ∀ {v : K}, v ∈ oneAddBall M → v ≠ 0 → ord K v = 0 → ∀ x, x ∈ oneAddBall M →
      v * x ∈ oneAddBall M := by
    intro v hv hv0 hvo x hx
    change v * x - 1 ∈ ordBall K M
    rw [show v * x - 1 = v * (x - 1) + (v - 1) by ring]
    refine add_mem_ordBall ?_ hv
    rw [mul_mem_ordBall_iff hv0, hvo, sub_zero]
    exact hx
  refine ⟨fun h => ?_, key hu huz hu0 y⟩
  have hinv : u⁻¹ ∈ oneAddBall M := by
    change u⁻¹ - 1 ∈ ordBall K M
    rw [show u⁻¹ - 1 = u⁻¹ * -(u - 1) by field_simp; ring, mul_mem_ordBall_iff (inv_ne_zero huz),
      ord_inv huz, hu0, neg_zero, sub_zero]
    exact neg_mem_ordBall hu
  have := key hinv (inv_ne_zero huz) (by rw [ord_inv huz, hu0, neg_zero]) _ h
  rwa [inv_mul_cancel_left₀ huz] at this

/-- **Balls are invisible to a ramified character.** If $\chi$ is ramified, then $Z(c \mathbf{1}_{\varpi^L \mathcal{O}_K}, \chi, s) = 0$ for each $L$, $c$ and $s$. -/
theorem zeta_indicator_ordBall_eq_zero {a : ℕ} (hχ : IsRamifiedConductor χ a) (L : ℤ) (c s : ℂ) :
    zeta χ μ ((ordBall K L).indicator fun _ => c) s = 0 := by
  obtain ⟨u, hu0, -, hχu⟩ := hχ.nontrivial
  refine integral_eq_zero_of_mul μ u.ne_zero hu0 (z := (χ u : ℂ)) ?_ fun x => ?_
  · intro h; exact hχu (Units.val_eq_one.1 h)
  have hm : (u : K) * x ∈ ordBall K L ↔ x ∈ ordBall K L := by
    rw [mul_mem_ordBall_iff u.ne_zero, hu0, sub_zero]
  rw [zetaFn_mul χ u.ne_zero, hu0, zpow_zero, mul_one, Units.mk0_val]
  by_cases hx : x ∈ ordBall K L
  · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx]; ring
  · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx]; ring

/-- **Small balls around $1$.** If $\chi$ has conductor exponent $a$ and $M < a$, then $Z(\mathbf{1}_{1 + \mathfrak{p}^M}, \chi, s) = 0$, because $\chi$ is not trivial on $1 + \mathfrak{p}^M$. -/
theorem zeta_indicator_oneAddBall_of_lt {a : ℕ} (hχ : IsRamifiedConductor χ a) {M : ℤ}
    (hMa : M < a) (s : ℂ) : zeta χ μ ((oneAddBall M).indicator 1) s = 0 := by
  obtain ⟨u, hu0, hu1, hχu⟩ := hχ.nontrivial
  have huM : (u : K) ∈ oneAddBall M := ordBall_anti (by omega) hu1
  refine integral_eq_zero_of_mul μ u.ne_zero hu0 (z := (χ u : ℂ)) ?_ fun x => ?_
  · intro h; exact hχu (Units.val_eq_one.1 h)
  have hm := mul_mem_oneAddBall_iff huM hu0 u.ne_zero x
  rw [zetaFn_mul χ u.ne_zero, hu0, zpow_zero, mul_one, Units.mk0_val]
  by_cases hx : x ∈ oneAddBall M
  · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx]; simp only [Pi.one_apply]; ring
  · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx]; ring

/-- **Large balls around $1$.** If $\chi$ has conductor exponent $a \le M$, then $Z(\mathbf{1}_{1 + \mathfrak{p}^M}, \chi, s) = \mu(\mathfrak{p}^M)$. -/
theorem zeta_indicator_oneAddBall_of_le {a : ℕ} (hχ : IsRamifiedConductor χ a) {M : ℤ}
    (hM : (a : ℤ) ≤ M) (s : ℂ) :
    zeta χ μ ((oneAddBall M).indicator 1) s = μ.real (ordBall K M) := by
  have ha : (1 : ℤ) ≤ M := le_trans (by exact_mod_cast hχ.one_le) hM
  have : ∀ y, (oneAddBall M).indicator (1 : K → ℂ) y * zetaFn χ s y =
      (oneAddBall M).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    by_cases hy : y ∈ oneAddBall M
    · obtain ⟨hy0, hord⟩ := ne_zero_and_ord_eq_zero_of_mem_oneAddBall ha hy
      have hya : y ∈ oneAddBall (a : ℤ) := ordBall_anti hM hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, one_mul, zetaFn,
        extChar_of_ne_zero χ hy0, hχ.trivial _ (by simpa using hya),
        (normAbs_eq_one_iff hy0).2 hord]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold zeta
  simp_rw [this]
  rw [integral_indicator_const _ (measurableSet_oneAddBall _), Complex.real_smul, mul_one,
    measureReal_oneAddBall]

/-- **Vanishing above the conductor, on any ball.** Let $\chi$ have conductor exponent $a \ge 1$ and $\psi$ conductor exponent $n$. If $L \ge -n - a + 1$ and $\varphi = \psi$ on $\varpi^L \mathcal{O}_K$, then $\int_{\varpi^L \mathcal{O}_K} \varphi(y) \chi^{-1}(y) |y|^{s - 1} \, dy = 0$. -/
theorem ballZeta_addChar_eq_zero_of_le {a : ℕ} (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ}
    {n : ℤ} (hψ : IsConductor ψ n) (s : ℂ) {L : ℤ} (hL : -n - a + 1 ≤ L) {φ : K → ℂ}
    (hφ : ∀ y ∈ ordBall K L, φ y = ψ y) : ballZeta χ⁻¹ μ φ s L = 0 := by
  obtain ⟨u, hu0, hu1, hχu⟩ := hχ.nontrivial
  refine integral_eq_zero_of_mul μ u.ne_zero hu0 (z := ((χ⁻¹ u : ℂˣ) : ℂ)) ?_ fun x => ?_
  · rw [inv_apply_coe]
    intro h
    exact hχu (Units.val_eq_one.1 (inv_eq_one.1 h))
  have hm : (u : K) * x ∈ ordBall K L ↔ x ∈ ordBall K L := by
    rw [mul_mem_ordBall_iff u.ne_zero, hu0, sub_zero]
  by_cases hx : x ∈ ordBall K L
  · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx, hφ _ (hm.2 hx), hφ _ hx,
      zetaFn_mul χ⁻¹ u.ne_zero, hu0, zpow_zero, mul_one, Units.mk0_val]
    have hψu : ψ ((u : K) * x) = ψ x := by
      have hmem : ((u : K) - 1) * x ∈ ordBall K (-n) := by
        have := mul_mem_ordBall_add hu1 hx
        exact ordBall_anti (by omega) this
      rw [show (u : K) * x = x + ((u : K) - 1) * x by ring, AddChar.map_add_eq_mul,
        hψ.trivial _ hmem, mul_one]
    rw [hψu]
    ring
  · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx, mul_zero]

variable (χ) in
/-- The ε-factor $\varepsilon(s, \chi, \psi) = G(\chi, \psi) (q^{-s})^{a + n}$ of a character $\chi$ of conductor exponent $a \ge 1$, for an additive character $\psi$ of conductor exponent $n$, with the Gauss integral $G(\chi, \psi)$ of `gaussInt` on the shell $\mathrm{ord} = -n - a$. -/
noncomputable def epsilonRamified (ψ : AddChar K ℂ) (a : ℕ) (n : ℤ) (s : ℂ) : ℂ :=
  gaussInt χ μ ψ (-n - a) * ((residueCard K : ℂ) ^ (-s)) ^ ((a : ℤ) + n)

/-- **The local functional equation for $\mathbf{1}_{1 + \mathfrak{p}^M}$.** Let $\chi$ have conductor exponent $a \ge 1$ and let $\psi$ be continuous of conductor exponent $n$. For each $M \in \mathbb{Z}$ and each $s$ with $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s), \quad \varphi = \mathbf{1}_{1 + \mathfrak{p}^M}.$$ For $M < a$ both sides are $0$. For $M \ge a$ the Fourier transform is $\mu(\mathfrak{p}^M) \psi \mathbf{1}_{\varpi^{-n-M} \mathcal{O}_K}$, and only the shell $\mathrm{ord} = -n - a$ gives a nonzero integral. -/
theorem localFunctionalEquation_oneAddBall (hχs : IsSmoothChar K χ) {a : ℕ}
    (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ} (hψc : Continuous ψ) {n : ℤ}
    (hψ : IsConductor ψ n) (M : ℤ) {s : ℂ}
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ ((oneAddBall M).indicator 1)) (1 - s) =
      epsilonRamified χ μ ψ a n s * zeta χ μ ((oneAddBall M).indicator 1) s := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
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
  rw [hfour, hzeta]
  rcases lt_or_ge M a with hMa | hMa
  · rw [ballZeta_addChar_eq_zero_of_le μ hχ hψ (1 - s) (by omega) hgB,
      zeta_indicator_oneAddBall_of_lt μ hχ hMa]
    ring
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
  have hdesc : ∀ k : ℕ, (k : ℤ) ≤ M - a →
      ballZeta χ⁻¹ μ g (1 - s) (-n - a - k) = ballZeta χ⁻¹ μ g (1 - s) (-n - a) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h0 := ballZeta_eq_succ_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχs) hs2 hgm hgC
        (-n - a - (k + 1 : ℕ))
      rw [shellCoeff_addChar_eq_zero_of_lt μ hχ hψ (by push_cast; omega) fun y hy =>
        hgB y (ordBall_anti (by push_cast; omega) (ordShell_subset_ordBall _ hy)), zero_mul,
        add_zero, show -n - a - ((k + 1 : ℕ) : ℤ) + 1 = -n - a - k by push_cast; ring] at h0
      rw [h0, ih (by omega)]
  have hMk : -n - M = -n - a - ((M - a).toNat : ℕ) := by omega
  rw [hMk, hdesc _ (by omega)]
  have hstep := ballZeta_eq_succ_of_lt χ⁻¹ μ (isSmoothChar_inv χ hχs) hs2 hgm hgC (-n - a)
  rw [ballZeta_addChar_eq_zero χ μ hχ hψ (1 - s) (φ := g) fun y hy =>
    hgB y (ordBall_anti (by omega) hy), zero_add] at hstep
  have hshell : shellCoeff χ⁻¹ μ g (-n - a) = gaussInt χ μ ψ (-n - a) := by
    unfold shellCoeff gaussInt
    congr 1
    funext y
    by_cases hy : y ∈ ordShell K (-n - a)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
        hgB y (ordBall_anti (by omega) (ordShell_subset_ordBall _ hy))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hX := cpow_neg_ne_zero (K := K) s
  rw [hstep, hshell, zeta_indicator_oneAddBall_of_le μ hχ hMa, epsilonRamified, cpow_neg_one_sub,
    show (residueCard K : ℂ)⁻¹ * ((residueCard K : ℂ) ^ (-s))⁻¹ * residueCard K =
      ((residueCard K : ℂ) ^ (-s))⁻¹ by field_simp, inv_zpow', neg_sub, sub_neg_eq_add, hμa]
  ring

omit [MeasurableSpace K] [BorelSpace K] in
/-- A character of conductor exponent $a$ has an inverse of conductor exponent $a$. -/
theorem IsRamifiedConductor.inv {a : ℕ} (hχ : IsRamifiedConductor χ a) :
    IsRamifiedConductor χ⁻¹ a :=
  ⟨hχ.one_le, fun x hx => by rw [MonoidHom.inv_apply, hχ.trivial x hx, inv_one], by
    obtain ⟨u, h0, h1, h2⟩ := hχ.nontrivial
    exact ⟨u, h0, h1, fun h => h2 (inv_eq_one.1 (by rwa [MonoidHom.inv_apply] at h))⟩⟩

variable (χ) in
/-- **Dilation of the zeta integral.** For $b \ne 0$, $Z(\varphi(b^{-1} \cdot), \chi, s) = \chi(b) (q^{-s})^{\mathrm{ord}(b)} Z(\varphi, \chi, s)$. -/
theorem zeta_comp_inv_mul (φ : K → ℂ) {b : K} (hb : b ≠ 0) (s : ℂ) :
    zeta χ μ (fun x => φ (b⁻¹ * x)) s =
      χ (Units.mk0 b hb) * ((residueCard K : ℂ) ^ (-s)) ^ ord K b * zeta χ μ φ s := by
  have h := integral_comp_mul_left μ hb fun x => φ (b⁻¹ * x) * zetaFn χ s x
  simp only [inv_mul_cancel_left₀ hb, zetaFn_mul χ hb] at h
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hqk : ((residueCard K : ℝ) ^ ord K b : ℝ) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast residueCard_pos'.ne')
  unfold zeta
  rw [Complex.real_smul] at h
  have h' : ∫ x, φ x * ((χ (Units.mk0 b hb) : ℂ) * ((residueCard K : ℂ) ^ (-s) *
      residueCard K) ^ ord K b * zetaFn χ s x) ∂μ =
      (χ (Units.mk0 b hb) : ℂ) * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ ord K b *
        ∫ x, φ x * zetaFn χ s x ∂μ := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [h'] at h
  have hc : (((residueCard K : ℝ) ^ ord K b : ℝ) : ℂ) = (residueCard K : ℂ) ^ ord K b := by
    push_cast; rfl
  rw [hc] at h
  rw [mul_zpow] at h
  have hqk' : (residueCard K : ℂ) ^ ord K b ≠ 0 := zpow_ne_zero _ hq
  apply mul_left_cancel₀ hqk'
  rw [← h]
  ring

/-- **Dilation of the Fourier transform.** For $b \ne 0$, $\widehat{\varphi(b^{-1} \cdot)}(\xi) = q^{-\mathrm{ord}(b)} \hat{\varphi}(b \xi)$. -/
theorem fourier_comp_inv_mul (ψ : AddChar K ℂ) (φ : K → ℂ) {b : K} (hb : b ≠ 0) (ξ : K) :
    fourier μ ψ (fun x => φ (b⁻¹ * x)) ξ =
      ((residueCard K : ℂ) ^ ord K b)⁻¹ * fourier μ ψ φ (b * ξ) := by
  have h := integral_comp_mul_left μ hb fun x => φ (b⁻¹ * x) * ψ (x * ξ)
  simp only [inv_mul_cancel_left₀ hb] at h
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hc : (((residueCard K : ℝ) ^ ord K b : ℝ) : ℂ) = (residueCard K : ℂ) ^ ord K b := by
    push_cast; rfl
  rw [Complex.real_smul, hc] at h
  unfold fourier
  rw [show (fun x => φ x * ψ (x * (b * ξ))) = fun x => φ x * ψ (b * x * ξ) by
    funext x; ring_nf, h, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hq), one_mul]

/-- **The functional equation is stable under dilation.** If $Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon Z(\varphi, \chi, s)$, then the same holds for $\varphi(b^{-1} \cdot)$ with the same $\varepsilon$, for each $b \ne 0$. Both sides are multiplied by $\chi(b) (q^{-s})^{\mathrm{ord}(b)}$. -/
theorem localFunctionalEquation_comp_inv_mul (ψ : AddChar K ℂ) {φ : K → ℂ} {b : K} (hb : b ≠ 0)
    {s ε : ℂ} (h : zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) = ε * zeta χ μ φ s) :
    zeta χ⁻¹ μ (fourier μ ψ fun x => φ (b⁻¹ * x)) (1 - s) =
      ε * zeta χ μ (fun x => φ (b⁻¹ * x)) s := by
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
  rw [hf, hz, zeta_comp_inv_mul χ⁻¹ μ _ (inv_ne_zero hb), h, zeta_comp_inv_mul χ μ φ hb, hu,
    map_inv, ord_inv hb, cpow_neg_one_sub]
  simp only [MonoidHom.inv_apply, inv_inv]
  rw [mul_zpow, inv_zpow', inv_zpow', zpow_neg, neg_neg]
  field_simp
  rw [← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_mul]

omit [MeasurableSpace K] [BorelSpace K] in
/-- For $b \ne 0$, $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}(x) = \mathbf{1}_{1 + \mathfrak{p}^{N - \mathrm{ord}(b)}}(b^{-1} x)$. -/
theorem ballIndicator_eq_comp {b : K} (hb : b ≠ 0) (N : ℤ) :
    ballIndicator b N = fun x => (oneAddBall (N - ord K b)).indicator 1 (b⁻¹ * x) := by
  funext x
  have hm : b⁻¹ * x ∈ oneAddBall (N - ord K b) ↔ x - b ∈ ordBall K N := by
    change b⁻¹ * x - 1 ∈ ordBall K (N - ord K b) ↔ _
    rw [show b⁻¹ * x - 1 = b⁻¹ * (x - b) by field_simp, mul_mem_ordBall_iff (inv_ne_zero hb),
      ord_inv hb, sub_neg_eq_add, sub_add_cancel]
  unfold ballIndicator
  by_cases hx : x - b ∈ ordBall K N
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hm.1 h))]

/-- **The local functional equation for a translated ball.** Let $\chi$ have conductor exponent $a \ge 1$ and let $\psi$ be continuous of conductor exponent $n$. For each $b$ and $N$ and each $s$ with $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, the function $\varphi = \mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ satisfies $Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s)$. For $b = 0$ both sides are $0$. For $b \ne 0$ the function is a dilation of $\mathbf{1}_{1 + \mathfrak{p}^{N - \mathrm{ord}(b)}}$. -/
theorem localFunctionalEquation_ballIndicator (hχs : IsSmoothChar K χ) {a : ℕ}
    (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ} (hψc : Continuous ψ) {n : ℤ}
    (hψ : IsConductor ψ n) (b : K) (N : ℤ) {s : ℂ}
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ (ballIndicator b N)) (1 - s) =
      epsilonRamified χ μ ψ a n s * zeta χ μ (ballIndicator b N) s := by
  by_cases hb : b = 0
  · subst hb
    have he : ballIndicator (0 : K) N = (ordBall K N).indicator fun _ => (1 : ℂ) := by
      funext x; simp [ballIndicator]; rfl
    rw [he, show ((ordBall K N).indicator fun _ => (1 : ℂ)) = (ordBall K N).indicator 1 from rfl,
      fourier_indicator_ordBall μ hψ N, zeta_indicator_ordBall_eq_zero μ hχ.inv,
      show ((ordBall K N).indicator 1 : K → ℂ) = (ordBall K N).indicator fun _ => (1 : ℂ) from rfl,
      zeta_indicator_ordBall_eq_zero μ hχ, mul_zero]
  rw [ballIndicator_eq_comp hb]
  exact localFunctionalEquation_comp_inv_mul μ ψ hb
    (localFunctionalEquation_oneAddBall μ hχs hχ hψc hψ _ hs')

variable [μ.Regular]

/-- **Tate's local functional equation for a ramified character.** Let $\chi$ be a smooth character of conductor exponent $a \ge 1$ and let $\psi$ be continuous of conductor exponent $n$. For each locally constant function $\varphi$ with compact support and each $s$ in the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s).$$ The proof writes $\varphi$ as a finite combination of translated balls by `exists_eq_sum_ballIndicator` and uses `localFunctionalEquation_ballIndicator` on each ball. -/
theorem localFunctionalEquation_of_isLocallyConstant (hχs : IsSmoothChar K χ) {a : ℕ}
    (hχ : IsRamifiedConductor χ a) {ψ : AddChar K ℂ} (hψc : Continuous ψ) {n : ℤ}
    (hψ : IsConductor ψ n) {φ : K → ℂ} (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ)
    {s : ℂ} (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) = epsilonRamified χ μ ψ a n s * zeta χ μ φ s := by
  have hs2 : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
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
    zeta_sum μ χ⁻¹ (isSmoothChar_inv χ hχs) hs2 T _ _ hfb, zeta_sum μ χ hχs hs T _ _ hbb,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [localFunctionalEquation_ballIndicator μ hχs hχ hψc hψ b N hs']
  ring

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The strip of convergence is not empty: there is $s$ with $|\chi(\varpi) q^{-s}| < 1$ and $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$. -/
theorem exists_mem_strip : ∃ s : ℂ, ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 ∧
    ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
  have hq0 : (0 : ℝ) < residueCard K := by exact_mod_cast residueCard_pos'
  have hq1 : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard
  set r := ‖(χ (unif K) : ℂ)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (Units.ne_zero _)
  have hh : 1 < (residueCard K : ℝ) ^ (1 / 2 : ℝ) := Real.one_lt_rpow hq1 (by norm_num)
  have hh0 : 0 < (residueCard K : ℝ) ^ (1 / 2 : ℝ) := by linarith
  refine ⟨((Real.logb (residueCard K) r + 1 / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [norm_mul, Complex.norm_natCast_cpow_of_pos residueCard_pos', ← hr]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg hq0.le, Real.rpow_add hq0, Real.rpow_logb hq0 hq1.ne' hr0, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
    exact inv_lt_one_of_one_lt₀ hh
  · rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos residueCard_pos', ← hr]
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    rw [show -(1 - (Real.logb (residueCard K) r + 1 / 2)) = Real.logb (residueCard K) r - 1 / 2 by
      ring, Real.rpow_sub hq0, Real.rpow_logb hq0 hq1.ne' hr0, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ hr0.ne', one_mul]
    exact inv_lt_one_of_one_lt₀ hh

/-- **The Gauss integral does not vanish.** Let $\chi$ be a smooth character of conductor exponent $a \ge 1$ and let $\psi$ be continuous of conductor exponent $n$. Then $G(\chi, \psi) = \int_{\varpi^{-n-a} \mathcal{O}_K^\times} \psi(y) \chi^{-1}(y) \, dy \ne 0$. The proof applies the functional equation twice, to $\varphi = \mathbf{1}_{1 + \mathfrak{p}^a}$ for $\chi$ and to $\hat{\varphi}$ for $\chi^{-1}$. By Fourier inversion, $\hat{\hat{\varphi}}(x) = c \varphi(-x)$ with $c \ne 0$, so $\varepsilon(1 - s, \chi^{-1}, \psi) \varepsilon(s, \chi, \psi) = c \chi(-1) \ne 0$. -/
theorem gaussInt_ne_zero (hχs : IsSmoothChar K χ) {a : ℕ} (hχ : IsRamifiedConductor χ a)
    {ψ : AddChar K ℂ} (hψc : Continuous ψ) {n : ℤ} (hψ : IsConductor ψ n) :
    gaussInt χ μ ψ (-n - a) ≠ 0 := by
  intro hG
  obtain ⟨s, hs, hs'⟩ := exists_mem_strip (χ := χ)
  set φ := ballIndicator (1 : K) (a : ℤ) with hφ
  have hφ1 : (oneAddBall (a : ℤ)).indicator 1 = φ := by
    rw [hφ, ballIndicator_eq_comp one_ne_zero]
    funext x
    simp [ord_one]
  have hZ : zeta χ μ φ s = μ.real (ordBall K a) := by
    rw [← hφ1, zeta_indicator_oneAddBall_of_le μ hχ le_rfl]
  have h1 := localFunctionalEquation_ballIndicator μ hχs hχ hψc hψ 1 a hs'
  rw [← hφ, epsilonRamified, hG, zero_mul, zero_mul] at h1
  have hloc : IsLocallyConstant (fourier μ ψ φ) := by
    have : fourier μ ψ φ = ⇑ψ *
        (ordBall K (-n - a)).indicator (fun _ => (μ.real (ordBall K a) : ℂ)) := by
      funext ξ
      rw [hφ, fourier_ballIndicator μ hψ 1 a, one_mul]
      rfl
    rw [this]
    exact hψ.isLocallyConstant.mul (isLocallyConstant_indicator (isOpen_ordBall _)
      (isClosed_ordBall _) (f := fun _ => (μ.real (ordBall K a) : ℂ))
        fun _ _ => Filter.Eventually.of_forall fun _ => rfl)
  have hcs : HasCompactSupport (fourier μ ψ φ) := by
    refine HasCompactSupport.intro (isCompact_ordBall (-n - a)) fun x hx => ?_
    rw [hφ, fourier_ballIndicator μ hψ, Set.indicator_of_notMem hx, mul_zero]
  have hsi : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
    rwa [inv_apply_coe]
  have hsi' : ‖((χ⁻¹ (unif K) : ℂˣ) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - (1 - s)))‖ < 1 := by
    rwa [inv_apply_coe, inv_inv, sub_sub_cancel]
  have h2 := localFunctionalEquation_of_isLocallyConstant μ (isSmoothChar_inv χ hχs) hχ.inv hψc hψ
    hloc hcs hsi hsi'
  rw [h1, mul_zero] at h2
  have hχχ : χ⁻¹⁻¹ = χ := by ext; simp
  rw [hχχ, sub_sub_cancel] at h2
  have hff : fourier μ ψ (fourier μ ψ φ) = fun x =>
      ((μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n : ℝ) : ℂ) * φ ((-1)⁻¹ * x) := by
    funext x
    rw [hφ, fourier_fourier_ballIndicator μ hψ]
    simp
  have hz : zeta χ μ (fun x => ((μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n : ℝ) : ℂ) *
      φ ((-1)⁻¹ * x)) s = ((μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n : ℝ) : ℂ) *
        zeta χ μ (fun x => φ ((-1)⁻¹ * x)) s := by
    unfold zeta; rw [← integral_const_mul]; congr 1; funext x; ring
  rw [hff, hz, zeta_comp_inv_mul χ μ φ (neg_ne_zero.2 one_ne_zero), hZ] at h2
  have hμ0 : ∀ N : ℤ, (μ.real (ordBall K N) : ℂ) ≠ 0 := fun N => by
    rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨measure_ordBall_ne_zero μ N, measure_ordBall_ne_top μ N⟩
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hc : ((μ.real (ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ n : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (pow_ne_zero _ (hμ0 0)) (zpow_ne_zero _ hq)
  exact mul_ne_zero hc (mul_ne_zero (mul_ne_zero (Units.ne_zero _)
    (zpow_ne_zero _ (cpow_neg_ne_zero s))) (hμ0 a)) h2

end Balls

end Langlands.LocalGL1
