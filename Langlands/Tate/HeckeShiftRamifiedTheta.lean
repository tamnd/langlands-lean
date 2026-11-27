/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeShiftFE
import Langlands.Tate.HeckeRamifiedSign

/-!
# The twisted theta series with a coefficient

This file twists the theta series with a coefficient of `Langlands/Tate/HeckeRamifiedSign.lean` by the character $\tau_\theta$ of `Langlands/Tate/HeckeShiftTheta.lean`. The twist gives a different imaginary shift $i \theta_w$ at each infinite place $w$. The coefficient is the periodic Gauss sum coefficient $c_J$ of a ramified character.

The unit condition is $f(u \alpha) \chi_\infty(u) \tau_\theta(u) = f(\alpha)$ for all units $u$. The coefficients have $f(0) = 0$, so the theta series has no term of $\alpha = 0$.

## Main definitions

* `Langlands.Tate.shiftCoeffTheta`: the twisted theta series $\tau_\theta(t) \, \Theta_{\mathfrak{a}}^{p, k}(f; t)$.
* `Langlands.Tate.shiftCoeffDualTheta`: the twisted dual theta series $\tau_{-\theta}(t) \, \Theta_{\mathfrak{b}}^{\vee, p, k}(g; t)$.

## Main results

* `Langlands.Tate.hasSum_integral_shiftCoeffTheta`: the unfolding of the Mellin integral into a series over the orbits of the units.
* `Langlands.Tate.shiftCoeffTheta_periodicCoeff_unitScale`: the transformation formula with the coefficients $c_J$ in the unit coordinates.
* `Langlands.Tate.shiftCoeffDualTheta_eq`: the twisted dual series is $\tau_\theta((n_w^2)_w)$ times a conjugate twisted theta series.
* `Langlands.Tate.shiftCoeffTheta_unitScale_add_int`: the periodicity in the unit coordinates.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem IsDedekindDomain
open scoped Real Classical nonZeroDivisors ENNReal

namespace Langlands.Tate

/-- The cube $[0, 1)^r$ of the unit coordinates. -/
local notation "cube" => Set.pi univ fun _ : Fin (rank _) => Ico (0 : ℝ) 1

section Definitions

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (θ : InfinitePlace K → ℝ)

/-- The twisted theta series $\tau_\theta(t) \, \Theta_{\mathfrak{a}}^{p, k}(f; t)$ of the ideal $\mathfrak{a}$ with the coefficient $f$. -/
noncomputable def shiftCoeffTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  torusFactor θ t * signCoeffTheta K ε p k a f t

/-- The twisted dual theta series $\tau_{-\theta}(t) \, \Theta_{\mathfrak{b}}^{\vee, p, k}(g; t)$ of the ideal $\mathfrak{b}$ with the coefficient $g$. The shifts change sign. -/
noncomputable def shiftCoeffDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  torusFactor (-θ) t * signCoeffDualTheta K ε p k b g t

end Definitions

section Unfold

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {f : K → ℂ} {B : ℝ}

/-- The twisted theta series with a coefficient is the sum of the twisted terms. -/
theorem shiftCoeffTheta_eq_tsum (t : InfinitePlace K → ℝ) :
    shiftCoeffTheta K ε p k θ a f t =
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), f α * shiftHeckeTerm ε p k θ (α : K) t := by
  rw [shiftCoeffTheta, signCoeffTheta, ← tsum_mul_left]
  exact tsum_congr fun α => by rw [shiftHeckeTerm]; ring

/-- A twisted term with a coefficient has the extended absolute value of the term without the twist. -/
theorem enorm_coeff_mul_shiftHeckeTerm (x : K) (t : InfinitePlace K → ℝ) :
    ‖f x * shiftHeckeTerm ε p k θ x t‖ₑ = ‖f x * signHeckeTerm ε p k x t‖ₑ := by
  rw [enorm_mul, enorm_mul, enorm_shiftHeckeTerm]

variable (a) in
/-- If $f(0) = 0$ and $t_w > 0$, the twisted theta series with the coefficient $f$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem shiftCoeffTheta_eq_tsum_nonzero (hB : ∀ α, ‖f α‖ ≤ B) (hf0 : f 0 = 0)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    shiftCoeffTheta K ε p k θ a f t =
      ∑' α : NonzeroElt a, f α * shiftHeckeTerm ε p k θ (α : K) t := by
  have h := signCoeffTheta_sub_eq_tsum (ε := ε) (p := p) (k := k) a hB ht
  rw [hf0, zero_mul, sub_zero] at h
  rw [shiftCoeffTheta, h, ← tsum_mul_left]
  exact tsum_congr fun α => by rw [shiftHeckeTerm]; ring

/-- **The periodicity of the twisted coefficient terms under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $f(u \alpha) \chi_\infty(u) \tau_\theta(u) = f(\alpha)$ for all units $u$ and $y > 0$, then $f(u \alpha) h_{t(y, c)}(u \alpha) = f(\alpha) h_{t(y, c + m)}(\alpha)$ for the twisted terms. -/
theorem shiftCoeffTerm_unitsEquiv
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K),
      f ((u : K) * α) * signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = f α)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    f ((unitsEquiv K q : K) * α) *
        shiftHeckeTerm ε p k θ ((unitsEquiv K q : K) * α) (unitScale K y c) =
      f α * shiftHeckeTerm ε p k θ α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [shiftHeckeTerm_mul (unitScale_pos hy c) (coe_ne_zero _) α, ← mul_assoc, ← mul_assoc, hf]
  congr 2
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- **The unfolding of the absolute values with a twisted coefficient.** Under the unit condition of `Langlands.Tate.shiftCoeffTerm_unitsEquiv` and for $y > 0$, $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |f(\alpha) h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |f(\alpha_I) h_{t(y, c)}(\alpha_I)| \, dc$$ for the twisted terms. -/
theorem tsum_lintegral_unitCube_shiftCoeffTerm
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K),
      f ((u : K) * α) * signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = f α)
    {y : ℝ} (hy : 0 < y) :
    ∑' α : NonzeroElt a, ∫⁻ c in cube, ‖f α * shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖f (orbitRep a I) * shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in cube,
        ‖f α * shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in cube,
          ‖f ((β.1 : NonzeroElt a) : K) *
            shiftHeckeTerm ε p k θ ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ), ∫⁻ c in cube,
          ‖f (orbitRep a I) * shiftHeckeTerm ε p k θ (orbitRep a I : K)
            (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, shiftCoeffTerm_unitsEquiv hf _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖f (orbitRep a I) *
            shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖f (orbitRep a I) *
            shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

/-- **The unfolding with a twisted coefficient for a fixed $y$.** If $f$ is bounded, $f(0) = 0$, the unit condition holds and $y > 0$, then $$\int_{[0, 1)^r} \tau_\theta(t(y, c)) \, \Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) \, dc = w_K \sum_I f(\alpha_I) \int_{\mathbb{R}^r} \tau_\theta(t(y, c)) \, h_{t(y, c)}(\alpha_I) \, dc.$$ -/
theorem hasSum_integral_unitCube_shiftCoeffTheta (hB : ∀ α, ‖f α‖ ≤ B) (hf0 : f 0 = 0)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K),
      f ((u : K) * α) * signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = f α)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)))
      (∫ c in cube, shiftCoeffTheta K ε p k θ a f (unitScale K y c)) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in cube,
      ‖f α * shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ ≠ ⊤ := by
    simp only [enorm_coeff_mul_shiftHeckeTerm]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (tsum_lintegral_signHeckeTerm_le hy))) (tsum_lintegral_signCoeffTerm_le hB y)
  have hm : ∀ x : K, Measurable fun c => f x * shiftHeckeTerm ε p k θ x (unitScale K y c) :=
    fun x => measurable_const.mul ((measurable_shiftHeckeTerm x).comp
      (continuous_unitScale y).measurable)
  set g : NonzeroElt a → ℂ := fun α => ∫ c in cube,
    f α * shiftHeckeTerm ε p k θ (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in cube, shiftCoeffTheta K ε p k θ a f (unitScale K y c) = ∑' α, g α := by
    simp_rw [shiftCoeffTheta_eq_tsum_nonzero a hB hf0 (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_shiftCoeffTerm (a := a) hf hy
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a, Integrable fun c =>
      f (orbitRep a I) * shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) * ∫⁻ c, ‖f (orbitRep a I) *
          shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in cube,
      f (orbitRep a I) * shiftHeckeTerm ε p k θ (orbitRep a I : K)
        (unitScale K y (c + fun i => (m i : ℝ))) with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, shiftCoeffTerm_unitsEquiv hf _ _ hy]
    have hsG : Summable fun q : torsion K × (Fin (rank K) → ℤ) => G q.2 := by
      refine (((unitsEquiv K).trans (unitsEquivFiber I)).summable_iff.2
        (hsum.comp_injective Subtype.coe_injective)).congr fun q => ?_
      exact hval q
    calc ∑' β : (orbitOf a ⁻¹' {I}), g β
        = ∑' q : torsion K × (Fin (rank K) → ℤ),
            g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) :=
          (((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq (fun β => g β)).symm
      _ = ∑' q : torsion K × (Fin (rank K) → ℤ), G q.2 := tsum_congr hval
      _ = ∑' _ : torsion K, ∑' m, G m := hsG.tsum_prod' fun ζ => hsG.prod_factor ζ
      _ = (torsionOrder K : ℂ) * ∑' m, G m := by
          have := Fintype.ofFinite (torsion K)
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
            Nat.card_eq_fintype_card]
      _ = _ := by rw [← integral_eq_tsum_unitCube _ (hint I), integral_const_mul]
  rw [h2]
  convert hsum.hasSum.tsum_fiberwise (orbitOf a) using 1
  exact funext fun I => (hfib I).symm

/-- **The unfolding of the twisted theta series with a coefficient.** Let $f$ be bounded with $f(0) = 0$ and $f(u \alpha) \chi_\infty(u) \tau_\theta(u) = f(\alpha)$ for all units $u$, let $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$. Then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \tau_\theta(t(y, c)) \, \Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) \, dc \, dy = w_K \, \Gamma_{p, k}^\theta(s') \sum_I f(\alpha_I) \chi_\infty(\alpha_I) \tau_\theta(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ where $I$ runs over $(\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. The series converges. -/
theorem hasSum_integral_shiftCoeffTheta (hB : ∀ α, ‖f α‖ ≤ B) (hf0 : f 0 = 0)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K),
      f ((u : K) * α) * signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = f α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (f (orbitRep a I) *
        (shiftGamma p k θ (2 * s / finrank ℚ K) * signInfinityWeight ε p k (orbitRep a I : K) *
          torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in cube, shiftCoeffTheta K ε p k θ a f (unitScale K y c)) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K)
      (unitScale K y c))) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in cube, shiftCoeffTheta K ε p k θ a f (unitScale K y c)) :=
    fun y hy => (hasSum_integral_unitCube_shiftCoeffTheta hB hf0 hf hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_const.mul
        (measurable_integral_shiftHeckeTerm _)))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_signCoeffTerm_lt_top ε p k a hB hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    have e := tsum_lintegral_unitCube_shiftCoeffTerm (a := a) hf hy
    simp only [enorm_coeff_mul_shiftHeckeTerm] at e
    rw [e, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun I => ?_
    simp only [hg]
    rw [enorm_mul, enorm_mul, ← ofReal_norm (x := (torsionOrder K : ℂ)), Complex.norm_natCast,
      ENNReal.ofReal_natCast, ← integral_const_mul]
    gcongr
    exact (enorm_integral_le_lintegral_enorm _).trans_eq
      (by simp only [enorm_coeff_mul_shiftHeckeTerm])
  have hsum : Summable fun I => ∫ y in Ioi (0 : ℝ), g I y := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun I => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have heq := integral_tsum hmeas hfin
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).tsum_eq] at heq
  have hterm : ∀ I : Orbits a, ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), g I y =
      (torsionOrder K : ℂ) * (f (orbitRep a I) *
        (shiftGamma p k θ (2 * s / finrank ℚ K) * signInfinityWeight ε p k (orbitRep a I : K) *
          torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))) := by
    intro I
    rw [← integral_unitScale_shiftHeckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K)
          (unitScale K y c)))) =
        fun y : ℝ => ((torsionOrder K : ℂ) * f (orbitRep a I)) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

end Unfold

section Periodic

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ}

/-- **The twisted theta transformation with Gauss sum coefficients.** Let $\chi$ be unitary and ramified at one place, let $p_v \le 1$, let $J$ be a nonzero integral ideal and $y > 0$. Then the twisted theta series of $c_J$ on $J$ at $t(y, c)$ is $\varepsilon_J \, \sqrt{y}^{\,-n}$ times the twisted dual series of $\overline{c_D}$ on $\mathfrak{f} J$ at $t(y^{-1}, -c)$, where $\varepsilon_J$ is `Langlands.Tate.ramifiedRootConst`. -/
theorem shiftCoeffTheta_periodicCoeff_unitScale (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    shiftCoeffTheta K ε p k θ (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
        (unitScale K y c) =
      ramifiedRootConst χ p k J * (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) *
        shiftCoeffDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) (unitScale K y⁻¹ (-c)) := by
  have h : torusFactor θ (unitScale K y c) = torusFactor (-θ) (unitScale K y⁻¹ (-c)) := by
    rw [← torusFactor_inv]
    congr 1
    funext w
    rw [unitScale_inv, inv_inv, neg_neg]
  rw [shiftCoeffTheta, signCoeffTheta_periodicCoeff_unitScale hS hu hp J hy c, shiftCoeffDualTheta,
    h]
  ring

end Periodic

section Coeff

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {f g : K → ℂ}

/-- The twisted theta series with a coefficient has the absolute value of the series without the twist. -/
theorem norm_shiftCoeffTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : InfinitePlace K → ℝ) :
    ‖shiftCoeffTheta K ε p k θ b f t‖ = ‖signCoeffTheta K ε p k b f t‖ := by
  rw [shiftCoeffTheta, norm_mul, norm_torusFactor, one_mul]

/-- The twisted dual theta series with a coefficient has the absolute value of the series without the twist. -/
theorem norm_shiftCoeffDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : InfinitePlace K → ℝ) :
    ‖shiftCoeffDualTheta K ε p k θ b g t‖ = ‖signCoeffDualTheta K ε p k b g t‖ := by
  rw [shiftCoeffDualTheta, norm_mul, norm_torusFactor, one_mul]

/-- If $|f| \le 1$, the twisted theta series with the coefficient $f$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_shiftCoeffTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ContinuousAt (shiftCoeffTheta K ε p k θ b f) t :=
  (continuousAt_torusFactor θ ht).mul (continuousAt_signCoeffTheta hf1 b ht)

/-- If $|g| \le 1$, the twisted dual theta series with the coefficient $g$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_shiftCoeffDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ContinuousAt (shiftCoeffDualTheta K ε p k θ b g) t :=
  (continuousAt_torusFactor (-θ) ht).mul (continuousAt_signCoeffDualTheta hg1 b ht)

variable (ε p k θ) in
/-- **The twisted dual series with a coefficient.** For $t_w > 0$, the twisted dual theta series of $\mathfrak{b}$ with the coefficient $g$ is $\tau_\theta((n_w^2)_w)$ times the complex conjugate of the twisted theta series of $(\mathfrak{b} \mathfrak{d})^{-1}$ with the coefficient $\bar{g}$ at $(n_w^2 t_w)_w$. -/
theorem shiftCoeffDualTheta_eq (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    shiftCoeffDualTheta K ε p k θ b g t =
      torusConst θ * conj (shiftCoeffTheta K ε p k θ (dualUnit K b) (fun β => conj (g β))
        (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  rw [shiftCoeffDualTheta, signCoeffDualTheta_eq ε p k b g (fun w => (ht w).le), shiftCoeffTheta,
    map_mul, torusFactor_neg_eq θ ht]
  ring

/-- **The periodicity of the twisted series with a coefficient.** If $f(u \alpha) \chi_\infty(u) \tau_\theta(u) = f(\alpha)$ for all units $u$ and $y > 0$, then the twisted theta series satisfies $\Theta_{\mathfrak{b}}(f; t(y, c + m)) = \Theta_{\mathfrak{b}}(f; t(y, c))$ for each integer vector $m$. -/
theorem shiftCoeffTheta_unitScale_add_int
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K),
      f ((u : K) * α) * signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = f α)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    shiftCoeffTheta K ε p k θ b f (unitScale K y (c + fun i => (m i : ℝ))) =
      shiftCoeffTheta K ε p k θ b f (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h, shiftCoeffTheta_eq_tsum, shiftCoeffTheta_eq_tsum]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) (unitOfInt K m)).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [shiftHeckeTerm_mul (unitScale_pos hy c) (coe_ne_zero _), ← mul_assoc, ← mul_assoc, hf]

end Coeff

end Langlands.Tate
