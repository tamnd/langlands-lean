/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeShiftTheta

/-!
# The functional equation of the partial Hecke sums with unequal shifts

This file repeats the unfolding, the functional equation pair and the completed partial Hecke sums of `Langlands/Tate/HeckeMixedSignFE.lean` for the twisted theta series of `Langlands/Tate/HeckeShiftTheta.lean`. The twist by $\tau_\theta$ gives a different shift $i \theta_w$ at each infinite place $w$.

The unit hypothesis is $\chi_\infty(u) \, \tau_\theta(u) = 1$ for all units $u$, where $\tau_\theta(u)$ is `Langlands.Tate.torusWeight`. The second hypothesis is that the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube. This is true for a nonzero weight, because the term is then zero.

Under these hypotheses and $p_v \le 1$, the completed partial Hecke sum $\Lambda_{\mathfrak{a}}$ is entire. For $\mathrm{Re}\, s > n / 2$ it is the series of $w_K \, \Gamma_{p, k, \theta}(2 s / n) \, \chi_\infty(\alpha) \, \tau_\theta(\alpha) \, |N(\alpha)|^{-2 s / n}$ over $\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. It satisfies $$\Lambda_{\mathfrak{a}}(n / 2 - s) = \varepsilon_{\mathfrak{a}} \, \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}.$$

## Main definitions

* `Langlands.Tate.shiftHeckeCubeTheta`, `Langlands.Tate.shiftHeckeCubeDualTheta`: the cube averages $F_{\mathfrak{a}}$ and $G_{\mathfrak{a}}$ of the twisted theta series.
* `Langlands.Tate.shiftHeckeFEPair`: the functional equation pair of $F_{\mathfrak{a}}$ and $G_{\mathfrak{a}}$.
* `Langlands.Tate.shiftCompletedPartialHecke`: the completed partial Hecke sum $\Lambda_{\mathfrak{a}}$ with the shifts.

## Main results

* `Langlands.Tate.hasSum_integral_shiftHeckeTheta`: the unfolding of the Mellin integral into the partial Hecke series.
* `Langlands.Tate.isStrongFEPair_shiftHeckeFEPair`: the pair has the constant terms zero.
* `Langlands.Tate.differentiable_shiftCompletedPartialHecke`: $\Lambda_{\mathfrak{a}}$ is entire.
* `Langlands.Tate.hasSum_shiftCompletedPartialHecke`: $\Lambda_{\mathfrak{a}}$ as a series for $\mathrm{Re}\, s > n / 2$.
* `Langlands.Tate.shiftCompletedPartialHecke_sub`: the functional equation of $\Lambda_{\mathfrak{a}}$.
-/

open MeasureTheory Module Filter Topology Set Complex Asymptotics ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical nonZeroDivisors ENNReal

namespace Langlands.Tate

variable {K : Type*} [Field K] [NumberField K]

/-- The cube $[0, 1)^r$ of the unit coordinates. -/
local notation "cube" => Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1

section Regular

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ}

/-- The torus character $\tau_\theta$ is measurable. -/
theorem measurable_torusFactor (θ : InfinitePlace K → ℝ) : Measurable (torusFactor θ) := by
  unfold torusFactor
  fun_prop

/-- The torus character $\tau_\theta$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_torusFactor (θ : InfinitePlace K → ℝ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (torusFactor θ) t := by
  have h : ∀ w, ContinuousAt (fun s : InfinitePlace K → ℝ => Real.log (s w)) t := fun w =>
    ((continuous_apply w).continuousAt).log (ht w).ne'
  unfold torusFactor
  refine Complex.continuous_exp.continuousAt.comp
    ((Complex.continuous_ofReal.continuousAt.comp ?_).mul continuousAt_const)
  exact tendsto_finsetSum _ fun w _ => continuousAt_const.mul (h w)

/-- The twisted term is measurable in $t$. -/
theorem measurable_shiftHeckeTerm (α : K) : Measurable fun t => shiftHeckeTerm ε p k θ α t :=
  (measurable_torusFactor θ).mul (measurable_signHeckeTerm α)

/-- The twisted term $h_{t(y, c)}(\alpha)$ is measurable in $(y, c)$. -/
theorem measurable_shiftHeckeTerm_unitScale (α : K) :
    Measurable fun q : ℝ × (Fin (rank K) → ℝ) => shiftHeckeTerm ε p k θ α (unitScale K q.1 q.2) := by
  refine (measurable_shiftHeckeTerm α).comp (Continuous.measurable (continuous_pi fun w => ?_))
  unfold unitScale
  fun_prop

/-- The twisted term is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_shiftHeckeTerm (α : K) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ContinuousAt (fun s => shiftHeckeTerm ε p k θ α s) t := by
  have hU : IsOpen (⋂ w, {s : InfinitePlace K → ℝ | 0 < s w}) :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  exact (continuousAt_torusFactor θ ht).mul ((continuousOn_signHeckeTerm α).continuousAt
    (Filter.mem_of_superset (hU.mem_nhds (mem_iInter.2 ht)) fun s hs => mem_iInter.1 hs))

/-- The twisted theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_shiftHeckeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (shiftHeckeTheta K ε p k θ b) t :=
  (continuousAt_torusFactor θ ht).mul (continuousAt_signHeckeTheta b ht)

/-- The twisted dual theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_shiftHeckeDualTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (shiftHeckeDualTheta K ε p k θ a) t :=
  (continuousAt_torusFactor (-θ) ht).mul (continuousAt_signHeckeDualTheta a ht)

/-- A function of $c$ that is continuous is integrable on the unit cube. -/
theorem integrableOn_cube_of_continuous {f : (Fin (rank K) → ℝ) → ℂ} (hf : Continuous f) :
    IntegrableOn f cube :=
  (hf.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Ico_subset_Icc_self)

/-- For $y > 0$ the twisted theta series in the unit coordinates is integrable on the unit cube. -/
theorem integrableOn_shiftHeckeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun c => shiftHeckeTheta K ε p k θ b (unitScale K y c)) cube :=
  integrableOn_cube_of_continuous (continuous_iff_continuousAt.2 fun c =>
    (continuousAt_shiftHeckeTheta b (unitScale_pos hy c)).comp (continuous_unitScale y).continuousAt)

/-- For $y > 0$ the twisted term in the unit coordinates is integrable on the unit cube. -/
theorem integrableOn_shiftHeckeTerm (α : K) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun c => shiftHeckeTerm ε p k θ α (unitScale K y c)) cube :=
  integrableOn_cube_of_continuous (continuous_iff_continuousAt.2 fun c =>
    (continuousAt_shiftHeckeTerm α (unitScale_pos hy c)).comp (continuous_unitScale y).continuousAt)

/-- The twisted theta series minus its term $\alpha = 0$ has the same absolute value as the signed theta series minus its term $\alpha = 0$. -/
theorem norm_shiftHeckeTheta_sub (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : InfinitePlace K → ℝ) :
    ‖shiftHeckeTheta K ε p k θ b t - shiftHeckeTerm ε p k θ 0 t‖ =
      ‖signHeckeTheta K ε p k b t - signHeckeTerm ε p k 0 t‖ := by
  rw [shiftHeckeTheta, shiftHeckeTerm, ← mul_sub, norm_mul, norm_torusFactor, one_mul]

/-- For a nonzero weight, the twisted term of $\alpha = 0$ is zero. -/
theorem shiftHeckeTerm_zero (h : p ≠ 0 ∨ k ≠ 0) (t : InfinitePlace K → ℝ) :
    shiftHeckeTerm ε p k θ 0 t = 0 := by
  rw [shiftHeckeTerm, signHeckeTerm_zero h, mul_zero]

/-- For a nonzero weight, the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube. -/
theorem integral_shiftHeckeTerm_zero (h : p ≠ 0 ∨ k ≠ 0) (y : ℝ) :
    ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0 := by
  simp only [shiftHeckeTerm_zero h, integral_zero]

end Regular

section Unfold

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The periodicity under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $\chi_\infty \tau_\theta$ is trivial on all units and $y > 0$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$ for the twisted terms. -/
theorem shiftHeckeTerm_unitsEquiv
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    shiftHeckeTerm ε p k θ ((unitsEquiv K q : K) * α) (unitScale K y c) =
      shiftHeckeTerm ε p k θ α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [shiftHeckeTerm_mul (unitScale_pos hy c) (coe_ne_zero _) α, hχ, one_mul]
  congr 1
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- **The unfolding of the absolute values.** If $\chi_\infty \tau_\theta$ is trivial on all units and $y > 0$, then $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |h_{t(y, c)}(\alpha_I)| \, dc$$ for the twisted terms. -/
theorem tsum_lintegral_unitCube_shiftHeckeTerm
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    {y : ℝ} (hy : 0 < y) :
    ∑' α : NonzeroElt a, ∫⁻ c in cube, ‖shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in cube, ‖shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in cube,
          ‖shiftHeckeTerm ε p k θ ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ), ∫⁻ c in cube,
          ‖shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, shiftHeckeTerm_unitsEquiv hχ _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

variable (a) in
/-- For $t_w > 0$, the twisted theta series minus its term $\alpha = 0$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem shiftHeckeTheta_sub_eq_tsum {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    shiftHeckeTheta K ε p k θ a t - shiftHeckeTerm ε p k θ 0 t =
      ∑' α : NonzeroElt a, shiftHeckeTerm ε p k θ (α : K) t := by
  rw [shiftHeckeTheta, shiftHeckeTerm, ← mul_sub, signHeckeTheta_sub_eq_tsum a ht, ← tsum_mul_left]
  rfl

/-- **The unfolding for a fixed $y$.** If $\chi_\infty \tau_\theta$ is trivial on all units and $y > 0$, then $$\int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc = w_K \sum_I \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha_I) \, dc$$ for the twisted theta series. -/
theorem hasSum_integral_unitCube_shiftHeckeTheta
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        ∫ c, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c))
      (∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
        shiftHeckeTerm ε p k θ 0 (unitScale K y c))) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in cube,
      ‖shiftHeckeTerm ε p k θ (α : K) (unitScale K y c)‖ₑ ≠ ⊤ := by
    simp only [enorm_shiftHeckeTerm]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (tsum_lintegral_signHeckeTerm_le hy)
  have hm : ∀ x : K, Measurable fun c => shiftHeckeTerm ε p k θ x (unitScale K y c) := fun x =>
    (measurable_shiftHeckeTerm x).comp (continuous_unitScale y).measurable
  set g : NonzeroElt a → ℂ := fun α => ∫ c in cube,
    shiftHeckeTerm ε p k θ (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
      shiftHeckeTerm ε p k θ 0 (unitScale K y c)) = ∑' α, g α := by
    simp_rw [shiftHeckeTheta_sub_eq_tsum a (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_shiftHeckeTerm (a := a) hχ hy
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a,
      Integrable fun c => shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) * ∫ c, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in cube,
      shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y (c + fun i => (m i : ℝ))) with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, shiftHeckeTerm_unitsEquiv hχ _ _ hy]
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
      _ = _ := by rw [integral_eq_tsum_unitCube _ (hint I)]
  rw [h2]
  convert hsum.hasSum.tsum_fiberwise (orbitOf a) using 1
  exact funext fun I => (hfib I).symm

end Unfold

section Mellin

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- The integral $\int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc$ of a twisted term is measurable in $y$. -/
theorem measurable_integral_shiftHeckeTerm (x : K) :
    Measurable fun y : ℝ => ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ x (unitScale K y c) :=
  (StronglyMeasurable.integral_prod_right' (f := fun q : ℝ × (Fin (rank K) → ℝ) =>
    shiftHeckeTerm ε p k θ x (unitScale K q.1 q.2))
    (measurable_shiftHeckeTerm_unitScale x).stronglyMeasurable).measurable

/-- **The unfolding of the twisted theta function.** Let $\chi_\infty \tau_\theta$ be trivial on all units of $K$, let $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$. Then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}(t(y, c)) - h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k, \theta}(s') \sum_I \chi_\infty(\alpha_I) \, \tau_\theta(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ where $I$ runs over $(\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$. The series converges. -/
theorem hasSum_integral_shiftHeckeTheta_sub
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (shiftGamma p k θ (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) * torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
          shiftHeckeTerm ε p k θ 0 (unitScale K y c))) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
        shiftHeckeTerm ε p k θ 0 (unitScale K y c))) :=
    fun y hy => (hasSum_integral_unitCube_shiftHeckeTheta hχ hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_integral_shiftHeckeTerm _))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_signHeckeTerm_lt_top ε p k a hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    have e := tsum_lintegral_unitCube_shiftHeckeTerm (a := a) hχ hy
    simp only [enorm_shiftHeckeTerm] at e
    rw [e, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun I => ?_
    simp only [hg]
    rw [enorm_mul, enorm_mul, ← ofReal_norm (x := (torsionOrder K : ℂ)), Complex.norm_natCast,
      ENNReal.ofReal_natCast]
    gcongr
    exact (enorm_integral_le_lintegral_enorm _).trans_eq (by simp only [enorm_shiftHeckeTerm])
  have hsum : Summable fun I => ∫ y in Ioi (0 : ℝ), g I y := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun I => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have heq := integral_tsum hmeas hfin
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).tsum_eq] at heq
  have hterm : ∀ I : Orbits a, ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), g I y =
      (torsionOrder K : ℂ) * (shiftGamma p k θ (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) * torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) := by
    intro I
    rw [← integral_unitScale_shiftHeckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c))) =
        fun y : ℝ => (torsionOrder K : ℂ) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, shiftHeckeTerm ε p k θ (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

/-- If the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube, then for $y > 0$ the cube integral of the twisted theta series does not change when this term is removed. -/
theorem integral_shiftHeckeTheta_sub
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    {y : ℝ} (hy : 0 < y) :
    ∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
        shiftHeckeTerm ε p k θ 0 (unitScale K y c)) =
      ∫ c in cube, shiftHeckeTheta K ε p k θ a (unitScale K y c) := by
  rw [integral_sub (integrableOn_shiftHeckeTheta a hy) (integrableOn_shiftHeckeTerm 0 hy), h0 y hy,
    sub_zero]

/-- **The unfolding without the term $\alpha = 0$.** Under the hypotheses of `hasSum_integral_shiftHeckeTheta_sub`, if the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube, then the same series converges to $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \Theta_{\mathfrak{a}}(t(y, c)) \, dc \, dy.$$ -/
theorem hasSum_integral_shiftHeckeTheta
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (shiftGamma p k θ (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) * torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in cube, shiftHeckeTheta K ε p k θ a (unitScale K y c)) := by
  have e : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
      ∫ c in cube, (shiftHeckeTheta K ε p k θ a (unitScale K y c) -
        shiftHeckeTerm ε p k θ 0 (unitScale K y c)) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in cube, shiftHeckeTheta K ε p k θ a (unitScale K y c) :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [integral_shiftHeckeTheta_sub h0 hy]
  rw [← e]
  exact hasSum_integral_shiftHeckeTheta_sub hχ hs

end Mellin


section Cube

variable (K) in
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
  (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
  (θ : InfinitePlace K → ℝ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) in
/-- The cube average $F(y) = \int_{[0, 1)^r} \tau_\theta(t(y, c)) \, \Theta_{\mathfrak{a}}(t(y, c)) \, dc$ of the twisted theta series. -/
noncomputable def shiftHeckeCubeTheta (y : ℝ) : ℂ :=
  ∫ c in cube, shiftHeckeTheta K ε p k θ a (unitScale K y c)

variable (K) in
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
  (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
  (θ : InfinitePlace K → ℝ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) in
/-- The cube average $G(y) = \int_{[0, 1)^r} \tau_{-\theta}(t(y, -c)) \, \widehat{\Theta}_{\mathfrak{a}}(t(y, -c)) \, dc$ of the twisted dual theta series. -/
noncomputable def shiftHeckeCubeDualTheta (y : ℝ) : ℂ :=
  ∫ c in cube, shiftHeckeDualTheta K ε p k θ a (unitScale K y (-c))

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The periodicity in the unit coordinates.** If $\chi_\infty \tau_\theta$ is trivial on all units and $y > 0$, then the twisted theta series satisfies $\Theta_{\mathfrak{b}}(t(y, c + m)) = \Theta_{\mathfrak{b}}(t(y, c))$ for each integer vector $m$. -/
theorem shiftHeckeTheta_unitScale_add_int
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    shiftHeckeTheta K ε p k θ b (unitScale K y (c + fun i => (m i : ℝ))) =
      shiftHeckeTheta K ε p k θ b (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h]
  exact shiftHeckeTheta_unit (t := unitScale K y c) b (hχ _) (unitScale_pos hy c)

/-- The functional equation of the cube averages: if $p_v \le 1$ for all real $v$ and $x > 0$, then $F(1 / x) = \varepsilon \, x^{n / 2} \, G(x)$. -/
theorem shiftHeckeCubeTheta_one_div (hp : ∀ v, p v ≤ 1) {x : ℝ} (hx : 0 < x) :
    shiftHeckeCubeTheta K ε p k θ a (1 / x) =
      (heckeRootConst K p k a * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        shiftHeckeCubeDualTheta K ε p k θ a x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [shiftHeckeCubeTheta, shiftHeckeCubeDualTheta, smul_eq_mul]
  simp_rw [shiftHeckeTheta_unitScale a hp (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul, heckeRootConst]

/-- **The dual cube average.** If $\chi_\infty \tau_\theta$ is trivial on all units and $y > 0$, then $G_{\mathfrak{a}}(y) = \tau_\theta((n_w^2)_w) \, \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$. -/
theorem shiftHeckeCubeDualTheta_eq_conj
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    {y : ℝ} (hy : 0 < y) :
    shiftHeckeCubeDualTheta K ε p k θ a y =
      torusConst θ * conj (shiftHeckeCubeTheta K ε p k θ (dualUnit K a) (heckeScale K * y)) := by
  have e : ∀ c : Fin (rank K) → ℝ, shiftHeckeDualTheta K ε p k θ a (unitScale K y (-c)) =
      torusConst θ * conj (shiftHeckeTheta K ε p k θ (dualUnit K a)
        (unitScale K (heckeScale K * y) (heckeShift K - c))) := fun c => by
    rw [shiftHeckeDualTheta_eq a (unitScale_pos hy _)]
    rw [show (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w) =
        unitScale K (heckeScale K * y) (heckeShift K - c) from
      funext fun w => mult_sq_mul_unitScale_neg y c w]
  rw [shiftHeckeCubeDualTheta, shiftHeckeCubeTheta]
  simp_rw [e]
  rw [integral_const_mul, integral_conj, integral_unitCube_sub
    (fun c => shiftHeckeTheta K ε p k θ (dualUnit K a) (unitScale K (heckeScale K * y) c))
    (fun m c => shiftHeckeTheta_unitScale_add_int hχ _
      (mul_pos (heckeScale_pos K) hy) c m) (heckeShift K)]

/-- The cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_shiftHeckeCubeTheta :
    ContinuousOn (shiftHeckeCubeTheta K ε p k θ a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i) (fun _ ht => continuousAt_shiftHeckeTheta a ht)
    fun _ hs => ⟨_, fun _ hst => (norm_shiftHeckeTheta a _).trans_le (norm_signHeckeTheta_le a hs hst)⟩

/-- The dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_shiftHeckeCubeDualTheta :
    ContinuousOn (shiftHeckeCubeDualTheta K ε p k θ a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_shiftHeckeDualTheta a ht)
    fun _ hs => ⟨_, fun _ hst =>
      (norm_shiftHeckeDualTheta a _).trans_le (norm_signHeckeDualTheta_le a hs hst)⟩

/-- If the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube, then $F(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_shiftHeckeCubeTheta
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) (r : ℝ) :
    shiftHeckeCubeTheta K ε p k θ a =O[atTop] (· ^ r) := by
  have hB := isBigO_integral_unitCube (u := id)
    (fun t => shiftHeckeTheta K ε p k θ a t - shiftHeckeTerm ε p k θ 0 t)
    (fun c hc i => abs_le_one_of_mem_unitCube hc i) a heckeConst_pos.le (fun s hs t hst => by
      rw [norm_shiftHeckeTheta_sub]
      exact norm_signHeckeTheta_sub_le a hs hst) r
  refine hB.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact integral_shiftHeckeTheta_sub h0 hy

/-- If $\chi_\infty \tau_\theta$ is trivial on all units and the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_shiftHeckeCubeDualTheta
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) (r : ℝ) :
    shiftHeckeCubeDualTheta K ε p k θ a =O[atTop] (· ^ r) := by
  have hl := heckeScale_pos K
  have h1 := (isBigO_shiftHeckeCubeTheta (a := dualUnit K a) h0 r).comp_tendsto
    (tendsto_id.const_mul_atTop' hl)
  have h2 : (fun y : ℝ => (heckeScale K * id y) ^ r) =O[atTop] (· ^ r) := by
    refine (isBigO_const_mul_self (heckeScale K ^ r) (fun y : ℝ => y ^ r) atTop).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 0] with y hy
    exact (Real.mul_rpow hl.le hy).symm
  refine IsBigO.of_norm_left ((h1.trans h2).norm_left.congr' ?_ EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [shiftHeckeCubeDualTheta_eq_conj hχ hy, norm_mul, norm_torusConst, one_mul, Complex.norm_conj]
  rfl

end Cube

section Pair

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

variable (ε) in
/-- For $p_v \le 1$, if $\chi_\infty \tau_\theta$ is trivial on all units and the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube, then the cube averages $F$ and $G$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon$ and with both constant terms zero. -/
noncomputable def shiftHeckeFEPair (θ : InfinitePlace K → ℝ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) :
    WeakFEPair ℂ where
  f := shiftHeckeCubeTheta K ε p k θ a
  g := shiftHeckeCubeDualTheta K ε p k θ a
  k := finrank ℚ K / 2
  ε := heckeRootConst K p k a
  f₀ := 0
  g₀ := 0
  hf_int := continuousOn_shiftHeckeCubeTheta.locallyIntegrableOn measurableSet_Ioi
  hg_int := continuousOn_shiftHeckeCubeDualTheta.locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := heckeRootConst_ne_zero
  h_feq x hx := shiftHeckeCubeTheta_one_div hp hx
  hf_top r := by simpa only [sub_zero] using isBigO_shiftHeckeCubeTheta h0 r
  hg_top r := by simpa only [sub_zero] using isBigO_shiftHeckeCubeDualTheta hχ h0 r

variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hp : ∀ v, p v ≤ 1)
  (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
  (h0 : ∀ y : ℝ, 0 < y → ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
include hp hχ h0

/-- The FE pair of the twisted cube averages is a strong FE pair. -/
theorem isStrongFEPair_shiftHeckeFEPair : IsStrongFEPair (shiftHeckeFEPair ε θ a hp hχ h0) :=
  ⟨rfl, rfl⟩

/-- The completed function of the pair is the Mellin transform of $F$. -/
theorem Λ_shiftHeckeFEPair_eq :
    (shiftHeckeFEPair ε θ a hp hχ h0).Λ = mellin (shiftHeckeCubeTheta K ε p k θ a) :=
  (isStrongFEPair_shiftHeckeFEPair hp hχ h0).Λ_eq

/-- The completed function of the dual pair is the Mellin transform of $G$. -/
theorem symm_Λ_shiftHeckeFEPair_eq :
    (shiftHeckeFEPair ε θ a hp hχ h0).symm.Λ = mellin (shiftHeckeCubeDualTheta K ε p k θ a) :=
  (isStrongFEPair_shiftHeckeFEPair hp hχ h0).symm_Λ_eq

/-- The Mellin transform of $F$ continues to an entire function. -/
theorem differentiable_Λ_shiftHeckeFEPair : Differentiable ℂ (shiftHeckeFEPair ε θ a hp hχ h0).Λ :=
  (isStrongFEPair_shiftHeckeFEPair hp hχ h0).differentiable_Λ

/-- The functional equation $\Lambda(n / 2 - s) = \varepsilon \, \mathcal{M}G(s)$ for all complex $s$. -/
theorem Λ_shiftHeckeFEPair_sub (s : ℂ) :
    (shiftHeckeFEPair ε θ a hp hχ h0).Λ (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * mellin (shiftHeckeCubeDualTheta K ε p k θ a) s := by
  have := (shiftHeckeFEPair ε θ a hp hχ h0).functional_equation s
  rw [symm_Λ_shiftHeckeFEPair_eq hp hχ h0, smul_eq_mul] at this
  convert this using 2
  · simp [shiftHeckeFEPair]
  · rfl

omit hp h0 in
/-- **The Mellin transform of the dual cube average.** If $\chi_\infty \tau_\theta$ is trivial on all units, then $\mathcal{M}G_{\mathfrak{a}}(s) = \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$ for all complex $s$. -/
theorem mellin_shiftHeckeCubeDualTheta (s : ℂ) :
    mellin (shiftHeckeCubeDualTheta K ε p k θ a) s = torusConst θ * (heckeScale K : ℂ) ^ (-s) *
      conj (mellin (shiftHeckeCubeTheta K ε p k θ (dualUnit K a)) (conj s)) := by
  have h : mellin (shiftHeckeCubeDualTheta K ε p k θ a) s = mellin (fun y => torusConst θ •
      conj (shiftHeckeCubeTheta K ε p k θ (dualUnit K a) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [shiftHeckeCubeDualTheta_eq_conj hχ hy, smul_eq_mul]
  rw [h, mellin_const_smul, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul,
    smul_eq_mul, map_mul, conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]
  ring

end Pair

section Completed

variable (K) in
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
  (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
  (θ : InfinitePlace K → ℝ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) in
/-- The completed partial Hecke sum $\Lambda_{\mathfrak{a}}(s) = 2^r c_K \, \mathcal{M}F_{\mathfrak{a}}(s)$ with the shifts $i \theta_w$, where $F_{\mathfrak{a}}$ is the cube average `Langlands.Tate.shiftHeckeCubeTheta` and $c_K$ is `Langlands.Tate.unitConst`. -/
noncomputable def shiftCompletedPartialHecke (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * mellin (shiftHeckeCubeTheta K ε p k θ a) s

variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ} {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- The completed partial Hecke sum is $2^r c_K$ times the completed function of the FE pair. -/
theorem shiftCompletedPartialHecke_eq (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) (s : ℂ) :
    shiftCompletedPartialHecke K ε p k θ a s =
      ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (shiftHeckeFEPair ε θ a hp hχ h0).Λ s := by
  rw [Λ_shiftHeckeFEPair_eq hp hχ h0, shiftCompletedPartialHecke]

/-- **The completed partial Hecke sum with the shifts is entire.** -/
theorem differentiable_shiftCompletedPartialHecke (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) :
    Differentiable ℂ (shiftCompletedPartialHecke K ε p k θ a) := by
  have e : shiftCompletedPartialHecke K ε p k θ a =
      fun s => ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (shiftHeckeFEPair ε θ a hp hχ h0).Λ s :=
    funext (shiftCompletedPartialHecke_eq hp hχ h0)
  rw [e]
  exact (differentiable_Λ_shiftHeckeFEPair hp hχ h0).const_mul _

/-- **The completed partial Hecke sum as a series.** If $\chi_\infty \tau_\theta$ is trivial on all units, the twisted term of $\alpha = 0$ has the mean value $0$ over the unit cube and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_{\mathfrak{a}}(s) = \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} w_K \, \Gamma_{p, k, \theta}(s') \, \chi_\infty(\alpha) \, \tau_\theta(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_shiftCompletedPartialHecke
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (shiftGamma p k θ (2 * s / finrank ℚ K) *
        signInfinityWeight ε p k (orbitRep a I : K) * torusWeight θ (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (shiftCompletedPartialHecke K ε p k θ a s) := by
  rw [shiftCompletedPartialHecke, mellin]
  simp_rw [smul_eq_mul]
  exact hasSum_integral_shiftHeckeTheta hχ h0 hs

/-- **The functional equation of the completed partial Hecke sums with the shifts.** Let $p_v \le 1$, let $\chi_\infty \tau_\theta$ be trivial on all units, and let the twisted term of $\alpha = 0$ have the mean value $0$ over the unit cube. Then for all complex $s$, $$\Lambda_{\mathfrak{a}}(n / 2 - s) = \varepsilon_{\mathfrak{a}} \, \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}.$$ -/
theorem shiftCompletedPartialHecke_sub (hp : ∀ v, p v ≤ 1)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) = 1)
    (h0 : ∀ y : ℝ, 0 < y → ∫ c in cube, shiftHeckeTerm ε p k θ 0 (unitScale K y c) = 0) (s : ℂ) :
    shiftCompletedPartialHecke K ε p k θ a (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * torusConst θ * (heckeScale K : ℂ) ^ (-s) *
        conj (shiftCompletedPartialHecke K ε p k θ (dualUnit K a) (conj s)) := by
  rw [shiftCompletedPartialHecke_eq hp hχ h0, Λ_shiftHeckeFEPair_sub hp hχ h0,
    mellin_shiftHeckeCubeDualTheta hχ, shiftCompletedPartialHecke, map_mul, Complex.conj_ofReal]
  ring

end Completed

end Langlands.Tate
