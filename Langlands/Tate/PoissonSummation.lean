/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Poisson summation on $\mathbb{Z}^d$

This file proves the Poisson summation formula for the standard lattice $\mathbb{Z}^d$ in $\mathbb{R}^d$. We model $\mathbb{R}^d$ as `EuclideanSpace ℝ d` for a finite type `d`, and the lattice as the image of `Langlands.Tate.intPoint : (d → ℤ) → EuclideanSpace ℝ d`.

## Conventions

The Fourier transform is the Fourier transform $\mathcal{F}$ of Mathlib, $$\mathcal{F} f(w) = \int_{\mathbb{R}^d} f(v) e^{-2 \pi i \langle v, w \rangle} \, dv,$$ with the Lebesgue measure. So $\mathcal{F} f(w) = \int f(v) \psi_\mathbb{R}(\langle v, w \rangle) \, dv$ for the additive character $\psi_\mathbb{R}(x) = e^{-2 \pi i x}$ of `Langlands.Tate.ArchimedeanFourier`. This measure is self-dual for $\psi_\mathbb{R}$, and $\mathbb{Z}^d$ has covolume one, so no constant appears in the formula.

## Main results

* `Langlands.Tate.tsum_add_intPoint_eq_tsum_fourier`: let $f$ be continuous, let $f$ satisfy the decay condition `Langlands.Tate.HasSummableTranslates`, and let $\sum_k \mathcal{F} f(k)$ converge. Then $$\sum_{m \in \mathbb{Z}^d} f(x + m) = \sum_{k \in \mathbb{Z}^d} \mathcal{F} f(k) e^{2 \pi i \langle x, k \rangle}.$$
* `Langlands.Tate.tsum_intPoint_eq_tsum_fourier`: the case $x = 0$, $\sum_m f(m) = \sum_k \mathcal{F} f(k)$.
* `SchwartzMap.tsum_add_intPoint_eq_tsum_fourier` and `SchwartzMap.tsum_intPoint_eq_tsum_fourier`: the same formulas for each Schwartz function, with no extra hypothesis.
* `SchwartzMap.tsum_add_intPoint_mul_eq_tsum_fourier`: the twisted formula $$\sum_{m} f(x + m) e^{2 \pi i \langle x + m, y \rangle} = \sum_{k} \mathcal{F} f(k - y) e^{2 \pi i \langle x, k \rangle}.$$
* `Langlands.Tate.HasDecay`: the condition $(1 + |x|)^N |f(x)| \le C$. For $N > d$ it implies the decay condition of Poisson summation (`Langlands.Tate.HasDecay.hasSummableTranslates`). It is stable under linear changes of variables (`Langlands.Tate.HasDecay.comp`). Each Schwartz function satisfies it for each $N$ (`SchwartzMap.hasDecay`).

## Proof

Let $P f(x) = \sum_m f(x + m)$ be the periodization of $f$ (`Langlands.Tate.periodize`). The decay condition gives uniform convergence on balls, so $P f$ is continuous. It is invariant under $\mathbb{Z}^d$, so it descends to a continuous function on the torus $\mathbb{T}^d = \mathbb{R}^d / \mathbb{Z}^d$ (`Langlands.Tate.torusPeriodize`).

The key step is the computation of the Fourier coefficients of $P f$ (`Langlands.Tate.mFourierCoeff_torusPeriodize`). The torus is identified with the half open cube $T_0 = (0, 1]^d$. The translates $T_m = m + T_0$ form a partition of $\mathbb{R}^d$ (`Langlands.Tate.tile`). So the integral over $T_0$ of $e^{-2 \pi i \langle y, k \rangle} P f(y)$ unfolds to the integral over $\mathbb{R}^d$ of $e^{-2 \pi i \langle y, k \rangle} f(y)$ (`Langlands.Tate.integral_tile_zero_eq_integral`). This gives $\widehat{P f}(k) = \mathcal{F} f(k)$.

The Fourier coefficients are summable by hypothesis. So the Fourier series of $P f$ converges to $P f$ at each point (`hasSum_mFourier_series_apply_of_summable` in Mathlib). This is the formula. For a Schwartz function $f$, both $f$ and $\mathcal{F} f$ decay faster than each power of $|x|$, and this gives all the hypotheses.

## References

* E. M. Stein and G. Weiss, Introduction to Fourier analysis on Euclidean spaces, chapter VII, section 2.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.2.
-/

open MeasureTheory Set Complex FourierTransform
open scoped RealInnerProductSpace

namespace Langlands.Tate

variable {d : Type*}

/-- The point of $\mathbb{R}^d$ with integer coordinates $m \in \mathbb{Z}^d$. The image of `intPoint` is the standard lattice $\mathbb{Z}^d$ of `EuclideanSpace ℝ d`. -/
noncomputable def intPoint (m : d → ℤ) : EuclideanSpace ℝ d := WithLp.toLp 2 (fun i => (m i : ℝ))

/-- The coordinates of `intPoint m` are the integers $m_i$. -/
@[simp] theorem intPoint_apply (m : d → ℤ) (i : d) : intPoint m i = m i := rfl

/-- The map $m \mapsto m$ from $\mathbb{Z}^d$ to $\mathbb{R}^d$ is additive. -/
theorem intPoint_add (m n : d → ℤ) : intPoint (m + n) = intPoint m + intPoint n := by
  ext i; simp

/-- The map $m \mapsto m$ from $\mathbb{Z}^d$ to $\mathbb{R}^d$ commutes with negation. -/
theorem intPoint_neg (m : d → ℤ) : intPoint (-m) = -intPoint m := by
  ext i; simp

/-- For real $t$, $|e^{2 \pi i t}| = 1$. -/
theorem norm_exp_two_pi_I_mul (t : ℝ) : ‖cexp (2 * Real.pi * I * t)‖ = 1 := by
  rw [show 2 * Real.pi * I * t = ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The map $\mathbb{Z}^d \to \mathbb{R}^d$ is injective. -/
theorem intPoint_injective : Function.Injective (intPoint (d := d)) := by
  intro m n h
  funext i
  have := congrArg (fun x : EuclideanSpace ℝ d => x i) h
  simpa using this

/-- The projection $\mathbb{R}^d \to \mathbb{R}^d / \mathbb{Z}^d$ onto the torus `UnitAddTorus d`. -/
def torusProj (x : EuclideanSpace ℝ d) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

/-- The projection to the torus is invariant under translation by $\mathbb{Z}^d$. -/
theorem torusProj_add_intPoint (x : EuclideanSpace ℝ d) (m : d → ℤ) :
    torusProj (x + intPoint m) = torusProj x := by
  funext i
  simp only [torusProj, PiLp.add_apply, intPoint_apply]
  rw [AddCircle.coe_add, add_eq_left, AddCircle.coe_eq_zero_iff]
  exact ⟨m i, by simp⟩

/-- The projection $\mathbb{R}^d \to \mathbb{R}^d / \mathbb{Z}^d$ is an open quotient map. -/
theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap (torusProj (d := d)) := by
  have h : IsOpenQuotientMap (Pi.map fun (_ : d) (x : ℝ) => (x : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact h.comp (PiLp.homeomorph ..).isOpenQuotientMap

/-- Two points with the same image in the torus differ by a point of $\mathbb{Z}^d$. -/
theorem exists_eq_add_intPoint_of_torusProj_eq {x y : EuclideanSpace ℝ d}
    (h : torusProj x = torusProj y) : ∃ m : d → ℤ, x = y + intPoint m := by
  have : ∀ i, ∃ n : ℤ, x i = y i + n := by
    intro i
    have hi := congrFun h i
    simp only [torusProj] at hi
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at hi
    obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simp at hn; linarith⟩
  choose m hm using this
  exact ⟨m, by ext i; simp [hm]⟩

variable [Fintype d]

/-- The character $e_k$ of the torus pulls back to $x \mapsto e^{2 \pi i \langle x, k \rangle}$ on $\mathbb{R}^d$. -/
theorem mFourier_torusProj (k : d → ℤ) (x : EuclideanSpace ℝ d) :
    UnitAddTorus.mFourier k (torusProj x) = cexp (2 * Real.pi * I * ⟪x, intPoint k⟫) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProj, fourier_coe_apply,
    PiLp.inner_apply, intPoint_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  congr 1 with i
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The half open unit cube $\prod_i (m_i, m_i + 1]$ with corner $m \in \mathbb{Z}^d$. These cubes form a partition of $\mathbb{R}^d$. -/
def tile (m : d → ℤ) : Set (EuclideanSpace ℝ d) := {y | ∀ i, y i ∈ Ioc (m i : ℝ) (m i + 1)}

/-- Each tile is a measurable set. -/
theorem measurableSet_tile (m : d → ℤ) : MeasurableSet (tile m) := by
  have : tile m = ⋂ i, (fun y : EuclideanSpace ℝ d => y i) ⁻¹' Ioc (m i : ℝ) (m i + 1) := by
    ext y; simp [tile]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ioc.preimage (EuclideanSpace.proj i).continuous.measurable

omit [Fintype d] in
/-- A point $y$ is in the tile of $m$ if and only if $\lceil y_i \rceil = m_i + 1$ for each $i$. -/
theorem mem_tile_iff {m : d → ℤ} {y : EuclideanSpace ℝ d} :
    y ∈ tile m ↔ ∀ i, ⌈y i⌉ = m i + 1 := by
  simp only [tile, mem_ofPred_eq, mem_Ioc, Int.ceil_eq_iff]
  push_cast
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [Fintype d] in
/-- Different tiles are disjoint. -/
theorem pairwise_disjoint_tile : Pairwise (Function.onFun Disjoint (tile (d := d))) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro y hm hn
  apply hmn
  funext i
  have h1 := mem_tile_iff.1 hm i
  have h2 := mem_tile_iff.1 hn i
  omega

omit [Fintype d] in
/-- The tiles cover $\mathbb{R}^d$. -/
theorem iUnion_tile : ⋃ m : d → ℤ, tile m = univ := by
  refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨fun i => ⌈y i⌉ - 1, ?_⟩
  rw [mem_tile_iff]
  intro i
  ring

omit [Fintype d] in
/-- The tile of $m$ is the translate of the tile of $0$ by $m$. -/
theorem preimage_add_tile (m : d → ℤ) :
    (· + intPoint m) ⁻¹' tile m = tile (0 : d → ℤ) := by
  ext y
  simp only [tile, mem_preimage, mem_ofPred_eq, PiLp.add_apply, intPoint_apply, mem_Ioc,
    Pi.zero_apply, Int.cast_zero, zero_add]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- A point of the tile of $0$ has norm at most $d$. -/
theorem norm_le_of_mem_tile_zero {y : EuclideanSpace ℝ d} (hy : y ∈ tile (0 : d → ℤ)) :
    ‖y‖ ≤ Fintype.card d := by
  have h1 : ‖y‖ ^ 2 ≤ (Fintype.card d : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hy i
          simp only [Pi.zero_apply, Int.cast_zero, zero_add, mem_Ioc] at this
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith [this.1, this.2]
      _ = Fintype.card d := by simp
  have h2 : (Fintype.card d : ℝ) ≤ (Fintype.card d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card d) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast h
      nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg y) (Nat.cast_nonneg _) two_ne_zero).1 (h1.trans h2)

/-- The tile of $0$ has finite volume. -/
theorem volume_tile_zero_lt_top : volume (tile (0 : d → ℤ)) < ⊤ :=
  ((Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ d)) (r := Fintype.card d)).subset
    fun _ hy => mem_closedBall_zero_iff.2 (norm_le_of_mem_tile_zero hy)).measure_lt_top

/-- $\int_{T_m} g = \int_{T_0} g(y + m) \, dy$, where $T_m$ is the tile of $m$. -/
theorem setIntegral_tile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : EuclideanSpace ℝ d → E) (m : d → ℤ) :
    ∫ z in tile m, g z = ∫ y in tile 0, g (y + intPoint m) := by
  rw [← preimage_add_tile m]
  exact ((measurePreserving_add_right volume (intPoint m)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) g (tile m)).symm

/-- The decay condition for Poisson summation. For each $R$ there is a summable sequence $u$ on $\mathbb{Z}^d$ with $|f(x + m)| \le u_m$ for all $m$ and all $|x| \le R$. This makes the series $\sum_m f(x + m)$ converge uniformly on compact sets. -/
def HasSummableTranslates (f : EuclideanSpace ℝ d → ℂ) : Prop :=
  ∀ R : ℝ, ∃ u : (d → ℤ) → ℝ, Summable u ∧
    ∀ (m : d → ℤ) (x : EuclideanSpace ℝ d), ‖x‖ ≤ R → ‖f (x + intPoint m)‖ ≤ u m

/-- The periodization $P f(x) = \sum_{m \in \mathbb{Z}^d} f(x + m)$ of $f$. -/
noncomputable def periodize (f : EuclideanSpace ℝ d → ℂ) (x : EuclideanSpace ℝ d) : ℂ :=
  ∑' m : d → ℤ, f (x + intPoint m)

omit [Fintype d] in
/-- The periodization is invariant under translation by $\mathbb{Z}^d$. -/
theorem periodize_add_intPoint (f : EuclideanSpace ℝ d → ℂ) (x : EuclideanSpace ℝ d)
    (n : d → ℤ) : periodize f (x + intPoint n) = periodize f x := by
  simp only [periodize, add_assoc, ← intPoint_add]
  exact (Equiv.addLeft n).tsum_eq fun m => f (x + intPoint m)

omit [Fintype d] in
/-- The periodization takes the same value at two points with the same image in the torus. -/
theorem periodize_eq_of_torusProj_eq (f : EuclideanSpace ℝ d → ℂ) {x y : EuclideanSpace ℝ d}
    (h : torusProj x = torusProj y) : periodize f x = periodize f y := by
  obtain ⟨m, rfl⟩ := exists_eq_add_intPoint_of_torusProj_eq h
  exact periodize_add_intPoint f y m

/-- Under the decay condition, the series $\sum_m f(x + m)$ converges. -/
theorem HasSummableTranslates.summable {f : EuclideanSpace ℝ d → ℂ} (hf : HasSummableTranslates f)
    (x : EuclideanSpace ℝ d) : Summable fun m : d → ℤ => f (x + intPoint m) := by
  obtain ⟨u, hu, hb⟩ := hf ‖x‖
  exact Summable.of_norm_bounded hu fun m => hb m x le_rfl

/-- Under the decay condition, the periodization of a continuous function is continuous. This is the Weierstrass M-test on balls. -/
theorem continuous_periodize {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) : Continuous (periodize f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨u, hu, hb⟩ := hf (‖x‖ + 1)
  have : ContinuousOn (periodize f) (Metric.closedBall x 1) := by
    refine continuousOn_tsum (fun m => (hc.comp (continuous_id.add continuous_const)).continuousOn) hu ?_
    intro m y hy
    refine hb m y ?_
    have := norm_le_norm_add_norm_sub' y x
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    linarith
  exact this.continuousAt (Metric.closedBall_mem_nhds x one_pos)

/-- The periodization of $f$ as a function on the torus $\mathbb{R}^d / \mathbb{Z}^d$. -/
noncomputable def torusPeriodize (f : EuclideanSpace ℝ d → ℂ) (t : UnitAddTorus d) : ℂ :=
  periodize f (Function.surjInv isOpenQuotientMap_torusProj.surjective t)

omit [Fintype d] in
/-- The function `torusPeriodize f` on the torus lifts to the periodization of $f$. -/
theorem torusPeriodize_torusProj (f : EuclideanSpace ℝ d → ℂ) (x : EuclideanSpace ℝ d) :
    torusPeriodize f (torusProj x) = periodize f x :=
  periodize_eq_of_torusProj_eq f (Function.surjInv_eq isOpenQuotientMap_torusProj.surjective _)

/-- Under the decay condition, `torusPeriodize f` is continuous on the torus. -/
theorem continuous_torusPeriodize {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) : Continuous (torusPeriodize f) := by
  rw [isOpenQuotientMap_torusProj.isQuotientMap.continuous_iff]
  have : torusPeriodize f ∘ torusProj = periodize f := funext (torusPeriodize_torusProj f)
  rw [this]
  exact continuous_periodize hc hf

/-- A function is integrable on a tile $T_m$ if and only if its translate by $m$ is integrable on $T_0$. -/
theorem integrableOn_tile_iff {E : Type*} [NormedAddCommGroup E] (g : EuclideanSpace ℝ d → E)
    (m : d → ℤ) :
    IntegrableOn g (tile m) ↔ IntegrableOn (fun y => g (y + intPoint m)) (tile 0) := by
  rw [← preimage_add_tile m]
  exact ((measurePreserving_add_right volume (intPoint m)).integrableOn_comp_preimage
    (measurableEmbedding_addRight _)).symm

/-- A continuous function with the decay condition is integrable on $\mathbb{R}^d$. -/
theorem integrable_of_hasSummableTranslates {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) : Integrable f := by
  obtain ⟨u, hu, hb⟩ := hf (Fintype.card d)
  have hV := volume_tile_zero_lt_top (d := d)
  rw [← integrableOn_univ, ← iUnion_tile]
  refine integrableOn_iUnion_of_summable_integral_norm (fun m => ?_) ?_
  · rw [integrableOn_tile_iff]
    refine IntegrableOn.of_bound hV
      (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable (u m) ?_
    exact ae_restrict_of_forall_mem (measurableSet_tile 0) fun y hy =>
      hb m y (norm_le_of_mem_tile_zero hy)
  · refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _)
      (fun m => ?_) (hu.mul_right (volume.real (tile (0 : d → ℤ))))
    rw [setIntegral_tile (fun x => ‖f x‖) m]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hV fun y hy => ?_
    rw [norm_norm]
    exact hb m y (norm_le_of_mem_tile_zero hy)

/-- Unfolding of the integral. Let $g$ be continuous, periodic for $\mathbb{Z}^d$ and of absolute value one. Then $\int_{T_0} g \cdot P f = \int_{\mathbb{R}^d} g f$. -/
theorem integral_tile_zero_eq_integral {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) (g : EuclideanSpace ℝ d → ℂ) (hg : Continuous g)
    (hgn : ∀ y, ‖g y‖ = 1) (hgp : ∀ y m, g (y + intPoint m) = g y) :
    ∫ y in tile 0, g y * periodize f y = ∫ y, g y * f y := by
  obtain ⟨u, hu, hb⟩ := hf (Fintype.card d)
  have hV := volume_tile_zero_lt_top (d := d)
  have hint : ∀ m : d → ℤ, IntegrableOn (fun y => g y * f (y + intPoint m)) (tile 0) := by
    intro m
    refine IntegrableOn.of_bound hV
      (hg.mul (hc.comp (continuous_id.add continuous_const))).aestronglyMeasurable (u m) ?_
    refine ae_restrict_of_forall_mem (measurableSet_tile 0) fun y hy => ?_
    rw [norm_mul, hgn, one_mul]
    exact hb m y (norm_le_of_mem_tile_zero hy)
  calc ∫ y in tile 0, g y * periodize f y
      = ∫ y in tile 0, ∑' m : d → ℤ, g y * f (y + intPoint m) := by
        simp only [periodize, tsum_mul_left]
    _ = ∑' m : d → ℤ, ∫ y in tile 0, g y * f (y + intPoint m) := by
        refine (integral_tsum_of_summable_integral_norm hint ?_).symm
        refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _)
          (fun m => ?_) (hu.mul_right (volume.real (tile (0 : d → ℤ))))
        refine (le_abs_self _).trans ?_
        rw [← Real.norm_eq_abs]
        refine norm_setIntegral_le_of_norm_le_const hV fun y hy => ?_
        rw [norm_norm, norm_mul, hgn, one_mul]
        exact hb m y (norm_le_of_mem_tile_zero hy)
    _ = ∑' m : d → ℤ, ∫ z in tile m, g z * f z := by
        refine tsum_congr fun m => ?_
        rw [setIntegral_tile (fun z => g z * f z) m]
        simp only [hgp]
    _ = ∫ z in ⋃ m : d → ℤ, tile m, g z * f z := by
        refine (integral_iUnion measurableSet_tile pairwise_disjoint_tile ?_).symm
        rw [iUnion_tile, integrableOn_univ]
        exact ((integrable_of_hasSummableTranslates hc hf).bdd_mul
          hg.aestronglyMeasurable (c := 1) (ae_of_all _ fun y => (hgn y).le))
    _ = ∫ y, g y * f y := by rw [iUnion_tile, Measure.restrict_univ]

/-- The Fourier coefficients of the periodization are the values of the Fourier transform: $\widehat{P f}(k) = \mathcal{F} f(k)$ for $k \in \mathbb{Z}^d$. -/
theorem mFourierCoeff_torusPeriodize {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodize f) k = 𝓕 f (intPoint k) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k 0]
  have h1 : {x : d → ℝ | ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} =
      WithLp.toLp 2 ⁻¹' tile (0 : d → ℤ) := by
    ext x; simp [tile]
  rw [h1]
  have h2 := (PiLp.volume_preserving_toLp d).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (d → ℝ)).measurableEmbedding
    (fun y => UnitAddTorus.mFourier (-k) (torusProj y) • torusPeriodize f (torusProj y))
    (tile 0)
  refine h2.trans ?_
  simp only [torusPeriodize_torusProj, smul_eq_mul]
  rw [integral_tile_zero_eq_integral hc hf (fun y => UnitAddTorus.mFourier (-k) (torusProj y))
    ((UnitAddTorus.mFourier (-k)).continuous.comp isOpenQuotientMap_torusProj.continuous)]
  · rw [Real.fourier_eq']
    congr 1 with y
    rw [mFourier_torusProj, smul_eq_mul, intPoint_neg, inner_neg_right]
    congr 2
    push_cast
    ring
  · intro y
    rw [mFourier_torusProj, norm_exp_two_pi_I_mul]
  · intro y m
    simp [torusProj_add_intPoint]

/-- Poisson summation on $\mathbb{Z}^d$ in the form of a `HasSum`: the series $\sum_k \mathcal{F} f(k) e^{2 \pi i \langle x, k \rangle}$ has the sum $\sum_m f(x + m)$. -/
theorem hasSum_tsum_add_intPoint {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) (hF : Summable fun k : d → ℤ => 𝓕 f (intPoint k))
    (x : EuclideanSpace ℝ d) :
    HasSum (fun k : d → ℤ => 𝓕 f (intPoint k) * cexp (2 * Real.pi * I * ⟪x, intPoint k⟫))
      (∑' m : d → ℤ, f (x + intPoint m)) := by
  let F : C(UnitAddTorus d, ℂ) := ⟨torusPeriodize f, continuous_torusPeriodize hc hf⟩
  have hcoeff : UnitAddTorus.mFourierCoeff F = fun k => 𝓕 f (intPoint k) :=
    funext (mFourierCoeff_torusPeriodize hc hf)
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F) (hcoeff ▸ hF)
    (torusProj x)
  rw [hcoeff] at hs
  simp only [smul_eq_mul, mFourier_torusProj] at hs
  have h2 : F (torusProj x) = ∑' m : d → ℤ, f (x + intPoint m) := torusPeriodize_torusProj f x
  rwa [h2] at hs

/-- For $N > d$, the series $\sum_{m \in \mathbb{Z}^d} (1 + |m|)^{-N}$ converges. -/
theorem summable_one_add_norm_intPoint_pow_inv {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun m : d → ℤ => ((1 + ‖intPoint m‖) ^ N)⁻¹ := by
  let b := (EuclideanSpace.basisFun d ℝ).toBasis
  let L := Submodule.span ℤ (Set.range b)
  have hrank : Module.finrank ℤ L = Fintype.card d := by
    rw [ZLattice.rank ℝ L, finrank_euclideanSpace]
  have hmem : ∀ m : d → ℤ, intPoint m ∈ L := by
    intro m
    have : intPoint m = ∑ i, m i • b i := by
      ext j
      classical
      simp [b, EuclideanSpace.basisFun_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let j : (d → ℤ) → L := fun m => ⟨intPoint m, hmem m⟩
  have hj : Function.Injective j := fun m n h =>
    intPoint_injective (congrArg Subtype.val h)
  have hs := (ZLattice.summable_norm_pow_inv L N (hrank ▸ hN)).comp_injective hj
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hpos : 0 < ‖intPoint m‖ := by
    rw [norm_pos_iff]
    intro h
    exact hm (intPoint_injective (h.trans (by ext; simp)))
  simp only [Function.comp_apply, j, ← Submodule.norm_coe, norm_inv, norm_pow, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), inv_pow]
  gcongr
  linarith

/-- **Poisson summation on $\mathbb{Z}^d$.** Let $f$ be continuous with the decay condition, and let $\sum_k \mathcal{F} f(k)$ converge. Then $$\sum_{m \in \mathbb{Z}^d} f(x + m) = \sum_{k \in \mathbb{Z}^d} \mathcal{F} f(k) e^{2 \pi i \langle x, k \rangle}.$$ -/
theorem tsum_add_intPoint_eq_tsum_fourier {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) (hF : Summable fun k : d → ℤ => 𝓕 f (intPoint k))
    (x : EuclideanSpace ℝ d) :
    ∑' m : d → ℤ, f (x + intPoint m) =
      ∑' k : d → ℤ, 𝓕 f (intPoint k) * cexp (2 * Real.pi * I * ⟪x, intPoint k⟫) :=
  (hasSum_tsum_add_intPoint hc hf hF x).tsum_eq.symm

/-- **Poisson summation on $\mathbb{Z}^d$ at $x = 0$.** Under the hypotheses of `tsum_add_intPoint_eq_tsum_fourier`, $\sum_m f(m) = \sum_k \mathcal{F} f(k)$. -/
theorem tsum_intPoint_eq_tsum_fourier {f : EuclideanSpace ℝ d → ℂ} (hc : Continuous f)
    (hf : HasSummableTranslates f) (hF : Summable fun k : d → ℤ => 𝓕 f (intPoint k)) :
    ∑' m : d → ℤ, f (intPoint m) = ∑' k : d → ℤ, 𝓕 f (intPoint k) := by
  simpa using tsum_add_intPoint_eq_tsum_fourier hc hf hF 0

/-- The function $f$ decays like $|x|^{-N}$: there is a constant $C$ with $(1 + |x|)^N |f(x)| \le C$ for all $x$. -/
def HasDecay {E : Type*} [NormedAddCommGroup E] (f : E → ℂ) (N : ℕ) : Prop :=
  ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C

/-- The bound $(1 + |x|)^N |f(x)| \le C$ in the form $|f(x)| \le C / (1 + |x|)^N$. -/
theorem HasDecay.le_div {E : Type*} [NormedAddCommGroup E] {f : E → ℂ} {N : ℕ}
    {C : ℝ} (hC : ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C) (x : E) :
    ‖f x‖ ≤ C / (1 + ‖x‖) ^ N := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hC x

/-- The decay condition is stable under composition with a map $T$ that satisfies $|z| \le K |T z|$, for example a linear isomorphism. -/
theorem HasDecay.comp {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : F → ℂ} {N : ℕ} (hf : HasDecay f N) (T : E → F) (K : ℝ)
    (hK : ∀ z, ‖z‖ ≤ K * ‖T z‖) : HasDecay (f ∘ T) N := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC (T 0))
  refine ⟨max 1 K ^ N * C, fun z => ?_⟩
  have h1 : 1 + ‖z‖ ≤ max 1 K * (1 + ‖T z‖) := by
    have := hK z
    nlinarith [le_max_left 1 K, le_max_right 1 K, norm_nonneg (T z), norm_nonneg z]
  calc (1 + ‖z‖) ^ N * ‖(f ∘ T) z‖ ≤ (max 1 K * (1 + ‖T z‖)) ^ N * ‖f (T z)‖ := by
        rw [Function.comp_apply]; gcongr
    _ = max 1 K ^ N * ((1 + ‖T z‖) ^ N * ‖f (T z)‖) := by rw [mul_pow]; ring
    _ ≤ max 1 K ^ N * C := by gcongr; exact hC _

/-- On $\mathbb{R}^d$, decay of order $N > d$ implies the decay condition `HasSummableTranslates` for Poisson summation. -/
theorem HasDecay.hasSummableTranslates {f : EuclideanSpace ℝ d → ℂ} {N : ℕ} (hf : HasDecay f N)
    (hN : Fintype.card d < N) : HasSummableTranslates f := by
  obtain ⟨C, hC⟩ := hf
  intro R
  refine ⟨fun m => C * (1 + |R|) ^ N / (1 + ‖intPoint m‖) ^ N, ?_, fun m x hx => ?_⟩
  · simp_rw [div_eq_mul_inv]
    exact (summable_one_add_norm_intPoint_pow_inv hN).mul_left _
  · refine (HasDecay.le_div hC _).trans ?_
    have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
    rw [div_le_div_iff₀ (by positivity) (by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    have h2 := norm_le_norm_add_norm_sub' (intPoint m) (x + intPoint m)
    have h3 : intPoint m - (x + intPoint m) = -x := by abel
    rw [h3, norm_neg] at h2
    have h4 : ‖x‖ ≤ |R| := hx.trans (le_abs_self R)
    nlinarith [norm_nonneg (x + intPoint m), abs_nonneg R]

/-- On $\mathbb{R}^d$, decay of order $N > d$ implies that $\sum_{k \in \mathbb{Z}^d} f(k)$ converges. -/
theorem HasDecay.summable_intPoint {f : EuclideanSpace ℝ d → ℂ} {N : ℕ} (hf : HasDecay f N)
    (hN : Fintype.card d < N) : Summable fun k : d → ℤ => f (intPoint k) := by
  simpa using (hf.hasSummableTranslates hN).summable 0

open scoped SchwartzMap

/-- A Schwartz function decays of each order $N$. -/
theorem _root_.SchwartzMap.hasDecay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℂ)) (N : ℕ) : HasDecay f N :=
  ⟨_, fun y => by
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl f y⟩

/-- A Schwartz function on $\mathbb{R}^d$ satisfies the decay condition for Poisson summation. -/
theorem _root_.SchwartzMap.hasSummableTranslates (f : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    HasSummableTranslates f :=
  (f.hasDecay (Fintype.card d + 1)).hasSummableTranslates (by omega)

/-- **Poisson summation for Schwartz functions on $\mathbb{R}^d$.** $$\sum_{m \in \mathbb{Z}^d} f(x + m) = \sum_{k \in \mathbb{Z}^d} \mathcal{F} f(k) e^{2 \pi i \langle x, k \rangle}.$$ -/
theorem _root_.SchwartzMap.tsum_add_intPoint_eq_tsum_fourier (f : 𝓢(EuclideanSpace ℝ d, ℂ))
    (x : EuclideanSpace ℝ d) :
    ∑' m : d → ℤ, f (x + intPoint m) =
      ∑' k : d → ℤ, 𝓕 f (intPoint k) * cexp (2 * Real.pi * I * ⟪x, intPoint k⟫) := by
  rw [SchwartzMap.fourier_coe]
  refine Langlands.Tate.tsum_add_intPoint_eq_tsum_fourier f.continuous f.hasSummableTranslates ?_ x
  rw [← SchwartzMap.fourier_coe]
  convert (𝓕 f).hasSummableTranslates.summable 0 using 3 with k
  rw [zero_add]

/-- **Poisson summation for Schwartz functions on $\mathbb{R}^d$ at $x = 0$.** $\sum_{m \in \mathbb{Z}^d} f(m) = \sum_{k \in \mathbb{Z}^d} \mathcal{F} f(k)$. -/
theorem _root_.SchwartzMap.tsum_intPoint_eq_tsum_fourier (f : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    ∑' m : d → ℤ, f (intPoint m) = ∑' k : d → ℤ, 𝓕 f (intPoint k) := by
  simpa using f.tsum_add_intPoint_eq_tsum_fourier 0

/-- **Twisted Poisson summation for Schwartz functions on $\mathbb{R}^d$.** For $x, y \in \mathbb{R}^d$, $$\sum_{m \in \mathbb{Z}^d} f(x + m) e^{2 \pi i \langle x + m, y \rangle} = \sum_{k \in \mathbb{Z}^d} \mathcal{F} f(k - y) e^{2 \pi i \langle x, k \rangle}.$$ This is Poisson summation for the function $z \mapsto f(z) e^{2 \pi i \langle z, y \rangle}$. -/
theorem _root_.SchwartzMap.tsum_add_intPoint_mul_eq_tsum_fourier
    (f : 𝓢(EuclideanSpace ℝ d, ℂ)) (x y : EuclideanSpace ℝ d) :
    ∑' m : d → ℤ, f (x + intPoint m) * cexp (2 * Real.pi * I * ⟪x + intPoint m, y⟫) =
      ∑' k : d → ℤ, 𝓕 f (intPoint k - y) * cexp (2 * Real.pi * I * ⟪x, intPoint k⟫) := by
  set g : EuclideanSpace ℝ d → ℂ := fun z => f z * cexp (2 * Real.pi * I * ⟪z, y⟫)
  have hc : Continuous g := f.continuous.mul (by fun_prop)
  have hf : HasSummableTranslates g := by
    intro R
    obtain ⟨u, hu, hb⟩ := f.hasSummableTranslates R
    refine ⟨u, hu, fun m z hz => ?_⟩
    simp only [g, norm_mul, norm_exp_two_pi_I_mul, mul_one]
    exact hb m z hz
  have hg : ∀ w, 𝓕 g w = 𝓕 f (w - y) := by
    intro w
    rw [SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
    congr 1 with v
    simp only [g, smul_eq_mul]
    rw [mul_comm (f v), ← mul_assoc, ← Complex.exp_add, inner_sub_right]
    congr 2
    push_cast
    ring
  have hF : Summable fun k : d → ℤ => 𝓕 g (intPoint k) := by
    simp only [hg]
    convert (𝓕 f).hasSummableTranslates.summable (-y) using 3 with k
    rw [sub_eq_neg_add]
  have := Langlands.Tate.tsum_add_intPoint_eq_tsum_fourier hc hf hF x
  simpa only [g, hg] using this

end Langlands.Tate
