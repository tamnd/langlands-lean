/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.IdealZeta
import Langlands.Tate.ImaginaryQuadratic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The theta function of a fractional ideal on the units

Let $K$ be a number field with $r = r_1 + r_2 - 1$ fundamental units $\varepsilon_1, \dots, \varepsilon_r$. For $y > 0$ and $c \in \mathbb{R}^r$ put $$t(y, c)_w = y \exp\Big(2 \sum_i c_i \log |\varepsilon_i|_w\Big).$$ For an integer vector $k$ the vector $t(y, c + k)$ is $t(y, c)$ times $|u|_w^2$ for the unit $u = \prod_i \varepsilon_i^{k_i}$. The theta function $\theta_{\mathfrak{a}}$ of `Langlands/Tate/DedekindTheta.lean` is invariant under the units, so $c \mapsto \theta_{\mathfrak{a}}(t(y, c))$ is periodic for $\mathbb{Z}^r$. This file defines $$\Theta_{\mathfrak{a}}(y) = \int_{[0, 1)^r} \theta_{\mathfrak{a}}(t(y, c)) \, dc,$$ and proves the transformation formula $$\Theta_{\mathfrak{a}}(1/y) = \frac{y^{n/2}}{N(\mathfrak{a}) \sqrt{|d_K|}} \, \Theta_{\mathfrak{a}^\vee}(y).$$ The proof uses the theta formula for $\theta_{\mathfrak{a}}$, the product formula $\prod_w |\varepsilon_i|_w^{n_w} = 1$, and the fact that $-[0, 1)^r$ is also a fundamental domain of $\mathbb{Z}^r$. With the decay of $\Theta_{\mathfrak{a}}(y) - 1$ at infinity, the pair $(\Theta_{\mathfrak{a}}, \Theta_{\mathfrak{a}^\vee})$ satisfies the hypotheses of `WeakFEPair` in Mathlib, with weight $n/2$.

This is the first step of Hecke's proof of the functional equation of the Dedekind zeta function for every number field. The Mellin transform of $\Theta_{\mathfrak{a}} - 1$ is a partial zeta function of the class of $\mathfrak{a}$, because the integral over $[0, 1)^r$ and the sum over $\mathfrak{a}$ together give the integral over all of $(0, \infty)^{S_\infty}$ for each orbit of the units.

## Main definitions

* `Langlands.Tate.unitScale`: the vector $t(y, c)$.
* `Langlands.Tate.unitTheta`: the function $\Theta_{\mathfrak{a}}$.
* `Langlands.Tate.unitThetaFEPair`: the pair $(\Theta_{\mathfrak{a}}, \Theta_{\mathfrak{a}^\vee})$ as a `WeakFEPair`.

## Main results

* `Langlands.Tate.dedekindTheta_unitScale_add_int`: the periodicity in $c$.
* `Langlands.Tate.unitTheta_inv`: the transformation formula.
-/

namespace Langlands.Tate

open Module Filter Topology Asymptotics MeasureTheory Set NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.mixedEmbedding

open scoped nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

section Scale

/-- The logarithm of the absolute value at a place $w$, as an additive map on the units: $u \mapsto \log |u|_w$. -/
noncomputable def placeLog (w : InfinitePlace K) : Additive (𝓞 K)ˣ →+ ℝ where
  toFun u := Real.log (w ((Additive.toMul u : (𝓞 K)ˣ) : K))
  map_zero' := by simp
  map_add' u v := by
    rw [toMul_add, coe_mul, map_mul,
      Real.log_mul (pos_iff.2 (coe_ne_zero _)).ne' (pos_iff.2 (coe_ne_zero _)).ne']

/-- The coordinate $\log |\varepsilon_i|_w$ of the fundamental unit $\varepsilon_i$ at the place $w$. -/
noncomputable def unitLog (i : Fin (rank K)) (w : InfinitePlace K) : ℝ :=
  placeLog K w (Additive.ofMul (fundSystem K i))

/-- The product formula for a fundamental unit: $\sum_w n_w \log |\varepsilon_i|_w = 0$. -/
theorem sum_mult_unitLog (i : Fin (rank K)) : ∑ w, (mult w : ℝ) * unitLog K i w = 0 :=
  sum_mult_mul_log (fundSystem K i)

/-- For an integer vector $k$, the unit $\prod_i \varepsilon_i^{k_i}$. -/
noncomputable def unitOfInt (k : Fin (rank K) → ℤ) : (𝓞 K)ˣ :=
  ∏ i, fundSystem K i ^ k i

/-- The absolute value of $u = \prod_i \varepsilon_i^{k_i}$ at $w$ is $\exp(\sum_i k_i \log |\varepsilon_i|_w)$. -/
theorem place_unitOfInt (k : Fin (rank K) → ℤ) (w : InfinitePlace K) :
    w (unitOfInt K k : K) = Real.exp (∑ i, (k i : ℝ) * unitLog K i w) := by
  have h : placeLog K w (Additive.ofMul (unitOfInt K k)) = ∑ i, (k i : ℝ) * unitLog K i w := by
    rw [unitOfInt, ofMul_prod, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofMul_zpow, map_zsmul, zsmul_eq_mul, unitLog]
  rw [← h]
  exact (Real.exp_log (pos_iff.2 (coe_ne_zero _))).symm

/-- The vector $t(y, c)_w = y \exp(2 \sum_i c_i \log |\varepsilon_i|_w)$. -/
noncomputable def unitScale (y : ℝ) (c : Fin (rank K) → ℝ) (w : InfinitePlace K) : ℝ :=
  y * Real.exp (2 * ∑ i, c i * unitLog K i w)

variable {K}

theorem unitScale_pos {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) (w : InfinitePlace K) :
    0 < unitScale K y c w :=
  mul_pos hy (Real.exp_pos _)

/-- A shift of $c$ by an integer vector $k$ multiplies $t(y, c)_w$ by $|u|_w^2$ for $u = \prod_i \varepsilon_i^{k_i}$. -/
theorem unitScale_add_int (y : ℝ) (c : Fin (rank K) → ℝ) (k : Fin (rank K) → ℤ)
    (w : InfinitePlace K) :
    unitScale K y (c + fun i => (k i : ℝ)) w = unitScale K y c w * w (unitOfInt K k : K) ^ 2 := by
  rw [unitScale, unitScale, place_unitOfInt, sq, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- The theta function is periodic in $c$: $\theta_I(t(y, c + k)) = \theta_I(t(y, c))$ for each integer vector $k$. -/
theorem dedekindTheta_unitScale_add_int (I : FractionalIdeal (𝓞 K)⁰ K) (y : ℝ)
    (c : Fin (rank K) → ℝ) (k : Fin (rank K) → ℤ) :
    dedekindTheta K I (unitScale K y (c + fun i => (k i : ℝ))) =
      dedekindTheta K I (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (k i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K k : K) ^ 2 :=
    funext fun w => unitScale_add_int y c k w
  rw [h, dedekindTheta_unit]

/-- The inverse of $t(y, c)$ is $t(y^{-1}, -c)$. -/
theorem unitScale_inv (y : ℝ) (c : Fin (rank K) → ℝ) (w : InfinitePlace K) :
    (unitScale K y c w)⁻¹ = unitScale K y⁻¹ (-c) w := by
  rw [unitScale, unitScale, mul_inv, ← Real.exp_neg]
  congr 2
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- The product formula for $t(y, c)$: $\prod_w \sqrt{t(y, c)_w}^{\,n_w} = \sqrt{y}^{\,n}$. -/
theorem prod_sqrt_unitScale {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ) :
    ∏ w, √(unitScale K y c w) ^ mult w = √y ^ finrank ℚ K := by
  have h1 : ∀ w : InfinitePlace K, √(unitScale K y c w) ^ mult w =
      √y ^ mult w * Real.exp ((mult w : ℝ) * ∑ i, c i * unitLog K i w) := by
    intro w
    have he : Real.exp (2 * ∑ i, c i * unitLog K i w) =
        Real.exp (∑ i, c i * unitLog K i w) * Real.exp (∑ i, c i * unitLog K i w) := by
      rw [← Real.exp_add, two_mul]
    rw [unitScale, he, Real.sqrt_mul hy, Real.sqrt_mul_self (Real.exp_pos _).le, mul_pow,
      ← Real.exp_nat_mul]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, prod_sqrt_pow_mult, ← Real.exp_sum]
  have h2 : ∑ w : InfinitePlace K, (mult w : ℝ) * ∑ i, c i * unitLog K i w = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := sum_mult_unitLog K i
    calc ∑ w : InfinitePlace K, (mult w : ℝ) * (c i * unitLog K i w)
        = c i * ∑ w : InfinitePlace K, (mult w : ℝ) * unitLog K i w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ = 0 := by rw [this, mul_zero]
  rw [h2, Real.exp_zero, mul_one]

end Scale

section Bounds

variable {K}

/-- On a constant vector the theta function of $\mathfrak{a}$ is the theta function of its lattice: $\theta_{\mathfrak{a}}((t)_w) = \theta_{\Lambda(\mathfrak{a})}(t)$. -/
theorem dedekindTheta_const (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    dedekindTheta K a (fun _ => t) = latticeTheta (traceLattice K a) t := by
  rw [latticeTheta, tsum_traceLattice K a fun r => Real.exp (-(Real.pi * t) * r), dedekindTheta]
  refine tsum_congr fun α => ?_
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The theta function decreases in each variable: if $0 < s_w \le t_w$ for each $w$, then $\theta_{\mathfrak{a}}(t) \le \theta_{\mathfrak{a}}(s)$. -/
theorem dedekindTheta_anti (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s t : InfinitePlace K → ℝ}
    (hs : ∀ w, 0 < s w) (hst : ∀ w, s w ≤ t w) :
    dedekindTheta K a t ≤ dedekindTheta K a s := by
  have ht : ∀ w, 0 < t w := fun w => (hs w).trans_le (hst w)
  refine (summable_dedekindTheta a ht).tsum_le_tsum (fun α => ?_) (summable_dedekindTheta a hs)
  refine Real.exp_le_exp.2 ?_
  have : ∑ w, (mult w : ℝ) * s w * w (α : K) ^ 2 ≤ ∑ w, (mult w : ℝ) * t w * w (α : K) ^ 2 :=
    Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hst w) (Nat.cast_nonneg _)) (sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- The term $\alpha = 0$ gives $\theta_{\mathfrak{a}}(t) \ge 1$. -/
theorem one_le_dedekindTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : 1 ≤ dedekindTheta K a t := by
  have h := (summable_dedekindTheta a ht).le_tsum
    ⟨0, Submodule.zero_mem ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)⟩
    fun _ _ => (Real.exp_pos _).le
  rw [dedekindTheta]
  simpa using h

/-- The theta function is continuous at each $t$ with $t_w > 0$ for all $w$. On the set of $s$ with $s_w > t_w / 2$ the series is dominated by the series of $\theta_{\mathfrak{a}}(t / 2)$. -/
theorem continuousAt_dedekindTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) : ContinuousAt (dedekindTheta K a) t := by
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | t w / 2 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have htU : t ∈ U := mem_iInter.2 fun w => half_lt_self (ht w)
  have hh : ∀ w, 0 < (fun w => t w / 2) w := fun w => half_pos (ht w)
  have hc : ContinuousOn (fun s => ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K),
      Real.exp (-Real.pi * ∑ w, (mult w : ℝ) * s w * w (α : K) ^ 2)) U := by
    refine continuousOn_tsum (fun α => by fun_prop) (summable_dedekindTheta a hh) ?_
    intro α s hs
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ?_
    have hs' := mem_iInter.1 hs
    have : ∑ w, (mult w : ℝ) * (t w / 2) * w (α : K) ^ 2 ≤
        ∑ w, (mult w : ℝ) * s w * w (α : K) ^ 2 :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hs' w).le (Nat.cast_nonneg _)) (sq_nonneg _)
    nlinarith [Real.pi_pos]
  exact hc.continuousAt (hU.mem_nhds htU)

theorem continuous_unitScale (y : ℝ) : Continuous fun c => unitScale K y c :=
  continuous_pi fun w => by unfold unitScale; fun_prop

theorem continuous_unitScale_left (c : Fin (rank K) → ℝ) :
    Continuous fun y => unitScale K y c :=
  continuous_pi fun w => by unfold unitScale; fun_prop

/-- For $y > 0$ the function $c \mapsto \theta_{\mathfrak{a}}(t(y, c))$ is continuous. -/
theorem continuous_dedekindTheta_unitScale (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ}
    (hy : 0 < y) : Continuous fun c => dedekindTheta K a (unitScale K y c) :=
  continuous_iff_continuousAt.2 fun c =>
    (continuousAt_dedekindTheta a (unitScale_pos hy c)).comp (continuous_unitScale y).continuousAt

variable (K) in
/-- The constant $m = \exp(-2 \sum_i \sum_w |\log |\varepsilon_i|_w|)$. For $c \in [0, 1]^r$ each coordinate of $t(y, c)$ is at least $y m$. -/
noncomputable def unitBound : ℝ :=
  Real.exp (-2 * ∑ i, ∑ w, |unitLog K i w|)

theorem unitBound_pos : 0 < unitBound K :=
  Real.exp_pos _

/-- For $c \in [0, 1]^r$ and $y \ge 0$, $y m \le t(y, c)_w$ for each place $w$. -/
theorem mul_unitBound_le {y : ℝ} (hy : 0 ≤ y) {c : Fin (rank K) → ℝ}
    (hc : ∀ i, c i ∈ Icc (0 : ℝ) 1) (w : InfinitePlace K) :
    y * unitBound K ≤ unitScale K y c w := by
  rw [unitScale, unitBound]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hy
  have h1 : ∀ i, -|unitLog K i w| ≤ c i * unitLog K i w := fun i => by
    obtain ⟨h0, h1⟩ := hc i
    rcases le_total 0 (unitLog K i w) with h | h
    · rw [abs_of_nonneg h]
      nlinarith
    · rw [abs_of_nonpos h]
      nlinarith
  have h2 : ∀ i, |unitLog K i w| ≤ ∑ v, |unitLog K i v| := fun i =>
    Finset.single_le_sum (f := fun v => |unitLog K i v|) (fun v _ => abs_nonneg _)
      (Finset.mem_univ w)
  have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  have h4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  simp only [Finset.sum_neg_distrib] at h3
  linarith

end Bounds

section Periodic

variable {r : ℕ}

/-- If $G$ on $\mathbb{R}^r$ is periodic for $\mathbb{Z}^r$, then $\int_{[0, 1)^r} G(-c) \, dc = \int_{[0, 1)^r} G(c) \, dc$. The reason is that $-[0, 1)^r$ is also a fundamental domain of $\mathbb{Z}^r$. -/
theorem setIntegral_comp_neg_of_periodic {G : (Fin r → ℝ) → ℝ}
    (hG : ∀ (c : Fin r → ℝ) (k : Fin r → ℤ), G (c + fun i => (k i : ℝ)) = G c) :
    ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), G (-c) =
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), G c := by
  rw [← ZSpan.fundamentalDomain_pi_basisFun]
  set b := Pi.basisFun ℝ (Fin r)
  have hD := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin r → ℝ))
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hneg := Measure.measurePreserving_neg (volume : Measure (Fin r → ℝ))
  have hN : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup
      (Neg.neg ⁻¹' ZSpan.fundamentalDomain b) volume :=
    hD.preimage_of_equiv hneg.quasiMeasurePreserving (e := Neg.neg) neg_bijective fun g x => by
      simp only [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg]
      abel
  have hper : ∀ (g : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (x : Fin r → ℝ),
      G (g +ᵥ x) = G x := by
    intro g x
    have hg : ∀ i, ∃ k : ℤ, (g : Fin r → ℝ) i = k := by
      intro i
      obtain ⟨k, hk⟩ := (b.mem_span_iff_repr_mem ℤ (g : Fin r → ℝ)).1 g.2 i
      exact ⟨k, by simpa [b] using hk.symm⟩
    choose k hk using hg
    have : (g : Fin r → ℝ) = fun i => (k i : ℝ) := funext hk
    rw [AddSubgroup.vadd_def, vadd_eq_add, this, add_comm]
    exact hG x k
  calc ∫ c in ZSpan.fundamentalDomain b, G (-c)
      = ∫ c in Neg.neg ⁻¹' ZSpan.fundamentalDomain b, G c := by
        rw [← hneg.setIntegral_preimage_emb (MeasurableEquiv.neg _).measurableEmbedding]
        simp only [neg_neg]
    _ = ∫ c in ZSpan.fundamentalDomain b, G c := hN.setIntegral_eq hD hper

end Periodic

section UnitTheta

variable {K}

/-- The cube $[0, 1)^r$ has volume $1$. -/
theorem volume_real_unitCube :
    (volume : Measure (Fin (rank K) → ℝ)).real (Set.pi univ fun _ => Ico (0 : ℝ) 1) = 1 := by
  simp [Measure.real, Real.volume_pi_Ico]

theorem volume_unitCube_ne_top :
    (volume : Measure (Fin (rank K) → ℝ)) (Set.pi univ fun _ => Ico (0 : ℝ) 1) ≠ ⊤ := by
  simp [Real.volume_pi_Ico]

theorem measurableSet_unitCube :
    MeasurableSet (Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem mem_Icc_of_mem_unitCube {c : Fin (rank K) → ℝ}
    (hc : c ∈ Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) (i : Fin (rank K)) :
    c i ∈ Icc (0 : ℝ) 1 :=
  Ico_subset_Icc_self (hc i (mem_univ i))

variable (K) in
/-- The theta function of $\mathfrak{a}$ averaged over the units: $$\Theta_{\mathfrak{a}}(y) = \int_{[0, 1)^r} \theta_{\mathfrak{a}}(t(y, c)) \, dc.$$ -/
noncomputable def unitTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : ℝ) : ℝ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), dedekindTheta K a (unitScale K y c)

theorem integrableOn_dedekindTheta_unitScale (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ}
    (hy : 0 < y) :
    IntegrableOn (fun c => dedekindTheta K a (unitScale K y c))
      (Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) :=
  ((continuous_dedekindTheta_unitScale a hy).continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Ico_subset_Icc_self)

/-- The bounds $1 \le \Theta_{\mathfrak{a}}(y) \le \theta_{\Lambda(\mathfrak{a})}(y m)$ for $y > 0$. -/
theorem one_le_unitTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y) :
    1 ≤ unitTheta K a y ∧ unitTheta K a y ≤ latticeTheta (traceLattice K a) (y * unitBound K) := by
  have hm : 0 < y * unitBound K := mul_pos hy unitBound_pos
  constructor
  · calc (1 : ℝ) = ∫ _ in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), (1 : ℝ) := by
          rw [setIntegral_const, volume_real_unitCube, one_smul]
      _ ≤ unitTheta K a y :=
          setIntegral_mono_on (integrableOn_const volume_unitCube_ne_top) (integrableOn_dedekindTheta_unitScale a hy)
            measurableSet_unitCube fun c _ => one_le_dedekindTheta a (unitScale_pos hy c)
  · calc unitTheta K a y
        ≤ ∫ _ in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
            latticeTheta (traceLattice K a) (y * unitBound K) :=
          setIntegral_mono_on (integrableOn_dedekindTheta_unitScale a hy) (integrableOn_const volume_unitCube_ne_top)
            measurableSet_unitCube fun c hc => by
              rw [← dedekindTheta_const]
              exact dedekindTheta_anti a (fun _ => hm)
                (mul_unitBound_le hy.le (mem_Icc_of_mem_unitCube hc))
      _ = latticeTheta (traceLattice K a) (y * unitBound K) := by
          rw [setIntegral_const, volume_real_unitCube, one_smul]

/-- The function $\Theta_{\mathfrak{a}}$ is continuous on $(0, \infty)$, by dominated convergence. -/
theorem continuousOn_unitTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (unitTheta K a) (Ioi 0) := by
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  have hh := half_pos hy₀'
  refine ContinuousAt.continuousWithinAt ?_
  show ContinuousAt (fun y => ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    dedekindTheta K a (unitScale K y c)) y₀
  refine continuousAt_of_dominated
    (bound := fun _ => latticeTheta (traceLattice K a) (y₀ / 2 * unitBound K)) ?_ ?_ ?_ ?_
  · filter_upwards [Ioi_mem_nhds (half_lt_self hy₀')] with y hy
    exact (continuous_dedekindTheta_unitScale a (hh.trans hy)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (half_lt_self hy₀')] with y hy
    have hy' : 0 < y := hh.trans hy
    refine (ae_restrict_iff' measurableSet_unitCube).2 (Eventually.of_forall fun c hc => ?_)
    rw [Real.norm_of_nonneg (zero_le_one.trans (one_le_dedekindTheta a (unitScale_pos hy' c))),
      ← dedekindTheta_const]
    refine dedekindTheta_anti a (fun _ => mul_pos hh unitBound_pos) fun w => ?_
    exact (mul_le_mul_of_nonneg_right (le_of_lt hy) unitBound_pos.le).trans
      (mul_unitBound_le hy'.le (mem_Icc_of_mem_unitCube hc) w)
  · exact integrableOn_const volume_unitCube_ne_top
  · exact Eventually.of_forall fun c =>
      ContinuousAt.comp (f := fun y => unitScale K y c)
        (continuousAt_dedekindTheta a (unitScale_pos hy₀' c))
        (continuous_unitScale_left c).continuousAt

theorem locallyIntegrableOn_unitTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LocallyIntegrableOn (fun y => (unitTheta K a y : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_unitTheta a)).locallyIntegrableOn
    measurableSet_Ioi

/-- The function $\Theta_{\mathfrak{a}} - 1$ is $O(y^s)$ at infinity for each $s$, because it is at most $\theta_{\Lambda(\mathfrak{a})}(y m) - 1$. -/
theorem isBigO_unitTheta_sub_one (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ) :
    (fun y => (unitTheta K a y : ℂ) - 1) =O[atTop] (· ^ s) := by
  have hm := unitBound_pos (K := K)
  have h1 := (isBigO_latticeTheta_sub_one (traceLattice K a) s).comp_tendsto
    (tendsto_id.atTop_mul_const hm)
  have h2 : (fun y : ℝ => (id y * unitBound K) ^ s) =O[atTop] (· ^ s) := by
    refine IsBigO.of_bound (unitBound K ^ s) ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    rw [id, Real.mul_rpow hy hm.le, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), mul_comm]
  refine IsBigO.trans ?_ (h1.trans h2)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  obtain ⟨h0, hle⟩ := one_le_unitTheta a hy
  have e1 : (unitTheta K a y : ℂ) - 1 = ((unitTheta K a y - 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (latticeTheta (traceLattice K a) (y * unitBound K) : ℂ) - 1 =
      ((latticeTheta (traceLattice K a) (y * unitBound K) - 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [Function.comp_apply, id]
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
    Real.norm_of_nonneg (by linarith), one_mul]
  linarith

/-- The theta formula at $t(y^{-1}, c)$: $$\theta_{\mathfrak{a}}(t(y^{-1}, c)) = \frac{\sqrt{y}^{\,n}}{N(\mathfrak{a}) \sqrt{|d_K|}} \, \theta_{\mathfrak{a}^\vee}(t(y, -c)).$$ -/
theorem dedekindTheta_unitScale_inv (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y)
    (c : Fin (rank K) → ℝ) :
    dedekindTheta K a (unitScale K y⁻¹ c) =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|)⁻¹ *
        √y ^ finrank ℚ K * dedekindTheta K (dualUnit K a) (unitScale K y (-c)) := by
  have h : (fun w => (unitScale K y⁻¹ c w)⁻¹) = unitScale K y (-c) :=
    funext fun w => by rw [unitScale_inv, inv_inv]
  rw [dedekindTheta_dual a (unitScale_pos (inv_pos.2 hy) c), prod_sqrt_unitScale (inv_pos.2 hy).le,
    Real.sqrt_inv, inv_pow, mul_inv, inv_inv, h]
  rfl

/-- The transformation formula of $\Theta_{\mathfrak{a}}$: for $y > 0$, $$\Theta_{\mathfrak{a}}(1/y) = \frac{\sqrt{y}^{\,n}}{N(\mathfrak{a}) \sqrt{|d_K|}} \, \Theta_{\mathfrak{a}^\vee}(y).$$ -/
theorem unitTheta_inv (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 < y) :
    unitTheta K a y⁻¹ =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|)⁻¹ *
        √y ^ finrank ℚ K * unitTheta K (dualUnit K a) y := by
  rw [unitTheta, unitTheta]
  simp_rw [dedekindTheta_unitScale_inv a hy]
  rw [integral_const_mul]
  exact congrArg (HMul.hMul _) (setIntegral_comp_neg_of_periodic
    (G := fun c => dedekindTheta K (dualUnit K a) (unitScale K y c))
    fun c k => dedekindTheta_unitScale_add_int _ y c k)

/-- The pair $(\Theta_{\mathfrak{a}}, \Theta_{\mathfrak{a}^\vee})$ as a `WeakFEPair`, with weight $n/2$, root number $(N(\mathfrak{a}) \sqrt{|d_K|})^{-1}$ and constant terms $1$. -/
noncomputable def unitThetaFEPair (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : WeakFEPair ℂ where
  f y := (unitTheta K a y : ℂ)
  g y := (unitTheta K (dualUnit K a) y : ℂ)
  k := finrank ℚ K / 2
  ε := (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
    √|(discr K : ℝ)|)⁻¹ : ℝ)
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_unitTheta a
  hg_int := locallyIntegrableOn_unitTheta (dualUnit K a)
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := Complex.ofReal_ne_zero.2
    (inv_ne_zero (mul_pos (absNorm_pos K a) (sqrt_abs_discr_pos K)).ne')
  h_feq x hx := by
    have hx' : (0 : ℝ) < x := hx
    have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
      congr 1
      ring
    rw [one_div, unitTheta_inv a hx', smul_eq_mul, ← hk]
    push_cast
    ring
  hf_top := isBigO_unitTheta_sub_one a
  hg_top := isBigO_unitTheta_sub_one (dualUnit K a)

end UnitTheta

end Langlands.Tate
