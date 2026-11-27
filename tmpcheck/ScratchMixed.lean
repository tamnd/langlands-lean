import Langlands.Tate.GlobalLattice
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory Module Complex FourierTransform
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace

namespace Langlands.Tate.ScratchMixed

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

set_option maxHeartbeats 400000 in
theorem v_stmt (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  sorry

set_option maxHeartbeats 400000 in
theorem v_A (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_B (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_C (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_D (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_E (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_F (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_G (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  simp only [Real.fourier_eq']
  all_goals sorry

set_option maxHeartbeats 400000 in
theorem v_H (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  simp only [Real.fourier_eq']
  congr 1
  all_goals sorry

set_option maxHeartbeats 400000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 200 in
theorem v_full (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  set ξ' := euclidean.toMixed K ξ
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by simp [ξ']
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  simp only [Real.fourier_eq']
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 1 with r
  rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp only [RCLike.re_to_real, mul_assoc, mul_comm r]

set_option maxHeartbeats 400000 in
theorem v_noset (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
    (g : {w : InfinitePlace K // IsComplex w} → ℂ → ℂ) (ξ : euclidean.mixedSpace K) :
    𝓕 (fun x => (∏ v, f v ((euclidean.toMixed K x).1 v)) *
      ∏ w, g w ((euclidean.toMixed K x).2 w)) ξ =
    (∏ v, 𝓕 (f v) ((euclidean.toMixed K ξ).1 v)) * ∏ w, 𝓕 (g w) ((euclidean.toMixed K ξ).2 w) := by
  rw [Real.fourier_eq', ← (euclidean.volumePreserving_toMixed_symm K).integral_comp
    (euclidean.toMixed K).symm.toHomeomorph.measurableEmbedding]
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', euclidean.toMixed K ξ = ξ' := ⟨_, rfl⟩
  rw [hξ']
  have hξ : ξ = (euclidean.toMixed K).symm ξ' := by rw [← hξ']; simp
  have e : ∀ y : mixedSpace K,
      cexp (↑(-2 * Real.pi * ⟪(euclidean.toMixed K).symm y, ξ⟫) * I) •
        ((∏ v, f v ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).1 v)) *
          ∏ w, g w ((euclidean.toMixed K ((euclidean.toMixed K).symm y)).2 w)) =
      (∏ v, cexp (↑(-2 * Real.pi * y.1 v * ξ'.1 v) * I) • f v (y.1 v)) *
        ∏ w, cexp (↑(-2 * Real.pi * ⟪y.2 w, ξ'.2 w⟫) * I) • g w (y.2 w) := fun y => by
    rw [hξ, inner_toMixed_symm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [smul_eq_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_mul]
    simp only [mul_assoc]
    ring
  simp only [e]
  rw [show (volume : Measure (mixedSpace K)) = volume.prod volume from
    MeasureTheory.Measure.volume_eq_prod _ _]
  rw [integral_prod_mul (fun a : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, cexp (↑(-2 * Real.pi * a v * ξ'.1 v) * I) • f v (a v))
    (fun b : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ w, cexp (↑(-2 * Real.pi * ⟪b w, ξ'.2 w⟫) * I) • g w (b w)),
    integral_fintype_prod_volume_eq_prod
      (fun v (r : ℝ) => cexp (↑(-2 * Real.pi * r * ξ'.1 v) * I) • f v r),
    integral_fintype_prod_volume_eq_prod
      (fun w (z : ℂ) => cexp (↑(-2 * Real.pi * ⟪z, ξ'.2 w⟫) * I) • g w z)]
  simp only [Real.fourier_eq']
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 1 with r
  rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp only [RCLike.re_to_real, mul_assoc, mul_comm r]

end Langlands.Tate.ScratchMixed
