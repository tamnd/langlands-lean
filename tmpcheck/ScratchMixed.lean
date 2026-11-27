import Langlands.Tate.GlobalLattice
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory Module Complex FourierTransform
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace

namespace Langlands.Tate.ScratchMixed

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The Fourier integral on $\mathbb{R}$ with the character written as a product. -/
theorem integral_exp_mul_smul_real (h : ℝ → ℂ) (s : ℝ) :
    ∫ r : ℝ, cexp (↑(-2 * Real.pi * r * s) * I) • h r = 𝓕 h s := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [RCLike.inner_apply, conj_trivial, mul_assoc, mul_comm s r]

/-- The Fourier integral on $\mathbb{C}$, written with the real inner product. -/
theorem integral_exp_inner_smul_complex (h : ℂ → ℂ) (s : ℂ) :
    ∫ z : ℂ, cexp (↑(-2 * Real.pi * ⟪z, s⟫) * I) • h z = 𝓕 h s :=
  (Real.fourier_eq' h s).symm

set_option maxHeartbeats 400000 in
theorem v_new (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
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
  simp only [integral_exp_mul_smul_real, integral_exp_inner_smul_complex]


section Irr
set_option allowUnsafeReducibility true in
attribute [local irreducible] stdOrthonormalBasis Module.Basis.addHaar
set_option maxHeartbeats 400000 in
theorem v_irr (f : {w : InfinitePlace K // IsReal w} → ℝ → ℂ)
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

end Irr

end Langlands.Tate.ScratchMixed
