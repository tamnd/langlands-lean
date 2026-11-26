/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.EpsteinZeta

/-!
# The trace form zeta function of a fractional ideal

Let $K$ be a number field of degree $n$ and let $\mathfrak{a}$ be a nonzero fractional ideal of $K$. For $\alpha \in K$ put $\|\alpha\|^2 = \sum_w n_w |\alpha|_w^2$, where $w$ runs over the infinite places of $K$ and $n_w$ is $1$ at a real place and $2$ at a complex place. This is the quadratic form $\mathrm{Tr}_{K/\mathbb{Q}}(\alpha \bar\alpha)$ of the Minkowski embedding. The function $$Z_{\mathfrak{a}}(s) = \sum_{\alpha \in \mathfrak{a}, \, \alpha \neq 0} \|\alpha\|^{-s}$$ is the Epstein zeta function of the lattice $\mathfrak{a}$ for this form. This file proves that the completed function $\Lambda_{\mathfrak{a}}(s) = \Gamma_\mathbb{R}(s) Z_{\mathfrak{a}}(s)$ has a meromorphic continuation with poles at most at $s = 0$ and $s = n$, and that $$\Lambda_{\mathfrak{a}}(n - s) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|}} \, \Lambda_{\mathfrak{a}^\vee}(s),$$ where $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$ is the dual of $\mathfrak{a}$ for the trace form.

When $K$ has only one infinite place, that is $K = \mathbb{Q}$ or $K$ imaginary quadratic, $\|\alpha\|^2$ is a constant multiple of a power of $|N(\alpha)|$. Then $Z_{\mathfrak{a}}$ is a multiple of a partial Dedekind zeta function, and the result gives the functional equation of the Dedekind zeta function.

## Main results

* `Langlands.Tate.completedIdealZeta_eq`: $\Lambda_{\mathfrak{a}}(s) = \Gamma_\mathbb{R}(s) Z_{\mathfrak{a}}(s)$ for $\mathrm{Re}\, s > n$.
* `Langlands.Tate.differentiableAt_completedIdealZeta`: $\Lambda_{\mathfrak{a}}$ is holomorphic outside $\{0, n\}$.
* `Langlands.Tate.completedIdealZeta_sub`: the functional equation above.
* `Langlands.Tate.completedIdealZeta_residue`: $(s - n) \Lambda_{\mathfrak{a}}(s) \to 2 (N(\mathfrak{a}) \sqrt{|d_K|})^{-1}$ as $s \to n$.
* `Langlands.Tate.completedEpsteinZeta_congr`: two lattices with the same theta function and the same covolume have the same completed Epstein zeta function.

## Proof

The function $\Lambda_{\mathfrak{a}}$ is the completed Epstein zeta function of the lattice $\Lambda_c(\mathfrak{a})$ of `Langlands.Tate.globalLattice`, with $c_w = \sqrt{n_w}$. Its covolume is $N(\mathfrak{a}) \sqrt{|d_K|}$. By `Langlands.Tate.mem_dualLattice_globalLattice`, the dual lattice is the image of $\mathfrak{a}^\vee$ under the conjugate embedding. This is not the lattice $\Lambda_c(\mathfrak{a}^\vee)$, but the two lattices have the same norms, so they have the same theta function. They also have the same covolume, because $N(\mathfrak{d}) = |d_K|$. The completed Epstein zeta function depends only on the theta function and the covolume. So the functional equation of `Langlands.Tate.completedEpsteinZeta_sub` for $\Lambda_c(\mathfrak{a})$ is the functional equation above.
-/

open MeasureTheory Module Filter Topology NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding
open scoped RealInnerProductSpace nonZeroDivisors Classical

namespace Langlands.Tate

section Congr

/-- The function $\Lambda$ of a `WeakFEPair` depends only on $f$, $k$, $\varepsilon$, $f_0$ and $g_0$. The function $g$ is determined by $f$ through the functional equation. -/
theorem weakFEPair_Λ_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : WeakFEPair E) (hf : P.f = Q.f) (hk : P.k = Q.k) (hε : P.ε = Q.ε) (hf₀ : P.f₀ = Q.f₀)
    (hg₀ : P.g₀ = Q.g₀) : P.Λ = Q.Λ := by
  funext s
  simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, WeakFEPair.f_modif, hf, hk, hε, hf₀, hg₀]

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]

/-- Two lattices of the same rank with the same theta function and the same covolume have the same completed Epstein zeta function. -/
theorem completedEpsteinZeta_congr (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ W) [DiscreteTopology M] [IsZLattice ℝ M] (hn : finrank ℝ V = finrank ℝ W)
    (hθ : ∀ t, latticeTheta L t = latticeTheta M t)
    (hc : ZLattice.covolume L = ZLattice.covolume M) :
    completedEpsteinZeta L = completedEpsteinZeta M := by
  have h : (thetaFEPair L).Λ = (thetaFEPair M).Λ := by
    refine weakFEPair_Λ_eq _ _ ?_ ?_ ?_ rfl rfl
    · funext t
      simp only [thetaFEPair, hθ]
    · simp only [thetaFEPair, hn]
    · simp only [thetaFEPair, hc]
  funext s
  simp only [completedEpsteinZeta, h]

end Congr

variable (K : Type*) [Field K] [NumberField K]

/-- The scaling constants $c_w = \sqrt{n_w}$. With them $|\varphi_c(\alpha)|^2 = \sum_w n_w |\alpha|_w^2$. -/
noncomputable abbrev traceScale : InfinitePlace K → ℝˣ :=
  thetaScale (K := K) (t := fun _ => 1) fun _ => one_pos

/-- The lattice $\Lambda_c(\mathfrak{a})$ of a nonzero fractional ideal for $c_w = \sqrt{n_w}$. -/
noncomputable abbrev traceLattice (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  globalLattice K (traceScale K) a

/-- The dual $\mathfrak{a}^\vee$ of a nonzero fractional ideal for the trace form, as a unit of the group of fractional ideals. -/
noncomputable def dualUnit (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ a.ne_zero)

/-- The fractional ideal of `Langlands.Tate.dualUnit` is the dual for the trace form. -/
@[simp]
theorem coe_dualUnit (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((dualUnit K a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K) := rfl

/-- The dual ideal is $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$. -/
theorem coe_dualUnit_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((dualUnit K a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ((a : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_dualUnit, dual_eq_inv_mul_different]

/-- The norm of the dual ideal is $N(\mathfrak{a}^\vee) = (N(\mathfrak{a}) \, |d_K|)^{-1}$, because $N(\mathfrak{d}) = |d_K|$. -/
theorem absNorm_dualUnit (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal.absNorm
        ((dualUnit K a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * |(discr K : ℝ)|)⁻¹ := by
  rw [coe_dualUnit_eq, map_inv₀, map_mul, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal K]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- For $c_w = \sqrt{n_w}$, $|\varphi_c(x)|^2 = \sum_w n_w |x|_w^2$. -/
theorem norm_globalEmbedding_traceScale_sq (x : K) :
    ‖globalEmbedding K (fun w => (traceScale K w : ℝ)) x‖ ^ 2 = ∑ w, (mult w : ℝ) * w x ^ 2 := by
  rw [norm_globalEmbedding_thetaScale_sq]
  simp only [mul_one]

/-- For $c_w = \sqrt{n_w}$, $|\psi_c(x)|^2 = \sum_w n_w |x|_w^2$. -/
theorem norm_globalConjEmbedding_traceScale_sq (x : K) :
    ‖globalConjEmbedding K (fun w => (traceScale K w : ℝ)) x‖ ^ 2 =
      ∑ w, (mult w : ℝ) * w x ^ 2 := by
  rw [norm_globalConjEmbedding_thetaScale_sq]
  simp only [mul_one]

omit [NumberField K] in
/-- The constants $c_w = \sqrt{n_w}$ satisfy $c_w c_w = n_w$. -/
theorem traceScale_mul_traceScale (w : InfinitePlace K) :
    (traceScale K w : ℝ) * traceScale K w = mult w := by
  rw [← sq, thetaScale_sq, mul_one]

/-- The covolume of the lattice of $\mathfrak{a}$ is $N(\mathfrak{a}) \sqrt{|d_K|}$. -/
theorem covolume_traceLattice (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceLattice K a) =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)| := by
  rw [traceLattice, covolume_globalLattice_thetaScale]
  simp only [Real.sqrt_one, one_pow, Finset.prod_const_one, mul_one]

/-- A sum over the norms of a lattice in the form $\sum_{\ell} F(|\ell|^2)$ is the sum over $\alpha \in \mathfrak{a}$ of $F(\sum_w n_w |\alpha|_w^2)$. -/
theorem tsum_traceLattice {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : ℝ → β) :
    ∑' ℓ : traceLattice K a, F (‖(ℓ : euclidean.mixedSpace K)‖ ^ 2) =
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), F (∑ w, (mult w : ℝ) * w (α : K) ^ 2) := by
  rw [← (globalLatticeEquiv K (traceScale K) a).tsum_eq]
  simp_rw [coe_globalLatticeEquiv, norm_globalEmbedding_traceScale_sq]
  rfl

/-- The same as `Langlands.Tate.tsum_traceLattice` for the dual lattice and the dual ideal. -/
theorem tsum_dualLattice_traceLattice {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : ℝ → β) :
    ∑' ℓ : dualLattice (traceLattice K a), F (‖(ℓ : euclidean.mixedSpace K)‖ ^ 2) =
      ∑' β : FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K),
        F (∑ w, (mult w : ℝ) * w (β : K) ^ 2) := by
  rw [← (globalDualEquiv K (traceScale K) a (traceScale K)
    (traceScale_mul_traceScale K)).tsum_eq]
  simp_rw [coe_globalDualEquiv, norm_globalConjEmbedding_traceScale_sq]
  rfl

/-- The dual lattice of the lattice of $\mathfrak{a}$ and the lattice of $\mathfrak{a}^\vee$ have the same theta function. -/
theorem latticeTheta_dualLattice_traceLattice (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    latticeTheta (dualLattice (traceLattice K a)) t = latticeTheta (traceLattice K (dualUnit K a)) t := by
  rw [latticeTheta, latticeTheta,
    tsum_dualLattice_traceLattice K a fun r => Real.exp (-(Real.pi * t) * r),
    tsum_traceLattice K (dualUnit K a) fun r => Real.exp (-(Real.pi * t) * r)]
  rfl

/-- The dual lattice of the lattice of $\mathfrak{a}$ and the lattice of $\mathfrak{a}^\vee$ have the same covolume $(N(\mathfrak{a}) \sqrt{|d_K|})^{-1}$. -/
theorem covolume_dualLattice_traceLattice (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (dualLattice (traceLattice K a)) =
      ZLattice.covolume (traceLattice K (dualUnit K a)) := by
  rw [covolume_dualLattice, covolume_traceLattice, covolume_traceLattice, absNorm_dualUnit]
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hs : √|(discr K : ℝ)| ^ 2 = |(discr K : ℝ)| := Real.sq_sqrt hd.le
  field_simp
  exact hs.symm

/-- The trace form zeta function of a nonzero fractional ideal, completed with the factor $\Gamma_\mathbb{R}(s)$: $$\Lambda_{\mathfrak{a}}(s) = \Gamma_\mathbb{R}(s) \sum_{\alpha \in \mathfrak{a}, \, \alpha \neq 0} \Big(\sum_w n_w |\alpha|_w^2\Big)^{-s/2}$$ for $\mathrm{Re}\, s > n$. It is the completed Epstein zeta function of the lattice of $\mathfrak{a}$. -/
noncomputable def completedIdealZeta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  completedEpsteinZeta (traceLattice K a) s

/-- The dimension of the euclidean mixed space is $n = [K : \mathbb{Q}]$. -/
theorem finrank_euclidean_mixedSpace : finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K :=
  euclidean.finrank K

/-- For $\mathrm{Re}\, s > n$, $$\Lambda_{\mathfrak{a}}(s) = \Gamma_\mathbb{R}(s) \sum_{\alpha \in \mathfrak{a}, \, \alpha \neq 0} \Big(\sum_w n_w |\alpha|_w^2\Big)^{-s/2}.$$ The power is written as $\big(\sqrt{\sum_w n_w |\alpha|_w^2}\big)^{-s}$. -/
theorem completedIdealZeta_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : (finrank ℚ K : ℝ) < s.re) :
    completedIdealZeta K a s = Complex.Gammaℝ s *
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), if (α : K) = 0 then 0 else
        ((√(∑ w, (mult w : ℝ) * w (α : K) ^ 2) : ℝ) : ℂ) ^ (-s) := by
  rw [← finrank_euclidean_mixedSpace] at hs
  rw [completedIdealZeta, completedEpsteinZeta_eq _ hs, epsteinZeta,
    ← (globalLatticeEquiv K (traceScale K) a).tsum_eq]
  congr 1
  refine tsum_congr fun α => ?_
  have h0 : globalLatticeEquiv K (traceScale K) a α = 0 ↔ (α : K) = 0 := by
    rw [Subtype.ext_iff, coe_globalLatticeEquiv, ZeroMemClass.coe_zero]
    constructor
    · intro h
      exact globalEmbedding_injective K (traceScale K) (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  simp only [h0]
  split_ifs
  · rfl
  · rw [coe_globalLatticeEquiv, ← norm_globalEmbedding_traceScale_sq,
      Real.sqrt_sq (norm_nonneg _)]

/-- The completed function $\Lambda_{\mathfrak{a}}$ is holomorphic on $\mathbb{C} \setminus \{0, n\}$. -/
theorem differentiableAt_completedIdealZeta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : s ≠ 0) (hs' : s ≠ finrank ℚ K) :
    DifferentiableAt ℂ (completedIdealZeta K a) s := by
  rw [← finrank_euclidean_mixedSpace] at hs'
  exact differentiableAt_completedEpsteinZeta _ hs hs'

/-- **The functional equation of the trace form zeta function.** For a nonzero fractional ideal $\mathfrak{a}$ of $K$, $$\Lambda_{\mathfrak{a}}(n - s) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|}} \, \Lambda_{\mathfrak{a}^\vee}(s),$$ where $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$ is the dual of $\mathfrak{a}$ for the trace form. -/
theorem completedIdealZeta_sub (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedIdealZeta K a (finrank ℚ K - s) =
      (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          √|(discr K : ℝ)|)⁻¹ : ℝ) * completedIdealZeta K (dualUnit K a) s := by
  rw [completedIdealZeta, ← finrank_euclidean_mixedSpace, completedEpsteinZeta_sub,
    covolume_traceLattice, completedIdealZeta,
    completedEpsteinZeta_congr _ _ rfl (latticeTheta_dualLattice_traceLattice K a)
      (covolume_dualLattice_traceLattice K a)]

/-- The residue at $s = n$: $(s - n) \Lambda_{\mathfrak{a}}(s) \to 2 \, (N(\mathfrak{a}) \sqrt{|d_K|})^{-1}$ as $s \to n$. -/
theorem completedIdealZeta_residue (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ => (s - finrank ℚ K) * completedIdealZeta K a s)
      (𝓝[≠] (finrank ℚ K : ℂ))
      (𝓝 (2 * (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          √|(discr K : ℝ)|)⁻¹ : ℝ))) := by
  have h := completedEpsteinZeta_residue (traceLattice K a)
  rw [finrank_euclidean_mixedSpace, covolume_traceLattice] at h
  exact h

end Langlands.Tate
