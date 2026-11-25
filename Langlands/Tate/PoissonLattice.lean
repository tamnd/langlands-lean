/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.PoissonSummation
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Poisson summation on a lattice

Let $V$ be a finite dimensional real inner product space and let $L \subset V$ be a full lattice, that is a discrete subgroup that spans $V$ (`IsZLattice ℝ L`). This file proves the Poisson summation formula $$\sum_{\ell \in L} f(\ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu)$$ and its versions with a shift and a twist.

## Conventions

The covolume $\mathrm{covol}(L)$ is `ZLattice.covolume L`, the volume of a fundamental domain for the Lebesgue measure of $V$ (the Haar measure with volume one on an orthonormal cube). The dual lattice is $L^\vee = \{\mu \in V : \langle \mu, \ell \rangle \in \mathbb{Z} \text{ for all } \ell \in L\}$ (`Langlands.Tate.dualLattice`). The Fourier transform is the Fourier transform $\mathcal{F}$ of Mathlib, $\mathcal{F} f(w) = \int_V f(v) e^{-2 \pi i \langle v, w \rangle} \, dv$, as in `Langlands.Tate.PoissonSummation`.

## Main results

* `Langlands.Tate.tsum_add_zlattice_eq_of_hasDecay`: let $f$ be continuous with $(1 + |v|)^N |f(v)| \le C$ for some $N > \dim V$ (`Langlands.Tate.HasDecay`), and let $\sum_{\mu \in L^\vee} \mathcal{F} f(\mu)$ converge. Then $$\sum_{\ell \in L} f(x + \ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu) e^{2 \pi i \langle x, \mu \rangle}.$$
* `Langlands.Tate.tsum_zlattice_eq_of_hasDecay`: the case $x = 0$.
* `SchwartzMap.tsum_add_zlattice_mul_eq`: for a Schwartz function $f$ and $x, y \in V$, $$\sum_{\ell \in L} f(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle} = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu - y) e^{2 \pi i \langle x, \mu \rangle}.$$
* `SchwartzMap.tsum_add_zlattice_eq` and `SchwartzMap.tsum_zlattice_eq`: the cases $y = 0$ and $x = y = 0$.
* `Langlands.Tate.summable_dualLattice_of_hasDecay`: a function with decay of order $N > \dim V$ is summable on $L^\vee$.

## Proof

Choose a basis $b$ of $L$ and let $A : \mathbb{R}^n \to V$ be the linear map with $A e_i = b_i$ (`Langlands.Tate.latticeEquiv`). Then $A$ sends $\mathbb{Z}^n$ onto $L$, and the formula for $L$ follows from the formula for $\mathbb{Z}^n$ applied to $f \circ A$. Two facts are necessary.

1. The image of the Lebesgue measure under $A$ is $\mathrm{covol}(L)^{-1}$ times the Lebesgue measure of $V$ (`Langlands.Tate.map_latticeEquiv_volume`). Both measures are Haar measures, so they differ by a constant. We find the constant on the fundamental domain of $b$, which is the image of the unit cube.
2. Let $D = (A^{-1})^*$ be the adjoint of $A^{-1}$ (`Langlands.Tate.dualMap`). Then $\langle A w, D z \rangle = \langle w, z \rangle$, so $D$ sends $\mathbb{Z}^n$ onto $L^\vee$ (`Langlands.Tate.dualIndexEquiv`). The vectors $D e_i$ form the dual basis of $b$.

With these facts, a change of variables gives $\mathcal{F}(f \circ A)(k) = \mathrm{covol}(L)^{-1} \mathcal{F} f(D k)$ (`Langlands.Tate.fourier_comp_latticeEquiv`). Then the sum over $k \in \mathbb{Z}^n$ is the sum over $\mu = D k \in L^\vee$.

## References

* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.2.
* J. Neukirch, Algebraic number theory, chapter VII, section 8.
-/

open MeasureTheory Set Complex FourierTransform Module
open scoped RealInnerProductSpace SchwartzMap

namespace Langlands.Tate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (L : Submodule ℤ V)

/-- The dual lattice $L^\vee = \{x \in V : \langle x, \ell \rangle \in \mathbb{Z} \text{ for all } \ell \in L\}$ of $L$ for the inner product of $V$. It is `LinearMap.BilinForm.dualSubmodule` for the bilinear form `innerₗ V`. -/
noncomputable def dualLattice : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L

/-- A vector $x$ is in $L^\vee$ if and only if $\langle x, \ell \rangle \in \mathbb{Z}$ for each $\ell \in L$. -/
theorem mem_dualLattice {x : V} : x ∈ dualLattice L ↔ ∀ y ∈ L, ∃ n : ℤ, ⟪x, y⟫ = n := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply]
  refine forall₂_congr fun y _ => ?_
  simp [eq_comm]

section Basis

variable [FiniteDimensional ℝ V] [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

/-- The linear isomorphism $A : \mathbb{R}^\iota \to V$ that sends the standard basis vector $e_i$ to the basis vector $b_i$ of $L$. It sends $\mathbb{Z}^\iota$ onto $L$. -/
noncomputable def latticeEquiv : EuclideanSpace ℝ ι ≃L[ℝ] V :=
  ((EuclideanSpace.basisFun ι ℝ).toBasis.equiv (b.ofZLatticeBasis ℝ L)
    (Equiv.refl ι)).toContinuousLinearEquiv

/-- The coordinates of $A x$ in the basis $b$ are the coordinates of $x$. -/
theorem repr_latticeEquiv (x : EuclideanSpace ℝ ι) (i : ι) :
    (b.ofZLatticeBasis ℝ L).repr (latticeEquiv L b x) i = x i := by
  simp [latticeEquiv, Basis.equiv]

/-- $A x = \sum_i x_i b_i$. -/
theorem latticeEquiv_apply (x : EuclideanSpace ℝ ι) :
    latticeEquiv L b x = ∑ i, x i • (b i : V) := by
  rw [← (b.ofZLatticeBasis ℝ L).sum_repr (latticeEquiv L b x)]
  simp [repr_latticeEquiv]

/-- The coordinates of $A^{-1} y$ are the coordinates of $y$ in the basis $b$. -/
theorem latticeEquiv_symm_apply (y : V) (i : ι) :
    (latticeEquiv L b).symm y i = (b.ofZLatticeBasis ℝ L).repr y i := by
  conv_rhs => rw [← (latticeEquiv L b).apply_symm_apply y]
  rw [repr_latticeEquiv]

/-- For $m \in \mathbb{Z}^\iota$, $A m$ is the lattice vector $\sum_i m_i b_i$. -/
theorem latticeEquiv_intPoint (m : ι → ℤ) :
    latticeEquiv L b (intPoint m) = ((b.equivFun.symm m : L) : V) := by
  rw [latticeEquiv_apply, Basis.equivFun_symm_apply]
  simp [Int.cast_smul_eq_zsmul]

include b in
/-- The dimension of $V$ is the rank of $L$. -/
theorem finrank_eq_card : finrank ℝ V = Fintype.card ι :=
  Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ L)

/-- $|z| \le \|A^{-1}\| \, |A z|$. -/
theorem norm_le_latticeEquiv (z : EuclideanSpace ℝ ι) :
    ‖z‖ ≤ ‖((latticeEquiv L b).symm : V →L[ℝ] EuclideanSpace ℝ ι)‖ * ‖latticeEquiv L b z‖ := by
  simpa using ((latticeEquiv L b).symm : V →L[ℝ] EuclideanSpace ℝ ι).le_opNorm (latticeEquiv L b z)

/-- The unit cube $[0, 1)^\iota$ has volume one. -/
theorem volume_unitCube : volume {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Ico (0 : ℝ) 1} = 1 := by
  have h : {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Ico (0 : ℝ) 1} =
      WithLp.ofLp ⁻¹' Set.pi univ fun _ => Ico (0 : ℝ) 1 := by
    ext x; simp
  rw [h, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp

/-- The map $A$ sends the unit cube $[0, 1)^\iota$ onto the fundamental domain of $L$ for the basis $b$. -/
theorem preimage_latticeEquiv_fundamentalDomain :
    latticeEquiv L b ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) =
      {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, repr_latticeEquiv]

/-- For $k, m \in \mathbb{Z}^\iota$, $\langle k, m \rangle = \sum_i k_i m_i$ is an integer. -/
theorem inner_intPoint (k m : ι → ℤ) : ⟪intPoint k, intPoint m⟫ = ((∑ i, k i * m i : ℤ) : ℝ) := by
  simp [PiLp.inner_apply, mul_comm]

/-- The map $D = (A^{-1})^* : \mathbb{R}^\iota \to V$, the adjoint of $A^{-1}$. It is characterized by $\langle A w, D z \rangle = \langle w, z \rangle$. It sends $\mathbb{Z}^\iota$ onto the dual lattice $L^\vee$. -/
noncomputable def dualMap : EuclideanSpace ℝ ι →L[ℝ] V :=
  ContinuousLinearMap.adjoint ((latticeEquiv L b).symm : V →L[ℝ] EuclideanSpace ℝ ι)

/-- $\langle y, D z \rangle = \langle A^{-1} y, z \rangle$. -/
theorem inner_dualMap (y : V) (z : EuclideanSpace ℝ ι) :
    ⟪y, dualMap L b z⟫ = ⟪(latticeEquiv L b).symm y, z⟫ :=
  ContinuousLinearMap.adjoint_inner_right _ y z

/-- $\langle A w, D z \rangle = \langle w, z \rangle$. -/
theorem inner_latticeEquiv_dualMap (w z : EuclideanSpace ℝ ι) :
    ⟪latticeEquiv L b w, dualMap L b z⟫ = ⟪w, z⟫ := by
  rw [inner_dualMap, ContinuousLinearEquiv.symm_apply_apply]

/-- $D$ is a left inverse of the adjoint $A^*$ of $A$. -/
theorem dualMap_adjoint (y : V) :
    dualMap L b (ContinuousLinearMap.adjoint (latticeEquiv L b : EuclideanSpace ℝ ι →L[ℝ] V) y) =
      y := by
  refine ext_inner_left ℝ fun v => ?_
  rw [inner_dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

/-- $|z| \le \|A\| \, |D z|$. The proof uses $|z|^2 = \langle A z, D z \rangle$. -/
theorem norm_le_dualMap (z : EuclideanSpace ℝ ι) :
    ‖z‖ ≤ ‖(latticeEquiv L b : EuclideanSpace ℝ ι →L[ℝ] V)‖ * ‖dualMap L b z‖ := by
  have h := inner_latticeEquiv_dualMap L b z z
  rw [real_inner_self_eq_norm_sq] at h
  have h2 := real_inner_le_norm (latticeEquiv L b z) (dualMap L b z)
  have h3 := mul_le_mul_of_nonneg_right
    ((latticeEquiv L b : EuclideanSpace ℝ ι →L[ℝ] V).le_opNorm z) (norm_nonneg (dualMap L b z))
  have h4 : ‖z‖ * ‖z‖ ≤ ‖z‖ * (‖(latticeEquiv L b : EuclideanSpace ℝ ι →L[ℝ] V)‖ *
      ‖dualMap L b z‖) := by
    simp only [ContinuousLinearEquiv.coe_coe] at h3 ⊢
    nlinarith
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_left h4 h0

/-- Each $\mu \in V$ is the image under $D$ of the vector $(\langle \mu, b_i \rangle)_i$. -/
theorem dualMap_inner_basis (μ : V) :
    dualMap L b (WithLp.toLp 2 fun i => ⟪μ, (b i : V)⟫) = μ := by
  refine ext_inner_left ℝ fun v => ?_
  rw [inner_dualMap]
  conv_rhs => rw [← (b.ofZLatticeBasis ℝ L).sum_repr v]
  simp only [PiLp.inner_apply, latticeEquiv_symm_apply, RCLike.inner_apply, conj_trivial,
    real_inner_comm μ]
  rw [inner_sum]
  simp [real_inner_smul_right, mul_comm]

/-- The map $D$ is injective. -/
theorem dualMap_injective : Function.Injective (dualMap L b) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have := inner_latticeEquiv_dualMap L b z z
  rw [hz, inner_zero_right] at this
  exact inner_self_eq_zero.1 this.symm

/-- $D$ sends $\mathbb{Z}^\iota$ into the dual lattice $L^\vee$. -/
theorem dualMap_intPoint_mem (k : ι → ℤ) : dualMap L b (intPoint k) ∈ dualLattice L := by
  rw [mem_dualLattice]
  intro y hy
  obtain ⟨m, rfl⟩ : ∃ m, y = latticeEquiv L b (intPoint m) :=
    ⟨b.equivFun ⟨y, hy⟩, by rw [latticeEquiv_intPoint, LinearEquiv.symm_apply_apply]⟩
  refine ⟨∑ i, k i * m i, ?_⟩
  rw [real_inner_comm, inner_latticeEquiv_dualMap, inner_intPoint]
  simp [mul_comm]

/-- The bijection $\mathbb{Z}^\iota \to L$, $m \mapsto \sum_i m_i b_i$. -/
noncomputable def latticeIndexEquiv : (ι → ℤ) ≃ L := b.equivFun.symm.toEquiv

/-- The bijection $\mathbb{Z}^\iota \to L$ is the restriction of $A$. -/
theorem coe_latticeIndexEquiv (m : ι → ℤ) :
    (latticeIndexEquiv L b m : V) = latticeEquiv L b (intPoint m) := by
  rw [latticeEquiv_intPoint]; rfl

/-- The bijection $\mathbb{Z}^\iota \to L^\vee$, $k \mapsto D k$. Its inverse sends $\mu$ to $(\langle \mu, b_i \rangle)_i$. -/
noncomputable def dualIndexEquiv : (ι → ℤ) ≃ dualLattice L :=
  Equiv.ofBijective (fun k => ⟨dualMap L b (intPoint k), dualMap_intPoint_mem L b k⟩) (by
    refine ⟨fun k k' h => intPoint_injective (dualMap_injective L b (congrArg Subtype.val h)), ?_⟩
    rintro ⟨μ, hμ⟩
    have : ∀ i, ∃ n : ℤ, ⟪μ, (b i : V)⟫ = n := fun i =>
      (mem_dualLattice L).1 hμ _ (b i).2
    choose n hn using this
    refine ⟨n, Subtype.ext ?_⟩
    have h : intPoint n = WithLp.toLp 2 fun i => ⟪μ, (b i : V)⟫ := by
      ext i; simp [hn]
    simp only [h, dualMap_inner_basis])

/-- The bijection $\mathbb{Z}^\iota \to L^\vee$ is the restriction of $D$. -/
theorem coe_dualIndexEquiv (k : ι → ℤ) :
    (dualIndexEquiv L b k : V) = dualMap L b (intPoint k) := rfl

include b in
/-- A version of `summable_dualLattice_of_hasDecay` with a given basis of $L$. -/
theorem summable_dualLattice_of_hasDecay_aux {f : V → ℂ} {N : ℕ} (hf : HasDecay f N)
    (hN : finrank ℝ V < N) : Summable fun μ : dualLattice L => f μ := by
  rw [← (dualIndexEquiv L b).summable_iff]
  exact (hf.comp (dualMap L b) _ (norm_le_dualMap L b)).summable_intPoint
    (by rwa [← finrank_eq_card L b])

variable [MeasurableSpace V] [BorelSpace V]

/-- The image of Lebesgue measure under $A$ is $\mathrm{covol}(L)^{-1}$ times the Lebesgue measure of $V$. The proof compares two Haar measures on the fundamental domain. -/
theorem map_latticeEquiv_volume :
    Measure.map (latticeEquiv L b) volume =
      ENNReal.ofReal (ZLattice.covolume L)⁻¹ • (volume : Measure V) := by
  have : (Measure.map (latticeEquiv L b) volume).IsAddHaarMeasure :=
    (latticeEquiv L b).isAddHaarMeasure_map volume
  set c := Measure.addHaarScalarFactor (Measure.map (latticeEquiv L b) volume) volume
  have h1 := Measure.isAddLeftInvariant_eq_smul (Measure.map (latticeEquiv L b) volume) volume
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet _
  have h2 : Measure.map (latticeEquiv L b) volume F = 1 := by
    rw [Measure.map_apply (latticeEquiv L b).continuous.measurable hF,
      preimage_latticeEquiv_fundamentalDomain, volume_unitCube]
  have h3 : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume (ZLattice.isAddFundamentalDomain b volume)
  have h4 : (c : ℝ) * ZLattice.covolume L = 1 := by
    rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    rw [h3, measureReal_def, ← ENNReal.coe_toReal, ← ENNReal.toReal_mul, h2, ENNReal.toReal_one]
  have hc : (c : ℝ) = (ZLattice.covolume L)⁻¹ := eq_inv_of_mul_eq_one_left h4
  rw [h1, ← hc, ENNReal.ofReal_coe_nnreal]
  rfl

/-- Change of variables: $\int_{\mathbb{R}^\iota} h(A z) \, dz = \mathrm{covol}(L)^{-1} \int_V h(y) \, dy$. -/
theorem integral_comp_latticeEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : V → F) :
    ∫ z, h (latticeEquiv L b z) = (ZLattice.covolume L)⁻¹ • ∫ y, h y := by
  have := integral_map_equiv (latticeEquiv L b).toHomeomorph.toMeasurableEquiv
    (μ := (volume : Measure (EuclideanSpace ℝ ι))) h
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
  rw [← this, map_latticeEquiv_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (ZLattice.covolume_pos L volume).le)]

/-- The Fourier transform of $f \circ A$: $\mathcal{F}(f \circ A)(k) = \mathrm{covol}(L)^{-1} \mathcal{F} f(D k)$. -/
theorem fourier_comp_latticeEquiv (f : V → ℂ) (k : EuclideanSpace ℝ ι) :
    𝓕 (f ∘ latticeEquiv L b) k = ((ZLattice.covolume L)⁻¹ : ℝ) • 𝓕 f (dualMap L b k) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_comp_latticeEquiv L b]
  congr 1 with v
  rw [inner_latticeEquiv_dualMap, Function.comp_apply]

include b in
/-- A version of `SchwartzMap.tsum_add_zlattice_mul_eq` with a given basis of $L$. -/
theorem tsum_add_zlattice_mul_eq_aux (f : 𝓢(V, ℂ)) (x y : V) :
    ∑' ℓ : L, f (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫) =
      ((ZLattice.covolume L)⁻¹ : ℝ) *
        ∑' μ : dualLattice L, 𝓕 f (μ - y) * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) := by
  set A := latticeEquiv L b
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f
  have hg : ∀ z, g z = f (A z) := fun z => rfl
  have key := g.tsum_add_intPoint_mul_eq_tsum_fourier (A.symm x)
    (ContinuousLinearMap.adjoint (A : EuclideanSpace ℝ ι →L[ℝ] V) y)
  have hl : ∀ m : ι → ℤ, g (A.symm x + intPoint m) *
      cexp (2 * Real.pi * I * ⟪A.symm x + intPoint m,
        ContinuousLinearMap.adjoint (A : EuclideanSpace ℝ ι →L[ℝ] V) y⟫) =
      f (x + latticeIndexEquiv L b m) * cexp (2 * Real.pi * I * ⟪x + latticeIndexEquiv L b m, y⟫) := by
    intro m
    rw [hg, ContinuousLinearMap.adjoint_inner_right, coe_latticeIndexEquiv]
    simp [A]
  have hr : ∀ k : ι → ℤ, 𝓕 g (intPoint k - ContinuousLinearMap.adjoint
      (A : EuclideanSpace ℝ ι →L[ℝ] V) y) * cexp (2 * Real.pi * I * ⟪A.symm x, intPoint k⟫) =
      ((ZLattice.covolume L)⁻¹ : ℝ) * (𝓕 f (dualIndexEquiv L b k - y) *
        cexp (2 * Real.pi * I * ⟪x, (dualIndexEquiv L b k : V)⟫)) := by
    intro k
    rw [SchwartzMap.fourier_coe]
    have : (g : EuclideanSpace ℝ ι → ℂ) = f ∘ A := rfl
    rw [this, fourier_comp_latticeEquiv, map_sub, dualMap_adjoint, coe_dualIndexEquiv,
      ← inner_dualMap, Complex.real_smul, mul_assoc, SchwartzMap.fourier_coe]
  simp only [hl, hr] at key
  rw [tsum_mul_left] at key
  rw [← (latticeIndexEquiv L b).tsum_eq, key, (dualIndexEquiv L b).tsum_eq
    (fun μ : dualLattice L => 𝓕 f (μ - y) * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫))]

include b in
/-- A version of `tsum_add_zlattice_eq_of_hasDecay` with a given basis of $L$. -/
theorem tsum_add_zlattice_eq_of_hasDecay_aux {f : V → ℂ} {N : ℕ} (hc : Continuous f)
    (hf : HasDecay f N) (hN : finrank ℝ V < N)
    (hF : Summable fun μ : dualLattice L => 𝓕 f μ) (x : V) :
    ∑' ℓ : L, f (x + ℓ) = ((ZLattice.covolume L)⁻¹ : ℝ) *
      ∑' μ : dualLattice L, 𝓕 f μ * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) := by
  set A := latticeEquiv L b
  have hg : HasSummableTranslates (f ∘ A) :=
    (hf.comp A _ (norm_le_latticeEquiv L b)).hasSummableTranslates
      (by rwa [← finrank_eq_card L b])
  have hFg : ∀ k : ι → ℤ, 𝓕 (f ∘ A) (intPoint k) =
      ((ZLattice.covolume L)⁻¹ : ℝ) • 𝓕 f (dualIndexEquiv L b k) := fun k => by
    rw [fourier_comp_latticeEquiv, coe_dualIndexEquiv]
  have hS : Summable fun k : ι → ℤ => 𝓕 (f ∘ A) (intPoint k) := by
    simp only [hFg]
    exact ((dualIndexEquiv L b).summable_iff.2 hF).const_smul _
  have key := tsum_add_intPoint_eq_tsum_fourier (hc.comp A.continuous) hg hS (A.symm x)
  have hl : ∀ m : ι → ℤ, (f ∘ A) (A.symm x + intPoint m) = f (x + latticeIndexEquiv L b m) :=
    fun m => by
      rw [Function.comp_apply, map_add, ContinuousLinearEquiv.apply_symm_apply,
        coe_latticeIndexEquiv]
  have hr : ∀ k : ι → ℤ, 𝓕 (f ∘ A) (intPoint k) *
      cexp (2 * Real.pi * I * ⟪A.symm x, intPoint k⟫) =
      ((ZLattice.covolume L)⁻¹ : ℝ) * (𝓕 f (dualIndexEquiv L b k) *
        cexp (2 * Real.pi * I * ⟪x, (dualIndexEquiv L b k : V)⟫)) := fun k => by
    rw [hFg, coe_dualIndexEquiv, ← inner_dualMap, Complex.real_smul, mul_assoc]
  simp only [hl, hr] at key
  rw [tsum_mul_left] at key
  rw [← (latticeIndexEquiv L b).tsum_eq, key, (dualIndexEquiv L b).tsum_eq
    (fun μ : dualLattice L => 𝓕 f μ * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫))]

end Basis

section Main

variable [FiniteDimensional ℝ V] [DiscreteTopology L] [IsZLattice ℝ L]

/-- If $f$ decays of order $N > \dim V$, then $\sum_{\mu \in L^\vee} f(\mu)$ converges. -/
theorem summable_dualLattice_of_hasDecay {f : V → ℂ} {N : ℕ} (hf : HasDecay f N)
    (hN : finrank ℝ V < N) : Summable fun μ : dualLattice L => f μ :=
  summable_dualLattice_of_hasDecay_aux L (Module.Free.chooseBasis ℤ L) hf hN

variable [MeasurableSpace V] [BorelSpace V]

/-- **Poisson summation on a lattice.** Let $f$ be continuous on $V$ with decay of order $N > \dim V$, and let $\sum_{\mu \in L^\vee} \mathcal{F} f(\mu)$ converge. Then $$\sum_{\ell \in L} f(x + \ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu) e^{2 \pi i \langle x, \mu \rangle}.$$ -/
theorem tsum_add_zlattice_eq_of_hasDecay {f : V → ℂ} {N : ℕ} (hc : Continuous f)
    (hf : HasDecay f N) (hN : finrank ℝ V < N)
    (hF : Summable fun μ : dualLattice L => 𝓕 f μ) (x : V) :
    ∑' ℓ : L, f (x + ℓ) = ((ZLattice.covolume L)⁻¹ : ℝ) *
      ∑' μ : dualLattice L, 𝓕 f μ * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) :=
  tsum_add_zlattice_eq_of_hasDecay_aux L (Module.Free.chooseBasis ℤ L) hc hf hN hF x

/-- **Poisson summation on a lattice at $x = 0$.** Under the hypotheses of `tsum_add_zlattice_eq_of_hasDecay`, $$\sum_{\ell \in L} f(\ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu).$$ -/
theorem tsum_zlattice_eq_of_hasDecay {f : V → ℂ} {N : ℕ} (hc : Continuous f)
    (hf : HasDecay f N) (hN : finrank ℝ V < N)
    (hF : Summable fun μ : dualLattice L => 𝓕 f μ) :
    ∑' ℓ : L, f ℓ = ((ZLattice.covolume L)⁻¹ : ℝ) * ∑' μ : dualLattice L, 𝓕 f μ := by
  simpa using tsum_add_zlattice_eq_of_hasDecay L hc hf hN hF 0

/-- **Twisted Poisson summation on a lattice for Schwartz functions.** For $x, y \in V$, $$\sum_{\ell \in L} f(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle} = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu - y) e^{2 \pi i \langle x, \mu \rangle}.$$ -/
theorem _root_.SchwartzMap.tsum_add_zlattice_mul_eq (f : 𝓢(V, ℂ)) (x y : V) :
    ∑' ℓ : L, f (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫) =
      ((ZLattice.covolume L)⁻¹ : ℝ) *
        ∑' μ : dualLattice L, 𝓕 f (μ - y) * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) :=
  tsum_add_zlattice_mul_eq_aux L (Module.Free.chooseBasis ℤ L) f x y

/-- **Poisson summation on a lattice for Schwartz functions.** For $x \in V$, $$\sum_{\ell \in L} f(x + \ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu) e^{2 \pi i \langle x, \mu \rangle}.$$ -/
theorem _root_.SchwartzMap.tsum_add_zlattice_eq (f : 𝓢(V, ℂ)) (x : V) :
    ∑' ℓ : L, f (x + ℓ) = ((ZLattice.covolume L)⁻¹ : ℝ) *
      ∑' μ : dualLattice L, 𝓕 f μ * cexp (2 * Real.pi * I * ⟪x, (μ : V)⟫) := by
  simpa using f.tsum_add_zlattice_mul_eq L x 0

/-- **Poisson summation on a lattice for Schwartz functions at $x = 0$.** $$\sum_{\ell \in L} f(\ell) = \frac{1}{\mathrm{covol}(L)} \sum_{\mu \in L^\vee} \mathcal{F} f(\mu).$$ -/
theorem _root_.SchwartzMap.tsum_zlattice_eq (f : 𝓢(V, ℂ)) :
    ∑' ℓ : L, f ℓ = ((ZLattice.covolume L)⁻¹ : ℝ) * ∑' μ : dualLattice L, 𝓕 f μ := by
  simpa using f.tsum_add_zlattice_mul_eq L 0 0

end Main

end Langlands.Tate
