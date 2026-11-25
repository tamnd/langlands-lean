/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.PoissonLattice
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Fractional ideals as lattices in the Minkowski space

Let $K$ be a number field with $r_1$ real places and $r_2$ complex places, degree $n = r_1 + 2 r_2$ and discriminant $d_K$. For an infinite place $w$ let $\sigma_w : K \to \mathbb{C}$ be the embedding that Mathlib chooses for $w$, let $|x|_w = |\sigma_w(x)|$, and let $n_w$ be $1$ if $w$ is real and $2$ if $w$ is complex. This file makes a nonzero fractional ideal $\mathfrak{a}$ into a full lattice in a euclidean space. It computes the covolume of this lattice and its dual lattice. These are the inputs of the theta transformation formula in `Langlands.Tate.DedekindTheta`.

## The space and the embeddings

The space is the euclidean mixed space $E = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ (`NumberField.mixedEmbedding.euclidean.mixedSpace`). Its inner product is the standard one, $$\langle x, y \rangle = \sum_{w \text{ real}} x_w y_w + \sum_{w \text{ complex}} \mathrm{Re}(x_w \bar y_w),$$ so $\mathbb{C} = \mathbb{R}^2$ has the usual inner product. The measure on $E$ is the Lebesgue measure of this inner product. It agrees with the measure `volume` on Mathlib's mixed space. For real numbers $c = (c_w)_w$ let $D_c$ multiply the coordinate at $w$ by $c_w$. We use two embeddings of $K$ in $E$:

* $\varphi_c(x) = (c_w \sigma_w(x))_w$ (`Langlands.Tate.globalEmbedding`),
* $\psi_c(x) = (c_w \overline{\sigma_w(x)})_w$ (`Langlands.Tate.globalConjEmbedding`).

So $|\varphi_c(x)|^2 = |\psi_c(x)|^2 = \sum_w c_w^2 |x|_w^2$, and $$\langle \psi_{c'}(x), \varphi_c(y) \rangle = \sum_w c'_w c_w \, \mathrm{Re}\, \sigma_w(xy).$$ If $c_w c'_w = n_w$ for each $w$, the right side is $\sum_w n_w \mathrm{Re}\, \sigma_w(xy) = \mathrm{Tr}_{K/\mathbb{Q}}(xy)$. This is how the trace form appears as an inner product. The conjugation in $\psi$ is necessary: without it a complex place gives $\mathrm{Re}(\sigma_w(x) \overline{\sigma_w(y)})$, which is not a trace.

## Main results

* `Langlands.Tate.trace_eq_inner`: $\langle \psi_{c'}(x), \varphi_c(y) \rangle = \mathrm{Tr}_{K/\mathbb{Q}}(xy)$ when $c_w c'_w = n_w$.
* `Langlands.Tate.globalLattice`: the full lattice $\Lambda_c(\mathfrak{a}) = \varphi_c(\mathfrak{a}) \subset E$ for $c_w \neq 0$.
* `Langlands.Tate.covolume_globalLattice`: $\mathrm{covol}(\Lambda_c(\mathfrak{a})) = \prod_w |c_w|^{n_w} \cdot N(\mathfrak{a}) \, 2^{-r_2} \sqrt{|d_K|}$.
* `Langlands.Tate.mem_dualLattice_globalLattice`: if $c_w c'_w = n_w$, then the dual lattice of $\Lambda_c(\mathfrak{a})$ is $\psi_{c'}(\mathfrak{a}^\vee)$. Here $\mathfrak{a}^\vee = \{\beta \in K : \mathrm{Tr}(\beta \mathfrak{a}) \subseteq \mathbb{Z}\}$.
* `Langlands.Tate.dual_eq_inv_mul_different`: $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$, where $\mathfrak{d}$ is the different ideal.

## Proofs

The covolume comes from Mathlib's formula `NumberField.mixedEmbedding.covolume_idealLattice` for $\sigma(\mathfrak{a})$ in the mixed space. The map $D_c$ has determinant $\prod_w c_w^{n_w}$, and a linear automorphism $e$ multiplies covolumes by $|\det e|$ (`Langlands.Tate.covolume_comap_linearEquiv`). For the dual lattice, the inclusion $\psi_{c'}(\mathfrak{a}^\vee) \subseteq \Lambda_c(\mathfrak{a})^\vee$ is the trace formula. Conversely, let $y$ be in the dual lattice and let $b_1, \dots, b_n$ be a $\mathbb{Z}$-basis of $\mathfrak{a}$. Then $m_i = \langle y, \varphi_c(b_i) \rangle$ is an integer. Let $b_i^*$ be the dual basis of $K$ for the trace form and $\beta = \sum_i m_i b_i^*$. Then $y - \psi_{c'}(\beta)$ is orthogonal to the lattice, so it is zero, and $\beta \in \mathfrak{a}^\vee$.

## References

* J. Neukirch, Algebraic number theory, chapter I, section 5 and chapter VII, section 5.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.2.
-/

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace ComplexConjugate nonZeroDivisors

namespace Langlands.Tate

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Let $L$ be a full lattice in a finite dimensional real vector space $E$ with a Haar measure $\mu$, and let $e$ be a linear automorphism of $E$. Then $\mathrm{covol}(e^{-1} L) = |\det e|^{-1} \, \mathrm{covol}(L)$. -/
theorem covolume_comap_linearEquiv (e : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ * ZLattice.covolume L μ := by
  set b := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (ZLattice.isAddFundamentalDomain b μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (ZLattice.isAddFundamentalDomain (b.ofZLatticeComap ℝ L e.toLinearEquiv) μ)]
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hF : ZSpan.fundamentalDomain ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis ℝ _)
      = e ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv, ZSpan.map_fundamentalDomain]
    congr!
    ext; simp
  rw [hF, measureReal_def, measureReal_def,
    show (e : E → E) = ((e : E →ₗ[ℝ] E) : E → E) from rfl,
    MeasureTheory.Measure.addHaar_preimage_linearMap μ hdet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

end Covolume

variable (K : Type*) [Field K]

section Trace

variable [NumberField K]

open scoped Classical in
/-- For an infinite place $w$ and $x \in K$, the sum of $\varphi(x)$ over the complex embeddings $\varphi$ that induce $w$ is $n_w \, \mathrm{Re}\, \sigma_w(x)$. Here $\sigma_w$ is the embedding chosen by Mathlib for $w$ and $n_w$ is the multiplicity of $w$. -/
theorem sum_filter_mk_eq (w : InfinitePlace K) (x : K) :
    ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ x =
      (mult w : ℂ) * ((w.embedding x).re : ℂ) := by
  have hfil : Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
      Finset.univ.filter
        (fun φ => φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding) := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  rw [hfil, Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w))]
  simp only [Finset.mem_univ, ite_true]
  by_cases hw : IsReal w
  · have h1 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw)
    rw [h1, Finset.union_idempotent, Finset.sum_singleton, mult_isReal ⟨w, hw⟩, Nat.cast_one,
      one_mul, ← embedding_of_isReal_apply hw, Complex.ofReal_re]
  · have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
    rw [← Finset.insert_eq, Finset.sum_pair hne,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hw⟩, ComplexEmbedding.conjugate_coe_eq,
      Complex.add_conj]
    push_cast; ring

/-- The trace as a sum over the infinite places: $\mathrm{Tr}_{K/\mathbb{Q}}(x) = \sum_w n_w \, \mathrm{Re}\, \sigma_w(x)$. -/
theorem trace_eq_sum_mult_re (x : K) :
    (Algebra.trace ℚ K x : ℝ) = ∑ w : InfinitePlace K, (mult w : ℝ) * (w.embedding x).re := by
  classical
  apply Complex.ofReal_injective
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ x) (fun σ => σ x)
    fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x)] at h
  simp_rw [sum_filter_mk_eq] at h
  push_cast
  rw [← h]
  simp

end Trace

section Scale

/-- The linear map of the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ that multiplies the coordinate at each infinite place $w$ by the real number $c_w$. -/
noncomputable def mixedScaleₗ (c : InfinitePlace K → ℝ) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.prodMap (LinearMap.pi fun w => (c w • LinearMap.id).comp (LinearMap.proj w))
    (LinearMap.pi fun w => (c w • LinearMap.id).comp (LinearMap.proj w))

/-- The real coordinates of $D_c x$ are $c_w x_w$. -/
@[simp]
theorem mixedScaleₗ_apply_fst (c : InfinitePlace K → ℝ) (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsReal w}) : (mixedScaleₗ K c x).1 w = c w * x.1 w := rfl

/-- The complex coordinates of $D_c x$ are $c_w x_w$. -/
@[simp]
theorem mixedScaleₗ_apply_snd (c : InfinitePlace K → ℝ) (x : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedScaleₗ K c x).2 w = (c w : ℂ) * x.2 w := by
  simp [mixedScaleₗ, Complex.real_smul]

/-- The scaling maps compose by multiplication: $D_c D_d = D_{cd}$. -/
theorem mixedScaleₗ_mul (c d : InfinitePlace K → ℝ) (x : mixedSpace K) :
    mixedScaleₗ K c (mixedScaleₗ K d x) = mixedScaleₗ K (c * d) x := by
  ext w
  · simp [mul_assoc]
  · simp [mul_assoc]

/-- The scaling by $c = 1$ is the identity. -/
theorem mixedScaleₗ_one (x : mixedSpace K) : mixedScaleₗ K 1 x = x := by
  ext w
  · simp
  · simp

/-- The determinant of the scaling is $\det D_c = \prod_w c_w^{n_w}$, because a complex coordinate counts as two real coordinates. -/
theorem det_mixedScaleₗ [NumberField K] (c : InfinitePlace K → ℝ) :
    LinearMap.det (mixedScaleₗ K c) = ∏ w, c w ^ mult w := by
  classical
  rw [mixedScaleₗ, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi,
    prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [LinearMap.det_smul, LinearMap.det_id, mult_isReal w, Module.finrank_self]
    simp
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [LinearMap.det_smul, LinearMap.det_id, mult_isComplex w, Complex.finrank_real_complex]
    simp

/-- The continuous linear automorphism $D_c$ of the mixed space that multiplies the coordinate at $w$ by the nonzero real number $c_w$. -/
noncomputable def mixedScale [NumberField K] (c : InfinitePlace K → ℝˣ) :
    mixedSpace K ≃L[ℝ] mixedSpace K :=
  (LinearEquiv.ofLinearMap (mixedScaleₗ K fun w => (c w : ℝ))
    (mixedScaleₗ K fun w => ((c w)⁻¹ : ℝˣ))
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, mixedScaleₗ_mul, LinearMap.id_apply]
      convert mixedScaleₗ_one K x
      ext w; simp)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, mixedScaleₗ_mul, LinearMap.id_apply]
      convert mixedScaleₗ_one K x
      ext w; simp)).toContinuousLinearEquiv

/-- Complex conjugation on the complex coordinates of the mixed space. It is the identity on the real coordinates. -/
noncomputable def mixedConj : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.prodMap LinearMap.id
    (LinearMap.pi fun w => Complex.conjAe.toLinearMap.comp (LinearMap.proj w))

/-- The conjugation does not change the real coordinates. -/
@[simp]
theorem mixedConj_apply_fst (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (mixedConj K x).1 w = x.1 w := rfl

/-- The conjugation acts on the complex coordinates by $z \mapsto \bar z$. -/
@[simp]
theorem mixedConj_apply_snd (x : mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedConj K x).2 w = conj (x.2 w) := rfl

/-- The conjugation is an involution. -/
theorem mixedConj_mixedConj (x : mixedSpace K) : mixedConj K (mixedConj K x) = x := by
  ext w
  · rfl
  · simp

end Scale

section Embedding

open scoped Classical

variable [NumberField K]

/-- The inner product of the euclidean mixed space in coordinates: $\langle x, y \rangle = \sum_{w \text{ real}} x_w y_w + \sum_{w \text{ complex}} \mathrm{Re}(x_w \bar y_w)$. -/
theorem inner_toMixed_symm (x y : mixedSpace K) :
    ⟪(euclidean.toMixed K).symm x, (euclidean.toMixed K).symm y⟫ =
      ∑ w, x.1 w * y.1 w + ∑ w, ⟪x.2 w, y.2 w⟫ := by
  simp [euclidean.toMixed, WithLp.prod_inner_apply, PiLp.inner_apply, mul_comm]

/-- The squared norm of the euclidean mixed space in coordinates: $|x|^2 = \sum_{w \text{ real}} x_w^2 + \sum_{w \text{ complex}} |x_w|^2$. -/
theorem norm_toMixed_symm_sq (x : mixedSpace K) :
    ‖(euclidean.toMixed K).symm x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toMixed_symm]
  simp [sq]

/-- The scaled Minkowski embedding $\varphi_c : K \to \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, $\varphi_c(x) = (c_w \sigma_w(x))_w$, with values in the euclidean mixed space. -/
noncomputable def globalEmbedding (c : InfinitePlace K → ℝ) : K →+ euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm.toLinearMap.toAddMonoidHom.comp
    ((mixedScaleₗ K c).toAddMonoidHom.comp (mixedEmbedding K).toAddMonoidHom)

/-- The conjugate scaled Minkowski embedding $\psi_c(x) = (c_w \overline{\sigma_w(x)})_w$. At a real place the conjugation does nothing. -/
noncomputable def globalConjEmbedding (c : InfinitePlace K → ℝ) : K →+ euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm.toLinearMap.toAddMonoidHom.comp
    ((mixedScaleₗ K c).toAddMonoidHom.comp
      ((mixedConj K).toAddMonoidHom.comp (mixedEmbedding K).toAddMonoidHom))

/-- The definition of $\varphi_c$ in terms of the mixed embedding. -/
theorem globalEmbedding_apply (c : InfinitePlace K → ℝ) (x : K) :
    globalEmbedding K c x = (euclidean.toMixed K).symm (mixedScaleₗ K c (mixedEmbedding K x)) :=
  rfl

/-- The definition of $\psi_c$ in terms of the mixed embedding. -/
theorem globalConjEmbedding_apply (c : InfinitePlace K → ℝ) (x : K) :
    globalConjEmbedding K c x =
      (euclidean.toMixed K).symm (mixedScaleₗ K c (mixedConj K (mixedEmbedding K x))) :=
  rfl

/-- The squared norm of $\varphi_c(x)$ is $|\varphi_c(x)|^2 = \sum_w c_w^2 |x|_w^2$. -/
theorem norm_globalEmbedding_sq (c : InfinitePlace K → ℝ) (x : K) :
    ‖globalEmbedding K c x‖ ^ 2 = ∑ w, c w ^ 2 * w x ^ 2 := by
  classical
  rw [globalEmbedding_apply, norm_toMixed_symm_sq, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_fst, mixedEmbedding_apply_isReal, ← norm_embedding_of_isReal w.2,
      Real.norm_eq_abs, sq_abs, mul_pow]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_snd, mixedEmbedding_apply_isComplex, norm_mul, norm_embedding_eq,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The squared norm of $\psi_c(x)$ is $|\psi_c(x)|^2 = \sum_w c_w^2 |x|_w^2$. -/
theorem norm_globalConjEmbedding_sq (c : InfinitePlace K → ℝ) (x : K) :
    ‖globalConjEmbedding K c x‖ ^ 2 = ∑ w, c w ^ 2 * w x ^ 2 := by
  classical
  rw [globalConjEmbedding_apply, norm_toMixed_symm_sq, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_fst, mixedConj_apply_fst, mixedEmbedding_apply_isReal,
      ← norm_embedding_of_isReal w.2, Real.norm_eq_abs, sq_abs, mul_pow]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_snd, mixedConj_apply_snd, mixedEmbedding_apply_isComplex, norm_mul,
      Complex.norm_conj, norm_embedding_eq, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The inner product of the two embeddings: $\langle \psi_{c'}(x), \varphi_c(y) \rangle = \sum_w c'_w c_w \, \mathrm{Re}\, \sigma_w(xy)$. -/
theorem inner_globalConjEmbedding_globalEmbedding (c c' : InfinitePlace K → ℝ) (x y : K) :
    ⟪globalConjEmbedding K c' x, globalEmbedding K c y⟫ =
      ∑ w, c' w * c w * (w.embedding (x * y)).re := by
  classical
  rw [globalConjEmbedding_apply, globalEmbedding_apply, inner_toMixed_symm, sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_fst, mixedScaleₗ_apply_fst, mixedConj_apply_fst,
      mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal, ← embedding_of_isReal_apply w.2,
      Complex.ofReal_re, map_mul]
    ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedScaleₗ_apply_snd, mixedScaleₗ_apply_snd, mixedConj_apply_snd,
      mixedEmbedding_apply_isComplex, mixedEmbedding_apply_isComplex, Complex.inner, map_mul,
      map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [show ((c w : ℂ) * w.1.embedding y * ((c' w : ℂ) * w.1.embedding x)) =
      ((c' w * c w : ℝ) : ℂ) * (w.1.embedding x * w.1.embedding y) by push_cast; ring,
      Complex.re_ofReal_mul]

/-- In the coordinates of the mixed space, $\varphi_c(x) = D_c \sigma(x)$. -/
theorem toMixed_globalEmbedding (c : InfinitePlace K → ℝ) (x : K) :
    euclidean.toMixed K (globalEmbedding K c x) = mixedScaleₗ K c (mixedEmbedding K x) := by
  rw [globalEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The embedding $\varphi_c$ is injective when every $c_w$ is nonzero. -/
theorem globalEmbedding_injective (c : InfinitePlace K → ℝˣ) :
    Function.Injective (globalEmbedding K fun w => (c w : ℝ)) := by
  intro x y h
  have h1 := congrArg (fun v => mixedScale K c⁻¹ (euclidean.toMixed K v)) h
  simp only [toMixed_globalEmbedding] at h1
  have h2 : ∀ z : K, mixedScale K c⁻¹ (mixedScaleₗ K (fun w => (c w : ℝ)) (mixedEmbedding K z)) =
      mixedEmbedding K z := fun z => (mixedScale K c).symm_apply_apply (mixedEmbedding K z)
  rw [h2, h2] at h1
  exact mixedEmbedding_injective K h1

/-- The embedding $\psi_c$ is injective when every $c_w$ is nonzero. -/
theorem globalConjEmbedding_injective (c : InfinitePlace K → ℝˣ) :
    Function.Injective (globalConjEmbedding K fun w => (c w : ℝ)) := by
  intro x y h
  have h1 := congrArg (fun v => mixedConj K (mixedScale K c⁻¹ (euclidean.toMixed K v))) h
  simp only [globalConjEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply] at h1
  have h2 : ∀ z : K, mixedConj K (mixedScale K c⁻¹ (mixedScaleₗ K (fun w => (c w : ℝ))
      (mixedConj K (mixedEmbedding K z)))) = mixedEmbedding K z := fun z => by
    rw [show mixedScale K c⁻¹
        (mixedScaleₗ K (fun w => (c w : ℝ)) (mixedConj K (mixedEmbedding K z))) =
          mixedConj K (mixedEmbedding K z) from
        (mixedScale K c).symm_apply_apply (mixedConj K (mixedEmbedding K z)),
      mixedConj_mixedConj]
  rw [h2, h2] at h1
  exact mixedEmbedding_injective K h1

/-- The trace form as an inner product. If $c_w c'_w = n_w$ for each place $w$, then $\langle \psi_{c'}(x), \varphi_c(y) \rangle = \mathrm{Tr}_{K/\mathbb{Q}}(xy)$. -/
theorem trace_eq_inner (c c' : InfinitePlace K → ℝ) (h : ∀ w, c w * c' w = mult w) (x y : K) :
    ⟪globalConjEmbedding K c' x, globalEmbedding K c y⟫ = (Algebra.trace ℚ K (x * y) : ℝ) := by
  rw [inner_globalConjEmbedding_globalEmbedding, trace_eq_sum_mult_re]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_comm (c' w), h]

/-- The lattice $\Lambda_c(\mathfrak{a}) = \varphi_c(\mathfrak{a})$ in the euclidean mixed space, for a nonzero fractional ideal $\mathfrak{a}$ and nonzero real numbers $c_w$. It is the preimage of Mathlib's `idealLattice` under the map $D_c^{-1}$. -/
noncomputable def globalLattice (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K a)
    ((euclidean.toMixed K).trans (mixedScale K c).symm).toLinearMap

variable (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The lattice $\Lambda_c(\mathfrak{a})$ is discrete. -/
instance : DiscreteTopology (globalLattice K c a) := by
  unfold globalLattice; infer_instance

/-- The lattice $\Lambda_c(\mathfrak{a})$ spans the space, so it is a full lattice. -/
instance : IsZLattice ℝ (globalLattice K c a) := by
  unfold globalLattice; infer_instance

/-- The points of $\Lambda_c(\mathfrak{a})$ are the vectors $\varphi_c(\alpha)$ with $\alpha \in \mathfrak{a}$. -/
theorem mem_globalLattice {y : euclidean.mixedSpace K} :
    y ∈ globalLattice K c a ↔
      ∃ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K), globalEmbedding K (fun w => (c w : ℝ)) α = y := by
  rw [← SetLike.mem_coe, globalLattice, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe,
    mem_idealLattice]
  refine exists_congr fun α => and_congr Iff.rfl ?_
  change _ = (mixedScale K c).symm (euclidean.toMixed K y) ↔ _
  rw [ContinuousLinearEquiv.eq_symm_apply, globalEmbedding_apply,
    ContinuousLinearEquiv.symm_apply_eq]
  rfl

/-- For $\alpha \in \mathfrak{a}$, the vector $\varphi_c(\alpha)$ is in $\Lambda_c(\mathfrak{a})$. -/
theorem globalEmbedding_mem {α : K} (hα : α ∈ (a : FractionalIdeal (𝓞 K)⁰ K)) :
    globalEmbedding K (fun w => (c w : ℝ)) α ∈ globalLattice K c a :=
  (mem_globalLattice K c a).2 ⟨α, hα, rfl⟩

/-- The bijection $\mathfrak{a} \to \Lambda_c(\mathfrak{a})$, $\alpha \mapsto \varphi_c(\alpha)$. -/
noncomputable def globalLatticeEquiv :
    (a : FractionalIdeal (𝓞 K)⁰ K) ≃ globalLattice K c a :=
  Equiv.ofBijective (fun α => ⟨globalEmbedding K _ α, globalEmbedding_mem K c a α.2⟩)
    ⟨fun α β h => Subtype.ext (globalEmbedding_injective K c (congrArg Subtype.val h)),
      fun ⟨y, hy⟩ => by
        obtain ⟨α, hα, rfl⟩ := (mem_globalLattice K c a).1 hy
        exact ⟨⟨α, hα⟩, rfl⟩⟩

/-- The bijection $\mathfrak{a} \to \Lambda_c(\mathfrak{a})$ sends $\alpha$ to $\varphi_c(\alpha)$. -/
@[simp]
theorem coe_globalLatticeEquiv (α : (a : FractionalIdeal (𝓞 K)⁰ K)) :
    (globalLatticeEquiv K c a α : euclidean.mixedSpace K) =
      globalEmbedding K (fun w => (c w : ℝ)) α := rfl

/-- The covolume of $\Lambda_c(\mathfrak{a})$ for the Lebesgue measure of the euclidean mixed space is $$\mathrm{covol}(\Lambda_c(\mathfrak{a})) = \prod_w |c_w|^{n_w} \cdot N(\mathfrak{a}) \, 2^{-r_2} \sqrt{|d_K|}.$$ -/
theorem covolume_globalLattice :
    ZLattice.covolume (globalLattice K c a) =
      (∏ w, |(c w : ℝ)| ^ mult w) *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|discr K|) := by
  have h : globalLattice K c a = ZLattice.comap ℝ
      (ZLattice.comap ℝ (idealLattice K a) (mixedScale K c).symm.toLinearMap)
      (euclidean.toMixed K).toLinearMap := by
    rw [ZLattice.comap_comp]; rfl
  rw [h, ZLattice.covolume_comap _ _ _ (euclidean.volumePreserving_toMixed K),
    covolume_comap_linearEquiv, covolume_idealLattice]
  congr 1
  have : ((mixedScale K c).symm : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      mixedScaleₗ K fun w => ((c w)⁻¹ : ℝˣ) := rfl
  rw [this, det_mixedScaleₗ, Finset.abs_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [abs_pow, Units.val_inv_eq_inv_val, abs_inv, inv_pow, inv_inv]

/-- A vector orthogonal to $\varphi_c(b_i)$ for each element $b_i$ of a $\mathbb{Z}$-basis of $\mathfrak{a}$ is zero. -/
theorem inner_eq_zero_of_forall_basis {z : euclidean.mixedSpace K}
    (hz : ∀ i, ⟪z, globalEmbedding K (fun w => (c w : ℝ)) (basisOfFractionalIdeal K a i)⟫ = 0) :
    z = 0 := by
  have h1 : ∀ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K),
      ⟪z, globalEmbedding K (fun w => (c w : ℝ)) α⟫ = 0 := by
    intro α hα
    have hα' : α ∈ Submodule.span ℤ (Set.range (basisOfFractionalIdeal K a)) :=
      (mem_span_basisOfFractionalIdeal K).2 hα
    clear hα
    induction hα' using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hz i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, inner_add_right, hx, hy, add_zero]
    | smul n x _ hx =>
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ n, real_inner_smul_right, hx, mul_zero]
  have h2 : Submodule.span ℝ (globalLattice K c a : Set (euclidean.mixedSpace K)) ≤
      LinearMap.ker (innerₛₗ ℝ z) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨α, hα, rfl⟩ := (mem_globalLattice K c a).1 hy
    exact h1 α hα
  rw [IsZLattice.span_top] at h2
  have h3 := h2 (Submodule.mem_top (x := z))
  simpa using h3

/-- The dual lattice of $\Lambda_c(\mathfrak{a})$. If $c_w c'_w = n_w$ for each place $w$, then $\Lambda_c(\mathfrak{a})^\vee = \psi_{c'}(\mathfrak{a}^\vee)$, where $\mathfrak{a}^\vee = \{\beta \in K : \mathrm{Tr}(\beta \mathfrak{a}) \subseteq \mathbb{Z}\}$ is the dual for the trace form. -/
theorem mem_dualLattice_globalLattice (c' : InfinitePlace K → ℝˣ)
    (h : ∀ w, (c w : ℝ) * c' w = mult w) {y : euclidean.mixedSpace K} :
    y ∈ dualLattice (globalLattice K c a) ↔
      ∃ β ∈ FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K),
        globalConjEmbedding K (fun w => (c' w : ℝ)) β = y := by
  have ha : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := a.ne_zero
  constructor
  · intro hy
    set b := basisOfFractionalIdeal K a
    set B := Algebra.traceForm ℚ K
    set bd := B.dualBasis (traceForm_nondegenerate ℚ K) b
    have hb : ∀ i, b i ∈ (a : FractionalIdeal (𝓞 K)⁰ K) := fun i => by
      rw [basisOfFractionalIdeal_apply]; exact (fractionalIdealBasis K a i).2
    have hm : ∀ i, ∃ m : ℤ, ⟪y, globalEmbedding K (fun w => (c w : ℝ)) (b i)⟫ = m := fun i =>
      (mem_dualLattice _).1 hy _ (globalEmbedding_mem K c a (hb i))
    choose m hm using hm
    set β : K := ∑ i, (m i : ℚ) • bd i
    have htr : ∀ j, Algebra.trace ℚ K (β * b j) = m j := by
      intro j
      have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ K) b
      calc Algebra.trace ℚ K (β * b j) = B β (b j) := (Algebra.traceForm_apply _ _ _).symm
        _ = ∑ i, (m i : ℚ) * B (bd i) (b j) := by
          simp [β, map_sum, LinearMap.sum_apply, map_smul]
        _ = m j := by simp only [B, bd, this]; simp
    have hβ : globalConjEmbedding K (fun w => (c' w : ℝ)) β = y := by
      rw [← sub_eq_zero]
      refine (inner_eq_zero_of_forall_basis K c a fun j => ?_).symm ▸ rfl
      rw [inner_sub_left, hm, trace_eq_inner K _ _ (fun w => h w), htr]
      simp
    refine ⟨β, (FractionalIdeal.mem_dual ha).2 fun α hα => ?_, hβ⟩
    obtain ⟨n, hn⟩ := (mem_dualLattice _).1 hy _ (globalEmbedding_mem K c a hα)
    rw [← hβ, trace_eq_inner K _ _ (fun w => h w)] at hn
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast]
    exact_mod_cast hn.symm
  · rintro ⟨β, hβ, rfl⟩
    rw [mem_dualLattice]
    intro ℓ hℓ
    obtain ⟨α, hα, rfl⟩ := (mem_globalLattice K c a).1 hℓ
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual ha).1 hβ α hα
    refine ⟨n, ?_⟩
    rw [trace_eq_inner K _ _ (fun w => h w), ← Algebra.traceForm_apply, ← hn, eq_intCast]
    simp

/-- The bijection $\mathfrak{a}^\vee \to \Lambda_c(\mathfrak{a})^\vee$, $\beta \mapsto \psi_{c'}(\beta)$, when $c_w c'_w = n_w$ for each place $w$. -/
noncomputable def globalDualEquiv (c' : InfinitePlace K → ℝˣ)
    (h : ∀ w, (c w : ℝ) * c' w = mult w) :
    FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K) ≃
      dualLattice (globalLattice K c a) :=
  Equiv.ofBijective
    (fun β => ⟨globalConjEmbedding K (fun w => (c' w : ℝ)) β,
      (mem_dualLattice_globalLattice K c a c' h).2 ⟨β, β.2, rfl⟩⟩)
    ⟨fun α β hαβ => Subtype.ext (globalConjEmbedding_injective K c' (congrArg Subtype.val hαβ)),
      fun ⟨y, hy⟩ => by
        obtain ⟨β, hβ, rfl⟩ := (mem_dualLattice_globalLattice K c a c' h).1 hy
        exact ⟨⟨β, hβ⟩, rfl⟩⟩

/-- The bijection $\mathfrak{a}^\vee \to \Lambda_c(\mathfrak{a})^\vee$ sends $\beta$ to $\psi_{c'}(\beta)$. -/
@[simp]
theorem coe_globalDualEquiv (c' : InfinitePlace K → ℝˣ) (h : ∀ w, (c w : ℝ) * c' w = mult w)
    (β : FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K)) :
    (globalDualEquiv K c a c' h β : euclidean.mixedSpace K) =
      globalConjEmbedding K (fun w => (c' w : ℝ)) β := rfl

end Embedding

section Different

variable [NumberField K]

/-- The dual of a fractional ideal for the trace form is $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$, where $\mathfrak{d}$ is the different ideal of $K$. -/
theorem dual_eq_inv_mul_different (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.dual ℤ ℚ I = (I * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), mul_inv, inv_inv,
    mul_comm]

end Different

end Langlands.Tate
