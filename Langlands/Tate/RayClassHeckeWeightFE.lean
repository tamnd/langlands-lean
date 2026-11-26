/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassHeckeWeight
import Langlands.Tate.RayClassFE

/-!
# Toward the functional equation of a Hecke character of an imaginary quadratic field with $n \neq 0$

Let $K$ be an imaginary quadratic field, let $\sigma$ be the embedding of its complex place, and let $\chi$ be a Hecke character with the archimedean parameters $(n, t)$. This file does the first steps of Hecke's proof of the functional equation of $L(s, \chi)$ for $n \neq 0$. It transfers the weighted Epstein zeta function of `Langlands.Tate.RayClassHeckeWeight` to the ideals of $K$, and it describes the coefficients of the partial $L$-series without the condition that $\chi$ is trivial at the infinite place.

## Main definitions

* `Langlands.Tate.mapLattice`: the image $e(L)$ of a lattice under a linear isometry $e$.
* `Langlands.Tate.quadIsometry`: the linear isometry of the euclidean mixed space of $K$ with $\mathbb{C}$.
* `Langlands.Tate.quadEmbed`: the map $\alpha \mapsto \sqrt 2 \sigma(\alpha)$ of $K$ to $\mathbb{C}$.
* `Langlands.Tate.quadLattice`: the lattice $\sqrt 2 \sigma(\mathfrak{a}) \subset \mathbb{C}$ of a fractional ideal $\mathfrak{a}$.
* `Langlands.Tate.infChar`: the infinite type $\chi_\infty : K^\times \to \mathbb{C}^\times$, $x \mapsto \prod_w \chi_w(x)$.
* `Langlands.Tate.periodicCoeff`: the periodic coefficient $c_J(\alpha) = \chi_{\mathrm{id}}((\alpha) J^{-1}) \chi_\infty(\alpha)$.

## Main results

* `dualLattice_mapLattice` and `covolume_mapLattice`: $e(L)^\vee = e(L^\vee)$ and $\mathrm{covol}(e(L)) = \mathrm{covol}(L)$.
* `coe_quadDualEquiv` and `inner_conj_quadEmbed`: the dual lattice of $\sqrt 2 \sigma(\mathfrak{a})$ is $\overline{\sqrt 2 \sigma(\mathfrak{a}^\vee)}$, and $\langle \overline{\sqrt 2 \sigma(\beta)}, \sqrt 2 \sigma(\xi) \rangle = \mathrm{Tr}(\beta \xi)$.
* `covolume_quadLattice`: $\mathrm{covol}(\sqrt 2 \sigma(\mathfrak{a})) = N(\mathfrak{a}) \sqrt{|d_K|}$.
* `hasSum_completedWeightZeta_quadLattice` and `hasSum_completedWeightZeta_dual_quadLattice`: the Dirichlet series of the weighted Epstein zeta functions of $\sqrt 2 \sigma(\mathfrak{a})$ and of its dual, written as sums over $\mathfrak{a}$ and over $\mathfrak{a}^\vee$.
* `completedWeightZeta_quadLattice_sub`: for $k \neq 0$, $\Lambda^k_{\sqrt 2 \sigma(\mathfrak{a})}(\sqrt 2 \sigma(\xi), 0; 2k + 2 - s) = (-i)^k (N(\mathfrak{a}) \sqrt{|d_K|})^{-1} \Lambda^k_{(\sqrt 2 \sigma(\mathfrak{a}))^\vee}(0, \sqrt 2 \sigma(\xi); s)$.
* `ideleChar_eq_infinitePart_mul_prod`: $\chi(x) = \chi(x_\infty) \prod_{v \in S} \chi_v(x_v)$ for an idele $x$ that is a unit outside $S$.
* `idealChar_toPrincipalIdeal_mul_infinitePart` and `idealChar_mul_infChar_eq`: reciprocity, $\chi_{\mathrm{id}}((x)) \chi_\infty(x) = 1$ for $x \equiv 1$ modulo the conductor.
* `infChar_unit_eq_one`: $\chi_\infty(\varepsilon) = 1$ for a unit $\varepsilon \equiv 1$ modulo the conductor.
* `infChar_apply_of_isArchimedeanParameter`: $\chi_\infty(x) = (\sigma(x) / |\sigma(x)|)^n |\sigma(x)|^{2t}$.
* `quadPlace_unit_zpow_eq_one`: $\sigma(\varepsilon)^n = 1$ for a unit $\varepsilon \equiv 1$ modulo the conductor.
* `periodicCoeff_eq_of_sub_mem`, `periodicCoeff_eq_zero_of_mem` and `periodicCoeff_unit_mul`: the periodic coefficient depends only on $\alpha$ modulo $\mathfrak{f} J$, it is $0$ on $\mathfrak{f} J$, and $c_J(\varepsilon \alpha) = \chi_\infty(\varepsilon) c_J(\alpha)$ for a unit $\varepsilon$.
* `rayCoeff_eq_periodicCoeff_mul_quad`: $\chi((\alpha) J^{-1}) = c_J(\alpha) (\overline{\sigma(\alpha)} / |\sigma(\alpha)|)^n |\sigma(\alpha)|^{-2t}$.

## Proofs

The isometry sends $x$ in the euclidean mixed space to its component at the complex place. It sends the Minkowski embedding with the trace scale to $\sqrt 2 \sigma$, and the conjugate embedding to $\sqrt 2 \bar\sigma$. So the lattice `Langlands.Tate.traceLattice` of $\mathfrak{a}$ goes to $\sqrt 2 \sigma(\mathfrak{a})$, and `Langlands.Tate.globalDualEquiv` gives the dual lattice. The covolume is `ZLattice.covolume_comap` with the measure preserving isometry, and the series are `Langlands.Tate.hasSum_completedWeightZeta` reindexed by these bijections.

The product formula with the infinite part is the proof of `Langlands.Tate.IsRayClassType.ideleChar_eq_prod`, where the factor $\chi(x_\infty)$ is kept. Reciprocity then follows as in `Langlands.Tate.IsRayClassType.idealChar_toPrincipalIdeal`, from $\chi(x) = 1$ for $x \in K^\times$. The infinite part of an imaginary quadratic field has one factor, and `Langlands.HeckeCharacter.IsArchimedeanParameter` gives its value. A unit has $|\sigma(\varepsilon)|^2 = |N(\varepsilon)| = 1$ by `NumberField.InfinitePlace.prod_eq_abs_norm`. The periodicity of $c_J$ is the proof of `Langlands.Tate.IsRayClassType.rayCoeff_eq_of_sub_mem`, with reciprocity in place of the ray class condition.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt K` for a Hecke character of an imaginary quadratic field with $n \neq 0$, and so it does not prove the functional equation of these characters. These steps are still open. First, the theta series with the coefficient: the sum over the residues $\xi$ of $J$ modulo $\mathfrak{f} J$ of $c_J(\xi)$ times the weighted Epstein zeta function of $\sqrt 2 \sigma(\mathfrak{f} J)$ at $\sqrt 2 \sigma(\xi)$, with $k = |n|$ and $\overline{\sigma(\alpha)}^{|n|}$ (or $\sigma(\alpha)^{|n|}$ for $n < 0$, through the complex conjugate lattice), and the reduction of $t$ to $0$ through `Langlands.Tate.heckeFunctionalEquation_of_twist`. The sum over $\alpha$ modulo the units must use `periodicCoeff_unit_mul` and `quadPlace_unit_zpow_eq_one`. Second, the weighted Gauss sums: the chain `Langlands.Tate.RayClassGauss` and its sequels assumes `Langlands.Tate.IsRayClassType` in each lemma, so it must be done again with `Langlands.Tate.periodicCoeff`. Third, the sorting of the dual series by the ideals $(\beta) \mathfrak{f} J \mathfrak{d}$, the sum over the ideal classes, the comparison of $\Gamma_\mathbb{R}(2u + |n|)$ with `Langlands.gammaFactor`, the root number $W = (-i)^{|n|} \tau(\chi) / \sqrt{N(\mathfrak{f})}$, and the assembly as in `Langlands.Tate.RayClassHecke`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 7 and 8.
-/

open MeasureTheory Module Filter Topology Set Complex
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace Classical nonZeroDivisors

namespace Langlands.Tate

section Isometry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The image $e(L)$ of a lattice $L \subset V$ under a linear isometry $e : V \to W$. -/
noncomputable def mapLattice (e : V ≃ₗᵢ[ℝ] W) (L : Submodule ℤ V) : Submodule ℤ W :=
  ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap

variable (e : V ≃ₗᵢ[ℝ] W) (L : Submodule ℤ V)

/-- A vector $y$ is in $e(L)$ if and only if $e^{-1}(y) \in L$. -/
theorem mem_mapLattice {y : W} : y ∈ mapLattice e L ↔ e.symm y ∈ L := Iff.rfl

/-- The image $e(\ell)$ of a vector $\ell \in L$ is in $e(L)$. -/
theorem apply_mem_mapLattice {x : V} (hx : x ∈ L) : e x ∈ mapLattice e L := by
  rw [mem_mapLattice, LinearIsometryEquiv.symm_apply_apply]
  exact hx

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

/-- The image of a discrete lattice is discrete. -/
instance [DiscreteTopology L] : DiscreteTopology (mapLattice e L) :=
  ZLattice.comap_discreteTopology ℝ L e.symm.toContinuousLinearEquiv.continuous
    e.symm.injective

/-- The image of a full lattice is a full lattice. -/
instance [DiscreteTopology L] [IsZLattice ℝ L] : IsZLattice ℝ (mapLattice e L) :=
  instIsZLatticeComap ℝ L e.symm.toContinuousLinearEquiv

/-- The bijection $L \to e(L)$, $\ell \mapsto e(\ell)$. -/
noncomputable def mapLatticeEquiv : L ≃ mapLattice e L where
  toFun ℓ := ⟨e ℓ, apply_mem_mapLattice e L ℓ.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv ℓ := by ext; simp
  right_inv y := by ext; simp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The vector of `mapLatticeEquiv e L ℓ` is $e(\ell)$. -/
@[simp] theorem coe_mapLatticeEquiv (ℓ : L) : (mapLatticeEquiv e L ℓ : W) = e ℓ := rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The dual lattice of $e(L)$ is $e(L^\vee)$. -/
theorem dualLattice_mapLattice : dualLattice (mapLattice e L) = mapLattice e (dualLattice L) := by
  ext y
  rw [mem_dualLattice, mem_mapLattice, mem_dualLattice]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := h (e x) (apply_mem_mapLattice e L hx)
    refine ⟨n, ?_⟩
    rw [← hn, ← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  · intro h x hx
    obtain ⟨n, hn⟩ := h (e.symm x) hx
    refine ⟨n, ?_⟩
    rw [← hn, ← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]

variable [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]

/-- The covolume of $e(L)$ is the covolume of $L$. -/
theorem covolume_mapLattice [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (mapLattice e L) = ZLattice.covolume L :=
  ZLattice.covolume_comap L volume volume (e := e.symm.toContinuousLinearEquiv)
    e.symm.measurePreserving

end Isometry

section Complex

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The complex place of an imaginary quadratic field. -/
noncomputable def quadPlace (hK : finrank ℚ K = 2) : {w : InfinitePlace K // IsComplex w} :=
  ⟨(Fintype.card_eq_one_iff.1 (card_infinitePlace_of_isQuadratic K hK)).choose,
    IsTotallyComplex.isComplex _⟩

/-- Each infinite place of an imaginary quadratic field is `quadPlace K hK`. -/
theorem eq_quadPlace (hK : finrank ℚ K = 2) (w : InfinitePlace K) : w = (quadPlace K hK).1 :=
  (Fintype.card_eq_one_iff.1 (card_infinitePlace_of_isQuadratic K hK)).choose_spec w

/-- Each complex place of an imaginary quadratic field is `quadPlace K hK`. -/
theorem eq_quadPlace' (hK : finrank ℚ K = 2) (w : {w : InfinitePlace K // IsComplex w}) :
    w = quadPlace K hK :=
  Subtype.ext (eq_quadPlace K hK w.1)

omit [NumberField K] in
/-- An imaginary quadratic field has no real place. -/
theorem isEmpty_isReal : IsEmpty {w : InfinitePlace K // IsReal w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩

/-- The linear isomorphism of the euclidean mixed space of an imaginary quadratic field with $\mathbb{C}$: the coordinate at the complex place. -/
noncomputable def quadLinearEquiv (hK : finrank ℚ K = 2) : euclidean.mixedSpace K ≃ₗ[ℝ] ℂ where
  toFun x := (euclidean.toMixed K x).2 (quadPlace K hK)
  map_add' x y := by simp
  map_smul' r x := by simp
  invFun z := (euclidean.toMixed K).symm (0, fun _ => z)
  left_inv x := by
    refine (euclidean.toMixed K).injective ?_
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ext w
    · exact ((isEmpty_isReal K).false w).elim
    · simp only
      rw [eq_quadPlace' K hK w]
  right_inv z := by simp

/-- The isometry of the euclidean mixed space of an imaginary quadratic field with $\mathbb{C}$: the coordinate at the complex place. -/
noncomputable def quadIsometry (hK : finrank ℚ K = 2) : euclidean.mixedSpace K ≃ₗᵢ[ℝ] ℂ :=
  ⟨quadLinearEquiv K hK, fun x => by
    have h := norm_toMixed_symm_sq K (euclidean.toMixed K x)
    rw [ContinuousLinearEquiv.symm_apply_apply,
      Fintype.sum_eq_zero _ fun w => ((isEmpty_isReal K).false w).elim, zero_add,
      Fintype.sum_eq_single (quadPlace K hK) fun w hw => absurd (eq_quadPlace' K hK w) hw] at h
    have h' := congrArg Real.sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), eq_comm] at h'⟩

/-- The isometry sends the coordinate vector $x$ to its coordinate at the complex place. -/
theorem quadIsometry_apply (hK : finrank ℚ K = 2) (x : euclidean.mixedSpace K) :
    quadIsometry K hK x = (euclidean.toMixed K x).2 (quadPlace K hK) := rfl

/-- The isometry sends $\varphi_c(\alpha)$ to $c_w \sigma_w(\alpha)$, where $w$ is the complex place. -/
theorem quadIsometry_globalEmbedding (hK : finrank ℚ K = 2) (c : InfinitePlace K → ℝ) (α : K) :
    quadIsometry K hK (globalEmbedding K c α) =
      (c (quadPlace K hK) : ℂ) * (quadPlace K hK).1.embedding α := by
  rw [quadIsometry_apply, toMixed_globalEmbedding, mixedScaleₗ_apply_snd,
    mixedEmbedding_apply_isComplex]

/-- The isometry sends $\psi_c(\beta)$ to $c_w \overline{\sigma_w(\beta)}$, where $w$ is the complex place. -/
theorem quadIsometry_globalConjEmbedding (hK : finrank ℚ K = 2) (c : InfinitePlace K → ℝ)
    (β : K) :
    quadIsometry K hK (globalConjEmbedding K c β) =
      (c (quadPlace K hK) : ℂ) * starRingEnd ℂ ((quadPlace K hK).1.embedding β) := by
  rw [quadIsometry_apply, globalConjEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply,
    mixedScaleₗ_apply_snd, mixedConj_apply_snd, mixedEmbedding_apply_isComplex]

/-- For $c_w = \sqrt{n_w}$ the scale at the complex place is $\sqrt 2$. -/
theorem traceScale_quadPlace (hK : finrank ℚ K = 2) :
    (traceScale K (quadPlace K hK) : ℝ) = √2 := by
  simp [traceScale, thetaScale, IsTotallyComplex.mult_eq]

/-- The lattice $\sqrt 2 \, \sigma(\mathfrak{a}) \subset \mathbb{C}$ of a nonzero fractional ideal $\mathfrak{a}$: the image of `Langlands.Tate.traceLattice` under `quadIsometry`. -/
noncomputable abbrev quadLattice (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ ℂ :=
  mapLattice (quadIsometry K hK) (traceLattice K a)

/-- The embedding $\alpha \mapsto \sqrt 2 \, \sigma(\alpha)$ of $K$ in $\mathbb{C}$, where $\sigma$ is the embedding of the complex place. -/
noncomputable def quadEmbed (hK : finrank ℚ K = 2) : K →+ ℂ :=
  (quadIsometry K hK).toLinearEquiv.toAddMonoidHom.comp
    (globalEmbedding K fun w => (traceScale K w : ℝ))

/-- The value of the embedding is $\sqrt 2 \, \sigma(\alpha)$. -/
theorem quadEmbed_apply (hK : finrank ℚ K = 2) (α : K) :
    quadEmbed K hK α = ((√2 : ℝ) : ℂ) * (quadPlace K hK).1.embedding α := by
  rw [quadEmbed, AddMonoidHom.comp_apply]
  exact (quadIsometry_globalEmbedding K hK _ α).trans (by rw [traceScale_quadPlace])

/-- The embedding $\alpha \mapsto \sqrt 2 \, \sigma(\alpha)$ is injective. -/
theorem quadEmbed_injective (hK : finrank ℚ K = 2) : Function.Injective (quadEmbed K hK) :=
  (quadIsometry K hK).injective.comp (globalEmbedding_injective K (traceScale K))

/-- The image of $\alpha$ is $0$ if and only if $\alpha = 0$. -/
theorem quadEmbed_eq_zero_iff (hK : finrank ℚ K = 2) {α : K} : quadEmbed K hK α = 0 ↔ α = 0 :=
  (injective_iff_map_eq_zero' _).1 (quadEmbed_injective K hK) α

/-- The isometry sends $\psi(\beta)$ to $\overline{\sqrt 2 \, \sigma(\beta)}$. -/
theorem quadIsometry_globalConjEmbedding_traceScale (hK : finrank ℚ K = 2) (β : K) :
    quadIsometry K hK (globalConjEmbedding K (fun w => (traceScale K w : ℝ)) β) =
      starRingEnd ℂ (quadEmbed K hK β) := by
  rw [quadIsometry_globalConjEmbedding, quadEmbed_apply, traceScale_quadPlace, map_mul,
    Complex.conj_ofReal]

/-- The norm of $\sqrt 2 \, \sigma(\alpha)$ is $\sqrt{2 |N(\alpha)|}$. -/
theorem norm_quadEmbed (hK : finrank ℚ K = 2) (α : K) :
    ‖quadEmbed K hK α‖ = √(2 * |(Algebra.norm ℚ α : ℝ)|) := by
  rw [quadEmbed, AddMonoidHom.comp_apply]
  change ‖quadIsometry K hK _‖ = _
  rw [LinearIsometryEquiv.norm_map, ← sum_mult_sq_eq_of_isQuadratic K hK,
    ← norm_globalEmbedding_traceScale_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The points of `quadLattice K hK a` are the numbers $\sqrt 2 \, \sigma(\alpha)$ with $\alpha \in \mathfrak{a}$. -/
noncomputable def quadLatticeEquiv (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (a : FractionalIdeal (𝓞 K)⁰ K) ≃ quadLattice K hK a :=
  (globalLatticeEquiv K (traceScale K) a).trans (mapLatticeEquiv _ _)

/-- The point of `quadLatticeEquiv` at $\alpha$ is $\sqrt 2 \, \sigma(\alpha)$. -/
@[simp] theorem coe_quadLatticeEquiv (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (α : (a : FractionalIdeal (𝓞 K)⁰ K)) :
    (quadLatticeEquiv K hK a α : ℂ) = quadEmbed K hK α := rfl

/-- The points of the dual lattice of `quadLattice K hK a` are the numbers $\overline{\sqrt 2 \, \sigma(\beta)}$ with $\beta \in \mathfrak{a}^\vee$. -/
noncomputable def quadDualEquiv (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K) ≃ dualLattice (quadLattice K hK a) :=
  ((globalDualEquiv K (traceScale K) a (traceScale K) (traceScale_mul_traceScale K)).trans
    (mapLatticeEquiv (quadIsometry K hK) _)).trans
    (LinearEquiv.ofEq _ _ (dualLattice_mapLattice _ _).symm).toEquiv

/-- The point of `quadDualEquiv` at $\beta$ is $\overline{\sqrt 2 \, \sigma(\beta)}$. -/
theorem coe_quadDualEquiv (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (β : FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K)) :
    (quadDualEquiv K hK a β : ℂ) = starRingEnd ℂ (quadEmbed K hK β) :=
  quadIsometry_globalConjEmbedding_traceScale K hK β

/-- The inner product of $\overline{\sqrt 2 \, \sigma(\beta)}$ and $\sqrt 2 \, \sigma(\xi)$ is the trace $\mathrm{Tr}(\beta \xi)$. -/
theorem inner_conj_quadEmbed (hK : finrank ℚ K = 2) (β ξ : K) :
    ⟪starRingEnd ℂ (quadEmbed K hK β), quadEmbed K hK ξ⟫ = (Algebra.trace ℚ K (β * ξ) : ℝ) := by
  rw [← quadIsometry_globalConjEmbedding_traceScale, quadEmbed, AddMonoidHom.comp_apply]
  change ⟪quadIsometry K hK _, quadIsometry K hK _⟫ = _
  rw [LinearIsometryEquiv.inner_map_map, trace_eq_inner K _ _ (traceScale_mul_traceScale K)]

/-- The covolume of `quadLattice K hK a` is $N(\mathfrak{a}) \sqrt{|d_K|}$. -/
theorem covolume_quadLattice (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (quadLattice K hK a) =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)| := by
  rw [covolume_mapLattice, covolume_traceLattice]

end Complex

section Transfer

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- **The weighted Epstein zeta function of an ideal.** For $\mathrm{Re}\, s > k + 2$ and $\xi \in K$, $\Lambda^k_{\sqrt 2 \sigma(\mathfrak{a})}(\sqrt 2 \sigma(\xi), 0; s)$ is the sum over $\alpha \in \mathfrak{a}$ with $\xi + \alpha \neq 0$ of $\Gamma_\mathbb{R}(s) \overline{\gamma}^k |\gamma|^{-s}$, where $\gamma = \sqrt 2 \, \sigma(\xi + \alpha)$. -/
theorem hasSum_completedWeightZeta_quadLattice (hK : finrank ℚ K = 2) (k : ℕ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ξ : K) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => if ξ + (α : K) = 0 then 0 else
      Complex.Gammaℝ s * ((starRingEnd ℂ (quadEmbed K hK (ξ + α))) ^ k *
        ((‖quadEmbed K hK (ξ + α)‖ : ℝ) : ℂ) ^ (-s)))
      (completedWeightZeta (quadLattice K hK a) k (quadEmbed K hK ξ) 0 s) := by
  have h := hasSum_completedWeightZeta (quadLattice K hK a) k (quadEmbed K hK ξ) 0 hs
  rw [← (quadLatticeEquiv K hK a).hasSum_iff] at h
  refine h.congr_fun fun α => ?_
  simp only [Function.comp_apply, coe_quadLatticeEquiv, ← map_add, quadEmbed_eq_zero_iff,
    inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- **The dual weighted Epstein zeta function of an ideal.** For $\mathrm{Re}\, s > k + 2$ and $\xi \in K$, $\Lambda^k_{(\sqrt 2 \sigma(\mathfrak{a}))^\vee}(0, \sqrt 2 \sigma(\xi); s)$ is the sum over the nonzero $\beta \in \mathfrak{a}^\vee$ of $\Gamma_\mathbb{R}(s) \gamma^k e^{2 \pi i \mathrm{Tr}(\beta \xi)} |\gamma|^{-s}$, where $\gamma = \sqrt 2 \, \sigma(\beta)$. -/
theorem hasSum_completedWeightZeta_dual_quadLattice (hK : finrank ℚ K = 2) (k : ℕ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ξ : K) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun β : FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K) =>
      if (β : K) = 0 then 0 else
      Complex.Gammaℝ s * ((quadEmbed K hK β) ^ k *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((β : K) * ξ) : ℚ) : ℝ)) *
        ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-s)))
      (completedWeightZeta (dualLattice (quadLattice K hK a)) k 0 (quadEmbed K hK ξ) s) := by
  have h := hasSum_completedWeightZeta (dualLattice (quadLattice K hK a)) k 0
    (quadEmbed K hK ξ) hs
  rw [← (quadDualEquiv K hK a).hasSum_iff] at h
  refine h.congr_fun fun β => ?_
  simp only [Function.comp_apply, coe_quadDualEquiv, zero_add, map_eq_zero,
    quadEmbed_eq_zero_iff, Complex.conj_conj, Complex.norm_conj, inner_conj_quadEmbed]

/-- **The functional equation of the weighted Epstein zeta function of an ideal.** For $k \neq 0$ and $\xi \in K$, $$\Lambda^k_{\sqrt 2 \sigma(\mathfrak{a})}(\sqrt 2 \sigma(\xi), 0; 2k + 2 - s) = \frac{(-i)^k}{N(\mathfrak{a}) \sqrt{|d_K|}} \Lambda^k_{(\sqrt 2 \sigma(\mathfrak{a}))^\vee}(0, \sqrt 2 \sigma(\xi); s).$$ -/
theorem completedWeightZeta_quadLattice_sub (hK : finrank ℚ K = 2) {k : ℕ} (hk : k ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ξ : K) (s : ℂ) :
    completedWeightZeta (quadLattice K hK a) k (quadEmbed K hK ξ) 0 (2 * k + 2 - s) =
      (-I) ^ k * (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|)⁻¹ : ℝ) *
        completedWeightZeta (dualLattice (quadLattice K hK a)) k 0 (quadEmbed K hK ξ) s := by
  rw [completedWeightZeta_sub _ hk, covolume_quadLattice, neg_zero, inner_zero_right]
  simp

end Transfer

section Reciprocity

open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Let $S$ be a finite set of finite places that contains the ramified places of $\chi$. For an idele $x$ whose components outside $S$ are units, $\chi(x) = \chi(x_\infty) \prod_{v \in S} \chi_v(x_v)$, where $x_\infty$ is the infinite part of $x$. There is no condition on $\chi$ at the infinite places. -/
theorem ideleChar_eq_infinitePart_mul_prod (χ : HeckeCharacter K) (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, Valued.v ((ideleFin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1)
    (hR : ∀ v ∉ S, χ.IsUnramifiedAt v) :
    ideleChar χ x = ideleChar χ (infinitePart x) * ∏ v ∈ S, χ.finiteComponent v (ideleFin v x) := by
  obtain ⟨T, k, hT⟩ := HeckeRat.Top.exists_trivial_on_units K χ
  set U := S ∪ T with hU
  set A := infinitePart x with hA
  set P : IdeleGroup (𝓞 K) K :=
    ∏ v ∈ U, IdeleGroup.ofAdicCompletion (𝓞 K) K v (ideleFin v x) with hP
  have hPinf : ∀ w, ideleInf w P = 1 := fun w => by
    rw [hP, map_prod]
    exact Finset.prod_eq_one fun v _ => ideleInf_ofAdicCompletion w v _
  have hPfin : ∀ v, ideleFin v P = if v ∈ U then ideleFin v x else 1 := by
    intro v
    rw [hP, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single v (fun w _ hw => ideleFin_ofAdicCompletion_of_ne hw _)
        (fun h => absurd hv h), ideleFin_ofAdicCompletion_self]
    · exact Finset.prod_eq_one fun w hw =>
        ideleFin_ofAdicCompletion_of_ne (ne_of_mem_of_not_mem hw hv) _
  set z : IdeleGroup (𝓞 K) K := x * A⁻¹ * P⁻¹ with hz
  have hzinf : ∀ w, ideleInf w z = 1 := fun w => by
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, ideleInf_infinitePart, hPinf]
    simp
  have hzfin : ∀ v, ideleFin v z = if v ∈ U then 1 else ideleFin v x := fun v => by
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, ideleFin_infinitePart, hPfin]
    split_ifs <;> simp
  have hz1 : ideleChar χ z = 1 := by
    refine hT z ?_ (fun v => ?_) (fun v hv => ?_)
    · funext w
      exact congrArg Units.val (hzinf w)
    · rw [← coe_ideleFin, hzfin]
      split_ifs with hv
      · simp
      · exact hS v fun h => hv (Finset.mem_union_left _ h)
    · rw [← coe_ideleFin, hzfin, ite_eq_left (Finset.mem_union_right _ hv)]
      simp
  have hxz : x = z * A * P := by
    rw [hz, mul_right_comm _ P⁻¹ A, inv_mul_cancel_right, inv_mul_cancel_right]
  rw [show ideleChar χ x = ideleChar χ z * ideleChar χ A * ideleChar χ P by
      rw [← map_mul, ← map_mul, ← hxz],
    hz1, one_mul, hP, map_prod]
  simp only [ideleChar_ofAdicCompletion]
  rw [hU]
  exact congrArg _ (Finset.prod_subset Finset.subset_union_left fun v _ hv =>
    finiteComponent_eq_one_of_isUnramifiedAt (hR v hv) (hS v hv)).symm

/-- **Reciprocity with an infinite factor.** Let $\chi$ have conductor $\mathfrak{f} = \prod_v \mathfrak{p}_v^{a_v}$. If $x \in K^\times$ satisfies $v(x - 1) \geq a_v$ at each ramified place $v$, then $\chi_{\mathrm{id}}((x)) \chi(x_\infty) = 1$, where $x_\infty$ is the image of $x$ in the infinite part of the ideles. There is no condition on $\chi$ at the infinite places. -/
theorem idealChar_toPrincipalIdeal_mul_infinitePart (χ : HeckeCharacter K) (x : Kˣ)
    (hx : ∀ v ∈ ramifiedSet χ, Valued.v (algebraMap K (v.adicCompletion K) (x : K) - 1) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ))) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K x) *
      ideleChar χ (infinitePart (IdeleGroup.unitEmbedding (𝓞 K) K x)) = 1 := by
  have hfin := Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = WithZero.exp
          (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) :=
    fun v => by rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count]
  have hunit : ∀ v ∈ ramifiedSet χ,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    have ha : χ.conductorExponent v ≠ 0 :=
      fun h => mem_ramifiedSet.1 hv ((conductorExponent_eq_zero_iff χ v).1 h)
    have hlt : Valued.v (algebraMap K (v.adicCompletion K) (x : K) - 1) < Valued.v
        (1 : v.adicCompletion K) := by
      rw [map_one]
      refine (hx v hv).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h := Valuation.map_add_eq_of_lt_left Valued.v hlt
    rwa [add_sub_cancel, map_one] at h
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 :=
    fun v hv => by
      have h := (hval v).symm.trans (hunit v hv)
      rw [← WithZero.exp_zero] at h
      exact neg_eq_zero.1 (WithZero.exp_injective h)
  set S := hfin.toFinset ∪ ramifiedSet χ with hSdef
  have hS : ∀ v ∉ S,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    rw [hval, show FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0
      by simpa using fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h)),
      neg_zero, WithZero.exp_zero]
  have hR : ∀ v ∉ S, χ.IsUnramifiedAt v := fun v hv =>
    not_not.1 fun h => hv (Finset.mem_union_right _ (mem_ramifiedSet.2 h))
  have h := ideleChar_eq_infinitePart_mul_prod χ _ S hS hR
  rw [ideleChar_unitEmbedding] at h
  rw [idealChar_apply, coe_toPrincipalIdeal, finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · rw [mul_comm, h]
    refine congrArg _ (Finset.prod_congr rfl fun v _ => ?_)
    by_cases hv : v ∈ ramifiedSet χ
    · rw [hcount v hv, zpow_zero]
      have ht : χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) :=
        Nat.sInf_mem (NonArchimedean.exists_isTrivialOnHigherUnits v χ)
      refine (ht _ (hunit v hv) ?_).symm
      rw [ideleFin_unitEmbedding]
      exact hx v hv
    · rw [finiteComponent_eq_zpow_of_isUnramifiedAt (not_not.1 (mt mem_ramifiedSet.2 hv)), hval,
        WithZero.log_exp, neg_neg]
  · intro v hv
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl fun h0 => hv (by simp only [h0, zpow_zero])

/-- The infinite part of an idele has character value $\chi(x_\infty) = \prod_w \chi_w(x_w)$. -/
theorem ideleChar_infinitePart_eq_prod (χ : HeckeCharacter K) (x : IdeleGroup (𝓞 K) K) :
    ideleChar χ (infinitePart x) = ∏ w : InfinitePlace K, χ.infiniteComponent w (ideleInf w x) := by
  rw [infinitePart, map_prod]
  rfl

/-- The component at an infinite place $w$ of the idele of $x \in K^\times$ maps to $\iota_w(x)$ under the embedding of the completion. -/
theorem extensionEmbedding_ideleInf_unitEmbedding (w : InfinitePlace K) (x : Kˣ) :
    InfinitePlace.Completion.extensionEmbedding w
      (ideleInf w (IdeleGroup.unitEmbedding (𝓞 K) K x) : w.Completion) = w.embedding x := by
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

/-- The infinite type of $\chi$ on $K^\times$: the character $x \mapsto \chi(x_\infty) = \prod_w \chi_w(x)$, where $x_\infty$ is the infinite part of the idele of $x$. -/
noncomputable def infChar (χ : HeckeCharacter K) : Kˣ →* ℂˣ where
  toFun x := ideleChar χ (infinitePart (IdeleGroup.unitEmbedding (𝓞 K) K x))
  map_one' := by simp [ideleChar_infinitePart_eq_prod]
  map_mul' x y := by
    simp only [ideleChar_infinitePart_eq_prod, map_mul, Finset.prod_mul_distrib]

/-- The value of the infinite type is $\chi(x_\infty)$. -/
theorem infChar_apply (χ : HeckeCharacter K) (x : Kˣ) :
    infChar χ x = ideleChar χ (infinitePart (IdeleGroup.unitEmbedding (𝓞 K) K x)) := rfl

/-- **Reciprocity for the ideal character and the infinite type.** Let $x, y \in K^\times$ with $v(y - x) \geq a_v + v(x)$ at each ramified place $v$, where $a_v$ is the exponent of the conductor. Then $\chi_{\mathrm{id}}((y)) \chi_\infty(y) = \chi_{\mathrm{id}}((x)) \chi_\infty(x)$. -/
theorem idealChar_mul_infChar_eq (χ : HeckeCharacter K) (x y : Kˣ)
    (h : ∀ v ∈ ramifiedSet χ, v.valuation K ((y : K) - x) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ)) * v.valuation K (x : K)) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K y) * infChar χ y =
      idealChar χ (toPrincipalIdeal (𝓞 K) K x) * infChar χ x := by
  have key := idealChar_toPrincipalIdeal_mul_infinitePart χ (y * x⁻¹) fun v hv => by
    have hx0 : v.valuation K (x : K) ≠ 0 := by simp
    rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, valued_algebraMap,
      Units.val_mul, show (y : K) * ((x⁻¹ : Kˣ) : K) - 1 = ((y : K) - x) * (x : K)⁻¹ by
        rw [Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ x.ne_zero], map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hx0)).2 (h v hv)
  rw [← infChar_apply] at key
  simp only [map_mul, map_inv] at key
  rw [← mul_inv_eq_one, ← key, mul_inv]
  ac_rfl

/-- **Units with trivial ideal.** For a unit $\varepsilon$ of $\mathcal{O}_K$ with $v(\varepsilon - 1) \geq a_v$ at each ramified place $v$, the infinite type is trivial: $\chi_\infty(\varepsilon) = 1$. -/
theorem infChar_unit_eq_one (χ : HeckeCharacter K) (u : (𝓞 K)ˣ)
    (hu : ∀ v ∈ ramifiedSet χ, Valued.v (algebraMap K (v.adicCompletion K) (u : K) - 1) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ))) :
    infChar χ (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 := by
  have h := idealChar_toPrincipalIdeal_mul_infinitePart χ
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) hu
  rwa [show toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 by
    rw [toPrincipalIdeal_eq_iff, Units.val_one, ← map_one (FractionalIdeal.spanSingleton _),
      FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]
    change algebraMap (𝓞 K) K _ * algebraMap (𝓞 K) K _ = 1
    rw [← map_mul, Units.inv_mul, map_one], map_one, one_mul, ← infChar_apply] at h

end Reciprocity

section QuadraticInfinite

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] {χ : HeckeCharacter K}

/-- **The infinite type of an imaginary quadratic field.** Let $\sigma$ be the embedding of the complex place. If $\chi$ has parameters $(n, t)$ at this place, then $\chi_\infty(x) = (\sigma(x) / |\sigma(x)|)^n |\sigma(x)|^{2t}$. -/
theorem infChar_apply_of_isArchimedeanParameter (hK : finrank ℚ K = 2) {n : ℤ} {t : ℂ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 n t) (x : Kˣ) :
    (infChar χ x : ℂ) = ((quadPlace K hK).1.embedding x /
        (‖(quadPlace K hK).1.embedding x‖ : ℂ)) ^ n *
      (‖(quadPlace K hK).1.embedding x‖ : ℂ) ^ (2 * t) := by
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Finset.prod_eq_single (quadPlace K hK).1
    (fun w _ hw => absurd (eq_quadPlace K hK w) hw) (fun h => absurd (Finset.mem_univ _) h),
    h.eq, extensionEmbedding_ideleInf_unitEmbedding, mult_isComplex (quadPlace K hK)]
  norm_num

/-- For a unit $\varepsilon$ of the ring of integers of an imaginary quadratic field, $|\sigma(\varepsilon)| = 1$. -/
theorem norm_quadPlace_unit (hK : finrank ℚ K = 2) (u : (𝓞 K)ˣ) :
    ‖(quadPlace K hK).1.embedding (u : K)‖ = 1 := by
  have h := prod_eq_abs_norm (u : K)
  rw [NumberField.Units.norm, Finset.prod_eq_single (quadPlace K hK).1
    (fun w _ hw => absurd (eq_quadPlace K hK w) hw) (fun h => absurd (Finset.mem_univ _) h),
    mult_isComplex (quadPlace K hK), Rat.cast_one] at h
  rw [norm_embedding_eq]
  exact (pow_eq_one_iff_of_nonneg (apply_nonneg _ _) two_ne_zero).1 h

/-- **Units in an imaginary quadratic field.** Let $\chi$ have parameters $(n, t)$ at the complex place. For a unit $\varepsilon$ of $\mathcal{O}_K$ with $\varepsilon \equiv 1$ modulo the conductor, $\sigma(\varepsilon)^n = 1$. -/
theorem quadPlace_unit_zpow_eq_one (hK : finrank ℚ K = 2) {n : ℤ} {t : ℂ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 n t) (u : (𝓞 K)ˣ)
    (hu : ∀ v ∈ ramifiedSet χ, Valued.v (algebraMap K (v.adicCompletion K) (u : K) - 1) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ))) :
    (quadPlace K hK).1.embedding (u : K) ^ n = 1 := by
  have h1 := congrArg Units.val (infChar_unit_eq_one χ u hu)
  rw [infChar_apply_of_isArchimedeanParameter K hK h] at h1
  have hn := norm_quadPlace_unit K hK u
  change ((quadPlace K hK).1.embedding (u : K) / (‖(quadPlace K hK).1.embedding (u : K)‖ : ℂ)) ^ n *
    (‖(quadPlace K hK).1.embedding (u : K)‖ : ℂ) ^ (2 * t) = 1 at h1
  rw [hn] at h1
  simpa using h1

end QuadraticInfinite

section PeriodicCoeff

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The periodic coefficient of the class of $J^{-1}$: for $\alpha \in K^\times$ that satisfies the condition of `Langlands.Tate.rayCoeff`, it is $\chi_{\mathrm{id}}((\alpha) J^{-1}) \chi_\infty(\alpha)$, and it is $0$ for the other $\alpha$. When $\chi$ is of ray class type it is `Langlands.Tate.rayCoeff`. -/
noncomputable def periodicCoeff (χ : HeckeCharacter K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ℂ :=
  if h : α ≠ 0 then rayCoeff χ J α * (infChar χ (Units.mk0 α h) : ℂ) else 0

/-- **The coefficient and the periodic coefficient.** For $\alpha \neq 0$, the coefficient $\chi((\alpha) J^{-1})$ of the partial $L$-series is the periodic coefficient times $\chi_\infty(\alpha)^{-1}$. -/
theorem rayCoeff_eq_periodicCoeff_mul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K} (hα : α ≠ 0) :
    rayCoeff χ J α = periodicCoeff χ J α * (((infChar χ (Units.mk0 α hα))⁻¹ : ℂˣ) : ℂ) := by
  rw [periodicCoeff, dite_eq_left hα, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_one]

/-- The periodic coefficient is $0$ when $\alpha$ does not satisfy the condition of `Langlands.Tate.rayCoeff`. -/
theorem periodicCoeff_eq_zero_of_not (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K}
    (hα : ¬ (α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K))) :
    periodicCoeff χ J α = 0 := by
  rw [periodicCoeff]
  split_ifs with h0
  · rw [rayCoeff, dite_eq_right hα, zero_mul]
  · rfl

/-- The value of the periodic coefficient at $\alpha$ that satisfies the condition of `Langlands.Tate.rayCoeff`. -/
theorem periodicCoeff_of_cond (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K}
    (hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) :
    periodicCoeff χ J α = ((idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 α hα.1)) *
      infChar χ (Units.mk0 α hα.1) * (idealChar χ J)⁻¹ : ℂˣ) : ℂ) := by
  rw [periodicCoeff, dite_eq_left hα.1, rayCoeff, dite_eq_left hα, ← Units.val_mul, mul_right_comm]

/-- If $\alpha$ satisfies the condition of `Langlands.Tate.rayCoeff` and $\alpha - \beta \in \mathfrak{f} J$, then $\beta$ satisfies it, and $\chi_{\mathrm{id}}((\beta)) \chi_\infty(\beta) = \chi_{\mathrm{id}}((\alpha)) \chi_\infty(\alpha)$. This needs one ramified place. There is no condition on $\chi$ at the infinite places. -/
theorem periodicCoeff_cond_of_sub_mem (hS : (ramifiedSet χ).Nonempty)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α β : K}
    (h : α - β ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K))
    (hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ hβ : β ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K),
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 β hβ.1)) * infChar χ (Units.mk0 β hβ.1) =
        idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 α hα.1)) *
          infChar χ (Units.mk0 α hα.1) := by
  have hva : ∀ v ∈ ramifiedSet χ, v.valuation K α =
      WithZero.exp (-FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := fun v hv => by
    have h1 := valuation_eq_exp_neg_count v (Units.mk0 _ hα.1)
    rw [Units.val_mk0] at h1
    rw [h1, hα.2 v hv]
  have hlt : ∀ v ∈ ramifiedSet χ, v.valuation K (β - α) < v.valuation K α := fun v hv => by
    rw [Valuation.map_sub_swap, hva v hv]
    refine (valuation_sub_le χ J h v).trans_lt ?_
    have ha : χ.conductorExponent v ≠ 0 :=
      fun h0 => mem_ramifiedSet.1 hv ((conductorExponent_eq_zero_iff χ v).1 h0)
    rw [← WithZero.exp_add, WithZero.exp_lt_exp]
    omega
  have hvβ : ∀ v ∈ ramifiedSet χ, v.valuation K β = v.valuation K α := fun v hv => by
    have := Valuation.map_add_eq_of_lt_left _ (hlt v hv)
    rwa [add_sub_cancel] at this
  obtain ⟨v₀, hv₀⟩ := hS
  have hβ0 : β ≠ 0 := fun h0 => by
    have := hvβ v₀ hv₀
    rw [h0, map_zero, hva v₀ hv₀] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨⟨hβ0, fun v hv' => ?_⟩, ?_⟩
  · have h1 := valuation_eq_exp_neg_count v (Units.mk0 _ hβ0)
    rw [Units.val_mk0, hvβ v hv', hva v hv'] at h1
    exact neg_injective (WithZero.exp_injective h1).symm
  · refine idealChar_mul_infChar_eq χ _ _ fun v hv' => ?_
    rw [Units.val_mk0, Units.val_mk0, Valuation.map_sub_swap, hva v hv', ← hα.2 v hv']
    have := valuation_sub_le χ J h v
    rwa [← hα.2 v hv'] at this

/-- **Periodicity of the periodic coefficient.** If $\chi$ is ramified at one place and $\alpha - \beta \in \mathfrak{f} J$, then the periodic coefficients of $\alpha$ and $\beta$ are equal. There is no condition on $\chi$ at the infinite places. -/
theorem periodicCoeff_eq_of_sub_mem (hS : (ramifiedSet χ).Nonempty)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α β : K}
    (h : α - β ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) :
    periodicCoeff χ J α = periodicCoeff χ J β := by
  have h' : β - α ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← neg_sub]
    exact Submodule.neg_mem _ h
  by_cases hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · obtain ⟨hβ, he⟩ := periodicCoeff_cond_of_sub_mem hS J h hα
    rw [periodicCoeff_of_cond J hα, periodicCoeff_of_cond J hβ, he]
  · by_cases hβ : β ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) =
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
    · exact absurd (periodicCoeff_cond_of_sub_mem hS J h' hβ).1 hα
    · rw [periodicCoeff_eq_zero_of_not J hα, periodicCoeff_eq_zero_of_not J hβ]

/-- If $\chi$ is ramified at one place, the periodic coefficient is $0$ on $\mathfrak{f} J$. -/
theorem periodicCoeff_eq_zero_of_mem (hS : (ramifiedSet χ).Nonempty)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K}
    (h : α ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) :
    periodicCoeff χ J α = 0 := by
  rw [periodicCoeff_eq_of_sub_mem hS J (β := 0) (by rwa [sub_zero]), periodicCoeff, dite_eq_right]
  exact fun h0 => h0 rfl

/-- **The periodic coefficient under the units.** For a unit $\varepsilon$ of $\mathcal{O}_K$, the periodic coefficient of $\varepsilon \alpha$ is $\chi_\infty(\varepsilon)$ times the periodic coefficient of $\alpha$. -/
theorem periodicCoeff_unit_mul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (α : K) :
    periodicCoeff χ J ((u : K) * α) =
      (infChar χ (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℂ) * periodicCoeff χ J α := by
  set ε : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u with hε
  have hεK : (ε : K) = (u : K) := rfl
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * α) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ α := by
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def, ← mul_assoc]
    change algebraMap (𝓞 K) K _ * algebraMap (𝓞 K) K _ * α = α
    rw [← map_mul, Units.inv_mul, map_one, one_mul]
  have hiff : ((u : K) * α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * α)) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) ↔ (α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := by
    rw [hspan, mul_ne_zero_iff, and_assoc, and_iff_right (by simp)]
  by_cases hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · have huα := hiff.2 hα
    have hmk : Units.mk0 ((u : K) * α) huα.1 = ε * Units.mk0 α hα.1 := Units.ext rfl
    have hP : toPrincipalIdeal (𝓞 K) K ε = 1 := by
      rw [toPrincipalIdeal_eq_iff, Units.val_one, ← map_one (FractionalIdeal.spanSingleton _),
        FractionalIdeal.spanSingleton_eq_spanSingleton]
      refine ⟨u⁻¹, ?_⟩
      rw [Units.smul_def, Algebra.smul_def]
      change algebraMap (𝓞 K) K _ * algebraMap (𝓞 K) K _ = 1
      rw [← map_mul, Units.inv_mul, map_one]
    rw [periodicCoeff_of_cond J huα, periodicCoeff_of_cond J hα, hmk, map_mul, map_mul, map_mul,
      hP, map_one, one_mul, ← Units.val_mul]
    congr 1
    ac_rfl
  · rw [periodicCoeff_eq_zero_of_not J hα, periodicCoeff_eq_zero_of_not J (mt hiff.1 hα),
      mul_zero]

end PeriodicCoeff

section QuadraticCoeff

open scoped ComplexConjugate

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] {χ : HeckeCharacter K}

/-- For $z \neq 0$, $(z / |z|)^{-1} = \bar z / |z|$. -/
theorem inv_div_norm {z : ℂ} (hz : z ≠ 0) : (z / (‖z‖ : ℂ))⁻¹ = conj z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [inv_div, div_eq_div_iff hz hn, mul_comm (conj z), Complex.mul_conj', sq]

/-- **The coefficient for an imaginary quadratic field.** Let $\sigma$ be the embedding of the complex place and let $\chi$ have parameters $(n, t)$ there. For $\alpha \neq 0$, the coefficient of the partial $L$-series is $$\chi((\alpha) J^{-1}) = c_J(\alpha) \Big(\frac{\overline{\sigma(\alpha)}}{|\sigma(\alpha)|}\Big)^n |\sigma(\alpha)|^{-2t},$$ where $c_J$ is the periodic coefficient. -/
theorem rayCoeff_eq_periodicCoeff_mul_quad (hK : finrank ℚ K = 2) {n : ℤ} {t : ℂ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 n t) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {α : K} (hα : α ≠ 0) :
    rayCoeff χ J α = periodicCoeff χ J α *
      ((conj ((quadPlace K hK).1.embedding α) / (‖(quadPlace K hK).1.embedding α‖ : ℂ)) ^ n *
        (‖(quadPlace K hK).1.embedding α‖ : ℂ) ^ (-(2 * t))) := by
  have hz : (quadPlace K hK).1.embedding α ≠ 0 := by simpa using hα
  rw [rayCoeff_eq_periodicCoeff_mul J hα, Units.val_inv_eq_inv_val,
    infChar_apply_of_isArchimedeanParameter K hK h, Units.val_mk0, mul_inv, ← inv_zpow,
    inv_div_norm hz, Complex.cpow_neg]

end QuadraticCoeff

end Langlands.Tate
