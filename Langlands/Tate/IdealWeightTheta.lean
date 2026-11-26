/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.MixedWeightTheta

/-!
# The weighted theta series of a fractional ideal

Let $K$ be a number field with $r_1$ real places and $r_2$ complex places, let $n_w$ be $1$ at a real place and $2$ at a complex place, and let $\mathfrak{d}$ be the different ideal of $K$. For nonzero real numbers $c = (c_w)_w$ let $\varphi_c(x) = (c_w \sigma_w(x))_w$ and $\psi_c(x) = (c_w \overline{\sigma_w(x)})_w$ be the two embeddings of `Langlands.Tate.GlobalLattice` in the euclidean mixed space $E = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$. Let $c'_w = n_w / c_w$. This file transfers the transformation formula `Langlands.Tate.mixedTheta_eq` of the weighted theta series on $E$ to the lattice $\varphi_c(\mathfrak{a})$ of a nonzero fractional ideal $\mathfrak{a}$. For $\xi, \eta \in K$ and $t_w > 0$ it gives $$\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)} = \frac{c_t^{p, k} e^{2 \pi i \mathrm{Tr}(\xi \eta)}}{\prod_w |c_w|^{n_w} N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}} \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_{1/t}^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}.$$ For $c = 1$ the lattice is $\sigma(\mathfrak{a})$, and the dual embedding $\psi_{c'}$ multiplies the conjugate coordinates at the complex places by $2$ through `Langlands.Tate.mixedScaleₗ`. This is the third step of Hecke's proof of the functional equation of the Hecke $L$-functions of a general number field.

## Main definitions

* `Langlands.Tate.dualScale`: the scaling constants $c'_w = n_w / c_w$.
* `Langlands.Tate.dualIdeal`: the fractional ideal $(\mathfrak{a} \mathfrak{d})^{-1}$.
* `Langlands.Tate.idealDualEquiv`: the bijection $(\mathfrak{a} \mathfrak{d})^{-1} \to \varphi_c(\mathfrak{a})^\vee$, $\beta \mapsto \psi_{c'}(\beta)$.
* `Langlands.Tate.idealTheta`: the theta series $\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)}$.
* `Langlands.Tate.idealDualTheta`: the theta series $\sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_t^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}$.

## Main results

* `covolume_globalLattice_one` and `covolume_dualLattice_globalLattice`: $\mathrm{covol}(\sigma(\mathfrak{a})) = N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}$, and $\mathrm{covol}(\varphi_c(\mathfrak{a})^\vee) = (\prod_w |c_w|^{n_w} N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$.
* `mem_dualLattice_globalLattice_iff` and `coe_dualLattice_globalLattice`: the dual lattice of $\varphi_c(\mathfrak{a})$ is $\psi_{c'}((\mathfrak{a} \mathfrak{d})^{-1})$.
* `toMixed_globalConjEmbedding_dualScale_one`: for $c = 1$, $\psi_{c'}(\beta) = D_n \overline{\sigma(\beta)}$, with the factor $n_w$ at each place.
* `mixedGaussWeight_globalEmbedding` and `mixedGaussWeight_globalConjEmbedding`: $G_t^{p, k}$ at $\varphi_c(x)$ and at $\psi_c(x)$ in terms of the embeddings $\sigma_w$.
* `mixedTheta_globalLattice` and `mixedTheta_dualLattice_globalLattice`: the theta series of `Langlands.Tate.MixedWeightTheta` of the two lattices are `idealTheta` and `idealDualTheta`.
* `idealTheta_eq`: the transformation formula above.
* `idealTheta_one_eq`: the same formula for $c = 1$, with the factor $(N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$.

## Proofs

The lattice $\varphi_c(\mathfrak{a})$ is `Langlands.Tate.globalLattice`, and its covolume is `Langlands.Tate.covolume_globalLattice`. Since $c_w c'_w = n_w$, `Langlands.Tate.mem_dualLattice_globalLattice` gives the dual lattice as $\psi_{c'}(\mathfrak{a}^\vee)$, and `Langlands.Tate.dual_eq_inv_mul_different` gives $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$. The inner products become traces by `Langlands.Tate.trace_eq_inner`. The formula is `Langlands.Tate.mixedTheta_eq` for $x = \varphi_c(\xi)$ and $y = \psi_{c'}(\eta)$, reindexed by the bijections $\mathfrak{a} \to \varphi_c(\mathfrak{a})$ and $(\mathfrak{a} \mathfrak{d})^{-1} \to \varphi_c(\mathfrak{a})^\vee$.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt K` for a general number field. The Mellin transform in the variables $t_w$, the integration over the unit group, the weighted Gauss sums, the sum over the ideal classes and the assembly are still open, as in `Langlands.Tate.MixedWeightTheta`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 7 and 8.
-/

open MeasureTheory Module Complex
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace nonZeroDivisors Classical

namespace Langlands.Tate

variable (K : Type*) [Field K] [NumberField K]

section Lattice

/-- The scaling constants $c'_w = n_w / c_w$ of the dual embedding. With them $c_w c'_w = n_w$ for each place $w$. -/
noncomputable def dualScale (c : InfinitePlace K → ℝˣ) : InfinitePlace K → ℝˣ :=
  fun w => Units.mk0 ((mult w : ℝ) / c w)
    (div_ne_zero (Nat.cast_ne_zero.2 mult_pos.ne') (c w).ne_zero)

omit [NumberField K] in
/-- The value of the dual scaling constant is $c'_w = n_w / c_w$. -/
@[simp]
theorem coe_dualScale (c : InfinitePlace K → ℝˣ) (w : InfinitePlace K) :
    (dualScale K c w : ℝ) = (mult w : ℝ) / c w := rfl

omit [NumberField K] in
/-- The constants satisfy $c_w c'_w = n_w$. -/
theorem mul_dualScale (c : InfinitePlace K → ℝˣ) (w : InfinitePlace K) :
    (c w : ℝ) * dualScale K c w = mult w := by
  rw [coe_dualScale, mul_div_cancel₀ _ (c w).ne_zero]

omit [NumberField K] in
/-- For $c = 1$ the dual constants are $c'_w = n_w$. So $c'_w = 2$ at a complex place. -/
theorem coe_dualScale_one (w : InfinitePlace K) : (dualScale K 1 w : ℝ) = mult w := by
  simp

/-- The fractional ideal $(\mathfrak{a} \mathfrak{d})^{-1}$, where $\mathfrak{d}$ is the different ideal of $K$. -/
noncomputable abbrev dualIdeal (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K :=
  ((a : FractionalIdeal (𝓞 K)⁰ K) * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹

variable (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The covolume of the lattice $\sigma(\mathfrak{a})$, that is $\varphi_c(\mathfrak{a})$ for $c = 1$, is $N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}$. -/
theorem covolume_globalLattice_one :
    ZLattice.covolume (globalLattice K 1 a) =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)| := by
  rw [covolume_globalLattice]
  simp

/-- The covolume of the dual lattice of $\varphi_c(\mathfrak{a})$ is $(\prod_w |c_w|^{n_w} N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$. -/
theorem covolume_dualLattice_globalLattice :
    ZLattice.covolume (dualLattice (globalLattice K c a)) =
      ((∏ w, |(c w : ℝ)| ^ mult w) *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|))⁻¹ := by
  rw [covolume_dualLattice, covolume_globalLattice]

/-- **The dual lattice of an ideal.** A vector $y$ is in the dual lattice of $\varphi_c(\mathfrak{a})$ if and only if $y = \psi_{c'}(\beta)$ for some $\beta \in (\mathfrak{a} \mathfrak{d})^{-1}$, where $c'_w = n_w / c_w$. -/
theorem mem_dualLattice_globalLattice_iff {y : euclidean.mixedSpace K} :
    y ∈ dualLattice (globalLattice K c a) ↔
      ∃ β ∈ dualIdeal K a, globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) β = y := by
  rw [mem_dualLattice_globalLattice K c a (dualScale K c) (mul_dualScale K c),
    dual_eq_inv_mul_different]

/-- **The dual lattice of an ideal as a set.** The dual lattice of $\varphi_c(\mathfrak{a})$ is the image $\psi_{c'}((\mathfrak{a} \mathfrak{d})^{-1})$. -/
theorem coe_dualLattice_globalLattice :
    (dualLattice (globalLattice K c a) : Set (euclidean.mixedSpace K)) =
      globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) '' (dualIdeal K a : Set K) := by
  ext y
  rw [SetLike.mem_coe, mem_dualLattice_globalLattice_iff]
  rfl

/-- For $c = 1$ the dual embedding is $\psi_{c'}(\beta) = D_n \overline{\sigma(\beta)}$ in the coordinates of the mixed space, where $D_n$ multiplies the coordinate at $w$ by $n_w$. -/
theorem toMixed_globalConjEmbedding_dualScale_one (β : K) :
    euclidean.toMixed K (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) =
      mixedScaleₗ K (fun w => (mult w : ℝ)) (mixedConj K (mixedEmbedding K β)) := by
  rw [globalConjEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply]
  congr
  funext w
  exact coe_dualScale_one K w

/-- The bijection $(\mathfrak{a} \mathfrak{d})^{-1} \to \varphi_c(\mathfrak{a})^\vee$, $\beta \mapsto \psi_{c'}(\beta)$. -/
noncomputable def idealDualEquiv : dualIdeal K a ≃ dualLattice (globalLattice K c a) :=
  (Equiv.subtypeEquivRight fun β => by rw [dual_eq_inv_mul_different]).trans
    (globalDualEquiv K c a (dualScale K c) (mul_dualScale K c))

/-- The bijection `idealDualEquiv` sends $\beta$ to $\psi_{c'}(\beta)$. -/
@[simp]
theorem coe_idealDualEquiv (β : dualIdeal K a) :
    (idealDualEquiv K c a β : euclidean.mixedSpace K) =
      globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) β := rfl

/-- The trace form as an inner product: $\langle \psi_{c'}(\beta), \varphi_c(\alpha) \rangle = \mathrm{Tr}(\beta \alpha)$. -/
theorem inner_globalConjEmbedding_dualScale (β α : K) :
    ⟪globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) β,
      globalEmbedding K (fun w => (c w : ℝ)) α⟫ = (Algebra.trace ℚ K (β * α) : ℝ) :=
  trace_eq_inner K _ _ (mul_dualScale K c) β α

end Lattice

section Theta

variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The weight at $\varphi_c(x)$ is $G_t^{p, k}(\varphi_c(x)) = \prod_v g_{p_v, t_v}(c_v \sigma_v(x)) \prod_w \overline{c_w \sigma_w(x)}^{k_w} e^{-\pi t_w |c_w \sigma_w(x)|^2}$, with $g_{p, t}(r) = r^p e^{-\pi t r^2}$. -/
theorem mixedGaussWeight_globalEmbedding (c t : InfinitePlace K → ℝ) (x : K) :
    mixedGaussWeight p k t (globalEmbedding K c x) =
      (∏ v, realGaussWeight (p v) (t v) (c v * embedding_of_isReal v.2 x)) *
        ∏ w, gaussWeight (k w) (t w) ((c w : ℂ) * w.1.embedding x) := by
  simp only [mixedGaussWeight, toMixed_globalEmbedding, mixedScaleₗ_apply_fst,
    mixedScaleₗ_apply_snd, mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex]

/-- The weight at $\psi_c(x)$ is $G_t^{p, k}(\psi_c(x)) = \prod_v g_{p_v, t_v}(c_v \sigma_v(x)) \prod_w \overline{c_w \overline{\sigma_w(x)}}^{k_w} e^{-\pi t_w |c_w \sigma_w(x)|^2}$, with $g_{p, t}(r) = r^p e^{-\pi t r^2}$. -/
theorem mixedGaussWeight_globalConjEmbedding (c t : InfinitePlace K → ℝ) (x : K) :
    mixedGaussWeight p k t (globalConjEmbedding K c x) =
      (∏ v, realGaussWeight (p v) (t v) (c v * embedding_of_isReal v.2 x)) *
        ∏ w, gaussWeight (k w) (t w) ((c w : ℂ) * starRingEnd ℂ (w.1.embedding x)) := by
  simp only [mixedGaussWeight, globalConjEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply,
    mixedScaleₗ_apply_fst, mixedScaleₗ_apply_snd, mixedConj_apply_fst, mixedConj_apply_snd,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex]

variable (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The weighted theta series of the ideal $\mathfrak{a}$, shifted by $\xi \in K$ and twisted by $\eta \in K$: $$\theta_{\mathfrak{a}, c}^{p, k}(\xi, \eta; t) = \sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)}.$$ -/
noncomputable def idealTheta (t : InfinitePlace K → ℝ) (ξ η : K) : ℂ :=
  ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K),
    mixedGaussWeight p k t (globalEmbedding K (fun w => (c w : ℝ)) (ξ + α)) *
      cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((ξ + α) * η) : ℚ) : ℝ))

/-- The dual weighted theta series over $(\mathfrak{a} \mathfrak{d})^{-1}$: $$\theta_{\mathfrak{a}, c}^{\vee, p, k}(\xi, \eta; t) = \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_t^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)},$$ with $c'_w = n_w / c_w$. -/
noncomputable def idealDualTheta (t : InfinitePlace K → ℝ) (ξ η : K) : ℂ :=
  ∑' β : dualIdeal K a,
    mixedGaussWeight p k t (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) (β - η)) *
      cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (((β : K) - η) * ξ) : ℚ) : ℝ))

/-- The theta series of the lattice $\varphi_c(\mathfrak{a})$ at $x = \varphi_c(\xi)$ and $y = \psi_{c'}(\eta)$ is the theta series of the ideal. -/
theorem mixedTheta_globalLattice (t : InfinitePlace K → ℝ) (ξ η : K) :
    mixedTheta p k (globalLattice K c a) t (globalEmbedding K (fun w => (c w : ℝ)) ξ)
      (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η) =
      idealTheta K p k c a t ξ η := by
  rw [mixedTheta, idealTheta, ← (globalLatticeEquiv K c a).tsum_eq]
  refine tsum_congr fun α => ?_
  rw [coe_globalLatticeEquiv, ← map_add, real_inner_comm, inner_globalConjEmbedding_dualScale,
    mul_comm η]

/-- The theta series of the dual lattice of $\varphi_c(\mathfrak{a})$ at $-\psi_{c'}(\eta)$ and $\varphi_c(\xi)$ is the dual theta series of the ideal. -/
theorem mixedTheta_dualLattice_globalLattice (t : InfinitePlace K → ℝ) (ξ η : K) :
    mixedTheta p k (dualLattice (globalLattice K c a)) t
      (-globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
      (globalEmbedding K (fun w => (c w : ℝ)) ξ) =
      idealDualTheta K p k c a t ξ η := by
  rw [mixedTheta, idealDualTheta, ← (idealDualEquiv K c a).tsum_eq]
  refine tsum_congr fun β => ?_
  rw [coe_idealDualEquiv, neg_add_eq_sub, ← map_sub, inner_globalConjEmbedding_dualScale]

/-- **The transformation formula of the weighted theta series of an ideal.** Let $p_v \in \{0, 1\}$ at the real places, $t_w > 0$ at all places, $\xi, \eta \in K$, and $c'_w = n_w / c_w$. Then $$\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)} = \frac{c_t^{p, k} e^{2 \pi i \mathrm{Tr}(\xi \eta)}}{\prod_w |c_w|^{n_w} N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}} \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_{1/t}^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}.$$ -/
theorem idealTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (ξ η : K) :
    idealTheta K p k c a t ξ η =
      mixedGaussConst p k t * (((∏ w, |(c w : ℝ)| ^ mult w) *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|))⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (ξ * η) : ℚ) : ℝ)) *
        idealDualTheta K p k c a (fun w => 1 / t w) ξ η := by
  rw [← mixedTheta_globalLattice, mixedTheta_eq p k _ hp ht, mixedTheta_dualLattice_globalLattice,
    covolume_globalLattice, real_inner_comm, inner_globalConjEmbedding_dualScale, mul_comm η]

/-- **The transformation formula for the lattice $\sigma(\mathfrak{a})$.** For $c = 1$, so that $c'_w = n_w$, $$\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\sigma(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)} = \frac{c_t^{p, k} e^{2 \pi i \mathrm{Tr}(\xi \eta)}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}} \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_{1/t}^{p, k}(D_n \overline{\sigma(\beta - \eta)}) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}.$$ -/
theorem idealTheta_one_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (ξ η : K) :
    idealTheta K p k 1 a t ξ η =
      mixedGaussConst p k t * (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (ξ * η) : ℚ) : ℝ)) *
        idealDualTheta K p k 1 a (fun w => 1 / t w) ξ η := by
  rw [idealTheta_eq K p k 1 a hp ht]
  simp

end Theta

end Langlands.Tate
