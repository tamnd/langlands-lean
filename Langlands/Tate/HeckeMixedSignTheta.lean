/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMellinUnits

/-!
# Theta series with a weight of mixed signs at the complex places

Let $K$ be a number field. The files `Langlands/Tate/MixedWeightTheta.lean` to `Langlands/Tate/HeckeMellinUnits.lean` use the weight $\overline{z}^{k_w} e^{-\pi t |z|^2}$ at each complex place $w$. This weight gives the infinity type $(\overline{\sigma_w(\alpha)} / |\sigma_w(\alpha)|)^{k_w}$, and so it covers only the parameters $n_w = k_w \ge 0$ at the complex places. This file adds a sign $\varepsilon_w$ at each complex place. If $\varepsilon_w$ is false, the weight at $w$ is $\overline{z}^{k_w} e^{-\pi t |z|^2}$. If $\varepsilon_w$ is true, the weight at $w$ is $z^{k_w} e^{-\pi t |z|^2}$.

The Fourier transform of $z^k e^{-\pi t |z|^2}$ follows from the Fourier transform of $\overline{z}^k e^{-\pi t |z|^2}$ (`Langlands.Tate.fourier_gaussWeight`), because the conjugation $z \mapsto \overline{z}$ is a linear isometry of $\mathbb{C}$ and the Fourier transform commutes with it. The file then repeats the Poisson summation on the mixed space, the theta series of a fractional ideal and the weighted theta series of `Langlands/Tate/HeckeMellinUnits.lean` with the signed weight. In the global part, the embedding $\sigma_w$ at a complex place is replaced by the signed embedding $\sigma^\varepsilon_w$, which is $\overline{\sigma_w}$ if $\varepsilon_w$ is true. The lemmas that do not depend on the weight are not repeated.

## Main definitions

* `Langlands.Tate.flipConj`: the map $z \mapsto \overline{z}$ if $b$ is true, and the identity if $b$ is false.
* `Langlands.Tate.signMixedGaussWeight`: the signed Gaussian weight $G^{\varepsilon, p, k}_t$ on the mixed space.
* `Langlands.Tate.signMixedTheta`: the theta series of a lattice with the signed weight.
* `Langlands.Tate.signEmbedding`: the signed embedding $\sigma^\varepsilon_w$ of $K$ at an infinite place $w$.
* `Langlands.Tate.signIdealTheta`, `Langlands.Tate.signIdealDualTheta`: the signed theta series of a fractional ideal and of its dual.
* `Langlands.Tate.signInfinityWeight`: the signed infinity type $\chi^{\varepsilon, p, k}_\infty$.
* `Langlands.Tate.signHeckeTerm`, `Langlands.Tate.signHeckeTheta`, `Langlands.Tate.signHeckeDualTheta`: the normalized terms and theta series of the signed weight.

## Main results

* `Langlands.Tate.fourier_pow_mul_gauss`: the Fourier transform of $z^k e^{-\pi t |z|^2}$ is $(-i)^k t^{-(k + 1)} \xi^k e^{-\pi |\xi|^2 / t}$.
* `Langlands.Tate.fourier_signMixedGaussWeight`: the Fourier transform of the signed weight on the mixed space.
* `Langlands.Tate.signMixedTheta_eq`: the Poisson formula for the signed theta series of a lattice.
* `Langlands.Tate.signIdealTheta_eq`: the transformation formula of the signed theta series of a fractional ideal.
* `Langlands.Tate.signHeckeTheta_eq`: the transformation formula of the normalized signed theta series.
* `Langlands.Tate.signHeckeTheta_unitScale`: the equivariance of the normalized signed theta series under the units.
-/

open MeasureTheory Module Filter Topology Set Complex FourierTransform
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped Real RealInnerProductSpace Classical nonZeroDivisors

namespace Langlands.Tate

section Flip

/-- The conjugation if $b$ is true: $\mathrm{flip}_b(z) = \bar z$ if $b$ is true and $\mathrm{flip}_b(z) = z$ if $b$ is false. -/
noncomputable def flipConj (b : Bool) (z : ℂ) : ℂ :=
  if b then starRingEnd ℂ z else z

/-- The flip for $b$ false is the identity. -/
@[simp]
theorem flipConj_false (z : ℂ) : flipConj false z = z := rfl

/-- The flip for $b$ true is the conjugation. -/
@[simp]
theorem flipConj_true (z : ℂ) : flipConj true z = starRingEnd ℂ z := rfl

/-- The flip does not change the absolute value. -/
theorem norm_flipConj (b : Bool) (z : ℂ) : ‖flipConj b z‖ = ‖z‖ := by
  cases b <;> simp

/-- The flip commutes with the multiplication by a real number. -/
theorem flipConj_ofReal_mul (b : Bool) (c : ℝ) (z : ℂ) :
    flipConj b ((c : ℂ) * z) = (c : ℂ) * flipConj b z := by
  cases b <;> simp

/-- The flip commutes with the conjugation. -/
theorem flipConj_conj (b : Bool) (z : ℂ) :
    flipConj b (starRingEnd ℂ z) = starRingEnd ℂ (flipConj b z) := by
  cases b <;> simp

/-- The flip is continuous. -/
theorem continuous_flipConj (b : Bool) : Continuous (flipConj b) := by
  cases b
  · exact continuous_id
  · exact Complex.continuous_conj

/-- The flip as a linear isometry of $\mathbb{C}$ over $\mathbb{R}$. -/
noncomputable def flipConjLIE (b : Bool) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  if b then Complex.conjLIE else LinearIsometryEquiv.refl ℝ ℂ

/-- The linear isometry `flipConjLIE` is the flip. -/
theorem coe_flipConjLIE (b : Bool) : (flipConjLIE b : ℂ → ℂ) = flipConj b := by
  cases b <;> rfl

/-- **The Fourier transform and the flip.** For each $g : \mathbb{C} \to \mathbb{C}$, $\mathcal{F}(g \circ \mathrm{flip}_b) = \mathcal{F}(g) \circ \mathrm{flip}_b$. The reason is that the conjugation preserves the measure and the inner product. -/
theorem fourier_comp_flipConj (b : Bool) (g : ℂ → ℂ) (ξ : ℂ) :
    𝓕 (fun z => g (flipConj b z)) ξ = 𝓕 g (flipConj b ξ) := by
  have h := Real.fourier_comp_linearIsometry (flipConjLIE b) g ξ
  rw [coe_flipConjLIE] at h
  exact h

/-- **Hecke's lemma for the weight $z^k e^{-\pi t |z|^2}$.** For $t > 0$, the Fourier transform of $z \mapsto \overline{\mathrm{flip}_b(z)}^k e^{-\pi t |z|^2}$ is $(-i)^k t^{-(k + 1)} \overline{\mathrm{flip}_b(\xi)}^k e^{-\pi |\xi|^2 / t}$. For $b$ true this is the weight $z^k e^{-\pi t |z|^2}$. -/
theorem fourier_gaussWeight_flipConj (b : Bool) (k : ℕ) {t : ℝ} (ht : 0 < t) (ξ : ℂ) :
    𝓕 (fun z => gaussWeight k t (flipConj b z)) ξ =
      (-I) ^ k * ((t ^ (k + 1))⁻¹ : ℝ) * gaussWeight k (1 / t) (flipConj b ξ) := by
  rw [fourier_comp_flipConj b (gaussWeight k t), fourier_gaussWeight k ht]

/-- The case $b$ true of `Langlands.Tate.fourier_gaussWeight_flipConj`: for $t > 0$, the Fourier transform of $z^k e^{-\pi t |z|^2}$ is $(-i)^k t^{-(k + 1)} \xi^k e^{-\pi |\xi|^2 / t}$. -/
theorem fourier_pow_mul_gauss (k : ℕ) {t : ℝ} (ht : 0 < t) (ξ : ℂ) :
    𝓕 (fun z : ℂ => z ^ k * (Real.exp (-(Real.pi * t) * ‖z‖ ^ 2) : ℂ)) ξ =
      (-I) ^ k * ((t ^ (k + 1))⁻¹ : ℝ) * (ξ ^ k * (Real.exp (-(Real.pi * (1 / t)) * ‖ξ‖ ^ 2) : ℂ)) := by
  have h := fourier_gaussWeight_flipConj true k ht ξ
  simp only [gaussWeight, flipConj_true, Complex.conj_conj, Complex.norm_conj] at h
  exact h

end Flip

section Mixed

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The Gaussian with a harmonic polynomial of mixed signs on the mixed space: $$G_t^{\varepsilon, p, k}(x) = \prod_{v \text{ real}} x_v^{p_v} e^{-\pi t_v x_v^2} \prod_{w \text{ complex}} \overline{\mathrm{flip}_{\varepsilon_w}(x_w)}^{k_w} e^{-\pi t_w |x_w|^2}.$$ The factor at $w$ is $\bar x_w^{k_w} e^{-\pi t_w |x_w|^2}$ if $\varepsilon_w$ is false and $x_w^{k_w} e^{-\pi t_w |x_w|^2}$ if $\varepsilon_w$ is true. -/
noncomputable def signMixedGaussWeight (t : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) : ℂ :=
  (∏ v, realGaussWeight (p v) (t v) ((euclidean.toMixed K x).1 v)) *
    ∏ w, gaussWeight (k w) (t w) (flipConj (ε w) ((euclidean.toMixed K x).2 w))

/-- **Hecke's lemma on the mixed space with mixed signs.** Let $p_v \in \{0, 1\}$ for each real place and $t_w > 0$ for each place. Then $\mathcal{F} G_t^{\varepsilon, p, k} = c_t^{p, k} \, G_{1/t}^{\varepsilon, p, k}$, with the constant $c_t^{p, k}$ of `Langlands.Tate.mixedGaussConst`. -/
theorem fourier_signMixedGaussWeight (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) (ξ : euclidean.mixedSpace K) :
    𝓕 (signMixedGaussWeight ε p k t) ξ =
      mixedGaussConst p k t * signMixedGaussWeight ε p k (fun w => 1 / t w) ξ := by
  have h := fourier_mixed_prod (fun v => realGaussWeight (p v) (t v))
    (fun w z => gaussWeight (k w) (t w) (flipConj (ε w) z)) ξ
  refine h.trans ?_
  simp only [fourier_realGaussWeight (hp _) (ht _), fourier_gaussWeight_flipConj _ _ (ht _),
    Finset.prod_mul_distrib, mixedGaussConst, signMixedGaussWeight]
  ring

/-- The signs do not change the absolute value: $|G_t^{\varepsilon, p, k}(x)| = |G_t^{p, k}(x)|$. -/
theorem norm_signMixedGaussWeight (t : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) :
    ‖signMixedGaussWeight ε p k t x‖ = ‖mixedGaussWeight p k t x‖ := by
  simp only [signMixedGaussWeight, mixedGaussWeight, norm_mul, norm_prod, norm_gaussWeight,
    norm_flipConj]

/-- The function $G_t^{\varepsilon, p, k}$ is continuous. -/
theorem continuous_signMixedGaussWeight (t : InfinitePlace K → ℝ) :
    Continuous (signMixedGaussWeight ε p k t) := by
  have hf : ∀ w, Continuous (flipConj (ε w)) := fun w => continuous_flipConj _
  unfold signMixedGaussWeight realGaussWeight gaussWeight
  fun_prop

/-- If $t_w > 0$ for each place $w$, then $G_t^{\varepsilon, p, k}(v) e^{2 \pi i \langle v, y \rangle}$ decays of each order $N$. -/
theorem hasDecay_signMixedGaussWeight_mul {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (y : euclidean.mixedSpace K) (N : ℕ) :
    HasDecay (fun v => signMixedGaussWeight ε p k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)) N := by
  obtain ⟨C, hC⟩ := hasDecay_mixedGaussWeight_mul p k ht y N
  refine ⟨C, fun v => ?_⟩
  have h := hC v
  rw [norm_mul, norm_signMixedGaussWeight, ← norm_mul]
  exact h

/-- If $t_w > 0$ for each place $w$, then the series $\sum_{\ell \in L} G_t^{\varepsilon, p, k}(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle}$ converges. -/
theorem summable_signMixedGaussWeight (L : Submodule ℤ (euclidean.mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L] {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x y : euclidean.mixedSpace K) :
    Summable fun ℓ : L =>
      signMixedGaussWeight ε p k t (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫) := by
  refine (summable_mixedGaussWeight p k L ht x y).norm.of_norm_bounded fun ℓ => ?_
  rw [norm_mul, norm_signMixedGaussWeight, ← norm_mul]

variable (L : Submodule ℤ (euclidean.mixedSpace K))

/-- The theta series of the lattice $L$ with the weight of mixed signs: $$\theta_L^{\varepsilon, p, k}(x, y; t) = \sum_{\ell \in L} G_t^{\varepsilon, p, k}(x + \ell) e^{2 \pi i \langle x + \ell, y \rangle}.$$ -/
noncomputable def signMixedTheta (t : InfinitePlace K → ℝ) (x y : euclidean.mixedSpace K) : ℂ :=
  ∑' ℓ : L, signMixedGaussWeight ε p k t (x + ℓ) * cexp (2 * Real.pi * I * ⟪x + ℓ, y⟫)

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The transformation formula of the theta series with mixed signs.** Let $p_v \in \{0, 1\}$ for each real place and $t_w > 0$ for each place. Then $$\theta_L^{\varepsilon, p, k}(x, y; t) = \frac{c_t^{p, k} e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(L)} \, \theta_{L^\vee}^{\varepsilon, p, k}(-y, x; 1/t).$$ -/
theorem signMixedTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x y : euclidean.mixedSpace K) :
    signMixedTheta ε p k L t x y =
      mixedGaussConst p k t * ((ZLattice.covolume L)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫) *
        signMixedTheta ε p k (dualLattice L) (fun w => 1 / t w) (-y) x := by
  set f : euclidean.mixedSpace K → ℂ := fun v =>
    signMixedGaussWeight ε p k t v * cexp (2 * Real.pi * I * ⟪v, y⟫)
  have hc : Continuous f := by
    have := continuous_signMixedGaussWeight ε p k t
    simp only [f]; fun_prop
  have hN : finrank ℝ (euclidean.mixedSpace K) < finrank ℝ (euclidean.mixedSpace K) + 1 :=
    Nat.lt_succ_self _
  have ht' : ∀ w, 0 < 1 / t w := fun w => one_div_pos.2 (ht w)
  have hFf : ∀ w, 𝓕 f w =
      mixedGaussConst p k t * signMixedGaussWeight ε p k (fun w => 1 / t w) (-y + w) :=
    fun w => by
      rw [fourier_mul_cexp_inner, fourier_signMixedGaussWeight ε p k hp ht, sub_eq_neg_add]
  have hF : Summable fun μ : dualLattice L => 𝓕 f μ := by
    simp only [hFf]
    exact ((summable_signMixedGaussWeight ε p k (dualLattice L) ht' (-y) 0).congr
      fun μ => by simp).mul_left _
  have key := tsum_add_zlattice_eq_of_hasDecay L hc
    (hasDecay_signMixedGaussWeight_mul ε p k ht y _) hN hF x
  rw [signMixedTheta, signMixedTheta, key]
  simp only [hFf]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun (μ : dualLattice L) => ?_
  have hinner : ⟪x, (μ : euclidean.mixedSpace K)⟫ = ⟪x, y⟫ + ⟪-y + μ, x⟫ := by
    rw [inner_add_left, inner_neg_left, real_inner_comm x y, real_inner_comm x μ]
    ring
  rw [hinner]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

end Mixed

section Embedding

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)

/-- The signed embedding at a place $w$: the embedding $\sigma_w$ if $w$ is real or $\varepsilon_w$ is false, and the conjugate embedding $\overline{\sigma_w}$ if $w$ is complex and $\varepsilon_w$ is true. -/
noncomputable def signEmbedding (w : InfinitePlace K) : K →+* ℂ :=
  if h : IsComplex w then (if ε ⟨w, h⟩ then (starRingEnd ℂ).comp w.embedding else w.embedding)
  else w.embedding

omit [NumberField K] in
/-- At a complex place the signed embedding is the flip of the embedding. -/
theorem signEmbedding_apply (w : {w : InfinitePlace K // IsComplex w}) (x : K) :
    signEmbedding ε w.1 x = flipConj (ε w) (w.1.embedding x) := by
  unfold signEmbedding flipConj
  simp only [w.2, ↓reduceDIte]
  cases ε w <;> rfl

variable {ε} in
omit [NumberField K] in
/-- The signed embedding induces the place $w$: $|\sigma^\varepsilon_w(x)| = |x|_w$. -/
theorem norm_signEmbedding (w : InfinitePlace K) (x : K) : ‖signEmbedding ε w x‖ = w x := by
  unfold signEmbedding
  split_ifs <;> simp [norm_embedding_eq]

end Embedding

section IdealTheta

variable (K : Type*) [Field K] [NumberField K]

section IdealSign

variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The weight at $\varphi_c(x)$ is $G_t^{\varepsilon, p, k}(\varphi_c(x)) = \prod_v g_{p_v, t_v}(c_v \sigma_v(x)) \prod_w \overline{c_w \sigma^\varepsilon_w(x)}^{k_w} e^{-\pi t_w |c_w \sigma^\varepsilon_w(x)|^2}$, with $g_{p, t}(r) = r^p e^{-\pi t r^2}$. -/
theorem signMixedGaussWeight_globalEmbedding (c t : InfinitePlace K → ℝ) (x : K) :
    signMixedGaussWeight ε p k t (globalEmbedding K c x) =
      (∏ v, realGaussWeight (p v) (t v) (c v * embedding_of_isReal v.2 x)) *
        ∏ w, gaussWeight (k w) (t w) ((c w : ℂ) * signEmbedding ε w.1 x) := by
  simp only [signMixedGaussWeight, toMixed_globalEmbedding, mixedScaleₗ_apply_fst,
    mixedScaleₗ_apply_snd, mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex,
    flipConj_ofReal_mul, signEmbedding_apply]

/-- The weight at $\psi_c(x)$ is $G_t^{\varepsilon, p, k}(\psi_c(x)) = \prod_v g_{p_v, t_v}(c_v \sigma_v(x)) \prod_w \overline{c_w \overline{\sigma^\varepsilon_w(x)}}^{k_w} e^{-\pi t_w |c_w \sigma^\varepsilon_w(x)|^2}$, with $g_{p, t}(r) = r^p e^{-\pi t r^2}$. -/
theorem signMixedGaussWeight_globalConjEmbedding (c t : InfinitePlace K → ℝ) (x : K) :
    signMixedGaussWeight ε p k t (globalConjEmbedding K c x) =
      (∏ v, realGaussWeight (p v) (t v) (c v * embedding_of_isReal v.2 x)) *
        ∏ w, gaussWeight (k w) (t w) ((c w : ℂ) * starRingEnd ℂ (signEmbedding ε w.1 x)) := by
  simp only [signMixedGaussWeight, globalConjEmbedding_apply, ContinuousLinearEquiv.apply_symm_apply,
    mixedScaleₗ_apply_fst, mixedScaleₗ_apply_snd, mixedConj_apply_fst, mixedConj_apply_snd,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex,
    flipConj_ofReal_mul, flipConj_conj, signEmbedding_apply]

variable (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The weighted theta series of the ideal $\mathfrak{a}$, shifted by $\xi \in K$ and twisted by $\eta \in K$: $$\theta_{\mathfrak{a}, c}^{p, k}(\xi, \eta; t) = \sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)}.$$ -/
noncomputable def signIdealTheta (t : InfinitePlace K → ℝ) (ξ η : K) : ℂ :=
  ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K),
    signMixedGaussWeight ε p k t (globalEmbedding K (fun w => (c w : ℝ)) (ξ + α)) *
      cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((ξ + α) * η) : ℚ) : ℝ))

/-- The dual weighted theta series over $(\mathfrak{a} \mathfrak{d})^{-1}$: $$\theta_{\mathfrak{a}, c}^{\vee, p, k}(\xi, \eta; t) = \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_t^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)},$$ with $c'_w = n_w / c_w$. -/
noncomputable def signIdealDualTheta (t : InfinitePlace K → ℝ) (ξ η : K) : ℂ :=
  ∑' β : dualIdeal K a,
    signMixedGaussWeight ε p k t (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) (β - η)) *
      cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (((β : K) - η) * ξ) : ℚ) : ℝ))

/-- The theta series of the lattice $\varphi_c(\mathfrak{a})$ at $x = \varphi_c(\xi)$ and $y = \psi_{c'}(\eta)$ is the theta series of the ideal. -/
theorem signMixedTheta_globalLattice (t : InfinitePlace K → ℝ) (ξ η : K) :
    signMixedTheta ε p k (globalLattice K c a) t (globalEmbedding K (fun w => (c w : ℝ)) ξ)
      (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η) =
      signIdealTheta K ε p k c a t ξ η := by
  rw [signMixedTheta, signIdealTheta, ← (globalLatticeEquiv K c a).tsum_eq]
  refine tsum_congr fun α => ?_
  rw [coe_globalLatticeEquiv, ← map_add, real_inner_comm, inner_globalConjEmbedding_dualScale,
    mul_comm η]

/-- The theta series of the dual lattice of $\varphi_c(\mathfrak{a})$ at $-\psi_{c'}(\eta)$ and $\varphi_c(\xi)$ is the dual theta series of the ideal. -/
theorem signMixedTheta_dualLattice_globalLattice (t : InfinitePlace K → ℝ) (ξ η : K) :
    signMixedTheta ε p k (dualLattice (globalLattice K c a)) t
      (-globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
      (globalEmbedding K (fun w => (c w : ℝ)) ξ) =
      signIdealDualTheta K ε p k c a t ξ η := by
  rw [signMixedTheta, signIdealDualTheta, ← (idealDualEquiv K c a).tsum_eq]
  refine tsum_congr fun β => ?_
  rw [coe_idealDualEquiv, neg_add_eq_sub, ← map_sub, inner_globalConjEmbedding_dualScale]

/-- **The transformation formula of the weighted theta series of an ideal.** Let $p_v \in \{0, 1\}$ at the real places, $t_w > 0$ at all places, $\xi, \eta \in K$, and $c'_w = n_w / c_w$. Then $$\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\varphi_c(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)} = \frac{c_t^{p, k} e^{2 \pi i \mathrm{Tr}(\xi \eta)}}{\prod_w |c_w|^{n_w} N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}} \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_{1/t}^{p, k}(\psi_{c'}(\beta - \eta)) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}.$$ -/
theorem signIdealTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (ξ η : K) :
    signIdealTheta K ε p k c a t ξ η =
      mixedGaussConst p k t * (((∏ w, |(c w : ℝ)| ^ mult w) *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|))⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (ξ * η) : ℚ) : ℝ)) *
        signIdealDualTheta K ε p k c a (fun w => 1 / t w) ξ η := by
  rw [← signMixedTheta_globalLattice, signMixedTheta_eq ε p k _ hp ht, signMixedTheta_dualLattice_globalLattice,
    covolume_globalLattice, real_inner_comm, inner_globalConjEmbedding_dualScale, mul_comm η]

/-- **The transformation formula for the lattice $\sigma(\mathfrak{a})$.** For $c = 1$, so that $c'_w = n_w$, $$\sum_{\alpha \in \mathfrak{a}} G_t^{p, k}(\sigma(\xi + \alpha)) e^{2 \pi i \mathrm{Tr}((\xi + \alpha) \eta)} = \frac{c_t^{p, k} e^{2 \pi i \mathrm{Tr}(\xi \eta)}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|}} \sum_{\beta \in (\mathfrak{a} \mathfrak{d})^{-1}} G_{1/t}^{p, k}(D_n \overline{\sigma(\beta - \eta)}) e^{2 \pi i \mathrm{Tr}((\beta - \eta) \xi)}.$$ -/
theorem signIdealTheta_one_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (ξ η : K) :
    signIdealTheta K ε p k 1 a t ξ η =
      mixedGaussConst p k t * (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (ξ * η) : ℚ) : ℝ)) *
        signIdealDualTheta K ε p k 1 a (fun w => 1 / t w) ξ η := by
  rw [signIdealTheta_eq K ε p k 1 a hp ht]
  simp

end IdealSign

end IdealTheta

section Places

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The phase of $\alpha$ at a place: $(\sigma_v(\alpha) / |\sigma_v(\alpha)|)^{p_v}$ at a real place $v$ and $(\overline{\sigma^\varepsilon_w(\alpha)} / |\sigma^\varepsilon_w(\alpha)|)^{k_w}$ at a complex place $w$. -/
noncomputable def signPlacePhase (α : K) (w : InfinitePlace K) : ℂ :=
  if h : IsReal w then ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩
  else (starRingEnd ℂ (signEmbedding ε w α) / (w α : ℂ)) ^ k ⟨w, not_isReal_iff_isComplex.1 h⟩

/-- The infinity type of the weight $(p, k)$ at $\alpha$: $$\chi^\varepsilon_\infty(\alpha) = \prod_{v \text{ real}} \Big(\frac{\sigma_v(\alpha)}{|\sigma_v(\alpha)|}\Big)^{p_v} \prod_{w \text{ complex}} \Big(\frac{\overline{\sigma^\varepsilon_w(\alpha)}}{|\sigma^\varepsilon_w(\alpha)|}\Big)^{k_w}.$$ -/
noncomputable def signInfinityWeight (α : K) : ℂ :=
  ∏ w : InfinitePlace K, signPlacePhase ε p k α w

/-- The factor of the weight at one place: $g_{p_v, t}(\sigma_v(\alpha))$ at a real place and $\overline{\sigma^\varepsilon_w(\alpha)}^{k_w} e^{-\pi t |\sigma^\varepsilon_w(\alpha)|^2}$ at a complex place. -/
noncomputable def signPlaceGauss (t : ℝ) (α : K) (w : InfinitePlace K) : ℂ :=
  if h : IsReal w then realGaussWeight (p ⟨w, h⟩) t (embedding_of_isReal h α)
  else gaussWeight (k ⟨w, not_isReal_iff_isComplex.1 h⟩) t (signEmbedding ε w α)

/-- The infinity type as a product over the real places and the complex places. -/
theorem signInfinityWeight_eq (α : K) :
    signInfinityWeight ε p k α =
      (∏ v : {w : InfinitePlace K // IsReal w},
        ((embedding_of_isReal v.2 α / v.1 α : ℝ) : ℂ) ^ p v) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        (starRingEnd ℂ (signEmbedding ε w.1 α) / (w.1 α : ℂ)) ^ k w := by
  rw [signInfinityWeight, prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by simp [signPlacePhase, v.2]
  · exact Finset.prod_congr rfl fun w _ => by
      simp [signPlacePhase, not_isReal_iff_isComplex.2 w.2]

/-- The weight $G_t^{p, k}$ at $\sigma(\alpha)$ is the product of the factors at the places. -/
theorem signMixedGaussWeight_eq_prod (t : InfinitePlace K → ℝ) (α : K) :
    signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α) =
      ∏ w, signPlaceGauss ε p k (t w) α w := by
  rw [signMixedGaussWeight_globalEmbedding, prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by simp [signPlaceGauss, v.2]
  · exact Finset.prod_congr rfl fun w _ => by
      simp [signPlaceGauss, not_isReal_iff_isComplex.2 w.2]

variable {ε p k}

omit [NumberField K] in
/-- **The Mellin transform at one place.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_0^\infty t^{z_w(s) - 1} g_w(t, \alpha) \, dt = \pi^{-z_w(s)} \Gamma(z_w(s)) \, \chi_w(\alpha) \, e^{-s n_w \log |\alpha|_w},$$ where $g_w$ is `signPlaceGauss` and $\chi_w$ is `signPlacePhase`. -/
theorem integral_signPlaceGauss {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) (w : InfinitePlace K) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (heckeExp p k s w - 1) * signPlaceGauss ε p k t α w =
      (π : ℂ) ^ (-heckeExp p k s w) * Complex.Gamma (heckeExp p k s w) * signPlacePhase ε p k α w *
        cexp (-(s * (mult w * Real.log (w α)))) := by
  have ha : 0 < w α := InfinitePlace.pos_iff.2 hα
  have hz := heckeExp_re_pos (p := p) (k := k) hs w
  by_cases h : IsReal w
  · have hr : embedding_of_isReal h α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_of_isReal]; exact ha.ne'
    simp only [signPlaceGauss, signPlacePhase, h, ↓reduceDIte]
    rw [integral_cpow_mul_realGaussWeight _ hz hr]
    have habs : |embedding_of_isReal h α| = w α := by
      rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
    have h1 : (embedding_of_isReal h α : ℂ) ^ p ⟨w, h⟩ =
        ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩ * (w α : ℂ) ^ p ⟨w, h⟩ := by
      rw [← mul_pow, ← Complex.ofReal_mul, div_mul_cancel₀ _ ha.ne']
    have h2 : (embedding_of_isReal h α) ^ 2 = w α ^ 2 := by rw [← habs, sq_abs]
    have h3 : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
    have h4 := ofReal_pow_mul_cpow_eq ha (p ⟨w, h⟩) (mult w) s
    rw [h1, h2]
    simp only [heckeExp, h3] at h4 ⊢
    linear_combination ((embedding_of_isReal h α / w α : ℝ) : ℂ) ^ p ⟨w, h⟩ *
      Complex.Gamma (((mult w : ℂ) * s + (p ⟨w, h⟩ : ℕ)) / 2) * h4
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 h
    have hv : signEmbedding ε w α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_signEmbedding]; exact ha.ne'
    simp only [signPlaceGauss, signPlacePhase, h, ↓reduceDIte]
    rw [integral_cpow_mul_gaussWeight _ hz hv, norm_signEmbedding]
    have h1 : (starRingEnd ℂ (signEmbedding ε w α)) ^ k ⟨w, hc⟩ =
        (starRingEnd ℂ (signEmbedding ε w α) / (w α : ℂ)) ^ k ⟨w, hc⟩ * (w α : ℂ) ^ k ⟨w, hc⟩ := by
      rw [← mul_pow, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 ha.ne')]
    have h3 : weightExp p k w = k ⟨w, hc⟩ := by simp [weightExp, h]
    have h4 := ofReal_pow_mul_cpow_eq ha (k ⟨w, hc⟩) (mult w) s
    rw [h1]
    simp only [heckeExp, h3] at h4 ⊢
    linear_combination (starRingEnd ℂ (signEmbedding ε w α) / (w α : ℂ)) ^ k ⟨w, hc⟩ *
      Complex.Gamma (((mult w : ℂ) * s + (k ⟨w, hc⟩ : ℕ)) / 2) * h4

omit [NumberField K] in
/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `integral_signPlaceGauss` is integrable on $(0, \infty)$. -/
theorem integrableOn_signPlaceGauss {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0)
    (w : InfinitePlace K) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (heckeExp p k s w - 1) * signPlaceGauss ε p k t α w)
      (Ioi 0) := by
  have ha : 0 < w α := InfinitePlace.pos_iff.2 hα
  have hz := heckeExp_re_pos (p := p) (k := k) hs w
  by_cases h : IsReal w
  · have hr : embedding_of_isReal h α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_embedding_of_isReal]; exact ha.ne'
    simp only [signPlaceGauss, h, ↓reduceDIte]
    exact integrableOn_cpow_mul_realGaussWeight _ hz hr
  · have hv : signEmbedding ε w α ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_signEmbedding]; exact ha.ne'
    simp only [signPlaceGauss, h, ↓reduceDIte]
    exact integrableOn_cpow_mul_gaussWeight _ hz hv

/-- **The Mellin transform of a weighted theta term.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} \prod_w t_w^{z_w(s) - 1} \, G_t^{p, k}(\sigma(\alpha)) \, dt = \Gamma_{p, k}(s) \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s},$$ with $z_w(s) = (n_w s + q_w) / 2$. -/
theorem integral_prod_cpow_mul_signMixedGaussWeight {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      heckeGamma p k s * signInfinityWeight ε p k α * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  have h : (fun t : InfinitePlace K → ℝ => (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
      signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α)) =
      fun t => ∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1) * signPlaceGauss ε p k (t w) α w := by
    funext t
    rw [signMixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]
  rw [h, integral_fintype_prod_eq_prod (fun w (t : ℝ) =>
    (t : ℂ) ^ (heckeExp p k s w - 1) * signPlaceGauss ε p k t α w)]
  simp_rw [integral_signPlaceGauss hs hα]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, heckeGamma,
    signInfinityWeight, ofReal_cpow_eq_exp (abs_norm_pos hα)]
  congr 2
  rw [← sum_mult_log α hα]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the integrand of `integral_prod_cpow_mul_signMixedGaussWeight` is integrable. -/
theorem integrable_prod_cpow_mul_signMixedGaussWeight {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ => (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have h := Integrable.fintype_prod (f := fun (w : InfinitePlace K) (t : ℝ) =>
    (t : ℂ) ^ (heckeExp p k s w - 1) * signPlaceGauss ε p k t α w)
    (μ := fun _ => volume.restrict (Ioi (0 : ℝ))) (fun w => integrableOn_signPlaceGauss hs hα w)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [signMixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]

end Places
section Weighted

variable {K : Type*} [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The normalized term of $\alpha$ in the weighted theta series: $$h_t(\alpha) = \prod_w t_w^{q_w / 2} \, G_t^{p, k}(\sigma(\alpha)).$$ At a real place the factor is $(\sqrt{t_v} \sigma_v(\alpha))^{p_v} e^{-\pi t_v \sigma_v(\alpha)^2}$, and at a complex place it is $(\sqrt{t_w} \overline{\sigma_w(\alpha)})^{k_w} e^{-\pi t_w |\sigma_w(\alpha)|^2}$. -/
noncomputable def signHeckeTerm (α : K) (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
    signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α)

variable {ε p k}

/-- For $t_w > 0$, $h_t(\alpha) \prod_w t_w^{n_w s / 2 - 1} = \prod_w t_w^{z_w(s) - 1} \, G_t^{p, k}(\sigma(\alpha))$. -/
theorem signHeckeTerm_mul_prod {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (α : K) (s : ℂ) :
    signHeckeTerm ε p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) =
      (∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1)) *
        signMixedGaussWeight ε p k t (globalEmbedding K (fun _ => 1) α) := by
  have h : ∏ w, (t w : ℂ) ^ (heckeExp p k s w - 1) =
      (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← cpow_add _ _ (Complex.ofReal_ne_zero.2 (ht w).ne'), heckeExp]
    congr 1
    ring
  rw [h, signHeckeTerm]
  ring

/-- For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, the function $h_t(\alpha) \prod_w t_w^{n_w s / 2 - 1}$ is integrable on $(0, \infty)^{S_\infty}$. -/
theorem integrable_signHeckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    Integrable (fun t : InfinitePlace K → ℝ =>
        signHeckeTerm ε p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  refine (integrable_prod_cpow_mul_signMixedGaussWeight (ε := ε) (p := p) (k := k) hs hα).congr ?_
  filter_upwards [ae_pi_Ioi_pos] with t ht
  exact (signHeckeTerm_mul_prod ht α s).symm

/-- **The Mellin transform of a normalized weighted theta term.** For $\mathrm{Re}\, s > 0$ and $\alpha \neq 0$, $$\int_{(0, \infty)^{S_\infty}} h_t(\alpha) \prod_w t_w^{n_w s / 2} \, \frac{dt_w}{t_w} = \Gamma_{p, k}(s) \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s}.$$ -/
theorem integral_signHeckeTerm_mul_prod {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ∫ t : InfinitePlace K → ℝ, signHeckeTerm ε p k α t * ∏ w, (t w : ℂ) ^ ((mult w : ℂ) * s / 2 - 1)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) =
      heckeGamma p k s * signInfinityWeight ε p k α * ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [← integral_prod_cpow_mul_signMixedGaussWeight (ε := ε) (p := p) (k := k) hs hα]
  refine integral_congr_ae ?_
  filter_upwards [ae_pi_Ioi_pos] with t ht
  exact signHeckeTerm_mul_prod ht α s

/-- **The Mellin transform of a weighted theta term in the unit coordinates.** For $\mathrm{Re}\, s > 0$, $\alpha \neq 0$ and $s' = 2 s / n$, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha) \, dc \, dy = \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N_{K/\mathbb{Q}}(\alpha)|^{-s'}.$$ -/
theorem integral_unitScale_signHeckeTerm {s : ℂ} (hs : 0 < s.re) {α : K} (hα : α ≠ 0) :
    ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k α (unitScale K y c) =
      heckeGamma p k (2 * s / finrank ℚ K) * signInfinityWeight ε p k α *
        ((|(Algebra.norm ℚ α : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)) := by
  have hre : 0 < (2 * s / finrank ℚ K).re := by
    rw [Complex.div_natCast_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    have := finrank_pos (R := ℚ) (M := K)
    positivity
  rw [integral_unitScale_eq _ (integrable_signHeckeTerm_mul_prod hre hα),
    integral_signHeckeTerm_mul_prod hre hα]

end Weighted

section Equivariance

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- The phase is multiplicative: $\chi_w(\alpha \beta) = \chi_w(\alpha) \chi_w(\beta)$. -/
theorem signPlacePhase_mul (α β : K) (w : InfinitePlace K) :
    signPlacePhase ε p k (α * β) w = signPlacePhase ε p k α w * signPlacePhase ε p k β w := by
  by_cases h : IsReal w
  · simp only [signPlacePhase, h, ↓reduceDIte, map_mul, ← mul_pow, ← Complex.ofReal_mul,
      mul_div_mul_comm]
  · simp only [signPlacePhase, h, ↓reduceDIte, map_mul, ← mul_pow, Complex.ofReal_mul,
      mul_div_mul_comm]

/-- **The infinity type is multiplicative.** $\chi_\infty(\alpha \beta) = \chi_\infty(\alpha) \chi_\infty(\beta)$. -/
theorem signInfinityWeight_mul (α β : K) :
    signInfinityWeight ε p k (α * β) = signInfinityWeight ε p k α * signInfinityWeight ε p k β := by
  simp only [signInfinityWeight, signPlacePhase_mul, Finset.prod_mul_distrib]

variable (ε p k) in
/-- The factor of the normalized term at one place: $t^{q_w / 2} g_w(t, \alpha)$. -/
noncomputable def signPlaceTerm (t : ℝ) (α : K) (w : InfinitePlace K) : ℂ :=
  (t : ℂ) ^ ((weightExp p k w : ℂ) / 2) * signPlaceGauss ε p k t α w

/-- The normalized term is the product of the factors at the places. -/
theorem signHeckeTerm_eq_prod (α : K) (t : InfinitePlace K → ℝ) :
    signHeckeTerm ε p k α t = ∏ w, signPlaceTerm ε p k (t w) α w := by
  rw [signHeckeTerm, signMixedGaussWeight_eq_prod, ← Finset.prod_mul_distrib]
  rfl

omit [NumberField K] in
/-- The action of $\beta \neq 0$ at one place: for $t \ge 0$, $$t^{q_w / 2} g_w(t, \beta \alpha) = \chi_w(\beta) \, (t |\beta|_w^2)^{q_w / 2} g_w(t |\beta|_w^2, \alpha).$$ -/
theorem signPlaceTerm_mul {t : ℝ} (ht : 0 ≤ t) {β : K} (hβ : β ≠ 0) (α : K) (w : InfinitePlace K) :
    signPlaceTerm ε p k t (β * α) w = signPlacePhase ε p k β w * signPlaceTerm ε p k (t * w β ^ 2) α w := by
  have hb : 0 < w β := InfinitePlace.pos_iff.2 hβ
  have hb' : (w β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hc : ((t * w β ^ 2 : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2) =
      (t : ℂ) ^ ((weightExp p k w : ℂ) / 2) * (w β : ℂ) ^ weightExp p k w := by
    rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht (by positivity), ofReal_sq_cpow_half hb]
  by_cases h : IsReal w
  · have h3 : weightExp p k w = p ⟨w, h⟩ := by simp [weightExp, h]
    have habs : (embedding_of_isReal h β) ^ 2 = w β ^ 2 := by
      rw [← norm_embedding_of_isReal h β, Real.norm_eq_abs, sq_abs]
    have he : -(π * t) * (embedding_of_isReal h (β * α)) ^ 2 =
        -(π * (t * w β ^ 2)) * (embedding_of_isReal h α) ^ 2 := by
      rw [map_mul, mul_pow, habs]
      ring
    simp only [signPlaceTerm, signPlaceGauss, signPlacePhase, h, ↓reduceDIte, realGaussWeight] at hc ⊢
    rw [hc, he, h3, map_mul, Complex.ofReal_mul, Complex.ofReal_div]
    field_simp
    have key : ((embedding_of_isReal h β : ℂ) / (w β : ℂ)) ^ p ⟨w, h⟩ * (w β : ℂ) ^ p ⟨w, h⟩ =
        (embedding_of_isReal h β : ℂ) ^ p ⟨w, h⟩ := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hb')]
    linear_combination -((t : ℂ) ^ ((p ⟨w, h⟩ : ℂ) / 2) *
      (embedding_of_isReal h α : ℂ) ^ p ⟨w, h⟩) * key
  · have hcx : IsComplex w := not_isReal_iff_isComplex.1 h
    have h3 : weightExp p k w = k ⟨w, hcx⟩ := by simp [weightExp, h]
    have he : -(π * t) * ‖signEmbedding ε w (β * α)‖ ^ 2 =
        -(π * (t * w β ^ 2)) * ‖signEmbedding ε w α‖ ^ 2 := by
      rw [map_mul, norm_mul, norm_signEmbedding w β]
      ring
    simp only [signPlaceTerm, signPlaceGauss, signPlacePhase, h, ↓reduceDIte, gaussWeight] at hc ⊢
    rw [hc, he, h3, map_mul, map_mul]
    field_simp
    have key : (starRingEnd ℂ (signEmbedding ε w β) / (w β : ℂ)) ^ k ⟨w, hcx⟩ *
        (w β : ℂ) ^ k ⟨w, hcx⟩ = (starRingEnd ℂ (signEmbedding ε w β)) ^ k ⟨w, hcx⟩ := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hb')]
    linear_combination -((t : ℂ) ^ ((k ⟨w, hcx⟩ : ℂ) / 2) *
      (starRingEnd ℂ (signEmbedding ε w α)) ^ k ⟨w, hcx⟩) * key

/-- **The action of $K^\times$ on the normalized terms.** For $\beta \neq 0$ and $t_w \ge 0$, $$h_t(\beta \alpha) = \chi_\infty(\beta) \, h_{t |\beta|^2}(\alpha),$$ where $(t |\beta|^2)_w = t_w |\beta|_w^2$. -/
theorem signHeckeTerm_mul {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) {β : K} (hβ : β ≠ 0)
    (α : K) :
    signHeckeTerm ε p k (β * α) t = signInfinityWeight ε p k β * signHeckeTerm ε p k α (fun w => t w * w β ^ 2) := by
  simp only [signHeckeTerm_eq_prod, signInfinityWeight, signPlaceTerm_mul (ht _) hβ, Finset.prod_mul_distrib]

/-- **The periodicity in the unit coordinates.** Let $u = \prod_i \varepsilon_i^{m_i}$. If $\chi_\infty(u) = 1$ and $y \ge 0$, then $h_{t(y, c)}(u \alpha) = h_{t(y, c + m)}(\alpha)$. -/
theorem signHeckeTerm_unitOfInt_mul {m : Fin (rank K) → ℤ}
    (hu : signInfinityWeight ε p k (unitOfInt K m : K) = 1) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin (rank K) → ℝ) (α : K) :
    signHeckeTerm ε p k ((unitOfInt K m : K) * α) (unitScale K y c) =
      signHeckeTerm ε p k α (unitScale K y (c + fun i => (m i : ℝ))) := by
  rw [signHeckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le) (coe_ne_zero _), hu, one_mul]
  congr 1
  funext w
  rw [unitScale_add_int]

end Equivariance

section Theta

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The normalized weighted theta series of $\mathfrak{a}$: $\Theta_{\mathfrak{a}}^{p, k}(t) = \prod_w t_w^{q_w / 2} \, \theta_{\mathfrak{a}, 1}^{p, k}(0, 0; t)$. -/
noncomputable def signHeckeTheta (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * signIdealTheta K ε p k 1 a t 0 0

/-- The normalized dual theta series: $\Theta_{\mathfrak{a}}^{\vee, p, k}(t) = \prod_w t_w^{q_w / 2} \, \theta_{\mathfrak{a}, 1}^{\vee, p, k}(0, 0; t)$. It is a sum over $(\mathfrak{a} \mathfrak{d})^{-1}$ of the weight $G_t^{p, k}$ at $D_n \overline{\sigma(\beta)}$. -/
noncomputable def signHeckeDualTheta (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * signIdealDualTheta K ε p k 1 a t 0 0

/-- The normalized theta series is the sum of the normalized terms: $\Theta_{\mathfrak{a}}^{p, k}(t) = \sum_{\alpha \in \mathfrak{a}} h_t(\alpha)$. -/
theorem signHeckeTheta_eq_tsum (t : InfinitePlace K → ℝ) :
    signHeckeTheta K ε p k a t = ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), signHeckeTerm ε p k (α : K) t := by
  have h1 : (fun w => ((1 : InfinitePlace K → ℝˣ) w : ℝ)) = fun _ => 1 := by
    funext w
    simp
  rw [signHeckeTheta, signIdealTheta, ← tsum_mul_left]
  refine tsum_congr fun α => ?_
  simp only [h1, zero_add, mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero,
    Complex.exp_zero, mul_one, signHeckeTerm]

variable {K ε p k}

/-- **The transformation formula of the normalized theta series.** Let $p_v \in \{0, 1\}$ and $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(t) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{a}}^{\vee, p, k}(1/t).$$ The weight of the Mellin transform changes from $\prod_w t_w^{n_w s / 2}$ to $\prod_w t_w^{n_w (1 - s) / 2}$ under $t \mapsto 1/t$. -/
theorem signHeckeTheta_eq (hp : ∀ v, p v ≤ 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    signHeckeTheta K ε p k a t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) * signHeckeDualTheta K ε p k a (fun w => 1 / t w) := by
  rw [signHeckeTheta, signIdealTheta_one_eq K ε p k a hp ht 0 0, signHeckeDualTheta]
  simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  linear_combination
    ((((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
      signIdealDualTheta K ε p k 1 a (fun w => 1 / t w) 0 0 * prod_cpow_mul_mixedGaussConst (p := p) (k := k) ht

/-- **The transformation formula in the unit coordinates.** Let $p_v \in \{0, 1\}$ and $y > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(t(y, c)) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|} \, \sqrt{y}^{\,n}} \, \Theta_{\mathfrak{a}}^{\vee, p, k}(t(y^{-1}, -c)).$$ -/
theorem signHeckeTheta_unitScale (hp : ∀ v, p v ≤ 1) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    signHeckeTheta K ε p k a (unitScale K y c) =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) * signHeckeDualTheta K ε p k a (unitScale K y⁻¹ (-c)) := by
  have h : (fun w => 1 / unitScale K y c w) = unitScale K y⁻¹ (-c) := by
    funext w
    rw [one_div, unitScale_inv]
  rw [signHeckeTheta_eq a hp (unitScale_pos hy c), prod_sqrt_unitScale hy.le, h]

end Theta

end Langlands.Tate
