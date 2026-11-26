/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeUnfold
import Langlands.Tate.PeriodicGauss

/-!
# The theta series of a ramified Hecke character

Let $K$ be a number field of degree $n$, fix a weight $(p, k)$ and let $h_t(\alpha)$ be the normalized term of `Langlands/Tate/HeckeMellinUnits.lean`. For a nonzero fractional ideal $\mathfrak{a}$ and a coefficient $f : K \to \mathbb{C}$, this file defines the theta series $\Theta_{\mathfrak{a}}^{p, k}(f; t) = \sum_{\alpha \in \mathfrak{a}} f(\alpha) h_t(\alpha)$. This file proves the two analytic steps of Hecke's proof that change for a ramified character. The first step is the unfolding of the Mellin transform for a coefficient with $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$. The second step is the theta transformation for a coefficient that is periodic modulo an ideal $\mathfrak{b} \subseteq \mathfrak{a}$, with the finite Gauss sums of $f$ as the dual coefficients. For the periodic coefficient $c_J$ of a Hecke character $\chi$ of conductor $\mathfrak{f}$, the period is $\mathfrak{f} J$, and the dual series has the coefficients $\tau_J(\chi) \overline{c_D(\beta)}$ on $D = (\mathfrak{f} J \mathfrak{d})^{-1}$.

## Main definitions

* `Langlands.Tate.coeffTheta`: the theta series $\Theta_{\mathfrak{a}}^{p, k}(f; t)$ with a coefficient.
* `Langlands.Tate.coeffDualTheta`: the dual theta series $\Theta_{\mathfrak{b}}^{\vee, p, k}(g; t)$ with a coefficient on $(\mathfrak{b} \mathfrak{d})^{-1}$.
* `Langlands.Tate.residueQuot`, `Langlands.Tate.residueRep`: the finite quotient $\mathfrak{a} / \mathfrak{b}$ and its representatives $\xi_q$.
* `Langlands.Tate.residueGauss`: the finite Gauss sum $\widehat{f}(\beta) = \sum_q f(\xi_q) e^{2 \pi i \mathrm{Tr}(\beta \xi_q)}$.

## Main results

* `Langlands.Tate.coeffTheta_eq_sum_residues`: the theta series with a periodic coefficient as a finite sum of shifted theta series of $\mathfrak{b}$.
* `Langlands.Tate.coeffTheta_eq`: the transformation formula $\Theta_{\mathfrak{a}}^{p, k}(f; t) = (-i)^{|p| + |k|} (N(\mathfrak{b}) 2^{-r_2} \sqrt{|d_K|} \prod_w \sqrt{t_w}^{\,n_w})^{-1} \Theta_{\mathfrak{b}}^{\vee, p, k}(\widehat{f}; 1/t)$.
* `Langlands.Tate.coeffTheta_periodicCoeff_eq`: the same formula for the periodic coefficient $c_J$ of a unitary ramified character, with the Gauss sum $\tau_J(\chi)$ and the dual coefficients $\overline{c_D}$.
* `Langlands.Tate.hasSum_integral_unitCube_coeffTheta`: the unfolding with a coefficient for a fixed $y > 0$.
* `Langlands.Tate.hasSum_integral_coeffTheta_sub`: the unfolding of the Mellin transform with a coefficient, $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) - f(0) h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I f(\alpha_I) \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ for $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$.

## Proof

For the transformation, the sum over $\mathfrak{a}$ splits into the finitely many classes $\xi_q + \mathfrak{b}$, and $f$ is constant on each class. On each class, the theta transformation `Langlands.Tate.idealTheta_eq` of the shifted theta series of $\mathfrak{b}$ gives a series over $(\mathfrak{b} \mathfrak{d})^{-1}$ with the character $e^{2 \pi i \mathrm{Tr}(\beta \xi_q)}$. The finite sum over $q$ then commutes with the sum over $\beta$. For $c_J$, the finite sum is the periodic Gauss sum, and `Langlands.Tate.periodicGaussCoeff_eq_periodicGaussSum_mul` gives $\tau_J(\chi) \overline{c_D(\beta)}$. For the unfolding, the method is the method of `Langlands/Tate/HeckeUnfold.lean`. The condition on $f$ gives $f(u \alpha) h_{t(y, c)}(u \alpha) = f(\alpha) h_{t(y, c + m)}(\alpha)$, and the bound $|f| \le B$ gives the absolute convergence from the bound for $f = 1$.

## Open parts

This file does not yet prove the functional equation of the Hecke $L$-function of a ramified character. The missing steps are these.
* The proof that the periodic coefficient $c_J$ satisfies $c_J(u \alpha) \chi_\infty(u) = c_J(\alpha)$ for the units $u$. This uses `infChar_mul_infinityWeight` of `Langlands/Tate/HeckeGeneralUnramified.lean`, which is not built yet.
* The identification of the dual series $\Theta_{\mathfrak{f} J}^{\vee, p, k}(\overline{c_D}; t)$ with the conjugate of the theta series $\Theta_D^{p, k}(c_D; t)$ of the dual ideal, as in `Langlands/Tate/HeckeFEPair.lean`.
* The FE pair with the coefficients, the symmetry of the dual sums and the sum over the ideal classes, with the root number $(-i)^{|p| + |k|} \tau(\chi) N(\mathfrak{f})^{-1/2} \chi(\mathfrak{d})$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped Real Classical nonZeroDivisors ENNReal RealInnerProductSpace

namespace Langlands.Tate

section Definitions

variable (K : Type*) [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The theta series of the ideal $\mathfrak{a}$ with the coefficient $f$: $\Theta_{\mathfrak{a}}^{p, k}(f; t) = \sum_{\alpha \in \mathfrak{a}} f(\alpha) h_t(\alpha)$, where $h_t$ is the normalized term `Langlands.Tate.heckeTerm`. -/
noncomputable def coeffTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), f α * heckeTerm p k (α : K) t

/-- The dual theta series of the ideal $\mathfrak{b}$ with the coefficient $g$: $$\Theta_{\mathfrak{b}}^{\vee, p, k}(g; t) = \prod_w t_w^{q_w / 2} \sum_{\beta \in (\mathfrak{b} \mathfrak{d})^{-1}} g(\beta) G_t^{p, k}(D_n \overline{\sigma(\beta)}).$$ For $g = 1$ it is `Langlands.Tate.heckeDualTheta`. -/
noncomputable def coeffDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
    ∑' β : dualIdeal K b, g β *
      mixedGaussWeight p k t (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β)

/-- The finite quotient $\varphi(\mathfrak{a}) / \varphi(\mathfrak{b})$ of the lattices of two fractional ideals. -/
noncomputable abbrev residueQuot (a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type _ :=
  traceLattice K a ⧸ subLattice (traceLattice K a) (traceLattice K b)

/-- The representative $\xi_q \in \mathfrak{a}$ of a class $q$ of $\varphi(\mathfrak{a}) / \varphi(\mathfrak{b})$. -/
noncomputable def residueRep {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (q : residueQuot K a b) : K :=
  ((globalLatticeEquiv K (traceScale K) a).symm q.out : K)

/-- The finite Gauss sum of a coefficient $f$: $\widehat{f}(\beta) = \sum_{q \in \mathfrak{a} / \mathfrak{b}} f(\xi_q) e^{2 \pi i \mathrm{Tr}(\beta \xi_q)}$. -/
noncomputable def residueGauss (a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) [Fintype (residueQuot K a b)]
    (f : K → ℂ) (β : K) : ℂ :=
  ∑ q : residueQuot K a b, f (residueRep K q) * traceExp K (β * residueRep K q)

end Definitions

section Residues

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- The scaling constants $c = 1$ give the plain values $1$. -/
theorem coe_one_units : (fun w => ((1 : InfinitePlace K → ℝˣ) w : ℝ)) = fun _ => 1 := by
  funext w
  simp

variable (p k) in
/-- The series of `Langlands.Tate.idealTheta` converges for $t_w > 0$. -/
theorem summable_idealTheta (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (ξ η : K) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      mixedGaussWeight p k t (globalEmbedding K (fun w => (c w : ℝ)) (ξ + α)) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((ξ + α) * η) : ℚ) : ℝ)) := by
  have h := summable_mixedGaussWeight p k (globalLattice K c a) ht
    (globalEmbedding K (fun w => (c w : ℝ)) ξ)
    (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
  rw [← (globalLatticeEquiv K c a).summable_iff] at h
  refine h.congr fun α => ?_
  simp only [Function.comp_apply]
  rw [coe_globalLatticeEquiv, ← map_add, real_inner_comm, inner_globalConjEmbedding_dualScale,
    mul_comm η]

variable (p k) in
/-- The series of `Langlands.Tate.idealDualTheta` converges for $t_w > 0$. -/
theorem summable_idealDualTheta (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (ξ η : K) :
    Summable fun β : dualIdeal K a =>
      mixedGaussWeight p k t (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) (β - η)) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (((β : K) - η) * ξ) : ℚ) : ℝ)) := by
  have h := summable_mixedGaussWeight p k (dualLattice (globalLattice K c a)) ht
    (-globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
    (globalEmbedding K (fun w => (c w : ℝ)) ξ)
  rw [← (idealDualEquiv K c a).summable_iff] at h
  refine h.congr fun β => ?_
  simp only [Function.comp_apply]
  rw [coe_idealDualEquiv, neg_add_eq_sub, ← map_sub, inner_globalConjEmbedding_dualScale]

/-- The shifted series of normalized terms: for $t_w > 0$ and $\xi \in K$, $\sum_{\gamma \in \mathfrak{b}} h_t(\xi + \gamma) = \prod_w t_w^{q_w / 2} \theta_{\mathfrak{b}, 1}^{p, k}(\xi, 0; t)$. -/
theorem hasSum_heckeTerm_add (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) (ξ : K) :
    HasSum (fun γ : (b : FractionalIdeal (𝓞 K)⁰ K) => heckeTerm p k (ξ + γ) t)
      ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * idealTheta K p k 1 b t ξ 0) := by
  have h := ((summable_idealTheta p k 1 b ht ξ 0).hasSum).mul_left
    (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2))
  rw [idealTheta]
  convert h using 2 with γ
  rw [coe_one_units, heckeTerm]
  simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]

/-- If $\mathfrak{b} \subseteq \mathfrak{a}$, then $\varphi(\mathfrak{b}) \subseteq \varphi(\mathfrak{a})$. -/
theorem traceLattice_le {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) : traceLattice K b ≤ traceLattice K a := by
  intro y hy
  obtain ⟨α, hα, rfl⟩ := (mem_globalLattice K _ _).1 hy
  exact globalEmbedding_mem K _ _ (hab hα)

/-- If $\mathfrak{b} \subseteq \mathfrak{a}$, then the quotient $\varphi(\mathfrak{a}) / \varphi(\mathfrak{b})$ is finite. -/
theorem finite_residueQuot {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) : Finite (residueQuot K a b) :=
  finite_quotient_subLattice _ _ (traceLattice_le hab)

/-- The bijection $\mathfrak{a} \to \varphi(\mathfrak{a})$ respects the translation by $\gamma \in \mathfrak{b}$: the preimage of $\ell + \varphi(\gamma)$ is $\xi + \gamma$, where $\xi$ is the preimage of $\ell$. -/
theorem coe_symm_add_globalLatticeEquiv {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) (ℓ : traceLattice K a)
    (γ : (b : FractionalIdeal (𝓞 K)⁰ K)) :
    ((globalLatticeEquiv K (traceScale K) a).symm
      (ℓ + ⟨globalLatticeEquiv K (traceScale K) b γ,
        traceLattice_le hab (globalLatticeEquiv K (traceScale K) b γ).2⟩) : K) =
      ((globalLatticeEquiv K (traceScale K) a).symm ℓ : K) + γ := by
  set e := globalLatticeEquiv K (traceScale K) a with he
  have h : ℓ + ⟨globalLatticeEquiv K (traceScale K) b γ,
      traceLattice_le hab (globalLatticeEquiv K (traceScale K) b γ).2⟩ =
      e ⟨((e.symm ℓ : _) : K) + γ, add_mem (e.symm ℓ).2 (hab γ.2)⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_add]
    change (ℓ : euclidean.mixedSpace K) + globalEmbedding K _ (γ : K) =
      globalEmbedding K _ (((e.symm ℓ : _) : K) + γ)
    rw [map_add]
    congr 1
    exact (congrArg Subtype.val (e.apply_symm_apply ℓ)).symm
  rw [h, e.symm_apply_apply]

/-- **The sum over an ideal sorted by the residues.** Let $\mathfrak{b} \subseteq \mathfrak{a}$ be nonzero fractional ideals, let $f$ be bounded and periodic modulo $\mathfrak{b}$ on $\mathfrak{a}$, and let $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(f; t) = \sum_{q \in \mathfrak{a} / \mathfrak{b}} f(\xi_q) \prod_w t_w^{q_w / 2} \theta_{\mathfrak{b}, 1}^{p, k}(\xi_q, 0; t).$$ -/
theorem coeffTheta_eq_sum_residues {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) [Fintype (residueQuot K a b)] {f : K → ℂ}
    (hf : ∀ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K), ∀ γ ∈ (b : FractionalIdeal (𝓞 K)⁰ K),
      f (α + γ) = f α) {B : ℝ} (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    coeffTheta K p k a f t = ∑ q : residueQuot K a b, f (residueRep K q) *
      ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        idealTheta K p k 1 b t (residueRep K q) 0) := by
  have hsumA : Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      f α * heckeTerm p k (α : K) t :=
    Summable.of_norm_bounded ((summable_heckeTerm p k a ht).norm.mul_left B) fun α => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB α) (norm_nonneg _)
  let e := globalLatticeEquiv K (traceScale K) a
  let F : traceLattice K a → ℂ := fun ℓ => f (e.symm ℓ) * heckeTerm p k (e.symm ℓ : K) t
  have hFs : HasSum F (coeffTheta K p k a f t) := by
    have h := (e.symm.hasSum_iff (f := fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      f α * heckeTerm p k (α : K) t)).2 hsumA.hasSum
    exact h
  have hfib : ∀ q : residueQuot K a b,
      HasSum (fun ℓ : {ℓ : traceLattice K a // (ℓ : residueQuot K a b) = q} => F ℓ)
        (f (residueRep K q) * ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
          idealTheta K p k 1 b t (residueRep K q) 0)) := by
    intro q
    refine (fiberEquiv _ _ (traceLattice_le hab) q).symm.hasSum_iff.1 ?_
    refine (globalLatticeEquiv K (traceScale K) b).hasSum_iff.1 ?_
    refine ((hasSum_heckeTerm_add b ht (residueRep K q)).mul_left
      (f (residueRep K q))).congr_fun fun γ => ?_
    change f (e.symm (q.out + ⟨globalLatticeEquiv K (traceScale K) b γ, _⟩) : K) *
      heckeTerm p k (e.symm (q.out + ⟨globalLatticeEquiv K (traceScale K) b γ, _⟩) : K) t = _
    rw [coe_symm_add_globalLatticeEquiv hab, hf _ (e.symm q.out).2 _ γ.2]
    rfl
  have h1 := ((Equiv.sigmaFiberEquiv (fun ℓ : traceLattice K a => (ℓ : residueQuot K a b))).hasSum_iff.2
    hFs).sigma hfib
  exact h1.unique (hasSum_fintype _)

/-- **The transformation formula of the theta series with a periodic coefficient.** Let $p_v \in \{0, 1\}$, let $\mathfrak{b} \subseteq \mathfrak{a}$ be nonzero fractional ideals, let $f$ be bounded and periodic modulo $\mathfrak{b}$ on $\mathfrak{a}$, and let $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(f; t) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{b}) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{b}}^{\vee, p, k}(\widehat{f}; 1/t),$$ where $\widehat{f}(\beta) = \sum_{q \in \mathfrak{a} / \mathfrak{b}} f(\xi_q) e^{2 \pi i \mathrm{Tr}(\beta \xi_q)}$ is the finite Gauss sum `Langlands.Tate.residueGauss` on the dual lattice $(\mathfrak{b} \mathfrak{d})^{-1}$. -/
theorem coeffTheta_eq (hp : ∀ v, p v ≤ 1) {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) [Fintype (residueQuot K a b)] {f : K → ℂ}
    (hf : ∀ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K), ∀ γ ∈ (b : FractionalIdeal (𝓞 K)⁰ K),
      f (α + γ) = f α) {B : ℝ} (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    coeffTheta K p k a f t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) *
        coeffDualTheta K p k b (residueGauss K a b f) (fun w => 1 / t w) := by
  have ht' : ∀ w, 0 < 1 / t w := fun w => one_div_pos.2 (ht w)
  have hq : ∀ ξ : K, (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
      idealTheta K p k 1 b t ξ 0 = (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) *
        ((∏ w, (((fun w => 1 / t w) w : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
          idealDualTheta K p k 1 b (fun w => 1 / t w) ξ 0) := by
    intro ξ
    rw [idealTheta_one_eq K p k b hp ht]
    simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    linear_combination
      ((((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
        idealDualTheta K p k 1 b (fun w => 1 / t w) ξ 0 *
          prod_cpow_mul_mixedGaussConst (p := p) (k := k) ht
  have hD : ∑' β : dualIdeal K b, residueGauss K a b f β *
      mixedGaussWeight p k (fun w => 1 / t w)
        (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) =
      ∑ q : residueQuot K a b, f (residueRep K q) *
        idealDualTheta K p k 1 b (fun w => 1 / t w) (residueRep K q) 0 := by
    simp only [idealDualTheta, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun q _ =>
      (summable_idealDualTheta p k 1 b ht' (residueRep K q) 0).mul_left (f (residueRep K q))]
    refine tsum_congr fun β => ?_
    rw [residueGauss, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [sub_zero, traceExp]
    ring
  rw [coeffTheta_eq_sum_residues hab hf hB ht, coeffDualTheta, hD]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hq]
  ring

end Residues

section Unfold

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {f : K → ℂ} {B : ℝ}

/-- For $t_w > 0$ and a bounded coefficient $f$, the family $f(\alpha) h_t(\alpha)$, $\alpha \in \mathfrak{a}$, is summable. -/
theorem summable_coeffTerm (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => f α * heckeTerm p k (α : K) t :=
  Summable.of_norm_bounded ((summable_heckeTerm p k a ht).norm.mul_left B) fun α => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB α) (norm_nonneg _)

omit [Field K] [NumberField K] in
/-- The bound $|f(\alpha) z| \le B |z|$ for the extended norms. -/
theorem enorm_coeff_mul_le (hB : ∀ α, ‖f α‖ ≤ B) (α : K) (z : ℂ) :
    ‖f α * z‖ₑ ≤ ENNReal.ofReal B * ‖z‖ₑ := by
  rw [enorm_mul, ← ofReal_norm (f α)]
  gcongr
  exact hB α

/-- The sum of the cube integrals of $|f(\alpha) h_{t(y, c)}(\alpha)|$ is at most $B$ times the same sum for $f = 1$. -/
theorem tsum_lintegral_coeffTerm_le (hB : ∀ α, ‖f α‖ ≤ B) (y : ℝ) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * heckeTerm p k (α : K) (unitScale K y c)‖ₑ ≤
      ENNReal.ofReal B * ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖heckeTerm p k (α : K) (unitScale K y c)‖ₑ := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun α => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun c => enorm_coeff_mul_le hB _ _

variable (p k a) in
/-- **The absolute convergence with a coefficient.** For a bounded coefficient $f$ and $\mathrm{Re}\, s > n / 2$, $$\int_0^\infty |y^{s - 1}| \sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |f(\alpha) h_{t(y, c)}(\alpha)| \, dc \, dy < \infty.$$ -/
theorem lintegral_enorm_mul_tsum_coeffTerm_lt_top (hB : ∀ α, ‖f α‖ ≤ B) {s : ℂ}
    (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a,
      ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * heckeTerm p k (α : K) (unitScale K y c)‖ₑ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun y => mul_le_mul_of_nonneg_left
    (tsum_lintegral_coeffTerm_le hB y) zero_le) ?_
  simp_rw [mul_left_comm _ (ENNReal.ofReal B)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_enorm_mul_tsum_lt_top p k a hs)

/-- **The periodicity of the coefficient terms under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $f(u \alpha) h_{t(y, c)}(u \alpha) = f(\alpha) h_{t(y, c + m)}(\alpha)$. -/
theorem coeffTerm_unitsEquiv
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * infinityWeight p k (u : K) = f α)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ) :
    f ((unitsEquiv K q : K) * α) * heckeTerm p k ((unitsEquiv K q : K) * α) (unitScale K y c) =
      f α * heckeTerm p k α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [heckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _) α, ← mul_assoc, hf]
  congr 2
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- **The unfolding of the absolute values with a coefficient.** If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |f(\alpha) h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |f(\alpha_I) h_{t(y, c)}(\alpha_I)| \, dc.$$ -/
theorem tsum_lintegral_unitCube_coeffTerm
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * infinityWeight p k (u : K) = f α)
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * heckeTerm p k (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖f (orbitRep a I) * heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * heckeTerm p k (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ‖f ((β.1 : NonzeroElt a) : K) *
            heckeTerm p k ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ),
          ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
            ‖f (orbitRep a I) * heckeTerm p k (orbitRep a I : K)
              (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, coeffTerm_unitsEquiv hf _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖f (orbitRep a I) * heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖f (orbitRep a I) * heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

variable (a) in
/-- For $t_w > 0$, the theta series with a coefficient minus its term $\alpha = 0$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem coeffTheta_sub_eq_tsum (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    coeffTheta K p k a f t - f 0 * heckeTerm p k 0 t =
      ∑' α : NonzeroElt a, f α * heckeTerm p k (α : K) t := by
  let z : (a : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  rw [coeffTheta, (summable_coeffTerm hB ht).tsum_eq_add_tsum_ite z]
  rw [show ((z : (a : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from rfl, add_sub_cancel_left]
  refine Eq.trans ?_ (tsum_subtype {α : (a : FractionalIdeal (𝓞 K)⁰ K) | (α : K) ≠ 0}
    (fun α => f α * heckeTerm p k (α : K) t)).symm
  refine tsum_congr fun α => ?_
  have hz : α = z ↔ (α : K) = 0 := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : (α : K) = 0
  · simp [hz.2 h, Set.indicator, z]
  · simp [mt hz.1 h, h]

/-- **The unfolding with a coefficient for a fixed $y$.** If $f$ is bounded, $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y > 0$, then $$\int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) - f(0) h_{t(y, c)}(0)\big) \, dc = w_K \sum_I f(\alpha_I) \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha_I) \, dc.$$ -/
theorem hasSum_integral_unitCube_coeffTheta (hB : ∀ α, ‖f α‖ ≤ B)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * infinityWeight p k (u : K) = f α)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, heckeTerm p k (orbitRep a I : K) (unitScale K y c)))
      (∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (coeffTheta K p k a f (unitScale K y c) - f 0 * heckeTerm p k 0 (unitScale K y c))) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      ‖f α * heckeTerm p k (α : K) (unitScale K y c)‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (tsum_lintegral_heckeTerm_le hy))) (tsum_lintegral_coeffTerm_le hB y)
  have hm : ∀ x : K, Measurable fun c => f x * heckeTerm p k x (unitScale K y c) := fun x =>
    measurable_const.mul ((measurable_heckeTerm x).comp (continuous_unitScale y).measurable)
  set g : NonzeroElt a → ℂ := fun α => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
    f α * heckeTerm p k (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      (coeffTheta K p k a f (unitScale K y c) - f 0 * heckeTerm p k 0 (unitScale K y c)) =
        ∑' α, g α := by
    simp_rw [coeffTheta_sub_eq_tsum a hB (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_coeffTerm (a := a) hf hy.le
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a, Integrable fun c =>
      f (orbitRep a I) * heckeTerm p k (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) * ∫⁻ c, ‖f (orbitRep a I) *
          heckeTerm p k (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, heckeTerm p k (orbitRep a I : K) (unitScale K y c)) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      f (orbitRep a I) * heckeTerm p k (orbitRep a I : K) (unitScale K y (c + fun i => (m i : ℝ)))
      with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, coeffTerm_unitsEquiv hf _ _ hy.le]
    have hsG : Summable fun q : torsion K × (Fin (rank K) → ℤ) => G q.2 := by
      refine (((unitsEquiv K).trans (unitsEquivFiber I)).summable_iff.2
        (hsum.subtype (orbitOf a ⁻¹' {I}))).congr fun q => ?_
      exact hval q
    calc ∑' β : (orbitOf a ⁻¹' {I}), g β
        = ∑' q : torsion K × (Fin (rank K) → ℤ),
            g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) :=
          (((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq (fun β => g β)).symm
      _ = ∑' q : torsion K × (Fin (rank K) → ℤ), G q.2 := tsum_congr hval
      _ = ∑' _ : torsion K, ∑' m, G m := hsG.tsum_prod' fun ζ => hsG.prod_factor ζ
      _ = (torsionOrder K : ℂ) * ∑' m, G m := by
          have := Fintype.ofFinite (torsion K)
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
            Nat.card_eq_fintype_card]
      _ = _ := by rw [← integral_eq_tsum_unitCube _ (hint I), integral_const_mul]
  rw [h2]
  convert hsum.hasSum.tsum_fiberwise (orbitOf a) using 1
  exact funext fun I => (hfib I).symm

/-- **The unfolding of the theta series with a coefficient.** Let $f$ be bounded with $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ of $K$, torsion included, let $\mathrm{Re}\, s > n / 2$ and $s' = 2 s / n$. Then $$2^{r - r_2} n R_K \int_0^\infty y^{s - 1} \int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) - f(0) h_{t(y, c)}(0)\big) \, dc \, dy = w_K \, \Gamma_{p, k}(s') \sum_I f(\alpha_I) \chi_\infty(\alpha_I) \, |N(\alpha_I)|^{-s'},$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. The series converges. -/
theorem hasSum_integral_coeffTheta_sub (hB : ∀ α, ‖f α‖ ≤ B)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * infinityWeight p k (u : K) = f α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (f (orbitRep a I) *
        (heckeGamma p k (2 * s / finrank ℚ K) * infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          (coeffTheta K p k a f (unitScale K y c) - f 0 * heckeTerm p k 0 (unitScale K y c))) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K)
      (unitScale K y c))) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (coeffTheta K p k a f (unitScale K y c) - f 0 * heckeTerm p k 0 (unitScale K y c))) :=
    fun y hy => (hasSum_integral_unitCube_coeffTheta hB hf hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_const.mul
        (measurable_integral_heckeTerm _)))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_coeffTerm_lt_top p k a hB hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    rw [tsum_lintegral_unitCube_coeffTerm hf (le_of_lt hy), ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun I => ?_
    simp only [hg]
    rw [enorm_mul, enorm_mul, ← ofReal_norm (x := (torsionOrder K : ℂ)), Complex.norm_natCast,
      ENNReal.ofReal_natCast, ← integral_const_mul]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  have hsum : Summable fun I => ∫ y in Ioi (0 : ℝ), g I y := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun I => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have heq := integral_tsum hmeas hfin
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).tsum_eq] at heq
  have hterm : ∀ I : Orbits a, ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), g I y =
      (torsionOrder K : ℂ) * (f (orbitRep a I) *
        (heckeGamma p k (2 * s / finrank ℚ K) * infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))) := by
    intro I
    rw [← integral_unitScale_heckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K)
          (unitScale K y c)))) =
        fun y : ℝ => ((torsionOrder K : ℂ) * f (orbitRep a I)) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, heckeTerm p k (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

end Unfold

section Periodic

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- If $\chi$ is unitary, the periodic coefficient has absolute value at most $1$. -/
theorem norm_periodicCoeff_le (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ‖periodicCoeff χ J α‖ ≤ 1 := by
  by_cases h : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · exact (norm_periodicCoeff_of_cond hu J h).le
  · rw [periodicCoeff_eq_zero_of_not J h, norm_zero]
    exact zero_le_one

/-- The ideal $\mathfrak{f} J$ is contained in $J$. -/
theorem conductor_mul_le (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    𝔣[conductorNZ χ * J] ≤ 𝔣[J] :=
  fun _ hx => mem_of_mem_conductor_mul (χ := χ) J hx

/-- The periodic coefficient of $J$ is periodic modulo $\mathfrak{f} J$, if $\chi$ is ramified at one place. -/
theorem periodicCoeff_add_of_mem (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) (α : K)
    {γ : K} (hγ : γ ∈ 𝔣[conductorNZ χ * J]) :
    periodicCoeff χ (FractionalIdeal.mk0 K J) (α + γ) =
      periodicCoeff χ (FractionalIdeal.mk0 K J) α := by
  refine periodicCoeff_eq_of_sub_mem hS _ ?_
  rw [add_sub_cancel_left]
  exact mem_conductor_mul_of_mem J hγ

/-- The finite Gauss sum of the periodic coefficient over $J / \mathfrak{f} J$ is the periodic Gauss sum $G_J(\beta)$ of `Langlands.Tate.periodicGaussCoeff`. -/
theorem residueGauss_periodicCoeff (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) :
    residueGauss K (FractionalIdeal.mk0 K J) (FractionalIdeal.mk0 K (conductorNZ χ * J))
      (periodicCoeff χ (FractionalIdeal.mk0 K J)) β = periodicGaussCoeff χ J β :=
  rfl

/-- The dual ideal $(\mathfrak{f} J \mathfrak{d})^{-1}$ is the ideal $D = (\mathfrak{f} J)^\vee$ of `Langlands.Tate.gaussDual`. -/
theorem dualIdeal_conductor_mul (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    dualIdeal K (FractionalIdeal.mk0 K (conductorNZ χ * J)) =
      (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_gaussDual, dual_eq_inv_mul_different]

/-- **The theta transformation with Gauss sum coefficients.** Let $\chi$ be unitary and ramified at one place, with conductor $\mathfrak{f}$, let $J$ be a nonzero integral ideal, let $c_J$ be the periodic coefficient `Langlands.Tate.periodicCoeff`, let $D = (\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$, let $p_v \in \{0, 1\}$ and let $t_w > 0$. Then $$\Theta_J^{p, k}(c_J; t) = \frac{(-i)^{|p| + |k|} \, \tau_J(\chi)}{N(\mathfrak{f} J) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{f} J}^{\vee, p, k}(\overline{c_D}; 1/t),$$ where $\tau_J(\chi)$ is the periodic Gauss sum `Langlands.Tate.periodicGaussSum` and the dual series runs over $\beta \in D$. -/
theorem coeffTheta_periodicCoeff_eq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    coeffTheta K p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J)) t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) * periodicGaussSum χ J *
        coeffDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β)) (fun w => 1 / t w) := by
  rw [coeffTheta_eq hp (conductor_mul_le χ J)
    (fun α _ γ hγ => periodicCoeff_add_of_mem hS J α hγ) (norm_periodicCoeff_le hu _) ht]
  have hD : coeffDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
      (residueGauss K (FractionalIdeal.mk0 K J) (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (periodicCoeff χ (FractionalIdeal.mk0 K J))) (fun w => 1 / t w) =
      periodicGaussSum χ J * coeffDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β)) (fun w => 1 / t w) := by
    have hsum : ∑' β : dualIdeal K (FractionalIdeal.mk0 K (conductorNZ χ * J)),
        residueGauss K (FractionalIdeal.mk0 K J) (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (periodicCoeff χ (FractionalIdeal.mk0 K J)) β *
        mixedGaussWeight p k (fun w => 1 / t w)
          (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) =
        periodicGaussSum χ J * ∑' β : dualIdeal K (FractionalIdeal.mk0 K (conductorNZ χ * J)),
          starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β) *
          mixedGaussWeight p k (fun w => 1 / t w)
            (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun β => ?_
      have hβ : (β : K) ∈ (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [← dualIdeal_conductor_mul]
        exact β.2
      rw [residueGauss_periodicCoeff, periodicGaussCoeff_eq_periodicGaussSum_mul hS hu J hβ,
        mul_assoc]
    rw [coeffDualTheta, coeffDualTheta, hsum]
    ring
  rw [hD]
  ring

end Periodic

end Langlands.Tate
