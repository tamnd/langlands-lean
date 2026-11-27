/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMixedSign
import Langlands.Tate.HeckeGeneralRamified

/-!
# Hecke's functional equation for ramified characters with signs

This file proves Hecke's functional equation for each Hecke character $\xi$ whose shifts $t_v$ at the infinite places are all equal to one number $t_0$. There is no condition on the signs of the integers $n_w$ at the complex places and no condition on the ramification. The unramified case is `Langlands.Tate.heckeFunctionalEquation_of_unramified_const_shift`. This file does the ramified case on the signed chain of `Langlands.Tate.HeckeMixedSignTheta`, `Langlands.Tate.HeckeMixedSignFE` and `Langlands.Tate.HeckeMixedSign`, with the periodic Gauss sum coefficients of `Langlands.Tate.HeckeRamifiedTheta` and `Langlands.Tate.HeckeGeneralRamified`.

## Main definitions

* `Langlands.Tate.signCoeffTheta`: the theta series $\Theta_{\mathfrak{a}}^{\varepsilon, p, k}(f; t) = \sum_{\alpha \in \mathfrak{a}} f(\alpha) h_t(\alpha)$ with a coefficient $f$ and the signed term `Langlands.Tate.signHeckeTerm`.
* `Langlands.Tate.signCoeffDualTheta`: the dual theta series with a coefficient $g$ and the signed Gauss weight.
* `Langlands.Tate.signRamifiedFEPair`: the Mathlib FE pair of the cube averages of $c_J$ and $\overline{c_D}$, with $D = (\mathfrak{f} J)^\vee$.
* `Langlands.Tate.signRamifiedPartial` and `Langlands.Tate.signRamifiedPartialConj`: the completed partial sums.
* `Langlands.Tate.signRamifiedClassCompleted` and `Langlands.Tate.signRamifiedClassCompletedConj`: the completed class sums.
* `Langlands.Tate.signRamifiedCompleted` and `Langlands.Tate.signRamifiedCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$.

## Main results

* `Langlands.Tate.signCoeffTheta_periodicCoeff_eq`: the theta transformation with the periodic Gauss sum coefficients $c_J$, with signs.
* `Langlands.Tate.signCoeffDualTheta_eq`: the dual series with a coefficient is the conjugate of the theta series of $(\mathfrak{b} \mathfrak{d})^{-1}$ with the conjugate coefficient.
* `Langlands.Tate.signRamifiedClassCompleted_eq_conj`: the functional equation of one class sum, with the root number `Langlands.Tate.ramifiedRootNumber` of $|n|$.
* `Langlands.Tate.entireFunctionalEquation_ramified_sign`: `Langlands.Tate.EntireFunctionalEquation` for a unitary character ramified at one finite place, with the parameters $(n_w, 0)$ and arbitrary signs.
* `Langlands.Tate.heckeFunctionalEquation_of_const_shift`: the conclusion of `Langlands.HeckeFunctionalEquationAt` for each Hecke character with $t_v = t_0$ at all infinite places.

## Proof

The proof follows `Langlands.Tate.HeckeGeneralRamified` and replaces the unsigned theta terms by the signed terms of `Langlands.Tate.HeckeMixedSignTheta`. At a complex place with $n_w < 0$, the signed term uses the conjugate embedding $\overline{\sigma_w}$ in place of $\sigma_w$ (`Langlands.Tate.signEmbedding`), so the weight is $(p, k)$ of $|n|$ and the sign is $\varepsilon_w$ = `Langlands.Tate.paramSign`. The unit condition of $c_J$ comes from `Langlands.Tate.infChar_mul_signInfinityWeight`. The Gamma factor of $|n|$ is the Gamma factor of $n$ by `Langlands.Tate.gammaFactor_absParam`. Because $c_J(0) = 0$ for a ramified character, the theta series has no constant term, so the completed functions are entire for each weight, the weight $0$ included. The assembly twists $\xi$ by $|\cdot|^{-t_0}$ to a unitary character $\chi$ with $t_v = 0$, and uses `Langlands.Tate.heckeFunctionalEquation_of_twist`.

## Open parts

* The characters whose shifts $t_v$ are not all equal. The twist by $|\cdot|^{-t_0}$ gives the shift $0$ only at all places at the same time.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen II*, Math. Z. 6 (1920).
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Sections 7 and 8.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem IsDedekindDomain
open scoped Real Classical nonZeroDivisors ENNReal RealInnerProductSpace

namespace Langlands.Tate

section Definitions

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The theta series of the ideal $\mathfrak{a}$ with the coefficient $f$: $\Theta_{\mathfrak{a}}^{p, k}(f; t) = \sum_{\alpha \in \mathfrak{a}} f(\alpha) h_t(\alpha)$, where $h_t$ is the normalized term `Langlands.Tate.signHeckeTerm`. -/
noncomputable def signCoeffTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), f α * signHeckeTerm ε p k (α : K) t

/-- The dual theta series of the ideal $\mathfrak{b}$ with the coefficient $g$: $$\Theta_{\mathfrak{b}}^{\vee, p, k}(g; t) = \prod_w t_w^{q_w / 2} \sum_{\beta \in (\mathfrak{b} \mathfrak{d})^{-1}} g(\beta) G_t^{p, k}(D_n \overline{\sigma(\beta)}).$$ For $g = 1$ it is `Langlands.Tate.heckeDualTheta`. -/
noncomputable def signCoeffDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    (t : InfinitePlace K → ℝ) : ℂ :=
  (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
    ∑' β : dualIdeal K b, g β *
      signMixedGaussWeight ε p k t (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β)
end Definitions

section Residues

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

variable (ε p k) in
/-- The series of `Langlands.Tate.signIdealTheta` converges for $t_w > 0$. -/
theorem summable_signIdealTheta (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (ξ η : K) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      signMixedGaussWeight ε p k t (globalEmbedding K (fun w => (c w : ℝ)) (ξ + α)) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((ξ + α) * η) : ℚ) : ℝ)) := by
  have h := summable_signMixedGaussWeight ε p k (globalLattice K c a) ht
    (globalEmbedding K (fun w => (c w : ℝ)) ξ)
    (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
  rw [← (globalLatticeEquiv K c a).summable_iff] at h
  refine h.congr fun α => ?_
  simp only [Function.comp_apply]
  rw [coe_globalLatticeEquiv, ← map_add, real_inner_comm, inner_globalConjEmbedding_dualScale,
    mul_comm η]

variable (ε p k) in
/-- The series of `Langlands.Tate.signIdealDualTheta` converges for $t_w > 0$. -/
theorem summable_signIdealDualTheta (c : InfinitePlace K → ℝˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (ξ η : K) :
    Summable fun β : dualIdeal K a =>
      signMixedGaussWeight ε p k t (globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) (β - η)) *
        cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (((β : K) - η) * ξ) : ℚ) : ℝ)) := by
  have h := summable_signMixedGaussWeight ε p k (dualLattice (globalLattice K c a)) ht
    (-globalConjEmbedding K (fun w => (dualScale K c w : ℝ)) η)
    (globalEmbedding K (fun w => (c w : ℝ)) ξ)
  rw [← (idealDualEquiv K c a).summable_iff] at h
  refine h.congr fun β => ?_
  simp only [Function.comp_apply]
  rw [coe_idealDualEquiv, neg_add_eq_sub, ← map_sub, inner_globalConjEmbedding_dualScale]

/-- The shifted series of normalized terms: for $t_w > 0$ and $\xi \in K$, $\sum_{\gamma \in \mathfrak{b}} h_t(\xi + \gamma) = \prod_w t_w^{q_w / 2} \theta_{\mathfrak{b}, 1}^{p, k}(\xi, 0; t)$. -/
theorem hasSum_signHeckeTerm_add (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) (ξ : K) :
    HasSum (fun γ : (b : FractionalIdeal (𝓞 K)⁰ K) => signHeckeTerm ε p k (ξ + γ) t)
      ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) * signIdealTheta K ε p k 1 b t ξ 0) := by
  have h := ((summable_signIdealTheta ε p k 1 b ht ξ 0).hasSum).mul_left
    (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2))
  rw [signIdealTheta]
  convert h using 2 with γ
  rw [coe_one_units, signHeckeTerm]
  simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
/-- **The sum over an ideal sorted by the residues.** Let $\mathfrak{b} \subseteq \mathfrak{a}$ be nonzero fractional ideals, let $f$ be bounded and periodic modulo $\mathfrak{b}$ on $\mathfrak{a}$, and let $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(f; t) = \sum_{q \in \mathfrak{a} / \mathfrak{b}} f(\xi_q) \prod_w t_w^{q_w / 2} \theta_{\mathfrak{b}, 1}^{p, k}(\xi_q, 0; t).$$ -/
theorem signCoeffTheta_eq_sum_residues {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) [Fintype (residueQuot K a b)] {f : K → ℂ}
    (hf : ∀ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K), ∀ γ ∈ (b : FractionalIdeal (𝓞 K)⁰ K),
      f (α + γ) = f α) {B : ℝ} (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    signCoeffTheta K ε p k a f t = ∑ q : residueQuot K a b, f (residueRep K q) *
      ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        signIdealTheta K ε p k 1 b t (residueRep K q) 0) := by
  have hsumA : Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      f α * signHeckeTerm ε p k (α : K) t :=
    Summable.of_norm_bounded ((summable_signHeckeTerm ε p k a ht).norm.mul_left B) fun α => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB α) (norm_nonneg _)
  let e := globalLatticeEquiv K (traceScale K) a
  let F : traceLattice K a → ℂ := fun ℓ => f (e.symm ℓ) * signHeckeTerm ε p k (e.symm ℓ : K) t
  have hFs : HasSum F (signCoeffTheta K ε p k a f t) := by
    have h := (e.symm.hasSum_iff (f := fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      f α * signHeckeTerm ε p k (α : K) t)).2 hsumA.hasSum
    exact h
  have hfib : ∀ q : residueQuot K a b,
      HasSum (fun ℓ : {ℓ : traceLattice K a // (ℓ : residueQuot K a b) = q} => F ℓ)
        (f (residueRep K q) * ((∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
          signIdealTheta K ε p k 1 b t (residueRep K q) 0)) := by
    intro q
    refine (fiberEquiv _ _ (traceLattice_le hab) q).symm.hasSum_iff.1 ?_
    refine (globalLatticeEquiv K (traceScale K) b).hasSum_iff.1 ?_
    refine ((hasSum_signHeckeTerm_add b ht (residueRep K q)).mul_left
      (f (residueRep K q))).congr_fun fun γ => ?_
    change f (e.symm (q.out + ⟨globalLatticeEquiv K (traceScale K) b γ, _⟩) : K) *
      signHeckeTerm ε p k (e.symm (q.out + ⟨globalLatticeEquiv K (traceScale K) b γ, _⟩) : K) t = _
    rw [coe_symm_add_globalLatticeEquiv hab, hf _ (e.symm q.out).2 _ γ.2]
    rfl
  have h1 := ((Equiv.sigmaFiberEquiv (fun ℓ : traceLattice K a => (ℓ : residueQuot K a b))).hasSum_iff.2
    hFs).sigma hfib
  exact h1.unique (hasSum_fintype _)

/-- **The transformation formula of the theta series with a periodic coefficient.** Let $p_v \in \{0, 1\}$, let $\mathfrak{b} \subseteq \mathfrak{a}$ be nonzero fractional ideals, let $f$ be bounded and periodic modulo $\mathfrak{b}$ on $\mathfrak{a}$, and let $t_w > 0$. Then $$\Theta_{\mathfrak{a}}^{p, k}(f; t) = \frac{(-i)^{|p| + |k|}}{N(\mathfrak{b}) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{b}}^{\vee, p, k}(\widehat{f}; 1/t),$$ where $\widehat{f}(\beta) = \sum_{q \in \mathfrak{a} / \mathfrak{b}} f(\xi_q) e^{2 \pi i \mathrm{Tr}(\beta \xi_q)}$ is the finite Gauss sum `Langlands.Tate.residueGauss` on the dual lattice $(\mathfrak{b} \mathfrak{d})^{-1}$. -/
theorem signCoeffTheta_eq (hp : ∀ v, p v ≤ 1) {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hab : (b : FractionalIdeal (𝓞 K)⁰ K) ≤ a) [Fintype (residueQuot K a b)] {f : K → ℂ}
    (hf : ∀ α ∈ (a : FractionalIdeal (𝓞 K)⁰ K), ∀ γ ∈ (b : FractionalIdeal (𝓞 K)⁰ K),
      f (α + γ) = f α) {B : ℝ} (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    signCoeffTheta K ε p k a f t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) *
        signCoeffDualTheta K ε p k b (residueGauss K a b f) (fun w => 1 / t w) := by
  have ht' : ∀ w, 0 < 1 / t w := fun w => one_div_pos.2 (ht w)
  have hq : ∀ ξ : K, (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
      signIdealTheta K ε p k 1 b t ξ 0 = (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) *
        ((∏ w, (((fun w => 1 / t w) w : ℝ) : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
          signIdealDualTheta K ε p k 1 b (fun w => 1 / t w) ξ 0) := by
    intro ξ
    rw [signIdealTheta_one_eq K ε p k b hp ht]
    simp only [mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    linear_combination
      ((((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ) *
        signIdealDualTheta K ε p k 1 b (fun w => 1 / t w) ξ 0 *
          prod_cpow_mul_mixedGaussConst (p := p) (k := k) ht
  have hD : ∑' β : dualIdeal K b, residueGauss K a b f β *
      signMixedGaussWeight ε p k (fun w => 1 / t w)
        (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) =
      ∑ q : residueQuot K a b, f (residueRep K q) *
        signIdealDualTheta K ε p k 1 b (fun w => 1 / t w) (residueRep K q) 0 := by
    simp only [signIdealDualTheta, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun q _ =>
      (summable_signIdealDualTheta ε p k 1 b ht' (residueRep K q) 0).mul_left (f (residueRep K q))]
    refine tsum_congr fun β => ?_
    rw [residueGauss, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [sub_zero, traceExp]
    ring
  rw [signCoeffTheta_eq_sum_residues hab hf hB ht, signCoeffDualTheta, hD]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hq]
  ring

end Residues

section Unfold

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {f : K → ℂ} {B : ℝ}

/-- For $t_w > 0$ and a bounded coefficient $f$, the family $f(\alpha) h_t(\alpha)$, $\alpha \in \mathfrak{a}$, is summable. -/
theorem summable_signCoeffTerm (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => f α * signHeckeTerm ε p k (α : K) t :=
  Summable.of_norm_bounded ((summable_signHeckeTerm ε p k a ht).norm.mul_left B) fun α => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB α) (norm_nonneg _)

/-- The sum of the cube integrals of $|f(\alpha) h_{t(y, c)}(\alpha)|$ is at most $B$ times the same sum for $f = 1$. -/
theorem tsum_lintegral_signCoeffTerm_le (hB : ∀ α, ‖f α‖ ≤ B) (y : ℝ) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ ≤
      ENNReal.ofReal B * ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun α => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun c => enorm_coeff_mul_le hB _ _

variable (ε p k a) in
/-- **The absolute convergence with a coefficient.** For a bounded coefficient $f$ and $\mathrm{Re}\, s > n / 2$, $$\int_0^\infty |y^{s - 1}| \sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |f(\alpha) h_{t(y, c)}(\alpha)| \, dc \, dy < \infty.$$ -/
theorem lintegral_enorm_mul_tsum_signCoeffTerm_lt_top (hB : ∀ α, ‖f α‖ ≤ B) {s : ℂ}
    (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1)‖ₑ * ∑' α : NonzeroElt a,
      ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun y => mul_le_mul_of_nonneg_left
    (tsum_lintegral_signCoeffTerm_le hB y) zero_le) ?_
  simp_rw [mul_left_comm _ (ENNReal.ofReal B)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_enorm_mul_tsum_signHeckeTerm_lt_top ε p k a hs)

/-- **The periodicity of the coefficient terms under all units.** Let $u = \zeta \prod_i \varepsilon_i^{m_i}$. If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $f(u \alpha) h_{t(y, c)}(u \alpha) = f(\alpha) h_{t(y, c + m)}(\alpha)$. -/
theorem signCoeffTerm_unitsEquiv
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * signInfinityWeight ε p k (u : K) = f α)
    (q : torsion K × (Fin (rank K) → ℤ)) (α : K) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ) :
    f ((unitsEquiv K q : K) * α) * signHeckeTerm ε p k ((unitsEquiv K q : K) * α) (unitScale K y c) =
      f α * signHeckeTerm ε p k α (unitScale K y (c + fun i => (q.2 i : ℝ))) := by
  rw [signHeckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _) α, ← mul_assoc, hf]
  congr 2
  funext w
  rw [unitScale_add_int, unitsEquiv_apply, Units.val_mul, map_mul, map_mul,
    (mem_torsion K).1 q.1.2 w, one_mul]

/-- **The unfolding of the absolute values with a coefficient.** If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $$\sum_{\alpha \in \mathfrak{a} \setminus 0} \int_{[0, 1)^r} |f(\alpha) h_{t(y, c)}(\alpha)| \, dc = w_K \sum_I \int_{\mathbb{R}^r} |f(\alpha_I) h_{t(y, c)}(\alpha_I)| \, dc.$$ -/
theorem tsum_lintegral_unitCube_signCoeffTerm
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * signInfinityWeight ε p k (u : K) = f α)
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ‖f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
  calc ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ‖f α * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ
      = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ‖f ((β.1 : NonzeroElt a) : K) *
            signHeckeTerm ε p k ((β.1 : NonzeroElt a) : K) (unitScale K y c)‖ₑ :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' q : torsion K × (Fin (rank K) → ℤ),
          ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
            ‖f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K)
              (unitScale K y (c + fun i => (q.2 i : ℝ)))‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun q => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, signCoeffTerm_unitsEquiv hf _ _ hy]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ‖f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ‖f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

variable (a) in
/-- For $t_w > 0$, the theta series with a coefficient minus its term $\alpha = 0$ is the sum over $\alpha \in \mathfrak{a} \setminus 0$. -/
theorem signCoeffTheta_sub_eq_tsum (hB : ∀ α, ‖f α‖ ≤ B) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) :
    signCoeffTheta K ε p k a f t - f 0 * signHeckeTerm ε p k 0 t =
      ∑' α : NonzeroElt a, f α * signHeckeTerm ε p k (α : K) t := by
  let z : (a : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  rw [signCoeffTheta, (summable_signCoeffTerm hB ht).tsum_eq_add_tsum_ite z]
  rw [show ((z : (a : FractionalIdeal (𝓞 K)⁰ K)) : K) = 0 from rfl, add_sub_cancel_left]
  refine Eq.trans ?_ (tsum_subtype {α : (a : FractionalIdeal (𝓞 K)⁰ K) | (α : K) ≠ 0}
    (fun α => f α * signHeckeTerm ε p k (α : K) t)).symm
  refine tsum_congr fun α => ?_
  have hz : α = z ↔ (α : K) = 0 := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : (α : K) = 0
  · simp [hz.2 h, Set.indicator, z]
  · simp [mt hz.1 h, h]

/-- **The unfolding with a coefficient for a fixed $y$.** If $f$ is bounded, $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y > 0$, then $$\int_{[0, 1)^r} \big(\Theta_{\mathfrak{a}}^{p, k}(f; t(y, c)) - f(0) h_{t(y, c)}(0)\big) \, dc = w_K \sum_I f(\alpha_I) \int_{\mathbb{R}^r} h_{t(y, c)}(\alpha_I) \, dc.$$ -/
theorem hasSum_integral_unitCube_signCoeffTheta (hB : ∀ α, ‖f α‖ ≤ B)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * signInfinityWeight ε p k (u : K) = f α)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)))
      (∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (signCoeffTheta K ε p k a f (unitScale K y c) - f 0 * signHeckeTerm ε p k 0 (unitScale K y c))) := by
  have hS : ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      ‖f α * signHeckeTerm ε p k (α : K) (unitScale K y c)‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (tsum_lintegral_signHeckeTerm_le hy))) (tsum_lintegral_signCoeffTerm_le hB y)
  have hm : ∀ x : K, Measurable fun c => f x * signHeckeTerm ε p k x (unitScale K y c) := fun x =>
    measurable_const.mul ((measurable_signHeckeTerm x).comp (continuous_unitScale y).measurable)
  set g : NonzeroElt a → ℂ := fun α => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
    f α * signHeckeTerm ε p k (α : K) (unitScale K y c) with hg
  have h2 : ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      (signCoeffTheta K ε p k a f (unitScale K y c) - f 0 * signHeckeTerm ε p k 0 (unitScale K y c)) =
        ∑' α, g α := by
    simp_rw [signCoeffTheta_sub_eq_tsum a hB (unitScale_pos hy _)]
    exact integral_tsum (fun α => (hm _).aestronglyMeasurable) hS
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hS) fun α => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have hE := tsum_lintegral_unitCube_signCoeffTerm (a := a) hf hy.le
  have hw1 : (1 : ℝ≥0∞) ≤ torsionOrder K :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  have hint : ∀ I : Orbits a, Integrable fun c =>
      f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨(hm _).aestronglyMeasurable, lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (hE ▸ hS)
      ((le_mul_of_one_le_left' hw1).trans (ENNReal.le_tsum (f := fun I : Orbits a =>
        (torsionOrder K : ℝ≥0∞) * ∫⁻ c, ‖f (orbitRep a I) *
          signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)‖ₑ) I)))⟩
  have hfib : ∀ I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), g β =
      (torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)) := by
    intro I
    set G : (Fin (rank K) → ℤ) → ℂ := fun m => ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
      f (orbitRep a I) * signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y (c + fun i => (m i : ℝ)))
      with hG
    have hval : ∀ q, g ((((unitsEquiv K).trans (unitsEquivFiber I)) q : _) : NonzeroElt a) =
        G q.2 := by
      intro q
      simp only [hg, hG]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only
      rw [Equiv.trans_apply, coe_unitsEquivFiber, signCoeffTerm_unitsEquiv hf _ _ hy.le]
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
theorem hasSum_integral_signCoeffTheta_sub (hB : ∀ α, ‖f α‖ ≤ B)
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * signInfinityWeight ε p k (u : K) = f α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (f (orbitRep a I) *
        (heckeGamma p k (2 * s / finrank ℚ K) * signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          (signCoeffTheta K ε p k a f (unitScale K y c) - f 0 * signHeckeTerm ε p k 0 (unitScale K y c))) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K)
      (unitScale K y c))) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y) ((y : ℂ) ^ (s - 1) *
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        (signCoeffTheta K ε p k a f (unitScale K y c) - f 0 * signHeckeTerm ε p k 0 (unitScale K y c))) :=
    fun y hy => (hasSum_integral_unitCube_signCoeffTheta hB hf hy).mul_left _
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_const.mul
        (measurable_integral_signHeckeTerm _)))).aestronglyMeasurable
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm]
    refine ne_top_of_le_ne_top (lintegral_enorm_mul_tsum_signCoeffTerm_lt_top ε p k a hB hs).ne
      (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_)
    rw [tsum_lintegral_unitCube_signCoeffTerm hf (le_of_lt hy), ← ENNReal.tsum_mul_left]
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
        (heckeGamma p k (2 * s / finrank ℚ K) * signInfinityWeight ε p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K)))) := by
    intro I
    rw [← integral_unitScale_signHeckeTerm hs0 (orbitRep a I).2]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        (f (orbitRep a I) * ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K)
          (unitScale K y c)))) =
        fun y : ℝ => ((torsionOrder K : ℂ) * f (orbitRep a I)) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, signHeckeTerm ε p k (orbitRep a I : K) (unitScale K y c)) from
      funext fun y => by ring, integral_const_mul]
    ring
  rw [heq]
  exact (hsum.hasSum.mul_left _).congr_fun fun I => (hterm I).symm

end Unfold

section Periodic

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
/-- **The theta transformation with Gauss sum coefficients.** Let $\chi$ be unitary and ramified at one place, with conductor $\mathfrak{f}$, let $J$ be a nonzero integral ideal, let $c_J$ be the periodic coefficient `Langlands.Tate.periodicCoeff`, let $D = (\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$, let $p_v \in \{0, 1\}$ and let $t_w > 0$. Then $$\Theta_J^{p, k}(c_J; t) = \frac{(-i)^{|p| + |k|} \, \tau_J(\chi)}{N(\mathfrak{f} J) 2^{-r_2} \sqrt{|d_K|} \, \prod_w \sqrt{t_w}^{\,n_w}} \, \Theta_{\mathfrak{f} J}^{\vee, p, k}(\overline{c_D}; 1/t),$$ where $\tau_J(\chi)$ is the periodic Gauss sum `Langlands.Tate.periodicGaussSum` and the dual series runs over $\beta \in D$. -/
theorem signCoeffTheta_periodicCoeff_eq (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    signCoeffTheta K ε p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J)) t =
      (-I) ^ (∑ v, p v + ∑ w, k w) *
        (((FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℝ) *
          (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ) *
        (((∏ w, √(t w) ^ mult w)⁻¹ : ℝ) : ℂ) * periodicGaussSum χ J *
        signCoeffDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β)) (fun w => 1 / t w) := by
  rw [signCoeffTheta_eq hp (conductor_mul_le χ J)
    (fun α _ γ hγ => periodicCoeff_add_of_mem hS J α hγ) (norm_periodicCoeff_le hu _) ht]
  have hD : signCoeffDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
      (residueGauss K (FractionalIdeal.mk0 K J) (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (periodicCoeff χ (FractionalIdeal.mk0 K J))) (fun w => 1 / t w) =
      periodicGaussSum χ J * signCoeffDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β)) (fun w => 1 / t w) := by
    have hsum : ∑' β : dualIdeal K (FractionalIdeal.mk0 K (conductorNZ χ * J)),
        residueGauss K (FractionalIdeal.mk0 K J) (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (periodicCoeff χ (FractionalIdeal.mk0 K J)) β *
        signMixedGaussWeight ε p k (fun w => 1 / t w)
          (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) =
        periodicGaussSum χ J * ∑' β : dualIdeal K (FractionalIdeal.mk0 K (conductorNZ χ * J)),
          starRingEnd ℂ (periodicCoeff χ (gaussDual χ J) β) *
          signMixedGaussWeight ε p k (fun w => 1 / t w)
            (globalConjEmbedding K (fun w => (dualScale K 1 w : ℝ)) β) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun β => ?_
      have hβ : (β : K) ∈ (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [← dualIdeal_conductor_mul]
        exact β.2
      rw [residueGauss_periodicCoeff, periodicGaussCoeff_eq_periodicGaussSum_mul hS hu J hβ,
        mul_assoc]
    rw [signCoeffDualTheta, signCoeffDualTheta, hsum]
    ring
  rw [hD]
  ring

end Periodic

section Coeff

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {f : K → ℂ}

/-- If $|f| \le 1$, $f(0) = 0$, $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(f; t)| \le C_{p, k} (\theta_{\mathfrak{b}}(s / 4) - 1)$. The bound holds for each weight, also for the weight $0$. -/
theorem norm_signCoeffTheta_le (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) :
    ‖signCoeffTheta K ε p k b f t‖ ≤ heckeConst p k * (dedekindTheta K b (fun _ => s / 4) - 1) := by
  let z : (b : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((b : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  have hθ : HasSum (fun α : (b : FractionalIdeal (𝓞 K)⁰ K) => thetaTerm (α : K) (fun _ => s / 4))
      (dedekindTheta K b (fun _ => s / 4)) :=
    (summable_dedekindTheta b (t := fun _ => s / 4) fun _ => by positivity).hasSum
  have hG := (hθ.sub (hasSum_ite_eq z (1 : ℝ))).mul_left (heckeConst p k)
  refine tsum_of_norm_bounded hG fun α => ?_
  by_cases h : α = z
  · subst h
    simp [thetaTerm, z, hf0]
  · simp only [h, ↓reduceIte, sub_zero, norm_mul]
    calc ‖f α‖ * ‖signHeckeTerm ε p k (α : K) t‖ ≤ 1 * ‖signHeckeTerm ε p k (α : K) t‖ :=
          mul_le_mul_of_nonneg_right (hf1 _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact norm_signHeckeTerm_le_const hs.le hst _

/-- If $|f| \le 1$, then the theta series $\Theta_{\mathfrak{b}}^{p, k}(f; \cdot)$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_signCoeffTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) : ContinuousAt (signCoeffTheta K ε p k b f) t := by
  obtain ⟨m, hm, hmt⟩ : ∃ m > 0, ∀ w, m ≤ t w := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty t, ?_, fun w => Finset.inf'_le _ (Finset.mem_univ w)⟩
    exact (Finset.lt_inf'_iff _).2 fun w _ => ht w
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | m / 2 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have htU : t ∈ U := mem_iInter.2 fun w => (half_lt_self hm).trans_le (hmt w)
  have hc : ContinuousOn (signCoeffTheta K ε p k b f) U := by
    refine continuousOn_tsum (fun α => continuousOn_const.mul ((continuousOn_signHeckeTerm (α : K)).mono
        fun s hs w => (half_pos hm).trans (mem_iInter.1 hs w)))
      ((summable_dedekindTheta b (t := fun _ => m / 2 / 4) fun _ => by positivity).mul_left
        (heckeConst p k)) ?_
    intro α s hs
    rw [norm_mul]
    calc ‖f α‖ * ‖signHeckeTerm ε p k (α : K) s‖ ≤ 1 * ‖signHeckeTerm ε p k (α : K) s‖ :=
          mul_le_mul_of_nonneg_right (hf1 _) (norm_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          exact norm_signHeckeTerm_le_const (half_pos hm).le (fun w => (mem_iInter.1 hs w).le) _
  exact hc.continuousAt (hU.mem_nhds htU)

variable (ε p k) in
/-- **The dual series with a coefficient.** For $t_w \ge 0$, the dual theta series of $\mathfrak{b}$ with the coefficient $g$ is the complex conjugate of the theta series of $(\mathfrak{b} \mathfrak{d})^{-1}$ with the coefficient $\bar{g}$ at the point $(n_w^2 t_w)_w$. -/
theorem signCoeffDualTheta_eq (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) :
    signCoeffDualTheta K ε p k b g t =
      conj (signCoeffTheta K ε p k (dualUnit K b) (fun β => conj (g β))
        (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have e : (dualIdeal K b : FractionalIdeal (𝓞 K)⁰ K) =
      ((dualUnit K b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
    (coe_dualUnit_eq K b).symm
  have hs : (fun w => (dualScale K 1 w : ℝ)) = fun w => (mult w : ℝ) := funext (coe_dualScale_one K)
  rw [signCoeffDualTheta, signCoeffTheta, Complex.conj_tsum, ← tsum_mul_left]
  let E : {x : K // x ∈ dualIdeal K b} ≃ {x : K // x ∈ ((dualUnit K b :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)} :=
    Equiv.subtypeEquivRight fun x => by rw [e]
  refine Eq.trans ?_ (E.tsum_eq _)
  refine tsum_congr fun β => ?_
  have hd := signDualTerm_eq (ε := ε) (p := p) (k := k) ht (β : K)
  simp only [hs]
  change _ = conj (conj (g β) * signHeckeTerm ε p k (β : K) fun w => (mult w : ℝ) ^ 2 * t w)
  rw [map_mul, Complex.conj_conj, ← hd]
  ring

/-- **The periodicity with a coefficient.** If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $\Theta_{\mathfrak{b}}^{p, k}(f; t(y, c + m)) = \Theta_{\mathfrak{b}}^{p, k}(f; t(y, c))$ for each integer vector $m$. -/
theorem signCoeffTheta_unitScale_add_int
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * signInfinityWeight ε p k (u : K) = f α)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    signCoeffTheta K ε p k b f (unitScale K y (c + fun i => (m i : ℝ))) =
      signCoeffTheta K ε p k b f (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h, signCoeffTheta, signCoeffTheta]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) (unitOfInt K m)).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [signHeckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _), ← mul_assoc, hf]

end Coeff

section Cube

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The cube average $F(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{b}}^{p, k}(f; t(y, c)) \, dc$ of the theta series with the coefficient $f$. -/
noncomputable def signCoeffCubeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ) (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), signCoeffTheta K ε p k b f (unitScale K y c)

/-- The cube average $G(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{b}}^{\vee, p, k}(g; t(y, -c)) \, dc$ of the dual theta series with the coefficient $g$. -/
noncomputable def signCoeffCubeDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ) (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    signCoeffDualTheta K ε p k b g (unitScale K y (-c))

variable {K ε p k}
variable {f g : K → ℂ}

/-- If $|g| \le 1$, then the dual theta series $\Theta_{\mathfrak{b}}^{\vee, p, k}(g; \cdot)$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_signCoeffDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) : ContinuousAt (signCoeffDualTheta K ε p k b g) t := by
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | 0 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have he : (fun s => conj (signCoeffTheta K ε p k (dualUnit K b) (fun β => conj (g β))
      (fun w => (mult w : ℝ) ^ 2 * s w))) =ᶠ[𝓝 t] signCoeffDualTheta K ε p k b g := by
    filter_upwards [hU.mem_nhds (mem_iInter.2 ht)] with s hs
    exact (signCoeffDualTheta_eq ε p k b g fun w => (mem_iInter.1 hs w).le).symm
  refine ContinuousAt.congr ?_ he
  refine Complex.continuous_conj.continuousAt.comp ?_
  refine ContinuousAt.comp (g := signCoeffTheta K ε p k (dualUnit K b) (fun β => conj (g β)))
    (continuousAt_signCoeffTheta (fun β => by rw [Complex.norm_conj]; exact hg1 β) _
      fun w => mul_pos (one_pos.trans_le (one_le_mult_sq w)) (ht w)) ?_
  exact (continuous_pi fun w => continuous_const.mul (continuous_apply w)).continuousAt

/-- If $|g| \le 1$, $g(0) = 0$, $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series with the coefficient $g$ at $t$ has the absolute value at most $C_{p, k} (\theta_{(\mathfrak{b} \mathfrak{d})^{-1}}(s / 4) - 1)$. -/
theorem norm_signCoeffDualTheta_le (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) :
    ‖signCoeffDualTheta K ε p k b g t‖ ≤
      heckeConst p k * (dedekindTheta K (dualUnit K b) (fun _ => s / 4) - 1) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [signCoeffDualTheta_eq ε p k b g fun w => hs.le.trans (hst w), Complex.norm_conj]
  exact norm_signCoeffTheta_le (fun β => by rw [Complex.norm_conj]; exact hg1 β)
    (by rw [hg0, map_zero]) _ hs hst'

/-- If $|f| \le 1$ and $f(0) = 0$, then the cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_signCoeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ContinuousOn (signCoeffCubeTheta K ε p k b f) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i) (fun _ ht => continuousAt_signCoeffTheta hf1 b ht)
    fun _ hs => ⟨_, fun _ hst => norm_signCoeffTheta_le hf1 hf0 b hs hst⟩

/-- If $|g| \le 1$ and $g(0) = 0$, then the dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_signCoeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ContinuousOn (signCoeffCubeDualTheta K ε p k b g) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_signCoeffDualTheta hg1 b ht)
    fun _ hs => ⟨_, fun _ hst => norm_signCoeffDualTheta_le hg1 hg0 b hs hst⟩

/-- If $|f| \le 1$ and $f(0) = 0$, then $F(y) = O(y^r)$ at infinity for each real $r$. There is no condition on the weight, because the term of $\alpha = 0$ is zero. -/
theorem isBigO_signCoeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    signCoeffCubeTheta K ε p k b f =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := id) _ (fun _ hc i => abs_le_one_of_mem_unitCube hc i) b
    heckeConst_pos.le (fun _ hs _ hst => norm_signCoeffTheta_le hf1 hf0 b hs hst) r

/-- If $|g| \le 1$ and $g(0) = 0$, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_signCoeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    signCoeffCubeDualTheta K ε p k b g =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := Neg.neg) _
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (dualUnit K b) heckeConst_pos.le (fun _ hs _ hst => norm_signCoeffDualTheta_le hg1 hg0 b hs hst) r

end Cube

section Pair

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- The theta transformation of `Langlands.Tate.signCoeffTheta_periodicCoeff_eq` at the point $t(y, c)$, with $1 / t(y, c) = t(y^{-1}, -c)$. -/
theorem signCoeffTheta_periodicCoeff_unitScale (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    signCoeffTheta K ε p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
        (unitScale K y c) =
      ramifiedRootConst χ p k J * (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) *
        signCoeffDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) (unitScale K y⁻¹ (-c)) := by
  have h : (fun w => 1 / unitScale K y c w) = unitScale K y⁻¹ (-c) := by
    funext w
    rw [one_div, unitScale_inv]
  rw [signCoeffTheta_periodicCoeff_eq hS hu hp J (unitScale_pos hy c), prod_sqrt_unitScale hy.le, h,
    ramifiedRootConst, heckeRootConst]
  ring

/-- **The functional equation of the cube averages of $c_J$.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. For $x > 0$, $F_J(1 / x) = \varepsilon_J \, x^{n / 2} \, G_J(x)$, where $F_J$ is the cube average of $c_J$ on $J$ and $G_J$ is the dual cube average of $\overline{c_D}$ on $\mathfrak{f} J$. -/
theorem signCoeffCubeTheta_one_div (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {x : ℝ} (hx : 0 < x) :
    signCoeffCubeTheta K ε p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
        (1 / x) =
      (ramifiedRootConst χ p k J * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [signCoeffCubeTheta, signCoeffCubeDualTheta, smul_eq_mul]
  simp_rw [signCoeffTheta_periodicCoeff_unitScale hS hu hp J (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul]

variable (ε p k) in
/-- **The FE pair of a ramified character.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. The cube averages $F_J$ of $c_J$ and $G_J$ of $\overline{c_D}$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon_J$ and with both constant terms zero. There is no condition on the weight, since $c_J(0) = 0$. -/
noncomputable def signRamifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : WeakFEPair ℂ where
  f := signCoeffCubeTheta K ε p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
  g := signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
    (fun β => conj (periodicCoeff χ (gaussDual χ J) β))
  k := finrank ℚ K / 2
  ε := ramifiedRootConst χ p k J
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_signCoeffCubeTheta (norm_periodicCoeff_le hu _) (periodicCoeff_zero _)
    _).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_signCoeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
    (by rw [periodicCoeff_zero, map_zero]) _).locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := ramifiedRootConst_ne_zero hS hu J
  h_feq x hx := signCoeffCubeTheta_one_div hS hu hp J hx
  hf_top r := by
    simpa only [sub_zero] using isBigO_signCoeffCubeTheta (norm_periodicCoeff_le hu _)
      (periodicCoeff_zero _) _ r
  hg_top r := by
    simpa only [sub_zero] using isBigO_signCoeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
      (by rw [periodicCoeff_zero, map_zero]) _ r

/-- The FE pair of a ramified character is a strong FE pair. -/
theorem isStrongFEPair_signRamifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : IsStrongFEPair (signRamifiedFEPair ε p k hS hu hp J) :=
  ⟨rfl, rfl⟩

end Pair

section Completed

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable (hS : (ramifiedSet χ).Nonempty) (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
variable (hp : ∀ v, p v ≤ 1)

/-- The completed function of the ramified pair is the Mellin transform of $F_J$. -/
theorem Λ_signRamifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (signRamifiedFEPair ε p k hS hu hp J).Λ = mellin (signCoeffCubeTheta K ε p k (FractionalIdeal.mk0 K J)
      (periodicCoeff χ (FractionalIdeal.mk0 K J))) :=
  (isStrongFEPair_signRamifiedFEPair hS hu hp J).Λ_eq

/-- The completed function of the dual ramified pair is the Mellin transform of $G_J$. -/
theorem symm_Λ_signRamifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (signRamifiedFEPair ε p k hS hu hp J).symm.Λ =
      mellin (signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) :=
  (isStrongFEPair_signRamifiedFEPair hS hu hp J).symm_Λ_eq

/-- The functional equation $\Lambda_J(n / 2 - s) = \varepsilon_J \, \mathcal{M}G_J(s)$ of the ramified pair for all complex $s$. -/
theorem Λ_signRamifiedFEPair_sub (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (signRamifiedFEPair ε p k hS hu hp J).Λ (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J *
        mellin (signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s := by
  have := (signRamifiedFEPair ε p k hS hu hp J).functional_equation s
  rw [symm_Λ_signRamifiedFEPair_eq hS hu hp J, smul_eq_mul] at this
  convert this using 2
  · simp [signRamifiedFEPair]
  · rfl

/-- **The dual series is the conjugate series.** If $c_D(u \beta) \chi_\infty(u) = c_D(\beta)$ for all units $u$, where $D = (\mathfrak{f} J)^\vee$, and $y \ge 0$, then $G_J(y) = \overline{F_D(\lambda y)}$, where $F_D$ is the cube average of $c_D$ on $D$. -/
theorem signCoeffCubeDualTheta_eq_conj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β) {y : ℝ} (hy : 0 ≤ y) :
    signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) y =
      conj (signCoeffCubeTheta K ε p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))
        (heckeScale K * y)) := by
  have h : ∀ c : Fin (rank K) → ℝ,
      (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w) =
        unitScale K (heckeScale K * y) (heckeShift K - c) :=
    fun c => funext fun w => mult_sq_mul_unitScale_neg y c w
  have hcc : (fun β => conj (conj (periodicCoeff χ (gaussDual χ J) β))) =
      periodicCoeff χ (gaussDual χ J) := funext fun β => Complex.conj_conj _
  have hd : dualUnit K (FractionalIdeal.mk0 K (conductorNZ χ * J)) = gaussDual χ J := rfl
  have hnn : ∀ (c : Fin (rank K) → ℝ) (w : InfinitePlace K), 0 ≤ unitScale K y (-c) w :=
    fun c w => mul_nonneg hy (Real.exp_pos _).le
  rw [signCoeffCubeDualTheta, signCoeffCubeTheta]
  simp_rw [signCoeffDualTheta_eq ε p k _ _ (hnn _), hcc, hd, h]
  rw [integral_conj, integral_unitCube_sub
    (fun c => signCoeffTheta K ε p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))
      (unitScale K (heckeScale K * y) c))
    (fun m c => signCoeffTheta_unitScale_add_int hc _ (mul_nonneg (heckeScale_pos K).le hy) c m)
    (heckeShift K)]

/-- **The Mellin transform of the dual series.** Under the unit condition of `Langlands.Tate.signCoeffCubeDualTheta_eq_conj`, $\mathcal{M}G_J(s) = \lambda^{-s} \, \overline{\mathcal{M}F_D(\bar{s})}$ for all complex $s$. -/
theorem mellin_signCoeffCubeDualTheta (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    mellin (signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      (heckeScale K : ℂ) ^ (-s) * conj (mellin (signCoeffCubeTheta K ε p k (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J))) (conj s)) := by
  have h : mellin (signCoeffCubeDualTheta K ε p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      mellin (fun y => conj (signCoeffCubeTheta K ε p k (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J)) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [signCoeffCubeDualTheta_eq_conj J hc (le_of_lt hy)]
  rw [h, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul, map_mul,
    conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]

variable (χ ε p k) in
/-- The completed partial sum $\Lambda_J(s) = 2^r c_K \, \mathcal{M}F_J(s)$ of the coefficient $c_J$ on the integral ideal $J$. -/
noncomputable def signRamifiedPartial (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (signCoeffCubeTheta K ε p k (FractionalIdeal.mk0 K J)
      (periodicCoeff χ (FractionalIdeal.mk0 K J))) s

variable (χ ε p k) in
/-- The conjugate completed partial sum $\Lambda^*_D(s) = \overline{2^r c_K \, \mathcal{M}F_D(\bar{s})}$ of the coefficient $c_D$ on $D = (\mathfrak{f} J)^\vee$. -/
noncomputable def signRamifiedPartialConj (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  conj (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (signCoeffCubeTheta K ε p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))) (conj s))

include hS hu hp in
/-- **The completed partial sum is entire.** -/
theorem differentiable_signRamifiedPartial (J : (Ideal (𝓞 K))⁰) :
    Differentiable ℂ (signRamifiedPartial χ ε p k J) := by
  have e : signRamifiedPartial χ ε p k J =
      fun s => ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signRamifiedFEPair ε p k hS hu hp J).Λ s := by
    funext s
    rw [Λ_signRamifiedFEPair_eq hS hu hp J, signRamifiedPartial]
  rw [e]
  exact (isStrongFEPair_signRamifiedFEPair hS hu hp J).differentiable_Λ.const_mul _

include hS hu hp in
/-- Under the unit condition for $c_D$, $\Lambda^*_D(s) = \lambda^s \, 2^r c_K \, \mathcal{M}G_J(s)$. -/
theorem signRamifiedPartialConj_eq (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    signRamifiedPartialConj χ ε p k J s = (heckeScale K : ℂ) ^ s *
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signRamifiedFEPair ε p k hS hu hp J).symm.Λ s) := by
  have hl : (heckeScale K : ℂ) ^ s * (heckeScale K : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.2 (heckeScale_pos K).ne'), add_neg_cancel, cpow_zero]
  rw [symm_Λ_signRamifiedFEPair_eq hS hu hp J, mellin_signCoeffCubeDualTheta J hc, signRamifiedPartialConj,
    map_mul, Complex.conj_ofReal]
  linear_combination (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * conj (mellin (signCoeffCubeTheta K ε p k
    (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))) (conj s))) * (-hl)

include hS hu hp in
/-- **The conjugate completed partial sum is entire.** -/
theorem differentiable_signRamifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β) :
    Differentiable ℂ (signRamifiedPartialConj χ ε p k J) := by
  have e : signRamifiedPartialConj χ ε p k J = fun s => (heckeScale K : ℂ) ^ s *
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (signRamifiedFEPair ε p k hS hu hp J).symm.Λ s) :=
    funext (signRamifiedPartialConj_eq hS hu hp J hc)
  rw [e]
  refine Differentiable.mul (fun s => ?_)
    ((isStrongFEPair_signRamifiedFEPair hS hu hp J).symm.differentiable_Λ.const_mul _)
  exact (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (heckeScale_pos K).ne')))

include hS hu hp in
/-- **The functional equation of the completed partial sums.** Let $\chi$ be unitary and ramified at one place, let $p_v \le 1$, and let $c_D$ satisfy the unit condition. Then for all complex $s$, $\Lambda_J(n / 2 - s) = \varepsilon_J \, \lambda^{-s} \, \Lambda^*_D(s)$. -/
theorem signRamifiedPartial_sub (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    signRamifiedPartial χ ε p k J (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J * (heckeScale K : ℂ) ^ (-s) * signRamifiedPartialConj χ ε p k J s := by
  rw [signRamifiedPartial, ← Λ_signRamifiedFEPair_eq hS hu hp J, Λ_signRamifiedFEPair_sub,
    mellin_signCoeffCubeDualTheta J hc, signRamifiedPartialConj, map_mul, Complex.conj_ofReal]
  ring

include hu in
/-- **The completed partial sum as a series.** If $c_J$ satisfies the unit condition and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_J(s) = \sum_{\alpha \in (J \setminus 0) / \mathcal{O}_K^\times} w_K \, c_J(\alpha) \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_signRamifiedPartial (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (α : K), periodicCoeff χ (FractionalIdeal.mk0 K J) ((u : K) * α) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (FractionalIdeal.mk0 K J) α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (FractionalIdeal.mk0 K J) => (torsionOrder K : ℂ) *
        (periodicCoeff χ (FractionalIdeal.mk0 K J) (orbitRep (FractionalIdeal.mk0 K J) I) *
        (heckeGamma p k (2 * s / finrank ℚ K) *
          signInfinityWeight ε p k (orbitRep (FractionalIdeal.mk0 K J) I : K) *
          ((|(Algebra.norm ℚ (orbitRep (FractionalIdeal.mk0 K J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (signRamifiedPartial χ ε p k J s) := by
  have h := hasSum_integral_signCoeffTheta_sub (a := FractionalIdeal.mk0 K J)
    (norm_periodicCoeff_le hu _) hc hs
  simp only [periodicCoeff_zero, zero_mul, sub_zero] at h
  rw [signRamifiedPartial, mellin]
  simp_rw [smul_eq_mul, signCoeffCubeTheta]
  exact h

include hu in
/-- **The conjugate completed partial sum as a series.** If $c_D$ satisfies the unit condition and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda^*_D(s) = \sum_{\beta \in (D \setminus 0) / \mathcal{O}_K^\times} w_K \, \overline{c_D(\beta)} \, \Gamma_{p, k}(s') \, \overline{\chi_\infty(\beta)} \, |N(\beta)|^{-s'}.$$ -/
theorem hasSum_signRamifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) = periodicCoeff χ (gaussDual χ J) β)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (gaussDual χ J) => (torsionOrder K : ℂ) *
        (conj (periodicCoeff χ (gaussDual χ J) (orbitRep (gaussDual χ J) I)) *
        (heckeGamma p k (2 * s / finrank ℚ K) *
          conj (signInfinityWeight ε p k (orbitRep (gaussDual χ J) I : K)) *
          ((|(Algebra.norm ℚ (orbitRep (gaussDual χ J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (signRamifiedPartialConj χ ε p k J s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have h := hasSum_integral_signCoeffTheta_sub (a := gaussDual χ J)
    (norm_periodicCoeff_le hu _) hc hs'
  simp only [periodicCoeff_zero, zero_mul, sub_zero] at h
  have e := h.map (starRingEnd ℂ) continuous_conj
  have hv : signRamifiedPartialConj χ ε p k J s = starRingEnd ℂ (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (conj s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), signCoeffTheta K ε p k (gaussDual χ J)
          (periodicCoeff χ (gaussDual χ J)) (unitScale K y c)) := by
    rw [signRamifiedPartialConj, mellin]
    simp_rw [smul_eq_mul, signCoeffCubeTheta]
  rw [hv]
  have hcs : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hcs, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_heckeGamma]

end Completed



section Unit

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The unit condition for the periodic coefficient with signs.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place, with arbitrary signs of the $n_w$, let $(p, k)$ be the weight of $|n|$ and let $\varepsilon$ be the sign of $n$. Then $c_J(u \alpha) \chi^{\varepsilon, p, k}_\infty(u) = c_J(\alpha)$ for each unit $u$ of $\mathcal{O}_K$, each $\alpha \in K$ and each nonzero fractional ideal $J$. -/
theorem periodicCoeff_unit_mul_signInfinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (α : K) :
    periodicCoeff χ J ((u : K) * α) * signInfinityWeight (paramSign K n)
        (realWeight K (absParam K n)) (complexWeight K (absParam K n)) (u : K) =
      periodicCoeff χ J α := by
  have h : (infChar χ (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℂ) *
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) (u : K) = 1 :=
    infChar_mul_signInfinityWeight hn _
  rw [periodicCoeff_unit_mul]
  linear_combination (periodicCoeff χ J α) * h

/-- **The periodic coefficient and the coefficient of the $L$-series with signs.** If $\chi$ has the parameters $(n_w, 0)$, with arbitrary signs of the $n_w$, and $\alpha \neq 0$, then $c_J(\alpha) \chi^{\varepsilon, p, k}_\infty(\alpha) = \chi((\alpha) J^{-1})$, where the right side is `Langlands.Tate.rayCoeff`. -/
theorem periodicCoeff_mul_signInfinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K} (hα : α ≠ 0) :
    periodicCoeff χ J α * signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) α =
      rayCoeff χ J α := by
  have h := infChar_mul_signInfinityWeight hn (Units.mk0 α hα)
  rw [Units.val_mk0] at h
  rw [periodicCoeff, dite_eq_left hα, mul_assoc, h, mul_one]

end Unit

section Classes

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

variable (χ) in
/-- The completed class sum $\Lambda_J(s, \chi) = N(J)^s \Lambda_J(n s / 2)$ of the weight $(p, k)$ of $|n|$ and the sign $\varepsilon$ of $n$. Here $\Lambda_J$ on the right is `Langlands.Tate.signRamifiedPartial`, which already contains the factor $\chi_{\mathrm{id}}(J)^{-1}$ in $c_J$. -/
noncomputable def signRamifiedClassCompleted (n : InfinitePlace K → ℤ) (J : (Ideal (𝓞 K))⁰)
    (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm 𝔣[J] : ℝ) : ℂ) ^ s *
    signRamifiedPartial χ (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) J ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_D(s, \chi^{-1}) = N(D)^s \Lambda^*_D(n s / 2)$ with $D = (\mathfrak{f} J)^\vee$, of the weight $(p, k)$ of $|n|$ and the sign $\varepsilon$ of $n$. -/
noncomputable def signRamifiedClassCompletedConj (n : InfinitePlace K → ℤ) (J : (Ideal (𝓞 K))⁰)
    (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    signRamifiedPartialConj χ (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) J ((finrank ℚ K : ℂ) * s / 2)

/-- **The class sum as a Dirichlet series.** Let $\chi$ have the parameters $(n_w, 0)$ with arbitrary signs of the $n_w$, and let $\mathrm{Re}\, s > 1$. Then $\Lambda_J(s, \chi)$ is the sum over the integral ideals $I$ in the class $[J]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi(I) N(I)^{-s}$, where $\chi(I) = 0$ if $I$ is not prime to $\mathfrak{f}$. There is no condition on the ramification. -/
theorem hasSum_signRamifiedClassCompleted {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (FractionalIdeal.mk0 K J))⁻¹ then
          (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
            rayWeight χ s I else 0)
      (signRamifiedClassCompleted χ n J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_signRamifiedPartial hu J (periodicCoeff_unit_mul_signInfinityWeight hn _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [signRamifiedClassCompleted]
  refine hasSum_rayCoeff_class χ _ (f := fun α => periodicCoeff χ (FractionalIdeal.mk0 K J) α *
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) α)
    (fun α hα => periodicCoeff_mul_signInfinityWeight hn _ hα) ?_
  convert h using 1
  funext I
  ring

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_signRamifiedClassCompleted`, $\Lambda^*_D(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[D]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi^{-1}(I) N(I)^{-s}$. -/
theorem hasSum_signRamifiedClassCompletedConj {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (gaussDual χ J))⁻¹ then
          (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
            rayWeight χ⁻¹ s I else 0)
      (signRamifiedClassCompletedConj χ n J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_signRamifiedPartialConj hu J (periodicCoeff_unit_mul_signInfinityWeight hn _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [signRamifiedClassCompletedConj]
  refine hasSum_rayCoeff_class χ⁻¹ _ (f := fun β => conj (periodicCoeff χ (gaussDual χ J) β) *
      conj (signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) β))
    (fun β hβ => by
      rw [← map_mul, periodicCoeff_mul_signInfinityWeight hn _ hβ, conj_rayCoeff hu]) ?_
  convert h using 1
  funext I
  ring

/-- **The functional equation of one class sum.** Let $\chi$ be ramified at one place, with the parameters $(n_w, 0)$ at each infinite place with arbitrary signs of the $n_w$. Then for all complex $s$, $$\Lambda_J(s, \chi) = W \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, (|d_K| N(\mathfrak{f}))^{1/2 - s} \, \Lambda^*_D(1 - s, \chi^{-1}),$$ with $D = (\mathfrak{f} J)^\vee$ and $W$ = `Langlands.Tate.ramifiedRootNumber` of $|n|$. -/
theorem signRamifiedClassCompleted_eq_conj (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    signRamifiedClassCompleted χ n J s = ramifiedRootNumber χ (absParam K n) *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
      signRamifiedClassCompletedConj χ n J (1 - s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have hc := periodicCoeff_unit_mul_signInfinityWeight hn (gaussDual χ J)
  set A : ℝ := (FractionalIdeal.absNorm 𝔣[J] : ℝ)
  set F : ℝ := (Ideal.absNorm χ.conductor : ℝ)
  set D : ℝ := |(discr K : ℝ)|
  have hA : 0 < A := absNorm_pos K _
  have hF : 0 < F := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 =>
    conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hNf : (FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℝ) = F * A := by
    rw [coe_mk0_conductorNZ_mul, map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul,
      Rat.cast_natCast]
  have hNG : (FractionalIdeal.absNorm (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      (F * A * D)⁻¹ := by
    rw [← hNf]
    exact absNorm_dualUnit (K := K) _
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) = ((D * F : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.ofReal_intCast, Int.cast_abs, Complex.ofReal_natCast]
  have key := cpow_mul_inv_eq hA hF hD (nrComplexPlaces K) s
  unfold signRamifiedClassCompleted signRamifiedClassCompletedConj
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring,
    signRamifiedPartial_sub hS hu (realWeight_absParam_le_one hn) J hc, heckeScale_cpow, ramifiedRootConst,
    heckeRootConst, periodicGaussSum_eq_one hS hu J, hNG, hX, hNf, ramifiedRootNumber]
  linear_combination ((-I) ^ (∑ v, realWeight K (absParam K n) v + ∑ w, complexWeight K (absParam K n) w) *
    periodicGaussSum χ 1 * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s))) *
    signRamifiedPartialConj χ (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) J
      ((finrank ℚ K : ℂ) * (1 - s) / 2)) * key

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The $L$-function as a sum over the ideal classes.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place with arbitrary signs of the $n_w$. For $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi),$$ where $\mathfrak{a}_C$ is the chosen integral ideal of the class $C$. There is no condition on the ramification. -/
theorem heckeGamma_mul_finiteLFunction_ramified_sign {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) {s : ℂ}
    (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
        χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), signRamifiedClassCompleted χ n (classIdeal K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_signRamifiedClassCompleted hn (classIdeal K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (FractionalIdeal.mk0 K (classIdeal K C)))⁻¹) ↔
        ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [← classRepUnit, mk_classRepUnit]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.heckeGamma_mul_finiteLFunction_ramified_sign`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1}).$$ -/
theorem heckeGamma_mul_finiteLFunction_inv_ramified_sign {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) {s : ℂ}
    (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
        χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), signRamifiedClassCompletedConj χ n (classIdeal K C) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_signRamifiedClassCompletedConj hn (classIdeal K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (gaussDual χ (classIdeal K C)))⁻¹) ↔
        ((ramifiedDualClass χ).symm (ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_gaussDual_classIdeal, Equiv.symm_apply_eq]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end LFunction

section Entire

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, 0)$, with $A$ = `Langlands.Tate.archRatio` of $|n|$. -/
noncomputable def signRamifiedCompleted (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s *
    ∑ C : ClassGroup (𝓞 K), signRamifiedClassCompleted χ n (classIdeal K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1})$ of the parameters $(n_w, 0)$. -/
noncomputable def signRamifiedCompletedConj (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s *
    ∑ C : ClassGroup (𝓞 K), signRamifiedClassCompletedConj χ n (classIdeal K C) s

/-- **The completed $L$-functions of a ramified character are entire.** -/
theorem differentiable_signRamifiedCompleted (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) :
    Differentiable ℂ (signRamifiedCompleted χ n) ∧ Differentiable ℂ (signRamifiedCompletedConj χ n) := by
  have hp := realWeight_absParam_le_one hn
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have hb : ∀ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Differentiable ℂ fun s : ℂ =>
        ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := fun b =>
    differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 (absNorm_pos K b).ne'))
  have hm : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2 :=
    (differentiable_id.const_mul _).div_const 2
  refine ⟨((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (Differentiable.fun_sum fun C _ => ?_),
    ((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (Differentiable.fun_sum fun C _ => ?_)⟩
  · exact (hb _).mul ((differentiable_signRamifiedPartial hS hu hp _).comp hm)
  · exact (hb _).mul ((differentiable_signRamifiedPartialConj hS hu hp _
      (periodicCoeff_unit_mul_signInfinityWeight hn _)).comp hm)

/-- The root number of a ramified character has norm $1$. -/
theorem norm_ramifiedRootNumber_absParam (hS : (ramifiedSet χ).Nonempty) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) : ‖ramifiedRootNumber χ (absParam K n)‖ = 1 := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h2 := norm_periodicGaussSum_sq hS hu 1
  have hF : 0 < (Ideal.absNorm χ.conductor : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 =>
    conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hτ : ‖periodicGaussSum χ 1‖ = √(Ideal.absNorm χ.conductor : ℝ) := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [ramifiedRootNumber, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow,
    one_mul, hτ, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_inv_cancel₀ (Real.sqrt_pos.2 hF).ne']

/-- **The entire functional equation for ramified characters with signs.** Let $\chi$ be ramified at one finite place, with the parameters $(n_w, 0)$ at each infinite place with arbitrary signs of the $n_w$, and let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W = (-i)^{\sum_w |n_w|} \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$ = `Langlands.Tate.ramifiedRootNumber` of $|n|$. -/
theorem entireFunctionalEquation_ramified_sign (hS : (ramifiedSet χ).Nonempty)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = 0) :
    EntireFunctionalEquation χ n n' t t' := by
  have ht0 : t = 0 := funext ht
  subst ht0
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := hn
  have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w = 0 := fun w => by
    have e := isArchimedeanParameter_unique (hn' w) (hp0 w).inv
    rwa [neg_zero] at e
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  obtain ⟨hd, hd'⟩ := differentiable_signRamifiedCompleted hS hp0
  refine ⟨signRamifiedCompleted χ n, signRamifiedCompletedConj χ n, ramifiedRootNumber χ (absParam K n), hd, hd',
    fun s hs => ?_, fun s hs => ?_, norm_ramifiedRootNumber_absParam hS hp0, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, ← gammaFactor_absParam hp0,
      gammaFactor_eq_archRatio_mul (absParam_nonneg n), signRamifiedCompleted,
      ← heckeGamma_mul_finiteLFunction_ramified_sign hp0 hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_eq_of_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      ← gammaFactor_absParam hp0, gammaFactor_eq_archRatio_mul (absParam_nonneg n),
      signRamifiedCompletedConj,
      ← heckeGamma_mul_finiteLFunction_inv_ramified_sign hp0 hs]
    field_simp
  · rw [signRamifiedCompletedConj, ← archRatio_mul (absParam K n) s, signRamifiedCompleted]
    simp_rw [signRamifiedClassCompleted_eq_conj hS hp0]
    rw [← Finset.mul_sum]
    ring

end Entire


section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the characters with one shift.** Let $\xi$ be a Hecke character with the archimedean parameters $(n, t)$, where $t_v = t_0$ for all $v$. There is no condition on the signs of the integers $n_w$ at the complex places and no condition on the ramification. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. If $\xi$ is unramified at each finite place, this is `Langlands.Tate.heckeFunctionalEquation_of_unramified_const_shift`. Otherwise $\Lambda$ is entire and the root number is `Langlands.Tate.ramifiedRootNumber` of $|n|$ for the unitary twist $\chi$ of $\xi$. -/
theorem heckeFunctionalEquation_of_const_shift (ξ : HeckeCharacter K)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) (t₀ : ℂ) (ht : ∀ v, t v = t₀) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(ξ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = ξ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = ξ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm ξ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  by_cases hu : ∀ v, ξ.IsUnramifiedAt v
  · exact heckeFunctionalEquation_of_unramified_const_shift ξ hu n n' t t' hn hn' t₀ ht
  push Not at hu
  obtain ⟨v₀, hv₀⟩ := hu
  obtain ⟨χ, hξ⟩ : ∃ χ : HeckeCharacter K, ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ t₀ :=
    ⟨ξ * normPowerChar K (-t₀), fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]⟩
  have hξ' := inv_of_twist hξ
  have hp : ∀ v, χ.IsArchimedeanParameter v (n v) (t v - t₀) := fun v =>
    isArchimedeanParameter_of_twist hξ (hn v)
  have hp' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v + t₀) := fun v => by
    have h := isArchimedeanParameter_of_twist hξ' (hn' v)
    rwa [sub_neg_eq_add] at h
  have ht0 : ∀ v, t v - t₀ = 0 := fun v => by rw [ht v, sub_self]
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := fun w => by
    rw [← ht0 w]
    exact hp w
  have hχu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hp0)
  have hS : (ramifiedSet χ).Nonempty :=
    ⟨v₀, mem_ramifiedSet.2 fun h => hv₀ ((isUnramifiedAt_twist_iff hξ v₀).2 h)⟩
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) :=
    entireFunctionalEquation_ramified_sign hS hp hp' ht0
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

end Assembly

end Langlands.Tate
