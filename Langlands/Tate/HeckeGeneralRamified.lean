/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeGeneralUnramified
import Langlands.Tate.HeckeRamifiedTheta

/-!
# Hecke's functional equation for ramified characters of a general number field

Let $K$ be a number field of degree $n$ with $r_2$ complex places, and let $\chi$ be a Hecke character that is ramified at one finite place at least, with the conductor $\mathfrak{f}$ and the archimedean parameters $(n_w, 0)$ at each infinite place $w$. Suppose that $n_w \ge 0$ for all $w$. Let $(p, k)$ be the weight with $p_v = n_v$ at the real places and $k_w = n_w$ at the complex places. This file proves the functional equation of the completed Hecke $L$-function of $\chi$. It uses the periodic coefficients $c_J$ and the theta series of `Langlands/Tate/HeckeRamifiedTheta.lean`, and the Gamma factors and the assembly of `Langlands/Tate/HeckeGeneralUnramified.lean`.

First, $c_J(u \alpha) \chi^{p, k}_\infty(u) = c_J(\alpha)$ for each unit $u$, and $c_J(\alpha) \chi^{p, k}_\infty(\alpha) = \chi((\alpha) J^{-1})$ for $\alpha \neq 0$. So the averages of the theta series of $c_J$ over the unit cube give a strong functional equation pair, with the root constant $\varepsilon_J = \varepsilon(\mathfrak{f} J) \tau_J(\chi)$. The dual series of this pair is the conjugate series of $\overline{c_D}$ for $D = (\mathfrak{f} J)^\vee$, so its Mellin transform is the conjugate completed partial sum $\Lambda^*_D(s) = \overline{\Lambda_D(\bar{s})}$.

Second, with $\Lambda_J(s, \chi) = N(J)^s \Lambda_J(n s / 2)$ and $\Lambda^*_D(s, \chi^{-1}) = N(D)^s \Lambda^*_D(n s / 2)$, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi), \qquad w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1}),$$ where $\mathfrak{a}_C$ is the chosen integral ideal of the class $C$. Here $\chi(I) = 0$ if $I$ is not prime to $\mathfrak{f}$.

Third, $\tau_J(\chi) = \tau_1(\chi)$ and $|\tau_1(\chi)|^2 = N(\mathfrak{f})$. With the Gamma factors of `Langlands/Tate/HeckeGeneralUnramified.lean`, $\Lambda(s, \chi) = W (|d_K| N(\mathfrak{f}))^{1/2 - s} \Lambda(1 - s, \chi^{-1})$ with $W = (-i)^{\sum_w n_w} \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$ and $|W| = 1$.

## Main definitions

* `Langlands.Tate.ramifiedRootConst`: the root constant $\varepsilon_J$ of the pair.
* `Langlands.Tate.coeffCubeTheta`, `Langlands.Tate.coeffCubeDualTheta`: the averages of the theta series over the unit cube.
* `Langlands.Tate.ramifiedFEPair`: the functional equation pair of $c_J$.
* `Langlands.Tate.ramifiedPartial`, `Langlands.Tate.ramifiedPartialConj`: the completed partial sums $\Lambda_J$ and $\Lambda^*_D$.
* `Langlands.Tate.ramifiedClassCompleted`, `Langlands.Tate.ramifiedClassCompletedConj`: the completed class sums.
* `Langlands.Tate.ramifiedRootNumber`: the root number $W$.
* `Langlands.Tate.ramifiedDualClass`: the permutation $C \mapsto [(\mathfrak{f} C)^\vee]$ of the class group.
* `Langlands.Tate.ramifiedCompleted`, `Langlands.Tate.ramifiedCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$ as finite sums over the ideal classes.

## Main results

* `Langlands.Tate.periodicCoeff_unit_mul_infinityWeight`: the unit condition for $c_J$.
* `Langlands.Tate.coeffDualTheta_eq`, `Langlands.Tate.coeffCubeDualTheta_eq_conj`: the dual series is the conjugate series.
* `Langlands.Tate.isStrongFEPair_ramifiedFEPair`: the pair is strong.
* `Langlands.Tate.ramifiedPartial_sub`: $\Lambda_J(n / 2 - s) = \varepsilon_J \lambda^{-s} \Lambda^*_D(s)$.
* `Langlands.Tate.hasSum_ramifiedPartial`, `Langlands.Tate.hasSum_ramifiedPartialConj`: the completed partial sums as series.
* `Langlands.Tate.periodicCoeff_mul_infinityWeight`, `Langlands.Tate.hasSum_rayCoeff_class`: the link between $c_J$ and $\chi$.
* `Langlands.Tate.hasSum_ramifiedClassCompleted`, `Langlands.Tate.hasSum_ramifiedClassCompletedConj`: the class sums as Dirichlet series.
* `Langlands.Tate.ramifiedClassCompleted_eq_conj`: the functional equation of one class sum.
* `Langlands.Tate.heckeGamma_mul_finiteLFunction_ramified`, `Langlands.Tate.heckeGamma_mul_finiteLFunction_inv_ramified`: the $L$-functions as sums over the ideal classes.
* `Langlands.Tate.norm_ramifiedRootNumber`: $|W| = 1$.
* `Langlands.Tate.entireFunctionalEquation_ramified`: the entire functional equation for a ramified $\chi$ with $n_w \ge 0$.
* `Langlands.Tate.heckeFunctionalEquation_of_parallel`: the conclusion of `Langlands.HeckeFunctionalEquationAt` for each $\xi$ with $t_v = t_0$ for all $v$ and with the $n_w$ at the complex places all of one sign, with no condition on the ramification.
* `Langlands.Tate.heckeFunctionalEquation_of_subsingleton`: the same conclusion for each $\xi$ if $K$ has one infinite place.

## Proof

The pair uses `Langlands.Tate.hasSum_integral_coeffTheta_sub` of `Langlands/Tate/HeckeRamifiedTheta.lean` and the Poisson summation for $c_J$. The constant term of the theta series is $0$, because $c_J(0) = 0$, so the completed partial sums are entire. The ramification is used for $\tau_J(\chi) \neq 0$ and $\tau_J(\chi) = \tau_1(\chi)$. The twist $\xi = \chi \|\cdot\|^{t_0}$ reduces the general case to $t = 0$ with `Langlands.Tate.heckeFunctionalEquation_of_twist`. If the $n_w$ at the complex places are $\le 0$, then `Langlands.Tate.EntireFunctionalEquation.of_inv` applies. If $\xi$ is unramified, `Langlands.Tate.heckeFunctionalEquation_of_unramified_parallel` applies.

## Open parts

The file does not treat a character with different exponents $t_v$ at different infinite places, and it does not treat a ramified character whose $n_w$ at the complex places have mixed signs. The signed theta series of `Langlands/Tate/HeckeMixedSignTheta.lean` is not used here. So `Langlands.HeckeFunctionalEquationAt K` is not proved for a general $K$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.

-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  IsDedekindDomain
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Unit

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The unit condition for the periodic coefficient.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place, with $n_w \ge 0$, and let $(p, k)$ be the weight of $n$. Then $c_J(u \alpha) \chi^{p, k}_\infty(u) = c_J(\alpha)$ for each unit $u$ of $\mathcal{O}_K$, each $\alpha \in K$ and each nonzero fractional ideal $J$. -/
theorem periodicCoeff_unit_mul_infinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (α : K) :
    periodicCoeff χ J ((u : K) * α) * infinityWeight (realWeight K n) (complexWeight K n) (u : K) =
      periodicCoeff χ J α := by
  have h : (infChar χ (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℂ) *
      infinityWeight (realWeight K n) (complexWeight K n) (u : K) = 1 :=
    infChar_mul_infinityWeight hn hn0 _
  rw [periodicCoeff_unit_mul]
  linear_combination (periodicCoeff χ J α) * h

end Unit

section Coeff

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {f : K → ℂ}

/-- If $|f| \le 1$, $f(0) = 0$, $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(f; t)| \le C_{p, k} (\theta_{\mathfrak{b}}(s / 4) - 1)$. The bound holds for each weight, also for the weight $0$. -/
theorem norm_coeffTheta_le (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) :
    ‖coeffTheta K p k b f t‖ ≤ heckeConst p k * (dedekindTheta K b (fun _ => s / 4) - 1) := by
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
    calc ‖f α‖ * ‖heckeTerm p k (α : K) t‖ ≤ 1 * ‖heckeTerm p k (α : K) t‖ :=
          mul_le_mul_of_nonneg_right (hf1 _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact norm_heckeTerm_le_const hs.le hst _

/-- If $|f| \le 1$, then the theta series $\Theta_{\mathfrak{b}}^{p, k}(f; \cdot)$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_coeffTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) : ContinuousAt (coeffTheta K p k b f) t := by
  obtain ⟨m, hm, hmt⟩ : ∃ m > 0, ∀ w, m ≤ t w := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty t, ?_, fun w => Finset.inf'_le _ (Finset.mem_univ w)⟩
    exact (Finset.lt_inf'_iff _).2 fun w _ => ht w
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | m / 2 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have htU : t ∈ U := mem_iInter.2 fun w => (half_lt_self hm).trans_le (hmt w)
  have hc : ContinuousOn (coeffTheta K p k b f) U := by
    refine continuousOn_tsum (fun α => continuousOn_const.mul ((continuousOn_heckeTerm (α : K)).mono
        fun s hs w => (half_pos hm).trans (mem_iInter.1 hs w)))
      ((summable_dedekindTheta b (t := fun _ => m / 2 / 4) fun _ => by positivity).mul_left
        (heckeConst p k)) ?_
    intro α s hs
    rw [norm_mul]
    calc ‖f α‖ * ‖heckeTerm p k (α : K) s‖ ≤ 1 * ‖heckeTerm p k (α : K) s‖ :=
          mul_le_mul_of_nonneg_right (hf1 _) (norm_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          exact norm_heckeTerm_le_const (half_pos hm).le (fun w => (mem_iInter.1 hs w).le) _
  exact hc.continuousAt (hU.mem_nhds htU)

variable (p k) in
/-- **The dual series with a coefficient.** For $t_w \ge 0$, the dual theta series of $\mathfrak{b}$ with the coefficient $g$ is the complex conjugate of the theta series of $(\mathfrak{b} \mathfrak{d})^{-1}$ with the coefficient $\bar{g}$ at the point $(n_w^2 t_w)_w$. -/
theorem coeffDualTheta_eq (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) :
    coeffDualTheta K p k b g t =
      conj (coeffTheta K p k (dualUnit K b) (fun β => conj (g β))
        (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have e : (dualIdeal K b : FractionalIdeal (𝓞 K)⁰ K) =
      ((dualUnit K b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
    (coe_dualUnit_eq K b).symm
  have hs : (fun w => (dualScale K 1 w : ℝ)) = fun w => (mult w : ℝ) := funext (coe_dualScale_one K)
  rw [coeffDualTheta, coeffTheta, Complex.conj_tsum, ← tsum_mul_left]
  let E : {x : K // x ∈ dualIdeal K b} ≃ {x : K // x ∈ ((dualUnit K b :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)} :=
    Equiv.subtypeEquivRight fun x => by rw [e]
  refine Eq.trans ?_ (E.tsum_eq _)
  refine tsum_congr fun β => ?_
  have hd := dualTerm_eq (p := p) (k := k) ht (β : K)
  simp only [hs]
  change _ = conj (conj (g β) * heckeTerm p k (β : K) fun w => (mult w : ℝ) ^ 2 * t w)
  rw [map_mul, Complex.conj_conj, ← hd]
  ring

/-- **The periodicity with a coefficient.** If $f(u \alpha) \chi_\infty(u) = f(\alpha)$ for all units $u$ and $y \ge 0$, then $\Theta_{\mathfrak{b}}^{p, k}(f; t(y, c + m)) = \Theta_{\mathfrak{b}}^{p, k}(f; t(y, c))$ for each integer vector $m$. -/
theorem coeffTheta_unitScale_add_int
    (hf : ∀ (u : (𝓞 K)ˣ) (α : K), f ((u : K) * α) * infinityWeight p k (u : K) = f α)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    coeffTheta K p k b f (unitScale K y (c + fun i => (m i : ℝ))) =
      coeffTheta K p k b f (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h, coeffTheta, coeffTheta]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) (unitOfInt K m)).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [heckeTerm_mul (t := unitScale K y c) (fun w => mul_nonneg hy (Real.exp_pos _).le)
    (coe_ne_zero _), ← mul_assoc, hf]

end Coeff

section Cube

variable (K : Type*) [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)

/-- The cube average $F(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{b}}^{p, k}(f; t(y, c)) \, dc$ of the theta series with the coefficient $f$. -/
noncomputable def coeffCubeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ) (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), coeffTheta K p k b f (unitScale K y c)

/-- The cube average $G(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{b}}^{\vee, p, k}(g; t(y, -c)) \, dc$ of the dual theta series with the coefficient $g$. -/
noncomputable def coeffCubeDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ) (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    coeffDualTheta K p k b g (unitScale K y (-c))

variable {K p k}
variable {f g : K → ℂ}

/-- If $|g| \le 1$, then the dual theta series $\Theta_{\mathfrak{b}}^{\vee, p, k}(g; \cdot)$ is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_coeffDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) : ContinuousAt (coeffDualTheta K p k b g) t := by
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | 0 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have he : (fun s => conj (coeffTheta K p k (dualUnit K b) (fun β => conj (g β))
      (fun w => (mult w : ℝ) ^ 2 * s w))) =ᶠ[𝓝 t] coeffDualTheta K p k b g := by
    filter_upwards [hU.mem_nhds (mem_iInter.2 ht)] with s hs
    exact (coeffDualTheta_eq p k b g fun w => (mem_iInter.1 hs w).le).symm
  refine ContinuousAt.congr ?_ he
  refine Complex.continuous_conj.continuousAt.comp ?_
  refine ContinuousAt.comp (g := coeffTheta K p k (dualUnit K b) (fun β => conj (g β)))
    (continuousAt_coeffTheta (fun β => by rw [Complex.norm_conj]; exact hg1 β) _
      fun w => mul_pos (one_pos.trans_le (one_le_mult_sq w)) (ht w)) ?_
  exact (continuous_pi fun w => continuous_const.mul (continuous_apply w)).continuousAt

/-- If $|g| \le 1$, $g(0) = 0$, $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series with the coefficient $g$ at $t$ has the absolute value at most $C_{p, k} (\theta_{(\mathfrak{b} \mathfrak{d})^{-1}}(s / 4) - 1)$. -/
theorem norm_coeffDualTheta_le (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) :
    ‖coeffDualTheta K p k b g t‖ ≤
      heckeConst p k * (dedekindTheta K (dualUnit K b) (fun _ => s / 4) - 1) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [coeffDualTheta_eq p k b g fun w => hs.le.trans (hst w), Complex.norm_conj]
  exact norm_coeffTheta_le (fun β => by rw [Complex.norm_conj]; exact hg1 β)
    (by rw [hg0, map_zero]) _ hs hst'

/-- If $|f| \le 1$ and $f(0) = 0$, then the cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_coeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ContinuousOn (coeffCubeTheta K p k b f) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i) (fun _ ht => continuousAt_coeffTheta hf1 b ht)
    fun _ hs => ⟨_, fun _ hst => norm_coeffTheta_le hf1 hf0 b hs hst⟩

/-- If $|g| \le 1$ and $g(0) = 0$, then the dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_coeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ContinuousOn (coeffCubeDualTheta K p k b g) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_coeffDualTheta hg1 b ht)
    fun _ hs => ⟨_, fun _ hst => norm_coeffDualTheta_le hg1 hg0 b hs hst⟩

/-- If $|f| \le 1$ and $f(0) = 0$, then $F(y) = O(y^r)$ at infinity for each real $r$. There is no condition on the weight, because the term of $\alpha = 0$ is zero. -/
theorem isBigO_coeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    coeffCubeTheta K p k b f =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := id) _ (fun _ hc i => abs_le_one_of_mem_unitCube hc i) b
    heckeConst_pos.le (fun _ hs _ hst => norm_coeffTheta_le hf1 hf0 b hs hst) r

/-- If $|g| \le 1$ and $g(0) = 0$, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_coeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    coeffCubeDualTheta K p k b g =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := Neg.neg) _
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (dualUnit K b) heckeConst_pos.le (fun _ hs _ hst => norm_coeffDualTheta_le hg1 hg0 b hs hst) r

end Cube

section Pair

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

variable (χ p k) in
/-- The constant $\varepsilon_J = (-i)^{\sum_v p_v + \sum_w k_w} \tau_J(\chi) \big(N(\mathfrak{f} J) \, 2^{-r_2} \sqrt{|d_K|}\big)^{-1}$ of the functional equation of the cube averages of $c_J$. -/
noncomputable def ramifiedRootConst (J : (Ideal (𝓞 K))⁰) : ℂ :=
  heckeRootConst K p k (FractionalIdeal.mk0 K (conductorNZ χ * J)) * periodicGaussSum χ J

/-- If $\chi$ is unitary and ramified at one place, the periodic Gauss sum $\tau_J(\chi)$ is not zero. -/
theorem periodicGaussSum_ne_zero (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) :
    periodicGaussSum χ J ≠ 0 := by
  intro h0
  have h := norm_periodicGaussSum_sq hS hu J
  rw [h0, norm_zero, zero_pow two_ne_zero] at h
  exact conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h.symm))

/-- The constant $\varepsilon_J$ is not zero. -/
theorem ramifiedRootConst_ne_zero (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) :
    ramifiedRootConst χ p k J ≠ 0 :=
  mul_ne_zero heckeRootConst_ne_zero (periodicGaussSum_ne_zero hS hu J)

/-- The theta transformation of `Langlands.Tate.coeffTheta_periodicCoeff_eq` at the point $t(y, c)$, with $1 / t(y, c) = t(y^{-1}, -c)$. -/
theorem coeffTheta_periodicCoeff_unitScale (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {y : ℝ} (hy : 0 < y) (c : Fin (rank K) → ℝ) :
    coeffTheta K p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
        (unitScale K y c) =
      ramifiedRootConst χ p k J * (((√y ^ finrank ℚ K)⁻¹ : ℝ) : ℂ) *
        coeffDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) (unitScale K y⁻¹ (-c)) := by
  have h : (fun w => 1 / unitScale K y c w) = unitScale K y⁻¹ (-c) := by
    funext w
    rw [one_div, unitScale_inv]
  rw [coeffTheta_periodicCoeff_eq hS hu hp J (unitScale_pos hy c), prod_sqrt_unitScale hy.le, h,
    ramifiedRootConst, heckeRootConst]
  ring

/-- **The functional equation of the cube averages of $c_J$.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. For $x > 0$, $F_J(1 / x) = \varepsilon_J \, x^{n / 2} \, G_J(x)$, where $F_J$ is the cube average of $c_J$ on $J$ and $G_J$ is the dual cube average of $\overline{c_D}$ on $\mathfrak{f} J$. -/
theorem coeffCubeTheta_one_div (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {x : ℝ} (hx : 0 < x) :
    coeffCubeTheta K p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
        (1 / x) =
      (ramifiedRootConst χ p k J * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [coeffCubeTheta, coeffCubeDualTheta, smul_eq_mul]
  simp_rw [coeffTheta_periodicCoeff_unitScale hS hu hp J (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul]

/-- The periodic coefficient vanishes at $0$. -/
theorem periodicCoeff_zero (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : periodicCoeff χ J 0 = 0 := by
  rw [periodicCoeff, dite_eq_right (fun h => absurd rfl h)]

/-- The complex conjugate of the periodic coefficient has absolute value at most $1$, for a unitary $\chi$. -/
theorem norm_conj_periodicCoeff_le (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (β : K) : ‖conj (periodicCoeff χ J β)‖ ≤ 1 := by
  rw [Complex.norm_conj]
  exact norm_periodicCoeff_le hu J β

variable (p k) in
/-- **The FE pair of a ramified character.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. The cube averages $F_J$ of $c_J$ and $G_J$ of $\overline{c_D}$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon_J$ and with both constant terms zero. There is no condition on the weight, since $c_J(0) = 0$. -/
noncomputable def ramifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : WeakFEPair ℂ where
  f := coeffCubeTheta K p k (FractionalIdeal.mk0 K J) (periodicCoeff χ (FractionalIdeal.mk0 K J))
  g := coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
    (fun β => conj (periodicCoeff χ (gaussDual χ J) β))
  k := finrank ℚ K / 2
  ε := ramifiedRootConst χ p k J
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_coeffCubeTheta (norm_periodicCoeff_le hu _) (periodicCoeff_zero _)
    _).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_coeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
    (by rw [periodicCoeff_zero, map_zero]) _).locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := ramifiedRootConst_ne_zero hS hu J
  h_feq x hx := coeffCubeTheta_one_div hS hu hp J hx
  hf_top r := by
    simpa only [sub_zero] using isBigO_coeffCubeTheta (norm_periodicCoeff_le hu _)
      (periodicCoeff_zero _) _ r
  hg_top r := by
    simpa only [sub_zero] using isBigO_coeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
      (by rw [periodicCoeff_zero, map_zero]) _ r

/-- The FE pair of a ramified character is a strong FE pair. -/
theorem isStrongFEPair_ramifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : IsStrongFEPair (ramifiedFEPair p k hS hu hp J) :=
  ⟨rfl, rfl⟩

end Pair

section Completed

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable (hS : (ramifiedSet χ).Nonempty) (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
variable (hp : ∀ v, p v ≤ 1)

/-- The completed function of the ramified pair is the Mellin transform of $F_J$. -/
theorem Λ_ramifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (ramifiedFEPair p k hS hu hp J).Λ = mellin (coeffCubeTheta K p k (FractionalIdeal.mk0 K J)
      (periodicCoeff χ (FractionalIdeal.mk0 K J))) :=
  (isStrongFEPair_ramifiedFEPair hS hu hp J).Λ_eq

/-- The completed function of the dual ramified pair is the Mellin transform of $G_J$. -/
theorem symm_Λ_ramifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (ramifiedFEPair p k hS hu hp J).symm.Λ =
      mellin (coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) :=
  (isStrongFEPair_ramifiedFEPair hS hu hp J).symm_Λ_eq

/-- The functional equation $\Lambda_J(n / 2 - s) = \varepsilon_J \, \mathcal{M}G_J(s)$ of the ramified pair for all complex $s$. -/
theorem Λ_ramifiedFEPair_sub (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (ramifiedFEPair p k hS hu hp J).Λ (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J *
        mellin (coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s := by
  have := (ramifiedFEPair p k hS hu hp J).functional_equation s
  rw [symm_Λ_ramifiedFEPair_eq hS hu hp J, smul_eq_mul] at this
  convert this using 2
  · simp [ramifiedFEPair]
  · rfl

/-- **The dual series is the conjugate series.** If $c_D(u \beta) \chi_\infty(u) = c_D(\beta)$ for all units $u$, where $D = (\mathfrak{f} J)^\vee$, and $y \ge 0$, then $G_J(y) = \overline{F_D(\lambda y)}$, where $F_D$ is the cube average of $c_D$ on $D$. -/
theorem coeffCubeDualTheta_eq_conj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β) {y : ℝ} (hy : 0 ≤ y) :
    coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) y =
      conj (coeffCubeTheta K p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))
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
  rw [coeffCubeDualTheta, coeffCubeTheta]
  simp_rw [coeffDualTheta_eq p k _ _ (hnn _), hcc, hd, h]
  rw [integral_conj, integral_unitCube_sub
    (fun c => coeffTheta K p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))
      (unitScale K (heckeScale K * y) c))
    (fun m c => coeffTheta_unitScale_add_int hc _ (mul_nonneg (heckeScale_pos K).le hy) c m)
    (heckeShift K)]

/-- **The Mellin transform of the dual series.** Under the unit condition of `Langlands.Tate.coeffCubeDualTheta_eq_conj`, $\mathcal{M}G_J(s) = \lambda^{-s} \, \overline{\mathcal{M}F_D(\bar{s})}$ for all complex $s$. -/
theorem mellin_coeffCubeDualTheta (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    mellin (coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      (heckeScale K : ℂ) ^ (-s) * conj (mellin (coeffCubeTheta K p k (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J))) (conj s)) := by
  have h : mellin (coeffCubeDualTheta K p k (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      mellin (fun y => conj (coeffCubeTheta K p k (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J)) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [coeffCubeDualTheta_eq_conj J hc (le_of_lt hy)]
  rw [h, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul, map_mul,
    conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]

variable (χ p k) in
/-- The completed partial sum $\Lambda_J(s) = 2^r c_K \, \mathcal{M}F_J(s)$ of the coefficient $c_J$ on the integral ideal $J$. -/
noncomputable def ramifiedPartial (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (coeffCubeTheta K p k (FractionalIdeal.mk0 K J)
      (periodicCoeff χ (FractionalIdeal.mk0 K J))) s

variable (χ p k) in
/-- The conjugate completed partial sum $\Lambda^*_D(s) = \overline{2^r c_K \, \mathcal{M}F_D(\bar{s})}$ of the coefficient $c_D$ on $D = (\mathfrak{f} J)^\vee$. -/
noncomputable def ramifiedPartialConj (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  conj (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (coeffCubeTheta K p k (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))) (conj s))

include hS hu hp in
/-- **The completed partial sum is entire.** -/
theorem differentiable_ramifiedPartial (J : (Ideal (𝓞 K))⁰) :
    Differentiable ℂ (ramifiedPartial χ p k J) := by
  have e : ramifiedPartial χ p k J =
      fun s => ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (ramifiedFEPair p k hS hu hp J).Λ s := by
    funext s
    rw [Λ_ramifiedFEPair_eq hS hu hp J, ramifiedPartial]
  rw [e]
  exact (isStrongFEPair_ramifiedFEPair hS hu hp J).differentiable_Λ.const_mul _

include hS hu hp in
/-- Under the unit condition for $c_D$, $\Lambda^*_D(s) = \lambda^s \, 2^r c_K \, \mathcal{M}G_J(s)$. -/
theorem ramifiedPartialConj_eq (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    ramifiedPartialConj χ p k J s = (heckeScale K : ℂ) ^ s *
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (ramifiedFEPair p k hS hu hp J).symm.Λ s) := by
  have hl : (heckeScale K : ℂ) ^ s * (heckeScale K : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.2 (heckeScale_pos K).ne'), add_neg_cancel, cpow_zero]
  rw [symm_Λ_ramifiedFEPair_eq hS hu hp J, mellin_coeffCubeDualTheta J hc, ramifiedPartialConj,
    map_mul, Complex.conj_ofReal]
  linear_combination (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * conj (mellin (coeffCubeTheta K p k
    (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))) (conj s))) * (-hl)

include hS hu hp in
/-- **The conjugate completed partial sum is entire.** -/
theorem differentiable_ramifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β) :
    Differentiable ℂ (ramifiedPartialConj χ p k J) := by
  have e : ramifiedPartialConj χ p k J = fun s => (heckeScale K : ℂ) ^ s *
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (ramifiedFEPair p k hS hu hp J).symm.Λ s) :=
    funext (ramifiedPartialConj_eq hS hu hp J hc)
  rw [e]
  refine Differentiable.mul (fun s => ?_)
    ((isStrongFEPair_ramifiedFEPair hS hu hp J).symm.differentiable_Λ.const_mul _)
  exact (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (heckeScale_pos K).ne')))

include hS hu hp in
/-- **The functional equation of the completed partial sums.** Let $\chi$ be unitary and ramified at one place, let $p_v \le 1$, and let $c_D$ satisfy the unit condition. Then for all complex $s$, $\Lambda_J(n / 2 - s) = \varepsilon_J \, \lambda^{-s} \, \Lambda^*_D(s)$. -/
theorem ramifiedPartial_sub (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    ramifiedPartial χ p k J (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J * (heckeScale K : ℂ) ^ (-s) * ramifiedPartialConj χ p k J s := by
  rw [ramifiedPartial, ← Λ_ramifiedFEPair_eq hS hu hp J, Λ_ramifiedFEPair_sub,
    mellin_coeffCubeDualTheta J hc, ramifiedPartialConj, map_mul, Complex.conj_ofReal]
  ring

include hu in
/-- **The completed partial sum as a series.** If $c_J$ satisfies the unit condition and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_J(s) = \sum_{\alpha \in (J \setminus 0) / \mathcal{O}_K^\times} w_K \, c_J(\alpha) \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_ramifiedPartial (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (α : K), periodicCoeff χ (FractionalIdeal.mk0 K J) ((u : K) * α) *
      infinityWeight p k (u : K) = periodicCoeff χ (FractionalIdeal.mk0 K J) α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (FractionalIdeal.mk0 K J) => (torsionOrder K : ℂ) *
        (periodicCoeff χ (FractionalIdeal.mk0 K J) (orbitRep (FractionalIdeal.mk0 K J) I) *
        (heckeGamma p k (2 * s / finrank ℚ K) *
          infinityWeight p k (orbitRep (FractionalIdeal.mk0 K J) I : K) *
          ((|(Algebra.norm ℚ (orbitRep (FractionalIdeal.mk0 K J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (ramifiedPartial χ p k J s) := by
  have h := hasSum_integral_coeffTheta_sub (a := FractionalIdeal.mk0 K J)
    (norm_periodicCoeff_le hu _) hc hs
  simp only [periodicCoeff_zero, zero_mul, sub_zero] at h
  rw [ramifiedPartial, mellin]
  simp_rw [smul_eq_mul, coeffCubeTheta]
  exact h

include hu in
/-- **The conjugate completed partial sum as a series.** If $c_D$ satisfies the unit condition and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda^*_D(s) = \sum_{\beta \in (D \setminus 0) / \mathcal{O}_K^\times} w_K \, \overline{c_D(\beta)} \, \Gamma_{p, k}(s') \, \overline{\chi_\infty(\beta)} \, |N(\beta)|^{-s'}.$$ -/
theorem hasSum_ramifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      infinityWeight p k (u : K) = periodicCoeff χ (gaussDual χ J) β)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (gaussDual χ J) => (torsionOrder K : ℂ) *
        (conj (periodicCoeff χ (gaussDual χ J) (orbitRep (gaussDual χ J) I)) *
        (heckeGamma p k (2 * s / finrank ℚ K) *
          conj (infinityWeight p k (orbitRep (gaussDual χ J) I : K)) *
          ((|(Algebra.norm ℚ (orbitRep (gaussDual χ J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (ramifiedPartialConj χ p k J s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have h := hasSum_integral_coeffTheta_sub (a := gaussDual χ J)
    (norm_periodicCoeff_le hu _) hc hs'
  simp only [periodicCoeff_zero, zero_mul, sub_zero] at h
  have e := h.map (starRingEnd ℂ) continuous_conj
  have hv : ramifiedPartialConj χ p k J s = starRingEnd ℂ (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (conj s - 1) *
        ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), coeffTheta K p k (gaussDual χ J)
          (periodicCoeff χ (gaussDual χ J)) (unitScale K y c)) := by
    rw [ramifiedPartialConj, mellin]
    simp_rw [smul_eq_mul, coeffCubeTheta]
  rw [hv]
  have hcs : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hcs, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_heckeGamma]

end Completed

section Ray

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The periodic coefficient and the coefficient of the $L$-series.** If $\chi$ has the parameters $(n_w, 0)$ with $n_w \ge 0$ and $\alpha \neq 0$, then $c_J(\alpha) \chi_{p, k}(\alpha) = \chi((\alpha) J^{-1})$, where $\chi_{p, k}$ = `Langlands.Tate.infinityWeight` of the weight of $n$ and the right side is `Langlands.Tate.rayCoeff`. -/
theorem periodicCoeff_mul_infinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K} (hα : α ≠ 0) :
    periodicCoeff χ J α * infinityWeight (realWeight K n) (complexWeight K n) α =
      rayCoeff χ J α := by
  have h := infChar_mul_infinityWeight hn hn0 (Units.mk0 α hα)
  rw [Units.val_mk0] at h
  rw [periodicCoeff, dite_eq_left hα, mul_assoc, h, mul_one]

/-- For a unitary $\chi$, the complex conjugate of the coefficient of $\chi$ is the coefficient of $\chi^{-1}$. -/
theorem conj_rayCoeff (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : conj (rayCoeff χ J α) = rayCoeff χ⁻¹ J α := by
  unfold rayCoeff
  simp only [ramifiedSet_inv]
  split_ifs with h
  · simp only [Units.val_mul, map_mul, idealChar_inv, Units.val_inv_eq_inv_val, map_inv₀,
      inv_inv]
    rw [← Complex.inv_eq_conj (norm_idealChar_of_unitary hu _),
      ← Complex.inv_eq_conj (norm_idealChar_of_unitary hu _), inv_inv]
  · rw [map_zero]

/-- **The coefficient at a generator.** If $(\alpha) = \mathfrak{b} I$ with $I$ integral, then $\chi((\alpha) \mathfrak{b}^{-1}) N(I)^{-s}$ is the weight `Langlands.Tate.rayWeight` of $I$, which includes the condition that $I$ is prime to the ramified places. -/
theorem rayCoeff_mul_cpow_of_spanSingleton (ψ : HeckeCharacter K)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (I : (Ideal (𝓞 K))⁰) {α : K} (hα : α ≠ 0)
    (h : FractionalIdeal.spanSingleton (𝓞 K)⁰ α =
      (b : FractionalIdeal (𝓞 K)⁰ K) * ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) :
    rayCoeff ψ b α * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) = rayWeight ψ s I := by
  have hI0 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero I)
  have hprin : toPrincipalIdeal (𝓞 K) K (Units.mk0 α hα) = b * FractionalIdeal.mk0 K I := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact h
  have hiff : (∀ v ∈ ramifiedSet ψ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (b : FractionalIdeal (𝓞 K)⁰ K)) ↔
      ∀ v ∈ ramifiedSet ψ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    refine forall₂_congr fun v _ => ?_
    rw [h, FractionalIdeal.count_mul K v b.ne_zero hI0, ← count_eq_zero_iff_not_dvd]
    omega
  rw [rayWeight_apply, rayCoeff]
  by_cases hc : ∀ v ∈ ramifiedSet ψ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K))
  · rw [dite_eq_left ⟨hα, hiff.2 hc⟩, ite_eq_left hc, hprin, map_mul,
      mul_comm (idealChar ψ b), mul_inv_cancel_right, one_mul]
  · rw [dite_eq_right (fun h' => hc (hiff.1 h'.2)), ite_eq_right hc]
    simp

/-- **From the orbits to the ideals, with ramification.** Let $f(\alpha) = \chi((\alpha) \mathfrak{b}^{-1})$ for $\alpha \neq 0$. If the series over $\alpha \in (\mathfrak{b} \setminus 0) / \mathcal{O}_K^\times$ of $w_K \, c \, f(\alpha) \, |N(\alpha)|^{-s}$ has the sum $L$, then the series over the integral ideals $I$ in the class $[\mathfrak{b}]^{-1}$ of $w_K \, c \, \psi(I) N(I)^{-s}$, with $\psi(I) = 0$ if $I$ is not prime to the ramified places, has the sum $N(\mathfrak{b})^s L$. -/
theorem hasSum_rayCoeff_class (ψ : HeckeCharacter K) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {f : K → ℂ} (hf : ∀ α : K, α ≠ 0 → f α = rayCoeff ψ b α) {c s L : ℂ}
    (h : HasSum (fun I : Orbits b => (torsionOrder K : ℂ) * (c * f (orbitRep b I : K) *
        ((|(Algebra.norm ℚ (orbitRep b I : K) : ℝ)| : ℝ) : ℂ) ^ (-s))) L) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K b)⁻¹ then
        (torsionOrder K : ℂ) * c * rayWeight ψ s I else 0)
      (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s * L) := by
  set g : (Ideal (𝓞 K))⁰ → ℂ := fun I => (torsionOrder K : ℂ) * c * rayWeight ψ s I with hg
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    absNorm_pos K b
  have hN0 : ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hN.ne'))
  have h1 : HasSum (g ∘ ((↑) : Orbits b → (Ideal (𝓞 K))⁰))
      (((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s * L) := by
    refine (h.mul_left _).congr_fun fun I => ?_
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (orbitRep b I : K) =
        (b : FractionalIdeal (𝓞 K)⁰ K) *
          (((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [spanSingleton_eq_mul_idealOf, idealOf_orbitRep]
    have hr := rayCoeff_mul_cpow_of_spanSingleton ψ b I (orbitRep b I).2 hspan s
    simp only [Function.comp_apply, hg, ← hr, hf _ (orbitRep b I).2, abs_norm_orbitRep,
      Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg hN.le (Nat.cast_nonneg _), Complex.ofReal_natCast,
      cpow_neg _ s, cpow_neg _ s]
    field_simp
  have h2 := (hasSum_subtype_iff_indicator (s := Orbits b)).1 h1
  convert h2 using 1
  funext I
  by_cases hI : I ∈ Orbits b
  · rw [Set.indicator_of_mem hI, ite_eq_left ((mem_orbits_iff b I).1 hI)]
  · rw [Set.indicator_of_notMem hI, ite_eq_right (fun h => hI ((mem_orbits_iff b I).2 h))]

end Ray

section Classes

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

variable (χ) in
/-- The completed class sum $\Lambda_J(s, \chi) = N(J)^s \Lambda_J(n s / 2)$ of the weight $(p, k)$ of $n$. Here $\Lambda_J$ on the right is `Langlands.Tate.ramifiedPartial`, which already contains the factor $\chi_{\mathrm{id}}(J)^{-1}$ in $c_J$. -/
noncomputable def ramifiedClassCompleted (n : InfinitePlace K → ℤ) (J : (Ideal (𝓞 K))⁰)
    (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm 𝔣[J] : ℝ) : ℂ) ^ s *
    ramifiedPartial χ (realWeight K n) (complexWeight K n) J ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_D(s, \chi^{-1}) = N(D)^s \Lambda^*_D(n s / 2)$ with $D = (\mathfrak{f} J)^\vee$, of the weight $(p, k)$ of $n$. -/
noncomputable def ramifiedClassCompletedConj (n : InfinitePlace K → ℤ) (J : (Ideal (𝓞 K))⁰)
    (s : ℂ) : ℂ :=
  ((FractionalIdeal.absNorm (gaussDual χ J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    ramifiedPartialConj χ (realWeight K n) (complexWeight K n) J ((finrank ℚ K : ℂ) * s / 2)

/-- **The class sum as a Dirichlet series.** Let $\chi$ have the parameters $(n_w, 0)$ with $n_w \ge 0$, and let $\mathrm{Re}\, s > 1$. Then $\Lambda_J(s, \chi)$ is the sum over the integral ideals $I$ in the class $[J]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi(I) N(I)^{-s}$, where $\chi(I) = 0$ if $I$ is not prime to $\mathfrak{f}$. There is no condition on the ramification. -/
theorem hasSum_ramifiedClassCompleted {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (FractionalIdeal.mk0 K J))⁻¹ then
          (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
            rayWeight χ s I else 0)
      (ramifiedClassCompleted χ n J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_ramifiedPartial hu J (periodicCoeff_unit_mul_infinityWeight hn hn0 _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [ramifiedClassCompleted]
  refine hasSum_rayCoeff_class χ _ (f := fun α => periodicCoeff χ (FractionalIdeal.mk0 K J) α *
      infinityWeight (realWeight K n) (complexWeight K n) α)
    (fun α hα => periodicCoeff_mul_infinityWeight hn hn0 _ hα) ?_
  convert h using 1
  funext I
  ring

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_ramifiedClassCompleted`, $\Lambda^*_D(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[D]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi^{-1}(I) N(I)^{-s}$. -/
theorem hasSum_ramifiedClassCompletedConj {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
        if ClassGroup.mk0 I = (ClassGroup.mk K (gaussDual χ J))⁻¹ then
          (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
            rayWeight χ⁻¹ s I else 0)
      (ramifiedClassCompletedConj χ n J s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_ramifiedPartialConj hu J (periodicCoeff_unit_mul_infinityWeight hn hn0 _)
    (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [ramifiedClassCompletedConj]
  refine hasSum_rayCoeff_class χ⁻¹ _ (f := fun β => conj (periodicCoeff χ (gaussDual χ J) β) *
      conj (infinityWeight (realWeight K n) (complexWeight K n) β))
    (fun β hβ => by
      rw [← map_mul, periodicCoeff_mul_infinityWeight hn hn0 _ hβ, conj_rayCoeff hu]) ?_
  convert h using 1
  funext I
  ring

omit [NumberField K] in
/-- **The constants of the class functional equation.** For $A, F, D > 0$, $$A^s \big(F A \, 2^{-r} \sqrt{D}\big)^{-1} = \frac{2^r}{\sqrt{F}} (D F)^{1/2 - s} \big((F A D)^{-1}\big)^{1 - s}.$$ -/
theorem cpow_mul_inv_eq {A F D : ℝ} (hA : 0 < A) (hF : 0 < F) (hD : 0 < D) (r : ℕ) (s : ℂ) :
    (A : ℂ) ^ s * ((((F * A) * (2⁻¹) ^ r * √D)⁻¹ : ℝ) : ℂ) =
      ((√F : ℝ) : ℂ)⁻¹ * (2 : ℂ) ^ r * ((D * F : ℝ) : ℂ) ^ (1 / 2 - s) *
        (((F * A * D)⁻¹ : ℝ) : ℂ) ^ (1 - s) := by
  have hA0 : (A : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  have hD0 : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD.ne'
  have hF0 : (F : ℂ) ≠ 0 := ofReal_ne_zero.2 hF.ne'
  have hsq : ∀ {x : ℝ}, 0 < x → ((√x : ℝ) : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := fun {x} hx => by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    push_cast
    rfl
  have hsq2 : (D : ℂ) ^ (1 / 2 : ℂ) * (D : ℂ) ^ (1 / 2 : ℂ) = D := by
    rw [← cpow_add _ _ hD0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, cpow_one]
  have hB : (((F * A * D)⁻¹ : ℝ) : ℂ) ^ (1 - s) =
      ((F : ℂ) / F ^ s * ((A : ℂ) / A ^ s) * ((D : ℂ) / D ^ s))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_ne_zero.symm), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) hD.le, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hF.le hA.le, cpow_sub _ _ hA0, cpow_sub _ _ hD0,
      cpow_sub _ _ hF0, cpow_one, cpow_one, cpow_one]
  have hC : ((D * F : ℝ) : ℂ) ^ (1 / 2 - s) =
      (D : ℂ) ^ (1 / 2 : ℂ) / D ^ s * ((F : ℂ) ^ (1 / 2 : ℂ) / F ^ s) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hD.le hF.le, cpow_sub _ _ hD0,
      cpow_sub _ _ hF0]
  have hX : (D : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hY : (F : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hF0)
  have hAs : (A : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hA0)
  have hDs : (D : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hFs : (F : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hF0)
  rw [hB, hC, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul,
    hsq hD, hsq hF, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat, inv_pow]
  field_simp
  rw [sq, hsq2]

variable (χ) in
/-- The root number $W = (-i)^{\sum_v p_v + \sum_w k_w} \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$ of the parameters $(n_w, 0)$, where $(p, k)$ is the weight of $n$. -/
noncomputable def ramifiedRootNumber (n : InfinitePlace K → ℤ) : ℂ :=
  (-I) ^ (∑ v, realWeight K n v + ∑ w, complexWeight K n w) * periodicGaussSum χ 1 *
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ)⁻¹

/-- **The functional equation of one class sum.** Let $\chi$ be ramified at one place, with the parameters $(n_w, 0)$ at each infinite place and $n_w \ge 0$. Then for all complex $s$, $$\Lambda_J(s, \chi) = W \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, (|d_K| N(\mathfrak{f}))^{1/2 - s} \, \Lambda^*_D(1 - s, \chi^{-1}),$$ with $D = (\mathfrak{f} J)^\vee$ and $W$ = `Langlands.Tate.ramifiedRootNumber`. -/
theorem ramifiedClassCompleted_eq_conj (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (hn0 : ∀ w, 0 ≤ n w) (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    ramifiedClassCompleted χ n J s = ramifiedRootNumber χ n *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
      ramifiedClassCompletedConj χ n J (1 - s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have hc := periodicCoeff_unit_mul_infinityWeight hn hn0 (gaussDual χ J)
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
  unfold ramifiedClassCompleted ramifiedClassCompletedConj
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring,
    ramifiedPartial_sub hS hu (realWeight_le_one hn) J hc, heckeScale_cpow, ramifiedRootConst,
    heckeRootConst, periodicGaussSum_eq_one hS hu J, hNG, hX, hNf, ramifiedRootNumber]
  linear_combination ((-I) ^ (∑ v, realWeight K n v + ∑ w, complexWeight K n w) *
    periodicGaussSum χ 1 * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s))) *
    ramifiedPartialConj χ (realWeight K n) (complexWeight K n) J
      ((finrank ℚ K : ℂ) * (1 - s) / 2)) * key

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The permutation $C \mapsto [(\mathfrak{f} \, C)^\vee] = (C [\mathfrak{f}] [\mathfrak{d}])^{-1}$ of the class group. -/
noncomputable def ramifiedDualClass : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.mulLeft (ClassGroup.mk0 (conductorNZ χ))).trans (dualClass K)

/-- The dual $D = (\mathfrak{f} \mathfrak{a}_C)^\vee$ of the chosen ideal $\mathfrak{a}_C$ is in the class `Langlands.Tate.ramifiedDualClass χ C`. -/
theorem mk_gaussDual_classIdeal (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (gaussDual χ (classIdeal K C)) = ramifiedDualClass χ C := by
  change ClassGroup.mk K (dualUnit K (FractionalIdeal.mk0 K (conductorNZ χ * classIdeal K C))) = _
  rw [dualUnit_eq, map_inv, map_mul, ClassGroup.mk_mk0, map_mul, mk0_classIdeal]
  rfl

/-- **The $L$-function as a sum over the ideal classes.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place with $n_w \ge 0$. For $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi),$$ where $\mathfrak{a}_C$ is the chosen integral ideal of the class $C$. There is no condition on the ramification. -/
theorem heckeGamma_mul_finiteLFunction_ramified {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) {s : ℂ}
    (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
        χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), ramifiedClassCompleted χ n (classIdeal K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_ramifiedClassCompleted hn hn0 (classIdeal K C) hs)
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

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.heckeGamma_mul_finiteLFunction_ramified`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1}).$$ -/
theorem heckeGamma_mul_finiteLFunction_inv_ramified {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) {s : ℂ}
    (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
        χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), ramifiedClassCompletedConj χ n (classIdeal K C) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_ramifiedClassCompletedConj hn hn0 (classIdeal K C) hs)
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
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, 0)$, with $A$ = `Langlands.Tate.archRatio`. -/
noncomputable def ramifiedCompleted (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K n s *
    ∑ C : ClassGroup (𝓞 K), ramifiedClassCompleted χ n (classIdeal K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \sum_C \Lambda^*_{(\mathfrak{f} \mathfrak{a}_C)^\vee}(s, \chi^{-1})$ of the parameters $(n_w, 0)$. -/
noncomputable def ramifiedCompletedConj (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K n s *
    ∑ C : ClassGroup (𝓞 K), ramifiedClassCompletedConj χ n (classIdeal K C) s

/-- **The completed $L$-functions of a ramified character are entire.** -/
theorem differentiable_ramifiedCompleted (hS : (ramifiedSet χ).Nonempty)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (hn0 : ∀ w, 0 ≤ n w) :
    Differentiable ℂ (ramifiedCompleted χ n) ∧ Differentiable ℂ (ramifiedCompletedConj χ n) := by
  have hp := realWeight_le_one hn
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have hb : ∀ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Differentiable ℂ fun s : ℂ =>
        ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := fun b =>
    differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 (absNorm_pos K b).ne'))
  have hm : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2 :=
    (differentiable_id.const_mul _).div_const 2
  refine ⟨((differentiable_const _).mul (differentiable_archRatio n)).mul
      (Differentiable.fun_sum fun C _ => ?_),
    ((differentiable_const _).mul (differentiable_archRatio n)).mul
      (Differentiable.fun_sum fun C _ => ?_)⟩
  · exact (hb _).mul ((differentiable_ramifiedPartial hS hu hp _).comp hm)
  · exact (hb _).mul ((differentiable_ramifiedPartialConj hS hu hp _
      (periodicCoeff_unit_mul_infinityWeight hn hn0 _)).comp hm)

/-- The root number of a ramified character has norm $1$. -/
theorem norm_ramifiedRootNumber (hS : (ramifiedSet χ).Nonempty) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) : ‖ramifiedRootNumber χ n‖ = 1 := by
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

/-- **The entire functional equation for ramified characters of nonnegative weight.** Let $\chi$ be ramified at one finite place, with the parameters $(n_w, 0)$ at each infinite place and $n_w \ge 0$, and let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W = (-i)^{\sum_w n_w} \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$ = `Langlands.Tate.ramifiedRootNumber`. -/
theorem entireFunctionalEquation_ramified (hS : (ramifiedSet χ).Nonempty)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = 0) (hn0 : ∀ w, 0 ≤ n w) :
    EntireFunctionalEquation χ n n' t t' := by
  have ht0 : t = 0 := funext ht
  subst ht0
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := hn
  have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w = 0 := fun w => by
    have e := isArchimedeanParameter_unique (hn' w) (hp0 w).inv
    rwa [neg_zero] at e
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  obtain ⟨hd, hd'⟩ := differentiable_ramifiedCompleted hS hp0 hn0
  refine ⟨ramifiedCompleted χ n, ramifiedCompletedConj χ n, ramifiedRootNumber χ n, hd, hd',
    fun s hs => ?_, fun s hs => ?_, norm_ramifiedRootNumber hS hp0, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_eq_archRatio_mul hn0, ramifiedCompleted,
      ← heckeGamma_mul_finiteLFunction_ramified hp0 hn0 hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_eq_of_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      gammaFactor_eq_archRatio_mul hn0, ramifiedCompletedConj,
      ← heckeGamma_mul_finiteLFunction_inv_ramified hp0 hn0 hs]
    field_simp
  · rw [ramifiedCompletedConj, ← archRatio_mul n s, ramifiedCompleted]
    simp_rw [ramifiedClassCompleted_eq_conj hS hp0 hn0]
    rw [← Finset.mul_sum]
    ring

end Entire

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the characters with parallel weight.** Let $\xi$ be a Hecke character with the archimedean parameters $(n, t)$, where $t_v = t_0$ for all $v$ and the integers $n_w$ at the complex places are all $\ge 0$ or all $\le 0$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. There is no condition on the ramification. If $\xi$ is unramified at each finite place, this is `Langlands.Tate.heckeFunctionalEquation_of_unramified_parallel`. Otherwise $\Lambda$ is entire and the root number is `Langlands.Tate.ramifiedRootNumber` of the unitary twist $\chi$ of $\xi$ or of $\xi^{-1}$. -/
theorem heckeFunctionalEquation_of_parallel (ξ : HeckeCharacter K)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) (t₀ : ℂ) (ht : ∀ v, t v = t₀)
    (hsign : (∀ w, ¬ IsReal w → 0 ≤ n w) ∨ (∀ w, ¬ IsReal w → n w ≤ 0)) :
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
  · exact heckeFunctionalEquation_of_unramified_parallel ξ hu n n' t t' hn hn' t₀ ht hsign
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
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) := by
    rcases hsign with hs | hs
    · have hn0 : ∀ w, 0 ≤ n w := fun w => by
        by_cases hw : IsReal w
        · rcases (hn w).isReal hw with h | h <;> omega
        · exact hs w hw
      exact entireFunctionalEquation_ramified hS hp hp' ht0 hn0
    · have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w + t₀ = 0 := fun w => by
        have e := isArchimedeanParameter_unique (hp' w) (hp w).inv
        rwa [ht0, neg_zero] at e
      have hn0 : ∀ w, 0 ≤ n' w := fun w => by
        rw [(hinv w).1]
        by_cases hw : IsReal w
        · rw [ite_eq_left hw]
          rcases (hn w).isReal hw with h | h <;> omega
        · rw [ite_eq_right hw]
          have := hs w hw
          omega
      have hpi : ∀ v, χ⁻¹⁻¹.IsArchimedeanParameter v (n v) (t v - t₀) := by
        rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
        exact hp
      exact EntireFunctionalEquation.of_inv (entireFunctionalEquation_ramified
        (by rwa [ramifiedSet_inv]) hp' hpi (fun w => (hinv w).2) hn0)
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

/-- **Hecke's functional equation for a field with one infinite place.** If $K$ has exactly one infinite place, as for $\mathbb{Q}$ and the imaginary quadratic fields, then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for each Hecke character $\xi$ of $K$. -/
theorem heckeFunctionalEquation_of_subsingleton [Subsingleton (InfinitePlace K)]
    (ξ : HeckeCharacter K) (n n' : InfinitePlace K → ℤ)
    (t t' : InfinitePlace K → ℂ) (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
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
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  refine heckeFunctionalEquation_of_parallel ξ n n' t t' hn hn' (t w₀)
    (fun v => by rw [Subsingleton.elim v w₀]) ?_
  rcases le_total 0 (n w₀) with h | h
  · exact Or.inl fun w _ => by rwa [Subsingleton.elim w w₀]
  · exact Or.inr fun w _ => by rwa [Subsingleton.elim w w₀]

end Assembly

end Langlands.Tate
