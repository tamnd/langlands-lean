/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeUnfold

/-!
# The FE pair of the weighted Hecke theta functions

Let $K$ be a number field of degree $n$ with $r_2$ complex places, unit rank $r$ and discriminant $d_K$, let $\mathfrak{d}$ be the different, and let $n_w$ be $1$ at a real place and $2$ at a complex place. Fix a weight $(p, k)$ with $p_v \le 1$ and a nonzero fractional ideal $\mathfrak{a}$. Let $\Theta_{\mathfrak{a}}^{p, k}$ be the normalized theta series and $\widehat{\Theta}_{\mathfrak{a}}^{p, k}$ the dual theta series of `Langlands/Tate/HeckeMellinUnits.lean`, and let $t(y, c)$ be the unit coordinates of `Langlands.Tate.unitScale`. This file does three steps of Hecke's proof of the functional equation.

First, $\widehat{\Theta}_{\mathfrak{a}}^{p, k}(t) = \overline{\Theta_{(\mathfrak{a} \mathfrak{d})^{-1}}^{p, k}((n_w^2 t_w)_w)}$. The complex conjugate of the term of weight $(p, k)$ is the term of the conjugate weight, and the factor $n_w^2$ comes from the factor $n_w$ in the trace form at a complex place.

Second, the cube averages $F(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) \, dc$ and $G(y) = \int_{[0, 1)^r} \widehat{\Theta}_{\mathfrak{a}}^{p, k}(t(y, -c)) \, dc$ satisfy $F(1 / x) = \varepsilon \, x^{n / 2} G(x)$ with $\varepsilon = (-i)^{\sum_v p_v + \sum_w k_w} (N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$. For a nonzero weight, the terms at $\alpha = 0$ are zero, so $F$ and $G$ decrease faster than each power of $y$ at infinity, and $(F, G)$ is a Mathlib strong FE pair of weight $n / 2$.

Third, the Mellin transform $\Lambda$ of $F$ is entire, satisfies $\Lambda(n / 2 - s) = \varepsilon \, \mathcal{M}G(s)$, and for $\mathrm{Re}\, s > n / 2$ it is a constant times the partial Hecke sum over the unit orbits of $\mathfrak{a} \setminus 0$.

## Main definitions

* `Langlands.Tate.heckeCubeTheta`: the cube average $F$ of $\Theta_{\mathfrak{a}}^{p, k}$.
* `Langlands.Tate.heckeCubeDualTheta`: the cube average $G$ of $\widehat{\Theta}_{\mathfrak{a}}^{p, k}$.
* `Langlands.Tate.heckeRootConst`: the constant $\varepsilon$.
* `Langlands.Tate.heckeFEPair`: the FE pair $(F, G)$.

## Main results

* `Langlands.Tate.heckeDualTheta_eq`: the dual theta series as the conjugate of the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$.
* `Langlands.Tate.heckeCubeTheta_one_div`: $F(1 / x) = \varepsilon \, x^{n / 2} G(x)$.
* `Langlands.Tate.isStrongFEPair_heckeFEPair`: the pair is a strong FE pair.
* `Langlands.Tate.differentiable_Λ_heckeFEPair`, `Langlands.Tate.differentiable_mellin_heckeCubeDualTheta`: the Mellin transforms of $F$ and $G$ are entire.
* `Langlands.Tate.Λ_heckeFEPair_sub`: $\Lambda(n / 2 - s) = \varepsilon \, \mathcal{M}G(s)$.
* `Langlands.Tate.hasSum_Λ_heckeFEPair`: $\Lambda(s)$ as the partial Hecke sum of $\mathfrak{a}$ for $\mathrm{Re}\, s > n / 2$.

## Proof

The identity of the dual series is a computation at each place, with a reindexing of the sum from `Langlands.Tate.dualIdeal` to `Langlands.Tate.dualUnit`. The equation of $F$ and $G$ is `Langlands.Tate.heckeTheta_unitScale` integrated over the cube. The bounds use $|h_t(\alpha)| \le C_{p, k}$ times the theta term of weight $0$ at $t / 4$, the lower bound $t(y, c)_w \ge y \, b_K$ for $|c_i| \le 1$, and the decay of `Langlands.Tate.latticeTheta`. The continuity of $F$ and $G$ is dominated convergence. The rest is the Mathlib theory of strong FE pairs and `Langlands.Tate.hasSum_integral_heckeTheta`.

## Open parts

The file does not yet identify $\mathcal{M}G$ with the partial Hecke sum of $(\mathfrak{a} \mathfrak{d})^{-1}$ for the conjugate weight. The missing steps are these.
* The periodicity $\Theta_{\mathfrak{b}}^{p, k}((t_w |u|_w^2)_w) = \Theta_{\mathfrak{b}}^{p, k}(t)$ for the units $u$ with $\chi_\infty(u) = 1$.
* The invariance of the cube integral of a periodic function under $c \mapsto c_0 - c$.
* The relation $(n_w^2 \, t(y, -c)_w)_w = t(\lambda y, c_0 - c)$ with $\lambda = 2^{4 r_2 / n}$ and a fixed $c_0 \in \mathbb{R}^r$, so that $G(y) = \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$.
With these steps, $\mathcal{M}G(s) = \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$, and `Langlands.Tate.hasSum_Λ_heckeFEPair` for $(\mathfrak{a} \mathfrak{d})^{-1}$ gives the symmetry $s \leftrightarrow n / 2 - s$ between the partial Hecke sums.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex Asymptotics ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Dual

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

omit [NumberField K] in
/-- For $x \ge 0$ the power $x^{q/2}$ is real, so its complex conjugate is itself. -/
theorem conj_ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) (q : ℕ) :
    conj ((x : ℂ) ^ ((q : ℂ) / 2)) = (x : ℂ) ^ ((q : ℂ) / 2) := by
  rw [show ((q : ℂ) / 2) = (((q : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx,
    Complex.conj_ofReal]

/-- The term of the dual theta series at $\beta$ is the complex conjugate of the normalized term of $\beta$ at the point $(n_w^2 t_w)_w$. Here $n_w$ is $1$ at a real place and $2$ at a complex place, and the conjugate embedding at a complex place gives the conjugate weight. -/
theorem dualTerm_eq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) (β : K) :
    (∏ w, (t w : ℂ) ^ ((weightExp p k w : ℂ) / 2)) *
        mixedGaussWeight p k t (globalConjEmbedding K (fun w => (mult w : ℝ)) β) =
      conj (heckeTerm p k β (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have hr : ∀ v : {w : InfinitePlace K // IsReal w}, weightExp p k v.1 = p v := fun v => by
    simp [weightExp, v.2]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, weightExp p k w.1 = k w := fun w => by
    simp [weightExp, not_isReal_iff_isComplex.2 w.2]
  rw [heckeTerm, mixedGaussWeight_globalConjEmbedding, mixedGaussWeight_globalEmbedding,
    prod_eq_prod_mul_prod, prod_eq_prod_mul_prod (fun w => (((mult w : ℝ) ^ 2 * t w : ℝ) : ℂ) ^
      ((weightExp p k w : ℂ) / 2))]
  simp only [hr, hc, map_mul, map_prod]
  have HR : ∀ v : {w : InfinitePlace K // IsReal w},
      (t v.1 : ℂ) ^ ((p v : ℂ) / 2) *
          realGaussWeight (p v) (t v.1) ((mult v.1 : ℝ) * embedding_of_isReal v.2 β) =
        conj ((((mult v.1 : ℝ) ^ 2 * t v.1 : ℝ) : ℂ) ^ ((p v : ℂ) / 2)) *
          conj (realGaussWeight (p v) ((mult v.1 : ℝ) ^ 2 * t v.1)
            ((1 : ℝ) * embedding_of_isReal v.2 β)) := by
    intro v
    rw [mult_isReal v, Nat.cast_one, one_pow, one_mul, one_mul, conj_ofReal_cpow_half (ht _)]
    simp only [realGaussWeight, map_mul, map_pow, Complex.conj_ofReal]
  have HC : ∀ w : {w : InfinitePlace K // IsComplex w},
      (t w.1 : ℂ) ^ ((k w : ℂ) / 2) *
          gaussWeight (k w) (t w.1) (((mult w.1 : ℝ) : ℂ) * conj (w.1.embedding β)) =
        conj ((((mult w.1 : ℝ) ^ 2 * t w.1 : ℝ) : ℂ) ^ ((k w : ℂ) / 2)) *
          conj (gaussWeight (k w) ((mult w.1 : ℝ) ^ 2 * t w.1)
            (((1 : ℝ) : ℂ) * w.1.embedding β)) := by
    intro w
    rw [mult_isComplex w, conj_ofReal_cpow_half (by have := ht w.1; positivity),
      Complex.ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (ht _),
      ofReal_sq_cpow_half (by norm_num)]
    simp only [gaussWeight, map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal,
      Complex.ofReal_one, one_mul, norm_mul]
    norm_num
    ring_nf
  calc _ = (∏ v : {w : InfinitePlace K // IsReal w}, (t v.1 : ℂ) ^ ((p v : ℂ) / 2) *
          realGaussWeight (p v) (t v.1) ((mult v.1 : ℝ) * embedding_of_isReal v.2 β)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (t w.1 : ℂ) ^ ((k w : ℂ) / 2) *
          gaussWeight (k w) (t w.1) (((mult w.1 : ℝ) : ℂ) * conj (w.1.embedding β)) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = _ := by
        simp only [HR, HC, Finset.prod_mul_distrib]
        ring

variable (p k) in
/-- The dual theta series of $\mathfrak{a}$ is the complex conjugate of the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ at the point $(n_w^2 t_w)_w$. So it is the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ for the conjugate weight, and the factor $n_w^2 = 4$ at a complex place is the only change of the variable. -/
theorem heckeDualTheta_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 ≤ t w) :
    heckeDualTheta K p k a t =
      conj (heckeTheta K p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * t w)) := by
  have e : (dualIdeal K a : FractionalIdeal (𝓞 K)⁰ K) =
      ((dualUnit K a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
    (coe_dualUnit_eq K a).symm
  have hs : (fun w => (dualScale K 1 w : ℝ)) = fun w => (mult w : ℝ) := funext (coe_dualScale_one K)
  rw [heckeDualTheta, idealDualTheta, heckeTheta_eq_tsum, Complex.conj_tsum, ← tsum_mul_left]
  let E : {x : K // x ∈ dualIdeal K a} ≃ {x : K // x ∈ ((dualUnit K a :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)} :=
    Equiv.subtypeEquivRight fun x => by rw [e]
  refine Eq.trans ?_ (E.tsum_eq _)
  refine tsum_congr fun β => ?_
  simp only [hs, sub_zero, mul_zero, map_zero, Rat.cast_zero, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  exact dualTerm_eq ht (β : K)

end Dual

section Bounds

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- The term $e^{-\pi \sum_w n_w t_w |\alpha|_w^2}$ of the theta function of weight $0$ decreases when $t$ increases. -/
theorem thetaTerm_anti (α : K) {s t : InfinitePlace K → ℝ} (hst : ∀ w, s w ≤ t w) :
    thetaTerm α t ≤ thetaTerm α s := by
  refine Real.exp_le_exp.2 ?_
  have : ∑ w, (mult w : ℝ) * s w * w α ^ 2 ≤ ∑ w, (mult w : ℝ) * t w * w α ^ 2 :=
    Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hst w) (Nat.cast_nonneg _)) (sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- If $s \ge 0$ and $t_w \ge s$ for all $w$, then $|h_t(\alpha)| \le C_{p, k}$ times the term of $\alpha$ in the theta function of weight $0$ at the constant point $s / 4$. -/
theorem norm_heckeTerm_le_const {s : ℝ} (hs : 0 ≤ s) {t : InfinitePlace K → ℝ}
    (hst : ∀ w, s ≤ t w) (α : K) :
    ‖heckeTerm p k α t‖ ≤ heckeConst p k * thetaTerm α (fun _ => s / 4) :=
  (norm_heckeTerm_le (fun w => hs.trans (hst w)) α).trans
    (mul_le_mul_of_nonneg_left (thetaTerm_anti α fun w => by have := hst w; linarith)
      heckeConst_pos.le)

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(t) - h_t(0)| \le C_{p, k} (\theta_{\mathfrak{b}}(s / 4) - 1)$. -/
theorem norm_heckeTheta_sub_le (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖heckeTheta K p k b t - heckeTerm p k 0 t‖ ≤
      heckeConst p k * (dedekindTheta K b (fun _ => s / 4) - 1) := by
  have ht : ∀ w, 0 < t w := fun w => hs.trans_le (hst w)
  let z : (b : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((b : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  have hθ : HasSum (fun α : (b : FractionalIdeal (𝓞 K)⁰ K) => thetaTerm (α : K) (fun _ => s / 4))
      (dedekindTheta K b (fun _ => s / 4)) :=
    (summable_dedekindTheta b (t := fun _ => s / 4) fun _ => by positivity).hasSum
  have hG := (hθ.sub (hasSum_ite_eq z (1 : ℝ))).mul_left (heckeConst p k)
  have hF : heckeTheta K p k b t - heckeTerm p k 0 t =
      ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
        (heckeTerm p k (α : K) t - if α = z then heckeTerm p k 0 t else 0) := by
    rw [Summable.tsum_sub (summable_heckeTerm p k b ht) ⟨_, hasSum_ite_eq z _⟩, tsum_ite_eq,
      heckeTheta_eq_tsum]
  rw [hF]
  refine tsum_of_norm_bounded hG fun α => ?_
  by_cases h : α = z
  · subst h
    simp [thetaTerm, z]
  · simp only [h, ↓reduceIte, sub_zero]
    exact norm_heckeTerm_le_const hs.le hst _

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then $|\Theta_{\mathfrak{b}}^{p, k}(t)| \le C_{p, k} \, \theta_{\mathfrak{b}}(s / 4)$. -/
theorem norm_heckeTheta_le (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖heckeTheta K p k b t‖ ≤ heckeConst p k * dedekindTheta K b (fun _ => s / 4) := by
  have h1 := norm_heckeTheta_sub_le (p := p) (k := k) b hs hst
  have h2 := norm_heckeTerm_le_const (p := p) (k := k) hs.le hst 0
  have h3 : thetaTerm (0 : K) (fun _ => s / 4) = 1 := by simp [thetaTerm]
  rw [h3] at h2
  calc ‖heckeTheta K p k b t‖
      ≤ ‖heckeTheta K p k b t - heckeTerm p k 0 t‖ + ‖heckeTerm p k 0 t‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

/-- Each normalized term $h_t(\alpha)$ is continuous in $t$ on the set of $t$ with all coordinates positive. -/
theorem continuousOn_heckeTerm (α : K) :
    ContinuousOn (fun t => heckeTerm p k α t) {t : InfinitePlace K → ℝ | ∀ w, 0 < t w} := by
  simp_rw [heckeTerm_eq_prod]
  refine continuousOn_finsetProd _ fun w _ => ?_
  have hg : Continuous fun t : ℝ => placeGauss p k t α w := by
    unfold placeGauss realGaussWeight gaussWeight
    split_ifs <;> fun_prop
  refine ContinuousOn.mul ?_ (hg.comp (continuous_apply w)).continuousOn
  refine (Complex.continuous_ofReal.comp (continuous_apply w)).continuousOn.cpow_const ?_
  exact fun t ht => Complex.ofReal_mem_slitPlane.2 (ht w)

/-- The normalized theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_heckeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (heckeTheta K p k b) t := by
  obtain ⟨m, hm, hmt⟩ : ∃ m > 0, ∀ w, m ≤ t w := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty t, ?_, fun w => Finset.inf'_le _ (Finset.mem_univ w)⟩
    exact (Finset.lt_inf'_iff _).2 fun w _ => ht w
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | m / 2 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have htU : t ∈ U := mem_iInter.2 fun w => (half_lt_self hm).trans_le (hmt w)
  have hc : ContinuousOn (fun s => ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
      heckeTerm p k (α : K) s) U := by
    refine continuousOn_tsum (fun α => (continuousOn_heckeTerm (α : K)).mono fun s hs w =>
        (half_pos hm).trans (mem_iInter.1 hs w))
      ((summable_dedekindTheta b (t := fun _ => m / 2 / 4) fun _ => by positivity).mul_left
        (heckeConst p k)) ?_
    intro α s hs
    exact norm_heckeTerm_le_const (half_pos hm).le (fun w => (mem_iInter.1 hs w).le) _
  have he : heckeTheta K p k b = fun s => ∑' α : (b : FractionalIdeal (𝓞 K)⁰ K),
      heckeTerm p k (α : K) s := funext (heckeTheta_eq_tsum K p k b)
  rw [he]
  exact hc.continuousAt (hU.mem_nhds htU)

omit [NumberField K] in
/-- The square of the multiplicity of an infinite place is at least $1$. -/
theorem one_le_mult_sq (w : InfinitePlace K) : 1 ≤ (mult w : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ mult w := Nat.one_le_cast.2 mult_pos
  nlinarith

/-- The dual theta series is continuous at each point $t$ with all coordinates positive. -/
theorem continuousAt_heckeDualTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : InfinitePlace K → ℝ}
    (ht : ∀ w, 0 < t w) : ContinuousAt (heckeDualTheta K p k a) t := by
  set U : Set (InfinitePlace K → ℝ) := ⋂ w, {s | 0 < s w}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have he : (fun s => conj (heckeTheta K p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * s w)))
      =ᶠ[𝓝 t] heckeDualTheta K p k a := by
    filter_upwards [hU.mem_nhds (mem_iInter.2 ht)] with s hs
    exact (heckeDualTheta_eq p k a fun w => (mem_iInter.1 hs w).le).symm
  refine ContinuousAt.congr ?_ he
  refine Complex.continuous_conj.continuousAt.comp ?_
  refine ContinuousAt.comp (g := heckeTheta K p k (dualUnit K a))
    (continuousAt_heckeTheta _ fun w => mul_pos (one_pos.trans_le (one_le_mult_sq w)) (ht w)) ?_
  exact (continuous_pi fun w => continuous_const.mul (continuous_apply w)).continuousAt

/-- If $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series at $t$ has the absolute value at most $C_{p, k} \, \theta_{(\mathfrak{a} \mathfrak{d})^{-1}}(s / 4)$. -/
theorem norm_heckeDualTheta_le (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 0 < s)
    {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖heckeDualTheta K p k a t‖ ≤
      heckeConst p k * dedekindTheta K (dualUnit K a) (fun _ => s / 4) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [heckeDualTheta_eq p k a fun w => hs.le.trans (hst w), Complex.norm_conj]
  exact norm_heckeTheta_le _ hs hst'

/-- If the weight is not zero, $s > 0$ and $t_w \ge s$ for all $w$, then the dual theta series at $t$ has the absolute value at most $C_{p, k} (\theta_{(\mathfrak{a} \mathfrak{d})^{-1}}(s / 4) - 1)$. -/
theorem norm_heckeDualTheta_le_of_ne (h : p ≠ 0 ∨ k ≠ 0) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℝ} (hs : 0 < s) {t : InfinitePlace K → ℝ} (hst : ∀ w, s ≤ t w) :
    ‖heckeDualTheta K p k a t‖ ≤
      heckeConst p k * (dedekindTheta K (dualUnit K a) (fun _ => s / 4) - 1) := by
  have hst' : ∀ w, s ≤ (mult w : ℝ) ^ 2 * t w := fun w => by
    have := hst w
    nlinarith [one_le_mult_sq w]
  rw [heckeDualTheta_eq p k a fun w => hs.le.trans (hst w), Complex.norm_conj]
  have := norm_heckeTheta_sub_le (p := p) (k := k) (dualUnit K a) hs hst'
  rwa [heckeTerm_zero h, sub_zero] at this

end Bounds

section Cube

variable {K : Type*} [Field K] [NumberField K]

/-- The cube $[0, 1)^r$ of the unit coordinates. -/
local notation "cube" => Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1

/-- If $y \ge 0$ and $|c_i| \le 1$ for all $i$, then each coordinate of $t(y, c)$ is at least $y$ times the constant `Langlands.Tate.unitBound`. -/
theorem mul_unitBound_le_of_abs_le {y : ℝ} (hy : 0 ≤ y) {c : Fin (rank K) → ℝ}
    (hc : ∀ i, |c i| ≤ 1) (w : InfinitePlace K) :
    y * unitBound K ≤ unitScale K y c w := by
  rw [unitScale, unitBound]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hy
  have h1 : ∀ i, -|unitLog K i w| ≤ c i * unitLog K i w := fun i => by
    have : |c i * unitLog K i w| ≤ |unitLog K i w| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hc i)
    exact (neg_le_neg this).trans (neg_abs_le _)
  have h2 : ∀ i, |unitLog K i w| ≤ ∑ v, |unitLog K i v| := fun i =>
    Finset.single_le_sum (f := fun v => |unitLog K i v|) (fun v _ => abs_nonneg _)
      (Finset.mem_univ w)
  have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  have h4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  simp only [Finset.sum_neg_distrib] at h3
  linarith

/-- Each coordinate of a point of the cube $[0, 1)^r$ has the absolute value at most $1$. -/
theorem abs_le_one_of_mem_unitCube {c : Fin (rank K) → ℝ} (hc : c ∈ cube) (i : Fin (rank K)) :
    |c i| ≤ 1 := by
  obtain ⟨h0, h1⟩ := mem_Icc_of_mem_unitCube hc i
  rw [abs_le]
  constructor <;> linarith

/-- Let $\Phi$ be continuous at each point with positive coordinates and bounded on each set $\{t : t_w \ge s\}$ with $s > 0$. Let $u$ be continuous with $|u(c)_i| \le 1$ on the cube. Then $y \mapsto \int_{[0, 1)^r} \Phi(t(y, u(c))) \, dc$ is continuous on $y > 0$. -/
theorem continuousOn_integral_unitCube (Φ : (InfinitePlace K → ℝ) → ℂ)
    {u : (Fin (rank K) → ℝ) → Fin (rank K) → ℝ} (hu : Continuous u)
    (hu1 : ∀ c ∈ cube, ∀ i, |u c i| ≤ 1)
    (hΦ : ∀ t : InfinitePlace K → ℝ, (∀ w, 0 < t w) → ContinuousAt Φ t)
    (hB : ∀ s : ℝ, 0 < s → ∃ B, ∀ t : InfinitePlace K → ℝ, (∀ w, s ≤ t w) → ‖Φ t‖ ≤ B) :
    ContinuousOn (fun y => ∫ c in cube, Φ (unitScale K y (u c))) (Ioi 0) := by
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  have hh := half_pos hy₀'
  obtain ⟨B, hB⟩ := hB (y₀ / 2 * unitBound K) (mul_pos hh unitBound_pos)
  have hcont : ∀ y : ℝ, 0 < y → Continuous fun c => Φ (unitScale K y (u c)) := fun y hy =>
    continuous_iff_continuousAt.2 fun c =>
      ContinuousAt.comp (f := fun c => unitScale K y (u c)) (hΦ _ (unitScale_pos hy (u c)))
        ((continuous_unitScale y).comp hu).continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ ?_ ?_
  · filter_upwards [Ioi_mem_nhds (half_lt_self hy₀')] with y hy
    exact (hcont y (hh.trans hy)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (half_lt_self hy₀')] with y hy
    have hy' : 0 < y := hh.trans hy
    refine (ae_restrict_iff' measurableSet_unitCube).2 (Eventually.of_forall fun c hc => ?_)
    refine hB _ fun w => ?_
    exact (mul_le_mul_of_nonneg_right (le_of_lt hy) unitBound_pos.le).trans
      (mul_unitBound_le_of_abs_le hy'.le (hu1 c hc) w)
  · exact integrableOn_const volume_unitCube_ne_top
  · exact Eventually.of_forall fun c =>
      ContinuousAt.comp (f := fun y => unitScale K y (u c)) (hΦ _ (unitScale_pos hy₀' (u c)))
        (continuous_unitScale_left (u c)).continuousAt

/-- If $|\Phi(t)| \le C (\theta_{\mathfrak{b}}(s / 4) - 1)$ when $t_w \ge s > 0$ for all $w$, and $|u(c)_i| \le 1$ on the cube, then $y \mapsto \int_{[0, 1)^r} \Phi(t(y, u(c))) \, dc$ is $O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_integral_unitCube (Φ : (InfinitePlace K → ℝ) → ℂ)
    {u : (Fin (rank K) → ℝ) → Fin (rank K) → ℝ} (hu1 : ∀ c ∈ cube, ∀ i, |u c i| ≤ 1)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ s : ℝ, 0 < s → ∀ t : InfinitePlace K → ℝ, (∀ w, s ≤ t w) →
      ‖Φ t‖ ≤ C * (dedekindTheta K b (fun _ => s / 4) - 1)) (r : ℝ) :
    (fun y => ∫ c in cube, Φ (unitScale K y (u c))) =O[atTop] (· ^ r) := by
  have hm : 0 < unitBound K / 4 := by have := unitBound_pos (K := K); positivity
  have h1 := (isBigO_latticeTheta_sub_one (traceLattice K b) r).comp_tendsto
    (tendsto_id.atTop_mul_const hm)
  have h2 : (fun y : ℝ => (id y * (unitBound K / 4)) ^ r) =O[atTop] (· ^ r) := by
    refine IsBigO.of_bound ((unitBound K / 4) ^ r) ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    rw [id, Real.mul_rpow hy hm.le, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), mul_comm]
  refine IsBigO.trans ?_ (h1.trans h2)
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hs : 0 < y * unitBound K := mul_pos hy unitBound_pos
  have hL : dedekindTheta K b (fun _ => y * unitBound K / 4) =
      latticeTheta (traceLattice K b) (id y * (unitBound K / 4)) := by
    rw [dedekindTheta_const, id, mul_div_assoc]
  have hI : ‖∫ c in cube, Φ (unitScale K y (u c))‖ ≤
      C * (latticeTheta (traceLattice K b) (id y * (unitBound K / 4)) - 1) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) volume_unitCube_ne_top.lt_top
      (f := fun c => Φ (unitScale K y (u c)))
      (C := C * (dedekindTheta K b (fun _ => y * unitBound K / 4) - 1))
      fun c hc => hB _ hs _ fun w => mul_unitBound_le_of_abs_le hy.le (hu1 c hc) w
    rwa [volume_real_unitCube, mul_one, hL] at this
  refine hI.trans (mul_le_mul_of_nonneg_left ?_ hC)
  simp only [Function.comp_apply]
  rw [show (latticeTheta (traceLattice K b) (id y * (unitBound K / 4)) : ℂ) - 1 =
    ((latticeTheta (traceLattice K b) (id y * (unitBound K / 4)) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real]
  exact Real.le_norm_self _

end Cube

section Pair

variable (K : Type*) [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The cube average $F(y) = \int_{[0, 1)^r} \Theta_{\mathfrak{a}}^{p, k}(t(y, c)) \, dc$ of the normalized theta series. -/
noncomputable def heckeCubeTheta (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1), heckeTheta K p k a (unitScale K y c)

/-- The cube average $G(y) = \int_{[0, 1)^r} \widehat{\Theta}_{\mathfrak{a}}^{p, k}(t(y, -c)) \, dc$ of the dual theta series. -/
noncomputable def heckeCubeDualTheta (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    heckeDualTheta K p k a (unitScale K y (-c))

/-- The constant $\varepsilon = (-i)^{\sum_v p_v + \sum_w k_w} \big(N(\mathfrak{a}) \, 2^{-r_2} \sqrt{|d_K|}\big)^{-1}$ of the functional equation of the cube averages. -/
noncomputable def heckeRootConst : ℂ :=
  (-I) ^ (∑ v, p v + ∑ w, k w) *
    (((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      (2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|)⁻¹ : ℝ)

variable {K p k a}

/-- The constant $\varepsilon$ is not zero. -/
theorem heckeRootConst_ne_zero : heckeRootConst K p k a ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 I_ne_zero)) (Complex.ofReal_ne_zero.2 ?_)
  have hd : 0 < |(discr K : ℝ)| := by
    have := discr_ne_zero K
    positivity
  have := absNorm_pos K a
  exact inv_ne_zero (by positivity)

/-- For $y \ge 0$ the dual cube average is the cube average of the complex conjugate of the normalized theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$ at $(n_w^2 \, t(y, -c)_w)_w$. -/
theorem heckeCubeDualTheta_eq {y : ℝ} (hy : 0 ≤ y) :
    heckeCubeDualTheta K p k a y =
      ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
        conj (heckeTheta K p k (dualUnit K a) (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w)) := by
  rw [heckeCubeDualTheta]
  congr 1
  funext c
  exact heckeDualTheta_eq p k a fun w => mul_nonneg hy (Real.exp_pos _).le

/-- The functional equation of the cube averages: if $p_v \le 1$ for all real $v$ and $x > 0$, then $F(1 / x) = \varepsilon \, x^{n / 2} \, G(x)$. -/
theorem heckeCubeTheta_one_div (hp : ∀ v, p v ≤ 1) {x : ℝ} (hx : 0 < x) :
    heckeCubeTheta K p k a (1 / x) =
      (heckeRootConst K p k a * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        heckeCubeDualTheta K p k a x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [heckeCubeTheta, heckeCubeDualTheta, smul_eq_mul]
  simp_rw [heckeTheta_unitScale a hp (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul, heckeRootConst]

/-- The cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_heckeCubeTheta : ContinuousOn (heckeCubeTheta K p k a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i) (fun _ ht => continuousAt_heckeTheta a ht)
    fun _ hs => ⟨_, fun _ hst => norm_heckeTheta_le a hs hst⟩

/-- The dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_heckeCubeDualTheta : ContinuousOn (heckeCubeDualTheta K p k a) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_heckeDualTheta a ht)
    fun _ hs => ⟨_, fun _ hst => norm_heckeDualTheta_le a hs hst⟩

/-- If the weight is not zero, then $F(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_heckeCubeTheta (h : p ≠ 0 ∨ k ≠ 0) (r : ℝ) :
    heckeCubeTheta K p k a =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := id) _ (fun c hc i => abs_le_one_of_mem_unitCube hc i) a
    heckeConst_pos.le (fun s hs t hst => by
      have := norm_heckeTheta_sub_le (p := p) (k := k) a hs hst
      rwa [heckeTerm_zero h, sub_zero] at this) r

/-- If the weight is not zero, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_heckeCubeDualTheta (h : p ≠ 0 ∨ k ≠ 0) (r : ℝ) :
    heckeCubeDualTheta K p k a =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := Neg.neg) _
    (fun c hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (dualUnit K a) heckeConst_pos.le (fun s hs t hst => norm_heckeDualTheta_le_of_ne h a hs hst) r

variable (a) in
/-- For $p_v \le 1$ and a nonzero weight, the cube averages $F$ and $G$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon$ and with both constant terms zero. -/
noncomputable def heckeFEPair (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) : WeakFEPair ℂ where
  f := heckeCubeTheta K p k a
  g := heckeCubeDualTheta K p k a
  k := finrank ℚ K / 2
  ε := heckeRootConst K p k a
  f₀ := 0
  g₀ := 0
  hf_int := continuousOn_heckeCubeTheta.locallyIntegrableOn measurableSet_Ioi
  hg_int := continuousOn_heckeCubeDualTheta.locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := heckeRootConst_ne_zero
  h_feq x hx := heckeCubeTheta_one_div hp hx
  hf_top r := by simpa only [sub_zero] using isBigO_heckeCubeTheta h r
  hg_top r := by simpa only [sub_zero] using isBigO_heckeCubeDualTheta h r

/-- The FE pair of the cube averages is a strong FE pair, because the constant terms are zero for a nonzero weight. -/
theorem isStrongFEPair_heckeFEPair (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) :
    IsStrongFEPair (heckeFEPair a hp h) :=
  ⟨rfl, rfl⟩

end Pair

section Completed

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
include hp h

/-- The completed function of the pair is the Mellin transform of $F$. -/
theorem Λ_heckeFEPair_eq : (heckeFEPair a hp h).Λ = mellin (heckeCubeTheta K p k a) :=
  (isStrongFEPair_heckeFEPair hp h).Λ_eq

/-- The completed function of the dual pair is the Mellin transform of $G$. -/
theorem symm_Λ_heckeFEPair_eq :
    (heckeFEPair a hp h).symm.Λ = mellin (heckeCubeDualTheta K p k a) :=
  (isStrongFEPair_heckeFEPair hp h).symm_Λ_eq

/-- The Mellin transform of $F$ continues to an entire function. -/
theorem differentiable_Λ_heckeFEPair : Differentiable ℂ (heckeFEPair a hp h).Λ :=
  (isStrongFEPair_heckeFEPair hp h).differentiable_Λ

/-- The Mellin transform of $G$ continues to an entire function. -/
theorem differentiable_mellin_heckeCubeDualTheta :
    Differentiable ℂ (mellin (heckeCubeDualTheta K p k a)) :=
  symm_Λ_heckeFEPair_eq hp h ▸ (isStrongFEPair_heckeFEPair hp h).symm.differentiable_Λ

/-- The functional equation $\Lambda(n / 2 - s) = \varepsilon \, \mathcal{M}G(s)$ for all complex $s$, where $\Lambda$ is the entire continuation of the Mellin transform of $F$. -/
theorem Λ_heckeFEPair_sub (s : ℂ) :
    (heckeFEPair a hp h).Λ (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * mellin (heckeCubeDualTheta K p k a) s := by
  have := (heckeFEPair a hp h).functional_equation s
  rw [symm_Λ_heckeFEPair_eq hp h, smul_eq_mul] at this
  convert this using 2
  · simp [heckeFEPair]
  · rfl

/-- If $\chi_\infty$ is trivial on the units and $\mathrm{Re}\, s > n / 2$, then $2^r c_K \Lambda(s)$ is the sum over the unit orbits of $\mathfrak{a} \setminus 0$ of $w_K \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}$ with $s' = 2 s / n$. Here $c_K$ is `Langlands.Tate.unitConst`. -/
theorem hasSum_Λ_heckeFEPair (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (heckeFEPair a hp h).Λ s) := by
  rw [Λ_heckeFEPair_eq hp h, mellin]
  simp_rw [smul_eq_mul]
  exact hasSum_integral_heckeTheta h hχ hs

end Completed

end Langlands.Tate
