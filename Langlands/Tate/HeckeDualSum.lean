/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeFEPair

/-!
# The dual side of the weighted Hecke functional equation

Let $K$ be a number field of degree $n$ with $r_2$ complex places and unit rank $r$, let $\mathfrak{d}$ be the different, and let $n_w$ be $1$ at a real place and $2$ at a complex place. Fix a weight $(p, k)$ with $p_v \le 1$, $(p, k) \neq 0$ and $\chi_\infty$ trivial on all units, and fix a nonzero fractional ideal $\mathfrak{a}$. Let $F_{\mathfrak{b}}$ and $G_{\mathfrak{a}}$ be the cube averages of `Langlands/Tate/HeckeFEPair.lean`. This file identifies $G_{\mathfrak{a}}$ with the complex conjugate of $F_{(\mathfrak{a} \mathfrak{d})^{-1}}$ and gets the symmetry of the completed partial Hecke sums.

First, the normalized theta series is periodic: $\Theta_{\mathfrak{b}}^{p, k}((t_w |u|_w^2)_w) = \Theta_{\mathfrak{b}}^{p, k}(t)$ for each unit $u$ with $\chi_\infty(u) = 1$.

Second, the integral over the cube $[0, 1)^r$ of a function that is periodic under $\mathbb{Z}^r$ does not change under $c \mapsto c_0 - c$.

Third, with $\lambda = 2^{4 r_2 / n}$ there is a vector $c_0 \in \mathbb{R}^r$ with $t(\lambda, c_0)_w = n_w^2$ for all $w$. So $n_w^2 \, t(y, -c)_w = t(\lambda y, c_0 - c)_w$. The value of $\lambda$ follows from the product formula $\prod_w t(y, c)_w^{n_w} = y^n$ and $\prod_w n_w^{2 n_w} = 4^{2 r_2}$.

With these steps, $G_{\mathfrak{a}}(y) = \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$ and $\mathcal{M}G_{\mathfrak{a}}(s) = \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$. Let $\Lambda_{\mathfrak{a}}(s) = 2^r c_K \, \mathcal{M}F_{\mathfrak{a}}(s)$ be the completed partial Hecke sum. It is entire, it is the partial Hecke sum of $\mathfrak{a}$ for $\mathrm{Re}\, s > n / 2$, and $$\Lambda_{\mathfrak{a}}(s) = \varepsilon_{\mathfrak{a}} \, \lambda^{s - n / 2} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(n / 2 - \bar{s})}$$ for all complex $s$, where $\varepsilon_{\mathfrak{a}}$ is `Langlands.Tate.heckeRootConst`. For $\mathrm{Re}\, s < 0$ the right side is the conjugate of the partial Hecke sum of $(\mathfrak{a} \mathfrak{d})^{-1}$.

## Main definitions

* `Langlands.Tate.heckeScale`: the constant $\lambda = 2^{4 r_2 / n}$.
* `Langlands.Tate.heckeShift`: a vector $c_0$ with $t(\lambda, c_0)_w = n_w^2$.
* `Langlands.Tate.completedPartialHecke`: the completed partial Hecke sum $\Lambda_{\mathfrak{a}}(s) = 2^r c_K \, \mathcal{M}F_{\mathfrak{a}}(s)$.

## Main results

* `Langlands.Tate.heckeTheta_unit`, `Langlands.Tate.heckeTheta_unitScale_add_int`: the periodicity of the normalized theta series.
* `Langlands.Tate.integral_unitCube_sub`: the invariance of the cube integral of a periodic function under $c \mapsto c_0 - c$.
* `Langlands.Tate.unitScale_heckeShift`, `Langlands.Tate.mult_sq_mul_unitScale_neg`: $t(\lambda, c_0)_w = n_w^2$ and $n_w^2 \, t(y, -c)_w = t(\lambda y, c_0 - c)_w$.
* `Langlands.Tate.heckeCubeDualTheta_eq_conj`: $G_{\mathfrak{a}}(y) = \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$.
* `Langlands.Tate.mellin_heckeCubeDualTheta`: $\mathcal{M}G_{\mathfrak{a}}(s) = \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$.
* `Langlands.Tate.differentiable_completedPartialHecke`, `Langlands.Tate.hasSum_completedPartialHecke`: $\Lambda_{\mathfrak{a}}$ is entire and is the partial Hecke sum for $\mathrm{Re}\, s > n / 2$.
* `Langlands.Tate.completedPartialHecke_sub`, `Langlands.Tate.completedPartialHecke_eq_conj`: the functional equation.
* `Langlands.Tate.hasSum_completedPartialHecke_of_re_neg`: $\Lambda_{\mathfrak{a}}(s)$ as the conjugate dual partial Hecke sum for $\mathrm{Re}\, s < 0$.

## Proof

The periodicity is the reindexing $\alpha \mapsto u \alpha$ of the ideal with `Langlands.Tate.unitMulEquiv` and `Langlands.Tate.heckeTerm_mul`. The reflection uses that the cube and its image under $c \mapsto c_0 - c$ are both fundamental domains of $\mathbb{Z}^r$. The vector $c_0$ comes from the surjectivity of Mathlib's `expMapBasis` onto $(0, \infty)^{S_\infty}$. The rest is `Langlands.Tate.heckeCubeDualTheta_eq`, the Mellin transform of a dilation and of a complex conjugate, and `Langlands.Tate.Λ_heckeFEPair_sub`.

## Open parts

The sum over the orbits of $(\mathfrak{a} \mathfrak{d})^{-1}$ appears as the complex conjugate of the sum for the weight $(p, k)$. The file does not rewrite it as the sum for the conjugate weight, and it does not yet assemble the partial sums over the ideal classes into the Hecke $L$-function of a Hecke character.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Periodic

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- **The periodicity under a unit.** If $u$ is a unit with $\chi_\infty(u) = 1$ and $t_w \ge 0$ for all $w$, then $\Theta_{\mathfrak{b}}^{p, k}((t_w |u|_w^2)_w) = \Theta_{\mathfrak{b}}^{p, k}(t)$. -/
theorem heckeTheta_unit (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {u : (𝓞 K)ˣ}
    (hu : infinityWeight p k (u : K) = 1) {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 ≤ t w) :
    heckeTheta K p k b (fun w => t w * w (u : K) ^ 2) = heckeTheta K p k b t := by
  rw [heckeTheta_eq_tsum, heckeTheta_eq_tsum]
  refine Eq.trans ?_ ((unitMulEquiv K (b : FractionalIdeal (𝓞 K)⁰ K) u).tsum_eq _)
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk]
  rw [heckeTerm_mul ht (coe_ne_zero u), hu, one_mul]

/-- **The periodicity in the unit coordinates.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $\Theta_{\mathfrak{b}}^{p, k}(t(y, c + m)) = \Theta_{\mathfrak{b}}^{p, k}(t(y, c))$ for each integer vector $m$. -/
theorem heckeTheta_unitScale_add_int (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : ℝ} (hy : 0 ≤ y) (c : Fin (rank K) → ℝ)
    (m : Fin (rank K) → ℤ) :
    heckeTheta K p k b (unitScale K y (c + fun i => (m i : ℝ))) =
      heckeTheta K p k b (unitScale K y c) := by
  have h : unitScale K y (c + fun i => (m i : ℝ)) =
      fun w => unitScale K y c w * w (unitOfInt K m : K) ^ 2 :=
    funext fun w => unitScale_add_int y c m w
  rw [h]
  exact heckeTheta_unit (t := unitScale K y c) b (hχ _) fun w => mul_nonneg hy (Real.exp_pos _).le

end Periodic

section Reflection

variable {r : ℕ}

/-- A vector of the integer span of the standard basis of $\mathbb{R}^r$ has integer coordinates. -/
theorem exists_int_of_mem_span_basisFun {g : Fin r → ℝ}
    (hg : g ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin r)))) :
    ∃ m : Fin r → ℤ, g = fun i => (m i : ℝ) := by
  have h : ∀ i, ∃ m : ℤ, g i = m := by
    intro i
    obtain ⟨m, hm⟩ := ((Pi.basisFun ℝ (Fin r)).mem_span_iff_repr_mem ℤ g).1 hg i
    exact ⟨m, by simpa using hm.symm⟩
  choose m hm using h
  exact ⟨m, funext hm⟩

/-- **The reflection of the cube.** Let $f$ be periodic under $\mathbb{Z}^r$. Then for each $c_0 \in \mathbb{R}^r$, $$\int_{[0, 1)^r} f(c_0 - c) \, dc = \int_{[0, 1)^r} f(c) \, dc.$$ -/
theorem integral_unitCube_sub (f : (Fin r → ℝ) → ℂ)
    (hf : ∀ (m : Fin r → ℤ) (c : Fin r → ℝ), f (c + fun i => (m i : ℝ)) = f c) (c₀ : Fin r → ℝ) :
    ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), f (c₀ - c) =
      ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), f c := by
  rw [← ZSpan.fundamentalDomain_pi_basisFun]
  set b := Pi.basisFun ℝ (Fin r)
  have hD := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin r → ℝ))
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hmp : MeasurePreserving (fun c : Fin r → ℝ => c₀ - c) volume volume :=
    Measure.measurePreserving_sub_left volume c₀
  have hD' := hD.preimage_of_equiv hmp.quasiMeasurePreserving (e := Neg.neg) neg_bijective
    fun g c => by
      simp only [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg]
      abel
  have hper : ∀ (g : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (c : Fin r → ℝ),
      f (c₀ - (g +ᵥ c)) = f (c₀ - c) := by
    intro g c
    obtain ⟨m, hm⟩ := exists_int_of_mem_span_basisFun (r := r) g.2
    have := hf (-m) (c₀ - c)
    rw [AddSubgroup.vadd_def, vadd_eq_add, hm]
    convert this using 2
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    ring
  rw [hD.setIntegral_eq hD' hper,
    hmp.setIntegral_preimage_emb (MeasurableEquiv.subLeft c₀).measurableEmbedding f]

end Reflection

section Scale

variable (K : Type*) [Field K] [NumberField K]

/-- The constant $\lambda = 2^{4 r_2 / n}$ of the change of variable from the dual theta series to the theta series of $(\mathfrak{a} \mathfrak{d})^{-1}$. -/
noncomputable def heckeScale : ℝ :=
  (2 : ℝ) ^ ((4 * nrComplexPlaces K : ℝ) / finrank ℚ K)

/-- The constant $\lambda$ is positive. -/
theorem heckeScale_pos : 0 < heckeScale K :=
  Real.rpow_pos_of_pos two_pos _

/-- The product $\prod_w n_w^{n_w}$ is $4^{r_2}$. -/
theorem prod_mult_pow_mult : ∏ w : InfinitePlace K, (mult w : ℝ) ^ mult w = 4 ^ nrComplexPlaces K := by
  rw [prod_eq_prod_mul_prod]
  have hr : ∀ v : {w : InfinitePlace K // IsReal w}, (mult v.1 : ℝ) ^ mult v.1 = 1 := fun v => by
    rw [mult_isReal v, Nat.cast_one, one_pow]
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, (mult w.1 : ℝ) ^ mult w.1 = 4 :=
    fun w => by rw [mult_isComplex w]; norm_num
  simp_rw [hr, hc]
  rw [Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

/-- **The exact value of $\lambda$.** There is a vector $c_0 \in \mathbb{R}^r$ with $t(\lambda, c_0)_w = n_w^2$ for all places $w$, where $\lambda = 2^{4 r_2 / n}$. -/
theorem exists_unitScale_eq_mult_sq :
    ∃ c₀ : Fin (rank K) → ℝ, ∀ w, unitScale K (heckeScale K) c₀ w = (mult w : ℝ) ^ 2 := by
  have hmem : (fun w : InfinitePlace K => (mult w : ℝ) ^ 2) ∈
      expMapBasis '' (univ : Set (realSpace K)) := by
    rw [image_expMapBasis]
    exact fun w _ => by have := one_le_mult_sq w; simp only [mem_Ioi]; linarith
  obtain ⟨x, -, hx⟩ := hmem
  set v := x w₀ with hv
  set c₀ : Fin (rank K) → ℝ := (2⁻¹ : ℝ) • (unitCoord K x).2 with hc₀
  have hsymm : (unitCoord K).symm (v, (2 : ℝ) • c₀) = x := by
    have e : (v, (2 : ℝ) • c₀) = unitCoord K x :=
      Prod.ext (unitCoord_apply_fst x).symm (by
        rw [hc₀, smul_smul, mul_inv_cancel₀ (two_ne_zero (α := ℝ)), one_smul])
    rw [e, MeasurableEquiv.symm_apply_apply]
  have hE : unitScale K (Real.exp v) c₀ = fun w => (mult w : ℝ) ^ 2 := by
    rw [← expMapBasis_unitCoord_symm, hsymm, hx]
  have hprod := prod_sqrt_unitScale (K := K) (Real.exp_pos v).le c₀
  rw [hE] at hprod
  have hl : ∏ w : InfinitePlace K, √((mult w : ℝ) ^ 2) ^ mult w = 4 ^ nrComplexPlaces K := by
    simp_rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    exact prod_mult_pow_mult K
  have hs : √(Real.exp v) = Real.exp (v / 2) := by
    rw [← Real.sqrt_sq (Real.exp_pos (v / 2)).le, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hl, hs, ← Real.exp_nat_mul] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_exp, Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 finrank_pos
  have hval : Real.exp v = heckeScale K := by
    rw [heckeScale, Real.rpow_def_of_pos two_pos]
    congr 1
    field_simp
    push_cast at hlog
    linarith
  exact ⟨c₀, fun w => by rw [← hval, hE]⟩

/-- A vector $c_0 \in \mathbb{R}^r$ with $t(\lambda, c_0)_w = n_w^2$ for all places $w$. -/
noncomputable def heckeShift : Fin (rank K) → ℝ :=
  (exists_unitScale_eq_mult_sq K).choose

variable {K}

/-- The point $t(\lambda, c_0)$ is $(n_w^2)_w$. -/
theorem unitScale_heckeShift (w : InfinitePlace K) :
    unitScale K (heckeScale K) (heckeShift K) w = (mult w : ℝ) ^ 2 :=
  (exists_unitScale_eq_mult_sq K).choose_spec w

/-- **The rescaling.** $n_w^2 \, t(y, -c)_w = t(\lambda y, c_0 - c)_w$ with $\lambda = 2^{4 r_2 / n}$. -/
theorem mult_sq_mul_unitScale_neg (y : ℝ) (c : Fin (rank K) → ℝ) (w : InfinitePlace K) :
    (mult w : ℝ) ^ 2 * unitScale K y (-c) w = unitScale K (heckeScale K * y) (heckeShift K - c) w := by
  rw [← unitScale_heckeShift w]
  simp only [unitScale, Pi.neg_apply, Pi.sub_apply]
  have he : Real.exp (2 * ∑ i, (heckeShift K i - c i) * unitLog K i w) =
      Real.exp (2 * ∑ i, heckeShift K i * unitLog K i w) *
        Real.exp (2 * ∑ i, -c i * unitLog K i w) := by
    rw [← Real.exp_add]
    congr 1
    simp only [sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [he]
  ring

end Scale

section Mellin

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

/-- **The dual cube average.** If $\chi_\infty$ is trivial on all units and $y \ge 0$, then $G_{\mathfrak{a}}(y) = \overline{F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\lambda y)}$. -/
theorem heckeCubeDualTheta_eq_conj (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {y : ℝ} (hy : 0 ≤ y) :
    heckeCubeDualTheta K p k a y =
      conj (heckeCubeTheta K p k (dualUnit K a) (heckeScale K * y)) := by
  have h : ∀ c : Fin (rank K) → ℝ,
      (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w) =
        unitScale K (heckeScale K * y) (heckeShift K - c) :=
    fun c => funext fun w => mult_sq_mul_unitScale_neg y c w
  rw [heckeCubeDualTheta_eq hy, heckeCubeTheta]
  simp_rw [h]
  rw [integral_conj, integral_unitCube_sub
    (fun c => heckeTheta K p k (dualUnit K a) (unitScale K (heckeScale K * y) c))
    (fun m c => heckeTheta_unitScale_add_int hχ _
      (mul_nonneg (heckeScale_pos K).le hy) c m) (heckeShift K)]

omit [NumberField K] in
/-- For $x \ge 0$ real and $z$ complex, $\overline{x^z} = x^{\bar{z}}$. -/
theorem conj_ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (z : ℂ) :
    conj ((x : ℂ) ^ z) = (x : ℂ) ^ conj z := by
  have harg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact Real.pi_pos.ne
  rw [cpow_conj _ _ harg, Complex.conj_ofReal]

omit [NumberField K] in
/-- The Mellin transform of the complex conjugate: $\mathcal{M}\bar{f}(s) = \overline{\mathcal{M}f(\bar{s})}$. -/
theorem mellin_conj (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => conj (f t)) s = conj (mellin f (conj s)) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul, map_mul, conj_ofReal_cpow (le_of_lt ht), map_sub, map_one,
    Complex.conj_conj]

/-- **The Mellin transform of the dual cube average.** If $\chi_\infty$ is trivial on all units, then $\mathcal{M}G_{\mathfrak{a}}(s) = \lambda^{-s} \, \overline{\mathcal{M}F_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})}$ for all complex $s$. -/
theorem mellin_heckeCubeDualTheta (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) (s : ℂ) :
    mellin (heckeCubeDualTheta K p k a) s =
      (heckeScale K : ℂ) ^ (-s) * conj (mellin (heckeCubeTheta K p k (dualUnit K a)) (conj s)) := by
  have h : mellin (heckeCubeDualTheta K p k a) s =
      mellin (fun y => conj (heckeCubeTheta K p k (dualUnit K a) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [heckeCubeDualTheta_eq_conj hχ (le_of_lt hy)]
  rw [h, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul, map_mul,
    conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]

end Mellin

section Completed

variable (K : Type*) [Field K] [NumberField K]
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The completed partial Hecke sum $\Lambda_{\mathfrak{a}}(s) = 2^r c_K \, \mathcal{M}F_{\mathfrak{a}}(s)$ of the weight $(p, k)$, where $F_{\mathfrak{a}}$ is the cube average `Langlands.Tate.heckeCubeTheta` and $c_K$ is `Langlands.Tate.unitConst`. For $p_v \le 1$ and $(p, k) \neq 0$ the Mellin integral converges for all $s$, and the function is entire. -/
noncomputable def completedPartialHecke (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * mellin (heckeCubeTheta K p k a) s

variable {K p k a}

/-- The completed partial Hecke sum is $2^r c_K$ times the completed function of the FE pair. -/
theorem completedPartialHecke_eq (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) (s : ℂ) :
    completedPartialHecke K p k a s =
      ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (heckeFEPair a hp h).Λ s := by
  rw [Λ_heckeFEPair_eq hp h, completedPartialHecke]

/-- **The completed partial Hecke sum is entire.** -/
theorem differentiable_completedPartialHecke (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0) :
    Differentiable ℂ (completedPartialHecke K p k a) := by
  have e : completedPartialHecke K p k a =
      fun s => ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (heckeFEPair a hp h).Λ s :=
    funext (completedPartialHecke_eq hp h)
  rw [e]
  exact (differentiable_Λ_heckeFEPair hp h).const_mul _

/-- **The completed partial Hecke sum as a series.** If $(p, k) \neq 0$, $\chi_\infty$ is trivial on all units and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_{\mathfrak{a}}(s) = \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} w_K \, \Gamma_{p, k}(s') \, \chi_\infty(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_completedPartialHecke (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        infinityWeight p k (orbitRep a I : K) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (completedPartialHecke K p k a s) := by
  rw [completedPartialHecke, mellin]
  simp_rw [smul_eq_mul]
  exact hasSum_integral_heckeTheta h hχ hs

/-- **The functional equation of the completed partial Hecke sums.** Let $p_v \le 1$, $(p, k) \neq 0$, and let $\chi_\infty$ be trivial on all units. Then for all complex $s$, $$\Lambda_{\mathfrak{a}}(n / 2 - s) = \varepsilon_{\mathfrak{a}} \, \lambda^{-s} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(\bar{s})},$$ with $\lambda = 2^{4 r_2 / n}$ and $\varepsilon_{\mathfrak{a}} = (-i)^{\sum_v p_v + \sum_w k_w} (N(\mathfrak{a}) 2^{-r_2} \sqrt{|d_K|})^{-1}$. -/
theorem completedPartialHecke_sub (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) (s : ℂ) :
    completedPartialHecke K p k a (finrank ℚ K / 2 - s) =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (-s) *
        conj (completedPartialHecke K p k (dualUnit K a) (conj s)) := by
  rw [completedPartialHecke_eq hp h, Λ_heckeFEPair_sub hp h, mellin_heckeCubeDualTheta hχ,
    completedPartialHecke, map_mul, Complex.conj_ofReal]
  ring

/-- **The functional equation, solved for $\Lambda_{\mathfrak{a}}(s)$.** Under the hypotheses of `completedPartialHecke_sub`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(s) = \varepsilon_{\mathfrak{a}} \, \lambda^{s - n / 2} \, \overline{\Lambda_{(\mathfrak{a} \mathfrak{d})^{-1}}(n / 2 - \bar{s})}.$$ -/
theorem completedPartialHecke_eq_conj (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) (s : ℂ) :
    completedPartialHecke K p k a s =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (s - finrank ℚ K / 2) *
        conj (completedPartialHecke K p k (dualUnit K a) (finrank ℚ K / 2 - conj s)) := by
  have e := completedPartialHecke_sub (a := a) hp h hχ (finrank ℚ K / 2 - s)
  rw [sub_sub_cancel, neg_sub] at e
  rw [e, map_sub, map_div₀, map_natCast, map_ofNat]

/-- **The dual series for $\mathrm{Re}\, s < 0$.** Under the hypotheses of `completedPartialHecke_sub`, let $\mathrm{Re}\, s < 0$ and $s^* = 2 (n / 2 - \bar{s}) / n$. Then $\Lambda_{\mathfrak{a}}(s)$ is the sum over $\beta \in ((\mathfrak{a} \mathfrak{d})^{-1} \setminus 0) / \mathcal{O}_K^\times$ of $$\varepsilon_{\mathfrak{a}} \, \lambda^{s - n / 2} \, \overline{w_K \, \Gamma_{p, k}(s^*) \, \chi_\infty(\beta) \, |N(\beta)|^{-s^*}}.$$ -/
theorem hasSum_completedPartialHecke_of_re_neg (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) {s : ℂ} (hs : s.re < 0) :
    HasSum (fun I : Orbits (dualUnit K a) =>
        heckeRootConst K p k a * (heckeScale K : ℂ) ^ (s - finrank ℚ K / 2) *
          conj ((torsionOrder K : ℂ) *
            (heckeGamma p k (2 * (finrank ℚ K / 2 - conj s) / finrank ℚ K) *
              infinityWeight p k (orbitRep (dualUnit K a) I : K) *
                ((|(Algebra.norm ℚ (orbitRep (dualUnit K a) I : K) : ℝ)| : ℝ) : ℂ) ^
                  (-(2 * (finrank ℚ K / 2 - conj s) / finrank ℚ K)))))
      (completedPartialHecke K p k a s) := by
  have hre : (finrank ℚ K : ℝ) / 2 < (finrank ℚ K / 2 - conj s).re := by
    rw [Complex.sub_re, Complex.conj_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  rw [completedPartialHecke_eq_conj hp h hχ]
  exact ((hasSum_completedPartialHecke (a := dualUnit K a) h hχ hre).map (starRingEnd ℂ)
    (continuous_conj)).mul_left _

end Completed

end Langlands.Tate
