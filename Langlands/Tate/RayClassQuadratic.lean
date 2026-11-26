/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeRamified
import Langlands.Tate.IdealZeta

/-!
# Shifted and twisted Epstein zeta functions

This file is the analytic part of the functional equation of the $L$-function of a Hecke character $\chi$ of ray class type of an imaginary quadratic field $K$. For such a $\chi$ with conductor $\mathfrak{f}$, the partial $L$-series of a class is a finite sum of lattice sums over $x + \mathfrak{f} J$ with $x \in J$. These are the shifted Epstein zeta functions below for the lattice $\mathfrak{f} J \subset \mathbb{C}$.

Let $M$ be a lattice in a real inner product space $V$ of dimension $n$, with dual lattice $M^\vee$. For $x, y \in V$, the shifted and twisted theta function and Epstein zeta function are $$\theta_M(x, y; t) = \sum_{\mu \in M} e^{-\pi t |x + \mu|^2} e^{2 \pi i \langle x + \mu, y \rangle}, \qquad Z_M(x, y; s) = \sum_{x + \mu \neq 0} e^{2 \pi i \langle x + \mu, y \rangle} |x + \mu|^{-s}.$$ The file proves the transformation formula of $\theta_M$, the meromorphic continuation of $\Lambda_M(x, y; s) = \Gamma_\mathbb{R}(s) Z_M(x, y; s)$, the functional equation $$\Lambda_M(x, y; n - s) = \mathrm{covol}(M)^{-1} e^{2 \pi i \langle x, y \rangle} \Lambda_{M^\vee}(-y, x; s),$$ and that $\Lambda_M(x, y; s)$ is entire if $x \notin M$ and $y \notin M^\vee$. It also proves that the ideal character of $\chi$ is periodic modulo the conductor.

## Main definitions

* `Langlands.Tate.shiftTheta`: the theta function $\theta_M(x, y; t)$.
* `Langlands.Tate.shiftConst`: the constant term $c_M(x)$, which is $1$ if $x \in M$ and $0$ if not.
* `Langlands.Tate.shiftThetaFEPair`: the pair $(\theta_M(x, y), \theta_{M^\vee}(-y, x))$ as a `WeakFEPair`.
* `Langlands.Tate.shiftEpsteinZeta`: the Epstein zeta function $Z_M(x, y; s)$.
* `Langlands.Tate.completedShiftEpsteinZeta`: the completed function $\Lambda_M(x, y; s)$.

## Main results

* `shiftTheta_eq`: $\theta_M(x, y; t) = \mathrm{covol}(M)^{-1} t^{-n/2} e^{2 \pi i \langle x, y \rangle} \theta_{M^\vee}(-y, x; 1/t)$.
* `hasSum_completedShiftEpsteinZeta` and `completedShiftEpsteinZeta_eq`: for $\mathrm{Re}\, s > n$, $\Lambda_M(x, y; s) = \Gamma_\mathbb{R}(s) Z_M(x, y; s)$.
* `differentiableAt_completedShiftEpsteinZeta`: $\Lambda_M(x, y; s)$ is holomorphic away from $s = 0$ and $s = n$. There is no pole at $s = 0$ if $x \notin M$, and no pole at $s = n$ if $y \notin M^\vee$.
* `differentiable_completedShiftEpsteinZeta`: $\Lambda_M(x, y; s)$ is entire if $x \notin M$ and $y \notin M^\vee$.
* `completedShiftEpsteinZeta_sub`: the functional equation above.
* `IsRayClassType.idealChar_toPrincipalIdeal_eq`: if $v(y - x) \geq a_v + v(x)$ at each ramified place, then $\chi((y)) = \chi((x))$.

## Proofs

The Fourier transform of $v \mapsto e^{-\pi t |v|^2} e^{2 \pi i \langle v, y \rangle}$ is $w \mapsto t^{-n/2} e^{-\pi |w - y|^2 / t}$. The Poisson summation formula on $x + M$ of `Langlands.Tate.tsum_add_zlattice_eq_of_hasDecay` then gives the transformation formula. The pair of theta functions is a `WeakFEPair`, so its Mellin transform has a meromorphic continuation and a functional equation. Its symmetric pair has the same function $\Lambda$ as the pair for $(M^\vee, -y, x)$, because $M^{\vee \vee} = M$, $\mathrm{covol}(M^\vee) = \mathrm{covol}(M)^{-1}$ and $c_M(-x) = c_M(x)$. The Dirichlet series comes from `hasSum_mellin_pi_mul_sq`. Periodicity follows from `Langlands.Tate.IsRayClassType.idealChar_toPrincipalIdeal` applied to $y / x$.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt` for a ramified $\chi$ of ray class type. These steps are still open. First, write the partial $L$-series of each ideal class as $w^{-1} N(J)^{s} \sum_{x \in J / \mathfrak{f} J} \chi((x) J^{-1}) Z_{\mathfrak{f} J}(x, 0; 2 s)$ in the embedding $K \subset \mathbb{C}$. Second, apply `completedShiftEpsteinZeta_sub` and identify the dual lattice $(\mathfrak{f} J)^\vee$ with $(\mathfrak{f} J \mathfrak{d})^{-1}$ up to conjugation and scaling. Third, use finite Fourier analysis on $J / \mathfrak{f} J$ and the Gauss sum $\tau(\chi)$ with $|\tau(\chi)|^2 = N(\mathfrak{f})$ for a primitive $\chi$ to collect the twisted sums into the partial $L$-series of $\chi^{-1}$, with root number $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open MeasureTheory Module Filter Topology Asymptotics Set Complex FourierTransform
open scoped RealInnerProductSpace Classical

namespace Langlands.Tate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Gaussian

/-- The additive character $e^{2 \pi i r}$ has absolute value $1$. -/
theorem norm_cexp_two_pi_I_mul (r : ℝ) : ‖cexp (2 * Real.pi * I * r)‖ = 1 := by
  rw [show (2 * Real.pi * I * r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A bound for a shifted Gaussian: for $a \ge 0$, $e^{-a |x + v|^2} \le e^{a |x|^2} e^{-(a/2) |v|^2}$. -/
theorem exp_neg_mul_norm_add_sq_le {a : ℝ} (ha : 0 ≤ a) (x v : V) :
    Real.exp (-a * ‖x + v‖ ^ 2) ≤ Real.exp (a * ‖x‖ ^ 2) * Real.exp (-(a / 2) * ‖v‖ ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
    have := norm_sub_le (x + v) x
    rwa [add_sub_cancel_left] at this
  have h2 : ‖v‖ ^ 2 ≤ 2 * ‖x + v‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg v) h1
    nlinarith [sq_nonneg (‖x + v‖ - ‖x‖)]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

variable (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M]

/-- For $a > 0$ and $x \in V$, the series $\sum_{\mu \in M} e^{-a |x + \mu|^2}$ converges. -/
theorem summable_exp_neg_mul_norm_add_sq {a : ℝ} (ha : 0 < a) (x : V) :
    Summable fun μ : M => Real.exp (-a * ‖x + μ‖ ^ 2) := by
  have hs : Summable fun μ : M => Real.exp (-(a / 2) * ‖(μ : V)‖ ^ 2) :=
    Complex.summable_ofReal.1 (summable_zlattice_of_hasDecay M
      (hasDecay_gaussian (E := V) (half_pos ha) _) (Nat.lt_succ_self (finrank ℝ V)))
  exact (hs.mul_left (Real.exp (a * ‖x‖ ^ 2))).of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    fun μ => exp_neg_mul_norm_add_sq_le ha.le x μ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [IsZLattice ℝ M] in
/-- A shifted lattice is discrete: there is $c > 0$ with $c \le |x + \mu|^2$ for each $\mu \in M$ with $x + \mu \neq 0$. -/
theorem exists_pos_le_norm_add_sq [ProperSpace V] (x : V) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ : M, x + (μ : V) ≠ 0 → c ≤ ‖x + μ‖ ^ 2 := by
  have H : IsClosed (M : Set V) := M.toAddSubgroup.isClosed_of_discreteTopology
  set S : Set M := {μ | ‖x + (μ : V)‖ ≤ 1 ∧ x + (μ : V) ≠ 0} with hS
  have hfin : S.Finite := by
    have := (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := -x) (r := 1)) H).preimage_embedding
      (Function.Embedding.subtype (· ∈ M))
    refine this.subset fun μ hμ => ?_
    simp only [Set.mem_preimage, Function.Embedding.coe_subtype, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add, SetLike.mem_coe, SetLike.coe_mem,
      and_true]
    rw [add_comm]
    exact hμ.1
  by_cases hne : S.Nonempty
  · obtain ⟨μ₀, hμ₀, hmin⟩ := Set.exists_min_image S (fun μ : M => ‖x + (μ : V)‖ ^ 2) hfin hne
    have hpos : 0 < ‖x + (μ₀ : V)‖ ^ 2 := by
      have := norm_pos_iff.2 hμ₀.2
      positivity
    refine ⟨min 1 (‖x + (μ₀ : V)‖ ^ 2), lt_min one_pos hpos, fun μ hμ => ?_⟩
    by_cases h1 : ‖x + (μ : V)‖ ≤ 1
    · exact (min_le_right _ _).trans (hmin μ ⟨h1, hμ⟩)
    · refine (min_le_left _ _).trans ?_
      push Not at h1
      nlinarith
  · refine ⟨1, one_pos, fun μ hμ => ?_⟩
    by_contra h
    push Not at h
    have h1 : ‖x + (μ : V)‖ ≤ 1 := by
      by_contra h'
      push Not at h'
      nlinarith
    exact hne ⟨μ, h1, hμ⟩

end Gaussian

section Theta

variable (M : Submodule ℤ V)

/-- The shifted and twisted theta function $$\theta_M(x, y; t) = \sum_{\mu \in M} e^{-\pi t |x + \mu|^2} e^{2 \pi i \langle x + \mu, y \rangle}$$ of a lattice $M$, for $x, y \in V$. It is meaningful for $t > 0$. -/
noncomputable def shiftTheta (x y : V) (t : ℝ) : ℂ :=
  ∑' μ : M, (Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫)

/-- The constant term of $\theta_M(x, y; t)$ at $t = \infty$: it is $1$ if $x \in M$ and $0$ otherwise. -/
noncomputable def shiftConst (x : V) : ℂ :=
  if x ∈ M then 1 else 0

omit [FiniteDimensional ℝ V] in
/-- The terms of the shifted theta series have absolute value $e^{-\pi t |x + \mu|^2}$. -/
theorem norm_shiftTheta_term (x y : V) (t : ℝ) (μ : M) :
    ‖(Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫)‖ =
      Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) := by
  rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

variable [DiscreteTopology M] [IsZLattice ℝ M]

/-- The series of $\theta_M(x, y; t)$ converges for $t > 0$. -/
theorem summable_shiftTheta (x y : V) {t : ℝ} (ht : 0 < t) :
    Summable fun μ : M =>
      (Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫) :=
  Summable.of_norm_bounded (summable_exp_neg_mul_norm_add_sq M (mul_pos Real.pi_pos ht) x)
    fun μ => (norm_shiftTheta_term M x y t μ).le

/-- The theta series without its constant term: $\sum_{x + \mu \neq 0} (\ldots) = \theta_M(x, y; t) - c_M(x)$. -/
theorem hasSum_shiftTheta_sub (x y : V) {t : ℝ} (ht : 0 < t) :
    HasSum (fun μ : M => if x + (μ : V) = 0 then 0 else
      (Real.exp (-(Real.pi * t) * ‖x + μ‖ ^ 2) : ℂ) * cexp (2 * Real.pi * I * ⟪x + μ, y⟫))
      (shiftTheta M x y t - shiftConst M x) := by
  have hs := (summable_shiftTheta M x y ht).hasSum
  by_cases hx : x ∈ M
  · set μ₀ : M := ⟨-x, M.neg_mem hx⟩
    have h := hasSum_ite_sub_hasSum hs μ₀
    have he : ∀ μ : M, x + (μ : V) = 0 ↔ μ = μ₀ := fun μ => by
      rw [Subtype.ext_iff, add_eq_zero_iff_eq_neg']
    have h0 : (Real.exp (-(Real.pi * t) * ‖x + (μ₀ : V)‖ ^ 2) : ℂ) *
        cexp (2 * Real.pi * I * ⟪x + (μ₀ : V), y⟫) = 1 := by
      simp [μ₀]
    simp only [he]
    have hc : shiftConst M x = 1 := by simp [shiftConst, hx]
    rw [hc, ← h0]
    exact h
  · have hne : ∀ μ : M, x + (μ : V) ≠ 0 := fun μ h =>
      hx (by rw [add_eq_zero_iff_eq_neg] at h; rw [h]; exact M.neg_mem μ.2)
    have hc : shiftConst M x = 0 := by simp [shiftConst, hx]
    simp only [hne, ite_false, hc, sub_zero]
    exact hs

/-- The shifted theta function is continuous on $(0, \infty)$. -/
theorem continuousOn_shiftTheta (x y : V) : ContinuousOn (shiftTheta M x y) (Ioi 0) := by
  intro t₀ ht₀
  have hδ : (0 : ℝ) < t₀ / 2 := half_pos ht₀
  have hc : ContinuousOn (shiftTheta M x y) (Ioi (t₀ / 2)) := by
    refine continuousOn_tsum (fun μ => by fun_prop)
      (summable_exp_neg_mul_norm_add_sq M (mul_pos Real.pi_pos hδ) x) ?_
    intro μ t ht
    rw [norm_shiftTheta_term]
    refine Real.exp_le_exp.2 ?_
    have h1 : t₀ / 2 ≤ t := le_of_lt ht
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg ‖x + (μ : V)‖)) (sub_nonneg.2 h1)]
  exact (hc.continuousAt (Ioi_mem_nhds (half_lt_self ht₀))).continuousWithinAt

/-- The shifted theta function is locally integrable on $(0, \infty)$. -/
theorem locallyIntegrableOn_shiftTheta (x y : V) :
    LocallyIntegrableOn (shiftTheta M x y) (Ioi 0) :=
  (continuousOn_shiftTheta M x y).locallyIntegrableOn measurableSet_Ioi

/-- The shifted theta function minus its constant term decays exponentially: for $c$ as in `Langlands.Tate.exists_pos_le_norm_add_sq` and $t \ge 1$, $$|\theta_M(x, y; t) - c_M(x)| \le e^{-\pi c (t - 1)} \sum_{\mu \in M} e^{-\pi |x + \mu|^2}.$$ -/
theorem norm_shiftTheta_sub_le (x y : V) {c : ℝ}
    (hc : ∀ μ : M, x + (μ : V) ≠ 0 → c ≤ ‖x + μ‖ ^ 2) {t : ℝ} (ht : 1 ≤ t) :
    ‖shiftTheta M x y t - shiftConst M x‖ ≤
      Real.exp (-(Real.pi * c) * (t - 1)) * ∑' μ : M, Real.exp (-(Real.pi * 1) * ‖x + μ‖ ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  refine (hasSum_shiftTheta_sub M x y ht0).norm_le_of_bounded
    ((summable_exp_neg_mul_norm_add_sq M (mul_pos Real.pi_pos one_pos) x).hasSum.mul_left
      (Real.exp (-(Real.pi * c) * (t - 1)))) fun μ => ?_
  split_ifs with hμ
  · rw [norm_zero]
    positivity
  · rw [norm_shiftTheta_term, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 ht)) (sub_nonneg.2 (hc μ hμ))]

/-- The shifted theta function minus its constant term is $O(t^r)$ at infinity for each $r$. -/
theorem isBigO_shiftTheta_sub (x y : V) (r : ℝ) :
    (fun t => shiftTheta M x y t - shiftConst M x) =O[atTop] (· ^ r) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_add_sq M x
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop (mul_pos Real.pi_pos hc0) r).isBigO
  refine IsBigO.trans ?_ hexp
  set B := ∑' μ : M, Real.exp (-(Real.pi * 1) * ‖x + μ‖ ^ 2)
  refine IsBigO.of_bound (Real.exp (Real.pi * c) * B) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc ‖shiftTheta M x y t - shiftConst M x‖
      ≤ Real.exp (-(Real.pi * c) * (t - 1)) * B := norm_shiftTheta_sub_le M x y hc ht
    _ = Real.exp (Real.pi * c) * B * Real.exp (-(Real.pi * c) * t) := by
        rw [mul_comm (Real.exp (Real.pi * c)), mul_assoc, ← Real.exp_add]
        ring_nf

end Theta

section Poisson

variable [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of a function twisted by an additive character is a translate: $\mathcal{F}\big(g(v) e^{2 \pi i \langle v, y \rangle}\big)(w) = \mathcal{F} g(w - y)$. -/
theorem fourier_mul_cexp_inner (g : V → ℂ) (y w : V) :
    𝓕 (fun v => g v * cexp (2 * Real.pi * I * ⟪v, y⟫)) w = 𝓕 g (w - y) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  congr 1 with v
  simp only [smul_eq_mul, inner_sub_right]
  rw [mul_comm (g v), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

variable (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M]

/-- **The transformation formula of the shifted and twisted theta function.** For $t > 0$ and $x, y \in V$, $$\theta_M(x, y; t) = \frac{e^{2 \pi i \langle x, y \rangle}}{\mathrm{covol}(M) \, t^{n/2}} \, \theta_{M^\vee}(-y, x; 1/t).$$ -/
theorem shiftTheta_eq {t : ℝ} (ht : 0 < t) (x y : V) :
    shiftTheta M x y t =
      ((ZLattice.covolume M)⁻¹ * (t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ : ℝ) *
        cexp (2 * Real.pi * I * ⟪x, y⟫) * shiftTheta (dualLattice M) (-y) x (1 / t) := by
  set g : V → ℂ := fun v => (Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) : ℂ)
  set f : V → ℂ := fun v => g v * cexp (2 * Real.pi * I * ⟪v, y⟫)
  have hc : Continuous f := by fun_prop
  have hN : finrank ℝ V < finrank ℝ V + 1 := Nat.lt_succ_self _
  have hd : HasDecay f (finrank ℝ V + 1) := by
    obtain ⟨C, hC⟩ := hasDecay_gaussian (E := V) (mul_pos Real.pi_pos ht) (finrank ℝ V + 1)
    refine ⟨C, fun v => ?_⟩
    have := hC v
    simp only [f, g, norm_mul, norm_cexp_two_pi_I_mul, mul_one]
    exact this
  have hFf : ∀ w, 𝓕 f w = ((t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ : ℝ) *
      (Real.exp (-(Real.pi * (1 / t)) * ‖-y + w‖ ^ 2) : ℂ) := fun w => by
    rw [fourier_mul_cexp_inner, fourier_gaussian ht, sub_eq_neg_add, one_div, ← div_eq_mul_inv]
  have hF : Summable fun μ : dualLattice M => 𝓕 f μ := by
    simp only [hFf]
    refine (Complex.summable_ofReal.2 (summable_exp_neg_mul_norm_add_sq (dualLattice M)
      (mul_pos Real.pi_pos (one_div_pos.2 ht)) (-y))).mul_left _
  have key := tsum_add_zlattice_eq_of_hasDecay M hc hd hN hF x
  rw [shiftTheta, shiftTheta]
  rw [key]
  simp only [hFf]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun (μ : dualLattice M) => ?_
  have hinner : ⟪x, (μ : V)⟫ = ⟪x, y⟫ + ⟪-y + μ, x⟫ := by
    rw [inner_add_left, inner_neg_left, real_inner_comm x y, real_inner_comm x μ]
    ring
  rw [hinner]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

end Poisson

section Pair

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
variable (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M]

/-- The pair $(\theta_M(x, y; \cdot), \theta_{M^\vee}(-y, x; \cdot))$ as a `WeakFEPair`, with weight $n/2$, root number $\mathrm{covol}(M)^{-1} e^{2 \pi i \langle x, y \rangle}$ and constant terms $c_M(x)$ and $c_{M^\vee}(-y)$. -/
noncomputable def shiftThetaFEPair (x y : V) : WeakFEPair ℂ where
  f := shiftTheta M x y
  g := shiftTheta (dualLattice M) (-y) x
  k := finrank ℝ V / 2
  ε := ((ZLattice.covolume M)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫)
  f₀ := shiftConst M x
  g₀ := shiftConst (dualLattice M) (-y)
  hf_int := locallyIntegrableOn_shiftTheta M x y
  hg_int := locallyIntegrableOn_shiftTheta (dualLattice M) (-y) x
  hk := by have := finrank_pos (R := ℝ) (M := V); positivity
  hε := mul_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (ZLattice.covolume_pos M).ne'))
    (Complex.exp_ne_zero _)
  h_feq t ht := by
    have ht' : (0 : ℝ) < 1 / t := one_div_pos.2 ht
    rw [shiftTheta_eq M ht' x y, one_div_one_div, smul_eq_mul, one_div,
      Real.inv_rpow (le_of_lt ht), inv_inv]
    push_cast
    ring
  hf_top := isBigO_shiftTheta_sub M x y
  hg_top := isBigO_shiftTheta_sub (dualLattice M) (-y) x

end Pair

section Zeta

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
variable (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M]

/-- The shifted and twisted Epstein zeta function $$Z_M(x, y; s) = \sum_{\mu \in M, \, x + \mu \neq 0} e^{2 \pi i \langle x + \mu, y \rangle} \, |x + \mu|^{-s}.$$ The series converges for $\mathrm{Re}\, s > n$. -/
noncomputable def shiftEpsteinZeta (x y : V) (s : ℂ) : ℂ :=
  ∑' μ : M, if x + (μ : V) = 0 then 0 else
    cexp (2 * Real.pi * I * ⟪x + μ, y⟫) * ((‖x + (μ : V)‖ : ℝ) : ℂ) ^ (-s)

/-- The completed shifted and twisted Epstein zeta function $\Lambda_M(x, y; s)$. It is the function $\Lambda$ of `Langlands.Tate.shiftThetaFEPair` at $s/2$, and it equals $\Gamma_\mathbb{R}(s) Z_M(x, y; s)$ for $\mathrm{Re}\, s > n$. -/
noncomputable def completedShiftEpsteinZeta (x y : V) (s : ℂ) : ℂ :=
  (shiftThetaFEPair M x y).Λ (s / 2)

/-- The Dirichlet series of the completed shifted Epstein zeta function: for $\mathrm{Re}\, s > n$, $$\Lambda_M(x, y; s) = \sum_{x + \mu \neq 0} \Gamma_\mathbb{R}(s) \, e^{2 \pi i \langle x + \mu, y \rangle} \, |x + \mu|^{-s}.$$ -/
theorem hasSum_completedShiftEpsteinZeta (x y : V) {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    HasSum (fun μ : M => if x + (μ : V) = 0 then 0 else Complex.Gammaℝ s *
      (cexp (2 * Real.pi * I * ⟪x + μ, y⟫) * ((‖x + (μ : V)‖ : ℝ) : ℂ) ^ (-s)))
      (completedShiftEpsteinZeta M x y s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  have hk : (shiftThetaFEPair M x y).k < (s / 2).re := by
    simp only [shiftThetaFEPair, Complex.div_ofNat_re]
    linarith
  have hM : mellin (fun t => shiftTheta M x y t - shiftConst M x) (s / 2) =
      (shiftThetaFEPair M x y).Λ (s / 2) :=
    ((shiftThetaFEPair M x y).hasMellin hk).2
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun μ : M => if ‖x + (μ : V)‖ = 0 then 0 else
      cexp (2 * Real.pi * I * ⟪x + μ, y⟫) * (Real.exp (-Real.pi * ‖x + (μ : V)‖ ^ 2 * t) : ℂ))
      (shiftTheta M x y t - shiftConst M x) := by
    intro t ht
    convert hasSum_shiftTheta_sub M x y ht using 2 with μ
    simp only [norm_eq_zero]
    split_ifs
    · rfl
    · rw [mul_comm]
      congr 3
      ring
  have hsum : Summable fun μ : M =>
      ‖cexp (2 * Real.pi * I * ⟪x + μ, y⟫)‖ / |‖x + (μ : V)‖| ^ s.re := by
    have := ZLattice.summable_norm_sub_rpow M (-s.re) (by rw [ZLattice.rank ℝ M]; linarith) (-x)
    refine this.congr fun μ => ?_
    rw [norm_cexp_two_pi_I_mul, abs_norm, Real.rpow_neg (norm_nonneg _), one_div, sub_neg_eq_add,
      add_comm]
  have := hasSum_mellin_pi_mul_sq hs0 hF hsum
  rw [hM] at this
  unfold completedShiftEpsteinZeta
  convert this using 2 with μ
  split_ifs with hμ
  · simp [hμ, Complex.zero_cpow (Complex.ne_zero_of_re_pos hs0)]
  · rw [abs_norm, div_eq_mul_inv, Complex.cpow_neg, mul_assoc]
    ring

/-- For $\mathrm{Re}\, s > n$, $\Lambda_M(x, y; s) = \Gamma_\mathbb{R}(s) Z_M(x, y; s)$. -/
theorem completedShiftEpsteinZeta_eq (x y : V) {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    completedShiftEpsteinZeta M x y s = Complex.Gammaℝ s * shiftEpsteinZeta M x y s := by
  rw [shiftEpsteinZeta, ← tsum_mul_left,
    (hasSum_completedShiftEpsteinZeta M x y hs).tsum_eq.symm]
  refine tsum_congr fun μ => ?_
  split_ifs <;> simp

/-- The series of $Z_M(x, y; s)$ converges absolutely for $\mathrm{Re}\, s > n$. -/
theorem summable_shiftEpsteinZeta (x y : V) {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    Summable fun μ : M => if x + (μ : V) = 0 then 0 else
      cexp (2 * Real.pi * I * ⟪x + μ, y⟫) * ((‖x + (μ : V)‖ : ℝ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have := ((hasSum_completedShiftEpsteinZeta M x y hs).summable).mul_left (Complex.Gammaℝ s)⁻¹
  refine this.congr fun μ => ?_
  split_ifs <;> simp [hG]

/-- The completed shifted Epstein zeta function is holomorphic on $\mathbb{C} \setminus \{0, n\}$. -/
theorem differentiableAt_completedShiftEpsteinZeta (x y : V) {s : ℂ}
    (hs : s ≠ 0 ∨ x ∉ M) (hs' : s ≠ finrank ℝ V ∨ y ∉ dualLattice M) :
    DifferentiableAt ℂ (completedShiftEpsteinZeta M x y) s := by
  have h1 : s / 2 ≠ 0 ∨ (shiftThetaFEPair M x y).f₀ = 0 := by
    rcases hs with hs | hs
    · exact Or.inl (div_ne_zero hs two_ne_zero)
    · exact Or.inr (by simp [shiftThetaFEPair, shiftConst, hs])
  have h2 : s / 2 ≠ ((shiftThetaFEPair M x y).k : ℂ) ∨ (shiftThetaFEPair M x y).g₀ = 0 := by
    rcases hs' with hs' | hs'
    · refine Or.inl ?_
      simp only [shiftThetaFEPair]
      push_cast
      intro h
      exact hs' (by linear_combination 2 * h)
    · exact Or.inr (by simp [shiftThetaFEPair, shiftConst, neg_mem_iff, hs'])
  exact ((shiftThetaFEPair M x y).differentiableAt_Λ h1 h2).comp s
    (differentiableAt_id.div_const 2)

/-- If $x \notin M$ and $y \notin M^\vee$, then $\Lambda_M(x, y; s)$ is an entire function. -/
theorem differentiable_completedShiftEpsteinZeta {x y : V} (hx : x ∉ M)
    (hy : y ∉ dualLattice M) : Differentiable ℂ (completedShiftEpsteinZeta M x y) := fun _ =>
  differentiableAt_completedShiftEpsteinZeta M x y (Or.inr hx) (Or.inr hy)

/-- The symmetric pair of `Langlands.Tate.shiftThetaFEPair` for $(M, x, y)$ has the same function $\Lambda$ as the pair for $(M^\vee, -y, x)$. -/
theorem shiftThetaFEPair_symm_Λ (x y : V) :
    (shiftThetaFEPair M x y).symm.Λ = (shiftThetaFEPair (dualLattice M) (-y) x).Λ := by
  refine weakFEPair_Λ_eq _ _ rfl rfl ?_ rfl ?_
  · simp only [WeakFEPair.symm, shiftThetaFEPair, covolume_dualLattice, inv_inv, mul_inv,
      ← Complex.exp_neg, inner_neg_left, real_inner_comm x y]
    push_cast
    ring_nf
    rw [inv_inv]
  · simp only [WeakFEPair.symm, shiftThetaFEPair, dualLattice_dualLattice, shiftConst,
      neg_mem_iff]

/-- **The functional equation of the shifted and twisted Epstein zeta function.** $$\Lambda_M(x, y; n - s) = \mathrm{covol}(M)^{-1} \, e^{2 \pi i \langle x, y \rangle} \, \Lambda_{M^\vee}(-y, x; s).$$ -/
theorem completedShiftEpsteinZeta_sub (x y : V) (s : ℂ) :
    completedShiftEpsteinZeta M x y (finrank ℝ V - s) =
      ((ZLattice.covolume M)⁻¹ : ℝ) * cexp (2 * Real.pi * I * ⟪x, y⟫) *
        completedShiftEpsteinZeta (dualLattice M) (-y) x s := by
  have h := (shiftThetaFEPair M x y).functional_equation (s / 2)
  rw [shiftThetaFEPair_symm_Λ] at h
  unfold completedShiftEpsteinZeta
  have hk : ((finrank ℝ V : ℂ) - s) / 2 = ((shiftThetaFEPair M x y).k : ℂ) - s / 2 := by
    simp only [shiftThetaFEPair]
    push_cast
    ring
  rw [hk, h, smul_eq_mul]
  rfl

end Zeta

section Congruence

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The ideal character is periodic modulo the conductor.** Let $\chi$ be of ray class type with conductor $\mathfrak{f} = \prod_v \mathfrak{p}_v^{a_v}$. If $x, y \in K^\times$ satisfy $v(y - x) \geq a_v + v(x)$ at each ramified place $v$, then $\chi((y)) = \chi((x))$. -/
theorem IsRayClassType.idealChar_toPrincipalIdeal_eq (hχ : IsRayClassType χ) (x y : Kˣ)
    (h : ∀ v ∈ ramifiedSet χ, v.valuation K ((y : K) - x) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ)) * v.valuation K (x : K)) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K y) = idealChar χ (toPrincipalIdeal (𝓞 K) K x) := by
  have key := hχ.idealChar_toPrincipalIdeal (y * x⁻¹) fun v hv => by
    have hx0 : v.valuation K (x : K) ≠ 0 := by simp
    rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, valued_algebraMap,
      Units.val_mul, show (y : K) * ((x⁻¹ : Kˣ) : K) - 1 = ((y : K) - x) * (x : K)⁻¹ by
        rw [Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ x.ne_zero], map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hx0)).2 (h v hv)
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at key
  exact key

end Congruence

end Langlands.Tate
