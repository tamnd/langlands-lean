/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.DedekindTheta
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The Epstein zeta function of a lattice

Let $V$ be a real inner product space of dimension $n \ge 1$ and let $L \subset V$ be a full lattice. The Epstein zeta function of $L$ is $$Z_L(s) = \sum_{\ell \in L, \, \ell \neq 0} |\ell|^{-s}.$$ The series converges for $\mathrm{Re}\, s > n$. This file proves that the completed function $\Lambda_L(s) = \Gamma_\mathbb{R}(s) Z_L(s)$, with $\Gamma_\mathbb{R}(s) = \pi^{-s/2} \Gamma(s/2)$, has a meromorphic continuation to $\mathbb{C}$ with poles at most at $s = 0$ and $s = n$, and that it satisfies the functional equation $$\Lambda_L(n - s) = \mathrm{covol}(L)^{-1} \, \Lambda_{L^\vee}(s),$$ where $L^\vee$ is the dual lattice. For $V = \mathbb{R}$ and $L = \mathbb{Z}$ the function $Z_L$ is $2 \zeta(s)$, and the result is Riemann's functional equation.

## Main results

* `Langlands.Tate.completedEpsteinZeta_eq`: $\Lambda_L(s) = \Gamma_\mathbb{R}(s) Z_L(s)$ for $\mathrm{Re}\, s > n$.
* `Langlands.Tate.differentiableAt_completedEpsteinZeta`: $\Lambda_L$ is holomorphic outside $\{0, n\}$.
* `Langlands.Tate.completedEpsteinZeta_sub`: the functional equation above.
* `Langlands.Tate.completedEpsteinZeta_residue`: $(s - n) \Lambda_L(s) \to 2 \, \mathrm{covol}(L)^{-1}$ as $s \to n$.
* `Langlands.Tate.dualLattice_dualLattice` and `Langlands.Tate.covolume_dualLattice`: $L^{\vee\vee} = L$ and $\mathrm{covol}(L^\vee) = \mathrm{covol}(L)^{-1}$.

## Proof

This is Riemann's second proof of the functional equation, in dimension $n$. Let $\theta_L(t) = \sum_{\ell \in L} e^{-\pi t |\ell|^2}$ for $t > 0$. Then:

1. $\theta_L$ is continuous on $(0, \infty)$, by uniform convergence on each half line $[\delta, \infty)$.
2. $\theta_L(t) - 1 = O(e^{-\pi c t})$ as $t \to \infty$, where $c > 0$ is a lower bound for $|\ell|^2$ on $L \setminus \{0\}$. Such a bound exists because $L$ is discrete.
3. $\theta_L(1/t) = \mathrm{covol}(L)^{-1} \, t^{n/2} \, \theta_{L^\vee}(t)$. This is `Langlands.Tate.tsum_zlattice_gaussian`.

So $(\theta_L, \theta_{L^\vee})$ is a pair of functions with the hypotheses of `WeakFEPair` in Mathlib, with weight $k = n/2$, root number $\mathrm{covol}(L)^{-1}$ and constant terms $1$. The function $\Lambda_L(s)$ is the function $\Lambda$ of this pair at $s/2$. Its Mellin transform is computed term by term with `hasSum_mellin_pi_mul_sq`, and this gives $\Lambda_L(s) = \Gamma_\mathbb{R}(s) Z_L(s)$. The summability of $\sum |\ell|^{-\sigma}$ for $\sigma > n$ is `ZLattice.summable_norm_rpow`.

The functional equation of the pair relates $\theta_L$ to the symmetric pair $(\theta_{L^\vee}, \theta_L)$. This is the pair of $L^\vee$, because $L^{\vee\vee} = L$ and $\mathrm{covol}(L^\vee) = \mathrm{covol}(L)^{-1}$. The second identity follows from step 3 applied twice at $t = 1$.

## References

* P. Epstein, Zur Theorie allgemeiner Zetafunctionen, Math. Ann. 56 (1903).
* J. Neukirch, Algebraic number theory, chapter VII, section 1.
* A. Terras, Harmonic analysis on symmetric spaces and applications II, section 1.4.
-/

open MeasureTheory Module Filter Topology Asymptotics Set
open scoped RealInnerProductSpace Classical

namespace Langlands.Tate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Dual

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

omit [FiniteDimensional ℝ V] in
variable (V) in
/-- The inner product of $V$ is a nondegenerate bilinear form. -/
theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simpa using hx x
  · simpa using hy y

/-- The dual lattice is the $\mathbb{Z}$-span of the dual basis of a real basis of $L$. -/
theorem dualLattice_eq_span [DecidableEq (Free.ChooseBasisIndex ℤ L)] :
    dualLattice L = Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ V)
      (innerₗ_nondegenerate V) ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ V)
    (innerₗ_nondegenerate V) ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  rwa [Basis.ofZLatticeBasis_span] at h

instance : DiscreteTopology (dualLattice L) := by
  classical
  rw [dualLattice_eq_span L]
  infer_instance

instance : IsZLattice ℝ (dualLattice L) where
  span_top := by
    rw [dualLattice_eq_span L]
    exact ZSpan.span_top _

/-- The dual of the dual lattice is the lattice: $L^{\vee\vee} = L$. -/
theorem dualLattice_dualLattice : dualLattice (dualLattice L) = L := by
  classical
  have h := LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (R := ℤ) (innerₗ V)
    (innerₗ_nondegenerate V) ⟨fun x y => by simp [real_inner_comm]⟩
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  rwa [Basis.ofZLatticeBasis_span] at h

end Dual

section Theta

variable (M : Submodule ℤ V)

/-- The theta function $\theta_M(t) = \sum_{\mu \in M} e^{-\pi t |\mu|^2}$ of a lattice $M$. It is meaningful for $t > 0$. -/
noncomputable def latticeTheta (t : ℝ) : ℝ :=
  ∑' μ : M, Real.exp (-(Real.pi * t) * ‖(μ : V)‖ ^ 2)

variable [DiscreteTopology M] [IsZLattice ℝ M]

/-- The series of $\theta_M(t)$ converges for $t > 0$. -/
theorem summable_latticeTheta {t : ℝ} (ht : 0 < t) :
    Summable fun μ : M => Real.exp (-(Real.pi * t) * ‖(μ : V)‖ ^ 2) := by
  have := summable_zlattice_of_hasDecay M
    (hasDecay_gaussian (E := V) (mul_pos Real.pi_pos ht) _)
    (Nat.lt_succ_self (finrank ℝ V))
  exact Complex.summable_ofReal.1 this

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [IsZLattice ℝ M] in
/-- A lattice is discrete: there is $c > 0$ with $c \le |\mu|^2$ for each nonzero $\mu \in M$. -/
theorem exists_pos_le_norm_sq : ∃ c : ℝ, 0 < c ∧ ∀ μ : M, μ ≠ 0 → c ≤ ‖(μ : V)‖ ^ 2 := by
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set M))
  refine ⟨ε ^ 2, by positivity, fun μ hμ => ?_⟩
  have : ε ≤ ‖(μ : V)‖ := by
    by_contra hlt
    exact hμ (h μ (by rwa [dist_zero_right, ← not_le]))
  exact pow_le_pow_left₀ hε.le this 2

/-- The theta series without its constant term: $\sum_{\mu \neq 0} e^{-\pi t |\mu|^2} = \theta_M(t) - 1$. -/
theorem hasSum_latticeTheta_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun μ : M => if μ = 0 then 0 else Real.exp (-(Real.pi * t) * ‖(μ : V)‖ ^ 2))
      (latticeTheta M t - 1) := by
  have := hasSum_ite_sub_hasSum (summable_latticeTheta M ht).hasSum 0
  simpa [latticeTheta] using this

/-- The theta function is continuous on $(0, \infty)$. -/
theorem continuousOn_latticeTheta : ContinuousOn (latticeTheta M) (Ioi 0) := by
  intro x hx
  have hδ : (0 : ℝ) < x / 2 := half_pos hx
  have hc : ContinuousOn (latticeTheta M) (Ioi (x / 2)) := by
    refine continuousOn_tsum (fun μ => by fun_prop) (summable_latticeTheta M hδ) ?_
    intro μ t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ?_
    have h1 : x / 2 ≤ t := le_of_lt ht
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg ‖(μ : V)‖)) (sub_nonneg.2 h1)]
  exact (hc.continuousAt (Ioi_mem_nhds (half_lt_self hx))).continuousWithinAt

/-- The theta function minus its constant term decays exponentially: for $c$ as in `Langlands.Tate.exists_pos_le_norm_sq` and $t \ge 1$, $$0 \le \theta_M(t) - 1 \le e^{-\pi c (t - 1)} \, (\theta_M(1) - 1).$$ -/
theorem latticeTheta_sub_one_le {c : ℝ} (hc : ∀ μ : M, μ ≠ 0 → c ≤ ‖(μ : V)‖ ^ 2) {t : ℝ}
    (ht : 1 ≤ t) :
    0 ≤ latticeTheta M t - 1 ∧
      latticeTheta M t - 1 ≤ Real.exp (-(Real.pi * c) * (t - 1)) * (latticeTheta M 1 - 1) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1 := hasSum_latticeTheta_sub_one M ht0
  have h2 := (hasSum_latticeTheta_sub_one M one_pos).mul_left (Real.exp (-(Real.pi * c) * (t - 1)))
  refine ⟨h1.nonneg fun μ => ?_, hasSum_le (fun μ => ?_) h1 h2⟩
  · split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  · split_ifs with hμ
    · simp
    · rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 ht)) (sub_nonneg.2 (hc μ hμ))]

/-- The theta function minus its constant term is $O(t^r)$ at infinity for each $r$. -/
theorem isBigO_latticeTheta_sub_one (r : ℝ) :
    (fun t => (latticeTheta M t : ℂ) - 1) =O[atTop] (· ^ r) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_sq M
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop (mul_pos Real.pi_pos hc0) r).isBigO
  refine IsBigO.trans ?_ hexp
  refine IsBigO.of_bound (Real.exp (Real.pi * c) * (latticeTheta M 1 - 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  obtain ⟨h0, hle⟩ := latticeTheta_sub_one_le M hc ht
  have : ((latticeTheta M t : ℂ) - 1) = ((latticeTheta M t - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc latticeTheta M t - 1
      ≤ Real.exp (-(Real.pi * c) * (t - 1)) * (latticeTheta M 1 - 1) := hle
    _ = Real.exp (Real.pi * c) * (latticeTheta M 1 - 1) * Real.exp (-(Real.pi * c) * t) := by
        rw [mul_comm (Real.exp (Real.pi * c)), mul_assoc, ← Real.exp_add]
        ring_nf

/-- The theta function is locally integrable on $(0, \infty)$. -/
theorem locallyIntegrableOn_latticeTheta :
    LocallyIntegrableOn (fun t => (latticeTheta M t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_latticeTheta M)).locallyIntegrableOn
    measurableSet_Ioi

end Theta

variable [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The theta transformation formula in the form $\theta_L(1/x) = \mathrm{covol}(L)^{-1} \, x^{n/2} \, \theta_{L^\vee}(x)$ for $x > 0$. -/
theorem latticeTheta_one_div {x : ℝ} (hx : 0 < x) :
    latticeTheta L (1 / x) =
      (ZLattice.covolume L)⁻¹ * x ^ ((finrank ℝ V : ℝ) / 2) * latticeTheta (dualLattice L) x := by
  have h := tsum_zlattice_gaussian L (one_div_pos.2 hx)
  rw [one_div, Real.inv_rpow hx.le, inv_inv, div_inv_eq_mul] at h
  rw [latticeTheta, one_div, h, latticeTheta]

/-- The covolume of the dual lattice: $\mathrm{covol}(L^\vee) = \mathrm{covol}(L)^{-1}$. -/
theorem covolume_dualLattice : ZLattice.covolume (dualLattice L) = (ZLattice.covolume L)⁻¹ := by
  have h1 := latticeTheta_one_div L one_pos
  have h2 := latticeTheta_one_div (dualLattice L) one_pos
  rw [dualLattice_dualLattice] at h2
  simp only [div_one, Real.one_rpow, mul_one] at h1 h2
  have hpos : 0 < latticeTheta L 1 :=
    (summable_latticeTheta L one_pos).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  have hL := ZLattice.covolume_pos L
  have hL' := ZLattice.covolume_pos (dualLattice L)
  rw [h2, ← mul_assoc] at h1
  have : (ZLattice.covolume L)⁻¹ * (ZLattice.covolume (dualLattice L))⁻¹ = 1 := by
    have := mul_right_cancel₀ hpos.ne' (h1.symm.trans (one_mul _).symm)
    exact this
  field_simp at this
  exact eq_inv_of_mul_eq_one_left (by linear_combination this.symm)

variable [Nontrivial V]

/-- The pair $(\theta_L, \theta_{L^\vee})$ as a `WeakFEPair`, with weight $n/2$, root number $\mathrm{covol}(L)^{-1}$ and constant terms $1$. -/
noncomputable def thetaFEPair : WeakFEPair ℂ where
  f t := (latticeTheta L t : ℂ)
  g t := (latticeTheta (dualLattice L) t : ℂ)
  k := finrank ℝ V / 2
  ε := ((ZLattice.covolume L)⁻¹ : ℝ)
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_latticeTheta L
  hg_int := locallyIntegrableOn_latticeTheta (dualLattice L)
  hk := by have := finrank_pos (R := ℝ) (M := V); positivity
  hε := Complex.ofReal_ne_zero.2 (inv_ne_zero (ZLattice.covolume_pos L).ne')
  h_feq x hx := by
    rw [latticeTheta_one_div L hx, smul_eq_mul]
    push_cast
    ring
  hf_top := isBigO_latticeTheta_sub_one L
  hg_top := isBigO_latticeTheta_sub_one (dualLattice L)

/-- The symmetric pair of `Langlands.Tate.thetaFEPair` for $L$ is the pair for $L^\vee$. -/
theorem thetaFEPair_symm : (thetaFEPair L).symm = thetaFEPair (dualLattice L) := by
  have h : (fun t => (latticeTheta L t : ℂ)) =
      fun t => (latticeTheta (dualLattice (dualLattice L)) t : ℂ) := by
    rw [dualLattice_dualLattice]
  simp only [WeakFEPair.symm, thetaFEPair, covolume_dualLattice, inv_inv, Complex.ofReal_inv]
  congr 1

/-- The Epstein zeta function $Z_L(s) = \sum_{\ell \in L, \, \ell \neq 0} |\ell|^{-s}$ of a lattice $L$. The series converges for $\mathrm{Re}\, s > n$. -/
noncomputable def epsteinZeta (s : ℂ) : ℂ :=
  ∑' ℓ : L, if ℓ = 0 then 0 else ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s)

/-- The completed Epstein zeta function $\Lambda_L(s)$. It is the function $\Lambda$ of `Langlands.Tate.thetaFEPair` at $s/2$, and it equals $\Gamma_\mathbb{R}(s) Z_L(s)$ for $\mathrm{Re}\, s > n$. -/
noncomputable def completedEpsteinZeta (s : ℂ) : ℂ :=
  (thetaFEPair L).Λ (s / 2)

/-- The Dirichlet series of the completed Epstein zeta function: for $\mathrm{Re}\, s > n$, $$\Lambda_L(s) = \sum_{\ell \neq 0} \Gamma_\mathbb{R}(s) \, |\ell|^{-s}.$$ -/
theorem hasSum_completedEpsteinZeta {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    HasSum (fun ℓ : L => if ℓ = 0 then 0 else Complex.Gammaℝ s * ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s))
      (completedEpsteinZeta L s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  have hk : (thetaFEPair L).k < (s / 2).re := by
    simp only [thetaFEPair, Complex.div_ofNat_re]
    linarith
  have hM : mellin (fun t => (latticeTheta L t : ℂ) - 1) (s / 2) = (thetaFEPair L).Λ (s / 2) :=
    ((thetaFEPair L).hasMellin hk).2
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun ℓ : L => if ‖(ℓ : V)‖ = 0 then 0 else
      (1 : ℂ) * (Real.exp (-Real.pi * ‖(ℓ : V)‖ ^ 2 * t) : ℂ)) ((latticeTheta L t : ℂ) - 1) := by
    intro t ht
    have := Complex.hasSum_ofReal.2 (hasSum_latticeTheta_sub_one L ht)
    push_cast at this
    convert this using 2 with ℓ
    simp only [norm_eq_zero, ZeroMemClass.coe_eq_zero, one_mul]
    split_ifs
    · rfl
    · congr 2
      ring
  have hsum : Summable fun ℓ : L => ‖(1 : ℂ)‖ / |‖(ℓ : V)‖| ^ s.re := by
    have := ZLattice.summable_norm_rpow L (-s.re) (by rw [ZLattice.rank ℝ L]; linarith)
    refine this.congr fun ℓ => ?_
    rw [norm_one, abs_norm, Real.rpow_neg (norm_nonneg _), one_div]
    rfl
  have := hasSum_mellin_pi_mul_sq hs0 hF hsum
  rw [hM] at this
  unfold completedEpsteinZeta
  convert this using 2 with ℓ
  split_ifs with hℓ
  · simp [hℓ, Complex.zero_cpow (Complex.ne_zero_of_re_pos hs0)]
  · rw [abs_norm, mul_one, div_eq_mul_inv, Complex.cpow_neg]

/-- For $\mathrm{Re}\, s > n$, $\Lambda_L(s) = \Gamma_\mathbb{R}(s) Z_L(s)$. -/
theorem completedEpsteinZeta_eq {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    completedEpsteinZeta L s = Complex.Gammaℝ s * epsteinZeta L s := by
  rw [epsteinZeta, ← tsum_mul_left, (hasSum_completedEpsteinZeta L hs).tsum_eq.symm]
  refine tsum_congr fun ℓ => ?_
  split_ifs <;> simp

/-- The series of $Z_L(s)$ converges for $\mathrm{Re}\, s > n$. -/
theorem summable_epsteinZeta {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    Summable fun ℓ : L => if ℓ = 0 then 0 else ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have := ((hasSum_completedEpsteinZeta L hs).summable).mul_left (Complex.Gammaℝ s)⁻¹
  refine this.congr fun ℓ => ?_
  split_ifs <;> simp [hG]

/-- The completed Epstein zeta function is holomorphic on $\mathbb{C} \setminus \{0, n\}$. -/
theorem differentiableAt_completedEpsteinZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ finrank ℝ V) :
    DifferentiableAt ℂ (completedEpsteinZeta L) s := by
  have h1 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  have h2 : s / 2 ≠ ((thetaFEPair L).k : ℂ) := by
    simp only [thetaFEPair]
    push_cast
    intro h
    exact hs' (by linear_combination 2 * h)
  exact ((thetaFEPair L).differentiableAt_Λ (Or.inl h1) (Or.inl h2)).comp s
    (differentiableAt_id.div_const 2)

/-- **The functional equation of the Epstein zeta function.** $$\Lambda_L(n - s) = \mathrm{covol}(L)^{-1} \, \Lambda_{L^\vee}(s).$$ -/
theorem completedEpsteinZeta_sub (s : ℂ) :
    completedEpsteinZeta L (finrank ℝ V - s) =
      ((ZLattice.covolume L)⁻¹ : ℝ) * completedEpsteinZeta (dualLattice L) s := by
  have h := (thetaFEPair L).functional_equation (s / 2)
  rw [thetaFEPair_symm] at h
  unfold completedEpsteinZeta
  have hk : ((finrank ℝ V : ℂ) - s) / 2 = ((thetaFEPair L).k : ℂ) - s / 2 := by
    simp only [thetaFEPair]
    push_cast
    ring
  rw [hk, h, smul_eq_mul]
  rfl

/-- The residue at $s = n$: $(s - n) \Lambda_L(s) \to 2 \, \mathrm{covol}(L)^{-1}$ as $s \to n$. -/
theorem completedEpsteinZeta_residue :
    Tendsto (fun s : ℂ => (s - finrank ℝ V) * completedEpsteinZeta L s)
      (𝓝[≠] (finrank ℝ V : ℂ)) (𝓝 (2 * ((ZLattice.covolume L)⁻¹ : ℝ))) := by
  have h := (thetaFEPair L).Λ_residue_k
  have hk : ((thetaFEPair L).k : ℂ) = (finrank ℝ V : ℂ) / 2 := by
    simp only [thetaFEPair]
    push_cast
    ring
  have hc : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (finrank ℝ V : ℂ))
      (𝓝[≠] ((thetaFEPair L).k : ℂ)) := by
    rw [hk]
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.div_const 2).tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h'
      exact hs (Set.mem_singleton_iff.2 (by linear_combination 2 * Set.mem_singleton_iff.1 h'))
  have := (h.comp hc).const_mul 2
  simp only [thetaFEPair, smul_eq_mul, mul_one] at this
  refine this.congr fun s => ?_
  simp only [Function.comp_apply, completedEpsteinZeta, thetaFEPair]
  push_cast
  ring

end Langlands.Tate
