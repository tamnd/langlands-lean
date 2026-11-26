/-
Copyright (c) 2026 Duc-Tam Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.IdealZeta
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The class zeta function of an imaginary quadratic field

Let $K$ be an imaginary quadratic field. Then $K$ has one infinite place $w$, with $n_w = 2$, and $\sum_w n_w |\alpha|_w^2 = 2 |N(\alpha)|$. So the trace form zeta function $\Lambda_{\mathfrak{a}}$ of `Langlands.Tate.completedIdealZeta` is a sum over the norms of the elements of $\mathfrak{a}$.

This file proves three results.

* `Langlands.Tate.completedIdealZeta_eq_of_isQuadratic`: the Dirichlet series of $\Lambda_{\mathfrak{a}}$ in terms of $|N(\alpha)|$.
* `Langlands.Tate.classTerm_spanSingleton_mul`: the function $\psi_{\mathfrak{a}}(s) = (N(\mathfrak{a}) \sqrt{|d_K|})^{s/2} \Lambda_{\mathfrak{a}}(s)$ depends only on the ideal class of $\mathfrak{a}$. The proof uses the identity theorem.
* `Langlands.Tate.classZeta_two_sub`: the sum $\Lambda_K(s) = \sum_C \psi_{\mathfrak{a}_C}(s)$ over the ideal classes satisfies $\Lambda_K(2 - s) = \Lambda_K(s)$ for $s \neq 0, 2$.

The identification of $\Lambda_K$ with the completed Dedekind zeta function is a later step.
-/

open Module Filter Topology NumberField NumberField.InfinitePlace

open scoped nonZeroDivisors Classical

namespace Langlands.Tate

section Identity

/-- The identity theorem in the form that this file uses. Two functions that are holomorphic on $\mathbb{C} \setminus \{p, q\}$ and agree on a right half plane agree on $\mathbb{C} \setminus \{p, q\}$. -/
theorem eq_of_eq_of_lt_re {f g : ℂ → ℂ} {p q : ℂ} {r : ℝ}
    (hf : ∀ s, s ≠ p → s ≠ q → DifferentiableAt ℂ f s)
    (hg : ∀ s, s ≠ p → s ≠ q → DifferentiableAt ℂ g s) (hfg : ∀ s : ℂ, r < s.re → f s = g s)
    {s : ℂ} (hp : s ≠ p) (hq : s ≠ q) : f s = g s := by
  set U : Set ℂ := {p, q}ᶜ with hU
  have hUo : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank
      (by simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
      ((Set.countable_singleton q).insert p)).isPreconnected
  have hmem : ∀ z, z ≠ p → z ≠ q → z ∈ U := fun z hp hq => by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hp, hq⟩
  have hmem' : ∀ z ∈ U, z ≠ p ∧ z ≠ q := fun z hz => by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact hz
  have hfa : AnalyticOnNhd ℂ f U := DifferentiableOn.analyticOnNhd
    (fun z hz => (hf z (hmem' z hz).1 (hmem' z hz).2).differentiableWithinAt) hUo
  have hga : AnalyticOnNhd ℂ g U := DifferentiableOn.analyticOnNhd
    (fun z hz => (hg z (hmem' z hz).1 (hmem' z hz).2).differentiableWithinAt) hUo
  set M : ℝ := max r (max ‖p‖ ‖q‖) with hM
  set z₀ : ℂ := ((M + 1 : ℝ) : ℂ) with hz₀
  have hre : z₀.re = M + 1 := Complex.ofReal_re _
  have hz₀p : z₀ ≠ p := by
    intro h
    have h1 : p.re ≤ ‖p‖ := Complex.re_le_norm p
    have h2 : ‖p‖ ≤ M := le_max_of_le_right (le_max_left _ _)
    have h3 : p.re = M + 1 := by rw [← h, hre]
    linarith
  have hz₀q : z₀ ≠ q := by
    intro h
    have h1 : q.re ≤ ‖q‖ := Complex.re_le_norm q
    have h2 : ‖q‖ ≤ M := le_max_of_le_right (le_max_right _ _)
    have h3 : q.re = M + 1 := by rw [← h, hre]
    linarith
  have hlt : r < z₀.re := by
    rw [hre]
    linarith [le_max_left r (max ‖p‖ ‖q‖)]
  have hev : f =ᶠ[𝓝 z₀] g := by
    have ho : IsOpen {z : ℂ | r < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hlt] with z hz using hfg z hz
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc (hmem z₀ hz₀p hz₀q) hev
    (hmem s hp hq)

end Identity

variable (K : Type*) [Field K] [NumberField K]

section Quadratic

/-- A totally complex field of degree $2$ has exactly one infinite place. -/
theorem card_infinitePlace_of_isQuadratic [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    Fintype.card (InfinitePlace K) = 1 := by
  have h := IsTotallyComplex.finrank (K := K)
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  omega

/-- For an imaginary quadratic field, $\sum_w n_w |x|_w^2 = 2 |N(x)|$. -/
theorem sum_mult_sq_eq_of_isQuadratic [IsTotallyComplex K] (hK : finrank ℚ K = 2) (x : K) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * w x ^ 2 = 2 * |(Algebra.norm ℚ x : ℝ)| := by
  obtain ⟨w₀, hw₀⟩ := Fintype.card_eq_one_iff.1 (card_infinitePlace_of_isQuadratic K hK)
  have hprod := InfinitePlace.prod_eq_abs_norm x
  rw [Fintype.prod_eq_single w₀ fun w hw => absurd (hw₀ w) hw, IsTotallyComplex.mult_eq] at hprod
  rw [Fintype.sum_eq_single w₀ fun w hw => absurd (hw₀ w) hw, IsTotallyComplex.mult_eq, hprod]
  push_cast
  ring

/-- For an imaginary quadratic field and $\mathrm{Re}\, s > 2$, $$\Lambda_{\mathfrak{a}}(s) = \Gamma_\mathbb{R}(s) \sum_{\alpha \in \mathfrak{a}, \, \alpha \neq 0} (2 |N(\alpha)|)^{-s/2}.$$ The power is written as $\big(\sqrt{2 |N(\alpha)|}\big)^{-s}$. -/
theorem completedIdealZeta_eq_of_isQuadratic [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 2 < s.re) :
    completedIdealZeta K a s = Complex.Gammaℝ s *
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), if (α : K) = 0 then 0 else
        ((√(2 * |(Algebra.norm ℚ (α : K) : ℝ)|) : ℝ) : ℂ) ^ (-s) := by
  rw [completedIdealZeta_eq K a (by rw [hK]; exact_mod_cast hs)]
  simp_rw [sum_mult_sq_eq_of_isQuadratic K hK]

/-- Multiplication by $x \in K^\times$ is a bijection $\mathfrak{a} \to x \mathfrak{a}$. -/
noncomputable def mulEquivIdeal (x : Kˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ↥(a : FractionalIdeal (𝓞 K)⁰ K) ≃
      ↥((toPrincipalIdeal (𝓞 K) K x * a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) :=
  Equiv.ofBijective
    (fun α => ⟨(x : K) * α, by
      rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul]
      exact ⟨α, α.2, rfl⟩⟩)
    ⟨fun α β h => Subtype.ext (mul_left_cancel₀ x.ne_zero (congrArg Subtype.val h)),
      fun ⟨β, hβ⟩ => by
        have h' := hβ
        rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul] at h'
        obtain ⟨α, hα, h⟩ := h'
        exact ⟨⟨α, hα⟩, Subtype.ext h.symm⟩⟩

@[simp]
theorem coe_mulEquivIdeal (x : Kˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (α : ↥(a : FractionalIdeal (𝓞 K)⁰ K)) : (mulEquivIdeal K x a α : K) = x * α := rfl

/-- The norm of $x \mathfrak{a}$ is $|N(x)| \, N(\mathfrak{a})$. -/
theorem absNorm_toPrincipalIdeal_mul (x : Kˣ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal.absNorm (((toPrincipalIdeal (𝓞 K) K x * a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) :
        FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      |(Algebra.norm ℚ (x : K) : ℝ)| * FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [Units.val_mul, map_mul, coe_toPrincipalIdeal, FractionalIdeal.absNorm_span_singleton]
  push_cast
  rfl

/-- For $\mathrm{Re}\, s > 2$, $\Lambda_{x \mathfrak{a}}(s) = |N(x)|^{-s/2} \Lambda_{\mathfrak{a}}(s)$. -/
theorem completedIdealZeta_toPrincipalIdeal_mul_of_lt [IsTotallyComplex K] (hK : finrank ℚ K = 2) (x : Kˣ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 2 < s.re) :
    completedIdealZeta K (toPrincipalIdeal (𝓞 K) K x * a) s =
      ((√|(Algebra.norm ℚ (x : K) : ℝ)| : ℝ) : ℂ) ^ (-s) * completedIdealZeta K a s := by
  rw [completedIdealZeta_eq_of_isQuadratic K hK _ hs, completedIdealZeta_eq_of_isQuadratic K hK _ hs,
    ← (mulEquivIdeal K x a).tsum_eq fun β => if (β : K) = 0 then (0 : ℂ) else
      ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)]
  have hterm : ∀ α : ↥(a : FractionalIdeal (𝓞 K)⁰ K),
      (if (mulEquivIdeal K x a α : K) = 0 then (0 : ℂ) else
        ((√(2 * |(Algebra.norm ℚ (mulEquivIdeal K x a α : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)) =
      ((√|(Algebra.norm ℚ (x : K) : ℝ)| : ℝ) : ℂ) ^ (-s) *
        (if (α : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (α : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)) := fun α => by
    rw [coe_mulEquivIdeal]
    by_cases hα : (α : K) = 0
    · simp only [hα, mul_zero, ite_true]
    · have hxα : (x : K) * α ≠ 0 := mul_ne_zero x.ne_zero hα
      rw [ite_eq_right hxα, ite_eq_right hα, map_mul]
      push_cast
      rw [abs_mul, mul_left_comm, Real.sqrt_mul (abs_nonneg _), Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  simp_rw [hterm]
  rw [tsum_mul_left]
  ring

end Quadratic

section ClassTerm

/-- The constant $c_{\mathfrak{a}} = \sqrt{N(\mathfrak{a}) \sqrt{|d_K|}}$. -/
noncomputable def idealScale (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  √((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|)

theorem absNorm_pos (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (0 : ℝ) < FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) := by
  have h0 : FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h => a.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast (FractionalIdeal.absNorm_nonneg _).lt_of_ne' h0

theorem sqrt_abs_discr_pos : 0 < √|(discr K : ℝ)| :=
  Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))

theorem idealScale_pos (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < idealScale K a :=
  Real.sqrt_pos.2 (mul_pos (absNorm_pos K a) (sqrt_abs_discr_pos K))

theorem idealScale_sq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealScale K a ^ 2 =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)| :=
  Real.sq_sqrt (mul_pos (absNorm_pos K a) (sqrt_abs_discr_pos K)).le

/-- The constant of the dual ideal is the inverse: $c_{\mathfrak{a}^\vee} = c_{\mathfrak{a}}^{-1}$. -/
theorem idealScale_dualUnit (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealScale K (dualUnit K a) = (idealScale K a)⁻¹ := by
  rw [idealScale, idealScale, absNorm_dualUnit, ← Real.sqrt_inv]
  congr 1
  have hd := sqrt_abs_discr_pos K
  have hs : √|(discr K : ℝ)| ^ 2 = |(discr K : ℝ)| := Real.sq_sqrt (abs_nonneg _)
  have hN := (absNorm_pos K a).ne'
  set t := √|(discr K : ℝ)| with ht
  rw [← hs]
  field_simp

/-- The term $\psi_{\mathfrak{a}}(s) = c_{\mathfrak{a}}^s \Lambda_{\mathfrak{a}}(s)$ of an ideal class. -/
noncomputable def classTerm (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (idealScale K a : ℂ) ^ s * completedIdealZeta K a s

theorem differentiableAt_classTerm (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 2) : DifferentiableAt ℂ (classTerm K a) s := by
  refine (differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.2 (idealScale_pos K a).ne'))).mul ?_
  exact differentiableAt_completedIdealZeta K a hs (by rw [hK]; exact_mod_cast hs')

/-- **The functional equation of a class term.** $\psi_{\mathfrak{a}}(2 - s) = \psi_{\mathfrak{a}^\vee}(s)$. -/
theorem classTerm_two_sub (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    classTerm K a (2 - s) = classTerm K (dualUnit K a) s := by
  have h := completedIdealZeta_sub K a s
  rw [hK] at h
  push_cast at h
  have hc := idealScale_pos K a
  have hc0 : (idealScale K a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have harg : (idealScale K a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact Real.pi_ne_zero.symm
  have hsq : ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℂ) *
      ((√|(discr K : ℝ)| : ℝ) : ℂ)) = (idealScale K a : ℂ) ^ 2 := by
    exact_mod_cast (idealScale_sq K a).symm
  rw [classTerm, classTerm, h, idealScale_dualUnit, Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
    Complex.cpow_sub _ _ hc0, Complex.cpow_two, hsq]
  have hcs : (idealScale K a : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hc0)
  field_simp

end ClassTerm

section ClassInvariance

variable [IsTotallyComplex K]

/-- The class term of $x \mathfrak{a}$ for $\mathrm{Re}\, s > 2$. -/
theorem classTerm_toPrincipalIdeal_mul_of_lt (hK : finrank ℚ K = 2) (x : Kˣ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 2 < s.re) :
    classTerm K (toPrincipalIdeal (𝓞 K) K x * a) s = classTerm K a s := by
  rw [classTerm, classTerm, completedIdealZeta_toPrincipalIdeal_mul_of_lt K hK x a hs]
  have hscale : idealScale K (toPrincipalIdeal (𝓞 K) K x * a) =
      √|(Algebra.norm ℚ (x : K) : ℝ)| * idealScale K a := by
    rw [idealScale, idealScale, absNorm_toPrincipalIdeal_mul, mul_assoc,
      Real.sqrt_mul (abs_nonneg _)]
  have hx : (√|(Algebra.norm ℚ (x : K) : ℝ)| : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (abs_pos.2 ?_))
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 x.ne_zero
  rw [hscale, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg _) (idealScale_pos K a).le, Complex.cpow_neg]
  have hx' : ((√|(Algebra.norm ℚ (x : K) : ℝ)| : ℝ) : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl hx)
  field_simp

/-- **Class invariance.** The class term $\psi_{\mathfrak{a}}$ depends only on the ideal class of $\mathfrak{a}$, for $s \neq 0, 2$. -/
theorem classTerm_toPrincipalIdeal_mul (hK : finrank ℚ K = 2) (x : Kˣ)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 2) :
    classTerm K (toPrincipalIdeal (𝓞 K) K x * a) s = classTerm K a s :=
  eq_of_eq_of_lt_re (fun _ h h' => differentiableAt_classTerm K hK _ h h')
    (fun _ h h' => differentiableAt_classTerm K hK _ h h')
    (fun _ h => classTerm_toPrincipalIdeal_mul_of_lt K hK x a h) hs hs'

omit [IsTotallyComplex K] in
/-- Two nonzero fractional ideals in the same class differ by a principal ideal. -/
theorem exists_eq_toPrincipalIdeal_mul {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K a = ClassGroup.mk K b) : ∃ x : Kˣ, b = toPrincipalIdeal (𝓞 K) K x * a := by
  have h1 : ClassGroup.mk K (b * a⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
  obtain ⟨y, hy⟩ := h1
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact (b * a⁻¹).ne_zero hy
  refine ⟨Units.mk0 y hy0, ?_⟩
  have h2 : toPrincipalIdeal (𝓞 K) K (Units.mk0 y hy0) = b * a⁻¹ :=
    toPrincipalIdeal_eq_iff.2 (by rw [Units.val_mk0]; exact hy.symm)
  rw [h2, inv_mul_cancel_right]

theorem classTerm_eq_of_mk_eq (hK : finrank ℚ K = 2) {a b : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K a = ClassGroup.mk K b) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 2) :
    classTerm K a s = classTerm K b s := by
  obtain ⟨x, rfl⟩ := exists_eq_toPrincipalIdeal_mul K h
  exact (classTerm_toPrincipalIdeal_mul K hK x a hs hs').symm

end ClassInvariance

section ClassZeta

theorem classGroup_mk_surjective :
    Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := fun C => by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  exact ⟨FractionalIdeal.mk0 K I, by rw [ClassGroup.mk_mk0, hI]⟩

/-- A choice of a fractional ideal $\mathfrak{a}_C$ in each ideal class $C$. -/
noncomputable def classRep (C : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Function.surjInv (classGroup_mk_surjective K) C

@[simp]
theorem mk_classRep (C : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRep K C) = C :=
  Function.surjInv_eq (classGroup_mk_surjective K) C

/-- The different ideal $\mathfrak{d} = (\mathcal{O}_K^\vee)^{-1}$ as a unit of the group of fractional ideals. -/
noncomputable def differentUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (dualUnit K 1)⁻¹

theorem dualUnit_eq (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : dualUnit K a = (a * differentUnit K)⁻¹ := by
  ext
  simp only [differentUnit, Units.val_inv_eq_inv_val, Units.val_mul, coe_dualUnit_eq,
    Units.val_one, one_mul, inv_inv]

/-- The class zeta function $\Lambda_K(s) = \sum_C \psi_{\mathfrak{a}_C}(s)$, a sum over the ideal classes of $K$. -/
noncomputable def classZeta (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), classTerm K (classRep K C) s

theorem differentiableAt_classZeta (hK : finrank ℚ K = 2) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 2) :
    DifferentiableAt ℂ (classZeta K) s := by
  have h : classZeta K = fun s => ∑ C : ClassGroup (𝓞 K), classTerm K (classRep K C) s := rfl
  rw [h]
  exact DifferentiableAt.fun_sum fun C _ => differentiableAt_classTerm K hK _ hs hs'

/-- **The functional equation of the class zeta function.** For an imaginary quadratic field $K$ and $s \neq 0, 2$, $\Lambda_K(2 - s) = \Lambda_K(s)$. -/
theorem classZeta_two_sub [IsTotallyComplex K] (hK : finrank ℚ K = 2) {s : ℂ} (hs : s ≠ 0)
    (hs' : s ≠ 2) : classZeta K (2 - s) = classZeta K s := by
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.mulRight (ClassGroup.mk K (differentUnit K))).trans (Equiv.inv _)
  have he : ∀ C, ClassGroup.mk K (dualUnit K (classRep K C)) = e C := fun C => by
    simp only [e, dualUnit_eq, map_inv, map_mul, mk_classRep, Equiv.trans_apply,
      Equiv.coe_mulRight, Equiv.inv_apply]
  simp only [classZeta, classTerm_two_sub K hK]
  rw [← e.sum_comp fun C => classTerm K (classRep K C) s]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← he]
  refine classTerm_eq_of_mk_eq K hK ?_ hs hs'
  rw [mk_classRep]

/-- The Dirichlet series of the class zeta function: for $\mathrm{Re}\, s > 2$, $$\Lambda_K(s) = \Gamma_\mathbb{R}(s) \sum_C c_{\mathfrak{a}_C}^s \sum_{\alpha \in \mathfrak{a}_C, \, \alpha \neq 0} (2 |N(\alpha)|)^{-s/2}.$$ -/
theorem classZeta_eq [IsTotallyComplex K] (hK : finrank ℚ K = 2) {s : ℂ} (hs : 2 < s.re) :
    classZeta K s = Complex.Gammaℝ s * ∑ C : ClassGroup (𝓞 K), (idealScale K (classRep K C) : ℂ) ^ s *
      ∑' α : (classRep K C : FractionalIdeal (𝓞 K)⁰ K), if (α : K) = 0 then 0 else
        ((√(2 * |(Algebra.norm ℚ (α : K) : ℝ)|) : ℝ) : ℂ) ^ (-s) := by
  rw [classZeta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [classTerm, completedIdealZeta_eq_of_isQuadratic K hK _ hs, mul_left_comm]

end ClassZeta

end Langlands.Tate
