/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.ImaginaryQuadratic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The Dedekind zeta function of an imaginary quadratic field

Let $F$ be an imaginary quadratic field, with discriminant $d$, $w$ roots of unity and Dedekind zeta function $\zeta_F$. This file proves that $$\Lambda^{\mathrm{cl}}(2u) = \frac{w}{2} |d|^{u/2} \Gamma_\mathbb{C}(u) \zeta_F(u)$$ for $\mathrm{Re}\, u > 1$, where $\Lambda^{\mathrm{cl}}$ is the class zeta function of `Langlands/Tate/ImaginaryQuadratic.lean` and $\zeta_F$ is Mathlib's `NumberField.dedekindZeta`. With the functional equation of $\Lambda^{\mathrm{cl}}$, the completed Dedekind zeta function of $F$ has a holomorphic continuation to $\mathbb{C} \setminus \{0, 1\}$ and the functional equation $u \mapsto 1 - u$.

The proof counts the elements of an integral ideal. Let $J$ be a nonzero integral ideal. For each nonzero $\alpha \in J$ there is a unique integral ideal $I$ with $(\alpha) = J I$. The map $\alpha \mapsto I$ is onto the integral ideals of the class $[J]^{-1}$, and its fibres are the orbits of the unit group. For an imaginary quadratic field the unit group is the group of roots of unity, so each fibre has $w$ elements. Thus $$\sum_{\alpha \in J, \, \alpha \neq 0} \Big(\frac{|N(\alpha)|}{N(J)}\Big)^{-u} = w \sum_{[I] = [J]^{-1}} N(I)^{-u},$$ and the sum over the classes gives $w \zeta_F(u)$.

## Main results

* `Langlands.Tate.mem_torsion_of_isQuadratic`: each unit is a root of unity.
* `Langlands.Tate.dedekindZeta_eq_of_hasSum`: the Dedekind zeta function as a sum over the nonzero ideals.
* `Langlands.Tate.natCard_generators`: the number of generators of $J I$.
* `Langlands.Tate.classZeta_two_mul`: the class zeta function and the Dedekind zeta function.
* `Langlands.Tate.completedQuadraticZeta_one_sub`: the functional equation of the completed Dedekind zeta function.
-/

namespace Langlands.Tate

open Module Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

open scoped nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

section DedekindSum

/-- If $\sum_{I \neq 0} N(I)^{-u}$ has the sum $X$, then $\zeta_K(u) = X$. -/
theorem dedekindZeta_eq_of_hasSum {u X : ℂ}
    (h : HasSum (fun I : (Ideal (𝓞 K))⁰ => ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)) ^ (-u)) X) :
    dedekindZeta K u = X := by
  have hf := h.tsum_fiberwise (fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K)))
  rw [dedekindZeta, LSeries]
  rw [← hf.tsum_eq]
  congr 1
  funext n
  have hfin : Finite ((fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}) :=
    ((Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn).to_subtype
  have := Fintype.ofFinite ((fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n})
  rw [tsum_fintype]
  have hc : ∀ I : ((fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}),
      ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℂ)) ^ (-u) = (n : ℂ) ^ (-u) :=
    fun I => by rw [show Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n from I.2]
  rw [Finset.sum_congr rfl fun I _ => hc I, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    have he : IsEmpty ((fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {0}) :=
      ⟨fun I => nonZeroDivisors.coe_ne_zero (I : (Ideal (𝓞 K))⁰)
        (Ideal.absNorm_eq_zero_iff.1 I.2)⟩
    rw [Nat.card_of_isEmpty, zero_smul]
  · rw [LSeries.term_of_ne_zero hn, nsmul_eq_mul, Complex.cpow_neg, div_eq_mul_inv]
    congr 2
    refine (Nat.card_congr
      { toFun := fun I => ⟨((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), I.2⟩
        invFun := fun I => ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero fun h0 => hn (by
          rw [← I.2, h0, map_zero])⟩, I.2⟩
        left_inv := fun I => rfl
        right_inv := fun I => rfl }).symm

end DedekindSum

section Units

variable [IsTotallyComplex K]

/-- For an imaginary quadratic field, each unit is a root of unity. -/
theorem mem_torsion_of_isQuadratic (hK : finrank ℚ K = 2) (x : (𝓞 K)ˣ) : x ∈ torsion K := by
  have hrank : rank K = 0 := by rw [rank, card_infinitePlace_of_isQuadratic K hK]
  have : IsEmpty (Fin (rank K)) := by rw [hrank]; infer_instance
  obtain ⟨⟨ζ, e⟩, hx, -⟩ := exist_unique_eq_mul_prod K x
  rw [Fintype.prod_empty, mul_one] at hx
  rw [hx]
  exact ζ.2

/-- For an imaginary quadratic field, the unit group has $w$ elements. -/
theorem natCard_units_of_isQuadratic (hK : finrank ℚ K = 2) :
    Nat.card (𝓞 K)ˣ = torsionOrder K :=
  (Nat.card_congr (Equiv.subtypeUnivEquiv (mem_torsion_of_isQuadratic K hK))).symm

theorem finite_units_of_isQuadratic (hK : finrank ℚ K = 2) : Finite (𝓞 K)ˣ :=
  Finite.of_equiv _ (Equiv.subtypeUnivEquiv (mem_torsion_of_isQuadratic K hK))

end Units

section Power

/-- For $r \geq 0$, $(\sqrt{r})^{2 z} = r^z$. -/
theorem sqrt_cpow_two_mul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ((√r : ℝ) : ℂ) ^ (2 * z) = (r : ℂ) ^ z := by
  have him : (Complex.log ((√r : ℝ) : ℂ) * 2).im = 0 := by
    rw [← Complex.ofReal_log (Real.sqrt_nonneg r)]
    simp
  rw [Complex.cpow_mul z (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; linarith [Real.pi_pos]),
    Complex.cpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt hr]

/-- The constant of a term: $c_J^{2u} \Gamma_\mathbb{R}(2u) (2 N(J) N(I))^{-u} = \frac{1}{2} \Gamma_\mathbb{C}(u) D^u N(I)^{-u}$, where $c_J = \sqrt{N(J) D}$. -/
theorem scale_mul_gamma_mul {A B D : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (u : ℂ) :
    ((√(A * D) : ℝ) : ℂ) ^ (2 * u) * Complex.Gammaℝ (2 * u) *
        ((√(2 * (A * B)) : ℝ) : ℂ) ^ (-(2 * u)) =
      Complex.Gammaℂ u / 2 * (D : ℂ) ^ u * (B : ℂ) ^ (-u) := by
  rw [show -(2 * u) = 2 * -u by ring, sqrt_cpow_two_mul (by positivity),
    sqrt_cpow_two_mul (by positivity), Complex.Gammaℝ_def, Complex.Gammaℂ_def,
    show -(2 * u) / 2 = -u by ring, show 2 * u / 2 = u by ring]
  have e1 := Complex.mul_cpow_ofReal_nonneg hA.le hD.le u
  have e2 := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_pos hA hB).le (-u)
  have e3 := Complex.mul_cpow_ofReal_nonneg hA.le hB.le (-u)
  have e4 := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le (-u)
  push_cast at e1 e2 e3 e4 ⊢
  rw [e1, e2, e3, e4]
  have hA' : (A : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hA.ne'))
  have h2 : (2 : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  simp only [Complex.cpow_neg]
  field_simp

end Power

section Count

omit [NumberField K] in
/-- If $(\alpha) = J I$ for nonzero ideals $J$ and $I$, then $\alpha \neq 0$. -/
theorem ne_zero_of_span_eq_mul (J I : (Ideal (𝓞 K))⁰) {α : 𝓞 K}
    (h : Ideal.span {α} = (J : Ideal (𝓞 K)) * I) : α ≠ 0 := fun h0 =>
  mul_ne_zero (nonZeroDivisors.coe_ne_zero J) (nonZeroDivisors.coe_ne_zero I) (by
    rw [← h, h0, Ideal.span_singleton_eq_bot.2 rfl, ← Submodule.zero_eq_bot])

/-- For a nonzero element $\alpha$ of a nonzero ideal $J$, there is a nonzero ideal $I$ with $(\alpha) = J I$. -/
theorem exists_span_eq_mul (J : (Ideal (𝓞 K))⁰) {α : 𝓞 K} (hα : α ∈ (J : Ideal (𝓞 K)))
    (h0 : α ≠ 0) : ∃ I : (Ideal (𝓞 K))⁰, Ideal.span {α} = (J : Ideal (𝓞 K)) * I := by
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hα)
  refine ⟨⟨I, mem_nonZeroDivisors_of_ne_zero fun hI0 => h0 ?_⟩, hI⟩
  rw [hI0, mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at hI
  exact hI

omit [NumberField K] in
theorem mem_of_span_eq_mul (J I : (Ideal (𝓞 K))⁰) {α : 𝓞 K}
    (h : Ideal.span {α} = (J : Ideal (𝓞 K)) * I) : α ∈ (J : Ideal (𝓞 K)) := by
  have hle : Ideal.span {α} ≤ (J : Ideal (𝓞 K)) := h.le.trans Ideal.mul_le_left
  exact (Ideal.span_singleton_le_iff_mem _).1 hle

/-- The nonzero elements $\alpha$ of $J$, sorted by the ideal $I$ with $(\alpha) = J I$. -/
noncomputable def elementEquiv (J : (Ideal (𝓞 K))⁰) :
    {α : 𝓞 K // α ∈ (J : Ideal (𝓞 K)) ∧ α ≠ 0} ≃
      Σ I : (Ideal (𝓞 K))⁰, {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} where
  toFun α := ⟨(exists_span_eq_mul K J α.2.1 α.2.2).choose, α.1,
    (exists_span_eq_mul K J α.2.1 α.2.2).choose_spec⟩
  invFun p := ⟨p.2.1, mem_of_span_eq_mul K J p.1 p.2.2, ne_zero_of_span_eq_mul K J p.1 p.2.2⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨I, α, hα⟩ := p
    refine Sigma.subtype_ext (Subtype.ext ?_) rfl
    exact mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero J)
      ((exists_span_eq_mul K J (mem_of_span_eq_mul K J I hα)
        (ne_zero_of_span_eq_mul K J I hα)).choose_spec.symm.trans hα)

variable [IsTotallyComplex K]

/-- The number of generators of $J I$ is $w$ if $[I] = [J]^{-1}$, and $0$ otherwise. -/
theorem natCard_generators (hK : finrank ℚ K = 2) (J I : (Ideal (𝓞 K))⁰) :
    Nat.card {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} =
      if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then torsionOrder K else 0 := by
  split_ifs with h
  · obtain ⟨x, hx0, hx⟩ := ClassGroup.mk0_eq_mk0_inv_iff.1 h
    rw [← natCard_units_of_isQuadratic K hK]
    refine (Nat.card_congr (Equiv.ofBijective (fun u : (𝓞 K)ˣ =>
      (⟨x * u, by rw [Ideal.span_singleton_mul_right_unit u.isUnit, mul_comm, hx]⟩ :
        {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I}))
      ⟨fun u v huv => ?_, fun α => ?_⟩)).symm
    · exact Units.ext (mul_left_cancel₀ hx0 (congrArg Subtype.val huv))
    · have hα : Ideal.span {x} = Ideal.span {(α : 𝓞 K)} := by rw [α.2, mul_comm, hx]
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hα
      exact ⟨u, Subtype.ext hu⟩
  · have : IsEmpty {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} :=
      ⟨fun α => h (ClassGroup.mk0_eq_mk0_inv_iff.2
        ⟨α.1, ne_zero_of_span_eq_mul K J I α.2, by rw [mul_comm, α.2]⟩)⟩
    exact Nat.card_of_isEmpty

theorem finite_generators (hK : finrank ℚ K = 2) (J I : (Ideal (𝓞 K))⁰) :
    Finite {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} := by
  by_cases h : ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹
  · refine Nat.finite_of_card_ne_zero ?_
    rw [natCard_generators K hK J I]
    simp [h, (torsionOrder_pos K).ne']
  · have : IsEmpty {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} :=
      ⟨fun α => h (ClassGroup.mk0_eq_mk0_inv_iff.2
        ⟨α.1, ne_zero_of_span_eq_mul K J I α.2, by rw [mul_comm, α.2]⟩)⟩
    infer_instance

/-- For $\mathrm{Re}\, s > 2$, the series $\sum_{\alpha \in \mathfrak{a}, \, \alpha \neq 0} (2 |N(\alpha)|)^{-s/2}$ converges. -/
theorem summable_quadraticTerm (hK : finrank ℚ K = 2) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 2 < s.re) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) => if (α : K) = 0 then (0 : ℂ) else
      ((√(2 * |(Algebra.norm ℚ (α : K) : ℝ)|) : ℝ) : ℂ) ^ (-s) := by
  have hs' : (finrank ℚ K : ℝ) < s.re := by
    rw [hK]
    exact_mod_cast hs
  rw [← finrank_euclidean_mixedSpace] at hs'
  refine ((globalLatticeEquiv K (traceScale K) a).summable_iff.2
    (summable_epsteinZeta (traceLattice K a) hs')).congr fun α => ?_
  have h0 : globalLatticeEquiv K (traceScale K) a α = 0 ↔ (α : K) = 0 := by
    rw [Subtype.ext_iff, coe_globalLatticeEquiv, ZeroMemClass.coe_zero]
    constructor
    · intro h
      exact globalEmbedding_injective K (traceScale K) (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  simp only [Function.comp_apply, h0]
  split_ifs
  · rfl
  · rw [← sum_mult_sq_eq_of_isQuadratic K hK, coe_globalLatticeEquiv,
      ← norm_globalEmbedding_traceScale_sq, Real.sqrt_sq (norm_nonneg _)]

end Count

section Main

/-- If $(\alpha) = J I$, then $|N(\alpha)| = N(J) N(I)$. -/
theorem abs_norm_eq_of_span_eq_mul (J I : (Ideal (𝓞 K))⁰) {α : 𝓞 K}
    (h : Ideal.span {α} = (J : Ideal (𝓞 K)) * I) :
    |(Algebra.norm ℚ (α : K) : ℝ)| =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * Ideal.absNorm (I : Ideal (𝓞 K)) := by
  have h1 := Ideal.absNorm_span_singleton α
  rw [h, map_mul] at h1
  rw [← Algebra.coe_norm_int, ← Nat.cast_mul, h1, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs]

/-- The nonzero elements of an integral ideal $J$ are the nonzero elements of $J$ as a fractional ideal. -/
noncomputable def nonzeroEquiv (J : (Ideal (𝓞 K))⁰) :
    {α : 𝓞 K // α ∈ (J : Ideal (𝓞 K)) ∧ α ≠ 0} ≃
      {β : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) // (β : K) ≠ 0} :=
  Equiv.ofBijective (fun α => ⟨⟨(α.1 : K), by
      rw [FractionalIdeal.coe_mk0]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨α.1, α.2.1, rfl⟩⟩, by
      exact fun h => α.2.2 (by exact_mod_cast (show ((α.1 : 𝓞 K) : K) = 0 from h))⟩)
    ⟨fun α β h => Subtype.ext (RingOfIntegers.coe_injective (congrArg (fun x => ((x.1 : K))) h)),
      fun β => by
        obtain ⟨⟨b, hb⟩, hb0⟩ := β
        rw [FractionalIdeal.coe_mk0] at hb
        obtain ⟨x, hx, hxb⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
        refine ⟨⟨x, hx, fun h0 => hb0 (by show b = 0; rw [← hxb, h0, map_zero])⟩, ?_⟩
        exact Subtype.ext (Subtype.ext hxb)⟩

/-- The nonzero integral ideal that the proof uses for a class. -/
noncomputable def classIdeal (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (ClassGroup.mk0_surjective C).choose

theorem mk0_classIdeal (C : ClassGroup (𝓞 K)) : ClassGroup.mk0 (classIdeal K C) = C :=
  (ClassGroup.mk0_surjective C).choose_spec

theorem two_lt_re_two_mul {u : ℂ} (hu : 1 < u.re) : 2 < (2 * u).re := by
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

variable [IsTotallyComplex K]

/-- For $\mathrm{Re}\, s > 2$, the series of $\alpha \in J$ sorted by the ideal $I$ with $(\alpha) = J I$. -/
theorem hasSum_quadraticTerm (hK : finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰) {s : ℂ}
    (hs : 2 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      (Nat.card {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} : ℂ) *
        ((√(2 * ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * Ideal.absNorm (I : Ideal (𝓞 K)))) : ℝ) :
          ℂ) ^ (-s))
      (∑' β : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K), if (β : K) = 0 then (0 : ℂ)
        else ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)) := by
  set g : ↥(FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) → ℂ := fun β =>
    if (β : K) = 0 then (0 : ℂ) else ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)
    with hg
  have h1 := (summable_quadraticTerm K hK (FractionalIdeal.mk0 K J) hs).hasSum
  have h2 := (hasSum_subtype_iff_of_support_subset (s := {β | (β : K) ≠ 0}) (f := g)
    (fun β hβ h0 => hβ (by simp only [hg, h0, ite_true]))).2 h1
  have h3 := (nonzeroEquiv K J).hasSum_iff.2 h2
  have h4 := (elementEquiv K J).symm.hasSum_iff.2 h3
  refine h4.sigma fun I => ?_
  have := finite_generators K hK J I
  have := Fintype.ofFinite {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I}
  have hv : ∀ c : {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I},
      g ⟨((c.1 : 𝓞 K) : K), ((nonzeroEquiv K J) ((elementEquiv K J).symm ⟨I, c⟩)).1.2⟩ =
        ((√(2 * ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * Ideal.absNorm (I : Ideal (𝓞 K)))) : ℝ) :
          ℂ) ^ (-s) := fun c => by
    have hc0 : ((c.1 : 𝓞 K) : K) ≠ 0 := by
      exact_mod_cast ne_zero_of_span_eq_mul K J I c.2
    simp only [hg, ite_eq_right hc0]
    rw [abs_norm_eq_of_span_eq_mul K J I c.2]
  have h5 := hasSum_fintype (fun _ : {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} =>
    ((√(2 * ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * Ideal.absNorm (I : Ideal (𝓞 K)))) : ℝ) :
      ℂ) ^ (-s))
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul] at h5
  exact h5.congr_fun fun c => hv c

/-- For $\mathrm{Re}\, u > 1$, the term of an integral ideal $J$ is a sum over the ideals of the class $[J]^{-1}$. -/
theorem hasSum_classTerm (hK : finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      (if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then (torsionOrder K : ℂ) else 0) *
        (Complex.Gammaℂ u / 2 * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u)))
      (classTerm K (FractionalIdeal.mk0 K J) (2 * u)) := by
  have hs := two_lt_re_two_mul hu
  have h := (hasSum_quadraticTerm K hK J hs).mul_left
    (((idealScale K (FractionalIdeal.mk0 K J) : ℝ) : ℂ) ^ (2 * u) * Complex.Gammaℝ (2 * u))
  rw [classTerm, completedIdealZeta_eq_of_isQuadratic K hK _ hs]
  convert h using 1
  · funext I
    have hN : (FractionalIdeal.absNorm (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
        (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) := by
      rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
    have hpos : ∀ I : (Ideal (𝓞 K))⁰, (0 : ℝ) < Ideal.absNorm (I : Ideal (𝓞 K)) := fun I =>
      Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 =>
        nonZeroDivisors.coe_ne_zero I (Ideal.absNorm_eq_zero_iff.1 h0))
    rw [natCard_generators K hK J I, idealScale, hN]
    split_ifs
    · have e := scale_mul_gamma_mul (hpos J) (hpos I) (sqrt_abs_discr_pos K) u
      simp only [Complex.ofReal_natCast] at e
      linear_combination (-(torsionOrder K : ℂ)) * e
    · simp
  · ring

/-- **The Dedekind zeta function of an imaginary quadratic field.** For $\mathrm{Re}\, u > 1$, $$\Lambda^{\mathrm{cl}}(2u) = \frac{w}{2} |d|^{u/2} \Gamma_\mathbb{C}(u) \zeta_F(u),$$ where $w$ is the number of roots of unity and $\zeta_F$ is Mathlib's `NumberField.dedekindZeta`. -/
theorem classZeta_two_mul (hK : finrank ℚ K = 2) {u : ℂ} (hu : 1 < u.re) :
    classZeta K (2 * u) = (torsionOrder K / 2 : ℂ) * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
      Complex.Gammaℂ u * dedekindZeta K u := by
  have hs := two_lt_re_two_mul hu
  have hs0 : 2 * u ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs2 : 2 * u ≠ 2 := fun h => by rw [h] at hs; norm_num at hs
  have h1 : classZeta K (2 * u) =
      ∑ C : ClassGroup (𝓞 K), classTerm K (FractionalIdeal.mk0 K (classIdeal K C)) (2 * u) :=
    Finset.sum_congr rfl fun C _ => classTerm_eq_of_mk_eq K hK
      (by rw [mk_classRep, ClassGroup.mk_mk0, mk0_classIdeal]) hs0 hs2
  set G := Complex.Gammaℂ u / 2 * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u with hG
  have h2 : HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      (torsionOrder K : ℂ) * G * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u))
      (classZeta K (2 * u)) := by
    rw [h1]
    convert hasSum_sum (fun C (_ : C ∈ Finset.univ) => hasSum_classTerm K hK (classIdeal K C) hu)
      using 1
    funext I
    rw [← Finset.sum_mul]
    have key : ∀ C : ClassGroup (𝓞 K),
        (ClassGroup.mk0 I = C⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
      fun C => ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
    simp_rw [mk0_classIdeal, key]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  have hΓ : Complex.Gammaℂ u ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.2 Real.pi_pos.ne')))
  have hD : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (sqrt_abs_discr_pos K).ne'))
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hG0 : G ≠ 0 := mul_ne_zero (div_ne_zero hΓ two_ne_zero) hD
  have hwG : (torsionOrder K : ℂ) * G ≠ 0 := mul_ne_zero hw hG0
  have h4 : dedekindZeta K u = classZeta K (2 * u) / ((torsionOrder K : ℂ) * G) := by
    refine dedekindZeta_eq_of_hasSum K ?_
    convert h2.div_const ((torsionOrder K : ℂ) * G) using 1
    funext I
    field_simp
  rw [h4, hG]
  field_simp

/-- The completed Dedekind zeta function of an imaginary quadratic field, $\Lambda_F(u) = \Lambda^{\mathrm{cl}}(2u)$. -/
noncomputable def completedQuadraticZeta (u : ℂ) : ℂ :=
  classZeta K (2 * u)

/-- For $\mathrm{Re}\, u > 1$, $\Lambda_F(u) = \frac{w}{2} |d|^{u/2} \Gamma_\mathbb{C}(u) \zeta_F(u)$. -/
theorem completedQuadraticZeta_eq (hK : finrank ℚ K = 2) {u : ℂ} (hu : 1 < u.re) :
    completedQuadraticZeta K u = (torsionOrder K / 2 : ℂ) * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u *
      Complex.Gammaℂ u * dedekindZeta K u :=
  classZeta_two_mul K hK hu

omit [IsTotallyComplex K] in
/-- The completed Dedekind zeta function is holomorphic on $\mathbb{C} \setminus \{0, 1\}$. -/
theorem differentiableAt_completedQuadraticZeta (hK : finrank ℚ K = 2) {u : ℂ} (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) : DifferentiableAt ℂ (completedQuadraticZeta K) u := by
  have h0 : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have h2 : 2 * u ≠ 2 := fun h => hu1 (by linear_combination h / 2)
  exact (differentiableAt_classZeta K hK h0 h2).comp u (differentiableAt_id.const_mul 2)

/-- **The functional equation of the Dedekind zeta function of an imaginary quadratic field.** For $u \neq 0, 1$, $\Lambda_F(1 - u) = \Lambda_F(u)$. -/
theorem completedQuadraticZeta_one_sub (hK : finrank ℚ K = 2) {u : ℂ} (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) : completedQuadraticZeta K (1 - u) = completedQuadraticZeta K u := by
  have h0 : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have h2 : 2 * u ≠ 2 := fun h => hu1 (by linear_combination h / 2)
  rw [completedQuadraticZeta, completedQuadraticZeta, show 2 * (1 - u) = 2 - 2 * u by ring,
    classZeta_two_sub K hK h0 h2]

end Main

end Langlands.Tate
