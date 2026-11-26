/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.UnitMellin
import Mathlib.LinearAlgebra.Countable

/-!
# The unfolding of the unit theta function

Let $\mathfrak{a}$ be a nonzero fractional ideal of a number field $K$ of degree $n$, with $w_K$ roots of unity and unit rank $r$. Each nonzero $\alpha \in \mathfrak{a}$ gives an integral ideal $I$ with $(\alpha) = \mathfrak{a} I$, and two elements give the same ideal if and only if they differ by a unit. The units are $\zeta \prod_i \varepsilon_i^{k_i}$ with $\zeta$ a root of unity and $k \in \mathbb{Z}^r$. A shift $c \mapsto c + k$ of the unit coordinates multiplies $t(y, c)_w$ by $|\prod_i \varepsilon_i^{k_i}|_w^2$. So the sum over $k$ of the integrals over $[0, 1)^r$ is one integral over $\mathbb{R}^r$. This is the unfolding step in Hecke's proof: $$\Theta_{\mathfrak{a}}(y) - 1 = w_K \sum_I \int_{\mathbb{R}^r} e^{-\pi \sum_w n_w t(y, c)_w |\alpha_I|_w^2} \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. With the result of `Langlands/Tate/UnitMellin.lean` for each term, the Mellin transform of $\Theta_{\mathfrak{a}} - 1$ is a Dirichlet series: for $\mathrm{Re}\, s > n/2$ and $s' = 2s/n$, $$\Lambda_{\mathfrak{a}}(s) = \frac{w_K}{2^{r - r_2} n R_K} \, \Gamma_K(s') \sum_I |N(\alpha_I)|^{-s'}.$$

## Main definitions

* `Langlands.Tate.idealOf`: the integral ideal $I$ with $(\alpha) = \mathfrak{a} I$.
* `Langlands.Tate.Orbits`: the integral ideals $I$ such that $\mathfrak{a} I$ is principal.
* `Langlands.Tate.orbitRep`: a generator $\alpha_I$ of $\mathfrak{a} I$.
* `Langlands.Tate.unitsEquiv`: the bijection $\mu_K \times \mathbb{Z}^r \to \mathcal{O}_K^\times$ of Dirichlet's unit theorem.

## Main results

* `Langlands.Tate.lintegral_eq_tsum_unitCube`: the integral over $\mathbb{R}^r$ is the sum over $k \in \mathbb{Z}^r$ of the integrals over $[0, 1)^r + k$.
* `Langlands.Tate.lintegral_unitCube_eq_tsum`: the unfolding, as an identity of integrals with values in $[0, \infty]$.
* `Langlands.Tate.hasSum_unitTheta_sub_one`: the unfolding as a convergent series.
* `Langlands.Tate.hasSum_Λ_unitThetaFEPair`: the Mellin transform as a Dirichlet series.

## Proof

All the sums and integrals have terms $\ge 0$, so the proof first works with values in $[0, \infty]$. There the sums and integrals commute with no condition. The integral over $[0, 1)^r$ of $\theta_{\mathfrak{a}} - 1$ is finite, so each term is finite, and the identity holds for real numbers. For the Mellin transform, the sum of the norms of the terms is the norm of $y^{s - 1} (\Theta_{\mathfrak{a}}(y) - 1)$, which is integrable for $\mathrm{Re}\, s > n/2$. So the integral of the sum is the sum of the integrals.

## References

* E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, chapter VIII.
* J. Neukirch, Algebraic number theory, chapter VII, section 5.
-/

namespace Langlands.Tate

open Module Filter Topology MeasureTheory Set NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Real Classical nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

section Orbit

variable (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The nonzero elements of a fractional ideal $\mathfrak{a}$. -/
abbrev NonzeroElt := {α : (a : FractionalIdeal (𝓞 K)⁰ K) // (α : K) ≠ 0}

variable {a}

theorem exists_spanSingleton_eq_mul (α : NonzeroElt a) :
    ∃ I : (Ideal (𝓞 K))⁰, FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) =
      (a : FractionalIdeal (𝓞 K)⁰ K) * ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  set b := ((a⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) with hb
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) ≤ (a : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 α.1.2
  have hb1 : b ≤ 1 := by
    rw [hb, ← Units.inv_mul a]
    gcongr
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hb1
  have hI0 : I ≠ 0 := by
    rintro rfl
    rw [Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, eq_comm, hb, mul_eq_zero] at hI
    rcases hI with h | h
    · exact Units.ne_zero _ h
    · exact α.2 ((FractionalIdeal.spanSingleton_eq_zero_iff).1 h)
  refine ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩
  change _ = _ * (I : FractionalIdeal (𝓞 K)⁰ K)
  rw [hI, hb, ← mul_assoc, Units.mul_inv, one_mul]

variable (a) in
/-- The integral ideal $I$ with $(\alpha) = \mathfrak{a} I$, for a nonzero $\alpha \in \mathfrak{a}$. -/
noncomputable def idealOf (α : NonzeroElt a) : (Ideal (𝓞 K))⁰ :=
  (exists_spanSingleton_eq_mul α).choose

theorem spanSingleton_eq_mul_idealOf (α : NonzeroElt a) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) =
      (a : FractionalIdeal (𝓞 K)⁰ K) * ((idealOf a α : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
  (exists_spanSingleton_eq_mul α).choose_spec

theorem idealOf_eq_iff (α β : NonzeroElt a) :
    idealOf a α = idealOf a β ↔ FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (β : K) := by
  rw [spanSingleton_eq_mul_idealOf, spanSingleton_eq_mul_idealOf]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (fun J => ((a⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) * J) h
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h'
    exact Subtype.ext (FractionalIdeal.coeIdeal_injective h')

/-- The product $u \alpha$ of a unit and a nonzero element of $\mathfrak{a}$. -/
noncomputable def unitSMul (u : (𝓞 K)ˣ) (α : NonzeroElt a) : NonzeroElt a :=
  ⟨⟨(u : K) * α, (unit_mul_mem_iff _ u).2 α.1.2⟩,
    mul_ne_zero (by simp) α.2⟩

omit [NumberField K] in
theorem coe_unitSMul (u : (𝓞 K)ˣ) (α : NonzeroElt a) :
    ((unitSMul u α : NonzeroElt a) : K) = (u : K) * α :=
  rfl

theorem idealOf_unitSMul (u : (𝓞 K)ˣ) (α : NonzeroElt a) :
    idealOf a (unitSMul u α) = idealOf a α := by
  rw [idealOf_eq_iff, FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨u⁻¹, ?_⟩
  rw [coe_unitSMul, Units.smul_def, Algebra.smul_def, ← mul_assoc]
  simp

variable (a) in
/-- The integral ideals $I$ such that $\mathfrak{a} I$ is principal. They index the orbits of the units on the nonzero elements of $\mathfrak{a}$. -/
abbrev Orbits := Set.range (idealOf a)

variable (a) in
/-- A generator of $\mathfrak{a} I$, for $I$ in `Orbits a`. -/
noncomputable def orbitRep (I : Orbits a) : NonzeroElt a :=
  I.2.choose

theorem idealOf_orbitRep (I : Orbits a) : idealOf a (orbitRep a I) = I :=
  I.2.choose_spec

variable (a) in
/-- The orbit of a nonzero element of $\mathfrak{a}$, given by its ideal $I$. -/
noncomputable def orbitOf (α : NonzeroElt a) : Orbits a :=
  ⟨idealOf a α, α, rfl⟩

/-- The units act simply transitively on each fibre of `orbitOf`. -/
noncomputable def unitsEquivFiber (I : Orbits a) : (𝓞 K)ˣ ≃ (orbitOf a ⁻¹' {I}) :=
  Equiv.ofBijective (fun u => ⟨unitSMul u (orbitRep a I), Subtype.ext (by
      simp only [orbitOf, idealOf_unitSMul, idealOf_orbitRep])⟩)
    ⟨fun u v h => by
      have h' := congrArg (fun x => ((x.1 : NonzeroElt a) : K)) h
      simp only [coe_unitSMul] at h'
      exact Units.ext (RingOfIntegers.coe_injective (mul_right_cancel₀ (orbitRep a I).2 h')),
    fun β => by
      have h : idealOf a (orbitRep a I) = idealOf a β.1 := by
        rw [idealOf_orbitRep]
        exact (congrArg Subtype.val (show orbitOf a β.1 = I from β.2)).symm
      obtain ⟨u, hu⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).1
        ((idealOf_eq_iff _ _).1 h)
      refine ⟨u, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
      rw [← hu, Units.smul_def, Algebra.smul_def]
      rfl⟩

theorem coe_unitsEquivFiber (I : Orbits a) (u : (𝓞 K)ˣ) :
    (((unitsEquivFiber I u).1 : NonzeroElt a) : K) = (u : K) * (orbitRep a I : K) :=
  rfl

end Orbit

section Units

variable (K) in
/-- Each unit is $\zeta \prod_i \varepsilon_i^{k_i}$ for a unique root of unity $\zeta$ and a unique $k \in \mathbb{Z}^r$. -/
noncomputable def unitsEquiv : torsion K × (Fin (rank K) → ℤ) ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective (fun p => (p.1 : (𝓞 K)ˣ) * unitOfInt K p.2)
    ⟨fun p q h => by
      exact (exist_unique_eq_mul_prod K ((q.1 : (𝓞 K)ˣ) * unitOfInt K q.2)).unique h.symm rfl,
    fun x => by
      obtain ⟨p, hp, -⟩ := exist_unique_eq_mul_prod K x
      exact ⟨p, hp.symm⟩⟩

theorem unitsEquiv_apply (p : torsion K × (Fin (rank K) → ℤ)) :
    unitsEquiv K p = (p.1 : (𝓞 K)ˣ) * unitOfInt K p.2 :=
  rfl

theorem thetaTerm_unit_mul (u : (𝓞 K)ˣ) (x : K) (t : InfinitePlace K → ℝ) :
    thetaTerm ((u : K) * x) t = thetaTerm x (fun w => t w * w (u : K) ^ 2) := by
  simp only [thetaTerm, map_mul, mul_pow]
  congr 2
  exact Finset.sum_congr rfl fun w _ => by ring

theorem thetaTerm_unitsEquiv (p : torsion K × (Fin (rank K) → ℤ)) (x : K) (y : ℝ)
    (c : Fin (rank K) → ℝ) :
    thetaTerm ((unitsEquiv K p : K) * x) (unitScale K y c) =
      thetaTerm x (unitScale K y (c + fun i => (p.2 i : ℝ))) := by
  have h1 : ((unitsEquiv K p : (𝓞 K)ˣ) : K) * x =
      ((unitOfInt K p.2 : (𝓞 K)ˣ) : K) * (((p.1 : (𝓞 K)ˣ) : K) * x) := by
    rw [unitsEquiv_apply, Units.val_mul, map_mul]
    ring
  rw [h1, thetaTerm_unit_mul, thetaTerm_unit_mul]
  congr 1
  funext w
  rw [unitScale_add_int, (mem_torsion K).1 p.1.2 w, one_pow, mul_one]

end Units

section Unfold

variable {r : ℕ}

/-- The integral of $F \ge 0$ over $\mathbb{R}^r$ is the sum over $k \in \mathbb{Z}^r$ of the integrals of $F(c + k)$ over $[0, 1)^r$. -/
theorem lintegral_eq_tsum_unitCube (F : (Fin r → ℝ) → ℝ≥0∞) :
    ∫⁻ c, F c = ∑' k : Fin r → ℤ,
      ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), F (c + fun i => (k i : ℝ)) := by
  rw [← ZSpan.fundamentalDomain_pi_basisFun]
  set b := Pi.basisFun ℝ (Fin r)
  have hD := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin r → ℝ))
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hmem : ∀ k : Fin r → ℤ, (fun i => (k i : ℝ)) ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    intro k
    rw [Submodule.mem_toAddSubgroup, b.mem_span_iff_repr_mem ℤ]
    intro i
    rw [Pi.basisFun_repr]
    exact ⟨k i, rfl⟩
  let e : (Fin r → ℤ) ≃ (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    Equiv.ofBijective (fun k => ⟨fun i => (k i : ℝ), hmem k⟩)
      ⟨fun k l h => funext fun i => by
        exact Int.cast_injective (α := ℝ) (congrFun (congrArg Subtype.val h) i),
      fun g => by
        have hg : ∀ i, ∃ k : ℤ, (g : Fin r → ℝ) i = k := by
          intro i
          obtain ⟨k, hk⟩ := (b.mem_span_iff_repr_mem ℤ (g : Fin r → ℝ)).1 g.2 i
          exact ⟨k, by simpa [b] using hk.symm⟩
        choose k hk using hg
        exact ⟨k, Subtype.ext (funext fun i => (hk i).symm)⟩⟩
  rw [hD.lintegral_eq_tsum', ← (e.trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun k => ?_
  refine lintegral_congr fun c => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, e,
    ]
  rw [add_comm]
  rfl

theorem continuous_thetaTerm (x : K) : Continuous (thetaTerm x) := by
  unfold thetaTerm
  fun_prop

theorem measurable_ofReal_thetaTerm (x : K) (y : ℝ) :
    Measurable fun c : Fin (rank K) → ℝ => ENNReal.ofReal (thetaTerm x (unitScale K y c)) :=
  ((continuous_thetaTerm x).comp (continuous_unitScale y)).measurable.ennreal_ofReal

variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

instance : Countable K :=
  Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)

instance (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Countable (Orbits a) :=
  (Set.countable_range (idealOf a)).to_subtype

/-- The theta function minus its constant term is the sum over the nonzero elements. -/
theorem ofReal_dedekindTheta_sub_one {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ENNReal.ofReal (dedekindTheta K a t - 1) =
      ∑' α : NonzeroElt a, ENNReal.ofReal (thetaTerm (α : K) t) := by
  have h1 : ENNReal.ofReal (dedekindTheta K a t) =
      ∑' α : (a : FractionalIdeal (𝓞 K)⁰ K), ENNReal.ofReal (thetaTerm (α : K) t) :=
    ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (summable_dedekindTheta a ht)
  let z : (a : FractionalIdeal (𝓞 K)⁰ K) :=
    ⟨0, show (0 : K) ∈ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) from
      Submodule.zero_mem _⟩
  rw [ENNReal.tsum_eq_add_tsum_ite z] at h1
  have h0 : thetaTerm ((z : (a : FractionalIdeal (𝓞 K)⁰ K)) : K) t = 1 := by
    simp [thetaTerm, z]
  rw [ENNReal.ofReal_sub _ zero_le_one, h1, h0, ENNReal.ofReal_one,
    ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  refine Eq.trans ?_ (tsum_subtype {α : (a : FractionalIdeal (𝓞 K)⁰ K) | (α : K) ≠ 0}
    (fun α => ENNReal.ofReal (thetaTerm (α : K) t))).symm
  refine tsum_congr fun α => ?_
  have hz : α = z ↔ (α : K) = 0 := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : (α : K) = 0
  · simp [hz.2 h, Set.indicator, z]
  · simp [mt hz.1 h, h]

/-- **The unfolding of the unit theta function.** For $y > 0$, $$\int_{[0, 1)^r} (\theta_{\mathfrak{a}}(t(y, c)) - 1) \, dc = w_K \sum_{I} \int_{\mathbb{R}^r} e^{-\pi \sum_w n_w t(y, c)_w |\alpha_I|_w^2} \, dc,$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem lintegral_unitCube_eq_tsum {y : ℝ} (hy : 0 < y) :
    ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ENNReal.ofReal (dedekindTheta K a (unitScale K y c) - 1) =
      ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
        ∫⁻ c, ENNReal.ofReal (thetaTerm (orbitRep a I : K) (unitScale K y c)) := by
  calc ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
        ENNReal.ofReal (dedekindTheta K a (unitScale K y c) - 1)
      = ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ∑' α : NonzeroElt a, ENNReal.ofReal (thetaTerm (α : K) (unitScale K y c)) :=
        lintegral_congr fun c => ofReal_dedekindTheta_sub_one (unitScale_pos hy c)
    _ = ∑' α : NonzeroElt a, ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ENNReal.ofReal (thetaTerm (α : K) (unitScale K y c)) :=
        lintegral_tsum fun α => (measurable_ofReal_thetaTerm _ y).aemeasurable
    _ = ∑' I : Orbits a, ∑' β : (orbitOf a ⁻¹' {I}), ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
          ENNReal.ofReal (thetaTerm ((β.1 : NonzeroElt a) : K) (unitScale K y c)) :=
        (ENNReal.tsum_fiberwise _ (orbitOf a)).symm
    _ = ∑' I : Orbits a, ∑' p : torsion K × (Fin (rank K) → ℤ),
          ∫⁻ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1),
            ENNReal.ofReal (thetaTerm (orbitRep a I : K) (unitScale K y (c + fun i => (p.2 i : ℝ)))) := by
        refine tsum_congr fun I => ?_
        rw [← ((unitsEquiv K).trans (unitsEquivFiber I)).tsum_eq]
        refine tsum_congr fun p => ?_
        refine lintegral_congr fun c => ?_
        rw [Equiv.trans_apply, coe_unitsEquivFiber, thetaTerm_unitsEquiv]
    _ = ∑' I : Orbits a, ∑' _ : torsion K,
          ∫⁻ c, ENNReal.ofReal (thetaTerm (orbitRep a I : K) (unitScale K y c)) := by
        refine tsum_congr fun I => ?_
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun _ => ?_
        rw [lintegral_eq_tsum_unitCube]
    _ = ∑' I : Orbits a, (torsionOrder K : ℝ≥0∞) *
          ∫⁻ c, ENNReal.ofReal (thetaTerm (orbitRep a I : K) (unitScale K y c)) := by
        refine tsum_congr fun I => ?_
        have := Fintype.ofFinite (torsion K)
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
          Nat.card_eq_fintype_card]

end Unfold

section Mellin

variable {a : (FractionalIdeal (𝓞 K)⁰ K)ˣ}

theorem continuous_thetaTerm_unitScale (x : K) :
    Continuous fun p : ℝ × (Fin (rank K) → ℝ) => thetaTerm x (unitScale K p.1 p.2) := by
  refine (continuous_thetaTerm x).comp (continuous_pi fun w => ?_)
  unfold unitScale
  fun_prop

theorem integral_unitCube_sub_one {y : ℝ} (hy : 0 < y) :
    ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), (dedekindTheta K a (unitScale K y c) - 1) =
      unitTheta K a y - 1 := by
  rw [integral_sub (integrableOn_dedekindTheta_unitScale a hy)
    (integrableOn_const volume_unitCube_ne_top), setIntegral_const, volume_real_unitCube,
    one_smul, unitTheta]

/-- **The unit theta function as a sum over the orbits.** For $y > 0$, $$\Theta_{\mathfrak{a}}(y) - 1 = w_K \sum_I \int_{\mathbb{R}^r} e^{-\pi \sum_w n_w t(y, c)_w |\alpha_I|_w^2} \, dc.$$ -/
theorem hasSum_unitTheta_sub_one {y : ℝ} (hy : 0 < y) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℝ) *
        ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c))
      (unitTheta K a y - 1) := by
  set L : Orbits a → ℝ≥0∞ := fun I =>
    ∫⁻ c, ENNReal.ofReal (thetaTerm (orbitRep a I : K) (unitScale K y c)) with hL
  have hX : 0 ≤ unitTheta K a y - 1 := sub_nonneg.2 (one_le_unitTheta a hy).1
  have hint : IntegrableOn (fun c => dedekindTheta K a (unitScale K y c) - 1)
      (Set.pi univ fun _ : Fin (rank K) => Ico (0 : ℝ) 1) :=
    (integrableOn_dedekindTheta_unitScale a hy).sub (integrableOn_const volume_unitCube_ne_top)
  have hE : ENNReal.ofReal (unitTheta K a y - 1) = ∑' I, (torsionOrder K : ℝ≥0∞) * L I := by
    rw [← integral_unitCube_sub_one hy, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun c => sub_nonneg.2 (one_le_dedekindTheta a (unitScale_pos hy c))),
      lintegral_unitCube_eq_tsum hy]
  have hfin : ∑' I, (torsionOrder K : ℝ≥0∞) * L I ≠ ⊤ := by
    rw [← hE]
    exact ENNReal.ofReal_ne_top
  have hw : (torsionOrder K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hLfin : ∀ I, L I ≠ ⊤ := fun I h => hfin (ENNReal.tsum_eq_top_of_eq_top
    ⟨I, by rw [h, ENNReal.mul_top hw]⟩)
  have hInt : ∀ I : Orbits a, Integrable fun c => thetaTerm (orbitRep a I : K) (unitScale K y c) :=
    fun I => ⟨((continuous_thetaTerm _).comp (continuous_unitScale y)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun c => (Real.exp_pos _).le)).2
        (lt_top_iff_ne_top.2 (hLfin I))⟩
  have hofReal : ∀ I : Orbits a, ENNReal.ofReal ((torsionOrder K : ℝ) *
      ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c)) = (torsionOrder K : ℝ≥0∞) * L I := by
    intro I
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ofReal_integral_eq_lintegral_ofReal (hInt I)
        (Eventually.of_forall fun c => (Real.exp_pos _).le)]
  have hnn : ∀ I : Orbits a, 0 ≤ (torsionOrder K : ℝ) *
      ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c) :=
    fun I => mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun c => (Real.exp_pos _).le)
  have hsum : Summable fun I : Orbits a => (torsionOrder K : ℝ) *
      ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c) := by
    refine (ENNReal.summable_toReal hfin).congr fun I => ?_
    rw [← hofReal, ENNReal.toReal_ofReal (hnn I)]
  refine hsum.hasSum_iff.2 ?_
  rw [← ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn) hX, ENNReal.ofReal_tsum_of_nonneg hnn hsum,
    hE]
  exact tsum_congr hofReal

theorem measurable_integral_thetaTerm (x : K) :
    Measurable fun y : ℝ => ∫ c : Fin (rank K) → ℝ, (thetaTerm x (unitScale K y c) : ℂ) :=
  (StronglyMeasurable.integral_prod_right' (f := fun p : ℝ × (Fin (rank K) → ℝ) =>
    (thetaTerm x (unitScale K p.1 p.2) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_thetaTerm_unitScale x)).stronglyMeasurable).measurable

/-- **The Mellin transform of the unit theta function as a Dirichlet series.** For $\mathrm{Re}\, s > n/2$ and $s' = 2s/n$, $$\Lambda_{\mathfrak{a}}(s) = \frac{w_K}{2^{r - r_2} n R_K} \, \Gamma_K(s') \sum_I |N(\alpha_I)|^{-s'},$$ where $I$ runs over the integral ideals with $\mathfrak{a} I = (\alpha_I)$ principal. -/
theorem hasSum_Λ_unitThetaFEPair {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (gammaK K (2 * s / finrank ℚ K) *
        ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) /
          ((unitConst K * 2 ^ rank K : ℝ) : ℂ))
      ((unitThetaFEPair a).Λ s) := by
  have hM := (unitThetaFEPair a).hasMellin (s := s) hs
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  set g : Orbits a → ℝ → ℂ := fun I y => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
    ∫ c : Fin (rank K) → ℝ, (thetaTerm (orbitRep a I : K) (unitScale K y c) : ℂ)) with hg
  have hpt : ∀ y ∈ Ioi (0 : ℝ), HasSum (fun I => g I y)
      ((y : ℂ) ^ (s - 1) • ((unitThetaFEPair a).f y - (unitThetaFEPair a).f₀)) := by
    intro y hy
    have h := ((hasSum_unitTheta_sub_one (a := a) hy).mapL Complex.ofRealCLM).mul_left
      ((y : ℂ) ^ (s - 1))
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_sub, Complex.ofReal_one] at h
    have e1 : (fun I => g I y) = fun I => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        ((∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c) : ℝ) : ℂ)) :=
      funext fun I => by rw [hg]; beta_reduce; rw [integral_complex_ofReal]
    rw [e1, smul_eq_mul]
    exact h
  have hmeas : ∀ I, AEStronglyMeasurable (g I) (volume.restrict (Ioi (0 : ℝ))) := fun I =>
    ((Complex.measurable_ofReal.pow_const (s - 1)).mul
      (measurable_const.mul (measurable_integral_thetaTerm _))).aestronglyMeasurable
  have hnorm : ∀ y ∈ Ioi (0 : ℝ), ∑' I, ‖g I y‖ₑ =
      ‖(y : ℂ) ^ (s - 1) • ((unitThetaFEPair a).f y - (unitThetaFEPair a).f₀)‖ₑ := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have h := (hasSum_unitTheta_sub_one (a := a) hy').mul_left (y ^ (s.re - 1))
    have hnn : ∀ I : Orbits a, 0 ≤ y ^ (s.re - 1) * ((torsionOrder K : ℝ) *
        ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c)) := fun I =>
      mul_nonneg (Real.rpow_nonneg hy'.le _)
        (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun c => (Real.exp_pos _).le))
    have hgI : ∀ I, ‖g I y‖ₑ = ENNReal.ofReal (y ^ (s.re - 1) * ((torsionOrder K : ℝ) *
        ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c))) := by
      intro I
      have hw0 : 0 ≤ (torsionOrder K : ℝ) * ∫ c, thetaTerm (orbitRep a I : K) (unitScale K y c) :=
        mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun c => (Real.exp_pos _).le)
      rw [← ofReal_norm, hg]
      beta_reduce
      congr 1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy', Complex.sub_re, Complex.one_re,
        integral_complex_ofReal, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg hw0]
    simp_rw [hgI]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn h.summable, h.tsum_eq, ← ofReal_norm]
    congr 1
    have hX : 0 ≤ unitTheta K a y - 1 := sub_nonneg.2 (one_le_unitTheta a hy').1
    change _ = ‖(y : ℂ) ^ (s - 1) • ((unitTheta K a y : ℂ) - 1)‖
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy', Complex.sub_re, Complex.one_re,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hX]
  have hfin : ∑' I, ∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun I => (hmeas I).enorm,
      setLIntegral_congr_fun measurableSet_Ioi hnorm]
    exact (hM.1.hasFiniteIntegral).ne
  have hterm : ∀ I : Orbits a, ∫ y in Ioi (0 : ℝ), g I y =
      (torsionOrder K : ℂ) * (gammaK K (2 * s / finrank ℚ K) *
        ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))) /
          ((unitConst K * 2 ^ rank K : ℝ) : ℂ) := by
    intro I
    have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
    rw [← integral_unitScale hs0 (orbitRep a I).2, eq_div_iff hC]
    simp only [hg]
    rw [show (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((torsionOrder K : ℂ) *
        ∫ c : Fin (rank K) → ℝ, (thetaTerm (orbitRep a I : K) (unitScale K y c) : ℂ))) =
        fun y : ℝ => (torsionOrder K : ℂ) * ((y : ℂ) ^ (s - 1) *
        ∫ c : Fin (rank K) → ℝ, (thetaTerm (orbitRep a I : K) (unitScale K y c) : ℂ)) from
      funext fun y => by ring, integral_const_mul]
    ring
  have hsum : Summable fun I => ∫ y in Ioi (0 : ℝ), g I y := by
    refine Summable.of_norm_bounded (g := fun I => (∫⁻ y in Ioi (0 : ℝ), ‖g I y‖ₑ).toReal)
      (ENNReal.summable_toReal hfin) fun I => ?_
    exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
  have heq := integral_tsum hmeas hfin
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => (hpt y hy).tsum_eq] at heq
  have hΛ : (unitThetaFEPair a).Λ s = ∑' I, ∫ y in Ioi (0 : ℝ), g I y := by
    rw [← hM.2, mellin, heq]
  rw [hΛ]
  exact (hsum.hasSum).congr_fun fun I => (hterm I).symm

end Mellin

end Langlands.Tate
