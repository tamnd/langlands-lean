/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Hecke
import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
import Mathlib

/-!
# Haar measures on a nonarchimedean completion of a number field

Let $K$ be a number field and let $v$ be a finite place of $K$, given as a height one prime $\mathfrak{p}_v$ of $\mathcal{O}_K$. Let $K_v$ be the completion `v.adicCompletion K` and let $\mathcal{O}_v$ be its ring of integers. Write $q = N(v) = |\mathcal{O}_K / \mathfrak{p}_v|$. This file sets up the measure theory on $K_v$ that the local part of Tate's thesis needs.

## Conventions

* The absolute value $|x|_v$ is the norm `‖x‖` of the normed field structure of Mathlib on $K_v$ (`NumberField.instNormedFieldValuedAdicCompletion`). It is normalized: $|x|_v = q^{-v(x)}$, so that $|\varpi_v|_v = q^{-1}$ for a uniformizer $\varpi_v$ (`norm_localUniformizer`). With this normalization the product formula holds.
* The additive measure `haar v` is the Haar measure $dx$ with $\mu(\mathcal{O}_v) = 1$. It is not the self dual measure for the standard additive character. The self dual measure is $N(\mathfrak{d}_v)^{-1/2} dx$, where $\mathfrak{d}_v$ is the local different, so the two agree at the places where $K$ is unramified over $\mathbb{Q}$.
* The multiplicative measure `multHaar v` is $d^\times x = (1 - q^{-1})^{-1} |x|_v^{-1} dx$. It is a measure on $K_v$ with $d^\times x(\{0\}) = 0$, so it is a measure on $K_v^\times$, and $\int_{\mathcal{O}_v^\times} d^\times x = 1$.
* The $\sigma$-algebra on $K_v$ is the Borel $\sigma$-algebra.

The sets of $K_v$ are written with the metric: $\mathcal{O}_v$ is `closedBall 0 1`, the maximal ideal $\mathfrak{p}_v$ is `ball 0 1`, the units $\mathcal{O}_v^\times$ are `sphere 0 1`, and $\mathfrak{p}_v^m$ is `closedBall 0 (q⁻¹ ^ m)`. The lemma `coe_adicCompletionIntegers` identifies `v.adicCompletionIntegers K` with the closed unit ball.

## Main results

* `haar_ball_one`: $\mu(\mathfrak{p}_v) = q^{-1}$.
* `distribHaarChar_eq_nnnorm`: the modulus of the action of $a \in K_v^\times$ on $K_v$ is $|a|_v$.
* `addHaar_smul_of_ne_zero` and `haar_smul`: $\mu(aE) = |a|_v \mu(E)$ for every Haar measure $\mu$ and $a \neq 0$.
* `haar_closedBall_pow`: $\mu(\mathfrak{p}_v^m) = q^{-m}$.
* `haar_sphere_one`: $\mu(\mathcal{O}_v^\times) = 1 - q^{-1}$.
* `multHaar_sphere_norm`: every shell $a \mathcal{O}_v^\times$ has measure $1$ for $d^\times x$; in particular $\int_{\mathcal{O}_v^\times} d^\times x = 1$ (`multHaar_sphere_one`).

## Proofs

The ring $\mathcal{O}_v$ is compact because $K_v$ is a proper metric space (`adicCompletionProperSpace` of the ported NYLL library). The key computation is $\mu(\mathfrak{p}_v) = q^{-1}$. The residue field $\mathcal{O}_v / \mathfrak{p}_v$ has $q$ elements, because it is isomorphic to $\mathcal{O}_K / \mathfrak{p}_v$. So $\mathcal{O}_v$ is the disjoint union of $q$ cosets $c + \mathfrak{p}_v$, and by translation invariance all of them have measure $\mu(\mathfrak{p}_v)$.

For the scaling law we use the modulus `MeasureTheory.distribHaarChar` of Mathlib. It is a homomorphism $K_v^\times \to \mathbb{R}_{>0}$ with $\mu(aE) = \mathrm{mod}(a) \mu(E)$. A unit $u$ of $\mathcal{O}_v$ has $u \mathcal{O}_v = \mathcal{O}_v$, so $\mathrm{mod}(u) = 1$. A uniformizer $\varpi$ has $\varpi \mathcal{O}_v = \mathfrak{p}_v$, so $\mathrm{mod}(\varpi) = q^{-1}$. Every $a \in K_v^\times$ is $u \varpi^k$, so $\mathrm{mod}(a) = q^{-k} = |a|_v$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.2.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, chapter 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The Borel $\sigma$-algebra on $K_v$. -/
noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _
/-- The $\sigma$-algebra on $K_v$ is the Borel $\sigma$-algebra. -/
instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- The norm $q = N(v) = |\mathcal{O}_K / \mathfrak{p}_v|$ of the place $v$, as a real number. It is the order of the residue field of $K_v$. -/
noncomputable abbrev q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

/-- The norm $N(v)$ is greater than $1$. -/
theorem one_lt_q : 1 < q v := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v

/-- The norm $N(v)$ is positive. -/
theorem q_pos : 0 < q v := zero_lt_one.trans (one_lt_q v)

/-- The absolute value of a nonzero element of $K_v$ is an integral power of $N(v)$. -/
theorem exists_norm_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = q v ^ k := by
  refine ⟨WithZero.log (Valued.v x), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).2 hx)]
  push_cast
  rfl

/-- The values of the absolute value are discrete: $|x|_v < 1$ if and only if $|x|_v \leq N(v)^{-1}$. -/
theorem norm_lt_one_iff_le {x : v.adicCompletion K} : ‖x‖ < 1 ↔ ‖x‖ ≤ (q v)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, (q_pos v).le]
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow v hx
  rw [hk, ← zpow_neg_one, zpow_lt_one_iff_right₀ (one_lt_q v), zpow_le_zpow_iff_right₀ (one_lt_q v)]
  omega

/-- The uniformizer $\varpi_v$ of `Langlands.localUniformizer` has $|\varpi_v|_v = N(v)^{-1}$. -/
theorem norm_localUniformizer :
    ‖(localUniformizer K v : v.adicCompletion K)‖ = (q v)⁻¹ := by
  have h := (v.valuation_exists_uniformizer K).choose_spec
  have h2 : Valued.v (localUniformizer K v : v.adicCompletion K) = WithZero.exp (-1) := by
    rw [← h]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [FinitePlace.norm_def, h2, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp

/-- The ring of integers $\mathcal{O}_v$, the closed unit ball, as a compact set with nonempty interior. -/
noncomputable def integersPositiveCompacts :
    TopologicalSpace.PositiveCompacts (v.adicCompletion K) where
  carrier := closedBall 0 1
  isCompact' := isCompact_closedBall 0 1
  interior_nonempty' := ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩

/-- The additive Haar measure $dx$ on $K_v$ with $\mu(\mathcal{O}_v) = 1$. -/
noncomputable def haar : Measure (v.adicCompletion K) :=
  Measure.addHaarMeasure (integersPositiveCompacts v)

/-- The measure $dx$ is an additive Haar measure. -/
instance : (haar v).IsAddHaarMeasure := by unfold haar; infer_instance
/-- The measure $dx$ is regular. -/
instance : (haar v).Regular := by unfold haar; infer_instance

/-- The normalization $\mu(\mathcal{O}_v) = 1$. -/
theorem haar_closedBall_one : haar v (closedBall 0 1) = 1 :=
  Measure.addHaarMeasure_self

/-- Two integers of $K_v$ have the same residue class if and only if their difference has absolute value less than $1$. -/
theorem residue_eq_residue_iff (y c : Valued.integer (v.adicCompletion K)) :
    IsLocalRing.residue _ y = IsLocalRing.residue _ c ↔
      ‖(y : v.adicCompletion K) - c‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    Valued.toNormedField.norm_lt_one_iff]
  rfl

/-- The residue field of $K_v$ has $N(v)$ elements. -/
theorem natCard_residueField :
    Nat.card (Valued.ResidueField (v.adicCompletion K)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField v).toEquiv.symm


/-- The maximal ideal has measure $\mu(\mathfrak{p}_v) = N(v)^{-1}$. The ring $\mathcal{O}_v$ is the disjoint union of the $N(v)$ cosets of $\mathfrak{p}_v$, and these cosets have the same measure. -/
theorem haar_ball_one : haar v (ball 0 1) = ENNReal.ofReal (q v)⁻¹ := by
  let 𝓀 := Valued.ResidueField (v.adicCompletion K)
  have : Finite 𝓀 := finite_adicCompletion_residueField K v
  let : Fintype 𝓀 := Fintype.ofFinite 𝓀
  choose c hc using IsLocalRing.residue_surjective (R := Valued.integer (v.adicCompletion K))
  have hU : closedBall (0 : v.adicCompletion K) 1 = ⋃ k : 𝓀, ball (c k : v.adicCompletion K) 1 := by
    ext x
    simp only [mem_closedBall_zero_iff, Set.mem_iUnion, mem_ball, dist_eq_norm]
    constructor
    · intro hx
      have hx' : x ∈ Valued.integer (v.adicCompletion K) :=
        (Valued.toNormedField.norm_le_one_iff).1 hx
      refine ⟨IsLocalRing.residue _ ⟨x, hx'⟩, ?_⟩
      have := (residue_eq_residue_iff v ⟨x, hx'⟩ (c (IsLocalRing.residue _ ⟨x, hx'⟩))).1
        (hc _).symm
      exact this
    · rintro ⟨k, hk⟩
      have hck : ‖(c k : v.adicCompletion K)‖ ≤ 1 :=
        (Valued.toNormedField.norm_le_one_iff).2 (c k).2
      calc ‖x‖ = ‖(x - c k) + c k‖ := by rw [sub_add_cancel]
        _ ≤ max ‖x - c k‖ ‖(c k : v.adicCompletion K)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le hk.le hck
  have hD : Pairwise (Function.onFun Disjoint fun k : 𝓀 => ball (c k : v.adicCompletion K) 1) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun x hxk hxl => hkl ?_
    rw [mem_ball, dist_eq_norm] at hxk hxl
    rw [← hc k, ← hc l, residue_eq_residue_iff]
    calc ‖(c k : v.adicCompletion K) - c l‖ = ‖-(x - c k) + (x - c l)‖ := by congr 1; ring
      _ ≤ max ‖-(x - c k)‖ ‖x - c l‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := by rw [norm_neg]; exact max_lt hxk hxl
  have hB (k : 𝓀) : haar v (ball (c k : v.adicCompletion K) 1) = haar v (ball 0 1) := by
    have : ball (c k : v.adicCompletion K) 1 = (fun x => x + -(c k : v.adicCompletion K)) ⁻¹' ball 0 1 := by
      ext x; simp [dist_eq_norm, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have h1 := haar_closedBall_one v
  rw [hU, measure_iUnion hD (fun _ => measurableSet_ball), funext hB, ENNReal.tsum_const,
    ENat.card_eq_coe_natCard, natCard_residueField] at h1
  rw [ENNReal.ofReal_inv_of_pos (q_pos v), ENNReal.ofReal_natCast]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast h1)


/-- If $|\varpi|_v = N(v)^{-1}$, then $\varpi \mathcal{O}_v = \mathfrak{p}_v$. -/
theorem ball_one_eq_smul {ϖ : v.adicCompletion K} (hϖ : ‖ϖ‖ = (q v)⁻¹) :
    ϖ • closedBall (0 : v.adicCompletion K) 1 = ball 0 1 := by
  rw [smul_unitClosedBall, hϖ]
  ext x
  simp [norm_lt_one_iff_le v]


/-- To compute the modulus of $a$, it is sufficient to compute the measure of $a \mathcal{O}_v$. -/
theorem distribHaarChar_eq_of_smul (a : (v.adicCompletion K)ˣ) (r : ℝ≥0)
    (h : haar v ((a : v.adicCompletion K) • closedBall 0 1) = r) :
    distribHaarChar (v.adicCompletion K) a = r := by
  have h0 : haar v (closedBall 0 1) ≠ 0 := by rw [haar_closedBall_one]; exact one_ne_zero
  have h1 : haar v (closedBall 0 1) ≠ ∞ := by rw [haar_closedBall_one]; exact ENNReal.one_ne_top
  apply distribHaarChar_eq_of_measure_smul_eq_mul h0 h1
  rw [haar_closedBall_one, mul_one]
  exact h


/-- A unit $u$ of $\mathcal{O}_v$ has modulus $1$, because $u \mathcal{O}_v = \mathcal{O}_v$. -/
theorem distribHaarChar_of_norm_eq_one (u : (v.adicCompletion K)ˣ)
    (hu : ‖(u : v.adicCompletion K)‖ = 1) :
    distribHaarChar (v.adicCompletion K) u = 1 := by
  apply distribHaarChar_eq_of_smul
  rw [smul_unitClosedBall, hu, haar_closedBall_one, ENNReal.coe_one]

/-- An element of absolute value $N(v)^{-1}$ has modulus $N(v)^{-1}$. -/
theorem distribHaarChar_of_norm_eq_inv_q (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : ‖(ϖ : v.adicCompletion K)‖ = (q v)⁻¹) :
    distribHaarChar (v.adicCompletion K) ϖ = (q v).toNNReal⁻¹ := by
  apply distribHaarChar_eq_of_smul
  rw [ball_one_eq_smul v hϖ, haar_ball_one, ENNReal.ofReal_inv_of_pos (q_pos v), ENNReal.ofReal,
    ENNReal.coe_inv (Real.toNNReal_pos.2 (q_pos v)).ne']

/-- The modulus of $K_v$ is the normalized absolute value: $\mathrm{mod}_{K_v}(a) = |a|_v$. -/
theorem distribHaarChar_eq_nnnorm (a : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) a = ‖(a : v.adicCompletion K)‖₊ := by
  set ϖ := localUniformizer K v
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow v a.ne_zero
  have hu : ‖((a * ϖ ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
    rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, norm_localUniformizer, hk,
      inv_zpow', ← zpow_add₀ (q_pos v).ne', add_neg_cancel, zpow_zero]
  have ha : a = (a * ϖ ^ k) * ϖ ^ (-k) := by group
  rw [ha, map_mul, map_zpow, distribHaarChar_of_norm_eq_one v _ hu,
    distribHaarChar_of_norm_eq_inv_q v ϖ (norm_localUniformizer v), one_mul, ← ha]
  ext
  rw [NNReal.coe_zpow, NNReal.coe_inv, Real.coe_toNNReal _ (q_pos v).le, coe_nnnorm, hk, inv_zpow',
    neg_neg]

/-- The scaling law for every Haar measure $\mu$ on $K_v$: $\mu(aE) = |a|_v \mu(E)$ for $a \neq 0$. -/
theorem addHaar_smul_of_ne_zero (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    {a : v.adicCompletion K} (ha : a ≠ 0) (E : Set (v.adicCompletion K)) :
    μ (a • E) = ENNReal.ofReal ‖a‖ * μ E := by
  have h := distribHaarChar_mul μ (Units.mk0 a ha) E
  rw [distribHaarChar_eq_nnnorm, Units.val_mk0] at h
  have hE : (Units.mk0 a ha • E) = a • E := rfl
  rw [hE] at h
  rw [← h, ofReal_norm]
  rfl

/-- The scaling law $\mu(aE) = |a|_v \mu(E)$ for $a \neq 0$. -/
theorem haar_smul {a : v.adicCompletion K} (ha : a ≠ 0) (E : Set (v.adicCompletion K)) :
    haar v (a • E) = ENNReal.ofReal ‖a‖ * haar v E :=
  addHaar_smul_of_ne_zero v (haar v) ha E

/-- The ball $a \mathcal{O}_v$ has measure $|a|_v$. -/
theorem haar_closedBall_norm {a : v.adicCompletion K} (ha : a ≠ 0) :
    haar v (closedBall 0 ‖a‖) = ENNReal.ofReal ‖a‖ := by
  rw [← smul_unitClosedBall, haar_smul v ha, haar_closedBall_one, mul_one]

/-- The ideal $\mathfrak{p}_v^m$, the ball of radius $N(v)^{-m}$, has measure $N(v)^{-m}$. -/
theorem haar_closedBall_pow (m : ℕ) :
    haar v (closedBall 0 ((q v)⁻¹ ^ m)) = ENNReal.ofReal ((q v)⁻¹ ^ m) := by
  have h : ((localUniformizer K v : v.adicCompletion K) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have := haar_closedBall_norm v h
  rwa [norm_pow, norm_localUniformizer] at this

/-- The units have measure $\mu(\mathcal{O}_v^\times) = 1 - N(v)^{-1}$. -/
theorem haar_sphere_one : haar v (sphere 0 1) = ENNReal.ofReal (1 - (q v)⁻¹) := by
  rw [← closedBall_sdiff_ball, measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
    (by rw [haar_ball_one]; exact ENNReal.ofReal_ne_top), haar_closedBall_one, haar_ball_one,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by have := q_pos v; positivity)]

/-- The shell $a \mathcal{O}_v^\times = \{x : |x|_v = |a|_v\}$ has measure $|a|_v (1 - N(v)^{-1})$. -/
theorem haar_sphere_norm {a : v.adicCompletion K} (ha : a ≠ 0) :
    haar v (sphere 0 ‖a‖) = ENNReal.ofReal (‖a‖ * (1 - (q v)⁻¹)) := by
  have h := smul_sphere' ha (0 : v.adicCompletion K) 1
  rw [smul_zero, mul_one] at h
  rw [← h, haar_smul v ha, haar_sphere_one, ← ENNReal.ofReal_mul (norm_nonneg _)]


/-- The ring `v.adicCompletionIntegers K` is the closed unit ball of $K_v$. -/
theorem coe_adicCompletionIntegers :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = closedBall 0 1 := by
  ext x
  rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

/-- The number $1 - N(v)^{-1}$ is positive. -/
theorem one_sub_inv_q_pos : 0 < 1 - (q v)⁻¹ := by
  have := one_lt_q v
  rw [sub_pos]
  exact inv_lt_one_of_one_lt₀ this

/-- The multiplicative measure $d^\times x = (1 - N(v)^{-1})^{-1} |x|_v^{-1} dx$ on $K_v$. Its density is zero at $x = 0$, so it is a measure on $K_v^\times$. -/
noncomputable def multHaar : Measure (v.adicCompletion K) :=
  (haar v).withDensity fun x => ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖x‖⁻¹)

/-- On a set where $|x|_v = r$, the measure $d^\times x$ is $(1 - N(v)^{-1})^{-1} r^{-1} dx$. -/
theorem multHaar_apply_of_subset_sphere {E : Set (v.adicCompletion K)} (hE : MeasurableSet E)
    {r : ℝ} (h : E ⊆ sphere 0 r) :
    multHaar v E = ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * r⁻¹) * haar v E := by
  rw [multHaar, withDensity_apply _ hE]
  rw [setLIntegral_congr_fun hE (g := fun _ => ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * r⁻¹))
    (fun x hx => by rw [mem_sphere_zero_iff_norm.1 (h hx)]), setLIntegral_const]

/-- The point $0$ has measure zero for $d^\times x$. -/
theorem multHaar_singleton_zero : multHaar v {0} = 0 := by
  rw [multHaar_apply_of_subset_sphere v isClosed_singleton.measurableSet (r := 0) (by simp)]
  simp

/-- Each shell $a \mathcal{O}_v^\times$ has measure $1$ for $d^\times x$. -/
theorem multHaar_sphere_norm {a : v.adicCompletion K} (ha : a ≠ 0) :
    multHaar v (sphere 0 ‖a‖) = 1 := by
  have h1 := one_sub_inv_q_pos v
  have h2 : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [multHaar_apply_of_subset_sphere v isClosed_sphere.measurableSet subset_rfl,
    haar_sphere_norm v ha, ← ENNReal.ofReal_mul (by positivity)]
  rw [show (1 - (q v)⁻¹)⁻¹ * ‖a‖⁻¹ * (‖a‖ * (1 - (q v)⁻¹)) = 1 by
    rw [mul_assoc, ← mul_assoc ‖a‖⁻¹, inv_mul_cancel₀ h2.ne', one_mul, inv_mul_cancel₀ h1.ne']]
  exact ENNReal.ofReal_one

/-- The normalization $\int_{\mathcal{O}_v^\times} d^\times x = 1$. -/
theorem multHaar_sphere_one : multHaar v (sphere 0 1) = 1 := by
  simpa using multHaar_sphere_norm v (one_ne_zero (α := v.adicCompletion K))

/-- A nonzero element of $\mathcal{O}_v$ has absolute value $N(v)^{-m}$ for some $m \geq 0$. -/
theorem exists_pow_of_norm_le_one {x : v.adicCompletion K} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = (q v)⁻¹ ^ m := by
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow v hx0
  have hk0 : k ≤ 0 := by
    rw [hk] at hx
    by_contra h
    exact absurd hx (not_le.2 (one_lt_zpow₀ (one_lt_q v) (by omega)))
  refine ⟨(-k).toNat, ?_⟩
  rw [hk, inv_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, inv_inv]

end Langlands.Tate.NonArchimedean
