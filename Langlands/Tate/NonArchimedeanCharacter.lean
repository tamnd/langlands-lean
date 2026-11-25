/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.NonArchimedeanZeta

/-!
# Characters of a nonarchimedean completion and ramified zeta integrals

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$, unit group $\mathcal{O}_v^\times$, uniformizer $\varpi$ and residue field of size $q = N(v)$. We use the additive measure $dx$ with $\int_{\mathcal{O}_v} dx = 1$ and the multiplicative measure $d^\times x = (1 - q^{-1})^{-1} |x|_v^{-1} dx$ of `Langlands.Tate.NonArchimedeanMeasure`. For a character $\chi$ of $K_v^\times$ the local zeta integral is
$$Z(f, \chi, s) = \int_{K_v^\times} f(x) \chi(x) |x|_v^s \, d^\times x.$$

## Invariance of the measures

For $a \in K_v^\times$ the image of $dx$ under $x \mapsto a x$ is $|a|_v^{-1} dx$. The density $|x|_v^{-1}$ has the inverse behaviour, so $d^\times x$ is invariant: $\int g(a x) \, d^\times x = \int g(x) \, d^\times x$. This gives the scaling law
$$Z(f, \chi, s) = \chi(a) |a|_v^s Z(f(a \cdot), \chi, s).$$

## Ramified characters

Suppose that $\chi(u) \neq 1$ for some $u \in \mathcal{O}_v^\times$. The function $f = \mathbf{1}_{\mathcal{O}_v}$ satisfies $f(u x) = f(x)$, and $|u x|_v = |x|_v$. So the substitution $x \mapsto u x$ gives $Z(f, \chi, s) = \chi(u) Z(f, \chi, s)$, and hence $Z(f, \chi, s) = 0$. The argument needs no integrability: if the integrand is not integrable, then both sides are $0$ by the convention for the Bochner integral. So at a ramified place the zeta integral of $\mathbf{1}_{\mathcal{O}_v}$ does not give the local factor $L(s, \chi) = 1$, and one must use other test functions.

## Characters trivial on higher units

The group $1 + \mathfrak{p}_v^m$ consists of the units $u$ with $|u - 1|_v \leq q^{-m}$. Every continuous character of $K_v^\times$ is trivial on some $1 + \mathfrak{p}_v^m$, and we use this as the hypothesis `IsTrivialOnHigherUnits`. It has the following consequences.

* $\chi$ is locally constant on $K_v^\times$, so it is continuous there and measurable for $d^\times x$.
* $|\chi(u)| = 1$ for $u \in \mathcal{O}_v^\times$. The image of the compact group $\mathcal{O}_v^\times$ under $|\chi|$ is a bounded subgroup of $\mathbb{R}_{>0}$, and such a subgroup is trivial.
* $|\chi(x)| \leq C |x|_v^{\sigma_0}$ on $\mathcal{O}_v \setminus \{0\}$ with $\sigma_0 = -\log_q |\chi(\varpi)|$. So $\chi(x) |x|_v^s$ is integrable on $\mathcal{O}_v$ for $d^\times x$ when $|\chi(\varpi)| < q^{\mathrm{Re}(s)}$.

An additive character $\psi$ that is trivial on a ball around $0$ is also continuous, and $|\psi(x)| = 1$ by the same argument with a bounded subgroup.

## Main results

* `integral_comp_mul_left`: the invariance of $d^\times x$.
* `zetaIntegral_eq_mul_comp`: the scaling law of $Z(f, \chi, s)$.
* `zetaIntegral_integers_of_ramified`: if $\chi$ is not trivial on $\mathcal{O}_v^\times$, then $Z(\mathbf{1}_{\mathcal{O}_v}, \chi, s) = 0$.
* `zetaIntegral_eq_zero_of_not_isUnramifiedAt`: the same for the local component of a Hecke character that is ramified at $v$.
* `continuousOn_charExt`, `integrableOn_closedBall_one_of_le` and `exists_norm_charExt_le`: continuity and integrability.
* `norm_charExt_of_norm_eq_one` and `norm_addChar_eq_one`: $\chi$ and $\psi$ are unitary.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.3.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, chapter 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The image of $dx$ under $x \mapsto a x$ is $|a|_v^{-1} dx$. -/
theorem map_mul_left_haar {a : v.adicCompletion K} (ha : a ≠ 0) :
    Measure.map (fun x => a * x) (haar v) = ENNReal.ofReal ‖a‖⁻¹ • haar v := by
  ext E hE
  rw [Measure.map_apply (measurable_const_mul a) hE, Measure.smul_apply, smul_eq_mul]
  have h : (fun x => a * x) ⁻¹' E = a⁻¹ • E := Set.preimage_smul₀ ha E
  rw [h, haar_smul v (inv_ne_zero ha), norm_inv]

/-- The change of variables $\int g(a x) \, dx = |a|_v^{-1} \int g(x) \, dx$ for the Lebesgue integral. -/
theorem lintegral_comp_mul_left_haar {a : v.adicCompletion K} (ha : a ≠ 0)
    (g : v.adicCompletion K → ℝ≥0∞) :
    ∫⁻ x, g (a * x) ∂haar v = ENNReal.ofReal ‖a‖⁻¹ * ∫⁻ x, g x ∂haar v := by
  have h := (Homeomorph.mulLeft₀ a ha).measurableEmbedding.lintegral_map (μ := haar v) g
  simp only [Homeomorph.coe_mulLeft₀] at h
  rw [← h, map_mul_left_haar v ha, lintegral_smul_measure, smul_eq_mul]

/-- The change of variables $\int g(a x) \, dx = |a|_v^{-1} \int g(x) \, dx$. -/
theorem integral_comp_mul_left_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : v.adicCompletion K} (ha : a ≠ 0) (g : v.adicCompletion K → E) :
    ∫ x, g (a * x) ∂haar v = ‖a‖⁻¹ • ∫ x, g x ∂haar v := by
  have h := (Homeomorph.mulLeft₀ a ha).measurableEmbedding.integral_map (μ := haar v) g
  simp only [Homeomorph.coe_mulLeft₀] at h
  rw [← h, map_mul_left_haar v ha, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (norm_nonneg a))]

/-- The density of $d^\times x$ with respect to $dx$. -/
theorem density_mul {a : v.adicCompletion K} (ha : a ≠ 0) (x : v.adicCompletion K) :
    ENNReal.ofReal ‖a‖ * ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖a * x‖⁻¹) =
      ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖x‖⁻¹) := by
  rw [← ENNReal.ofReal_mul (norm_nonneg a), norm_mul, mul_inv, mul_left_comm, ← mul_assoc ‖a‖,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 ha), one_mul]

/-- The multiplicative measure $d^\times x$ is invariant under $x \mapsto a x$ for every $a \in K_v^\times$. -/
theorem map_mul_left_multHaar {a : v.adicCompletion K} (ha : a ≠ 0) :
    Measure.map (fun x => a * x) (multHaar v) = multHaar v := by
  ext E hE
  have hm : Measurable fun x : v.adicCompletion K => ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖x‖⁻¹) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_norm.inv)
  rw [Measure.map_apply (measurable_const_mul a) hE, multHaar, withDensity_apply _
    (measurable_const_mul a hE), withDensity_apply _ hE, ← lintegral_indicator
    (measurable_const_mul a hE), ← lintegral_indicator hE]
  have h : ∀ x, ((fun x => a * x) ⁻¹' E).indicator
      (fun x => ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖x‖⁻¹)) x =
      ENNReal.ofReal ‖a‖ *
        E.indicator (fun x => ENNReal.ofReal ((1 - (q v)⁻¹)⁻¹ * ‖x‖⁻¹)) (a * x) := by
    intro x
    by_cases hx : a * x ∈ E
    · rw [Set.indicator_of_mem (show x ∈ (fun x => a * x) ⁻¹' E from hx), Set.indicator_of_mem hx,
        density_mul v ha]
    · rw [Set.indicator_of_notMem (show x ∉ (fun x => a * x) ⁻¹' E from hx),
        Set.indicator_of_notMem hx, mul_zero]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_mul_left_haar v ha, ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg a),
    mul_inv_cancel₀ (norm_ne_zero_iff.2 ha), ENNReal.ofReal_one, one_mul]

/-- The map $x \mapsto a x$ preserves $d^\times x$. -/
theorem measurePreserving_mul_left {a : v.adicCompletion K} (ha : a ≠ 0) :
    MeasurePreserving (fun x => a * x) (multHaar v) (multHaar v) :=
  ⟨measurable_const_mul a, map_mul_left_multHaar v ha⟩

/-- The invariance $\int g(a x) \, d^\times x = \int g(x) \, d^\times x$ for $a \in K_v^\times$. -/
theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : v.adicCompletion K} (ha : a ≠ 0) (g : v.adicCompletion K → E) :
    ∫ x, g (a * x) ∂multHaar v = ∫ x, g x ∂multHaar v :=
  (measurePreserving_mul_left v ha).integral_comp (Homeomorph.mulLeft₀ a ha).measurableEmbedding g


/-- The extension by zero of a character is multiplicative: $\chi(a x) = \chi(a) \chi(x)$ for $a \neq 0$. -/
theorem charExt_mul {F : Type*} [GroupWithZero F] (χ : Fˣ →* ℂˣ) {a : F} (ha : a ≠ 0) (x : F) :
    charExt χ (a * x) = χ (Units.mk0 a ha) * charExt χ x := by
  by_cases hx : x = 0
  · simp [charExt, hx]
  · have hax : a * x ≠ 0 := mul_ne_zero ha hx
    simp only [charExt, hx, hax, ↓reduceDIte]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp

/-- The extension by zero of $\chi^{-1}$ is the inverse of the extension of $\chi$, with $0^{-1} = 0$. -/
theorem charExt_inv {F : Type*} [GroupWithZero F] (χ : Fˣ →* ℂˣ) (x : F) :
    charExt χ⁻¹ x = (charExt χ x)⁻¹ := by
  by_cases hx : x = 0
  · simp [charExt, hx]
  · simp [charExt, hx]

/-- On a unit $u$ the extension by zero takes the value $\chi(u)$. -/
theorem charExt_units {F : Type*} [GroupWithZero F] (χ : Fˣ →* ℂˣ) (u : Fˣ) :
    charExt χ (u : F) = χ u := by
  simp [charExt, u.ne_zero]

/-- The power $|a x|_v^s = |a|_v^s |x|_v^s$. -/
theorem norm_mul_cpow (a x : v.adicCompletion K) (s : ℂ) :
    ((‖a * x‖ : ℝ) : ℂ) ^ s = (‖a‖ : ℂ) ^ s * (‖x‖ : ℂ) ^ s := by
  rw [norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]

/-- The scaling law of the zeta integral: $Z(f, \chi, s) = \chi(a) |a|_v^s Z(f(a \cdot), \chi, s)$ for $a \in K_v^\times$. -/
theorem zetaIntegral_eq_mul_comp (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (s : ℂ) {a : v.adicCompletion K} (ha : a ≠ 0) :
    zetaIntegral v f χ s =
      χ (Units.mk0 a ha) * (‖a‖ : ℂ) ^ s * zetaIntegral v (fun x => f (a * x)) χ s := by
  rw [zetaIntegral, ← integral_comp_mul_left v ha, zetaIntegral, ← integral_const_mul]
  congr 1
  ext x
  rw [charExt_mul χ ha, norm_mul_cpow]
  ring

/-- If $g(a x) = c g(x)$ for all $x$ with $c \neq 1$, then $\int g \, d^\times x = 0$. -/
theorem integral_eq_zero_of_comp_mul (g : v.adicCompletion K → ℂ) {a : v.adicCompletion K}
    (ha : a ≠ 0) {c : ℂ} (hc : c ≠ 1) (hg : ∀ x, g (a * x) = c * g x) :
    ∫ x, g x ∂multHaar v = 0 := by
  have h := integral_comp_mul_left v ha g
  simp_rw [hg, integral_const_mul] at h
  have h1 : (c - 1) * ∫ x, g x ∂multHaar v = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hc)

/-- If $f(u x) = f(x)$ for a unit $u$ with $\chi(u) \neq 1$, then $Z(f, \chi, s) = 0$. -/
theorem zetaIntegral_eq_zero_of_ne_one (f : v.adicCompletion K → ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (u : (v.adicCompletion K)ˣ)
    (hu : ‖(u : v.adicCompletion K)‖ = 1) (hf : ∀ x, f (u * x) = f x) (hχ : χ u ≠ 1) :
    zetaIntegral v f χ s = 0 := by
  refine integral_eq_zero_of_comp_mul v _ u.ne_zero (c := χ u) ?_ fun x => ?_
  · intro h
    exact hχ (Units.val_eq_one.1 h)
  · rw [hf, charExt_mul χ u.ne_zero, norm_mul_cpow, hu, Complex.ofReal_one, Complex.one_cpow,
      Units.mk0_val]
    ring

/-- The ramified case: if $\chi$ is not trivial on $\mathcal{O}_v^\times$, then $Z(\mathbf{1}_{\mathcal{O}_v}, \chi, s) = 0$ for every $s$. -/
theorem zetaIntegral_integers_of_ramified (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ¬ ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ u = 1) (s : ℂ) :
    zetaIntegral v ((closedBall 0 1).indicator 1) χ s = 0 := by
  push Not at hχ
  obtain ⟨u, hu, hχu⟩ := hχ
  refine zetaIntegral_eq_zero_of_ne_one v _ χ s u hu (fun x => ?_) hχu
  simp only [Set.indicator, mem_closedBall_zero_iff, norm_mul, hu, one_mul, Pi.one_apply]

/-- For a Hecke character $\chi$ ramified at $v$, the zeta integral of $\mathbf{1}_{\mathcal{O}_v}$ against $\chi_v$ is $0$. So it is not the local factor $L_v(s, \chi) = 1$, and at a ramified place one needs other test functions. -/
theorem zetaIntegral_eq_zero_of_not_isUnramifiedAt (χ : HeckeCharacter K)
    (hχ : ¬ χ.IsUnramifiedAt v) (s : ℂ) :
    zetaIntegral v ((v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator 1)
      (χ.finiteComponent v) s = 0 := by
  rw [coe_adicCompletionIntegers]
  exact zetaIntegral_integers_of_ramified v _ (fun h => hχ ((isUnramifiedAt_iff v χ).2 h)) s

/-- The character $\chi$ of $K_v^\times$ is trivial on the group $1 + \mathfrak{p}_v^m$ of units $u$ with $|u - 1|_v \leq N(v)^{-m}$. For $m = 0$ this group is $\mathcal{O}_v^\times$. -/
def IsTrivialOnHigherUnits (χ : (v.adicCompletion K)ˣ →* ℂˣ) (m : ℕ) : Prop :=
  ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 →
    ‖(u : v.adicCompletion K) - 1‖ ≤ (q v)⁻¹ ^ m → χ u = 1

/-- The condition $|x|_v \leq N(v)^{-m}$ is the condition $v(x) \geq m$ on the valuation. -/
theorem norm_le_inv_q_pow_iff (x : v.adicCompletion K) (m : ℕ) :
    ‖x‖ ≤ (q v)⁻¹ ^ m ↔ Valued.v x ≤ WithZero.exp (-(m : ℤ)) := by
  have h : (q v)⁻¹ ^ m = (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp (-(m : ℤ))) : ℝ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp [q]
  rw [FinitePlace.norm_def, h, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le]

/-- The condition of `Langlands.HeckeCharacter.IsTrivialOnHigherUnits` for a Hecke character is the condition `IsTrivialOnHigherUnits` for its local component. -/
theorem isTrivialOnHigherUnits_iff (χ : HeckeCharacter K) (m : ℕ) :
    χ.IsTrivialOnHigherUnits v m ↔ IsTrivialOnHigherUnits v (χ.finiteComponent v) m := by
  constructor
  · intro h u hu hu1
    exact h u (Valued.toNormedField.norm_eq_one_iff.1 hu) ((norm_le_inv_q_pow_iff v _ m).1 hu1)
  · intro h u hu hu1
    exact h u (Valued.toNormedField.norm_eq_one_iff.2 hu) ((norm_le_inv_q_pow_iff v _ m).2 hu1)

/-- If $|x - 1|_v < 1$, then $|x|_v = 1$. -/
theorem norm_eq_one_of_norm_sub_one_lt {x : v.adicCompletion K} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : v.adicCompletion K)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rw [sub_add_cancel, norm_one] at h2
  rw [h2, max_eq_right h.le]

/-- The number $N(v)^{-1}$ is in $(0, 1)$. -/
theorem inv_q_lt_one : (q v)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_q v)

/-- A character trivial on $1 + \mathfrak{p}_v^m$ is locally constant on $K_v^\times$: if $|y - x|_v \leq N(v)^{-m-1} |x|_v$, then $\chi(y) = \chi(x)$. -/
theorem charExt_eq_of_norm_sub_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) {x y : v.adicCompletion K} (hx : x ≠ 0)
    (hxy : ‖y - x‖ ≤ (q v)⁻¹ ^ (m + 1) * ‖x‖) : charExt χ y = charExt χ x := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have ht : ‖y / x - 1‖ ≤ (q v)⁻¹ ^ (m + 1) := by
    rw [div_sub_one hx, norm_div, div_le_iff₀ hx']
    exact hxy
  have hlt : ‖y / x - 1‖ < 1 :=
    ht.trans_lt (pow_lt_one₀ (inv_nonneg.2 (q_pos v).le) (inv_q_lt_one v) (by omega))
  have h1 := norm_eq_one_of_norm_sub_one_lt v hlt
  have ht0 : y / x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hy : y = y / x * x := (div_mul_cancel₀ y hx).symm
  rw [hy, charExt_mul χ ht0, hχ _ (by rwa [Units.val_mk0]), Units.val_one, one_mul]
  rw [Units.val_mk0]
  exact ht.trans (pow_le_pow_of_le_one (inv_nonneg.2 (q_pos v).le) (inv_q_lt_one v).le
    (Nat.le_succ m))

/-- A character trivial on $1 + \mathfrak{p}_v^m$ is continuous on $K_v^\times$. -/
theorem continuousOn_charExt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) : ContinuousOn (charExt χ) {0}ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  refine ContinuousAt.continuousWithinAt (Filter.EventuallyEq.continuousAt (y := charExt χ x) ?_)
  have hr : 0 < (q v)⁻¹ ^ (m + 1) * ‖x‖ := by
    have := q_pos v
    have := norm_pos_iff.2 hx0
    positivity
  filter_upwards [closedBall_mem_nhds x hr] with y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  exact charExt_eq_of_norm_sub_le v hχ hx0 hy

/-- An additive character trivial on the ball of radius $N(v)^d$ is continuous. -/
theorem continuous_addChar (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => Filter.EventuallyEq.continuousAt (y := ψ x) ?_
  filter_upwards [closedBall_mem_nhds x (zpow_pos (q_pos v) d)] with y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [show y = x + (y - x) by ring, AddChar.map_add_eq_mul, h1 _ hy, mul_one]

/-- Almost every point is nonzero for $d^\times x$. -/
theorem ae_ne_zero : ∀ᵐ x ∂multHaar v, x ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (multHaar_singleton_zero v)

/-- A function that is continuous on $K_v^\times$ is measurable for $d^\times x$. -/
theorem aestronglyMeasurable_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    {g : v.adicCompletion K → E} (hg : ContinuousOn g {0}ᶜ) :
    AEStronglyMeasurable g (multHaar v) := by
  have h : (multHaar v).restrict {0}ᶜ = multHaar v :=
    Measure.restrict_eq_self_of_ae_mem (ae_ne_zero v)
  rw [← h]
  exact hg.aestronglyMeasurable (measurableSet_singleton 0).compl

/-- For $\sigma > 0$ the function $|x|_v^\sigma$ is integrable on $\mathcal{O}_v$ for $d^\times x$. The proof uses `zetaIntegral_unramified` for the trivial character: the integral is $(1 - N(v)^{-\sigma})^{-1} \neq 0$, so the integrand is integrable. -/
theorem integrableOn_norm_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ σ) (closedBall 0 1) (multHaar v) := by
  have hq := q_pos v
  have hz := zetaIntegral_unramified v 1 (fun _ _ => rfl) (localUniformizer K v)
    (norm_localUniformizer v) (σ : ℂ) (by simpa using Real.one_lt_rpow (one_lt_q v) hσ)
  have hne : zetaIntegral v ((closedBall 0 1).indicator 1) 1 (σ : ℂ) ≠ 0 := by
    rw [hz]
    refine inv_ne_zero (sub_ne_zero.2 fun h => ?_)
    have h2 : ‖(1 : ℂ)‖ = ‖((1 : (v.adicCompletion K)ˣ →* ℂˣ) (localUniformizer K v) : ℂ) *
        (q v : ℂ) ^ (-(σ : ℂ))‖ := by rw [h]
    rw [MonoidHom.one_apply, Units.val_one, one_mul, norm_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, Complex.ofReal_re] at h2
    have h3 : q v ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (one_lt_q v) (by linarith)
    linarith
  have hi : Integrable (fun x => (closedBall (0 : v.adicCompletion K) 1).indicator 1 x *
      charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x * (‖x‖ : ℂ) ^ (σ : ℂ)) (multHaar v) := by
    by_contra h
    exact hne (integral_undef h)
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine hi.norm.congr ?_
  filter_upwards [ae_ne_zero v] with x hx
  have hx' := norm_pos_iff.2 hx
  by_cases hb : x ∈ closedBall (0 : v.adicCompletion K) 1
  · simp [hb, charExt, hx, Complex.norm_cpow_eq_rpow_re_of_pos hx']
  · simp [hb]

/-- A measurable function $g$ with $|g(x)| \leq C |x|_v^\sigma$ on $\mathcal{O}_v \setminus \{0\}$, for some $\sigma > 0$, is integrable on $\mathcal{O}_v$ for $d^\times x$. -/
theorem integrableOn_closedBall_one_of_le {E : Type*} [NormedAddCommGroup E]
    {g : v.adicCompletion K → E} (hg : AEStronglyMeasurable g (multHaar v)) {C σ : ℝ}
    (hσ : 0 < σ) (hb : ∀ x : v.adicCompletion K, x ≠ 0 → ‖x‖ ≤ 1 → ‖g x‖ ≤ C * ‖x‖ ^ σ) :
    IntegrableOn g (closedBall 0 1) (multHaar v) := by
  refine Integrable.mono' ((integrableOn_norm_rpow v hσ).const_mul C) hg.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae (ae_ne_zero v)]
    with x hx hx0
  exact hb x hx0 (mem_closedBall_zero_iff.1 hx)

/-- The bound $|\chi(x)| \leq C |x|_v^t$ on $\mathcal{O}_v \setminus \{0\}$ for a character $\chi$ trivial on some $1 + \mathfrak{p}_v^m$, where $t$ is defined by $|\chi(\varpi_v)| = N(v)^{-t}$. -/
theorem exists_norm_charExt_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) :
    ∃ C : ℝ, ∀ x : v.adicCompletion K, x ≠ 0 → ‖x‖ ≤ 1 →
      ‖charExt χ x‖ ≤ C * ‖x‖ ^ (-Real.logb (q v) ‖(χ (localUniformizer K v) : ℂ)‖) := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : v.adicCompletion K) 1).exists_bound_of_continuousOn
    ((continuousOn_charExt v hχ).mono fun x hx h0 => by
      rw [Set.mem_singleton_iff] at h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hx
      exact zero_ne_one hx)
  refine ⟨C, fun x hx0 hx1 => ?_⟩
  set ϖ := localUniformizer K v
  set r := ‖(χ ϖ : ℂ)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (Units.ne_zero _)
  have hq := q_pos v
  obtain ⟨n, hn⟩ := exists_pow_of_norm_le_one v hx0 hx1
  have hϖn : ((ϖ : v.adicCompletion K) ^ n) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  set u := ((ϖ : v.adicCompletion K) ^ n)⁻¹ * x with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_pow, norm_localUniformizer, hn,
      inv_mul_cancel₀ (pow_ne_zero _ (inv_pos.2 hq).ne')]
  have hxu : x = (ϖ : v.adicCompletion K) ^ n * u := by
    rw [hu, ← mul_assoc, mul_inv_cancel₀ hϖn, one_mul]
  have hpow : ((q v)⁻¹ ^ n) ^ (-Real.logb (q v) r) = r ^ n := by
    rw [← Real.rpow_pow_comm (inv_nonneg.2 hq.le), Real.inv_rpow hq.le, Real.rpow_neg hq.le,
      inv_inv, Real.rpow_logb hq (one_lt_q v).ne' hr0]
  have hχn : (χ (Units.mk0 _ hϖn) : ℂ) = (χ ϖ : ℂ) ^ n := by
    have h : Units.mk0 _ hϖn = ϖ ^ n := by
      ext
      simp
    rw [h, map_pow, Units.val_pow_eq_pow_val]
  rw [hn, hpow, hxu, charExt_mul χ hϖn, hχn, norm_mul, norm_pow, ← hr, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC u (mem_sphere_zero_iff_norm.2 hun)) (pow_nonneg hr0.le n)

/-- If $|\chi(\varpi_v)| < N(v)^\sigma$, then the exponent $t$ of `exists_norm_charExt_le` satisfies $t + \sigma > 0$. -/
theorem neg_logb_add_pos {χ : (v.adicCompletion K)ˣ →* ℂˣ} {σ : ℝ}
    (hs : ‖(χ (localUniformizer K v) : ℂ)‖ < q v ^ σ) :
    0 < -Real.logb (q v) ‖(χ (localUniformizer K v) : ℂ)‖ + σ := by
  have := (Real.logb_lt_iff_lt_rpow (one_lt_q v) (norm_pos_iff.2 (Units.ne_zero _))).2 hs
  linarith

/-- If $r > 0$ and the powers $r^n$ and $r^{-n}$ are bounded, then $r = 1$. -/
theorem eq_one_of_pow_le {r C : ℝ} (hr : 0 < r) (h1 : ∀ n : ℕ, r ^ n ≤ C)
    (h2 : ∀ n : ℕ, r⁻¹ ^ n ≤ C) : r = 1 := by
  rcases lt_trichotomy r 1 with h | h | h
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_inv₀ hr).2 h)
    exact absurd (h2 n) (not_le.2 hn)
  · exact h
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (h1 n) (not_le.2 hn)

/-- The sphere $\mathcal{O}_v^\times$ does not contain $0$. -/
theorem sphere_one_subset_compl : sphere (0 : v.adicCompletion K) 1 ⊆ {0}ᶜ := by
  intro x hx h0
  rw [Set.mem_singleton_iff] at h0
  rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hx
  exact zero_ne_one hx

/-- A character trivial on some $1 + \mathfrak{p}_v^m$ is unitary on $\mathcal{O}_v^\times$: $|\chi(u)| = 1$. The image of the compact group $\mathcal{O}_v^\times$ under $|\chi|$ is a bounded subgroup of $\mathbb{R}_{>0}$, so it is trivial. -/
theorem norm_charExt_of_norm_eq_one {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) {x : v.adicCompletion K} (hx : ‖x‖ = 1) :
    ‖charExt χ x‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : v.adicCompletion K) 1).exists_bound_of_continuousOn
    ((continuousOn_charExt v hχ).mono (sphere_one_subset_compl v))
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  set u := Units.mk0 x hx0
  have hxu : x = (u : v.adicCompletion K) := rfl
  rw [hxu, charExt_units]
  refine eq_one_of_pow_le (C := C) (norm_pos_iff.2 (Units.ne_zero _)) (fun n => ?_) (fun n => ?_)
  · have h := hC ((u ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      (by rw [mem_sphere_zero_iff_norm, Units.val_pow_eq_pow_val, norm_pow, ← hxu, hx, one_pow])
    rwa [charExt_units, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  · have h := hC ((u⁻¹ ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      (by rw [mem_sphere_zero_iff_norm, Units.val_pow_eq_pow_val, norm_pow,
        Units.val_inv_eq_inv_val,
        norm_inv, ← hxu, hx, inv_one, one_pow])
    rwa [charExt_units, map_pow, Units.val_pow_eq_pow_val, norm_pow, map_inv,
      Units.val_inv_eq_inv_val, norm_inv] at h

/-- An additive character trivial on a ball around $0$ is unitary: $|\psi(x)| = 1$. The image of the compact group $\{y : |y|_v \leq |x|_v\}$ under $|\psi|$ is a bounded subgroup of $\mathbb{R}_{>0}$, so it is trivial. -/
theorem norm_addChar_eq_one (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) (x : v.adicCompletion K) :
    ‖ψ x‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : v.adicCompletion K) ‖x‖).exists_bound_of_continuousOn
    (continuous_addChar v ψ d h1).continuousOn
  have hn (y : v.adicCompletion K) (n : ℕ) : n • y ∈ closedBall (0 : v.adicCompletion K) ‖y‖ := by
    rw [mem_closedBall_zero_iff, nsmul_eq_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg y) (IsUltrametricDist.norm_natCast_le_one _ n)
  have h0 : ψ x ≠ 0 := by
    intro h
    have h' := AddChar.map_add_eq_mul ψ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h'
    exact one_ne_zero h'
  refine eq_one_of_pow_le (C := C) (norm_pos_iff.2 h0) (fun n => ?_) (fun n => ?_)
  · have h := hC _ (hn x n)
    rwa [AddChar.map_nsmul_eq_pow, norm_pow] at h
  · have h := hC _ (by have h := hn (-x) n; rwa [norm_neg] at h)
    rwa [AddChar.map_nsmul_eq_pow, AddChar.map_neg_eq_inv, norm_pow, norm_inv] at h

end Langlands.Tate.NonArchimedean
