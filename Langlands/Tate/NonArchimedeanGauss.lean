/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.NonArchimedeanCharacter
import Langlands.Tate.NonArchimedeanFourier

/-!
# Gauss sums on a nonarchimedean completion

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$, unit group $\mathcal{O}_v^\times$ and residue field of size $q = N(v)$. Let $du$ be the additive Haar measure `haar v` with $\int_{\mathcal{O}_v} du = 1$. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a character and let $\psi : K_v \to \mathbb{C}$ be an additive character. For $c \in K_v$ the Gauss sum is
$$G(\chi, \psi, c) = \int_{\mathcal{O}_v^\times} \chi(u) \psi(c u) \, du.$$
This is the local root number of Tate's thesis, up to a power of $q$ and a value of $\chi$.

## Conductors

We say that $\chi$ is trivial on the higher units $1 + \mathfrak{p}_v^m$ when $\chi(u) = 1$ for all $u$ with $|u - 1|_v \leq q^{-m}$. The conductor exponent of a ramified $\chi$ is the least $a \geq 1$ with this property. We write $a = b + 1$, so $\chi$ is trivial on $1 + \mathfrak{p}_v^{b+1}$ but not on $1 + \mathfrak{p}_v^b$. For $\psi$ we use the conductor exponent $d$ of `Langlands.Tate.NonArchimedeanFourier`: $\psi$ is trivial on $\{|x|_v \leq q^d\}$ and not on $\{|x|_v \leq q^{d+1}\}$.

## Main results

* `gaussSum_mul_gaussSum_inv`: if $|c|_v = q^{d+a}$, then $G(\chi, \psi, c) \, G(\chi^{-1}, \psi, -c) = q^{-a}$.
* `conj_gaussSum`: $\overline{G(\chi, \psi, c)} = G(\chi^{-1}, \psi, -c)$, because $\chi$ and $\psi$ take values of absolute value $1$.
* `norm_gaussSum_sq`: $|G(\chi, \psi, c)|^2 = q^{-a}$.
* `gaussSum_ne_zero`: $G(\chi, \psi, c) \neq 0$.

The factor $q^{-a}$ is the measure of $1 + \mathfrak{p}_v^a$ for $du$. With the self dual measure $q^{-d/2} du$ one gets the familiar value $|G|^2 = q^{-a-d}$ instead.

## Proofs

The main tool is the change of variables $u \mapsto w u$ for a unit $w$. It preserves $du$ and maps $\mathcal{O}_v^\times$ onto itself, so $G(\chi, \psi, c) = \chi(w) G(\chi, \psi, c w)$.

For the product formula we write $G(\chi, \psi, c) G(\chi^{-1}, \psi, -c)$ as a double integral over $\mathcal{O}_v^\times \times \mathcal{O}_v^\times$ and substitute $u = t w$. Fubini's theorem gives
$$\int_{\mathcal{O}_v^\times} \chi(t) \int_{\mathcal{O}_v^\times} \psi(c (t - 1) w) \, dw \, dt.$$
The inner integral is the integral of an additive character over a sphere. It is the difference of the integrals over the closed unit ball and over the open unit ball, and each of these is a measure or $0$ by orthogonality. The result is $1 - q^{-1}$ if $|t - 1|_v \leq q^{-a}$, it is $-q^{-1}$ if $|t - 1|_v = q^{-b}$, and it is $0$ otherwise. The outer integral then reduces to integrals of $\chi$ over $1 + \mathfrak{p}_v^a$, where $\chi = 1$, and over $1 + \mathfrak{p}_v^b$, where the integral is $0$ by orthogonality, because $\chi$ is not trivial there.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.3.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, chapter 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise ComplexConjugate

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The Gauss sum $G(\chi, \psi, c) = \int_{\mathcal{O}_v^\times} \chi(u) \psi(c u) \, du$ for the additive measure $du$ with $\mu(\mathcal{O}_v) = 1$. -/
noncomputable def gaussSum (χ : (v.adicCompletion K)ˣ →* ℂˣ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (c : v.adicCompletion K) : ℂ :=
  ∫ u in sphere 0 1, charExt χ u * ψ (c * u) ∂haar v

/-- Multiplication by an element of absolute value $1$ preserves $dx$ on a set $S$ that it maps onto itself. -/
theorem setIntegral_comp_mul_of_norm_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (v.adicCompletion K)} (hS : MeasurableSet S) {w : v.adicCompletion K} (hw : ‖w‖ = 1)
    (hSw : ∀ x, w * x ∈ S ↔ x ∈ S) (g : v.adicCompletion K → E) :
    ∫ x in S, g (w * x) ∂haar v = ∫ x in S, g x ∂haar v := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.1 (by rw [hw]; exact one_ne_zero)
  rw [← integral_indicator hS, ← integral_indicator hS]
  have h := integral_comp_mul_left_haar v hw0 (S.indicator g)
  rw [hw, inv_one, one_smul] at h
  rw [← h]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hSw x).2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx ((hSw x).1 h)]

/-- Orthogonality on a set $S$: if $g(w x) = c g(x)$ on $S$ with $c \neq 1$, and multiplication by $w$ maps $S$ onto itself, then $\int_S g \, dx = 0$. -/
theorem setIntegral_eq_zero_of_comp_mul {S : Set (v.adicCompletion K)} (hS : MeasurableSet S)
    {w : v.adicCompletion K} (hw : ‖w‖ = 1) (hSw : ∀ x, w * x ∈ S ↔ x ∈ S)
    (g : v.adicCompletion K → ℂ) {c : ℂ} (hc : c ≠ 1) (hg : ∀ x ∈ S, g (w * x) = c * g x) :
    ∫ x in S, g x ∂haar v = 0 := by
  have h := setIntegral_comp_mul_of_norm_eq_one v hS hw hSw g
  rw [setIntegral_congr_fun hS hg, integral_const_mul] at h
  have h1 : (c - 1) * ∫ x in S, g x ∂haar v = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hc)

/-- The sphere $\mathcal{O}_v^\times$ is stable under multiplication by an element of absolute value $1$. -/
theorem mul_mem_sphere_iff {w : v.adicCompletion K} (hw : ‖w‖ = 1) (x : v.adicCompletion K) :
    w * x ∈ sphere (0 : v.adicCompletion K) 1 ↔ x ∈ sphere 0 1 := by
  simp only [mem_sphere_zero_iff_norm, norm_mul, hw, one_mul]

/-- The Gauss sum transforms under units: $G(\chi, \psi, c) = \chi(w) G(\chi, \psi, c w)$ for $|w|_v = 1$. -/
theorem gaussSum_eq_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (c : v.adicCompletion K) {w : v.adicCompletion K} (hw : ‖w‖ = 1) :
    gaussSum v χ ψ c = χ (Units.mk0 w (norm_ne_zero_iff.1 (by rw [hw]; exact one_ne_zero))) *
      gaussSum v χ ψ (c * w) := by
  rw [gaussSum, ← setIntegral_comp_mul_of_norm_eq_one v isClosed_sphere.measurableSet hw
    (mul_mem_sphere_iff v hw), gaussSum, ← integral_const_mul]
  congr 1
  ext u
  rw [charExt_mul χ (norm_ne_zero_iff.1 (by rw [hw]; exact one_ne_zero)), mul_assoc c w u]
  ring

/-- The group $1 + \mathfrak{p}_v^m$, as the set of $t$ with $|t|_v = 1$ and $|t - 1|_v \leq r$, is stable under multiplication by its elements. -/
theorem mul_mem_higherUnits {r : ℝ} {w x : v.adicCompletion K}
    (hw : w ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r)
    (hx : x ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r) :
    w * x ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r := by
  simp only [Set.mem_inter_iff, mem_sphere_zero_iff_norm, mem_closedBall, dist_eq_norm] at hw hx ⊢
  refine ⟨by rw [norm_mul, hw.1, hx.1, one_mul], ?_⟩
  calc ‖w * x - 1‖ = ‖w * (x - 1) + (w - 1)‖ := by ring_nf
    _ ≤ max ‖w * (x - 1)‖ ‖w - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ r := max_le (by rw [norm_mul, hw.1, one_mul]; exact hx.2) hw.2

/-- The inverse of an element of $1 + \mathfrak{p}_v^m$ is in $1 + \mathfrak{p}_v^m$. -/
theorem inv_mem_higherUnits {r : ℝ} {w : v.adicCompletion K}
    (hw : w ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r) :
    w⁻¹ ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r := by
  simp only [Set.mem_inter_iff, mem_sphere_zero_iff_norm, mem_closedBall, dist_eq_norm] at hw ⊢
  have hw0 : w ≠ 0 := norm_ne_zero_iff.1 (by rw [hw.1]; exact one_ne_zero)
  refine ⟨by rw [norm_inv, hw.1, inv_one], ?_⟩
  rw [show w⁻¹ - 1 = w⁻¹ * -(w - 1) by field_simp; ring, norm_mul, norm_inv, hw.1, inv_one,
    one_mul, norm_neg]
  exact hw.2

/-- Multiplication by an element $w$ of $1 + \mathfrak{p}_v^m$ maps $1 + \mathfrak{p}_v^m$ onto itself. -/
theorem mul_mem_higherUnits_iff {r : ℝ} {w : v.adicCompletion K}
    (hw : w ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r) (x : v.adicCompletion K) :
    w * x ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r ↔
      x ∈ sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 r := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Set.mem_inter_iff, mem_sphere_zero_iff_norm, norm_zero] at hw
    exact zero_ne_one hw.1
  constructor
  · intro h
    have := mul_mem_higherUnits v (inv_mem_higherUnits v hw) h
    rwa [← mul_assoc, inv_mul_cancel₀ hw0, one_mul] at this
  · exact mul_mem_higherUnits v hw

/-- Orthogonality for a character on $1 + \mathfrak{p}_v^m$: if $\chi$ is not trivial on $1 + \mathfrak{p}_v^m$, then $\int_{1 + \mathfrak{p}_v^m} \chi(t) \, dt = 0$. -/
theorem setIntegral_charExt_higherUnits {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : ¬ IsTrivialOnHigherUnits v χ m) :
    ∫ t in sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 ((q v)⁻¹ ^ m),
      charExt χ t ∂haar v = 0 := by
  simp only [IsTrivialOnHigherUnits, not_forall] at hχ
  obtain ⟨w, hw1, hw2, hχw⟩ := hχ
  have hw : (w : v.adicCompletion K) ∈
      sphere (0 : v.adicCompletion K) 1 ∩ closedBall 1 ((q v)⁻¹ ^ m) := by
    rw [Set.mem_inter_iff, mem_sphere_zero_iff_norm, mem_closedBall, dist_eq_norm]
    exact ⟨hw1, hw2⟩
  refine setIntegral_eq_zero_of_comp_mul v (isClosed_sphere.inter isClosed_closedBall).measurableSet
    hw1 (mul_mem_higherUnits_iff v hw) _ (c := χ w) (fun h => hχw (Units.val_eq_one.1 h))
    fun x _ => ?_
  rw [charExt_mul χ w.ne_zero, Units.mk0_val]

/-- The integral of $\psi(b w)$ over the units: $\int_{\mathcal{O}_v^\times} \psi(b w) \, dw = \mathbf{1}_{\{|b|_v \leq q^d\}} - q^{-1} \mathbf{1}_{\{|b|_v \leq q^{d+1}\}}$, for $\psi$ of conductor exponent $d$. It is the difference of the Fourier transforms of $\mathbf{1}_{\mathcal{O}_v}$ and $\mathbf{1}_{\mathfrak{p}_v}$. -/
theorem setIntegral_sphere_addChar (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) (b : v.adicCompletion K) :
    ∫ w in sphere 0 1, ψ (b * w) ∂haar v =
      (closedBall 0 (q v ^ d)).indicator 1 b -
        (closedBall 0 (q v ^ d / (q v)⁻¹)).indicator (fun _ => (((q v)⁻¹ : ℝ) : ℂ)) b := by
  have hψ := continuous_addChar v ψ d h1
  have hint : IntegrableOn (fun w => ψ (b * w)) (closedBall 0 1) (haar v) :=
    (hψ.comp (continuous_const_mul b)).continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  set ϖ := (localUniformizer K v : v.adicCompletion K)
  have hball : ball (0 : v.adicCompletion K) 1 = closedBall 0 ‖ϖ‖ := by
    ext x
    rw [mem_ball_zero_iff, mem_closedBall_zero_iff, norm_localUniformizer, norm_lt_one_iff_le v]
  have e (r : ℝ) : ∫ w in closedBall 0 r, ψ (b * w) ∂haar v =
      fourier v ψ ((closedBall 0 r).indicator 1) b := by
    rw [fourier_indicator_eq_setIntegral]
    rfl
  rw [← closedBall_sdiff_ball, setIntegral_sdiff measurableSet_ball hint ball_subset_closedBall,
    hball,
    e, e, fourier_indicator_integers v ψ d h1 h2,
    fourier_indicator_closedBall_of_conductor v ψ d h1 h2 (Units.ne_zero _), norm_localUniformizer]


/-- The ball $1 + \mathfrak{p}_v^m$ for $m \geq 1$ consists of units. -/
theorem closedBall_one_subset_sphere {r : ℝ} (hr : r < 1) :
    closedBall (1 : v.adicCompletion K) r ⊆ sphere 0 1 := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  exact mem_sphere_zero_iff_norm.2 (norm_eq_one_of_norm_sub_one_lt v (hx.trans_lt hr))

/-- The ball $1 + \mathfrak{p}_v^m$ has measure $N(v)^{-m}$. -/
theorem haar_closedBall_one_pow (m : ℕ) :
    haar v (closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ m)) = ENNReal.ofReal ((q v)⁻¹ ^ m) := by
  have h : closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ m) =
      (fun x => x + -1) ⁻¹' closedBall 0 ((q v)⁻¹ ^ m) := by
    ext x
    simp [dist_eq_norm, sub_eq_add_neg]
  rw [h, measure_preimage_add_right, haar_closedBall_pow]

/-- If $|c|_v = q^{d + a}$, then $|c y|_v \leq q^{d + k}$ if and only if $|y|_v \leq q^{k - a}$. -/
theorem norm_mul_le_zpow_iff {c : v.adicCompletion K} {d k : ℤ} {a : ℕ}
    (hc : ‖c‖ = q v ^ (d + a)) (y : v.adicCompletion K) :
    ‖c * y‖ ≤ q v ^ (d + k) ↔ ‖y‖ ≤ q v ^ (k - a) := by
  rw [norm_mul, hc, ← le_div_iff₀' (zpow_pos (q_pos v) _), ← zpow_sub₀ (q_pos v).ne',
    show d + k - (d + a) = k - a by ring]

/-- The power $q^{-m}$ as an integral power. -/
theorem zpow_neg_natCast (m : ℕ) : q v ^ (-(m : ℤ)) = (q v)⁻¹ ^ m := by
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- The product formula for Gauss sums. Let $\chi$ have conductor exponent $a = b + 1 \geq 1$ and let $\psi$ have conductor exponent $d$. If $|c|_v = q^{d + a}$, then $G(\chi, \psi, c) G(\chi^{-1}, \psi, -c) = q^{-a}$.

The proof writes the product as a double integral over $\mathcal{O}_v^\times \times \mathcal{O}_v^\times$, substitutes $u = w t$, and changes the order of integration. The inner integral $\int_{\mathcal{O}_v^\times} \psi(c (t - 1) w) \, dw$ is $\mathbf{1}_{1 + \mathfrak{p}_v^a}(t) - q^{-1} \mathbf{1}_{1 + \mathfrak{p}_v^{a - 1}}(t)$, and the integral of $\chi$ over $1 + \mathfrak{p}_v^{a-1}$ is zero. -/
theorem gaussSum_mul_gaussSum_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    gaussSum v χ ψ c * gaussSum v χ⁻¹ ψ (-c) = (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) := by
  set S := sphere (0 : v.adicCompletion K) 1 with hSdef
  have hS : MeasurableSet S := isClosed_sphere.measurableSet
  have hS0 := sphere_one_subset_compl v
  have hne (w : v.adicCompletion K) (hw : w ∈ S) : w ≠ 0 := fun h => hS0 hw h
  have hχS : ContinuousOn (charExt χ) S := (continuousOn_charExt v hχ).mono hS0
  set Φ : v.adicCompletion K → v.adicCompletion K → ℂ :=
    fun w t => charExt χ t * ψ (c * (t - 1) * w) with hΦ
  -- Step 1: the product is a double integral.
  have step1 : gaussSum v χ ψ c * gaussSum v χ⁻¹ ψ (-c) =
      ∫ w in S, ∫ t in S, Φ w t ∂haar v ∂haar v := by
    rw [show gaussSum v χ⁻¹ ψ (-c) = ∫ u in S, charExt χ⁻¹ u * ψ (-c * u) ∂haar v from rfl,
      ← integral_const_mul]
    refine setIntegral_congr_fun hS fun w hw => ?_
    have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
    have hw0 := hne w hw
    rw [gaussSum_eq_mul v χ ψ c hw1, gaussSum, mul_comm (χ _ : ℂ), mul_assoc, ← integral_mul_const]
    congr 1
    funext t
    have hχw : charExt χ w = χ (Units.mk0 w hw0) := by simp [charExt, hw0]
    have hu : (χ (Units.mk0 w hw0) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [hΦ]
    rw [charExt_inv, hχw, show c * (t - 1) * w = c * w * t + -c * w by ring,
      AddChar.map_add_eq_mul]
    field_simp
  -- Step 2: change the order of integration.
  have : IsFiniteMeasure ((haar v).restrict S) :=
    isFiniteMeasure_restrict.2 (isCompact_sphere 0 1).measure_lt_top.ne
  have hint :
      Integrable (Function.uncurry Φ) (((haar v).restrict S).prod ((haar v).restrict S)) := by
    have hm : AEStronglyMeasurable (charExt χ) ((haar v).restrict S) := hχS.aestronglyMeasurable hS
    have hψc : Continuous fun p : v.adicCompletion K × v.adicCompletion K =>
        ψ (c * (p.2 - 1) * p.1) :=
      (continuous_addChar v ψ d h1).comp (by fun_prop)
    refine Integrable.of_bound (hm.comp_snd.mul hψc.aestronglyMeasurable) 1 ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hS.prod hS)] with p hp
    simp only [Function.uncurry, hΦ, norm_mul, norm_addChar_eq_one v ψ d h1,
      norm_charExt_of_norm_eq_one v hχ (mem_sphere_zero_iff_norm.1 hp.2), mul_one, le_refl]
  rw [step1, integral_integral_swap hint]
  -- Step 3: the inner integral.
  have hA (y : v.adicCompletion K) : ‖c * y‖ ≤ q v ^ d ↔ ‖y‖ ≤ (q v)⁻¹ ^ (b + 1) := by
    have h := norm_mul_le_zpow_iff v hc y (k := 0)
    rwa [add_zero, zero_sub, zpow_neg_natCast] at h
  have hB (y : v.adicCompletion K) : ‖c * y‖ ≤ q v ^ d / (q v)⁻¹ ↔ ‖y‖ ≤ (q v)⁻¹ ^ b := by
    have h := norm_mul_le_zpow_iff v hc y (k := 1)
    rw [div_inv_eq_mul]
    rwa [show (1 : ℤ) - ((b + 1 : ℕ) : ℤ) = -(b : ℤ) by push_cast; ring, zpow_neg_natCast,
      zpow_add_one₀ (q_pos v).ne'] at h
  set A := closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ (b + 1))
  set B := closedBall (1 : v.adicCompletion K) ((q v)⁻¹ ^ b)
  have step3 : ∀ t ∈ S, ∫ w in S, Φ w t ∂haar v =
      A.indicator (charExt χ) t - (((q v)⁻¹ : ℝ) : ℂ) * B.indicator (charExt χ) t := by
    intro t _
    have hAB : ‖t - 1‖ ≤ (q v)⁻¹ ^ (b + 1) → ‖t - 1‖ ≤ (q v)⁻¹ ^ b := fun h =>
      h.trans (pow_le_pow_of_le_one (inv_nonneg.2 (q_pos v).le) (inv_q_lt_one v).le
        (Nat.le_succ b))
    simp only [hΦ]
    rw [integral_const_mul, setIntegral_sphere_addChar v ψ d h1 h2]
    simp only [Set.indicator, mem_closedBall_zero_iff, Pi.one_apply]
    simp only [hA, hB, A, B, mem_closedBall, dist_eq_norm]
    by_cases h3 : ‖t - 1‖ ≤ (q v)⁻¹ ^ (b + 1)
    · simp only [h3, hAB h3, ↓reduceIte]
      ring
    · by_cases h4 : ‖t - 1‖ ≤ (q v)⁻¹ ^ b
      · simp only [h3, h4, ↓reduceIte]
        ring
      · simp only [h3, h4, ↓reduceIte]
        ring
  -- Step 4: the integrals over $1 + \mathfrak{p}_v^a$ and $1 + \mathfrak{p}_v^{a-1}$.
  rw [setIntegral_congr_fun hS step3]
  have hiχ : IntegrableOn (charExt χ) S (haar v) := hχS.integrableOn_compact (isCompact_sphere 0 1)
  have hiA : IntegrableOn (A.indicator (charExt χ)) S (haar v) :=
    hiχ.indicator measurableSet_closedBall
  have hiB : IntegrableOn (B.indicator (charExt χ)) S (haar v) :=
    hiχ.indicator measurableSet_closedBall
  have hq1 : (q v)⁻¹ ^ (b + 1) < 1 :=
    pow_lt_one₀ (inv_nonneg.2 (q_pos v).le) (inv_q_lt_one v) (by omega)
  have hSA : S ∩ A = A := Set.inter_eq_right.2 (closedBall_one_subset_sphere v hq1)
  have hA1 : ∫ x in A, charExt χ x ∂haar v = (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_closedBall (g := fun _ => (1 : ℂ)) ?_,
      setIntegral_const, Measure.real, haar_closedBall_one_pow,
      ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.2 (q_pos v).le) _)]
    · simp
    · intro x hx
      have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 (closedBall_one_subset_sphere v hq1 hx)
      have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx1]; exact one_ne_zero)
      rw [mem_closedBall, dist_eq_norm] at hx
      simp only [charExt, hx0, ↓reduceDIte]
      rw [hχ (Units.mk0 x hx0) hx1 hx, Units.val_one]
  rw [integral_sub hiA (hiB.const_mul _), integral_const_mul,
    setIntegral_indicator measurableSet_closedBall, setIntegral_indicator measurableSet_closedBall,
    hSA, hA1, setIntegral_charExt_higherUnits v hχ', mul_zero, sub_zero]

/-- The complex conjugate of a Gauss sum: $\overline{G(\chi, \psi, c)} = G(\chi^{-1}, \psi, -c)$. It holds because $\chi$ and $\psi$ are unitary. -/
theorem conj_gaussSum {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ} (hχ : IsTrivialOnHigherUnits v χ m)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) (c : v.adicCompletion K) :
    conj (gaussSum v χ ψ c) = gaussSum v χ⁻¹ ψ (-c) := by
  rw [gaussSum, ← integral_conj, gaussSum]
  refine setIntegral_congr_fun isClosed_sphere.measurableSet fun u hu => ?_
  rw [map_mul, ← Complex.inv_eq_conj (norm_charExt_of_norm_eq_one v hχ
    (mem_sphere_zero_iff_norm.1 hu)), ← Complex.inv_eq_conj (norm_addChar_eq_one v ψ d h1 _),
    charExt_inv, ← AddChar.map_neg_eq_inv, neg_mul]

/-- The absolute value of a Gauss sum: $|G(\chi, \psi, c)|^2 = q^{-a}$, where $a \geq 1$ is the conductor exponent of $\chi$ and $|c|_v = q^{d + a}$. -/
theorem norm_gaussSum_sq {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    ‖gaussSum v χ ψ c‖ ^ 2 = (q v)⁻¹ ^ (b + 1) := by
  have h := gaussSum_mul_gaussSum_inv v hχ hχ' ψ d h1 h2 hc
  rw [← conj_gaussSum v hχ ψ d h1, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- A Gauss sum of a ramified character is not zero. -/
theorem gaussSum_ne_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    gaussSum v χ ψ c ≠ 0 := by
  intro h
  have h' := gaussSum_mul_gaussSum_inv v hχ hχ' ψ d h1 h2 hc
  rw [h, zero_mul, eq_comm, Complex.ofReal_eq_zero] at h'
  exact pow_ne_zero _ (inv_ne_zero (q_pos v).ne') h'

end Langlands.Tate.NonArchimedean
