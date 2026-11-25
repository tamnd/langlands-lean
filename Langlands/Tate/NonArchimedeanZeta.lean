/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.NonArchimedeanMeasure

/-!
# The unramified local zeta integral

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$ and norm $q = N(v)$. For a function $f$ on $K_v$ and a character $\chi : K_v^\times \to \mathbb{C}^\times$ the local zeta integral of Tate is
$$Z(f, \chi, s) = \int_{K_v^\times} f(x) \chi(x) |x|_v^s \, d^\times x.$$
The conventions for $|x|_v$ and $d^\times x$ are those of `Langlands.Tate.NonArchimedeanMeasure`: $|\varpi_v|_v = q^{-1}$ and $\int_{\mathcal{O}_v^\times} d^\times x = 1$. In Lean the integral is over $K_v$, with the character extended by $\chi(0) = 0$ (`charExt`); the point $0$ has measure zero for $d^\times x$.

## Main results

* `zetaIntegral_unramified`: if $\chi$ is trivial on $\mathcal{O}_v^\times$, $|\varpi|_v = q^{-1}$ and $|\chi(\varpi)| < q^{\mathrm{Re}(s)}$, then $Z(\mathbf{1}_{\mathcal{O}_v}, \chi, s) = (1 - \chi(\varpi) q^{-s})^{-1}$.
* `zetaIntegral_eq_localFactor`: for a Hecke character $\chi$ unramified at $v$, the zeta integral of $\mathbf{1}_{\mathcal{O}_v}$ against the local component $\chi_v$ is exactly `HeckeCharacter.localFactor χ v s`, the Euler factor of the finite L-function. This is the local input for the Euler product of the global zeta integral.

## Proof

The set $\mathcal{O}_v \setminus \{0\}$ is the disjoint union of the shells $S_m = \varpi^m \mathcal{O}_v^\times = \{x : |x|_v = q^{-m}\}$ for $m \geq 0$. On $S_m$ we have $\chi(x) = \chi(\varpi)^m$, because $\chi$ is trivial on units, and $|x|_v^s = q^{-ms}$. So the integrand is the constant $z^m$ on $S_m$, with $z = \chi(\varpi) q^{-s}$. Each shell has measure $1$ for $d^\times x$. The condition on $s$ says $|z| < 1$, so the integrand is integrable and the integral is the geometric series $\sum_{m \geq 0} z^m = (1 - z)^{-1}$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.5.
* D. Bump, Automorphic forms and representations, proposition 3.1.4 for $\mathrm{GL}(1)$.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open Classical in
/-- The extension of a character $\chi : F^\times \to \mathbb{C}^\times$ to $F$ by $\chi(0) = 0$. -/
noncomputable def charExt {F : Type*} [GroupWithZero F] (χ : Fˣ →* ℂˣ) (x : F) : ℂ :=
  if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

/-- The local zeta integral $Z(f, \chi, s) = \int_{K_v^\times} f(x) \chi(x) |x|_v^s \, d^\times x$. -/
noncomputable def zetaIntegral (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * (‖x‖ : ℂ) ^ s ∂multHaar v

/-- For $r \geq 0$, $(r^m)^s = (r^s)^m$. -/
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (s : ℂ) :
    ((r ^ m : ℝ) : ℂ) ^ s = ((r : ℂ) ^ s) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr m) hr, ih,
      pow_succ]

/-- For $r \geq 0$, $(r^{-1})^s = r^{-s}$. -/
theorem ofReal_inv_cpow {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]


/-- The unramified computation. Let $\chi$ be trivial on $\mathcal{O}_v^\times$ and let $|\varpi|_v = N(v)^{-1}$. If $|\chi(\varpi)| < N(v)^{\mathrm{Re}(s)}$, then $Z(\mathbf{1}_{\mathcal{O}_v}, \chi, s) = (1 - \chi(\varpi) N(v)^{-s})^{-1}$. -/
theorem zetaIntegral_unramified (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 → χ u = 1)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : ‖(ϖ : v.adicCompletion K)‖ = (q v)⁻¹) (s : ℂ)
    (hs : ‖(χ ϖ : ℂ)‖ < q v ^ s.re) :
    zetaIntegral v ((closedBall 0 1).indicator 1) χ s = (1 - χ ϖ * (q v : ℂ) ^ (-s))⁻¹ := by
  set z : ℂ := χ ϖ * (q v : ℂ) ^ (-s) with hzdef
  have hq := q_pos v
  have hz : ‖z‖ < 1 := by
    rw [hzdef, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, Real.rpow_neg hq.le,
      ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hs
  set S : ℕ → Set (v.adicCompletion K) := fun m => sphere 0 ((q v)⁻¹ ^ m) with hS
  set h : v.adicCompletion K → ℂ := fun x => charExt χ x * (‖x‖ : ℂ) ^ s with hh
  have hval (m : ℕ) : ∀ x ∈ S m, h x = z ^ m := by
    intro x hx
    rw [hS, mem_sphere_zero_iff_norm] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hx
      exact (pow_pos (inv_pos.2 hq) m).ne hx
    set u : (v.adicCompletion K)ˣ := Units.mk0 x hx0 * ϖ⁻¹ ^ m with hu
    have hun : ‖(u : v.adicCompletion K)‖ = 1 := by
      rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, Units.val_mk0, hx,
        Units.val_inv_eq_inv_val, norm_inv, hϖ, ← mul_pow, mul_inv_cancel₀ (inv_pos.2 hq).ne',
        one_pow]
    have hx' : Units.mk0 x hx0 = u * ϖ ^ m := by rw [hu]; group
    simp only [hh, charExt, hx0, ↓reduceDIte]
    rw [hx', map_mul, hχ u hun, one_mul, map_pow, Units.val_pow_eq_pow_val, hx,
      ofReal_pow_cpow (inv_nonneg.2 hq.le), ofReal_inv_cpow hq.le, hzdef, mul_pow]
  have hmeas (m : ℕ) : MeasurableSet (S m) := isClosed_sphere.measurableSet
  have hμ (m : ℕ) : multHaar v (S m) = 1 := by
    have h1 : ((ϖ : v.adicCompletion K) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have := multHaar_sphere_norm v h1
    rwa [norm_pow, hϖ] at this
  have hint (m : ℕ) : IntegrableOn h (S m) (multHaar v) := by
    refine (integrableOn_const (C := z ^ m) (by rw [hμ]; exact ENNReal.one_ne_top)).congr_fun
      (fun x hx => (hval m x hx).symm) (hmeas m)
  have hI (m : ℕ) : ∫ x in S m, h x ∂multHaar v = z ^ m := by
    rw [setIntegral_congr_fun (hmeas m) (hval m), setIntegral_const, measureReal_def, hμ]
    simp
  have hInorm (m : ℕ) : ∫ x in S m, ‖h x‖ ∂multHaar v = ‖z‖ ^ m := by
    rw [setIntegral_congr_fun (hmeas m) (fun x hx => by rw [hval m x hx]), setIntegral_const,
      measureReal_def, hμ]
    simp
  have hD : Pairwise (Function.onFun Disjoint S) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun x hxm hxn => hmn ?_
    rw [hS, mem_sphere_zero_iff_norm] at hxm hxn
    exact pow_right_injective₀ (inv_pos.2 hq) (inv_lt_one_of_one_lt₀ (one_lt_q v)).ne
      (hxm.symm.trans hxn)
  have hiU : IntegrableOn h (⋃ m, S m) (multHaar v) :=
    integrableOn_iUnion_of_summable_integral_norm hint
      (by simp_rw [hInorm]; exact summable_geometric_of_lt_one (norm_nonneg _) hz)
  have hsum := hasSum_integral_iUnion hmeas hD hiU
  simp_rw [hI] at hsum
  have hU : closedBall (0 : v.adicCompletion K) 1 =ᵐ[multHaar v] ⋃ m, S m := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun x hx => ?_) (multHaar_singleton_zero v)
      rw [Set.mem_sdiff, mem_closedBall_zero_iff, Set.mem_iUnion] at hx
      by_contra hx0
      obtain ⟨m, hm⟩ := exists_pow_of_norm_le_one v hx0 hx.1
      exact hx.2 ⟨m, by rw [hS, mem_sphere_zero_iff_norm]; exact hm⟩
    · convert measure_empty (μ := multHaar v)
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      rw [Set.mem_sdiff, Set.mem_iUnion, mem_closedBall_zero_iff] at hx
      obtain ⟨⟨m, hm⟩, hx⟩ := hx
      rw [hS, mem_sphere_zero_iff_norm] at hm
      exact hx (hm ▸ pow_le_one₀ (inv_nonneg.2 hq.le) (inv_le_one_of_one_le₀ (one_lt_q v).le))
  have hf : (fun x => (closedBall (0 : v.adicCompletion K) 1).indicator 1 x * charExt χ x *
      (‖x‖ : ℂ) ^ s) = (closedBall (0 : v.adicCompletion K) 1).indicator h := by
    ext x
    by_cases hx : x ∈ closedBall (0 : v.adicCompletion K) 1 <;> simp [hx, hh]
  rw [zetaIntegral, hf, integral_indicator measurableSet_closedBall, setIntegral_congr_set hU]
  exact hsum.unique (hasSum_geometric_of_norm_lt_one hz)


/-- A Hecke character is unramified at $v$ if and only if $\chi_v$ is trivial on the elements of absolute value $1$. -/
theorem isUnramifiedAt_iff (χ : HeckeCharacter K) :
    χ.IsUnramifiedAt v ↔ ∀ u : (v.adicCompletion K)ˣ, ‖(u : v.adicCompletion K)‖ = 1 →
      χ.finiteComponent v u = 1 := by
  constructor
  · intro hχ u hu
    refine hχ u (Valued.toNormedField.norm_eq_one_iff.1 hu) ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero, ← Valued.toNormedField.norm_le_one_iff]
    calc ‖(u : v.adicCompletion K) - 1‖ = ‖(u : v.adicCompletion K) + -1‖ := by
          rw [sub_eq_add_neg]
      _ ≤ max ‖(u : v.adicCompletion K)‖ ‖(-1 : v.adicCompletion K)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ = 1 := by simp [hu]
  · intro hχ u hu _
    exact hχ u (Valued.toNormedField.norm_eq_one_iff.2 hu)

/-- The local zeta integral of $\mathbf{1}_{\mathcal{O}_v}$ is the Euler factor: if $\chi$ is unramified at $v$ and $|\chi_v(\varpi_v)| < N(v)^{\mathrm{Re}(s)}$, then $Z(\mathbf{1}_{\mathcal{O}_v}, \chi_v, s) = L_v(s, \chi)$, the factor `HeckeCharacter.localFactor`. -/
theorem zetaIntegral_eq_localFactor (χ : HeckeCharacter K) (hχ : χ.IsUnramifiedAt v) (s : ℂ)
    (hs : ‖(χ.finiteComponent v (localUniformizer K v) : ℂ)‖ <
      (Ideal.absNorm v.asIdeal : ℝ) ^ s.re) :
    zetaIntegral v ((v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator 1)
      (χ.finiteComponent v) s = χ.localFactor v s := by
  rw [HeckeCharacter.localFactor, ite_eq_left_of_eq_true _ _ (eq_true hχ), coe_adicCompletionIntegers,
    zetaIntegral_unramified v _ ((isUnramifiedAt_iff v χ).1 hχ) _ (norm_localUniformizer v) s hs]
  simp only [q, Complex.ofReal_natCast]

end Langlands.Tate.NonArchimedean
