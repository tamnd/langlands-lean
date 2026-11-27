/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Langlands.Statements.Modularity
import Langlands.Bridge.AnthropicFLT

/-!
# Certified instances of modularity for five semistable curves

This file goes with the lab experiment E5. It defines the elliptic curves 11a1, 14a1, 15a1, 17a1 and 37a1 of the tables of Cremona over $\mathbb{Q}$, proves that they are elliptic and semistable in the sense of `Langlands.IsSemistable`, and applies `Langlands.ModularitySemistableQ` to them. The semistability is proved without a hypothesis. The modularity is conditional: it depends on `Langlands.ModularitySemistableQ`, or on the three hypotheses of `Langlands.Bridge.modularitySemistableQ_of_anthropicFLT`.

## Main definitions

* `Langlands.Modular.E11a1`, `Langlands.Modular.E14a1`, `Langlands.Modular.E15a1`, `Langlands.Modular.E17a1`, `Langlands.Modular.E37a1`: the five curves over $\mathbb{Q}$.
* `Langlands.Modular.E11a1Int` and the other `Int` curves: the same equations over $\mathbb{Z}$.

## Main results

* `Langlands.Modular.valuation_le_valuation_minimal`: for an integral Weierstrass equation $W$ over the fraction field $K$ of a discrete valuation ring with $\Delta(W) \ne 0$, the valuations of $\Delta$ and of $c_4$ of $W$ are at most those of the minimal model.
* `Langlands.Modular.not_hasAdditiveReduction_minimal`: an integral equation whose $\Delta$ or $c_4$ is a unit has no additive reduction.
* `Langlands.Modular.isSemistable_map_of_isCoprime`: an equation over $\mathbb{Z}$ with $\Delta \ne 0$ and $\gcd(c_4, \Delta) = 1$ gives a semistable curve over $\mathbb{Q}$.
* `Langlands.Modular.isSemistable_E11a1` and the four other cases: the curves are semistable.
* `Langlands.Modular.modular_E11a1_of_semistable` and the four other cases: `ModularitySemistableQ` gives a cusp form of weight 2 whose coefficients are those of $L(E, s)$.
* `Langlands.Modular.modular_E11a1_of_anthropicFLT` and the four other cases: the same conclusion from the hypotheses of `Langlands.Bridge.modularitySemistableQ_of_anthropicFLT`.

## Proof

Let $W' = C \cdot W$ be the minimal model, with $u$ the scale of $C$. The equation $W = C^{-1} \cdot W'$ is integral, so minimality gives $v(\Delta(W)) \le v(\Delta(W')) = v(u^{-1})^{12} v(\Delta(W))$ for the multiplicative valuation $v$. Since $\Delta(W) \ne 0$, this gives $v(u^{-1}) \ge 1$, and then $v(c_4(W')) = v(u^{-1})^4 v(c_4(W)) \ge v(c_4(W))$. If $\Delta(W)$ is a unit, then $v(\Delta(W')) = 1$ and the reduction is good. If $c_4(W)$ is a unit, then $v(c_4(W')) = 1$ and the reduction is not additive. An integer pair $c_4, \Delta$ with $\gcd = 1$ stays coprime in the local ring of each completion, so one of them is a unit there.

## Implementation notes

The discriminants and the values of $c_4$ are computed by `decide` over $\mathbb{Z}$. They are $\Delta = -11^5, -2^6 7^3, 3^4 5^4, -17^4, 37$ and $c_4 = 496, -215, 481, 33, 48$. The file does not use Tate's algorithm. It does not prove that the five models are global minimal models, and it does not compute the conductor. These facts are not needed for semistability.

## References

* J. Cremona, Algorithms for modular elliptic curves, second edition, 1997, table 1.
* J. Silverman, The arithmetic of elliptic curves, second edition, 2009, sections VII.1 and VII.5.
-/

namespace Langlands.Modular

open IsDedekindDomain WeierstrassCurve

section Reduction

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

/-- For an integral Weierstrass equation $W$ over the fraction field of a discrete valuation ring with $\Delta(W) \ne 0$, the valuations of $\Delta(W)$ and of $c_4(W)$ are at most the valuations of $\Delta$ and of $c_4$ of the minimal model `W.minimal R`. -/
theorem valuation_le_valuation_minimal (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : W.Δ ≠ 0) :
    valuation K (maximalIdeal R) W.Δ ≤ valuation K (maximalIdeal R) (W.minimal R).Δ ∧
      valuation K (maximalIdeal R) W.c₄ ≤ valuation K (maximalIdeal R) (W.minimal R).c₄ := by
  set C := (W.exists_isMinimal R).choose
  have hC : W.minimal R = C • W := rfl
  have hback : C⁻¹ • W.minimal R = W := by rw [hC, smul_smul, inv_mul_cancel, one_smul]
  have hint : IsIntegral R (C⁻¹ • W.minimal R) := by rw [hback]; infer_instance
  have hmin := (IsMinimal.val_Δ_maximal (R := R) (W := W.minimal R))
  have key : valuation_Δ_aux R (C⁻¹ • W.minimal R) ≤
      valuation_Δ_aux R ((1 : VariableChange K) • W.minimal R) := by
    rcases le_total (valuation_Δ_aux R (C⁻¹ • W.minimal R))
      (valuation_Δ_aux R ((1 : VariableChange K) • W.minimal R)) with h | h
    · exact h
    · exact hmin.2 hint h
  rw [hback, one_smul] at key
  have key' := Subtype.coe_le_coe.mpr key
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral] at key'
  have hΔ' : valuation K (maximalIdeal R) W.Δ ≠ 0 := by simpa using hΔ
  rw [hC, variableChange_Δ, map_mul, map_pow] at key'
  have ha : 1 ≤ valuation K (maximalIdeal R) (↑C.u⁻¹ : K) := by
    by_contra h
    have h12 := pow_lt_one₀ zero_le (not_le.mp h) (n := 12) (by norm_num)
    have := mul_lt_mul_of_pos_right h12 (zero_lt_iff.mpr hΔ')
    rw [one_mul] at this
    exact absurd key' (not_le.mpr this)
  refine ⟨by rw [hC, variableChange_Δ, map_mul, map_pow]; exact key', ?_⟩
  rw [hC, variableChange_c₄, map_mul, map_pow]
  exact le_mul_of_one_le_left zero_le (one_le_pow₀ ha)

/-- An integral Weierstrass equation $W_R$ over a discrete valuation ring $R$ whose discriminant or $c_4$ is a unit has no additive reduction: the minimal model of $W = W_R \otimes K$ does not have additive reduction, if $\Delta(W) \ne 0$. -/
theorem not_hasAdditiveReduction_minimal (W : WeierstrassCurve K) (WR : WeierstrassCurve R)
    (hW : W = WR⁄K) (hΔ : W.Δ ≠ 0) (h : IsUnit WR.Δ ∨ IsUnit WR.c₄) :
    ¬ (W.minimal R).HasAdditiveReduction R := by
  have : IsIntegral R W := ⟨⟨WR, hW⟩⟩
  obtain ⟨h1, h2⟩ := valuation_le_valuation_minimal (R := R) W hΔ
  have hval : ∀ r : R, IsUnit r → valuation K (maximalIdeal R) (algebraMap R K r) = 1 :=
    fun r hr => (valuation_eq_one_iff_notMem (maximalIdeal R)).mpr
      (IsLocalRing.notMem_maximalIdeal.mpr hr)
  intro hA
  rcases h with hu | hu
  · have e : W.Δ = algebraMap R K WR.Δ := by rw [hW, baseChange, map_Δ]
    rw [e, hval _ hu] at h1
    exact absurd hA.badReduction (not_lt.mpr h1)
  · have e : W.c₄ = algebraMap R K WR.c₄ := by rw [hW, baseChange, map_c₄]
    rw [e, hval _ hu] at h2
    exact absurd hA.additiveReduction (not_lt.mpr h2)

end Reduction

open NumberField

/-- A Weierstrass equation $W$ over $\mathbb{Z}$ with $\Delta(W) \ne 0$ and $\gcd(c_4(W), \Delta(W)) = 1$ gives a semistable curve over $\mathbb{Q}$. -/
theorem isSemistable_map_of_isCoprime (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (h : IsCoprime W.c₄ W.Δ) : IsSemistable (W.map (Int.castRingHom ℚ)) := by
  intro v
  set R := v.adicCompletionIntegers ℚ
  set K := v.adicCompletion ℚ
  apply not_hasAdditiveReduction_minimal (R := R) _ (W.map (Int.castRingHom R))
  · simp only [baseChange, map_map]
    congr 1
    exact RingHom.ext_int _ _
  · rw [baseChange, map_Δ, map_Δ]
    exact (map_ne_zero _).mpr (by simpa using hΔ)
  · obtain ⟨x, y, hxy⟩ := h.map (Int.castRingHom R)
    rw [map_c₄, map_Δ]
    have hu : IsUnit (x * Int.castRingHom R W.c₄ + y * Int.castRingHom R W.Δ) := by
      rw [hxy]; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hu | hu
    · exact Or.inr (isUnit_of_mul_isUnit_right hu)
    · exact Or.inl (isUnit_of_mul_isUnit_right hu)

/-- The curve over $\mathbb{Q}$ of a Weierstrass equation over $\mathbb{Z}$ with $\Delta \ne 0$ is elliptic. -/
theorem isElliptic_map_of_Δ_ne_zero (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.map (Int.castRingHom ℚ)).IsElliptic :=
  ⟨by rw [map_Δ]; exact isUnit_iff_ne_zero.mpr (by simpa using hΔ)⟩

open Bridge Ported.AnthropicFLT

section E11a1

/-- The equation $y^2 + y = x^3 - x^2 - 10x - 20$ of the curve 11a1 over $\mathbb{Z}$. -/
def E11a1Int : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- The curve 11a1 over $\mathbb{Q}$, with the equation $y^2 + y = x^3 - x^2 - 10x - 20$. -/
def E11a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, -10, -20⟩

/-- The curve 11a1 over $\mathbb{Q}$ is the curve of its equation over $\mathbb{Z}$. -/
theorem E11a1_eq_map : E11a1 = E11a1Int.map (Int.castRingHom ℚ) := by
  ext <;> simp [E11a1, E11a1Int]

/-- The discriminant of the equation of 11a1 over $\mathbb{Z}$ is $-11^5$. -/
theorem E11a1Int_Δ : E11a1Int.Δ = -161051 := by decide

/-- The coefficient $c_4$ of the equation of 11a1 over $\mathbb{Z}$ is $496$. -/
theorem E11a1Int_c₄ : E11a1Int.c₄ = 496 := by decide

/-- The discriminant of 11a1 is $-11^5 = -161051$. -/
theorem E11a1_Δ : E11a1.Δ = -161051 := by
  rw [E11a1_eq_map, map_Δ, E11a1Int_Δ]; norm_num

/-- The curve 11a1 is elliptic. -/
instance isElliptic_E11a1 : E11a1.IsElliptic := by
  rw [E11a1_eq_map]; exact isElliptic_map_of_Δ_ne_zero _ (by rw [E11a1Int_Δ]; decide)

/-- The curve 11a1 is semistable. -/
theorem isSemistable_E11a1 : IsSemistable E11a1 := by
  rw [E11a1_eq_map]
  exact isSemistable_map_of_isCoprime _ (by rw [E11a1Int_Δ]; decide)
    (by rw [Int.isCoprime_iff_gcd_eq_one, E11a1Int_Δ, E11a1Int_c₄]; decide)

/-- `ModularitySemistableQ` gives a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 11a1. -/
theorem modular_E11a1_of_semistable (h : ModularitySemistableQ) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E11a1.LFunction n : ℂ) :=
  h E11a1 isSemistable_E11a1

/-- The hypotheses of `modularitySemistableQ_of_anthropicFLT` give a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 11a1. -/
theorem modular_E11a1_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E11a1.LFunction n : ℂ) :=
  modular_E11a1_of_semistable (modularitySemistableQ_of_anthropicFLT hS hM hF)

end E11a1

section E14a1

/-- The equation $y^2 + xy + y = x^3 + 4x - 6$ of the curve 14a1 over $\mathbb{Z}$. -/
def E14a1Int : WeierstrassCurve ℤ := ⟨1, 0, 1, 4, -6⟩

/-- The curve 14a1 over $\mathbb{Q}$, with the equation $y^2 + xy + y = x^3 + 4x - 6$. -/
def E14a1 : WeierstrassCurve ℚ := ⟨1, 0, 1, 4, -6⟩

/-- The curve 14a1 over $\mathbb{Q}$ is the curve of its equation over $\mathbb{Z}$. -/
theorem E14a1_eq_map : E14a1 = E14a1Int.map (Int.castRingHom ℚ) := by
  ext <;> simp [E14a1, E14a1Int]

/-- The discriminant of the equation of 14a1 over $\mathbb{Z}$ is $-2^6 7^3$. -/
theorem E14a1Int_Δ : E14a1Int.Δ = -21952 := by decide

/-- The coefficient $c_4$ of the equation of 14a1 over $\mathbb{Z}$ is $-215$. -/
theorem E14a1Int_c₄ : E14a1Int.c₄ = -215 := by decide

/-- The discriminant of 14a1 is $-2^6 7^3 = -21952$. -/
theorem E14a1_Δ : E14a1.Δ = -21952 := by
  rw [E14a1_eq_map, map_Δ, E14a1Int_Δ]; norm_num

/-- The curve 14a1 is elliptic. -/
instance isElliptic_E14a1 : E14a1.IsElliptic := by
  rw [E14a1_eq_map]; exact isElliptic_map_of_Δ_ne_zero _ (by rw [E14a1Int_Δ]; decide)

/-- The curve 14a1 is semistable. -/
theorem isSemistable_E14a1 : IsSemistable E14a1 := by
  rw [E14a1_eq_map]
  exact isSemistable_map_of_isCoprime _ (by rw [E14a1Int_Δ]; decide)
    (by rw [Int.isCoprime_iff_gcd_eq_one, E14a1Int_Δ, E14a1Int_c₄]; decide)

/-- `ModularitySemistableQ` gives a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 14a1. -/
theorem modular_E14a1_of_semistable (h : ModularitySemistableQ) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E14a1.LFunction n : ℂ) :=
  h E14a1 isSemistable_E14a1

/-- The hypotheses of `modularitySemistableQ_of_anthropicFLT` give a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 14a1. -/
theorem modular_E14a1_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E14a1.LFunction n : ℂ) :=
  modular_E14a1_of_semistable (modularitySemistableQ_of_anthropicFLT hS hM hF)

end E14a1

section E15a1

/-- The equation $y^2 + xy + y = x^3 + x^2 - 10x - 10$ of the curve 15a1 over $\mathbb{Z}$. -/
def E15a1Int : WeierstrassCurve ℤ := ⟨1, 1, 1, -10, -10⟩

/-- The curve 15a1 over $\mathbb{Q}$, with the equation $y^2 + xy + y = x^3 + x^2 - 10x - 10$. -/
def E15a1 : WeierstrassCurve ℚ := ⟨1, 1, 1, -10, -10⟩

/-- The curve 15a1 over $\mathbb{Q}$ is the curve of its equation over $\mathbb{Z}$. -/
theorem E15a1_eq_map : E15a1 = E15a1Int.map (Int.castRingHom ℚ) := by
  ext <;> simp [E15a1, E15a1Int]

/-- The discriminant of the equation of 15a1 over $\mathbb{Z}$ is $3^4 5^4$. -/
theorem E15a1Int_Δ : E15a1Int.Δ = 50625 := by decide

/-- The coefficient $c_4$ of the equation of 15a1 over $\mathbb{Z}$ is $481$. -/
theorem E15a1Int_c₄ : E15a1Int.c₄ = 481 := by decide

/-- The discriminant of 15a1 is $3^4 5^4 = 50625$. -/
theorem E15a1_Δ : E15a1.Δ = 50625 := by
  rw [E15a1_eq_map, map_Δ, E15a1Int_Δ]; norm_num

/-- The curve 15a1 is elliptic. -/
instance isElliptic_E15a1 : E15a1.IsElliptic := by
  rw [E15a1_eq_map]; exact isElliptic_map_of_Δ_ne_zero _ (by rw [E15a1Int_Δ]; decide)

/-- The curve 15a1 is semistable. -/
theorem isSemistable_E15a1 : IsSemistable E15a1 := by
  rw [E15a1_eq_map]
  exact isSemistable_map_of_isCoprime _ (by rw [E15a1Int_Δ]; decide)
    (by rw [Int.isCoprime_iff_gcd_eq_one, E15a1Int_Δ, E15a1Int_c₄]; decide)

/-- `ModularitySemistableQ` gives a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 15a1. -/
theorem modular_E15a1_of_semistable (h : ModularitySemistableQ) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E15a1.LFunction n : ℂ) :=
  h E15a1 isSemistable_E15a1

/-- The hypotheses of `modularitySemistableQ_of_anthropicFLT` give a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 15a1. -/
theorem modular_E15a1_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E15a1.LFunction n : ℂ) :=
  modular_E15a1_of_semistable (modularitySemistableQ_of_anthropicFLT hS hM hF)

end E15a1

section E17a1

/-- The equation $y^2 + xy + y = x^3 - x^2 - x - 14$ of the curve 17a1 over $\mathbb{Z}$. -/
def E17a1Int : WeierstrassCurve ℤ := ⟨1, -1, 1, -1, -14⟩

/-- The curve 17a1 over $\mathbb{Q}$, with the equation $y^2 + xy + y = x^3 - x^2 - x - 14$. -/
def E17a1 : WeierstrassCurve ℚ := ⟨1, -1, 1, -1, -14⟩

/-- The curve 17a1 over $\mathbb{Q}$ is the curve of its equation over $\mathbb{Z}$. -/
theorem E17a1_eq_map : E17a1 = E17a1Int.map (Int.castRingHom ℚ) := by
  ext <;> simp [E17a1, E17a1Int]

/-- The discriminant of the equation of 17a1 over $\mathbb{Z}$ is $-17^4$. -/
theorem E17a1Int_Δ : E17a1Int.Δ = -83521 := by decide

/-- The coefficient $c_4$ of the equation of 17a1 over $\mathbb{Z}$ is $33$. -/
theorem E17a1Int_c₄ : E17a1Int.c₄ = 33 := by decide

/-- The discriminant of 17a1 is $-17^4 = -83521$. -/
theorem E17a1_Δ : E17a1.Δ = -83521 := by
  rw [E17a1_eq_map, map_Δ, E17a1Int_Δ]; norm_num

/-- The curve 17a1 is elliptic. -/
instance isElliptic_E17a1 : E17a1.IsElliptic := by
  rw [E17a1_eq_map]; exact isElliptic_map_of_Δ_ne_zero _ (by rw [E17a1Int_Δ]; decide)

/-- The curve 17a1 is semistable. -/
theorem isSemistable_E17a1 : IsSemistable E17a1 := by
  rw [E17a1_eq_map]
  exact isSemistable_map_of_isCoprime _ (by rw [E17a1Int_Δ]; decide)
    (by rw [Int.isCoprime_iff_gcd_eq_one, E17a1Int_Δ, E17a1Int_c₄]; decide)

/-- `ModularitySemistableQ` gives a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 17a1. -/
theorem modular_E17a1_of_semistable (h : ModularitySemistableQ) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E17a1.LFunction n : ℂ) :=
  h E17a1 isSemistable_E17a1

/-- The hypotheses of `modularitySemistableQ_of_anthropicFLT` give a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 17a1. -/
theorem modular_E17a1_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E17a1.LFunction n : ℂ) :=
  modular_E17a1_of_semistable (modularitySemistableQ_of_anthropicFLT hS hM hF)

end E17a1

section E37a1

/-- The equation $y^2 + y = x^3 - x$ of the curve 37a1 over $\mathbb{Z}$. -/
def E37a1Int : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- The curve 37a1 over $\mathbb{Q}$, with the equation $y^2 + y = x^3 - x$. -/
def E37a1 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- The curve 37a1 over $\mathbb{Q}$ is the curve of its equation over $\mathbb{Z}$. -/
theorem E37a1_eq_map : E37a1 = E37a1Int.map (Int.castRingHom ℚ) := by
  ext <;> simp [E37a1, E37a1Int]

/-- The discriminant of the equation of 37a1 over $\mathbb{Z}$ is $37$. -/
theorem E37a1Int_Δ : E37a1Int.Δ = 37 := by decide

/-- The coefficient $c_4$ of the equation of 37a1 over $\mathbb{Z}$ is $48$. -/
theorem E37a1Int_c₄ : E37a1Int.c₄ = 48 := by decide

/-- The discriminant of 37a1 is $37$. -/
theorem E37a1_Δ : E37a1.Δ = 37 := by
  rw [E37a1_eq_map, map_Δ, E37a1Int_Δ]; norm_num

/-- The curve 37a1 is elliptic. -/
instance isElliptic_E37a1 : E37a1.IsElliptic := by
  rw [E37a1_eq_map]; exact isElliptic_map_of_Δ_ne_zero _ (by rw [E37a1Int_Δ]; decide)

/-- The curve 37a1 is semistable. -/
theorem isSemistable_E37a1 : IsSemistable E37a1 := by
  rw [E37a1_eq_map]
  exact isSemistable_map_of_isCoprime _ (by rw [E37a1Int_Δ]; decide)
    (by rw [Int.isCoprime_iff_gcd_eq_one, E37a1Int_Δ, E37a1Int_c₄]; decide)

/-- `ModularitySemistableQ` gives a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 37a1. -/
theorem modular_E37a1_of_semistable (h : ModularitySemistableQ) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E37a1.LFunction n : ℂ) :=
  h E37a1 isSemistable_E37a1

/-- The hypotheses of `modularitySemistableQ_of_anthropicFLT` give a cusp form of weight 2 on $\Gamma_0(N)$ whose coefficients are those of $L(E, s)$ for $E$ = 37a1. -/
theorem modular_E37a1_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E37a1.LFunction n : ℂ) :=
  modular_E37a1_of_semistable (modularitySemistableQ_of_anthropicFLT hS hM hF)

end E37a1

end Langlands.Modular
