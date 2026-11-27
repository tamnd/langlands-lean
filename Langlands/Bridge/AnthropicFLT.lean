/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Definitions/Def_FLTPrelim_Modularity.lean
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean
-- The ported definitions are Copyright 2026 Anthropic, PBC, released under the Apache License, Version 2.0.
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Langlands.Statements.Modularity

/-!
# The bridge to the anthropics FLT port: modularity of semistable curves

The repository anthropics/fermats-last-theorem (Apache 2.0) proves `WeierstrassCurve.modularity_of_semistableModel`. This file copies the statement of that theorem and the definitions that it uses, and compares it with `Langlands.ModularitySemistableQ`.

The source is the commit `6e837e75355538c7f80bab5b956861e86c4eacc2` of anthropics/fermats-last-theorem, on the toolchain `v4.33.1`. The statement is in `Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean`, line 131. The definitions are in `Definitions/Def_FLTPrelim_Modularity.lean`. The file `ATTRIBUTION.md` of the source does not list this definitions file as derived from a third party work, so its copyright holder is Anthropic, PBC, as the file `NOTICE` of the source states.

## Main definitions

* `Langlands.Ported.AnthropicFLT.IsSemistableModel`: an integral Weierstrass equation $W$ is a semistable model if for each prime $p$ with $p \mid \Delta(W)$ we have $p \nmid c_4(W)$.
* `Langlands.Ported.AnthropicFLT.IsModular`: an elliptic curve $E$ over $\mathbb{Q}$ is modular if it has an integral model $W$ and a normalized eigenform $f$ of weight 2 on $\Gamma_0(N)$ with $a_p(f) = a_p(W)$ for each prime $p$ of good reduction of $W$ with $p \nmid N$.
* `Langlands.Ported.AnthropicFLT.ModularityOfSemistableModel`: the statement of `WeierstrassCurve.modularity_of_semistableModel`, as a `Prop`.
* `Langlands.Bridge.SemistableIntegralModel`: each semistable elliptic curve over $\mathbb{Q}$ in the sense of `Langlands.IsSemistable` has an integral model that is a semistable model.
* `Langlands.Bridge.FullCoefficientsOfModular`: a semistable curve that is modular in the sense of the source has a cusp form whose coefficients are all the coefficients of $L(E, s)$.

## Main results

* `Langlands.Bridge.isModular_of_isSemistable`: the statement of the source and `SemistableIntegralModel` give `IsModular E` for each semistable elliptic curve $E$ over $\mathbb{Q}$.
* `Langlands.Bridge.modularitySemistableQ_of_anthropicFLT`: the statement of the source, `SemistableIntegralModel` and `FullCoefficientsOfModular` give `Langlands.ModularitySemistableQ`. This is the `proved-mod` form of 09.2.2 of the spec.

## The changes to the source

* The theorem `WeierstrassCurve.modularity_of_semistableModel` is the `def` `ModularityOfSemistableModel` of type `Prop`, with the same binders and the same conclusion. Its proof in the source is not ported. The theorem enters only as a hypothesis.
* The definitions are in the namespace `Langlands.Ported.AnthropicFLT` and have the last component of their source name: `ModularFormClass.qCoeff` is `qCoeff`, `CuspForm.IsNormalizedEigenform` is `IsNormalizedEigenform`, and `WeierstrassCurve.card`, `traceOfFrobenius`, `reductionMod`, `apOfModel`, `IsGoodPrimeFor`, `IsSemistableModel`, `IsIntegralModelOf`, `IsModularModelOfLevel`, `IsModularModel` and `IsModular` keep their last component. Thus the dot notation of the source is function application here.
* The instance `WeierstrassCurve.Affine.Point.instFinite` and its two private lemmas are not ported. The definitions use `Nat.card`, which does not need the instance.
* The definitions are otherwise copied without change. The source spelling `CuspForm (CongruenceSubgroup.Gamma0 N) 2` elaborates on the toolchain of the project to the same type as the spelling of `Langlands/Statements/Modularity.lean`.

## The gap between the two statements

The two statements differ in three points.

1. The hypothesis. The source takes an integral equation $W$ with $\Delta(W) \ne 0$ and $p \mid \Delta \Rightarrow p \nmid c_4$. The project takes a curve $E$ over $\mathbb{Q}$ with no additive reduction at a minimal model of each completion. A semistable $E$ has such an integral model: its global minimal model, which exists because $\mathbb{Z}$ is a principal ideal domain, has multiplicative reduction at each bad prime, so $p \nmid c_4$ there. This is `SemistableIntegralModel`. It needs Tate's criterion and global minimal models over $\mathbb{Q}$, which Mathlib does not have.
2. The coefficients. The source asks for $a_p(f) = a_p(W)$ only at the primes $p$ of good reduction with $p \nmid N$, and $a_p(W)$ is $p + 1 - \# W(\mathbb{F}_p)$ of the reduction of $W$ modulo $p$. The project asks for $a_n(f) = a_n(E)$ for every $n \ge 1$, with the coefficients of `WeierstrassCurve.LFunction`. The passage needs strong multiplicity one, the newform of level the conductor (Carayol), the local factors at the bad primes, and the comparison of the reduction modulo $p$ with the reduction of the minimal model over $\mathbb{Z}_p$. This is `FullCoefficientsOfModular`.
3. The model. The source concludes for the curve `W.map (Int.castRingHom ℚ)`, which is isomorphic to $E$ but not equal to $E$. The definition `IsModular` is stable under a change of variables, and the proof of `isModular_of_isSemistable` composes the two changes of variables. This point is proved here.

The converse implication also needs points 1 and 2, and in addition that a form with the coefficients of $L(E, s)$ at a level $N$ that the bad primes divide is a normalized eigenform in the sense of the source.

## References

* A. Wiles, Modular elliptic curves and Fermat's last theorem, Ann. of Math. 141 (1995).
* R. Taylor and A. Wiles, Ring-theoretic properties of certain Hecke algebras, Ann. of Math. 141 (1995).
* H. Carayol, Sur les représentations l-adiques associées aux formes modulaires de Hilbert, Ann. Sci. ENS 19 (1986).
* J. Silverman, The arithmetic of elliptic curves, second edition, 2009.
-/

noncomputable section

namespace Langlands.Ported.AnthropicFLT

open UpperHalfPlane WeierstrassCurve

universe u

/-- The coefficient of $q^n$ in the $q$-expansion of $f$ with the parameter $q = e^{2 \pi i \tau}$. This is `ModularFormClass.qCoeff` of the source. -/
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

/-- A cusp form of weight 2 on $\Gamma_0(N)$ is a normalized eigenform if $a_1 = 1$, the coefficients are multiplicative, and they satisfy the recursion of the Euler factor at each prime. This is `CuspForm.IsNormalizedEigenform` of the source. -/
structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where
  /-- The first coefficient is 1. -/
  qCoeff_one : qCoeff f 1 = 1
  /-- The coefficients are multiplicative. -/
  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n
  /-- The recursion at a prime that does not divide the level. -/
  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)
  /-- The recursion at a prime that divides the level. -/
  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))

section Card

variable {F : Type u} [CommRing F] (W : WeierstrassCurve F)

/-- The number of points of $W$, with the point at infinity. This is `WeierstrassCurve.card` of the source. -/
def card : ℕ := Nat.card W.toAffine.Point

/-- The trace of Frobenius $\# F + 1 - \# W(F)$. This is `WeierstrassCurve.traceOfFrobenius` of the source. -/
def traceOfFrobenius : ℤ := (Nat.card F : ℤ) + 1 - (card W : ℤ)

end Card

/-- The reduction of an integral Weierstrass equation modulo $p$. This is `WeierstrassCurve.reductionMod` of the source. -/
def reductionMod (W : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  W.map (Int.castRingHom (ZMod p))

/-- The coefficient $a_p(W) = p + 1 - \# W(\mathbb{F}_p)$ of an integral Weierstrass equation. This is `WeierstrassCurve.apOfModel` of the source. -/
def apOfModel (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  traceOfFrobenius (reductionMod W p)

/-- The prime $p$ is good for the integral equation $W$ if $p \nmid \Delta(W)$. This is `WeierstrassCurve.IsGoodPrimeFor` of the source. -/
def IsGoodPrimeFor (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ W.Δ

/-- The integral equation $W$ is a semistable model if each prime that divides $\Delta(W)$ does not divide $c_4(W)$. This is `WeierstrassCurve.IsSemistableModel` of the source. -/
def IsSemistableModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄

/-- The integral equation $W$ is an integral model of $E$ if a change of variables over $\mathbb{Q}$ takes $E$ to $W$. This is `WeierstrassCurve.IsIntegralModelOf` of the source. -/
def IsIntegralModelOf (W : WeierstrassCurve ℤ) (E : WeierstrassCurve ℚ) : Prop :=
  ∃ C : VariableChange ℚ, C • E = W.map (Int.castRingHom ℚ)

/-- The integral equation $W$ is modular of level $N$ if a normalized eigenform $f$ of weight 2 on $\Gamma_0(N)$ has $a_p(f) = a_p(W)$ for each good prime $p \nmid N$. This is `WeierstrassCurve.IsModularModelOfLevel` of the source. -/
def IsModularModelOfLevel (W : WeierstrassCurve ℤ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, IsNormalizedEigenform f ∧
    ∀ p : ℕ, p.Prime → IsGoodPrimeFor W p → ¬ p ∣ N →
      qCoeff f p = (apOfModel W p : ℂ)

/-- The integral equation $W$ is modular if it is modular of some level $N \ge 1$. This is `WeierstrassCurve.IsModularModel` of the source. -/
def IsModularModel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ IsModularModelOfLevel W N

/-- The curve $E$ over $\mathbb{Q}$ is modular if it has an integral model that is modular. This is `WeierstrassCurve.IsModular` of the source. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ W : WeierstrassCurve ℤ, IsIntegralModelOf W E ∧ IsModularModel W

/-- **Modularity of semistable models** (Wiles, Taylor-Wiles), the statement of `WeierstrassCurve.modularity_of_semistableModel` of anthropics/fermats-last-theorem. An integral Weierstrass equation $W$ with $\Delta(W) \ne 0$ that is a semistable model gives a modular curve over $\mathbb{Q}$. -/
def ModularityOfSemistableModel : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0) (_hW : IsSemistableModel W),
    IsModular (W.map (Int.castRingHom ℚ))

end Langlands.Ported.AnthropicFLT

namespace Langlands.Bridge

open Ported.AnthropicFLT WeierstrassCurve

/-- Each semistable elliptic curve over $\mathbb{Q}$ in the sense of `Langlands.IsSemistable` has an integral model that is a semistable model in the sense of the source. This follows from the existence of a global minimal model over $\mathbb{Q}$ and Tate's criterion: a minimal model with multiplicative reduction at $p$ has $p \nmid c_4$. Reference: Silverman, Chapter VII and Section VIII.8. -/
def SemistableIntegralModel : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsSemistable E →
    ∃ W : WeierstrassCurve ℤ, IsIntegralModelOf W E ∧ IsSemistableModel W

/-- A semistable elliptic curve over $\mathbb{Q}$ that is modular in the sense of the source has a cusp form of weight 2 on $\Gamma_0(N)$ for some $N \ge 1$ whose coefficients are all the coefficients of $L(E, s)$. This follows from strong multiplicity one, the theorem of Carayol on the level of the newform, and the local factors at the bad primes. -/
def FullCoefficientsOfModular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsSemistable E → IsModular E →
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → Langlands.qCoeff f n = (E.LFunction n : ℂ)

/-- An integral model of an integral model is an integral model. -/
theorem isIntegralModelOf_trans {W W' : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ}
    (h' : IsIntegralModelOf W' (W.map (Int.castRingHom ℚ))) (h : IsIntegralModelOf W E) :
    IsIntegralModelOf W' E := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  exact ⟨C' * C, by rw [mul_smul, hC, hC']⟩

/-- The discriminant of an integral model of an elliptic curve is not zero. -/
theorem Δ_ne_zero_of_isIntegralModelOf {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (h : IsIntegralModelOf W E) : W.Δ ≠ 0 := by
  obtain ⟨C, hC⟩ := h
  intro hW
  have h1 : (C • E).Δ = 0 := by rw [hC, map_Δ, hW, map_zero]
  rw [variableChange_Δ] at h1
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) E.isUnit_Δ.ne_zero h1

/-- A curve that is modular in the sense of the source stays modular after a change of variables that takes it to an integral equation. -/
theorem isModular_of_isIntegralModelOf {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ}
    (h : IsIntegralModelOf W E) (hW : IsModular (W.map (Int.castRingHom ℚ))) : IsModular E := by
  obtain ⟨W', hW', hM⟩ := hW
  exact ⟨W', isIntegralModelOf_trans hW' h, hM⟩

/-- The statement of the source and `SemistableIntegralModel` give `IsModular E` for each semistable elliptic curve $E$ over $\mathbb{Q}$. -/
theorem isModular_of_isSemistable (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : IsSemistable E) : IsModular E := by
  obtain ⟨W, hWE, hW⟩ := hM E hE
  exact isModular_of_isIntegralModelOf hWE (hS W (Δ_ne_zero_of_isIntegralModelOf hWE) hW)

/-- **Modularity of semistable elliptic curves over $\mathbb{Q}$ from the anthropics FLT port**, `proved-mod` the hypotheses `SemistableIntegralModel` and `FullCoefficientsOfModular`. The statement `ModularityOfSemistableModel` of the source enters only as a hypothesis. -/
theorem modularitySemistableQ_of_anthropicFLT (hS : ModularityOfSemistableModel)
    (hM : SemistableIntegralModel) (hF : FullCoefficientsOfModular) :
    ModularitySemistableQ := by
  intro E _ hE
  exact hF E hE (isModular_of_isSemistable hS hM E hE)

end Langlands.Bridge
