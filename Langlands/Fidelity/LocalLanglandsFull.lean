/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.LanglandsFamilyPairsEps
import Langlands.Local.GL1LFactor

/-!
# Fidelity checks for the local Langlands correspondence with the factors of pairs

This file has the fidelity checks F2, F3 and F4 of spec 06.3 for the statement `Langlands.LocalLanglandsGLFull` of `Langlands.Local.LanglandsFamilyPairs`.

## Main definitions

* `Langlands.Fidelity.detFrob`: the determinant $\det(-q^{-s} \Phi \mid (V^{I_K})_{N = 0})$ that occurs in the condition `monodromy` of `Langlands.IsWDEpsilon`.
* `Langlands.Fidelity.epsTate`: Tate's ε-factor of a character for a Haar measure and an additive character with a conductor, and $1$ in the other cases.
* `Langlands.Fidelity.galEps`: a Galois ε-factor in each dimension. It is Tate's ε-factor of $\det r \circ \mathrm{art}_K$ in dimension one, and it is $1$ on the representations with $N = 0$ in the other dimensions. Deligne's formula for the monodromy gives the value when $N \neq 0$.
* `Langlands.Fidelity.galEpsSign`: the factor `galEps` multiplied by $-1$ in dimension two.
* `Langlands.Fidelity.trivWD`: the trivial Weil-Deligne representation $(1, 0)$ of dimension $m$.

## Main results

* `Langlands.Fidelity.det_smul_frob_eq_of_iso`: isomorphic Weil-Deligne representations have the same $\det(c \Phi \mid (V^{I_K})_{N = 0})$.
* `Langlands.Fidelity.isWDEpsilon_galEps`: `galEps` has the conditions of `IsWDEpsilon`.
* `Langlands.Fidelity.isLanglandsFamilyPairs_recFamily`: the family $(\mathrm{rec}_0, \mathrm{rec}_1)$ has the conditions of `IsLanglandsFamilyPairs` for `galEps`.
* `Langlands.Fidelity.localLanglandsGLFull_one`: F2, the statement `LocalLanglandsGLFull 1` holds.
* `Langlands.Fidelity.isWDEpsilon_galEpsSign`, `Langlands.Fidelity.galEps_ne_galEpsSign`: F3, the conditions `IsWDEpsilon` do not determine the Galois ε-factor.
* `Langlands.Fidelity.not_unique_epsilon_one`: F3, two different Galois ε-factors give the conditions of `IsLanglandsFamilyPairs` for the same family $(\mathrm{rec}_0, \mathrm{rec}_1)$.
* `Langlands.Fidelity.subsingleton_wdIso_zero`: the Weil-Deligne representations of dimension zero are all isomorphic.
* `Langlands.Fidelity.recFamily_unique`: for $n = 1$, the conditions of `IsLanglandsFamily` determine the family. So for $n = 1$ the conditions on pairs add no information on $\mathrm{rec}$.
* `Langlands.Fidelity.nonempty_irrSmooth_one`, `Langlands.Fidelity.nonempty_wdIso`: F4, the types of the correspondence are not empty.

## F2

The witness for `LocalLanglandsGLFull 1` is the family `Langlands.LocalGL1.recFamily` of `Langlands.Local.GL1`, with the ε-factor `galEps`. The conditions on pairs for $m = m' = 1$ are `Langlands.isRSLFactor_tensor_wdOfChar` and `Langlands.isRSEpsilonFactor_one`. The proof found no hypothesis of the statement that is contradictory. Two points of the statement are weak:

* The condition `dimOne` of `IsWDEpsilon` asks for Tate's functional equation for each conductor exponent $k$ of $\psi$, but the value of $\varepsilon$ does not depend on $k$. The proof does not need the uniqueness of the conductor exponent: it uses the exponent that `Classical.choose` gives, and Tate's functional equation for this exponent.
* The condition `epsilonPair` asks for the self dual measure, but for $GL_1$ the two ε-factors of pairs agree for each Haar measure. The hypothesis `IsSelfDual` is not used.
* The condition `iso` of `IsWDEpsilon` forces the proof `det_smul_frob_eq_of_iso`, because the condition `monodromy` fixes $\varepsilon(\rho)$ from $\varepsilon((r, 0))$ and the determinants on $(V^{I_K})_{N = 0}$.

## F3

The ε-factor in `LocalLanglandsGLFull` is a parameter with the conditions of `IsWDEpsilon`. These conditions do not determine it in dimension $m \ge 2$: `galEpsSign` is a second ε-factor with these conditions, and it is different from `galEps` in dimension two. For $n = 1$ both give the conditions of `IsLanglandsFamilyPairs` for the same family, so the ε-factor in a witness of `LocalLanglandsGLFull 1` is not unique. For $n \ge 2$ the ε-factor of the tensor products $\rho \otimes \rho'$ of dimension $m m' \ge 2$ is free up to the conditions of `IsWDEpsilon`. Thus condition 6 compares the Rankin-Selberg ε-factor with a function that the statement chooses, not with the ε-factor of Deligne and Langlands. This is the weakness that the implementation notes of `Langlands.Local.LanglandsFamilyPairs` state; the results here prove it.

The variant of spec 06.3, a second family that satisfies `IsLanglandsFamily` (a twist by an unramified quadratic character for $n = 2$), needs a correspondence for $GL_2$, which is not in the library. For $n = 1$ there is no such second family: `recFamily_unique` proves that the conditions of `IsLanglandsFamily` determine $\mathrm{rec}_0$ and $\mathrm{rec}_1$.

## F4

The statement is not true for a trivial reason:

* The types are not empty. `nonempty_irrSmooth_one` gives the class of the trivial character of $GL_1(K)$, and `nonempty_wdIso` gives the trivial Weil-Deligne representation in each dimension. The bijections $\mathrm{rec}_m$ are between types that `Langlands.LocalGL1.irrEquiv` and `Langlands.LocalGL1.wdEquiv` identify with the smooth characters of $K^\times$ for $m = 1$.
* The bijections are not found by cardinality: condition 1 fixes $\mathrm{rec}_1$ (`recFamily_unique`), and conditions 2 to 6 relate it to the other $\mathrm{rec}_m$.
* The topologies are the ones of the library. $GL_m(K)$ has the topology of the matrices over the local field $K$, and the Weil group has the topology of `Langlands.WeilGroup`, with an open inertia subgroup. The smoothness conditions are not empty for these topologies.
* The ε-factor is an existential parameter. In dimension one it is fixed by Tate's functional equation, and the condition `monomial` asks for $c \neq 0$. So the conditions on pairs are not satisfied by $\varepsilon = 0$.

## What is still open

* `LocalLanglandsGLFull n` for $n \ge 2$.
* A Galois ε-factor that is determined by its conditions, with the additivity and the inductivity in degree zero.
* A second family with the conditions of `IsLanglandsFamily` for $n = 2$.
-/

namespace Langlands.Fidelity

universe u

open Langlands LocalGL1 MeasureTheory Matrix

section Epsilon

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {m : ℕ}

/-- The determinant $\det(-q^{-s} \Phi \mid (V^{I_K})_{N = 0})$ of the condition `monodromy` of `IsWDEpsilon`. -/
noncomputable def detFrob (ρ : WeilDeligneRep K m) (s : ℂ) : ℂ :=
  LinearMap.det (-((residueCard K : ℂ) ^ (-s)) • ρ.frobOnLSpace)

/-- The representation $(r, 0)$ of $(r, 0)$ is $(r, 0)$. -/
theorem forgetN_forgetN (ρ : WeilDeligneRep K m) : ρ.forgetN.forgetN = ρ.forgetN :=
  rfl

/-- A conjugation by $g$ sends $(V^{I_K})_{N = 0}$ of $\rho$ into the space of $\rho'$. -/
theorem mulVec_mem_lSpace {ρ ρ' : WeilDeligneRep K m} (g : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ))
    {v : Fin m → ℂ} (hv : v ∈ ρ.lSpace) : (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v ∈ ρ'.lSpace := by
  have key : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) *ᵥ ((g : Matrix _ _ ℂ) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key, hv.1, Matrix.mulVec_zero]
  · rw [hr, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key,
      hv.2 i hi]

/-- The linear map $v \mapsto g v$ from $(V^{I_K})_{N = 0}$ of $\rho$ to the space of $\rho'$. -/
noncomputable def lSpaceMap {ρ ρ' : WeilDeligneRep K m} (g : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ)) :
    ρ.lSpace →ₗ[ℂ] ρ'.lSpace :=
  (Matrix.toLin' (g : Matrix (Fin m) (Fin m) ℂ)).restrict fun _ hv => mulVec_mem_lSpace g hr hN hv

/-- The map `lSpaceMap` is $v \mapsto g v$. -/
theorem lSpaceMap_apply {ρ ρ' : WeilDeligneRep K m} (g : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ)) (v : ρ.lSpace) :
    (lSpaceMap g hr hN v : Fin m → ℂ) = (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ (v : Fin m → ℂ) :=
  rfl

/-- The action of the Frobenius on $(V^{I_K})_{N = 0}$ is $v \mapsto r(\Phi) v$. -/
theorem frobOnLSpace_apply (ρ : WeilDeligneRep K m) (v : ρ.lSpace) :
    (ρ.frobOnLSpace v : Fin m → ℂ) = (ρ.r (geomFrob K) : Matrix (Fin m) (Fin m) ℂ) *ᵥ (v : Fin m → ℂ) :=
  rfl

/-- The inverse equations of a conjugation. -/
theorem iso_symm_eqs {ρ ρ' : WeilDeligneRep K m} (g : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ)) :
    (∀ w, ρ.r w = g⁻¹ * ρ'.r w * g⁻¹⁻¹) ∧
      ρ.N = ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * ρ'.N * (g⁻¹⁻¹ : GL (Fin m) ℂ) := by
  refine ⟨fun w => by simp [hr, mul_assoc], ?_⟩
  rw [hN, inv_inv]
  simp [← mul_assoc]

/-- The maps $v \mapsto g v$ and $v \mapsto g^{-1} v$ are inverse. -/
theorem lSpaceMap_comp {ρ ρ' : WeilDeligneRep K m} (g g' : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ))
    (hr' : ∀ w, ρ.r w = g' * ρ'.r w * g'⁻¹)
    (hN' : ρ.N = (g' : Matrix (Fin m) (Fin m) ℂ) * ρ'.N * (g'⁻¹ : GL (Fin m) ℂ)) (hg : g' * g = 1) :
    lSpaceMap g' hr' hN' ∘ₗ lSpaceMap g hr hN = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [LinearMap.comp_apply, lSpaceMap_apply, lSpaceMap_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hg,
    Units.val_one, Matrix.one_mulVec, LinearMap.id_apply]

/-- The map $v \mapsto g v$ commutes with the Frobenius. -/
theorem lSpaceMap_frob {ρ ρ' : WeilDeligneRep K m} (g : GL (Fin m) ℂ)
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ)) :
    lSpaceMap g hr hN ∘ₗ ρ.frobOnLSpace = ρ'.frobOnLSpace ∘ₗ lSpaceMap g hr hN := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lSpaceMap_apply, frobOnLSpace_apply, frobOnLSpace_apply,
    lSpaceMap_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr, Units.val_mul, Units.val_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- Isomorphic Weil-Deligne representations have the same determinant $\det(c \Phi \mid (V^{I_K})_{N = 0})$. -/
theorem det_smul_frob_eq_of_iso {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') (c : ℂ) :
    LinearMap.det (c • ρ'.frobOnLSpace) = LinearMap.det (c • ρ.frobOnLSpace) := by
  obtain ⟨g, hr, hN⟩ := h
  obtain ⟨hr', hN'⟩ := iso_symm_eqs g hr hN
  set f := lSpaceMap g hr hN
  set f' := lSpaceMap g⁻¹ hr' hN'
  have h1 : f' ∘ₗ f = LinearMap.id := lSpaceMap_comp g g⁻¹ hr hN hr' hN' (inv_mul_cancel g)
  have h2 : f ∘ₗ f' = LinearMap.id := by
    obtain ⟨hr'', hN''⟩ := iso_symm_eqs g⁻¹ hr' hN'
    have := lSpaceMap_comp g⁻¹ g⁻¹⁻¹ hr' hN' hr'' hN'' (inv_mul_cancel g⁻¹)
    simpa only [inv_inv] using this
  let e : ρ.lSpace ≃ₗ[ℂ] ρ'.lSpace := LinearEquiv.ofLinearMap f f' h2 h1
  have hc : c • ρ'.frobOnLSpace =
      (e : ρ.lSpace →ₗ[ℂ] ρ'.lSpace) ∘ₗ (c • ρ.frobOnLSpace) ∘ₗ (e.symm : ρ'.lSpace →ₗ[ℂ] ρ.lSpace) := by
    change c • ρ'.frobOnLSpace = f ∘ₗ (c • ρ.frobOnLSpace) ∘ₗ f'
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ← LinearMap.comp_assoc, lSpaceMap_frob,
      LinearMap.comp_assoc, h2, LinearMap.comp_id]
  rw [hc, LinearMap.det_conj]

/-- The action of the Frobenius on $(V^{I_K})_{N = 0}$ has a nonzero determinant. -/
theorem det_frobOnLSpace_ne_zero (ρ : WeilDeligneRep K m) : LinearMap.det ρ.frobOnLSpace ≠ 0 := by
  let f' : Module.End ℂ ρ.lSpace :=
    (Matrix.toLin' (ρ.r (geomFrob K)⁻¹ : Matrix (Fin m) (Fin m) ℂ)).restrict (ρ.lSpace_stable _)
  have h : f' * ρ.frobOnLSpace = 1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    change (ρ.r (geomFrob K)⁻¹ : Matrix (Fin m) (Fin m) ℂ) *ᵥ
      ((ρ.r (geomFrob K) : Matrix (Fin m) (Fin m) ℂ) *ᵥ v.1) = v.1
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  intro h0
  have := congrArg LinearMap.det h
  rw [map_mul, h0, mul_zero, map_one] at this
  exact zero_ne_one this

/-- The value $q^{-s}$ is not zero. -/
theorem qpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast (residueCard_pos' (K := K)).ne'
  exact Complex.cpow_ne_zero_iff.2 (Or.inl hq)

/-- The determinant `detFrob` is not zero. -/
theorem detFrob_ne_zero (ρ : WeilDeligneRep K m) (s : ℂ) : detFrob ρ s ≠ 0 := by
  rw [detFrob, LinearMap.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (qpow_ne_zero s))) (det_frobOnLSpace_ne_zero ρ)

/-- The determinant `detFrob` is $(-1)^d \det \Phi \cdot (q^{-s})^d$ with $d$ the dimension of $(V^{I_K})_{N = 0}$. -/
theorem detFrob_eq (ρ : WeilDeligneRep K m) (s : ℂ) :
    detFrob ρ s = (-1) ^ Module.finrank ℂ ρ.lSpace * LinearMap.det ρ.frobOnLSpace *
      ((residueCard K : ℂ) ^ (-s)) ^ Module.finrank ℂ ρ.lSpace := by
  rw [detFrob, LinearMap.det_smul, neg_eq_neg_one_mul, mul_pow]
  ring

/-- Isomorphic Weil-Deligne representations have the same `detFrob`. -/
theorem detFrob_eq_of_iso {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') : detFrob ρ' = detFrob ρ :=
  funext fun _ => det_smul_frob_eq_of_iso h _

/-- An isomorphism of $\rho$ and $\rho'$ gives an isomorphism of $(r, 0)$ and $(r', 0)$. -/
theorem forgetN_iso {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') : ρ.forgetN.Iso ρ'.forgetN := by
  obtain ⟨g, hr, -⟩ := h
  exact ⟨g, hr, by simp [WeilDeligneRep.forgetN]⟩

variable (K) in
/-- Isomorphic Weil-Deligne representations give the same character $\det r \circ \mathrm{art}_K$. -/
theorem charOfWD_eq_of_iso (art : Kˣ ≃ₜ* WeilGroup.Ab K) {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') :
    charOfWD K art ρ' = charOfWD K art ρ := by
  ext x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
  rw [charOfWD_apply K art ρ hw, charOfWD_apply K art ρ' hw, WeilDeligneRep.det_eq_of_iso h]

variable [MeasurableSpace K] [BorelSpace K]

open Classical in
/-- Tate's ε-factor $\varepsilon(s, \chi, \psi)$ for the measure $\mu$, if $\mu$ is a Haar measure and $\psi$ has a conductor exponent; the exponent is the one that `Classical.choose` gives. In the other cases the value is $1$. -/
noncomputable def epsTate (μ : Measure K) (χ : Kˣ →* ℂˣ) (ψ : AddChar K ℂ) (s : ℂ) : ℂ :=
  if h : μ.IsAddHaarMeasure ∧ ∃ k, IsConductor ψ k then
    haveI := h.1
    tateEpsilon μ χ ψ h.2.choose s
  else 1

omit [BorelSpace K] in
/-- For a Haar measure and an additive character with a conductor exponent, `epsTate` is `tateEpsilon` for some conductor exponent. -/
theorem epsTate_eq (μ : Measure K) [hμ : μ.IsAddHaarMeasure] (χ : Kˣ →* ℂˣ) {ψ : AddChar K ℂ} {k : ℤ}
    (hψ : IsConductor ψ k) : ∃ k', IsConductor ψ k' ∧ epsTate μ χ ψ = tateEpsilon μ χ ψ k' := by
  have h : μ.IsAddHaarMeasure ∧ ∃ k, IsConductor ψ k := ⟨hμ, k, hψ⟩
  exact ⟨h.2.choose, h.2.choose_spec, funext fun s => by simp only [epsTate, h, and_self, ↓reduceDIte]⟩

/-- For a smooth character, `epsTate` is a monomial $c (q^{-s})^k$ with $c \neq 0$. -/
theorem epsTate_monomial (μ : Measure K) {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (ψ : AddChar K ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, ∀ s, epsTate μ χ ψ s = c * ((residueCard K : ℂ) ^ (-s)) ^ k := by
  by_cases h : μ.IsAddHaarMeasure ∧ ∃ k, IsConductor ψ k
  · have := h.1
    obtain ⟨k, hk⟩ := h.2
    obtain ⟨k', hk', he⟩ := epsTate_eq μ χ hk
    rw [he]
    exact tateEpsilon_monomial μ hχ hk'
  · exact ⟨1, one_ne_zero, 0, fun s => by simp [epsTate, h]⟩

variable (K) in
/-- **A Galois ε-factor in each dimension.** On a representation $\rho$ with $(r, 0) = \rho_0$ the value is $E(\rho_0) \det(-q^{-s} \Phi \mid V^{I_K}) / \det(-q^{-s} \Phi \mid (V^{I_K})_{N = 0})$, where $E(\rho_0)$ is Tate's ε-factor of $\det r \circ \mathrm{art}_K$ in dimension one and $1$ in the other dimensions. This is the form that Deligne's formula for the monodromy forces. -/
noncomputable def galEps (art : Kˣ ≃ₜ* WeilGroup.Ab K) : WDEpsilonFn K :=
  fun μ m ρ ψ s =>
    (if m = 1 then epsTate μ (charOfWD K art ρ.forgetN) ψ s else 1) *
      detFrob ρ.forgetN s / detFrob ρ s

omit [BorelSpace K] in
variable (K) in
/-- The value of `galEps` on $\rho$ is the value on $(r, 0)$ times the quotient of the two determinants. -/
theorem galEps_mul_detFrob (art : Kˣ ≃ₜ* WeilGroup.Ab K) (μ : Measure K) (ρ : WeilDeligneRep K m)
    (ψ : AddChar K ℂ) (s : ℂ) :
    galEps K art μ m ρ ψ s * detFrob ρ s = galEps K art μ m ρ.forgetN ψ s * detFrob ρ.forgetN s := by
  simp only [galEps, forgetN_forgetN]
  rw [div_mul_cancel₀ _ (detFrob_ne_zero ρ s), div_mul_cancel₀ _ (detFrob_ne_zero _ s)]

omit [BorelSpace K] in
variable (K) in
/-- In dimension one, `galEps` is `epsTate` of the character $\det r \circ \mathrm{art}_K$. -/
theorem galEps_one (art : Kˣ ≃ₜ* WeilGroup.Ab K) (μ : Measure K) (ρ : WeilDeligneRep K 1)
    (ψ : AddChar K ℂ) : galEps K art μ 1 ρ ψ = epsTate μ (charOfWD K art ρ) ψ := by
  have hρ : ρ.forgetN = ρ := wd_ext K rfl (N_eq_zero K ρ).symm
  funext s
  simp only [galEps, hρ, ↓reduceIte]
  rw [mul_div_assoc, div_self (detFrob_ne_zero ρ s), mul_one]

variable (K) in
/-- **The ε-factor `galEps` has the conditions of `IsWDEpsilon`.** So the existential parameter $\varepsilon$ of `LocalLanglandsGLFull` has a witness. -/
theorem isWDEpsilon_galEps (art : Kˣ ≃ₜ* WeilGroup.Ab K) : IsWDEpsilon K art (galEps K art) where
  iso μ m ρ ρ' h ψ s := by
    have h' : ρ.Iso ρ' := Quotient.exact h
    simp only [galEps]
    rw [detFrob_eq_of_iso h', detFrob_eq_of_iso (forgetN_iso h'),
      charOfWD_eq_of_iso K art (forgetN_iso h')]
  monomial μ m ρ ψ := by
    obtain ⟨c, hc, k, hk⟩ : ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, ∀ s,
        (if m = 1 then epsTate μ (charOfWD K art ρ.forgetN) ψ s else 1) =
          c * ((residueCard K : ℂ) ^ (-s)) ^ k := by
      split_ifs
      · exact epsTate_monomial μ (isSmoothChar_charOfWD K art _) ψ
      · exact ⟨1, one_ne_zero, 0, fun s => by simp⟩
    have ha := det_frobOnLSpace_ne_zero ρ
    have ha₀ := det_frobOnLSpace_ne_zero ρ.forgetN
    refine ⟨c * ((-1) ^ Module.finrank ℂ ρ.forgetN.lSpace * LinearMap.det ρ.forgetN.frobOnLSpace) /
        ((-1) ^ Module.finrank ℂ ρ.lSpace * LinearMap.det ρ.frobOnLSpace),
      div_ne_zero (mul_ne_zero hc (mul_ne_zero (pow_ne_zero _ (by norm_num)) ha₀))
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) ha),
      k + ((Module.finrank ℂ ρ.forgetN.lSpace : ℤ) - Module.finrank ℂ ρ.lSpace), fun s => ?_⟩
    have hX := qpow_ne_zero (K := K) s
    simp only [galEps]
    rw [hk, detFrob_eq, detFrob_eq, zpow_add₀ hX, zpow_sub₀ hX, zpow_natCast, zpow_natCast]
    field_simp
  dimOne μ _ ρ ψ k hψ := by
    rw [galEps_one]
    obtain ⟨k', hk', he⟩ := epsTate_eq μ (charOfWD K art ρ) hψ
    rw [he]
    exact isTateEpsilon_tateEpsilon μ (isSmoothChar_charOfWD K art ρ) hk'
  monodromy μ m ρ ψ s := galEps_mul_detFrob K art μ ρ ψ s

end Epsilon

section Positive

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The family $(\mathrm{rec}_0, \mathrm{rec}_1)$ has the conditions of `IsLanglandsFamily`. This is the proof of `Langlands.LocalGL1.localLanglandsGL_one` for the family `recFamily`. -/
theorem isLanglandsFamily_recFamily' (hart : IsLocalArtinMap K art) :
    IsLanglandsFamily K art 1 (recFamily K art) where
  gl1 _ := rec1_gl1 K art
  map
    | 0, _ => isLanglandsMap_rec0 K art
    | 1, _ =>
      { central := rec1_central K art
        twist := rec1_twist K art
        dual := rec1_dual K art
        lFactor := fun π ρ h => by
          have := π.2.1.1
          rw [eq_wdOfChar_of_rec1 K art h]
          exact isGJLFactor_wdOfChar hart _ _ π.1 (rho_irrChar K π) }
    | _ + 2, h => absurd h (by omega)

variable [MeasurableSpace K] [BorelSpace K]

/-- **The family $(\mathrm{rec}_0, \mathrm{rec}_1)$ has the conditions of `IsLanglandsFamilyPairs`** for the ε-factor `galEps`. The L-factor of pairs is `Langlands.isRSLFactor_tensor_wdOfChar` and the ε-factor of pairs is `Langlands.isRSEpsilonFactor_one`. -/
theorem isLanglandsFamilyPairs_recFamily (hart : IsLocalArtinMap K art) :
    IsLanglandsFamilyPairs K art (galEps K art) 1 (recFamily K art) where
  toIsLanglandsFamily := isLanglandsFamily_recFamily' K art hart
  lFactorPair m hm m' hm' h1 π π' ρ ρ' hρ hρ' ψ _ _ _ _ μ _ _ := by
    obtain rfl : m = 1 := by omega
    obtain rfl : m' = 1 := by omega
    obtain rfl := eq_wdOfChar_of_rec1 K art hρ
    obtain rfl := eq_wdOfChar_of_rec1 K art hρ'
    have := π.2.1.1
    have := π'.2.1.1
    exact isRSLFactor_tensor_wdOfChar μ hart _ _ π.1 π'.1 (rho_irrChar K π) (rho_irrChar K π') ψ
  epsilonPair m hm m' hm' h1 π π' ρ ρ' hρ hρ' ψ k hψ _ _ μ _ _ _ := by
    obtain rfl : m = 1 := by omega
    obtain rfl : m' = 1 := by omega
    obtain rfl := eq_wdOfChar_of_rec1 K art hρ
    obtain rfl := eq_wdOfChar_of_rec1 K art hρ'
    have := π.2.1.1
    have := π'.2.1.1
    have hχ := isSmoothChar_irrChar K π
    have hχ' := isSmoothChar_irrChar K π'
    have he : galEps K art μ (1 * 1) ((wdOfChar K art _ hχ).tensor (wdOfChar K art _ hχ')) ψ =
        galEps K art μ 1 (wdOfChar K art _ (isSmoothChar_mul_pair hχ hχ')) ψ :=
      congrArg (fun ρ : WeilDeligneRep K 1 => galEps K art μ 1 ρ ψ) (tensor_wdOfChar art hχ hχ')
    rw [he, galEps_one, charOfWD_wdOfChar_eq]
    obtain ⟨k', hk', he'⟩ := epsTate_eq μ (irrChar K π * irrChar K π') hψ
    rw [he']
    exact isRSEpsilonFactor_one μ hχ hχ' π.1 π'.1 (rho_irrChar K π) (rho_irrChar K π') hk'

/-- **F2: the local Langlands correspondence for $GL_1$ with the factors of pairs.** The statement `LocalLanglandsGLFull 1` holds, with the ε-factor `galEps` and the family $(\mathrm{rec}_0, \mathrm{rec}_1)$ of `Langlands.LocalGL1.recFamily`. -/
theorem localLanglandsGLFull_one : LocalLanglandsGLFull.{u} 1 := by
  intro K _ _ _ _ art hart
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  exact ⟨galEps K art, isWDEpsilon_galEps K art, recFamily K art,
    isLanglandsFamilyPairs_recFamily K art hart⟩

end Positive

section Negative

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The trivial Weil-Deligne representation $(1, 0)$ of dimension $m$. -/
noncomputable def trivWD (m : ℕ) : WeilDeligneRep K m where
  r := 1
  isOpen_ker := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  N := 0
  isNilpotent := IsNilpotent.zero
  conj w := by simp
  semisimple w := by
    rw [MonoidHom.one_apply, Units.val_one, Matrix.toLin'_one]
    exact Module.End.isSemisimple_id

variable [MeasurableSpace K] [BorelSpace K]

variable {K} in
/-- The ε-factor `galEps` multiplied by $-1$ in dimension two. -/
noncomputable def galEpsSign (art : Kˣ ≃ₜ* WeilGroup.Ab K) : WDEpsilonFn K :=
  fun μ m ρ ψ s => (if m = 2 then -1 else 1) * galEps K art μ m ρ ψ s

/-- **F3: a second ε-factor with the conditions of `IsWDEpsilon`.** The factor `galEpsSign` has the conditions of `IsWDEpsilon`. -/
theorem isWDEpsilon_galEpsSign : IsWDEpsilon K art (galEpsSign art) where
  iso μ m ρ ρ' h ψ s := by
    simp only [galEpsSign]
    rw [(isWDEpsilon_galEps K art).iso μ m ρ ρ' h ψ s]
  monomial μ m ρ ψ := by
    obtain ⟨c, hc, k, hk⟩ := (isWDEpsilon_galEps K art).monomial μ m ρ ψ
    refine ⟨(if m = 2 then -1 else 1) * c, mul_ne_zero (by split_ifs <;> norm_num) hc, k, fun s => ?_⟩
    simp only [galEpsSign]
    rw [hk, mul_assoc]
  dimOne μ _ ρ ψ k hψ := by
    have h : galEpsSign art μ 1 ρ ψ = galEps K art μ 1 ρ ψ := funext fun s => by simp [galEpsSign]
    rw [h]
    exact (isWDEpsilon_galEps K art).dimOne μ ρ ψ k hψ
  monodromy μ m ρ ψ s := by
    simp only [galEpsSign]
    rw [mul_assoc, (isWDEpsilon_galEps K art).monodromy μ m ρ ψ s, mul_assoc]

/-- **F3: the conditions `IsWDEpsilon` do not determine the Galois ε-factor.** The factors `galEps` and `galEpsSign` are different on the trivial representation of dimension two. -/
theorem galEps_ne_galEpsSign : galEps K art ≠ galEpsSign art := by
  intro h
  have h2 := congrFun (congrFun (congrFun (congrFun (congrFun h 0) 2) (trivWD K 2)) 1) 0
  simp only [galEpsSign, ↓reduceIte] at h2
  obtain ⟨c, hc, k, hk⟩ := (isWDEpsilon_galEps K art).monomial 0 2 (trivWD K 2) 1
  have h0 : galEps K art 0 2 (trivWD K 2) 1 0 ≠ 0 := by
    rw [hk]
    exact mul_ne_zero hc (zpow_ne_zero _ (qpow_ne_zero 0))
  refine h0 ?_
  linear_combination h2 / 2

/-- **F3: the ε-factor of a witness of `LocalLanglandsGLFull 1` is not unique.** There are two different ε-factors with the conditions of `IsWDEpsilon`, and the family $(\mathrm{rec}_0, \mathrm{rec}_1)$ has the conditions of `IsLanglandsFamilyPairs` for both. -/
theorem not_unique_epsilon_one (hart : IsLocalArtinMap K art) :
    ∃ ε₁ ε₂ : WDEpsilonFn K, ε₁ ≠ ε₂ ∧ IsWDEpsilon K art ε₁ ∧ IsWDEpsilon K art ε₂ ∧
      IsLanglandsFamilyPairs K art ε₁ 1 (recFamily K art) ∧
        IsLanglandsFamilyPairs K art ε₂ 1 (recFamily K art) := by
  have h := isLanglandsFamilyPairs_recFamily K art hart
  refine ⟨galEps K art, galEpsSign art, galEps_ne_galEpsSign K art, isWDEpsilon_galEps K art,
    isWDEpsilon_galEpsSign K art, h, ⟨h.toIsLanglandsFamily, h.lFactorPair, ?_⟩⟩
  intro m hm m' hm' h1 π π' ρ ρ' hρ hρ' ψ k hψ hg hg' μ _ _ hμ
  have hmm : m * m' ≤ 1 * 1 := Nat.mul_le_mul hm (hm'.trans hm)
  have he : galEpsSign art μ (m * m') (ρ.tensor ρ') ψ = galEps K art μ (m * m') (ρ.tensor ρ') ψ :=
    funext fun s => by simp [galEpsSign, show m * m' ≠ 2 by omega]
  rw [he]
  exact h.epsilonPair m hm m' hm' h1 π π' ρ ρ' hρ hρ' ψ k hψ hg hg' μ hμ

omit [MeasurableSpace K] [BorelSpace K] in
/-- The Weil-Deligne representations of dimension zero are all isomorphic. -/
theorem subsingleton_wdIso_zero : Subsingleton (WDIso K 0) := by
  refine ⟨fun x y => Quotient.inductionOn₂ x y fun ρ ρ' => Quotient.sound ?_⟩
  exact ⟨1, fun w => Units.ext (Subsingleton.elim _ _), Subsingleton.elim _ _⟩

omit [MeasurableSpace K] [BorelSpace K] in
/-- **For $n = 1$ the conditions of `IsLanglandsFamily` determine the family.** Condition 1 fixes $\mathrm{rec}_1$, and $\mathrm{rec}_0$ is a map between two types with one element. So for $n = 1$ the conditions on pairs of `IsLanglandsFamilyPairs` add no information on $\mathrm{rec}$, and a second family as in spec 06.3 needs $n \ge 2$. -/
theorem recFamily_unique {rec rec' : ∀ m ≤ 1, IrrSmooth (GL (Fin m) K) ≃ WDIso K m}
    (h : IsLanglandsFamily K art 1 rec) (h' : IsLanglandsFamily K art 1 rec') : rec = rec' := by
  funext m hm
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · have := subsingleton_wdIso_zero K
    exact Equiv.ext fun _ => Subsingleton.elim _ _
  refine Equiv.ext fun x => Quotient.inductionOn x fun π => ?_
  have hx : (Quotient.mk _ π : IrrSmooth (GL (Fin 1) K)) =
      charClass K (irrChar K π) (isSmoothChar_irrChar K π) :=
    Quotient.sound (iso_irrChar K π)
  rw [hx]
  obtain ⟨ρ, hρ⟩ := Quotient.exists_rep (rec 1 hm (charClass K (irrChar K π) (isSmoothChar_irrChar K π)))
  obtain ⟨ρ', hρ'⟩ := Quotient.exists_rep (rec' 1 hm (charClass K (irrChar K π) (isSmoothChar_irrChar K π)))
  have e := h.gl1 hm _ _ ρ hρ
  have e' := h'.gl1 hm _ _ ρ' hρ'
  have hr : ρ.r = ρ'.r := by
    ext w i j
    obtain ⟨x, hx⟩ : ∃ x : Kˣ, (QuotientGroup.mk w : WeilGroup.Ab K) = art x :=
      ⟨art.symm (QuotientGroup.mk w), (art.apply_symm_apply _).symm⟩
    fin_cases i
    fin_cases j
    exact (e x w hx).trans (e' x w hx).symm
  rw [← hρ, ← hρ', wd_ext K hr ((N_eq_zero K ρ).trans (N_eq_zero K ρ').symm)]

end Negative

section Triviality

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The trivial character of $K^\times$ is smooth. -/
theorem isSmoothChar_one : IsSmoothChar K (1 : Kˣ →* ℂˣ) := by
  change IsOpen (((1 : Kˣ →* ℂˣ).ker : Subgroup Kˣ) : Set Kˣ)
  rw [MonoidHom.ker_one, Subgroup.coe_top]
  exact isOpen_univ

/-- **F4: the type of the irreducible smooth representations of $GL_1(K)$ is not empty.** It has the class of the trivial character. -/
theorem nonempty_irrSmooth_one : Nonempty (IrrSmooth (GL (Fin 1) K)) :=
  ⟨charClass K 1 (isSmoothChar_one K)⟩

/-- **F4: the type of the classes of Weil-Deligne representations is not empty** in each dimension. It has the class of the trivial representation. -/
theorem nonempty_wdIso (m : ℕ) : Nonempty (WDIso K m) :=
  ⟨WDIso.mk (trivWD K m)⟩

end Triviality

end Langlands.Fidelity
