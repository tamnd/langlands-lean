/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Hilbert-Samuel multiplicity of a noetherian local ring

Let $(R, \mathfrak{m})$ be a noetherian local ring of Krull dimension $d$. The Hilbert-Samuel function of $R$ is $n \mapsto \ell_R(R/\mathfrak{m}^n)$. This file shows that each $R/\mathfrak{m}^n$ has finite length. The Hilbert-Samuel multiplicity $e(R)$ is the natural number $e$ such that $$\frac{d!\, \ell_R(R/\mathfrak{m}^n)}{n^d} \to e, \qquad n \to \infty.$$ The multiplicity is a notion that the statement of the Breuil-Mezard conjecture uses (`Langlands/Statements/BreuilMezard.lean`).

## Main definitions

* `Langlands.hilbertSamuelFunction`: the function $n \mapsto \ell_R(R/\mathfrak{m}^n)$, with values in $\mathbb{N}$.
* `Langlands.localKrullDim`: the Krull dimension $d$ of $R$ as a natural number, the height of $\mathfrak{m}$.
* `Langlands.hilbertSamuelRatio`: the sequence $d!\, \ell_R(R/\mathfrak{m}^n) / n^d$ of real numbers.
* `Langlands.HasHilbertSamuelMultiplicity`: the sequence tends to the natural number $e$.
* `Langlands.hilbertSamuelMultiplicity`: the multiplicity $e(R)$, that is the limit when it is a natural number, and $0$ otherwise.
* `Langlands.moduleHilbertSamuelFunction`, `Langlands.moduleKrullDim`, `Langlands.moduleHilbertSamuelMultiplicity`: the same notions for an $R$-module $M$, with $\ell_R(M/\mathfrak{m}^n M)$ and the dimension of the support of $M$.

## Main results

* `Langlands.localKrullDim_eq_ringKrullDim`: the natural number $d$ is the Krull dimension of $R$.
* `Langlands.isFiniteLength_quotient_maximalIdeal_pow`, `Langlands.coe_hilbertSamuelFunction`: the module $R/\mathfrak{m}^n$ has finite length, so the function with values in $\mathbb{N}$ is the length.
* `Langlands.HasHilbertSamuelMultiplicity.hilbertSamuelMultiplicity_eq`: if the sequence tends to $e$, then $e(R) = e$.
* `Langlands.hilbertSamuelMultiplicity_of_isArtinianRing`, `Langlands.coe_hilbertSamuelMultiplicity_of_isArtinianRing`: $e(R) = \ell_R(R)$ for an artinian local ring $R$.
* `Langlands.hilbertSamuelMultiplicity_field`: $e(k) = 1$ for a field $k$.
* `Langlands.hilbertSamuelMultiplicity_of_isDiscreteValuationRing`: $e(R) = 1$ for a discrete valuation ring $R$.
* `Langlands.hilbertSamuelMultiplicity_powerSeries`: $e(k[[x]]) = 1$ for a field $k$.
* `Langlands.isFiniteLength_quotient_maximalIdeal_pow_smul_top`: $M/\mathfrak{m}^n M$ has finite length for a finitely generated module $M$.
* `Langlands.moduleHilbertSamuelMultiplicity_self`: the multiplicity of the module $R$ is $e(R)$.

## The existence of the limit

The limit exists for each noetherian local ring, and it is a positive integer. The proof uses the Hilbert-Samuel polynomial: $\ell_R(R/\mathfrak{m}^n)$ is a polynomial in $n$ of degree $d$ for large $n$, and $e(R)$ is $d!$ times its leading coefficient. This needs the theorem of Hilbert and Serre for the graded ring $\bigoplus_n \mathfrak{m}^n/\mathfrak{m}^{n+1}$ and the dimension theorem, which says that the degree is $d$. Mathlib does not have these results, and this file does not prove them. Thus this file does not prove that the limit exists in general. For this reason `Langlands.hilbertSamuelMultiplicity` is $0$ when there is no limit in $\mathbb{N}$. The file proves the existence of the limit for the artinian local rings and for the discrete valuation rings.

## Proof

For $n \neq 0$ the maximal ideal is the only prime ideal that contains $\mathfrak{m}^n$, so $R/\mathfrak{m}^n$ is an artinian ring (`IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`). It is noetherian and artinian as an $R$-module, so its length is finite. If $R$ is artinian, then $d = 0$ and $\mathfrak{m}^n = 0$ for large $n$, so the sequence is eventually $\ell_R(R)$. If $R$ is a discrete valuation ring, then $d = 1$ and $\ell_R(R/\mathfrak{m}^n) = n$ (`IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`), so the sequence is $1$ for $n \ge 1$.

## References

* H. Matsumura, Commutative ring theory, section 14.
* M. F. Atiyah and I. G. Macdonald, Introduction to commutative algebra, chapter 11.
-/

namespace Langlands

open IsLocalRing Filter Topology

section Ring

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The Hilbert-Samuel function $n \mapsto \ell_R(R/\mathfrak{m}^n)$ of a local ring. The value is the length as a natural number. It is the length for a noetherian local ring (`Langlands.coe_hilbertSamuelFunction`). -/
noncomputable def hilbertSamuelFunction (n : ℕ) : ℕ :=
  (Module.length R (R ⧸ maximalIdeal R ^ n)).toNat

/-- The Krull dimension of a local ring as a natural number: the height of the maximal ideal. For a noetherian local ring it is the Krull dimension (`Langlands.localKrullDim_eq_ringKrullDim`). -/
noncomputable def localKrullDim : ℕ :=
  (maximalIdeal R).height.toNat

/-- The sequence $d!\, \ell_R(R/\mathfrak{m}^n) / n^d$, where $d$ is the Krull dimension of $R$. -/
noncomputable def hilbertSamuelRatio (n : ℕ) : ℝ :=
  (hilbertSamuelFunction R n : ℝ) * (localKrullDim R).factorial / (n : ℝ) ^ localKrullDim R

/-- The sequence $d!\, \ell_R(R/\mathfrak{m}^n) / n^d$ tends to the natural number $e$. -/
def HasHilbertSamuelMultiplicity (e : ℕ) : Prop :=
  Tendsto (hilbertSamuelRatio R) atTop (𝓝 (e : ℝ))

open Classical in
/-- The Hilbert-Samuel multiplicity $e(R)$ of a local ring: the limit of $d!\, \ell_R(R/\mathfrak{m}^n) / n^d$ when this limit is a natural number, and $0$ otherwise. The limit is a natural number for each noetherian local ring, but this file does not prove it in general. -/
noncomputable def hilbertSamuelMultiplicity : ℕ :=
  if h : ∃ e, HasHilbertSamuelMultiplicity R e then h.choose else 0

variable {R} in
/-- The limit is unique. -/
theorem HasHilbertSamuelMultiplicity.unique {e e' : ℕ} (h : HasHilbertSamuelMultiplicity R e)
    (h' : HasHilbertSamuelMultiplicity R e') : e = e' := by
  exact_mod_cast tendsto_nhds_unique h h'

variable {R} in
/-- If the sequence tends to $e$, then $e(R) = e$. -/
theorem HasHilbertSamuelMultiplicity.hilbertSamuelMultiplicity_eq {e : ℕ}
    (h : HasHilbertSamuelMultiplicity R e) : hilbertSamuelMultiplicity R = e := by
  have hex : ∃ e, HasHilbertSamuelMultiplicity R e := ⟨e, h⟩
  rw [hilbertSamuelMultiplicity, dite_eq_left hex]
  exact hex.choose_spec.unique h

/-- If the sequence does not tend to a natural number, then $e(R) = 0$ by definition. -/
theorem hilbertSamuelMultiplicity_of_not_exists (h : ¬ ∃ e, HasHilbertSamuelMultiplicity R e) :
    hilbertSamuelMultiplicity R = 0 := by
  rw [hilbertSamuelMultiplicity, dite_eq_right h]

variable [IsNoetherianRing R]

/-- For a noetherian local ring, `Langlands.localKrullDim` is the Krull dimension. -/
theorem localKrullDim_eq_ringKrullDim : (localKrullDim R : WithBot ℕ∞) = ringKrullDim R := by
  rw [← maximalIdeal_height_eq_ringKrullDim, localKrullDim]
  exact_mod_cast ENat.natCast_toNat Ideal.height_ne_top_of_isPrime

/-- For $n \neq 0$ the ring $R/\mathfrak{m}^n$ is artinian. -/
theorem isArtinianRing_quotient_maximalIdeal_pow {n : ℕ} (hn : n ≠ 0) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ n) :=
  quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
    ⟨⟨inferInstance, Ideal.pow_le_self hn⟩, fun _ ⟨hp, hle⟩ _ => hp.le_of_pow_le hle⟩

/-- The $R$-module $R/\mathfrak{m}^n$ has finite length. -/
theorem isFiniteLength_quotient_maximalIdeal_pow (n : ℕ) :
    IsFiniteLength R (R ⧸ maximalIdeal R ^ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have := isArtinianRing_quotient_maximalIdeal_pow R hn
  have : IsArtinian R (R ⧸ maximalIdeal R ^ n) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := maximalIdeal R ^ n))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, this⟩

/-- The length of $R/\mathfrak{m}^n$ is finite. -/
theorem length_quotient_maximalIdeal_pow_ne_top (n : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ n) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_quotient_maximalIdeal_pow R n)

/-- The Hilbert-Samuel function is the length of $R/\mathfrak{m}^n$. -/
theorem coe_hilbertSamuelFunction (n : ℕ) :
    (hilbertSamuelFunction R n : ℕ∞) = Module.length R (R ⧸ maximalIdeal R ^ n) :=
  ENat.natCast_toNat (length_quotient_maximalIdeal_pow_ne_top R n)

end Ring

section Artinian

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsArtinianRing R]

/-- An artinian local ring has dimension $0$. -/
theorem localKrullDim_eq_zero_of_isArtinianRing : localKrullDim R = 0 := by
  have : Ring.KrullDimLE 0 R := isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  have h := localKrullDim_eq_ringKrullDim R
  rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp this] at h
  exact_mod_cast h

omit [IsLocalRing R] in
/-- An artinian ring has finite length as a module over itself. -/
theorem length_ne_top_of_isArtinianRing : Module.length R R ≠ ⊤ :=
  Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- For an artinian local ring, $\ell_R(R/\mathfrak{m}^n) = \ell_R(R)$ for large $n$. -/
theorem hilbertSamuelFunction_eventually_eq_length :
    ∀ᶠ n in atTop, hilbertSamuelFunction R n = (Module.length R R).toNat := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : maximalIdeal R ^ n = ⊥ := le_bot_iff.mp ((Ideal.pow_le_pow_right hn).trans_eq hN)
  rw [hilbertSamuelFunction, (Submodule.quotEquivOfEqBot _ h).length_eq]

/-- For an artinian local ring the sequence tends to $\ell_R(R)$. -/
theorem hasHilbertSamuelMultiplicity_of_isArtinianRing :
    HasHilbertSamuelMultiplicity R (Module.length R R).toNat := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hilbertSamuelFunction_eventually_eq_length R] with n hn
  simp [hilbertSamuelRatio, hn, localKrullDim_eq_zero_of_isArtinianRing]

/-- For an artinian local ring, $e(R) = \ell_R(R)$, with the length as a natural number. -/
theorem hilbertSamuelMultiplicity_of_isArtinianRing :
    hilbertSamuelMultiplicity R = (Module.length R R).toNat :=
  (hasHilbertSamuelMultiplicity_of_isArtinianRing R).hilbertSamuelMultiplicity_eq

/-- For an artinian local ring, $e(R) = \ell_R(R)$. -/
theorem coe_hilbertSamuelMultiplicity_of_isArtinianRing :
    (hilbertSamuelMultiplicity R : ℕ∞) = Module.length R R := by
  rw [hilbertSamuelMultiplicity_of_isArtinianRing,
    ENat.natCast_toNat (length_ne_top_of_isArtinianRing R)]

end Artinian

/-- For a field $k$, $e(k) = 1$. -/
theorem hilbertSamuelMultiplicity_field (k : Type*) [Field k] :
    hilbertSamuelMultiplicity k = 1 := by
  rw [hilbertSamuelMultiplicity_of_isArtinianRing, Module.length_eq_one]
  rfl

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A discrete valuation ring has dimension $1$. -/
theorem localKrullDim_eq_one_of_isDiscreteValuationRing : localKrullDim R = 1 := by
  have h := localKrullDim_eq_ringKrullDim R
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h

/-- For a discrete valuation ring, $\ell_R(R/\mathfrak{m}^n) = n$. -/
theorem hilbertSamuelFunction_of_isDiscreteValuationRing (n : ℕ) :
    hilbertSamuelFunction R n = n := by
  rw [hilbertSamuelFunction, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  rfl

/-- For a discrete valuation ring the sequence tends to $1$. -/
theorem hasHilbertSamuelMultiplicity_of_isDiscreteValuationRing :
    HasHilbertSamuelMultiplicity R 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  simp [hilbertSamuelRatio, hilbertSamuelFunction_of_isDiscreteValuationRing,
    localKrullDim_eq_one_of_isDiscreteValuationRing, this]

/-- For a discrete valuation ring, $e(R) = 1$. -/
theorem hilbertSamuelMultiplicity_of_isDiscreteValuationRing :
    hilbertSamuelMultiplicity R = 1 :=
  (hasHilbertSamuelMultiplicity_of_isDiscreteValuationRing R).hilbertSamuelMultiplicity_eq

end DVR

/-- For a field $k$, $e(k[[x]]) = 1$. -/
theorem hilbertSamuelMultiplicity_powerSeries (k : Type*) [Field k] :
    hilbertSamuelMultiplicity (PowerSeries k) = 1 :=
  hilbertSamuelMultiplicity_of_isDiscreteValuationRing _

section Module

variable (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The Hilbert-Samuel function $n \mapsto \ell_R(M/\mathfrak{m}^n M)$ of a module $M$ over a local ring. The value is the length as a natural number. It is the length for a finitely generated module over a noetherian local ring (`Langlands.coe_moduleHilbertSamuelFunction`). -/
noncomputable def moduleHilbertSamuelFunction (n : ℕ) : ℕ :=
  (Module.length R (M ⧸ (maximalIdeal R ^ n • ⊤ : Submodule R M))).toNat

/-- The dimension of a module $M$ as a natural number: the Krull dimension of the support of $M$. It is $0$ for $M = 0$. For $M \neq 0$ over a noetherian local ring it is the dimension of the support (`Langlands.moduleKrullDim_eq_supportDim`). -/
noncomputable def moduleKrullDim : ℕ :=
  ((Module.supportDim R M).unbotD 0).toNat

/-- The sequence $d!\, \ell_R(M/\mathfrak{m}^n M) / n^d$, where $d$ is the dimension of $M$. -/
noncomputable def moduleHilbertSamuelRatio (n : ℕ) : ℝ :=
  (moduleHilbertSamuelFunction R M n : ℝ) * (moduleKrullDim R M).factorial /
    (n : ℝ) ^ moduleKrullDim R M

/-- The sequence $d!\, \ell_R(M/\mathfrak{m}^n M) / n^d$ tends to the natural number $e$. -/
def HasModuleHilbertSamuelMultiplicity (e : ℕ) : Prop :=
  Tendsto (moduleHilbertSamuelRatio R M) atTop (𝓝 (e : ℝ))

open Classical in
/-- The Hilbert-Samuel multiplicity $e(M)$ of a module $M$ over a local ring: the limit of $d!\, \ell_R(M/\mathfrak{m}^n M) / n^d$ when this limit is a natural number, and $0$ otherwise. This file does not prove that the limit exists. -/
noncomputable def moduleHilbertSamuelMultiplicity : ℕ :=
  if h : ∃ e, HasModuleHilbertSamuelMultiplicity R M e then h.choose else 0

variable {R M} in
/-- If the sequence tends to $e$, then $e(M) = e$. -/
theorem HasModuleHilbertSamuelMultiplicity.moduleHilbertSamuelMultiplicity_eq {e : ℕ}
    (h : HasModuleHilbertSamuelMultiplicity R M e) : moduleHilbertSamuelMultiplicity R M = e := by
  have hex : ∃ e, HasModuleHilbertSamuelMultiplicity R M e := ⟨e, h⟩
  rw [moduleHilbertSamuelMultiplicity, dite_eq_left hex]
  exact_mod_cast tendsto_nhds_unique hex.choose_spec h

variable [IsNoetherianRing R]

/-- For a nonzero module over a noetherian local ring, `Langlands.moduleKrullDim` is the dimension of the support. The support has finite dimension because its dimension is at most the dimension of $R$. -/
theorem moduleKrullDim_eq_supportDim [Nontrivial M] :
    (moduleKrullDim R M : WithBot ℕ∞) = Module.supportDim R M := by
  have hbot := Module.supportDim_ne_bot_of_nontrivial R M
  have htop : Module.supportDim R M < ⊤ :=
    (Module.supportDim_le_ringKrullDim R M).trans_lt ringKrullDim_lt_top
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [moduleKrullDim, ← hd, WithBot.unbotD_coe]
  have : d ≠ ⊤ := by
    rintro rfl
    exact htop.ne (by rw [← hd]; rfl)
  exact_mod_cast ENat.natCast_toNat this

/-- For a finitely generated module $M$ over a noetherian local ring, $M/\mathfrak{m}^n M$ has finite length. -/
theorem isFiniteLength_quotient_maximalIdeal_pow_smul_top [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R (M ⧸ (maximalIdeal R ^ n • ⊤ : Submodule R M)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have := isArtinianRing_quotient_maximalIdeal_pow R hn
  have : Module.Finite (R ⧸ maximalIdeal R ^ n)
      (M ⧸ (maximalIdeal R ^ n • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinian R (M ⧸ (maximalIdeal R ^ n • ⊤ : Submodule R M)) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := maximalIdeal R ^ n))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, this⟩

/-- The Hilbert-Samuel function of a finitely generated module is the length of $M/\mathfrak{m}^n M$. -/
theorem coe_moduleHilbertSamuelFunction [Module.Finite R M] (n : ℕ) :
    (moduleHilbertSamuelFunction R M n : ℕ∞) =
      Module.length R (M ⧸ (maximalIdeal R ^ n • ⊤ : Submodule R M)) :=
  ENat.natCast_toNat (Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_maximalIdeal_pow_smul_top R M n))

omit [IsNoetherianRing R] in
/-- The Hilbert-Samuel function of the module $R$ is the Hilbert-Samuel function of $R$. -/
theorem moduleHilbertSamuelFunction_self (n : ℕ) :
    moduleHilbertSamuelFunction R R n = hilbertSamuelFunction R n := by
  have h : (maximalIdeal R ^ n • ⊤ : Submodule R R) = maximalIdeal R ^ n := by
    rw [Ideal.smul_top_eq_map]
    simp
  rw [moduleHilbertSamuelFunction, h, hilbertSamuelFunction]

/-- The dimension of the module $R$ is the dimension of $R$. -/
theorem moduleKrullDim_self : moduleKrullDim R R = localKrullDim R := by
  have h := moduleKrullDim_eq_supportDim R R
  rw [Module.supportDim_self_eq_ringKrullDim, ← localKrullDim_eq_ringKrullDim] at h
  exact_mod_cast h

/-- The multiplicity of the module $R$ is $e(R)$. -/
theorem moduleHilbertSamuelMultiplicity_self :
    moduleHilbertSamuelMultiplicity R R = hilbertSamuelMultiplicity R := by
  have h : moduleHilbertSamuelRatio R R = hilbertSamuelRatio R := by
    ext n
    rw [moduleHilbertSamuelRatio, hilbertSamuelRatio, moduleHilbertSamuelFunction_self,
      moduleKrullDim_self]
  by_cases hex : ∃ e, HasHilbertSamuelMultiplicity R e
  · obtain ⟨e, he⟩ := hex
    rw [he.hilbertSamuelMultiplicity_eq]
    exact HasModuleHilbertSamuelMultiplicity.moduleHilbertSamuelMultiplicity_eq
      (by rw [HasModuleHilbertSamuelMultiplicity, h]; exact he)
  · rw [hilbertSamuelMultiplicity_of_not_exists R hex, moduleHilbertSamuelMultiplicity,
      dite_eq_right]
    rintro ⟨e, he⟩
    exact hex ⟨e, by rw [HasHilbertSamuelMultiplicity, ← h]; exact he⟩

end Module

end Langlands
