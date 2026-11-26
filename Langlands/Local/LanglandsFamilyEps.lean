/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1LFactor
import Langlands.Local.GL1EpsilonUnramifiedFull

/-!
# The ε-factor conditions of the local Langlands correspondence for $GL_1$

Let $K$ be a nonarchimedean local field with residue field of $q$ elements and uniformizer $\varpi$, and let $\mathrm{art}_K : K^\times \to W_K^{ab}$ be a local Artin map. The statement `Langlands.IsLanglandsFamily` leaves out condition 6, the equality of the ε-factors of pairs, and condition 5 for pairs with $m' \ge 2$. This file adds these conditions for $m = m' = 1$, where all the factors are Tate's local factors of characters.

On the automorphic side, the ε-factor of the representation $\chi \circ \det$ of $GL_1(K)$ is Tate's factor $\varepsilon(s, \chi, \psi)$. The file defines it by the explicit formulas of `Langlands.Local.GL1Epsilon` and `Langlands.Local.GL1EpsilonRamified`, and proves that it is the factor in Tate's local functional equation $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) L(1 - s, \chi^{-1})^{-1} = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s) L(s, \chi)^{-1}$$ for each locally constant function $\varphi$ with compact support. For the pair $(\chi, \chi')$ of characters of $GL_1(K)$, the local factors of $\pi \times \pi'$ are the Tate factors of $\chi \chi'$.

On the Galois side, the project has no ε-factor of Deligne and Langlands for Weil-Deligne representations, because its definition needs the Weil groups of all finite extensions of $K$ and induction. This file defines it only in dimension one: the ε-factor of a Weil-Deligne representation $\rho$ of dimension one is the Tate ε-factor of the character $\det r \circ \mathrm{art}_K$ of $K^\times$. This is the definition of Deligne and Langlands in dimension one. The tensor product of two Weil-Deligne representations of dimension one is $(r r', 0)$.

## Main definitions

* `Langlands.LocalGL1.IsUnramifiedChar`: the character $\chi$ is trivial on $\mathcal{O}_K^\times$.
* `Langlands.LocalGL1.conductorExp`: the conductor exponent $a(\chi)$ of a ramified smooth character.
* `Langlands.LocalGL1.tateEpsilon`: Tate's ε-factor $\varepsilon(s, \chi, \psi)$ for the Haar measure $\mu$ and an additive character $\psi$ of conductor exponent $n$.
* `Langlands.LocalGL1.lFactorInv`: the inverse $L(s, \chi)^{-1}$ of the Tate L-factor.
* `Langlands.LocalGL1.wdEpsilon`: the ε-factor of a Weil-Deligne representation of dimension one, through $\mathrm{art}_K$.
* `Langlands.LocalGL1.wdTensorOne`: the tensor product of two Weil-Deligne representations of dimension one.
* `Langlands.LocalGL1.IsLanglandsFamilyEps`: `IsLanglandsFamily` with the ε-factor condition for $m = 1$ and conditions 5 and 6 for the pairs with $m = m' = 1$.

## Main results

* `Langlands.LocalGL1.exists_isRamifiedConductor`, `Langlands.LocalGL1.IsRamifiedConductor.unique`: each smooth ramified character has exactly one conductor exponent.
* `Langlands.LocalGL1.localFunctionalEquation_tateEpsilon`: Tate's local functional equation with `tateEpsilon`, for each locally constant $\varphi$ with compact support.
* `Langlands.LocalGL1.wdTensorOne_r`, `Langlands.LocalGL1.wdTensorOne_N`: the tensor product is $(r r', 0)$.
* `Langlands.LocalGL1.isLanglandsFamilyEps_of_isLanglandsFamily`, `Langlands.LocalGL1.isLanglandsFamilyEps_iff`: for a local Artin map, `IsLanglandsFamilyEps` is equivalent to `IsLanglandsFamily`.
* `Langlands.LocalGL1.isLanglandsFamilyEps_recFamily`: the family $(\mathrm{rec}_0, \mathrm{rec}_1)$ satisfies `IsLanglandsFamilyEps`.
* `Langlands.LocalGL1.rec_one_eq`, `Langlands.LocalGL1.IsLanglandsFamilyEps.unique_one`: two families agree on $GL_1(K)$, and two families with $n = 1$ are equal.

## Implementation notes

In dimension one, condition 1 says that $\mathrm{rec}_1(\chi)$ is $\chi \circ \mathrm{art}_K^{-1}$. The ε-factor of a Weil-Deligne representation of dimension one is the Tate ε-factor transported by $\mathrm{art}_K$, so condition 1 implies the ε-factor conditions, and Tate's local theory for $\chi \chi'$ gives condition 5 for the pairs with $m = m' = 1$. Thus the new conditions add nothing to `IsLanglandsFamily` for $n \le 1$, and the uniqueness for $n = 1$ follows from condition 1 alone. The file proves this and says it in the statements.

The ε-factor depends on the Haar measure $\mu$ and on the additive character $\psi$. The conditions are stated for each $\mu$, each $\psi$ and each $n \in \mathbb{Z}$. The definition `tateEpsilon` is Tate's factor when $\psi$ has conductor exponent $n$, by `localFunctionalEquation_tateEpsilon`. For other values of $n$ it is only a formula, and the conditions are then equalities of formulas.

## What is still open

* The ε-factors of Deligne and Langlands for Weil-Deligne representations of dimension $m \ge 2$, and the Godement-Jacquet or Rankin-Selberg ε-factors for $GL_m(K)$ with $m \ge 2$. Without them, condition 6 for $m \ge 2$ cannot be stated.
* The L-factors and ε-factors of pairs $\pi \times \pi'$ with $m' \ge 2$. These need the Rankin-Selberg integrals of Jacquet, Piatetski-Shapiro and Shalika and the tensor product of Weil-Deligne representations of dimension $m m'$.
* Henniart's uniqueness theorem for $n \ge 2$, which needs condition 6 for all pairs with $m, m' \le n$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta functions, thesis, 1950.
* P. Deligne, Les constantes des équations fonctionnelles des fonctions L, LNM 349, 1973.
* G. Henniart, Caractérisation de la correspondance de Langlands locale par les facteurs ε de paires, Invent. Math. 113 (1993).
-/

namespace Langlands.LocalGL1

universe u

open MeasureTheory Matrix Topology

section Conductor

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The character $\chi$ of $K^\times$ is unramified: it is trivial on the elements with $|x| = 1$, that is on $\mathcal{O}_K^\times$. -/
def IsUnramifiedChar (χ : Kˣ →* ℂˣ) : Prop :=
  ∀ x : Kˣ, normAbs K x = 1 → χ x = 1

/-- The character $\chi^{-1}$ is unramified exactly when $\chi$ is unramified. -/
theorem isUnramifiedChar_inv_iff (χ : Kˣ →* ℂˣ) : IsUnramifiedChar χ⁻¹ ↔ IsUnramifiedChar χ := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := h x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  · rw [MonoidHom.inv_apply, h x hx, inv_one]

/-- **Existence of the conductor exponent.** A smooth character $\chi$ of $K^\times$ that is not trivial on $\mathcal{O}_K^\times$ has a conductor exponent $a \ge 1$: it is trivial on $1 + \mathfrak{p}^a$ and not trivial on $(1 + \mathfrak{p}^{a - 1}) \cap \mathcal{O}_K^\times$. The kernel of $\chi$ is open, so it contains some $1 + \mathfrak{p}^M$, and $a$ is the least such $M \ge 1$. -/
theorem exists_isRamifiedConductor {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ1 : ¬ IsUnramifiedChar χ) : ∃ a, IsRamifiedConductor χ a := by
  classical
  obtain ⟨W, hW, hWker⟩ := (Units.isEmbedding_val₀ (G₀ := K)).isInducing.isOpen_iff.1 hχ
  have h1 : (1 : K) ∈ W := by
    have : (1 : Kˣ) ∈ (Units.val ⁻¹' W) := by
      rw [hWker]
      exact one_mem _
    simpa using this
  have hn : {z : K | 1 + z ∈ W} ∈ 𝓝 (0 : K) := by
    have hc : Continuous fun z : K => 1 + z := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds h1)
  obtain ⟨N, hN⟩ := exists_ordBall_subset hn
  let P : ℕ → Prop := fun a => 1 ≤ a ∧ ∀ x : Kˣ, (x : K) ∈ oneAddBall (a : ℤ) → χ x = 1
  have hP : ∃ a, P a := by
    refine ⟨max N.toNat 1, le_max_right _ _, fun x hx => ?_⟩
    have hle : N ≤ ((max N.toNat 1 : ℕ) : ℤ) := by omega
    have hx' : (x : K) - 1 ∈ ordBall K N := ordBall_anti hle hx
    have hxW : (x : K) ∈ W := by simpa using hN hx'
    have : x ∈ χ.ker := by
      rw [← SetLike.mem_coe, ← hWker]
      exact hxW
    exact this
  obtain ⟨x, hx, hχx⟩ : ∃ x : Kˣ, normAbs K x = 1 ∧ χ x ≠ 1 := by
    simpa [IsUnramifiedChar] using hχ1
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, ?_⟩
  by_cases ha : Nat.find hP = 1
  · refine ⟨x, (normAbs_eq_one_iff x.ne_zero).1 hx, ?_, hχx⟩
    rw [ha]
    change (x : K) - 1 ∈ ordBall K (((1 : ℕ) : ℤ) - 1)
    have h0 : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
    rw [h0, sub_eq_add_neg]
    have hx0 : (x : K) ∈ ordBall K 0 :=
      mem_ordBall_of_le x.ne_zero (by rw [(normAbs_eq_one_iff x.ne_zero).1 hx])
    have h10 : (1 : K) ∈ ordBall K 0 := mem_ordBall_of_le one_ne_zero (by rw [ord_one])
    exact add_mem_ordBall hx0 (neg_mem_ordBall h10)
  · have h2 : 2 ≤ Nat.find hP := by have := (Nat.find_spec hP).1; omega
    have hnot : ¬ P (Nat.find hP - 1) := Nat.find_min hP (by omega)
    have hb : 1 ≤ Nat.find hP - 1 := by omega
    simp only [P, hb, true_and, not_forall] at hnot
    obtain ⟨y, hy, hχy⟩ := hnot
    have hcast : ((Nat.find hP - 1 : ℕ) : ℤ) = (Nat.find hP : ℤ) - 1 := by omega
    rw [hcast] at hy
    refine ⟨y, (ne_zero_and_ord_eq_zero_of_mem_oneAddBall (by omega) hy).2, hy, hχy⟩

/-- **Uniqueness of the conductor exponent.** A character has at most one conductor exponent. -/
theorem IsRamifiedConductor.unique {χ : Kˣ →* ℂˣ} {a b : ℕ} (ha : IsRamifiedConductor χ a)
    (hb : IsRamifiedConductor χ b) : a = b := by
  have key : ∀ {a b : ℕ}, IsRamifiedConductor χ a → IsRamifiedConductor χ b → ¬ a < b := by
    intro a b ha hb hab
    obtain ⟨u, -, hu, hχu⟩ := hb.nontrivial
    exact hχu (ha.trivial u (ordBall_anti (by omega) hu))
  have h1 := key ha hb
  have h2 := key hb ha
  omega

open Classical in
/-- The conductor exponent $a(\chi) \ge 1$ of a ramified smooth character $\chi$, given by `exists_isRamifiedConductor` and `IsRamifiedConductor.unique`. The value is $0$ when $\chi$ has no conductor exponent in the sense of `IsRamifiedConductor`, for example when $\chi$ is unramified. -/
noncomputable def conductorExp (χ : Kˣ →* ℂˣ) : ℕ :=
  if h : ∃ a, IsRamifiedConductor χ a then Nat.find h else 0

/-- A smooth ramified character has the conductor exponent `conductorExp χ`. -/
theorem isRamifiedConductor_conductorExp {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ1 : ¬ IsUnramifiedChar χ) : IsRamifiedConductor χ (conductorExp χ) := by
  have h := exists_isRamifiedConductor hχ hχ1
  classical
  unfold conductorExp
  split
  · exact Nat.find_spec ‹_›
  · exact absurd h ‹_›

end Conductor

section Epsilon

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

open Classical in
/-- **Tate's ε-factor** $\varepsilon(s, \chi, \psi)$ of a character $\chi$ of $K^\times$, for the Haar measure $\mu$ and an additive character $\psi$ of conductor exponent $n$. For $\chi$ unramified it is `epsilonUnramified`, $\mu(\mathcal{O}_K) q^n \chi(\varpi)^n (q^{-s})^n$. For $\chi$ ramified it is `epsilonRamified` with $a = a(\chi)$, $G(\chi, \psi) (q^{-s})^{a + n}$. The functional equation that characterizes it is `localFunctionalEquation_tateEpsilon`. -/
noncomputable def tateEpsilon (χ : Kˣ →* ℂˣ) (ψ : AddChar K ℂ) (n : ℤ) (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then epsilonUnramified χ μ n s
  else epsilonRamified χ μ ψ (conductorExp χ) n s

omit [MeasurableSpace K] [BorelSpace K] in
open Classical in
/-- The inverse $L(s, \chi)^{-1}$ of Tate's L-factor: $1 - \chi(\varpi) q^{-s}$ for $\chi$ unramified, and $1$ for $\chi$ ramified. -/
noncomputable def lFactorInv (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then 1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) else 1

variable [μ.Regular]

/-- **Tate's local functional equation** with `tateEpsilon`. Let $\chi$ be a smooth character of $K^\times$ and let $\psi$ be an additive character of conductor exponent $n$. For each locally constant function $\varphi$ with compact support and each $s$ in the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) L(1 - s, \chi^{-1})^{-1} = \varepsilon(s, \chi, \psi) Z(\varphi, \chi, s) L(s, \chi)^{-1}.$$ -/
theorem localFunctionalEquation_tateEpsilon {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) {φ : K → ℂ} (hφ : IsLocallyConstant φ)
    (hφs : HasCompactSupport φ) {s : ℂ} (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    (hs' : ‖(χ (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1) :
    zeta χ⁻¹ μ (fourier μ ψ φ) (1 - s) * lFactorInv χ⁻¹ (1 - s) =
      tateEpsilon μ χ ψ n s * (zeta χ μ φ s * lFactorInv χ s) := by
  by_cases hu : IsUnramifiedChar χ
  · have hu' : IsUnramifiedChar χ⁻¹ := (isUnramifiedChar_inv_iff χ).2 hu
    simp only [lFactorInv, tateEpsilon, hu, hu', ↓reduceIte, inv_apply_coe]
    exact localFunctionalEquation_unramified_of_isLocallyConstant χ μ hχ hu hψ hφ hφs hs hs'
  · have hu' : ¬ IsUnramifiedChar χ⁻¹ := fun h => hu ((isUnramifiedChar_inv_iff χ).1 h)
    simp only [lFactorInv, tateEpsilon, hu, hu', ↓reduceIte, mul_one]
    exact localFunctionalEquation_of_isLocallyConstant μ hχ (isRamifiedConductor_conductorExp hχ hu)
      hψ.continuous hψ hφ hφs hs hs'

end Epsilon

section WeilDeligne

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

variable {K} in
/-- The product of two smooth characters is smooth. -/
theorem isSmoothChar_mul {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ') :
    IsSmoothChar K (χ * χ') := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ'.ker) (fun x hx => ?_)
    (by rw [Subgroup.coe_inf]; exact hχ.inter hχ')
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, mul_one]

/-- **The ε-factor of a Weil-Deligne representation of dimension one**, defined through the Artin map: $\varepsilon(s, \rho, \psi) = \varepsilon(s, \det r \circ \mathrm{art}_K, \psi)$, the Tate ε-factor of the character of $K^\times$ that corresponds to $\rho$. The project has no ε-factor of Deligne and Langlands in higher dimension. In dimension one, this is the definition of Deligne and Langlands. -/
noncomputable def wdEpsilon [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (ρ : WeilDeligneRep K 1) (ψ : AddChar K ℂ) (n : ℤ) (s : ℂ) : ℂ :=
  tateEpsilon μ (charOfWD K art ρ) ψ n s

/-- **The tensor product of two Weil-Deligne representations of dimension one.** It is the representation $(\chi \chi' \circ \mathrm{art}_K^{-1}, 0)$ for the characters $\chi = \det r \circ \mathrm{art}_K$ and $\chi' = \det r' \circ \mathrm{art}_K$. By `wdTensorOne_r` and `wdTensorOne_N` it is $(r r', 0)$, which is $(r \otimes r', N \otimes 1 + 1 \otimes N')$ in dimension one. -/
noncomputable def wdTensorOne (ρ ρ' : WeilDeligneRep K 1) : WeilDeligneRep K 1 :=
  wdOfChar K art (charOfWD K art ρ * charOfWD K art ρ')
    (isSmoothChar_mul (isSmoothChar_charOfWD K art ρ) (isSmoothChar_charOfWD K art ρ'))

/-- The tensor product acts on $W_K$ by $r(w) r'(w)$. -/
theorem wdTensorOne_r (ρ ρ' : WeilDeligneRep K 1) (w : WeilGroup K) :
    (wdTensorOne K art ρ ρ').r w = ρ.r w * ρ'.r w := by
  have hw : (QuotientGroup.mk w : WeilGroup.Ab K) = art (art.symm (QuotientGroup.mk w)) :=
    (art.apply_symm_apply _).symm
  rw [wdTensorOne, wdOfChar_r, weilChar_apply, MonoidHom.mul_apply, charOfWD_apply K art ρ hw,
    charOfWD_apply K art ρ' hw, map_mul, ← r_eq_unitGL_det, ← r_eq_unitGL_det]

/-- The tensor product has monodromy operator $0$. -/
theorem wdTensorOne_N (ρ ρ' : WeilDeligneRep K 1) : (wdTensorOne K art ρ ρ').N = 0 :=
  rfl

variable {K art} in
/-- The representation $(\chi \circ \mathrm{art}_K^{-1}, 0)$ depends only on $\chi$. -/
theorem wdOfChar_congr {χ χ' : Kˣ →* ℂˣ} (h : χ = χ') (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ') : wdOfChar K art χ hχ = wdOfChar K art χ' hχ' := by
  subst h
  rfl

/-- The character of $K^\times$ that corresponds to $(\chi \circ \mathrm{art}_K^{-1}, 0)$ is $\chi$. -/
theorem charOfWD_wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    charOfWD K art (wdOfChar K art χ hχ) = χ := by
  ext x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
  rw [charOfWD_apply K art _ hw]
  simp [WeilDeligneRep.det, wdOfChar_r, det_unitGL, weilChar_apply, hw]

/-- The character of $K^\times$ that corresponds to the tensor product is the product $\chi \chi'$. -/
theorem charOfWD_wdTensorOne (ρ ρ' : WeilDeligneRep K 1) :
    charOfWD K art (wdTensorOne K art ρ ρ') = charOfWD K art ρ * charOfWD K art ρ' :=
  charOfWD_wdOfChar K art _ _

/-- If a Weil-Deligne representation $\rho$ of dimension one has $r(w) = \chi(x)$ whenever $w$ maps to $\mathrm{art}_K(x)$, then its character $\det r \circ \mathrm{art}_K$ is $\chi$. -/
theorem charOfWD_eq_of_forall {ρ : WeilDeligneRep K 1} {χ : Kˣ →* ℂˣ}
    (h : ∀ (x : Kˣ) (w : WeilGroup K), (QuotientGroup.mk w : WeilGroup.Ab K) = art x →
      (ρ.r w : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = χ x) :
    charOfWD K art ρ = χ := by
  ext x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
  rw [charOfWD_apply K art ρ hw, ← h x w hw]
  simp [WeilDeligneRep.det]

end WeilDeligne

section Family

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- **The conditions on a family $(\mathrm{rec}_m)_{m \le n}$ with the ε-factors for $m = m' = 1$.** These are the conditions of `IsLanglandsFamily` and three more conditions on $GL_1(K)$, for each Haar measure $\mu$ of $K$, each additive character $\psi$ and each $k \in \mathbb{Z}$:

* the ε-factor condition for $m = 1$: if $\rho$ represents $\mathrm{rec}_1(\chi)$, then $\varepsilon(s, \chi, \psi) = \varepsilon(s, \rho, \psi)$;
* condition 6 for $m = m' = 1$: if $\rho, \rho'$ represent $\mathrm{rec}_1(\chi), \mathrm{rec}_1(\chi')$, then $\varepsilon(s, \chi \chi', \psi) = \varepsilon(s, \rho \otimes \rho', \psi)$, since the representation $\pi \times \pi'$ of $GL_1(K) \times GL_1(K)$ has the local factors of $\chi \chi'$;
* condition 5 for $m = m' = 1$: the Godement-Jacquet L-factor of $\chi \chi' \circ \det$ is $L(s, \rho \otimes \rho')$.

The ε-factor on the Galois side is `wdEpsilon`, which is defined through the Artin map, so for a local Artin map these conditions follow from condition 1 (`isLanglandsFamilyEps_iff`). Condition 6 and condition 5 for pairs with $m \ge 2$ or $m' \ge 2$ are not here, so for $n \ge 2$ these conditions do not determine the family. -/
structure IsLanglandsFamilyEps (n : ℕ) (rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m) : Prop
    extends IsLanglandsFamily K art n rec where
  /-- The ε-factor of $\chi$ is the ε-factor of $\mathrm{rec}_1(\chi)$. -/
  epsilon : ∀ (h : 1 ≤ n) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (ρ : WeilDeligneRep K 1),
    WDIso.mk ρ = rec 1 h (charClass K χ hχ) →
      ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
        (ψ : AddChar K ℂ) (k : ℤ) (s : ℂ), tateEpsilon μ χ ψ k s = wdEpsilon K art μ ρ ψ k s
  /-- Condition 6 for $m = m' = 1$: the ε-factor of $\chi \chi'$ is the ε-factor of $\mathrm{rec}_1(\chi) \otimes \mathrm{rec}_1(\chi')$. -/
  epsilonPair : ∀ (h : 1 ≤ n) (χ χ' : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ')
    (ρ ρ' : WeilDeligneRep K 1), WDIso.mk ρ = rec 1 h (charClass K χ hχ) →
      WDIso.mk ρ' = rec 1 h (charClass K χ' hχ') →
        ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
          (ψ : AddChar K ℂ) (k : ℤ) (s : ℂ),
            tateEpsilon μ (χ * χ') ψ k s = wdEpsilon K art μ (wdTensorOne K art ρ ρ') ψ k s
  /-- Condition 5 for $m = m' = 1$: the L-factor of $\chi \chi' \circ \det$ is the L-factor of $\mathrm{rec}_1(\chi) \otimes \mathrm{rec}_1(\chi')$. -/
  lFactorPair : ∀ (h : 1 ≤ n) (χ χ' : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ')
    (ρ ρ' : WeilDeligneRep K 1), WDIso.mk ρ = rec 1 h (charClass K χ hχ) →
      WDIso.mk ρ' = rec 1 h (charClass K χ' hχ') →
        IsGJLFactor K (SmoothRep.charRep (detChar K 1 (χ * χ'))
          (isOpen_ker_detChar K 1 _ (isSmoothChar_mul hχ hχ'))) (wdTensorOne K art ρ ρ').lFactor

variable {K art}

/-- For a local Artin map, each family with the conditions of `IsLanglandsFamily` has the ε-factor conditions of `IsLanglandsFamilyEps`. The ε-factor conditions follow from condition 1 and the definition of `wdEpsilon`, and condition 5 for pairs follows from condition 1 and Tate's local theory for $\chi \chi'$. -/
theorem isLanglandsFamilyEps_of_isLanglandsFamily (hart : IsLocalArtinMap K art) {n : ℕ}
    {rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m} (hrec : IsLanglandsFamily K art n rec) :
    IsLanglandsFamilyEps K art n rec where
  toIsLanglandsFamily := hrec
  epsilon h χ hχ ρ hρ _ _ μ _ ψ k s := by
    rw [wdEpsilon, charOfWD_eq_of_forall K art (hrec.gl1 h χ hχ ρ hρ)]
  epsilonPair h χ χ' hχ hχ' ρ ρ' hρ hρ' _ _ μ _ ψ k s := by
    rw [wdEpsilon, charOfWD_wdTensorOne, charOfWD_eq_of_forall K art (hrec.gl1 h χ hχ ρ hρ),
      charOfWD_eq_of_forall K art (hrec.gl1 h χ' hχ' ρ' hρ')]
  lFactorPair h χ χ' hχ hχ' ρ ρ' hρ hρ' := by
    have e : charOfWD K art ρ * charOfWD K art ρ' = χ * χ' := by
      rw [charOfWD_eq_of_forall K art (hrec.gl1 h χ hχ ρ hρ),
        charOfWD_eq_of_forall K art (hrec.gl1 h χ' hχ' ρ' hρ')]
    have := (SmoothRep.charRep_isIrreducible _
      (isOpen_ker_detChar K 1 _ (isSmoothChar_mul hχ hχ'))).1.1
    rw [wdTensorOne, wdOfChar_congr e _ (isSmoothChar_mul hχ hχ')]
    exact isGJLFactor_wdOfChar hart _ _ _ fun _ _ => rfl

/-- For a local Artin map, `IsLanglandsFamilyEps` is equivalent to `IsLanglandsFamily`. So the ε-factor conditions for $m = m' = 1$ add nothing to conditions 1 to 5. -/
theorem isLanglandsFamilyEps_iff (hart : IsLocalArtinMap K art) {n : ℕ}
    {rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m} :
    IsLanglandsFamilyEps K art n rec ↔ IsLanglandsFamily K art n rec :=
  ⟨fun h => h.toIsLanglandsFamily, isLanglandsFamilyEps_of_isLanglandsFamily hart⟩

variable (K art) in
/-- The family $(\mathrm{rec}_0, \mathrm{rec}_1)$ satisfies `IsLanglandsFamily` for each local Artin map, with no hypothesis. -/
theorem isLanglandsFamily_recFamily_of_isLocalArtinMap (hart : IsLocalArtinMap K art) :
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

variable (K art) in
/-- **The $GL_1$ family with the ε-factors.** For each local Artin map, the family $(\mathrm{rec}_0, \mathrm{rec}_1)$ satisfies `IsLanglandsFamilyEps`: conditions 1 to 5, the ε-factor condition for $m = 1$, and conditions 5 and 6 for the pairs with $m = m' = 1$. -/
theorem isLanglandsFamilyEps_recFamily (hart : IsLocalArtinMap K art) :
    IsLanglandsFamilyEps K art 1 (recFamily K art) :=
  isLanglandsFamilyEps_of_isLanglandsFamily hart
    (isLanglandsFamily_recFamily_of_isLocalArtinMap K art hart)

/-- **Uniqueness on $GL_1(K)$.** Two families with the conditions of `IsLanglandsFamily` have the same bijection $\mathrm{rec}_1$. This follows from condition 1 alone: a Weil-Deligne representation of dimension one is determined by its character. -/
theorem rec_one_eq {n : ℕ} (h1 : 1 ≤ n) {rec rec' : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m}
    (hrec : IsLanglandsFamily K art n rec) (hrec' : IsLanglandsFamily K art n rec') :
    rec 1 h1 = rec' 1 h1 := by
  ext x
  obtain ⟨⟨χ, hχ⟩, rfl⟩ := (irrEquiv K).symm.surjective x
  change rec 1 h1 (charClass K χ hχ) = rec' 1 h1 (charClass K χ hχ)
  obtain ⟨ρ, hρ⟩ := Quotient.exists_rep (rec 1 h1 (charClass K χ hχ))
  obtain ⟨ρ', hρ'⟩ := Quotient.exists_rep (rec' 1 h1 (charClass K χ hχ))
  have e := charOfWD_eq_of_forall K art (hrec.gl1 h1 χ hχ ρ hρ)
  have e' := charOfWD_eq_of_forall K art (hrec'.gl1 h1 χ hχ ρ' hρ')
  have hr : ρ.r = ρ'.r := by
    ext1 w
    have hw : (QuotientGroup.mk w : WeilGroup.Ab K) = art (art.symm (QuotientGroup.mk w)) :=
      (art.apply_symm_apply _).symm
    rw [r_eq_unitGL_det, r_eq_unitGL_det, ← charOfWD_apply K art ρ hw,
      ← charOfWD_apply K art ρ' hw, e, e']
  rw [← hρ, ← hρ', wd_ext K hr (by rw [N_eq_zero, N_eq_zero])]

/-- **Uniqueness for $n = 1$.** Two families $(\mathrm{rec}_0, \mathrm{rec}_1)$ with the conditions of `IsLanglandsFamilyEps` are equal. For $m = 0$ both sides have one element, and for $m = 1$ this is `rec_one_eq`, which uses only condition 1. -/
theorem IsLanglandsFamilyEps.unique_one {rec rec' : ∀ m ≤ 1, IrrSmooth (GL (Fin m) K) ≃ WDIso K m}
    (hrec : IsLanglandsFamilyEps K art 1 rec) (hrec' : IsLanglandsFamilyEps K art 1 rec') :
    ∀ m (h : m ≤ 1), rec m h = rec' m h
  | 0, _ => Equiv.ext fun _ => Subsingleton.elim _ _
  | 1, h => rec_one_eq h hrec.toIsLanglandsFamily hrec'.toIsLanglandsFamily
  | _ + 2, h => absurd h (by omega)

end Family

end Langlands.LocalGL1
