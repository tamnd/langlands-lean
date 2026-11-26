/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1
import Langlands.WeilGroup.Degree
import Langlands.WeilGroup.Ab
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Langlands.Reciprocity.Exists
import Mathlib.NumberTheory.Padics.LocalField


/-!
# Tate's local theory for $GL_1$

Let $K$ be a nonarchimedean local field with residue field of $q$ elements, uniformizer $\varpi$ and normalized absolute value $|x| = q^{-\mathrm{ord}(x)}$. Let $\chi : K^\times \to \mathbb{C}^\times$ be a smooth character and $\mu$ a Haar measure on $K$. For a locally constant function $\varphi$ with compact support, this file computes the local zeta integral $$Z(\varphi, \chi, s) = \int_K \varphi(y) \chi(y) |y|^{s - 1} \, d\mu(y).$$ It shows that $Z(\varphi, \chi, s)$ is a Laurent polynomial in $q^{-s}$ plus $\varphi(0)$ times a multiple of $(1 - \chi(\varpi) q^{-s})^{-1}$ when $\chi$ is unramified, and a Laurent polynomial in $q^{-s}$ when $\chi$ is ramified. With this, it proves that the $L$-factor of the Weil-Deligne representation of $\chi \circ \mathrm{art}^{-1}$ is the Godement-Jacquet $L$-factor of the representation $\chi \circ \det$ of $GL_1(K)$, and it gives the local Langlands correspondence for $GL_1$.

The statement `Langlands.LocalGL1.GL1LFactor` asks this for each representation $\pi$ of $GL_1(K)$ by $\chi \circ \det$, also for $\pi = 0$. For $\pi = 0$ each zeta integral is $0$, so the span of the zeta integrals is $0$ and it does not contain the $L$-factor. Thus the statement is false, and this file proves the negation. The file proves the correct statement `Langlands.LocalGL1.GL1LFactorNontrivial`, with the added hypothesis that the space of $\pi$ is not zero. An irreducible representation is not zero, so this is sufficient for the local Langlands correspondence for $GL_1$.

## Main definitions

* `Langlands.LocalGL1.ord`: the order $\mathrm{ord}(x) \in \mathbb{Z}$ of the valuation of $x$.
* `Langlands.LocalGL1.ordBall`, `Langlands.LocalGL1.ordShell`: the ball $\varpi^N \mathcal{O}_K$ and the shell $\varpi^k \mathcal{O}_K^\times$.
* `Langlands.LocalGL1.extChar`: the extension of $\chi$ to $K$ by $\chi(0) = 0$.
* `Langlands.LocalGL1.zetaFn`: the function $y \mapsto \chi(y) |y|^{s - 1}$.
* `Langlands.LocalGL1.zeta`: the local zeta integral $Z(\varphi, \chi, s)$.
* `Langlands.LocalGL1.ballZeta`, `Langlands.LocalGL1.shellCoeff`: the zeta integral over a ball, and the integral of $\varphi \chi$ over a shell.
* `Langlands.LocalGL1.zetaBound`: the number $s_0(\chi) = 1 + \log_q |\chi(\varpi)|$. The zeta integrals converge for $\mathrm{Re}(s) > s_0(\chi)$.
* `Langlands.LocalGL1.entryHomeomorph`: the identification $M_1(K) \cong K$.
* `Langlands.LocalGL1.GL1LFactorNontrivial`: the statement `GL1LFactor` with the added hypothesis that the space of $\pi$ is not zero.

## Main results

* `Langlands.LocalGL1.unramified_iff`: $\chi$ is trivial on $\mathcal{O}_K^\times$ exactly when $\chi \circ \mathrm{art}^{-1}$ is trivial on the inertia group.
* `Langlands.LocalGL1.distribHaarChar_eq`: the Haar measure changes by $|a| = q^{-\mathrm{ord}(a)}$ under $y \mapsto a y$.
* `Langlands.LocalGL1.exists_zeta_eq`: Tate's local computation $Z(\varphi, \chi, s) = A(q^{-s}) / q^{-M s} + \varphi(0) (\chi(\varpi) q^{-s})^N T_0(s)$, with $T_0(s)$ the zeta integral of the indicator of $\mathcal{O}_K$.
* `Langlands.LocalGL1.gjZeta_eq_zeta`: the Godement-Jacquet zeta integral of $\chi \circ \det$ is a local zeta integral of $\chi$.
* `Langlands.LocalGL1.isGJLFactor_wdOfChar`: for $\pi \ne 0$, the $L$-factor of $\chi \circ \mathrm{art}^{-1}$ is the Godement-Jacquet $L$-factor of $\pi$.
* `Langlands.LocalGL1.gl1LFactorNontrivial`: the statement `GL1LFactorNontrivial`.
* `Langlands.LocalGL1.not_gl1LFactor`: the statement `GL1LFactor` is false.
* `Langlands.LocalGL1.localLanglandsGL_one`: the local Langlands correspondence `LocalLanglandsGL 1`, with no hypothesis.

## Proof

Let $T_N(s)$ be the zeta integral over the ball $\mathrm{ord} \ge N$ and $c_k$ the integral of $\varphi \chi$ over the shell $\mathrm{ord} = k$. Then $T_m = T_{m + 1} + c_m (q^{1 - s})^m$. If $\varphi$ is constant on the ball $\mathrm{ord} \ge N$, the change of variables $y \mapsto \varpi y$ gives $T_{N + 1} = \chi(\varpi) q^{-s} T_N$. For $\varphi = 1$ on $\mathcal{O}_K$ this gives $T_0 (1 - \chi(\varpi) q^{-s}) = c_0$. Here $c_0 = \mu(\mathcal{O}_K^\times) \ne 0$ when $\chi$ is unramified, and $c_0 = 0$ when $\chi$ is ramified. Thus the zeta integrals span the space $\mathbb{C}[q^{s}, q^{-s}] L(s, \chi)$, with $L(s, \chi) = (1 - \chi(\varpi) q^{-s})^{-1}$ or $L(s, \chi) = 1$.

## Implementation notes

The definition `IsGJLFactor` asks for convergence only for $\mathrm{Re}(s)$ large. This file uses the bound $\mathrm{Re}(s) > s_0(\chi)$, not $\mathrm{Re}(s) > 0$, because $\chi$ is not unitary in general.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta functions, thesis, 1950.
* C. J. Bushnell and G. Henniart, The local Langlands conjecture for $GL(2)$, chapter 6, section 23.
-/

namespace Langlands.LocalGL1

universe u

open ValuativeRel

section Valuation

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

local notation "iso" => IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K

variable (K) in
/-- The normalized valuation $\mathrm{ord}(x) \in \mathbb{Z}$, with $\mathrm{ord}(0) = 0$. A uniformizer has $\mathrm{ord} = 1$. -/
noncomputable def ord (x : K) : ℤ :=
  -WithZero.log (iso (valuation K x))

/-- The value group image of the valuation of $x \ne 0$ is not zero. -/
theorem iso_valuation_ne_zero {x : K} (hx : x ≠ 0) : iso (valuation K x) ≠ 0 := by
  simpa using hx

/-- The order is additive: $\mathrm{ord}(x y) = \mathrm{ord}(x) + \mathrm{ord}(y)$. -/
theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord K (x * y) = ord K x + ord K y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul (iso_valuation_ne_zero hx) (iso_valuation_ne_zero hy)]
  ring

/-- The order of $1$ is $0$. -/
theorem ord_one : ord K 1 = 0 := by simp [ord]

/-- The order of $x^{-1}$ is $-\mathrm{ord}(x)$. -/
theorem ord_inv {x : K} (hx : x ≠ 0) : ord K x⁻¹ = -ord K x := by
  have := ord_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ord_one] at this
  omega

/-- The order of $x^n$ is $n \, \mathrm{ord}(x)$. -/
theorem ord_zpow (x : K) (n : ℤ) : ord K (x ^ n) = n * ord K x := by
  simp only [ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

/-- For $x, y \ne 0$, $v(x) \le v(y)$ exactly when $\mathrm{ord}(y) \le \mathrm{ord}(x)$. -/
theorem valuation_le_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    valuation K x ≤ valuation K y ↔ ord K y ≤ ord K x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (iso_valuation_ne_zero hx)
    (iso_valuation_ne_zero hy), OrderIsoClass.map_le_map_iff]

/-- For $x, y \ne 0$, $v(x) = v(y)$ exactly when $\mathrm{ord}(x) = \mathrm{ord}(y)$. -/
theorem valuation_eq_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    valuation K x = valuation K y ↔ ord K x = ord K y := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_iff hx hy, valuation_le_iff hy hx]
  exact and_comm

/-- For $x \ne 0$, $v(x) \le 1$ exactly when $\mathrm{ord}(x) \ge 0$. -/
theorem valuation_le_one_iff {x : K} (hx : x ≠ 0) : valuation K x ≤ 1 ↔ 0 ≤ ord K x := by
  rw [← map_one (valuation K), valuation_le_iff hx one_ne_zero, ord_one]

/-- For $x \ne 0$, $v(x) = 1$ exactly when $\mathrm{ord}(x) = 0$. -/
theorem valuation_eq_one_iff {x : K} (hx : x ≠ 0) : valuation K x = 1 ↔ ord K x = 0 := by
  rw [← map_one (valuation K), valuation_eq_iff hx one_ne_zero, ord_one]

/-- Each integer is the order of an element $x \ne 0$. -/
theorem exists_ord_eq (n : ℤ) : ∃ x : K, x ≠ 0 ∧ ord K x = n := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective ((iso).symm (WithZero.exp (-n)))
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    have := congrArg (iso) hx
    rw [map_zero, OrderMonoidIso.apply_symm_apply, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  · simp [ord, hx]

/-- The residue field has a positive number $q$ of elements. -/
theorem residueCard_pos' : 0 < residueCard K := by
  unfold residueCard
  exact Nat.card_pos

/-- The number $q$ of elements of the residue field is larger than $1$. -/
theorem one_lt_residueCard : 1 < residueCard K := by
  unfold residueCard
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- For $x \ne 0$, the normalized absolute value is $|x| = q^{-\mathrm{ord}(x)}$. -/
theorem normAbs_eq_zpow {x : K} (hx : x ≠ 0) :
    normAbs K x = (residueCard K : ℝ) ^ (-ord K x) := by
  simp only [normAbs, hx, ↓reduceIte, ord, neg_neg]

/-- For $x \ne 0$, $|x| = 1$ exactly when $\mathrm{ord}(x) = 0$. -/
theorem normAbs_eq_one_iff {x : K} (hx : x ≠ 0) : normAbs K x = 1 ↔ ord K x = 0 := by
  rw [normAbs_eq_zpow hx]
  have h1 : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard
  constructor
  · intro h
    have := (zpow_right_injective₀ (by linarith : (0 : ℝ) < residueCard K) h1.ne').eq_iff.1
      (h.trans (zpow_zero _).symm)
    omega
  · intro h
    rw [h, neg_zero, zpow_zero]

/-- An element with $\mathrm{ord} = 1$ is a uniformizer. -/
theorem isUniformizer_of_ord_eq_one {x : K} (hx : x ≠ 0) (h : ord K x = 1) : IsUniformizer x := by
  have hint : x ∈ 𝒪[K] := (valuation_le_one_iff hx).2 (by omega)
  have hv := Valuation.integer.integers (valuation K)
  refine ⟨⟨x, hint⟩, ⟨fun hu => ?_, fun a b hab => ?_⟩, rfl⟩
  · have := (hv.isUnit_iff_valuation_eq_one).1 hu
    rw [show algebraMap 𝒪[K] K ⟨x, hint⟩ = x from rfl, valuation_eq_one_iff hx] at this
    omega
  · have hab' : x = (a : K) * b := congrArg Subtype.val hab
    have ha0 : (a : K) ≠ 0 := fun h0 => hx (by rw [hab', h0, zero_mul])
    have hb0 : (b : K) ≠ 0 := fun h0 => hx (by rw [hab', h0, mul_zero])
    have hsum := ord_mul ha0 hb0
    rw [← hab', h] at hsum
    have ha1 := (valuation_le_one_iff ha0).1 a.2
    have hb1 := (valuation_le_one_iff hb0).1 b.2
    rcases (show ord K a = 0 ∨ ord K b = 0 by omega) with h0 | h0
    · left
      exact (hv.isUnit_iff_valuation_eq_one).2 ((valuation_eq_one_iff ha0).2 h0)
    · right
      exact (hv.isUnit_iff_valuation_eq_one).2 ((valuation_eq_one_iff hb0).2 h0)

variable (K) in
/-- A chosen uniformizer of $K$, as a unit. -/
noncomputable def unif : Kˣ :=
  Units.mk0 (exists_ord_eq (K := K) 1).choose (exists_ord_eq (K := K) 1).choose_spec.1

/-- The order of the chosen uniformizer is $1$. -/
theorem ord_unif : ord K (unif K : K) = 1 :=
  (exists_ord_eq (K := K) 1).choose_spec.2

/-- The chosen element `unif K` is a uniformizer. -/
theorem isUniformizer_unif : IsUniformizer (unif K : K) :=
  isUniformizer_of_ord_eq_one (unif K).ne_zero ord_unif

/-- Each unit is $u \varpi^n$ with $\mathrm{ord}(u) = 0$ and $n = \mathrm{ord}(x)$. -/
theorem ord_mul_unif_zpow (x : Kˣ) :
    ord K ((x * unif K ^ (-ord K x) : Kˣ) : K) = 0 := by
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ord_mul x.ne_zero (zpow_ne_zero _ (unif K).ne_zero),
    ord_zpow, ord_unif]
  ring

end Valuation

section Artin

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The degree map $W_K^{ab} \to \mathbb{Z}$. The degree map of $W_K$ is trivial on the closure of the commutator subgroup, because its kernel is the inertia subgroup, which is open and contains the commutator subgroup. -/
noncomputable def degreeAb : WeilGroup.Ab K →* Multiplicative ℤ :=
  QuotientGroup.lift _ (WeilGroup.degree K) (by
    refine Subgroup.topologicalClosure_minimal _
      ((WeilGroup.commutator_le_inertia K).trans (WeilGroup.ker_degree K).ge) ?_
    rw [WeilGroup.ker_degree]
    exact Subgroup.isClosed_of_isOpen _ (WeilGroup.isOpen_inertia K))

/-- The degree of the class of $w$ in $W_K^{ab}$ is the degree of $w$. -/
theorem degreeAb_mk (w : WeilGroup K) :
    degreeAb K (QuotientGroup.mk w) = WeilGroup.degree K w :=
  QuotientGroup.lift_mk _ _ _

variable {K} in
/-- The local Artin map sends $x$ to an element of degree $\mathrm{ord}(x)$. -/
theorem degreeAb_art {art : Kˣ ≃ₜ* WeilGroup.Ab K} (hart : IsLocalArtinMap K art) (x : Kˣ) :
    degreeAb K (art x) = Multiplicative.ofAdd (ord K x) := by
  have h1 : ∀ y : Kˣ, IsUniformizer (y : K) → degreeAb K (art y) = Multiplicative.ofAdd 1 := by
    intro y hy
    obtain ⟨Φ, hΦ, h⟩ := hart.uniformizer y hy
    rw [h, degreeAb_mk]
    exact (WeilGroup.degree_eq_one_iff K Φ).2 hΦ
  set u : Kˣ := x * unif K ^ (-ord K x) with hu
  have hu0 : ord K (u : K) = 0 := ord_mul_unif_zpow x
  have huϖ : IsUniformizer ((u * unif K : Kˣ) : K) := by
    refine isUniformizer_of_ord_eq_one (u * unif K).ne_zero ?_
    rw [Units.val_mul, ord_mul u.ne_zero (unif K).ne_zero, hu0, ord_unif, zero_add]
  have hdu : degreeAb K (art u) = 1 := by
    have := h1 _ huϖ
    rw [map_mul, map_mul, h1 _ isUniformizer_unif] at this
    exact mul_eq_right.1 this
  have hx : x = u * unif K ^ ord K x := by rw [hu]; group
  rw [hx, map_mul, map_mul, hdu, one_mul, map_zpow, map_zpow, h1 _ isUniformizer_unif, ← hx, ← ofAdd_zsmul,
    smul_eq_mul, mul_one]

variable {K} in
/-- **The unramified characters on the two sides agree.** For a local Artin map $\mathrm{art}_K$, a character $\chi$ of $K^\times$ is trivial on the units $|x| = 1$ if and only if $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup. -/
theorem unramified_iff {art : Kˣ ≃ₜ* WeilGroup.Ab K} (hart : IsLocalArtinMap K art)
    (χ : Kˣ →* ℂˣ) : (∀ x : Kˣ, normAbs K x = 1 → χ x = 1) ↔
      ∀ i ∈ WeilGroup.inertia K, weilChar K art χ i = 1 := by
  constructor
  · intro h i hi
    rw [weilChar_apply]
    refine h _ ((normAbs_eq_one_iff (Units.ne_zero _)).2 ?_)
    have h2 := degreeAb_art hart (art.symm (QuotientGroup.mk i))
    rw [ContinuousMulEquiv.apply_symm_apply, degreeAb_mk,
      show WeilGroup.degree K i = 1 from (WeilGroup.ker_degree K).ge hi] at h2
    exact (Multiplicative.ofAdd.injective (h2.symm.trans ofAdd_zero.symm))
  · intro h x hx
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
    have hd := degreeAb_art hart x
    rw [← hw, degreeAb_mk, (normAbs_eq_one_iff x.ne_zero).1 hx, ofAdd_zero] at hd
    have hwi : w ∈ WeilGroup.inertia K := (WeilGroup.ker_degree K).le hd
    have := h w hwi
    rwa [weilChar_apply, hw, ContinuousMulEquiv.symm_apply_apply] at this

end Artin

section Topology

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open Topology Filter

variable (K) in
/-- The ball $\varpi^N \mathcal{O}_K$: the elements $z$ with $z = 0$ or $\mathrm{ord}(z) \ge N$. -/
def ordBall (N : ℤ) : Set K :=
  {z | z = 0 ∨ N ≤ ord K z}

variable (K) in
/-- The shell $\varpi^k \mathcal{O}_K^\times$: the elements $z \ne 0$ with $\mathrm{ord}(z) = k$. -/
def ordShell (k : ℤ) : Set K :=
  {z | z ≠ 0 ∧ ord K z = k}

/-- The point $0$ is in each ball. -/
theorem zero_mem_ordBall (N : ℤ) : (0 : K) ∈ ordBall K N := Or.inl rfl

/-- A point $z \ne 0$ is in the ball $\mathrm{ord} \ge N$ exactly when $\mathrm{ord}(z) \ge N$. -/
theorem mem_ordBall_of_ne_zero {z : K} (hz : z ≠ 0) {N : ℤ} : z ∈ ordBall K N ↔ N ≤ ord K z :=
  ⟨fun h => h.resolve_left hz, Or.inr⟩

/-- The balls get smaller when $N$ increases. -/
theorem ordBall_anti {M N : ℤ} (h : M ≤ N) : ordBall K N ⊆ ordBall K M := by
  rintro z (hz | hz)
  · exact Or.inl hz
  · exact Or.inr (h.trans hz)

/-- The shell $\mathrm{ord} = k$ is in the ball $\mathrm{ord} \ge k$. -/
theorem ordShell_subset_ordBall (k : ℤ) : ordShell K k ⊆ ordBall K k :=
  fun _ hz => Or.inr hz.2.ge

/-- The point $1$ is in the shell $\mathrm{ord} = 0$. -/
theorem one_mem_ordShell_zero : (1 : K) ∈ ordShell K 0 := ⟨one_ne_zero, ord_one⟩

/-- The valuation is locally constant away from $0$, so $\mathrm{ord}$ is too. -/
theorem eventually_ord_eq {y : K} (hy : y ≠ 0) :
    ∀ᶠ z in 𝓝 y, z ≠ 0 ∧ ord K z = ord K y := by
  have h := (valuation K).locally_const (x := y) (by simpa using hy)
  filter_upwards [h] with z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hz
    exact hy ((map_eq_zero _).1 hz.symm)
  exact ⟨hz0, (valuation_eq_iff hz0 hy).1 hz⟩

/-- Each ball is a neighborhood of $0$. -/
theorem ordBall_mem_nhds_zero (N : ℤ) : ordBall K N ∈ 𝓝 (0 : K) := by
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  have ha : ((unif K : K) ^ (N - 1)) ≠ 0 := zpow_ne_zero _ (unif K).ne_zero
  refine ⟨Units.mk0 (valuation K ((unif K : K) ^ (N - 1))) ((valuation K).ne_zero_iff.2 ha), fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  refine Or.inr ?_
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz
  have := mt (valuation_le_iff ha hz0).2 (not_le.2 hz)
  rw [ord_zpow, ord_unif, mul_one] at this
  omega

/-- Each neighborhood of $0$ contains a ball. -/
theorem exists_ordBall_subset {s : Set K} (hs : s ∈ 𝓝 (0 : K)) : ∃ N : ℤ, ordBall K N ⊆ s := by
  have h0 : (0 : K) ∈ s := mem_of_mem_nhds hs
  rw [IsValuativeTopology.mem_nhds_zero_iff] at hs
  obtain ⟨γ, hγ⟩ := hs
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact γ.ne_zero ha.symm
  refine ⟨ord K a + 1, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · rw [hz0]
    exact h0
  rw [mem_ordBall_of_ne_zero hz0] at hz
  refine hγ ?_
  simp only [Set.mem_ofPred_eq, ← ha]
  refine lt_of_le_of_ne ((valuation_le_iff hz0 ha0).2 (by omega)) fun h => ?_
  have := (valuation_eq_iff hz0 ha0).1 h
  omega

/-- Each ball is open. -/
theorem isOpen_ordBall (N : ℤ) : IsOpen (ordBall K N) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  by_cases hz0 : z = 0
  · subst hz0
    exact ordBall_mem_nhds_zero N
  · filter_upwards [eventually_ord_eq hz0] with w hw
    exact Or.inr (hw.2 ▸ (mem_ordBall_of_ne_zero hz0).1 hz)

/-- Each shell is open. -/
theorem isOpen_ordShell (k : ℤ) : IsOpen (ordShell K k) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [eventually_ord_eq hz.1] with w hw
  exact ⟨hw.1, hw.2.trans hz.2⟩

/-- Each shell is closed. -/
theorem isClosed_ordShell (k : ℤ) : IsClosed (ordShell K k) := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz => ?_)
  by_cases hz0 : z = 0
  · subst hz0
    filter_upwards [ordBall_mem_nhds_zero (k + 1)] with w hw hw'
    rcases hw with h | h
    · exact hw'.1 h
    · have := hw'.2
      omega
  · filter_upwards [eventually_ord_eq hz0] with w hw hw'
    exact hz ⟨hz0, hw.2 ▸ hw'.2⟩

/-- The ball $\mathrm{ord} \ge N$ is a closed ball for the valuation. -/
theorem ordBall_eq (N : ℤ) :
    ordBall K N = {z | valuation K z ≤ valuation K ((unif K : K) ^ N)} := by
  have ha : ((unif K : K) ^ N) ≠ 0 := zpow_ne_zero _ (unif K).ne_zero
  ext z
  by_cases hz0 : z = 0
  · simp [hz0, zero_mem_ordBall]
  · rw [mem_ordBall_of_ne_zero hz0, Set.mem_ofPred_eq, valuation_le_iff hz0 ha, ord_zpow, ord_unif,
      mul_one]

/-- Each ball is compact. -/
theorem isCompact_ordBall (N : ℤ) : IsCompact (ordBall K N) := by
  rw [ordBall_eq]
  exact IsNonarchimedeanLocalField.isCompact_closedBall K _

/-- Each ball is closed. -/
theorem isClosed_ordBall (N : ℤ) : IsClosed (ordBall K N) :=
  (isCompact_ordBall N).isClosed

/-- Each shell is compact. -/
theorem isCompact_ordShell (k : ℤ) : IsCompact (ordShell K k) :=
  (isCompact_ordBall k).of_isClosed_subset (isClosed_ordShell k) (ordShell_subset_ordBall k)

/-- For $a \ne 0$, $a z$ is in the ball $\mathrm{ord} \ge N$ exactly when $z$ is in the ball $\mathrm{ord} \ge N - \mathrm{ord}(a)$. -/
theorem mul_mem_ordBall_iff {a : K} (ha : a ≠ 0) (z : K) (N : ℤ) :
    a * z ∈ ordBall K N ↔ z ∈ ordBall K (N - ord K a) := by
  by_cases hz0 : z = 0
  · simp [hz0, zero_mem_ordBall]
  · rw [mem_ordBall_of_ne_zero (mul_ne_zero ha hz0), mem_ordBall_of_ne_zero hz0, ord_mul ha hz0]
    omega

/-- For $a \ne 0$, $a z$ is in the shell $\mathrm{ord} = k$ exactly when $z$ is in the shell $\mathrm{ord} = k - \mathrm{ord}(a)$. -/
theorem mul_mem_ordShell_iff {a : K} (ha : a ≠ 0) (z : K) (k : ℤ) :
    a * z ∈ ordShell K k ↔ z ∈ ordShell K (k - ord K a) := by
  by_cases hz0 : z = 0
  · simp [ordShell, hz0]
  · simp only [ordShell, Set.mem_ofPred_eq, mul_ne_zero ha hz0, hz0, ne_eq, not_false_eq_true,
      true_and, ord_mul ha hz0]
    omega

/-- The ball $\mathrm{ord} \ge 0$ is the ring of integers $\mathcal{O}_K$. -/
theorem ordBall_zero_eq_integer : ordBall K 0 = (𝒪[K] : Set K) := by
  ext z
  by_cases hz0 : z = 0
  · simp [hz0, zero_mem_ordBall]
  · rw [mem_ordBall_of_ne_zero hz0, SetLike.mem_coe, Valuation.mem_integer_iff,
      valuation_le_one_iff hz0]

/-- An integer is in the maximal ideal exactly when it is in $\varpi \mathcal{O}_K$. -/
theorem mem_ordBall_one_iff (a : 𝒪[K]) : (a : K) ∈ ordBall K 1 ↔ a ∈ 𝓂[K] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation K))]
  by_cases ha : (a : K) = 0
  · simp [ha, zero_mem_ordBall, show algebraMap 𝒪[K] K a = 0 from ha]
  · rw [mem_ordBall_of_ne_zero ha, show algebraMap 𝒪[K] K a = (a : K) from rfl,
      valuation_eq_one_iff ha]
    have := (valuation_le_one_iff ha).1 a.2
    omega

end Topology

section Measure

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The point $0$ of $K$ is not isolated. -/
theorem neBot_nhdsNE_zero : (𝓝[≠] (0 : K)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro t ht
  obtain ⟨N, hN⟩ := exists_ordBall_subset ht
  have h0 : ((unif K : K) ^ N) ≠ 0 := zpow_ne_zero _ (unif K).ne_zero
  refine ⟨(unif K : K) ^ N, hN ((mem_ordBall_of_ne_zero h0).2 ?_), h0⟩
  rw [ord_zpow, ord_unif, mul_one]

/-- Multiplication by a unit $a$ moves the ball $\mathrm{ord} \ge N$ to the ball $\mathrm{ord} \ge N + \mathrm{ord}(a)$. -/
theorem units_smul_ordBall (a : Kˣ) (N : ℤ) : a • ordBall K N = ordBall K (N + ord K a) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul,
    mul_mem_ordBall_iff (a⁻¹).ne_zero, Units.val_inv_eq_inv_val, ord_inv a.ne_zero, sub_neg_eq_add]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- The ring $\mathcal{O}_K$ is the disjoint union of the $q$ cosets of $\varpi \mathcal{O}_K$, so $\mu(\mathcal{O}_K) = q \mu(\varpi \mathcal{O}_K)$. -/
theorem measure_ordBall_zero : μ (ordBall K 0) = residueCard K * μ (ordBall K 1) := by
  choose c hc using IsLocalRing.residue_surjective (R := 𝒪[K])
  have hO : ∀ x : K, x ∈ ordBall K 0 ↔ x ∈ 𝒪[K] := fun x => by
    rw [ordBall_zero_eq_integer, SetLike.mem_coe]
  have hU : ordBall K 0 = ⋃ k : 𝓀[K], (fun x => x + -(c k : K)) ⁻¹' ordBall K 1 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro hx
      have hx' : x ∈ 𝒪[K] := (hO x).1 hx
      refine ⟨IsLocalRing.residue _ ⟨x, hx'⟩, ?_⟩
      have h := hc (IsLocalRing.residue _ ⟨x, hx'⟩)
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h
      have h2 := (mem_ordBall_one_iff _).2 (neg_mem h)
      convert h2 using 1
      simp only [neg_sub, AddSubgroupClass.coe_sub]
      ring
    · rintro ⟨k, hk⟩
      have h1 : x + -(c k : K) ∈ 𝒪[K] := (hO _).1 (ordBall_anti zero_le_one hk)
      have hx : x = (x + -(c k : K)) + c k := by ring
      rw [hO, hx]
      exact add_mem h1 (c k).2
  have hD : Pairwise (Function.onFun Disjoint
      fun k : 𝓀[K] => (fun x => x + -(c k : K)) ⁻¹' ordBall K 1) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun x hxk hxl => hkl ?_
    simp only [Set.mem_preimage] at hxk hxl
    have hk' : x + -(c k : K) ∈ 𝒪[K] := (hO _).1 (ordBall_anti zero_le_one hxk)
    have hl' : x + -(c l : K) ∈ 𝒪[K] := (hO _).1 (ordBall_anti zero_le_one hxl)
    have hmk := (mem_ordBall_one_iff ⟨_, hk'⟩).1 hxk
    have hml := (mem_ordBall_one_iff ⟨_, hl'⟩).1 hxl
    rw [← hc k, ← hc l, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : c k - c l = (⟨_, hl'⟩ : 𝒪[K]) - ⟨_, hk'⟩ := Subtype.ext (by
      simp only [AddSubgroupClass.coe_sub]
      ring)
    rw [this]
    exact sub_mem hml hmk
  have hB (k : 𝓀[K]) : μ ((fun x => x + -(c k : K)) ⁻¹' ordBall K 1) = μ (ordBall K 1) :=
    measure_preimage_add_right _ _ _
  rw [hU, measure_iUnion hD (fun k => (measurable_add_const _) (isOpen_ordBall 1).measurableSet),
    funext hB, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  rfl

omit [BorelSpace K] in
/-- Each ball has a measure that is not zero. -/
theorem measure_ordBall_ne_zero (N : ℤ) : μ (ordBall K N) ≠ 0 :=
  (isOpen_ordBall N).measure_ne_zero μ ⟨0, zero_mem_ordBall N⟩

omit [BorelSpace K] in
/-- Each ball has finite measure. -/
theorem measure_ordBall_ne_top (N : ℤ) : μ (ordBall K N) ≠ ∞ :=
  (isCompact_ordBall N).measure_lt_top.ne

omit [BorelSpace K] in
/-- Each shell has finite measure. -/
theorem measure_ordShell_ne_top (k : ℤ) : μ (ordShell K k) ≠ ∞ :=
  (isCompact_ordShell k).measure_lt_top.ne

variable [μ.Regular]

include μ in
/-- The modulus of $a \in K^\times$ is $|a| = q^{-\mathrm{ord}(a)}$. -/
theorem distribHaarChar_eq (a : Kˣ) :
    distribHaarChar K a = (residueCard K : ℝ≥0) ^ (-ord K (a : K)) := by
  have h0 := measure_ordBall_ne_zero μ 0
  have h1 := measure_ordBall_ne_top μ 0
  have hq : (residueCard K : ℝ≥0) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have hϖ : distribHaarChar K (unif K) = (residueCard K : ℝ≥0)⁻¹ := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul h0 h1 ?_
    rw [units_smul_ordBall, ord_unif, zero_add, measure_ordBall_zero μ, ENNReal.coe_inv hq,
      ← mul_assoc, ENNReal.coe_natCast, ENNReal.inv_mul_cancel (by exact_mod_cast hq)
      (ENNReal.natCast_ne_top _), one_mul]
  set u : Kˣ := a * unif K ^ (-ord K (a : K)) with hu
  have hu1 : distribHaarChar K u = 1 := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul h0 h1 ?_
    rw [units_smul_ordBall, ord_mul_unif_zpow, add_zero, ENNReal.coe_one, one_mul]
  have ha : a = u * unif K ^ ord K (a : K) := by rw [hu]; group
  rw [ha, map_mul, map_zpow, hu1, hϖ, one_mul, ← ha, inv_zpow']

/-- The image of $\mu$ under $x \mapsto a x$ is $|a|^{-1} \mu$. -/
theorem map_mul_left_eq {a : K} (ha : a ≠ 0) :
    Measure.map (fun x => a * x) μ = (((residueCard K : ℝ≥0) ^ ord K a : ℝ≥0) : ℝ≥0∞) • μ := by
  ext E hE
  rw [Measure.map_apply (measurable_const_mul a) hE, Measure.smul_apply, smul_eq_mul]
  have h : (fun x => a * x) ⁻¹' E = (Units.mk0 a ha)⁻¹ • E := Set.preimage_smul₀ ha E
  rw [h, ← distribHaarChar_mul μ, distribHaarChar_eq μ, Units.val_inv_eq_inv_val, Units.val_mk0,
    ord_inv ha, neg_neg]

/-- The change of variables $\int g(a x) \, d\mu(x) = |a|^{-1} \int g \, d\mu$. -/
theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : K}
    (ha : a ≠ 0) (g : K → E) :
    ∫ x, g (a * x) ∂μ = ((residueCard K : ℝ) ^ ord K a) • ∫ x, g x ∂μ := by
  have h := (Homeomorph.mulLeft₀ a ha).measurableEmbedding.integral_map (μ := μ) g
  simp only [Homeomorph.coe_mulLeft₀] at h
  rw [← h, map_mul_left_eq μ ha, integral_smul_measure]
  congr 1

omit [μ.Regular] in
/-- A point has measure zero. -/
theorem measure_zero_singleton : μ {0} = 0 := by
  have := neBot_nhdsNE_zero (K := K)
  exact measure_singleton 0

end Measure

section Character

open Topology Filter

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

open scoped Classical in
/-- The extension of a character $\chi$ of $K^\times$ to $K$ by $\chi(0) = 0$. -/
noncomputable def extChar (y : K) : ℂ :=
  if h : y = 0 then 0 else (χ (Units.mk0 y h) : ℂ)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The extension of $\chi$ is $0$ at $0$. -/
theorem extChar_zero : extChar χ (0 : K) = 0 := by simp [extChar]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The extension of $\chi$ is $\chi$ at each $y \ne 0$. -/
theorem extChar_of_ne_zero {y : K} (hy : y ≠ 0) : extChar χ y = χ (Units.mk0 y hy) := by
  simp [extChar, hy]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The extension of $\chi$ is not zero at each $y \ne 0$. -/
theorem extChar_ne_zero {y : K} (hy : y ≠ 0) : extChar χ y ≠ 0 := by
  rw [extChar_of_ne_zero χ hy]
  exact Units.ne_zero _

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The extension of $\chi$ is multiplicative: $\chi(a y) = \chi(a) \chi(y)$ for $a \ne 0$. -/
theorem extChar_mul {a : K} (ha : a ≠ 0) (y : K) :
    extChar χ (a * y) = χ (Units.mk0 a ha) * extChar χ y := by
  by_cases hy : y = 0
  · simp [hy, extChar_zero]
  · rw [extChar_of_ne_zero χ hy, extChar_of_ne_zero χ (mul_ne_zero ha hy), ← Units.val_mul,
      ← map_mul]
    congr 3
    ext
    simp

/-- The extension of a smooth character is locally constant away from $0$. -/
theorem eventually_extChar_eq (hχ : IsSmoothChar K χ) {y : K} (hy : y ≠ 0) :
    ∀ᶠ z in 𝓝 y, extChar χ z = extChar χ y := by
  obtain ⟨W, hW, hWker⟩ := (Units.isEmbedding_val₀ (G₀ := K)).isInducing.isOpen_iff.1 hχ
  have h1 : (1 : K) ∈ W := by
    have : (1 : Kˣ) ∈ (Units.val ⁻¹' W) := by
      rw [hWker]
      exact one_mem _
    simpa using this
  have hc : Tendsto (fun z : K => z * y⁻¹) (𝓝 y) (𝓝 1) := by
    have := Continuous.tendsto (f := fun z : K => z * y⁻¹) (by fun_prop) y
    simpa [Function.comp_def, mul_inv_cancel₀ hy] using this
  filter_upwards [hc (hW.mem_nhds h1), eventually_ne_nhds hy] with z hz hz0
  have hmem : Units.mk0 (z * y⁻¹) (mul_ne_zero hz0 (inv_ne_zero hy)) ∈ χ.ker := by
    rw [← SetLike.mem_coe, ← hWker]
    exact hz
  have hzy : Units.mk0 z hz0 = Units.mk0 y hy * Units.mk0 (z * y⁻¹) (mul_ne_zero hz0 (inv_ne_zero hy)) := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    field_simp
  rw [extChar_of_ne_zero χ hz0, extChar_of_ne_zero χ hy, hzy, map_mul, MonoidHom.mem_ker.1 hmem,
    mul_one]

/-- The power $|y|^w = (q^{-w})^{\mathrm{ord}(y)}$ for $y \ne 0$. -/
theorem normAbs_cpow {y : K} (hy : y ≠ 0) (w : ℂ) :
    (normAbs K y : ℂ) ^ w = ((residueCard K : ℂ) ^ (-w)) ^ ord K y := by
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast residueCard_pos'
  rw [normAbs_eq_zpow hy]
  have h1 : (((residueCard K : ℝ) ^ (-ord K y) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (zpow_pos hq _).ne'
  have h2 : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2, ← Complex.exp_int_mul,
    ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    show (residueCard K : ℂ) = ((residueCard K : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hq.le]
  congr 1
  push_cast
  ring

/-- The function $y \mapsto \chi(y) |y|^{s - 1}$ on $K$, which is $0$ at $0$. The zeta integral of $\Phi$ is $\int \Phi(y) \chi(y) |y|^{s - 1} \, dy$. -/
noncomputable def zetaFn (s : ℂ) (y : K) : ℂ :=
  extChar χ y * (normAbs K y : ℂ) ^ (s - 1)

/-- The function $\chi(y) |y|^{s - 1}$ is $0$ at $0$. -/
theorem zetaFn_zero (s : ℂ) : zetaFn χ s (0 : K) = 0 := by
  simp [zetaFn, extChar_zero]

/-- For $y \ne 0$, $\chi(y) |y|^{s - 1} = \chi(y) (q^{-s} q)^{\mathrm{ord}(y)}$. -/
theorem zetaFn_eq {y : K} (hy : y ≠ 0) (s : ℂ) :
    zetaFn χ s y = extChar χ y * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ ord K y := by
  have h2 : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  rw [zetaFn, normAbs_cpow hy, neg_sub, sub_eq_neg_add, Complex.cpow_add _ _ h2, Complex.cpow_one]

/-- For $a \ne 0$, $\chi(a y) |a y|^{s - 1} = \chi(a) (q^{-s} q)^{\mathrm{ord}(a)} \chi(y) |y|^{s - 1}$. -/
theorem zetaFn_mul {a : K} (ha : a ≠ 0) (s : ℂ) (y : K) :
    zetaFn χ s (a * y) = χ (Units.mk0 a ha) *
      ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ ord K a * zetaFn χ s y := by
  by_cases hy : y = 0
  · simp [hy, zetaFn_zero]
  have h2 : (residueCard K : ℂ) ^ (-s) * residueCard K ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne')))
      (by exact_mod_cast residueCard_pos'.ne')
  rw [zetaFn_eq χ (mul_ne_zero ha hy), zetaFn_eq χ hy, extChar_mul χ ha, ord_mul ha hy,
    zpow_add₀ h2]
  ring

/-- For a smooth character, $\chi(y) |y|^{s - 1}$ is locally constant away from $0$. -/
theorem eventually_zetaFn_eq (hχ : IsSmoothChar K χ) (s : ℂ) {y : K} (hy : y ≠ 0) :
    ∀ᶠ z in 𝓝 y, zetaFn χ s z = zetaFn χ s y := by
  filter_upwards [eventually_extChar_eq χ hχ hy, eventually_ord_eq hy] with z hz hz'
  rw [zetaFn_eq χ hz'.1, zetaFn_eq χ hy, hz, hz'.2]

end Character

section Zeta

open MeasureTheory Topology Filter
open scoped NNReal ENNReal

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

/-- The number $q^{-s} q$ is not zero. -/
theorem qX_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) * residueCard K ≠ 0 :=
  mul_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne')))
    (by exact_mod_cast residueCard_pos'.ne')

/-- The number $\chi(\varpi) q^{1 - s}$. -/
noncomputable def zetaRatio (s : ℂ) : ℂ :=
  (χ (unif K) : ℂ) * ((residueCard K : ℂ) ^ (-s) * residueCard K)

/-- The number $\chi(\varpi) q^{1 - s}$ is not zero. -/
theorem zetaRatio_ne_zero (s : ℂ) : zetaRatio χ s ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (qX_ne_zero s)

/-- For $y \ne 0$ with $k = \mathrm{ord}(y)$, the element $y \varpi^{-k}$ is a unit. -/
theorem mem_ordShell_zero_div {y : K} (hy : y ≠ 0) :
    y * ((unif K : K) ^ ord K y)⁻¹ ∈ ordShell K 0 := by
  have ha : (unif K : K) ^ ord K y ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  refine ⟨mul_ne_zero hy (inv_ne_zero ha), ?_⟩
  rw [ord_mul hy (inv_ne_zero ha), ord_inv ha, ord_zpow, ord_unif]
  ring

/-- For $y = \varpi^k u$ with $k = \mathrm{ord}(y)$, the value $\chi(y) |y|^{s - 1}$ is $(\chi(\varpi) q^{1 - s})^k \chi(u)$. -/
theorem zetaFn_eq_zetaRatio {y : K} (hy : y ≠ 0) (s : ℂ) :
    zetaFn χ s y = zetaRatio χ s ^ ord K y * extChar χ (y * ((unif K : K) ^ ord K y)⁻¹) := by
  have ha : (unif K : K) ^ ord K y ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have hu := mem_ordShell_zero_div hy
  have hyu : y = (unif K : K) ^ ord K y * (y * ((unif K : K) ^ ord K y)⁻¹) := by field_simp
  conv_lhs => rw [hyu]
  rw [zetaFn_mul χ ha, zetaFn_eq χ hu.1, hu.2, zpow_zero, mul_one, ord_zpow, ord_unif, mul_one]
  have : Units.mk0 ((unif K : K) ^ ord K y) ha = unif K ^ ord K y := by
    ext
    simp
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val, zetaRatio]
  simp only [mul_zpow]

include χ in
/-- The extension of a smooth character is continuous away from $0$. -/
theorem continuousOn_extChar (hχ : IsSmoothChar K χ) : ContinuousOn (extChar χ) {0}ᶜ :=
  fun _ hy => ((continuousAt_congr (eventually_extChar_eq χ hχ hy)).2
    continuousAt_const).continuousWithinAt

/-- The function $\chi(y) |y|^{s - 1}$ is continuous away from $0$. -/
theorem continuousOn_zetaFn (hχ : IsSmoothChar K χ) (s : ℂ) : ContinuousOn (zetaFn χ s) {0}ᶜ :=
  fun _ hy => ((continuousAt_congr (eventually_zetaFn_eq χ hχ s hy)).2
    continuousAt_const).continuousWithinAt

/-- A smooth character is bounded on $\mathcal{O}_K^\times$. -/
theorem exists_bound_extChar (hχ : IsSmoothChar K χ) :
    ∃ C, ∀ y ∈ ordShell K 0, ‖extChar χ y‖ ≤ C :=
  (isCompact_ordShell 0).exists_bound_of_continuousOn
    ((continuousOn_extChar χ hχ).mono fun _ hy => hy.1)

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- A function that is continuous away from $0$ is almost everywhere strongly measurable for a Haar measure, because a point has measure zero. -/
theorem aestronglyMeasurable_of_continuousOn {f : K → ℂ} (hf : ContinuousOn f {0}ᶜ) :
    AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable (μ := μ) (measurableSet_singleton 0).compl
  rwa [Measure.restrict_eq_self_of_ae_mem (s := ({0} : Set K)ᶜ)
    (compl_mem_ae_iff.2 (measure_zero_singleton μ))] at h

/-- If $|\chi(\varpi) q^{1 - s}| \le 1$, then $\chi(y) |y|^{s - 1}$ is integrable on each measurable subset of a ball. -/
theorem integrable_indicator_zetaFn (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1)
    {S : Set K} (hS : MeasurableSet S) {N : ℤ} (hSN : S ⊆ ordBall K N) :
    Integrable (S.indicator (zetaFn χ s)) μ := by
  obtain ⟨C, hC⟩ := exists_bound_extChar χ hχ
  have hr : 0 < ‖zetaRatio χ s‖ := norm_pos_iff.2 (zetaRatio_ne_zero χ s)
  rw [integrable_indicator_iff hS]
  refine Measure.integrableOn_of_bounded (M := ‖zetaRatio χ s‖ ^ N * C)
    (ne_top_of_le_ne_top (measure_ordBall_ne_top μ N) (measure_mono hSN))
    (aestronglyMeasurable_of_continuousOn μ (continuousOn_zetaFn χ hχ s)) ?_
  refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun y hy => ?_)
  by_cases hy0 : y = 0
  · rw [hy0, zetaFn_zero, norm_zero]
    exact mul_nonneg (zpow_nonneg hr.le _) ((norm_nonneg _).trans (hC 1 one_mem_ordShell_zero))
  rw [zetaFn_eq_zetaRatio χ hy0, norm_mul, norm_zpow]
  exact mul_le_mul (zpow_le_zpow_right_of_le_one₀ hr hs ((mem_ordBall_of_ne_zero hy0).1 (hSN hy)))
    (hC _ (mem_ordShell_zero_div hy0)) (norm_nonneg _) (zpow_nonneg hr.le _)

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- The ball $\mathrm{ord} \ge m$ is the union of the ball $\mathrm{ord} \ge m + 1$ and the shell $\mathrm{ord} = m$. -/
theorem indicator_ordBall_eq (m : ℤ) (f : K → ℂ) (y : K) :
    (ordBall K m).indicator f y = (ordBall K (m + 1)).indicator f y + (ordShell K m).indicator f y := by
  by_cases hy : y = 0
  · subst hy
    rw [Set.indicator_of_mem (zero_mem_ordBall _), Set.indicator_of_mem (zero_mem_ordBall _),
      Set.indicator_of_notMem (fun h : (0 : K) ∈ ordShell K m => h.1 rfl), add_zero]
  have hb := fun N => mem_ordBall_of_ne_zero (K := K) hy (N := N)
  have hs : y ∈ ordShell K m ↔ ord K y = m := ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  by_cases h1 : ord K y = m
  · rw [Set.indicator_of_mem ((hb m).2 h1.ge),
      Set.indicator_of_notMem (s := ordBall K (m + 1)) (by rw [hb]; omega),
      Set.indicator_of_mem (hs.2 h1), zero_add]
  · rw [Set.indicator_of_notMem (s := ordShell K m) (fun h => h1 (hs.1 h)), add_zero]
    by_cases h2 : m + 1 ≤ ord K y
    · rw [Set.indicator_of_mem ((hb m).2 (by omega)), Set.indicator_of_mem ((hb _).2 h2)]
    · rw [Set.indicator_of_notMem (s := ordBall K m) (by rw [hb]; omega),
        Set.indicator_of_notMem (s := ordBall K (m + 1)) (by rw [hb]; omega)]

/-- The integral $\int_{\mathrm{ord}(y) \ge N} \varphi(y) \chi(y) |y|^{s - 1} \, dy$. -/
noncomputable def ballZeta (φ : K → ℂ) (s : ℂ) (N : ℤ) : ℂ :=
  ∫ y, (ordBall K N).indicator (fun y => φ y * zetaFn χ s y) y ∂μ

/-- The integral $\int_{\mathrm{ord}(y) = k} \varphi(y) \chi(y) \, dy$. It does not depend on $s$. -/
noncomputable def shellCoeff (φ : K → ℂ) (k : ℤ) : ℂ :=
  ∫ y, (ordShell K k).indicator (fun y => φ y * extChar χ y) y ∂μ

/-- The step $T_m = T_{m + 1} + c_m (q^{1 - s})^m$ for the integrals over balls, with $c_m$ the integral over the shell $\mathrm{ord} = m$. -/
theorem ballZeta_eq_succ (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1)
    {φ : K → ℂ} (hφm : AEStronglyMeasurable φ μ) {C : ℝ} (hφC : ∀ y, ‖φ y‖ ≤ C) (m : ℤ) :
    ballZeta χ μ φ s m = ballZeta χ μ φ s (m + 1) +
      shellCoeff χ μ φ m * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ m := by
  have hint : ∀ S, MeasurableSet S → S ⊆ ordBall K m →
      Integrable (S.indicator (fun y => φ y * zetaFn χ s y)) μ := by
    intro S hS hSm
    have : S.indicator (fun y => φ y * zetaFn χ s y) = fun y => φ y * S.indicator (zetaFn χ s) y :=
      funext fun y => Set.indicator_mul_right S φ (zetaFn χ s)
    rw [this]
    exact (integrable_indicator_zetaFn χ μ hχ hs hS hSm).bdd_mul hφm (Eventually.of_forall hφC)
  have hshell : ∀ y, (ordShell K m).indicator (fun y => φ y * zetaFn χ s y) y =
      (ordShell K m).indicator (fun y => φ y * extChar χ y) y *
        ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ m := by
    intro y
    by_cases hy : y ∈ ordShell K m
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, zetaFn_eq χ hy.1, hy.2, mul_assoc]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold ballZeta shellCoeff
  simp_rw [indicator_ordBall_eq m]
  rw [integral_add (hint _ (isClosed_ordBall _).measurableSet (ordBall_anti (by omega)))
    (hint _ (isClosed_ordShell m).measurableSet (ordShell_subset_ordBall m))]
  simp_rw [hshell]
  rw [integral_mul_const]

/-- The sum $T_m = T_{m + n} + \sum_{j < n} c_{m + j} (q^{1 - s})^{m + j}$. -/
theorem ballZeta_eq_add (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1)
    {φ : K → ℂ} (hφm : AEStronglyMeasurable φ μ) {C : ℝ} (hφC : ∀ y, ‖φ y‖ ≤ C) (m : ℤ) (n : ℕ) :
    ballZeta χ μ φ s m = ballZeta χ μ φ s (m + n) + ∑ j ∈ Finset.range n,
      shellCoeff χ μ φ (m + j) * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ (m + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, ballZeta_eq_succ χ μ hχ hs hφm hφC (m + n), Finset.sum_range_succ]
    push_cast
    ring_nf

variable [μ.Regular]

/-- The step $T_{N + 1} = \chi(\varpi) q^{-s} T_N$ for $\varphi = 1$. -/
theorem ballZeta_one_succ (s : ℂ) (N : ℤ) :
    ballZeta χ μ (fun _ => 1) s (N + 1) =
      (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) * ballZeta χ μ (fun _ => 1) s N := by
  have hϖ : (unif K : K) ≠ 0 := Units.ne_zero _
  have h := integral_comp_mul_left μ hϖ
    ((ordBall K (N + 1)).indicator (fun y => (fun _ => (1 : ℂ)) y * zetaFn χ s y))
  have hfun : (fun x => (ordBall K (N + 1)).indicator (fun y => (fun _ => (1 : ℂ)) y * zetaFn χ s y)
      ((unif K : K) * x)) = fun x => zetaRatio χ s *
        (ordBall K N).indicator (fun y => (fun _ => (1 : ℂ)) y * zetaFn χ s y) x := by
    funext x
    by_cases hx : x ∈ ordBall K N
    · have : (unif K : K) * x ∈ ordBall K (N + 1) := by
        rw [mul_mem_ordBall_iff hϖ, ord_unif]
        simpa using hx
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hx, one_mul, one_mul, zetaFn_mul χ hϖ,
        ord_unif, zpow_one, Units.mk0_val, zetaRatio]
    · have : (unif K : K) * x ∉ ordBall K (N + 1) := by
        rw [mul_mem_ordBall_iff hϖ, ord_unif]
        simpa using hx
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hx, mul_zero]
  rw [hfun, integral_const_mul, ord_unif, zpow_one, Complex.real_smul] at h
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  unfold ballZeta
  rw [zetaRatio] at h
  push_cast at h
  refine mul_left_cancel₀ hq ?_
  linear_combination -h

/-- The formula $T_N = (\chi(\varpi) q^{-s})^N T_0$ for $\varphi = 1$ and $N \ge 0$. -/
theorem ballZeta_one_nat (s : ℂ) (N : ℕ) :
    ballZeta χ μ (fun _ => 1) s N =
      ((χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N * ballZeta χ μ (fun _ => 1) s 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, ballZeta_one_succ, ih, pow_succ]
    ring

/-- The zeta integral $Z(\varphi, \chi, s) = \int_K \varphi(y) \chi(y) |y|^{s - 1} \, dy$. -/
noncomputable def zeta (φ : K → ℂ) (s : ℂ) : ℂ :=
  ∫ y, φ y * zetaFn χ s y ∂μ

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- If $|\chi(\varpi) q^{1 - s}| \le 1$, then $1 - \chi(\varpi) q^{-s} \ne 0$. -/
theorem one_sub_ne_zero {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1) :
    1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard
  have hq0 : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast residueCard_pos'.ne'
  have heq : (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) = zetaRatio χ s / residueCard K := by
    rw [zetaRatio]
    field_simp
  intro h
  have h2 : ‖zetaRatio χ s / residueCard K‖ < 1 := by
    rw [norm_div, Complex.norm_natCast, div_lt_one (by linarith)]
    linarith
  rw [← heq, ← sub_eq_zero.1 h, norm_one] at h2
  exact lt_irrefl _ h2

/-- The integral $T_0$ over $\mathcal{O}_K$ for $\varphi = 1$ satisfies $T_0 (1 - \chi(\varpi) q^{-s}) = c_0$, with $c_0 = \int_{\mathcal{O}_K^\times} \chi$. -/
theorem ballZeta_one_zero (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1) :
    ballZeta χ μ (fun _ => 1) s 0 * (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) =
      shellCoeff χ μ (fun _ => 1) 0 := by
  have h := ballZeta_eq_succ χ μ hχ hs (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (C := 1) (fun _ => by simp) 0
  rw [ballZeta_one_succ, zpow_zero, mul_one] at h
  linear_combination h

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- For $\chi$ trivial on $\mathcal{O}_K^\times$, the constant $c_0$ is the volume of $\mathcal{O}_K^\times$. -/
theorem shellCoeff_one_of_unramified (hχ1 : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) :
    shellCoeff χ μ (fun _ => 1) 0 = (μ.real (ordShell K 0) : ℂ) := by
  have : ∀ y, (ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * extChar χ y) y =
      (ordShell K 0).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    by_cases hy : y ∈ ordShell K 0
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul, extChar_of_ne_zero χ hy.1,
        hχ1 _ (by rw [Units.val_mk0]; exact (normAbs_eq_one_iff hy.1).2 hy.2), Units.val_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  unfold shellCoeff
  simp_rw [this]
  rw [integral_indicator_const _ (isClosed_ordShell 0).measurableSet, Complex.real_smul, mul_one]

/-- For $\chi$ not trivial on $\mathcal{O}_K^\times$, the constant $c_0$ is $0$. -/
theorem shellCoeff_one_of_ramified {u : Kˣ} (hu : normAbs K u = 1) (hχu : χ u ≠ 1) :
    shellCoeff χ μ (fun _ => 1) 0 = 0 := by
  have hu0 : ord K (u : K) = 0 := (normAbs_eq_one_iff u.ne_zero).1 hu
  have h := integral_comp_mul_left μ u.ne_zero
    ((ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * extChar χ y))
  have hfun : (fun x => (ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * extChar χ y)
      ((u : K) * x)) = fun x => (χ u : ℂ) *
        (ordShell K 0).indicator (fun y => (fun _ => (1 : ℂ)) y * extChar χ y) x := by
    funext x
    have hm : (u : K) * x ∈ ordShell K 0 ↔ x ∈ ordShell K 0 := by
      rw [mul_mem_ordShell_iff u.ne_zero, hu0, sub_zero]
    by_cases hx : x ∈ ordShell K 0
    · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx, one_mul, one_mul,
        extChar_mul χ u.ne_zero, Units.mk0_val]
    · rw [Set.indicator_of_notMem (fun h => hx (hm.1 h)), Set.indicator_of_notMem hx, mul_zero]
  rw [hfun, integral_const_mul, hu0, zpow_zero, one_smul] at h
  unfold shellCoeff
  have h1 : (χ u : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (fun h => hχu (Units.val_eq_one.1 h))
  refine mul_left_cancel₀ h1 ?_
  linear_combination h

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- A locally constant function on $K$ is constant on a ball $\mathrm{ord} \ge N$ with $N \ge 0$. -/
theorem exists_nat_eq_of_isLocallyConstant {φ : K → ℂ} (hφ : IsLocallyConstant φ) :
    ∃ N : ℕ, ∀ y ∈ ordBall K N, φ y = φ 0 := by
  obtain ⟨N, hN⟩ := exists_ordBall_subset ((IsLocallyConstant.iff_eventually_eq φ).1 hφ 0)
  exact ⟨N.toNat, fun y hy => hN (ordBall_anti (Int.self_le_toNat N) hy)⟩

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- A function on $K$ with compact support has its support in a ball $\mathrm{ord} \ge -M$ with $M \ge 0$. -/
theorem exists_nat_tsupport_subset {φ : K → ℂ} (hφ : HasCompactSupport φ) :
    ∃ M : ℕ, tsupport φ ⊆ ordBall K (-(M : ℤ)) := by
  refine hφ.isCompact.elim_directed_cover (fun n : ℕ => ordBall K (-(n : ℤ)))
    (fun n => isOpen_ordBall _) ?_ ?_
  · intro z _
    rw [Set.mem_iUnion]
    by_cases hz : z = 0
    · exact ⟨0, hz ▸ zero_mem_ordBall _⟩
    · exact ⟨(-ord K z).toNat, (mem_ordBall_of_ne_zero hz).2 (by omega)⟩
  · exact fun m n => ⟨max m n, ordBall_anti (by push_cast; omega),
      ordBall_anti (by push_cast; omega)⟩

/-- **Tate's local computation.** For a Schwartz-Bruhat function $\varphi$ on $K$ there are a polynomial $A$ and $M, N \ge 0$ with $Z(\varphi, \chi, s) = A(X) X^{-M} + \varphi(0) (\chi(\varpi) X)^N T_0(s)$, where $X = q^{-s}$ and $T_0(s) = Z(1_{\mathcal{O}_K}, \chi, s)$, for each $s$ with $|\chi(\varpi) q^{1 - s}| \le 1$. -/
theorem exists_zeta_eq (hχ : IsSmoothChar K χ) {φ : K → ℂ} (hφ : IsLocallyConstant φ)
    (hφs : HasCompactSupport φ) :
    ∃ (A : Polynomial ℂ) (M N : ℕ), ∀ s : ℂ, ‖zetaRatio χ s‖ ≤ 1 →
      zeta χ μ φ s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ M +
        φ 0 * ((χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
          ballZeta χ μ (fun _ => 1) s 0 := by
  obtain ⟨N, hN⟩ := exists_nat_eq_of_isLocallyConstant hφ
  obtain ⟨M, hM⟩ := exists_nat_tsupport_subset hφs
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  have hφm : AEStronglyMeasurable φ μ := hφ.continuous.aestronglyMeasurable
  refine ⟨∑ j ∈ Finset.range (M + N), Polynomial.C (shellCoeff χ μ φ (-(M : ℤ) + j) *
    (residueCard K : ℂ) ^ (-(M : ℤ) + j)) * Polynomial.X ^ j, M, N, fun s hs => ?_⟩
  have hX : (residueCard K : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne'))
  have h1 : zeta χ μ φ s = ballZeta χ μ φ s (-(M : ℤ)) := by
    unfold zeta ballZeta
    congr 1
    funext y
    by_cases hy : y ∈ ordBall K (-(M : ℤ))
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (fun h => hy (hM h)),
        zero_mul]
  have h2 : ballZeta χ μ φ s N = φ 0 * ballZeta χ μ (fun _ => 1) s N := by
    unfold ballZeta
    rw [← integral_const_mul]
    congr 1
    funext y
    by_cases hy : y ∈ ordBall K N
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hN y hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [h1, ballZeta_eq_add χ μ hχ hs hφm hC (-(M : ℤ)) (M + N),
    show -(M : ℤ) + ((M + N : ℕ) : ℤ) = (N : ℤ) by push_cast; ring, h2, ballZeta_one_nat,
    Polynomial.eval_finsetSum, Finset.sum_div]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_zpow, zpow_add₀ hX, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp
  · ring

omit [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The zeta integral of the indicator of $\mathcal{O}_K$ is $T_0$. -/
theorem zeta_indicator_ordBall (s : ℂ) :
    zeta χ μ ((ordBall K 0).indicator fun _ => 1) s = ballZeta χ μ (fun _ => 1) s 0 := by
  unfold zeta ballZeta
  congr 1
  funext y
  by_cases hy : y ∈ ordBall K 0
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The zeta integral of $1_{\mathcal{O}_K^\times} \chi^{-1}$ is the volume of $\mathcal{O}_K^\times$. -/
theorem zeta_indicator_ordShell (s : ℂ) :
    zeta χ μ ((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) s = μ.real (ordShell K 0) := by
  have : ∀ y, (ordShell K 0).indicator (fun y => (extChar χ y)⁻¹) y * zetaFn χ s y =
      (ordShell K 0).indicator (fun _ => (1 : ℂ)) y := by
    intro y
    by_cases hy : y ∈ ordShell K 0
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, zetaFn,
        (normAbs_eq_one_iff hy.1).2 hy.2, Complex.ofReal_one, Complex.one_cpow, mul_one,
        inv_mul_cancel₀ (extChar_ne_zero χ hy.1)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  unfold zeta
  simp_rw [this]
  rw [integral_indicator_const _ (isClosed_ordShell 0).measurableSet, Complex.real_smul, mul_one]

omit [BorelSpace K] [μ.Regular] in
/-- The volume of $\mathcal{O}_K^\times$ is not zero. -/
theorem measureReal_ordShell_ne_zero : μ.real (ordShell K 0) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨(isOpen_ordShell 0).measure_ne_zero μ ⟨1, one_mem_ordShell_zero⟩,
    measure_ordShell_ne_top μ 0⟩

end Zeta

section Bound

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (χ : Kˣ →* ℂˣ)

/-- The bound $s_0(\chi) = 1 + \log_q |\chi(\varpi)|$. The zeta integrals converge absolutely for $\mathrm{Re}(s) > s_0(\chi)$. -/
noncomputable def zetaBound : ℝ :=
  1 + Real.logb (residueCard K) ‖(χ (unif K) : ℂ)‖

/-- For $\mathrm{Re}(s) > s_0(\chi)$, the number $|\chi(\varpi) q^{1 - s}|$ is at most $1$. -/
theorem norm_zetaRatio_le {s : ℂ} (hs : zetaBound χ < s.re) : ‖zetaRatio χ s‖ ≤ 1 := by
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard
  have hq0 : (0 : ℝ) < residueCard K := by linarith
  have hc : 0 < ‖(χ (unif K) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hn : ‖(residueCard K : ℂ) ^ (-s)‖ = (residueCard K : ℝ) ^ (-s.re) := by
    rw [show (residueCard K : ℂ) = ((residueCard K : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  rw [zetaRatio, norm_mul, norm_mul, hn, Complex.norm_natCast]
  have h : ‖(χ (unif K) : ℂ)‖ =
      (residueCard K : ℝ) ^ (Real.logb (residueCard K) ‖(χ (unif K) : ℂ)‖) :=
    (Real.rpow_logb hq0 hq.ne' hc).symm
  rw [h, ← Real.rpow_add_one hq0.ne', ← Real.rpow_add hq0]
  apply Real.rpow_le_one_of_one_le_of_nonpos hq.le
  unfold zetaBound at hs
  linarith

end Bound

section Main

open MeasureTheory Topology Filter

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [Field K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The indicator of a clopen set $S$ times a function that is locally constant on $S$ is locally constant. -/
theorem isLocallyConstant_indicator {S : Set K} (hSo : IsOpen S) (hSc : IsClosed S) {f : K → ℂ}
    (hf : ∀ y ∈ S, ∀ᶠ z in 𝓝 y, f z = f y) : IsLocallyConstant (S.indicator f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  by_cases hy : y ∈ S
  · filter_upwards [hSo.mem_nhds hy, hf y hy] with z hz hfz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hy, hfz]
  · filter_upwards [hSc.isOpen_compl.mem_nhds hy] with z hz
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]

variable (K) in
/-- The homeomorphism $M_1(K) \to K$, $x \mapsto x_{00}$. -/
def entryHomeomorph : Matrix (Fin 1) (Fin 1) K ≃ₜ K where
  toFun x := x 0 0
  invFun y := fun _ _ => y
  left_inv x := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable (K) in
/-- The additive isomorphism $M_1(K) \to K$, $x \mapsto x_{00}$. -/
def entryAddEquiv : Matrix (Fin 1) (Fin 1) K ≃+ K :=
  { (entryHomeomorph K).toEquiv with map_add' := fun _ _ => rfl }

/-- For a representation of $GL_1(K)$ by $\chi \circ \det$, the Godement-Jacquet zeta integral is $\lambda(v) Z(\Phi \circ e^{-1}, \chi, s)$ for the image of the Haar measure of $M_1(K)$ under $e : x \mapsto x_{00}$. -/
theorem gjZeta_eq_zeta [MeasurableSpace K] [BorelSpace K] (χ : Kˣ →* ℂˣ)
    (π : SmoothRep (GL (Fin 1) K))
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (Φ : Matrix (Fin 1) (Fin 1) K → ℂ) (v : π.V) (l : Module.Dual ℂ π.V) (s : ℂ) :
    gjZeta K π Φ v l s = l v * zeta χ (letI := matrixBorel K 1
      Measure.map (entryHomeomorph K) (matrixHaar K 1)) (Φ ∘ (entryHomeomorph K).symm) s := by
  let := matrixBorel K 1
  have : BorelSpace (Matrix (Fin 1) (Fin 1) K) := ⟨rfl⟩
  unfold gjZeta zeta
  rw [(entryHomeomorph K).measurableEmbedding.integral_map, ← integral_const_mul]
  congr 1
  funext x
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  have hdet : x.det = x 0 0 := Matrix.det_fin_one x
  have he : entryHomeomorph K x = x 0 0 := rfl
  rw [he]
  split_ifs with h
  · have h0 : x 0 0 ≠ 0 := hdet ▸ h.ne_zero
    have hd : Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) = Units.mk0 (x 0 0) h0 := by
      ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mk0, Matrix.det_fin_one]
      rfl
    rw [SmoothRep.coeff, hπ, map_smul, smul_eq_mul, zetaFn, extChar_of_ne_zero χ h0, hdet, hd]
    push_cast
    ring_nf
  · have h0 : x 0 0 = 0 := by
      by_contra h0
      exact h (hdet ▸ Ne.isUnit h0)
    rw [h0, zetaFn_zero, mul_zero, mul_zero]

/-- **Tate's local theory for $GL_1$** in the Godement-Jacquet form. Let $\pi$ be a nonzero representation of $GL_1(K)$ that acts by $\chi \circ \det$. Then the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0)$ is the Godement-Jacquet L-factor of $\pi$. -/
theorem isGJLFactor_wdOfChar {art : Kˣ ≃ₜ* WeilGroup.Ab K} (hart : IsLocalArtinMap K art)
    (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (π : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) :
    IsGJLFactor K π (wdOfChar K art χ hχ).lFactor := by
  classical
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let := matrixBorel K 1
  have : BorelSpace (Matrix (Fin 1) (Fin 1) K) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → K))
  have : (matrixHaar K 1).IsAddHaarMeasure := by
    unfold matrixHaar
    infer_instance
  have : (matrixHaar K 1).Regular := by
    unfold matrixHaar
    infer_instance
  set e := entryHomeomorph K
  set μ : Measure K := Measure.map e (matrixHaar K 1) with hμ
  have : μ.IsAddHaarMeasure :=
    (entryAddEquiv K).isAddHaarMeasure_map (matrixHaar K 1) e.continuous e.symm.continuous
  have : μ.Regular := Measure.Regular.map e
  have hZ : ∀ Φ (w : π.V) (m : Module.Dual ℂ π.V) s,
      gjZeta K π Φ w m s = m w * zeta χ μ (Φ ∘ e.symm) s :=
    fun Φ w m s => gjZeta_eq_zeta χ π hπ Φ w m s
  have hL : ∀ s, (wdOfChar K art χ hχ).lFactor s =
      if ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 then (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 1 := by
    intro s
    rw [lFactor_wdOfChar_eq K art hart χ hχ (unif K) isUniformizer_unif s, ← unramified_iff hart χ]
  have hX : ∀ s : ℂ, (residueCard K : ℂ) ^ (-s) ≠ 0 := fun s =>
    Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne'))
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  have hsm : l ∈ smoothVectors π.ρ.dual := by
    refine Subgroup.isOpen_mono (H₁ := (detChar K 1 χ).ker) ?_ (isOpen_ker_detChar K 1 χ hχ)
    intro g hg
    have hg' : (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = 1 := by
      have : χ (Matrix.GeneralLinearGroup.det g) = 1 := hg
      rw [this, Units.val_one]
    rw [mem_vecStabilizer, Representation.dual_apply]
    ext w
    simp [Module.Dual.transpose_apply, hπ, hg']
  have hc0 : (μ.real (ordShell K 0) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (measureReal_ordShell_ne_zero μ)
  refine ⟨?_, ?_, ?_⟩
  · by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · exact ⟨1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X, by simp,
        fun s => by rw [(hL s).trans (ite_eq_left hunr)]; simp⟩
    · exact ⟨1, by simp, fun s => by rw [(hL s).trans (ite_eq_right hunr)]; simp⟩
  · intro Φ w m hΦ
    obtain ⟨A, M, N, hA⟩ := exists_zeta_eq χ μ hχ (hΦ.1.comp_continuous e.symm.continuous)
      (hΦ.2.comp_homeomorph e.symm)
    by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · refine ⟨Polynomial.C (m.1 w) * (A * (1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X) +
        Polynomial.C ((Φ ∘ e.symm) 0 * (μ.real (ordShell K 0) : ℂ) * (χ (unif K) : ℂ) ^ N) *
          Polynomial.X ^ (N + M)), M, zetaBound χ, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_unramified χ μ hunr] at h0
      have h1 := one_sub_ne_zero χ hs'
      have hT : ballZeta χ μ (fun _ => 1) s 0 =
          (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
        rw [← h0, mul_div_cancel_right₀ _ h1]
      rw [hZ, hA s hs', hT, (hL s).trans (ite_eq_left hunr)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
      have hXs := hX s
      generalize (residueCard K : ℂ) ^ (-s) = X at hXs h1 ⊢
      generalize (χ (unif K) : ℂ) = c at h1 ⊢
      have h1' : 1 - X * c ≠ 0 := by rwa [mul_comm]
      field_simp
      ring
    · simp only [not_forall] at hunr
      obtain ⟨u, hu, hχu⟩ := hunr
      refine ⟨Polynomial.C (m.1 w) * A, M, zetaBound χ, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_ramified χ μ hu hχu] at h0
      have hT : ballZeta χ μ (fun _ => 1) s 0 = 0 :=
        (mul_eq_zero.1 h0).resolve_right (one_sub_ne_zero χ hs')
      have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
      rw [hZ, hA s hs', hT, (hL s).trans (ite_eq_right hn)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
  · by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · have hΦ0 : IsSchwartzBruhat K (((ordBall K 0).indicator fun _ => (1 : ℂ)) ∘ e) :=
        ⟨(isLocallyConstant_indicator (isOpen_ordBall 0) (isClosed_ordBall 0)
          (fun _ _ => Eventually.of_forall fun _ => rfl)).comp_continuous e.continuous,
          (HasCompactSupport.intro (isCompact_ordBall 0)
            (fun _ hy => Set.indicator_of_notMem hy _)).comp_homeomorph e⟩
      refine ⟨1, fun _ => ((ordBall K 0).indicator fun _ => (1 : ℂ)) ∘ e, fun _ => v,
        fun _ => ⟨l, hsm⟩, fun _ => Polynomial.C ((l v * (μ.real (ordShell K 0) : ℂ))⁻¹), 0,
        zetaBound χ, fun _ => hΦ0, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_unramified χ μ hunr] at h0
      have h1 := one_sub_ne_zero χ hs'
      rw [Fin.sum_univ_one, hZ, Function.comp_assoc, e.self_comp_symm, Function.comp_id,
        zeta_indicator_ordBall, (hL s).trans (ite_eq_left hunr)]
      simp only [Polynomial.eval_C, pow_zero, div_one]
      have hT : ballZeta χ μ (fun _ => 1) s 0 =
          (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
        rw [← h0, mul_div_cancel_right₀ _ h1]
      rw [hT]
      have := hl
      field_simp
    · simp only [not_forall] at hunr
      have hΦ1 : IsSchwartzBruhat K
          (((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) ∘ e) :=
        ⟨(isLocallyConstant_indicator (isOpen_ordShell 0) (isClosed_ordShell 0)
          (fun y hy => (eventually_extChar_eq χ hχ hy.1).mono fun z hz => by rw [hz])).comp_continuous
            e.continuous,
          (HasCompactSupport.intro (isCompact_ordShell 0)
            (fun _ hy => Set.indicator_of_notMem hy _)).comp_homeomorph e⟩
      refine ⟨1, fun _ => ((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) ∘ e, fun _ => v,
        fun _ => ⟨l, hsm⟩, fun _ => Polynomial.C ((l v * (μ.real (ordShell K 0) : ℂ))⁻¹), 0,
        zetaBound χ, fun _ => hΦ1, fun s hs => ?_⟩
      obtain ⟨u, hu, hχu⟩ := hunr
      have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
      rw [Fin.sum_univ_one, hZ, Function.comp_assoc, e.self_comp_symm, Function.comp_id,
        zeta_indicator_ordShell, (hL s).trans (ite_eq_right hn)]
      simp only [Polynomial.eval_C, pow_zero, div_one]
      have := hl
      field_simp

/-- `GL1LFactor` with the extra hypothesis that the space of $\pi$ is not zero. This is the form of Tate's local theory that `LocalLanglandsGL 1` uses. -/
def GL1LFactorNontrivial : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (π : SmoothRep (GL (Fin 1) K)), Nontrivial π.V →
        (∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) →
          IsGJLFactor K π (wdOfChar K art χ hχ).lFactor

/-- Tate's local theory for $GL_1$ holds for each nonzero representation. -/
theorem gl1LFactorNontrivial : GL1LFactorNontrivial.{u} :=
  fun _ _ _ _ _ _ hart χ hχ π _ hπ => isGJLFactor_wdOfChar hart χ hχ π hπ

end Main

section Final

/-- `GL1LFactor` is false: for the zero representation each zeta integral is $0$, so no finite combination of zeta integrals is the L-factor. -/
theorem not_gl1LFactor : ¬ GL1LFactor.{0} := by
  intro h
  obtain ⟨art, hart⟩ := exists_isLocalArtinMap ℚ_[2]
  have hχ : IsSmoothChar ℚ_[2] (1 : ℚ_[2]ˣ →* ℂˣ) := by
    unfold IsSmoothChar
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  let π : SmoothRep (GL (Fin 1) ℚ_[2]) :=
    { V := PUnit
      ρ := 1
      smooth := fun v => by
        have : (vecStabilizer (1 : Representation ℂ (GL (Fin 1) ℚ_[2]) PUnit) v :
            Set (GL (Fin 1) ℚ_[2])) = Set.univ :=
          Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
        rw [this]
        exact isOpen_univ }
  obtain ⟨-, -, j, Φ, v, l, A, k, s₀, -, hL⟩ :=
    h ℚ_[2] art hart 1 hχ π (fun _ _ => Subsingleton.elim _ _)
  have hz : ∀ i s, gjZeta ℚ_[2] π (Φ i) (v i) (l i) s = 0 := by
    intro i s
    have hc : ∀ g, π.coeff (v i) (l i) g = 0 := fun g => by
      rw [SmoothRep.coeff, Subsingleton.elim (π.ρ g (v i)) 0, map_zero]
    simp [gjZeta, hc]
  set s : ℂ := ((max s₀ 0 + 1 : ℝ) : ℂ)
  have hs : s₀ < s.re := by
    simp only [s, Complex.ofReal_re]
    linarith [le_max_left s₀ 0]
  have h0 := hL s hs
  simp only [hz, mul_zero, Finset.sum_const_zero] at h0
  have hq : (1 : ℝ) < residueCard ℚ_[2] := by exact_mod_cast one_lt_residueCard
  have hX : ‖(residueCard ℚ_[2] : ℂ) ^ (-s)‖ < 1 := by
    rw [show (residueCard ℚ_[2] : ℂ) = ((residueCard ℚ_[2] : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simp only [s, Complex.ofReal_re]; linarith [le_max_right s₀ 0])
  rw [lFactor_wdOfChar_eq ℚ_[2] art hart 1 hχ (unif ℚ_[2]) isUniformizer_unif s] at h0
  split_ifs at h0
  · simp only [MonoidHom.one_apply, Units.val_one, one_mul, inv_eq_zero] at h0
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hX
    exact lt_irrefl _ hX
  · exact one_ne_zero h0

/-- **The local Langlands correspondence for $GL_1$** over each nonarchimedean local field. -/
theorem localLanglandsGL_one : LocalLanglandsGL.{u} 1 := by
  intro K _ _ _ _ art hart
  refine ⟨recFamily K art, ?_⟩
  refine
    { gl1 := fun _ => rec1_gl1 K art
      map := fun
        | 0, _ => isLanglandsMap_rec0 K art
        | 1, _ =>
          { central := rec1_central K art
            twist := rec1_twist K art
            dual := rec1_dual K art
            lFactor := fun π ρ h => by
              have := π.2.1.1
              rw [eq_wdOfChar_of_rec1 K art h]
              exact isGJLFactor_wdOfChar hart _ _ π.1 (rho_irrChar K π) }
        | _ + 2, h => absurd h (by omega) }

end Final

end Langlands.LocalGL1
