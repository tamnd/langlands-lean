/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.PrincipalIrreducible

/-!
# The irreducibility criterion for principal series of $GL_2$

Let $K$ be a nonarchimedean local field, let $G = GL_2(K)$, and let $\chi_1, \chi_2$ be smooth characters of $K^\times$. This module proves that the normalized principal series of $(\chi_1, \chi_2)$ is irreducible if $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$. This is the criterion of Bushnell and Henniart, chapter 3, section 9.

## Main results

* `IsAffineStable.translate_sub_mem`: let $Y$ be a space of functions on $K$ that is stable under translations and dilations. If $Y$ contains a nonzero test function, then $Y$ contains each difference $\varphi(\cdot + y) - \varphi$ of test functions.
* `jacquetKer_le_of_inf_ne_bot`: if a $G$-stable subspace $W$ of $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ meets the big cell subspace $V_w$ in a nonzero function, then $W$ contains the kernel $V(N)$ of the Jacquet module.
* `eq_of_inf_principalSeriesBigCell_eq_bot`: if a nonzero $G$-stable subspace $W$ meets $V_w$ only in $0$, then $\chi_1 = \chi_2$.
* `eq_top_of_jacquetKer_le`: a nonzero $G$-stable subspace that contains $V(N)$ is the whole space, if `Langlands.bigCellChar` is not trivial on some $\mathrm{diag}(a, a^{-1})$.
* `principalSeriesInd_isIrreducible`: the unnormalized criterion.
* `normPrincipalSeries_irreducible`: the normalized criterion.
* `normPrincipalSeries_quotient_jacquet_nontrivial` and `normPrincipalSeries_hom_injective`: the two statements that `Langlands.Smooth.PrincipalIrreducible` lists as open. Both now follow.

## Method

A function of $V_w$ is determined by its restriction to the big cell $B w N$. This restriction is a test function on $K$, and the torus and $N$ act on it by dilations and translations. A nonzero $G$-stable subspace that meets $V_w$ thus contains all differences of translates, and these span $V(N) \cap V_w$. The Jacquet module $V_N$ has dimension $2$, and a torus element $\mathrm{diag}(a, a^{-1})$ with a nontrivial eigenvalue on $V_N$ moves the remaining vector into the subspace.

## Open parts

The structure of the reducible case, $\chi_1 \chi_2^{-1} = |\cdot|^{\pm 1}$, is not proved. In that case the principal series has length $2$, with a twist of the Steinberg representation and a character as its factors.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
-/

universe u

open Representation Matrix

namespace Langlands

section BallQuotients

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open ValuativeRel

/-- There is an element $\varpi$ of $K$ with $v(\varpi) = v(\varpi)$, the generator `uniformizer K` of the value group. -/
theorem exists_valuation_eq_uniformizer :
    ∃ π : K, π ≠ 0 ∧ valuation K π = uniformizer K := by
  have hu : uniformizer K ≠ 0 := uniformizer_ne_zero
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective (uniformizer K)
  refine ⟨π, fun h => hu ?_, hπ⟩
  rw [← hπ, h, map_zero]

/-- If $v(a) = v(\varpi)^k$, then $v(y a) \le v(\varpi)^m$ exactly when $v(y) \le v(\varpi)^{m - k}$. -/
theorem valuation_mul_le_zpow_iff {a : K} {k : ℤ} (ha : valuation K a = uniformizer K ^ k)
    (y : K) (m : ℤ) :
    valuation K (y * a) ≤ uniformizer K ^ m ↔ valuation K y ≤ uniformizer K ^ (m - k) := by
  have hu : uniformizer K ≠ 0 := uniformizer_ne_zero
  rw [map_mul, ha, show uniformizer K ^ m = uniformizer K ^ (m - k) * uniformizer K ^ k by
    rw [← zpow_add₀ hu, sub_add_cancel]]
  exact mul_le_mul_iff_of_pos_right (zpow_pos uniformizer_pos k)

/-- Multiplication by $a$ with $v(a) = v(\varpi)^k$ takes the ball of index $m - k$ onto the ball of index $m$. -/
theorem mul_mem_piBall_iff {a : K} {k : ℤ} (ha : valuation K a = uniformizer K ^ k)
    (y : K) (m : ℤ) : y * a ∈ piBall K m ↔ y ∈ piBall K (m - k) := by
  rw [mem_piBall, mem_piBall]
  exact valuation_mul_le_zpow_iff ha y m

variable (K) in
/-- The quotient $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ of two consecutive balls of $K$. It has $q$ elements. -/
abbrev BallQuot (n : ℤ) : Type u :=
  ↥(piBall K n) ⧸ (piBall K (n + 1)).addSubgroupOf (piBall K n)

/-- The quotient $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ is finite. -/
instance (n : ℤ) : Finite (BallQuot K n) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [← AddSubgroup.index_eq_card, ← AddSubgroup.relIndex, relIndex_piBall_add_one]
  exact (residueCard_pos K).ne'

/-- A choice of a finite type structure on $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$. -/
noncomputable instance (n : ℤ) : Fintype (BallQuot K n) := Fintype.ofFinite _

/-- The quotient $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ has $q$ elements. -/
theorem card_ballQuot (n : ℤ) : Fintype.card (BallQuot K n) = residueCard K := by
  rw [← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← AddSubgroup.relIndex,
    relIndex_piBall_add_one]

/-- The chosen representative in $\mathfrak{p}^n$ of a class of $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$. -/
noncomputable def ballRep {n : ℤ} (q : BallQuot K n) : K :=
  ((Quotient.out q : piBall K n) : K)

/-- The representative of a class of $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ is in $\mathfrak{p}^n$. -/
theorem ballRep_mem {n : ℤ} (q : BallQuot K n) : ballRep q ∈ piBall K n :=
  (Quotient.out q).2

/-- Two elements of $\mathfrak{p}^n$ have the same class exactly when their difference is in $\mathfrak{p}^{n + 1}$. -/
theorem ballQuot_mk_eq_iff {n : ℤ} (a b : piBall K n) :
    (QuotientAddGroup.mk a : BallQuot K n) = QuotientAddGroup.mk b ↔
      (b : K) - a ∈ piBall K (n + 1) := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
    AddSubgroup.coe_neg, neg_add_eq_sub]

/-- The class of the representative of $q$ is $q$. -/
theorem ballQuot_mk_ballRep {n : ℤ} (q : BallQuot K n) :
    (QuotientAddGroup.mk ⟨ballRep q, ballRep_mem q⟩ : BallQuot K n) = q :=
  QuotientAddGroup.out_eq' q

/-- The representative of the class of $a \in \mathfrak{p}^n$ differs from $a$ by an element of $\mathfrak{p}^{n + 1}$. -/
theorem ballRep_mk_sub_mem {n : ℤ} (a : piBall K n) :
    ballRep (QuotientAddGroup.mk a : BallQuot K n) - a ∈ piBall K (n + 1) :=
  (ballQuot_mk_eq_iff a ⟨_, ballRep_mem _⟩).1 (ballQuot_mk_ballRep _).symm

/-- A class of $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ is $0$ exactly when its representative is in $\mathfrak{p}^{n + 1}$. -/
theorem ballQuot_eq_zero_iff {n : ℤ} (q : BallQuot K n) :
    q = 0 ↔ ballRep q ∈ piBall K (n + 1) := by
  conv_lhs => rw [← ballQuot_mk_ballRep q]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

/-- Let $\psi$ be invariant under translation by $\mathfrak{p}^{n + 1}$, and let $f : \iota \to \mathfrak{p}^n$ give a bijection of $\iota$ with $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$. Then the sum of $\psi(x + f(i))$ over $\iota$ is the sum of $\psi(x + r)$ over the chosen representatives $r$. -/
theorem sum_ballQuot_of_bijective {n : ℤ} {ι : Type*} [Fintype ι] (f : ι → K)
    (hf : ∀ i, f i ∈ piBall K n)
    (hbij : Function.Bijective fun i => (QuotientAddGroup.mk ⟨f i, hf i⟩ : BallQuot K n))
    {ψ : K → ℂ} (hψ : ∀ x z, z ∈ piBall K (n + 1) → ψ (x + z) = ψ x) (x : K) :
    ∑ i, ψ (x + f i) = ∑ q : BallQuot K n, ψ (x + ballRep q) := by
  refine Fintype.sum_bijective _ hbij _ _ fun i => ?_
  rw [show x + ballRep (QuotientAddGroup.mk ⟨f i, hf i⟩ : BallQuot K n) =
    (x + f i) + (ballRep (QuotientAddGroup.mk ⟨f i, hf i⟩ : BallQuot K n) - f i) by ring,
    hψ _ _ (ballRep_mk_sub_mem _)]

/-- A map from $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ to itself that is injective is bijective. -/
theorem bijective_of_injective_ballQuot {n m : ℤ} {e : BallQuot K n → BallQuot K m}
    (he : Function.Injective e) : Function.Bijective e := by
  rw [Fintype.bijective_iff_injective_and_card, card_ballQuot, card_ballQuot]
  exact ⟨he, rfl⟩

/-- Translation by $z \in \mathfrak{p}^n$ permutes the classes: for $\psi$ invariant under $\mathfrak{p}^{n + 1}$, the sum of $\psi(x + z + r)$ over the representatives $r$ does not depend on $z$. -/
theorem sum_ballQuot_add {n : ℤ} {ψ : K → ℂ} (hψ : ∀ x z, z ∈ piBall K (n + 1) → ψ (x + z) = ψ x)
    {z : K} (hz : z ∈ piBall K n) (x : K) :
    ∑ q : BallQuot K n, ψ (x + (z + ballRep q)) = ∑ q : BallQuot K n, ψ (x + ballRep q) := by
  have hf : ∀ q : BallQuot K n, z + ballRep q ∈ piBall K n := fun q =>
    add_mem hz (ballRep_mem q)
  refine sum_ballQuot_of_bijective _ hf (bijective_of_injective_ballQuot fun q q' h => ?_) hψ x
  rw [ballQuot_mk_eq_iff] at h
  rw [← ballQuot_mk_ballRep q, ← ballQuot_mk_ballRep q', ballQuot_mk_eq_iff]
  simpa using h

/-- Multiplication by $c$ with $v(c) = v(\varpi)^k$ takes the classes of $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ to the classes of $\mathfrak{p}^m / \mathfrak{p}^{m + 1}$ for $m = n + k$. -/
theorem sum_ballQuot_mul {n m k : ℤ} (hm : m = n + k) {c : K}
    (hc : valuation K c = uniformizer K ^ k) {ψ : K → ℂ}
    (hψ : ∀ x z, z ∈ piBall K (m + 1) → ψ (x + z) = ψ x) (x : K) :
    ∑ q : BallQuot K n, ψ (x + c * ballRep q) = ∑ q : BallQuot K m, ψ (x + ballRep q) := by
  have hf : ∀ q : BallQuot K n, c * ballRep q ∈ piBall K m := fun q => by
    rw [mul_comm, mul_mem_piBall_iff hc, hm, add_sub_cancel_right]
    exact ballRep_mem q
  refine sum_ballQuot_of_bijective _ hf (bijective_of_injective_ballQuot fun q q' h => ?_) hψ x
  rw [ballQuot_mk_eq_iff] at h
  rw [← ballQuot_mk_ballRep q, ← ballQuot_mk_ballRep q', ballQuot_mk_eq_iff]
  have h' : (ballRep q' - ballRep q) * c ∈ piBall K (m + 1) := by
    simpa [mul_sub, mul_comm] using h
  rw [mul_mem_piBall_iff hc, hm, show n + k + 1 - k = n + 1 by ring] at h'
  exact h'

open Classical in
variable (K) in
/-- The indicator function of the ball $\mathfrak{p}^n = \{x : v(x) \le v(\varpi)^n\}$, with values in $\mathbb{C}$. -/
noncomputable def ballInd (n : ℤ) (x : K) : ℂ :=
  if x ∈ piBall K n then 1 else 0

/-- The indicator function of $\mathfrak{p}^n$ is $1$ on $\mathfrak{p}^n$. -/
theorem ballInd_of_mem {n : ℤ} {x : K} (h : x ∈ piBall K n) : ballInd K n x = 1 := by
  simp [ballInd, h]

/-- The indicator function of $\mathfrak{p}^n$ is $0$ outside $\mathfrak{p}^n$. -/
theorem ballInd_of_not_mem {n : ℤ} {x : K} (h : x ∉ piBall K n) : ballInd K n x = 0 := by
  simp [ballInd, h]

/-- The ball $\mathfrak{p}^n$ is the disjoint union of the $q$ balls $-r + \mathfrak{p}^{n + 1}$. -/
theorem sum_ballInd (n : ℤ) (x : K) :
    ∑ q : BallQuot K n, ballInd K (n + 1) (x + ballRep q) = ballInd K n x := by
  classical
  by_cases hx : x ∈ piBall K n
  · have key : ∀ q : BallQuot K n, ballInd K (n + 1) (x + ballRep q) =
        if q = QuotientAddGroup.mk ⟨-x, neg_mem hx⟩ then 1 else 0 := by
      intro q
      have : x + ballRep q ∈ piBall K (n + 1) ↔ q = QuotientAddGroup.mk ⟨-x, neg_mem hx⟩ := by
        rw [← ballQuot_mk_ballRep q, ballQuot_mk_eq_iff, ballQuot_mk_ballRep]
        constructor
        · intro h
          rw [← neg_mem_iff]
          simpa [add_comm] using h
        · intro h
          rw [← neg_mem_iff] at h
          simpa [add_comm] using h
      by_cases h : x + ballRep q ∈ piBall K (n + 1)
      · rw [ballInd_of_mem h]
        simp [this.1 h]
      · have hq : ¬ q = QuotientAddGroup.mk ⟨-x, neg_mem hx⟩ := fun h' => h (this.2 h')
        rw [ballInd_of_not_mem h]
        simp [hq]
    rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_ite_eq', ballInd_of_mem hx]
    simp
  · rw [ballInd_of_not_mem hx]
    refine Finset.sum_eq_zero fun q _ => ballInd_of_not_mem fun h => hx ?_
    have := sub_mem (piBall_antitone (by omega) h) (ballRep_mem q)
    simpa using this

/-- If $x \in \mathfrak{p}^a$ and $r \in \mathfrak{p}^b$, then $x r \in \mathfrak{p}^{a + b}$. -/
theorem mul_mem_piBall_add {a b : ℤ} {x r : K} (hx : x ∈ piBall K a) (hr : r ∈ piBall K b) :
    x * r ∈ piBall K (a + b) := by
  rw [mem_piBall] at *
  rw [map_mul, zpow_add₀ uniformizer_ne_zero]
  exact mul_le_mul' hx hr

/-- The ball $\mathfrak{p}^m$ is stable under multiplication by $\mathcal{O}_K = \mathfrak{p}^0$. -/
theorem mul_mem_piBall {m : ℤ} {x r : K} (hx : x ∈ piBall K m) (hr : r ∈ piBall K 0) :
    x * r ∈ piBall K m := by
  simpa using mul_mem_piBall_add hx hr

/-- If $v(a) = v(\varpi)^k$, then $x \mapsto 1_{\mathfrak{p}^m}(x a)$ is the indicator function of $\mathfrak{p}^{m - k}$. -/
theorem ballInd_mul {a : K} {k : ℤ} (ha : valuation K a = uniformizer K ^ k) (m : ℤ) :
    (fun x => ballInd K m (x * a)) = ballInd K (m - k) := by
  funext x
  by_cases h : x ∈ piBall K (m - k)
  · rw [ballInd_of_mem h, ballInd_of_mem ((mul_mem_piBall_iff ha x m).2 h)]
  · rw [ballInd_of_not_mem h, ballInd_of_not_mem fun h' => h ((mul_mem_piBall_iff ha x m).1 h')]

/-- The indicator function of $\mathfrak{p}^m$ is invariant under translation by $\mathfrak{p}^m$. -/
theorem ballInd_add {m : ℤ} (x : K) {z : K} (hz : z ∈ piBall K m) :
    ballInd K m (x + z) = ballInd K m x := by
  by_cases h : x ∈ piBall K m
  · rw [ballInd_of_mem h, ballInd_of_mem (add_mem h hz)]
  · rw [ballInd_of_not_mem h, ballInd_of_not_mem fun h' => h
      (((piBall K m).add_mem_cancel_right hz).1 h')]

/-- An element of $\mathfrak{p}^0$ that is not in $\mathfrak{p}^1$ has valuation $1$. -/
theorem valuation_eq_one_of_mem {r : K} (h0 : r ∈ piBall K 0) (h1 : r ∉ piBall K 1) :
    valuation K r = 1 := by
  rw [mem_piBall, zpow_zero] at h0
  rw [mem_piBall_one, not_lt] at h1
  exact le_antisymm h0 h1

end BallQuotients

section TestFunctions

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open ValuativeRel

variable (K) in
/-- A test function on $K$: a function that is invariant under translation by a ball $\mathfrak{p}^m$ and vanishes outside a ball $\mathfrak{p}^n$. -/
def IsTestFun (φ : K → ℂ) : Prop :=
  (∃ m : ℤ, ∀ x z, z ∈ piBall K m → φ (x + z) = φ x) ∧ ∃ n : ℤ, ∀ x, x ∉ piBall K n → φ x = 0

variable (K) in
/-- A subspace of functions on $K$ that is stable under the translations $\varphi \mapsto \varphi(\cdot + y)$ and the dilations $\varphi \mapsto \varphi(\cdot \, a)$ with $a \neq 0$. -/
def IsAffineStable (Y : Submodule ℂ (K → ℂ)) : Prop :=
  (∀ φ ∈ Y, ∀ y : K, (fun x => φ (x + y)) ∈ Y) ∧
    ∀ φ ∈ Y, ∀ a : K, a ≠ 0 → (fun x => φ (x * a)) ∈ Y

variable {Y : Submodule ℂ (K → ℂ)}

/-- A sum of translates by the representatives of $\mathfrak{p}^n / \mathfrak{p}^{n + 1}$ stays in a stable subspace. -/
theorem IsAffineStable.sum_mem (hY : IsAffineStable K Y) {φ : K → ℂ} (hφ : φ ∈ Y) (n : ℤ) :
    (fun x => ∑ q : BallQuot K n, φ (x + ballRep q)) ∈ Y := by
  have e : (fun x => ∑ q : BallQuot K n, φ (x + ballRep q)) =
      ∑ q : BallQuot K n, fun x => φ (x + ballRep q) := by
    funext x
    simp [Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun q _ => hY.1 φ hφ _

/-- Let $n \le -1$, and assume that $0$ is the only function of $Y$ that is invariant under $\mathcal{O}_K$ and vanishes outside $\mathfrak{p}^{n + 1}$. Then for $g \in Y$ invariant under $\mathcal{O}_K$ and $0$ outside $\mathfrak{p}^n$, the sum of $g$ over each coset of $\mathfrak{p}^{-1} / \mathcal{O}_K$ is $0$. -/
theorem IsAffineStable.sum_eq_zero_of_min (hY : IsAffineStable K Y) {n : ℤ} (hn : n ≤ -1)
    (hmin : ∀ h ∈ Y, (∀ x z, z ∈ piBall K 0 → h (x + z) = h x) →
      (∀ x, x ∉ piBall K (n + 1) → h x = 0) → h = 0)
    {g : K → ℂ} (hg : g ∈ Y) (hO : ∀ x z, z ∈ piBall K 0 → g (x + z) = g x)
    (hS : ∀ x, x ∉ piBall K n → g x = 0) (x : K) :
    ∑ q : BallQuot K (-1), g (x + ballRep q) = 0 := by
  obtain ⟨π, hπ0, hπ⟩ := exists_valuation_eq_uniformizer (K := K)
  set T : K → ℂ := fun x => ∑ q : BallQuot K (-1), g (x + ballRep q) with hT
  have hTY : T ∈ Y := hY.sum_mem hg (-1)
  have hgO : ∀ x z, z ∈ piBall K (-1 + 1) → g (x + z) = g x := fun x z hz =>
    hO x z (by simpa using hz)
  have hTinv : ∀ y w, w ∈ piBall K (-1) → T (y + w) = T y := by
    intro y w hw
    simp only [hT]
    rw [← sum_ballQuot_add hgO hw y]
    simp only [add_assoc]
  have hπi : valuation K π⁻¹ = uniformizer K ^ (-1 : ℤ) := by
    rw [map_inv₀, hπ, _root_.zpow_neg_one]
  have hTS : ∀ y, y ∉ piBall K n → T y = 0 := by
    intro y hy
    refine Finset.sum_eq_zero fun q _ => hS _ fun h => hy ?_
    have := sub_mem h (piBall_antitone hn (ballRep_mem q))
    simpa using this
  have hh := hmin (fun y => T (y * π⁻¹)) (hY.2 T hTY _ (inv_ne_zero hπ0))
    (fun y z hz => by
      simp only [add_mul]
      refine hTinv _ _ ?_
      rw [mul_mem_piBall_iff hπi]
      simpa using hz)
    (fun y hy => by
      refine hTS _ fun h => hy ?_
      rw [mul_mem_piBall_iff hπi] at h
      simpa using h)
  have h1 := congrFun hh (x * π)
  simp only [mul_assoc, mul_inv_cancel₀ hπ0, mul_one, Pi.zero_apply] at h1
  exact h1

/-- Let $n \le -2$, and assume that $0$ is the only function of $Y$ that is invariant under $\mathcal{O}_K$ and vanishes outside $\mathfrak{p}^{n + 1}$. Then $0$ is also the only function of $Y$ that is invariant under $\mathcal{O}_K$ and vanishes outside $\mathfrak{p}^n$. The proof averages the dilations by $1 + \varpi^{-n - 1} r$ with $r \in \mathcal{O}_K / \mathfrak{p}$. -/
theorem IsAffineStable.eq_zero_of_min (hY : IsAffineStable K Y) {n : ℤ} (hn : n ≤ -2)
    (hmin : ∀ h ∈ Y, (∀ x z, z ∈ piBall K 0 → h (x + z) = h x) →
      (∀ x, x ∉ piBall K (n + 1) → h x = 0) → h = 0)
    {g : K → ℂ} (hg : g ∈ Y) (hO : ∀ x z, z ∈ piBall K 0 → g (x + z) = g x)
    (hS : ∀ x, x ∉ piBall K n → g x = 0) : g = 0 := by
  classical
  obtain ⟨π, hπ0, hπ⟩ := exists_valuation_eq_uniformizer (K := K)
  funext y
  by_cases hy : y ∈ piBall K n
  swap
  · exact hS y hy
  set g' : K → ℂ := fun x => g (x + y) with hg'_def
  have hg' : g' ∈ Y := hY.1 g hg y
  have hO' : ∀ x z, z ∈ piBall K 0 → g' (x + z) = g' x := fun x z hz => by
    simp only [hg'_def, add_right_comm x z y]
    exact hO _ _ hz
  have hS' : ∀ x, x ∉ piBall K n → g' x = 0 := fun x hx =>
    hS _ fun h => hx (by simpa using sub_mem h hy)
  set c₀ : K := π ^ (-n - 1) with hc₀_def
  have hc₀ : valuation K c₀ = uniformizer K ^ (-n - 1) := by
    rw [hc₀_def, map_zpow₀, hπ]
  have hval : ∀ q : BallQuot K 0, valuation K (c₀ * ballRep q) < 1 := fun q => by
    rw [← mem_piBall_one]
    refine piBall_antitone (show (1 : ℤ) ≤ -n - 1 by omega) ?_
    rw [mul_comm, mul_mem_piBall_iff hc₀, sub_self]
    exact ballRep_mem q
  have hunit : ∀ q : BallQuot K 0, valuation K (1 + c₀ * ballRep q) = 1 := fun q =>
    Valuation.map_one_add_of_lt _ (hval q)
  have hne : ∀ q : BallQuot K 0, 1 + c₀ * ballRep q ≠ 0 := fun q h => by
    have := hunit q
    rw [h, map_zero] at this
    exact zero_ne_one this
  set A : K → ℂ := fun x => ∑ q : BallQuot K 0, g' (x * (1 + c₀ * ballRep q)) with hA_def
  have hAY : A ∈ Y := by
    have e : A = ∑ q : BallQuot K 0, fun x => g' (x * (1 + c₀ * ballRep q)) := by
      funext x
      simp [hA_def, Finset.sum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun q _ => hY.2 _ hg' _ (hne q)
  have hq : (residueCard K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (residueCard_pos K).ne'
  have hA : ∀ x, A x = if x ∈ piBall K (n + 1) then (residueCard K : ℂ) * g' x else 0 := by
    intro x
    by_cases hx : x ∈ piBall K (n + 1)
    · simp only [hx, ↓reduceIte]
      have e : ∀ q : BallQuot K 0, g' (x * (1 + c₀ * ballRep q)) = g' x := fun q => by
        rw [mul_add, mul_one]
        refine hO' x _ ?_
        rw [← mul_assoc, mul_comm x c₀, mul_assoc, mul_comm]
        rw [mul_mem_piBall_iff hc₀, show (0 : ℤ) - (-n - 1) = n + 1 by ring]
        exact mul_mem_piBall hx (ballRep_mem q)
      simp only [hA_def, e, Finset.sum_const, Finset.card_univ, card_ballQuot, nsmul_eq_mul]
    · simp only [hx, ↓reduceIte]
      by_cases hxn : x ∈ piBall K n
      · have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
        obtain ⟨j, hj⟩ := exists_valuation_eq_zpow hx0
        have hjn : j = n := by
          rw [mem_piBall, hj, uniformizer_zpow_le_iff] at hxn hx
          omega
        have hc : valuation K (x * c₀) = uniformizer K ^ (-1 : ℤ) := by
          rw [map_mul, hj, hc₀, hjn, ← zpow_add₀ uniformizer_ne_zero]
          congr 1
          ring
        have e := sum_ballQuot_mul (n := 0) (m := -1) (k := -1) (by norm_num) hc (ψ := g')
          (fun x z hz => hO' x z (by simpa using hz)) x
        have e2 : A x = ∑ q : BallQuot K 0, g' (x + x * c₀ * ballRep q) :=
          Finset.sum_congr rfl fun q _ => by congr 1; ring
        rw [e2, e]
        exact hY.sum_eq_zero_of_min (by omega) hmin hg' hO' hS' x
      · refine Finset.sum_eq_zero fun q _ => hS' _ fun h => hxn ?_
        rw [mem_piBall, map_mul, hunit q, mul_one] at h
        exact h
  have hAO : ∀ x z, z ∈ piBall K 0 → A (x + z) = A x := by
    intro x z hz
    have hz' : z ∈ piBall K (n + 1) := piBall_antitone (by omega) hz
    rw [hA, hA, hO' x z hz]
    simp only [(piBall K (n + 1)).add_mem_cancel_right hz']
  have hAS : ∀ x, x ∉ piBall K (n + 1) → A x = 0 := fun x hx => by
    rw [hA]
    simp only [hx, ↓reduceIte]
  have h0 := congrFun (hmin A hAY hAO hAS) 0
  rw [hA] at h0
  simp only [zero_mem, ↓reduceIte] at h0
  have := (mul_eq_zero.1 h0).resolve_left hq
  simpa [hg'_def] using this

/-- Assume that $0$ is the only function of $Y$ that is invariant under $\mathcal{O}_K$ and vanishes outside $\mathcal{O}_K$, and let $g \neq 0$ in $Y$ be invariant under $\mathcal{O}_K$ and $0$ outside $\mathfrak{p}^{-1}$. Then $1_{\mathcal{O}_K} - q^{-1} 1_{\mathfrak{p}^{-1}}$ is in $Y$. The proof averages the dilations by the units of $\mathcal{O}_K / \mathfrak{p}$. -/
theorem IsAffineStable.ballInd_sub_mem_of_one (hY : IsAffineStable K Y)
    (hmin : ∀ h ∈ Y, (∀ x z, z ∈ piBall K 0 → h (x + z) = h x) →
      (∀ x, x ∉ piBall K 0 → h x = 0) → h = 0)
    {g : K → ℂ} (hg : g ∈ Y) (hO : ∀ x z, z ∈ piBall K 0 → g (x + z) = g x)
    (hS : ∀ x, x ∉ piBall K (-1) → g x = 0) (hg0 : g ≠ 0) :
    ballInd K 0 - (residueCard K : ℂ)⁻¹ • ballInd K (-1) ∈ Y := by
  classical
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  set h : K → ℂ := fun x => g (x + y) with hh_def
  have hhY : h ∈ Y := hY.1 g hg y
  have hO' : ∀ x z, z ∈ piBall K 0 → h (x + z) = h x := fun x z hz => by
    simp only [hh_def, add_right_comm x z y]
    exact hO _ _ hz
  have hy' : y ∈ piBall K (-1) := by
    by_contra hy'
    exact hy (hS y hy')
  have hS' : ∀ x, x ∉ piBall K (-1) → h x = 0 := fun x hx =>
    hS _ fun h' => hx (by simpa using sub_mem h' hy')
  have hh0 : h 0 ≠ 0 := by simpa [hh_def] using hy
  have hsum : ∀ x, ∑ q : BallQuot K (-1), h (x + ballRep q) = 0 :=
    hY.sum_eq_zero_of_min (n := -1) le_rfl (fun h' hh' hO'' hS'' => hmin h' hh' hO''
      (by simpa using hS'')) hhY hO' hS'
  have hrep : ∀ q : BallQuot K 0, q ≠ 0 → valuation K (ballRep q) = 1 := fun q hq =>
    valuation_eq_one_of_mem (ballRep_mem q) fun h1 => hq ((ballQuot_eq_zero_iff q).2
      (by simpa using h1))
  set G : K → ℂ := fun x => ∑ q ∈ Finset.univ.erase (0 : BallQuot K 0), h (x * ballRep q)
    with hG_def
  have hGY : G ∈ Y := by
    have e : G = ∑ q ∈ Finset.univ.erase (0 : BallQuot K 0), fun x => h (x * ballRep q) := by
      funext x
      simp [hG_def, Finset.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun q hq => hY.2 _ hhY _ fun h0 => ?_
    have := hrep q (Finset.ne_of_mem_erase hq)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hq : (residueCard K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (residueCard_pos K).ne'
  have hG : ∀ x, G x = h 0 * ((residueCard K : ℂ) * ballInd K 0 x - ballInd K (-1) x) := by
    intro x
    have hsplit : G x = ∑ q : BallQuot K 0, h (x * ballRep q) - h (x * ballRep 0) :=
      Finset.sum_erase_eq_sub (Finset.mem_univ _)
    have h00 : x ∈ piBall K (-1) → h (x * ballRep (0 : BallQuot K 0)) = h 0 := fun hx => by
      have hr : ballRep (0 : BallQuot K 0) ∈ piBall K 1 := by
        simpa using (ballQuot_eq_zero_iff (0 : BallQuot K 0)).1 rfl
      have := mul_mem_piBall_add hx hr
      rw [← zero_add (x * _)]
      exact hO' 0 _ (by simpa using this)
    by_cases hx0 : x ∈ piBall K 0
    · have hx1 : x ∈ piBall K (-1) := piBall_antitone (by norm_num) hx0
      have e : ∀ q : BallQuot K 0, h (x * ballRep q) = h 0 := fun q => by
        rw [← zero_add (x * _)]
        exact hO' 0 _ (mul_mem_piBall hx0 (ballRep_mem q))
      rw [hsplit, h00 hx1]
      simp only [e, Finset.sum_const, Finset.card_univ, card_ballQuot, nsmul_eq_mul,
        ballInd_of_mem hx0, ballInd_of_mem hx1]
      ring
    · by_cases hx1 : x ∈ piBall K (-1)
      · have hx : x ≠ 0 := fun h' => hx0 (h' ▸ zero_mem _)
        obtain ⟨j, hj⟩ := exists_valuation_eq_zpow hx
        have hj1 : j = -1 := by
          rw [mem_piBall, hj, uniformizer_zpow_le_iff] at hx0 hx1
          omega
        rw [hj1] at hj
        have e := sum_ballQuot_mul (n := 0) (m := -1) (k := -1) (by norm_num) hj (ψ := h)
          (fun x z hz => hO' x z (by simpa using hz)) 0
        have hs0 := hsum 0
        simp only [zero_add] at e hs0
        rw [hsplit, h00 hx1, e, hs0, ballInd_of_not_mem hx0, ballInd_of_mem hx1]
        ring
      · have e : G x = 0 := Finset.sum_eq_zero fun q hq => hS' _ fun h' => hx1 (mem_piBall.2
          (by simpa [map_mul, hrep q (Finset.ne_of_mem_erase hq)] using mem_piBall.1 h'))
        rw [e, ballInd_of_not_mem hx0, ballInd_of_not_mem hx1]
        ring
  have e : ballInd K 0 - (residueCard K : ℂ)⁻¹ • ballInd K (-1) =
      ((residueCard K : ℂ) * h 0)⁻¹ • G := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hG]
    field_simp
  rw [e]
  exact Y.smul_mem _ hGY

/-- If $1_{\mathcal{O}_K} - \alpha 1_{\mathfrak{p}^{-1}}$ is in $Y$ for some $\alpha$, then each function $x \mapsto 1_{\mathfrak{p}^n}(x + c) - 1_{\mathfrak{p}^n}(x)$ is in $Y$. The dilations give $1_{\mathfrak{p}^n} - \alpha 1_{\mathfrak{p}^{n - 1}}$, a telescoping sum gives $1_{\mathfrak{p}^n} - \alpha^k 1_{\mathfrak{p}^{n - k}}$, and translation by $c \in \mathfrak{p}^{n - k}$ fixes the second term. -/
theorem IsAffineStable.ballInd_translate_sub_mem (hY : IsAffineStable K Y) {α : ℂ}
    (hα : ballInd K 0 - α • ballInd K (-1) ∈ Y) (n : ℤ) (c : K) :
    (fun x => ballInd K n (x + c) - ballInd K n x) ∈ Y := by
  obtain ⟨π, hπ0, hπ⟩ := exists_valuation_eq_uniformizer (K := K)
  have hdil : ∀ m : ℤ, ballInd K m - α • ballInd K (m - 1) ∈ Y := by
    intro m
    have ha : valuation K (π ^ (-m)) = uniformizer K ^ (-m) := by rw [map_zpow₀, hπ]
    have h := hY.2 _ hα (π ^ (-m)) (zpow_ne_zero _ hπ0)
    have e : (fun x => (ballInd K 0 - α • ballInd K (-1)) (x * π ^ (-m))) =
        ballInd K m - α • ballInd K (m - 1) := by
      have e1 := ballInd_mul ha 0
      have e2 := ballInd_mul ha (-1)
      rw [show (0 : ℤ) - -m = m by ring] at e1
      rw [show (-1 : ℤ) - -m = m - 1 by ring] at e2
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, ← congrFun e1 x, ← congrFun e2 x]
    rwa [e] at h
  have htel : ∀ (k : ℕ) (m : ℤ), ballInd K m - α ^ k • ballInd K (m - k) ∈ Y := by
    intro k
    induction k with
    | zero =>
      intro m
      simp
    | succ k ih =>
      intro m
      have e : ballInd K m - α ^ (k + 1) • ballInd K (m - ((k + 1 : ℕ) : ℤ)) =
          (ballInd K m - α ^ k • ballInd K (m - k)) +
            α ^ k • (ballInd K (m - k) - α • ballInd K (m - k - 1)) := by
        rw [show m - ((k + 1 : ℕ) : ℤ) = m - k - 1 by push_cast; ring]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
        ring
      rw [e]
      exact Y.add_mem (ih m) (Y.smul_mem _ (hdil (m - k)))
  by_cases hc : c = 0
  · subst hc
    simp only [add_zero, sub_self]
    exact Y.zero_mem
  obtain ⟨j, hj⟩ := exists_valuation_eq_zpow hc
  set k := (n - j).toNat
  have hck : c ∈ piBall K (n - k) := by
    rw [mem_piBall, hj, uniformizer_zpow_le_iff]
    omega
  have h := Y.sub_mem (hY.1 _ (htel k n) c) (htel k n)
  have e : (fun x => (ballInd K n - α ^ k • ballInd K (n - k)) (x + c)) -
      (ballInd K n - α ^ k • ballInd K (n - k)) =
      fun x => ballInd K n (x + c) - ballInd K n x := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ballInd_add x hck]
    ring
  rwa [e] at h

/-- If all the functions $x \mapsto 1_{\mathfrak{p}^n}(x + c) - 1_{\mathfrak{p}^n}(x)$ are in $Y$, then $\varphi(\cdot + y) - \varphi$ is in $Y$ for each function $\varphi$ that is invariant under $\mathfrak{p}^m$ and vanishes outside $\mathfrak{p}^{m - k}$. The proof is by induction on $k$: write $\varphi$ as the sum of its restrictions to the $q$ cosets of $\mathfrak{p}^{m - k}$ in $\mathfrak{p}^{m - k - 1}$. -/
theorem IsAffineStable.translate_sub_mem_of_ballInd (hY : IsAffineStable K Y)
    (he : ∀ (n : ℤ) (c : K), (fun x => ballInd K n (x + c) - ballInd K n x) ∈ Y) (k : ℕ) :
    ∀ (m : ℤ) (φ : K → ℂ), (∀ x z, z ∈ piBall K m → φ (x + z) = φ x) →
      (∀ x, x ∉ piBall K (m - k) → φ x = 0) → ∀ y, (fun x => φ (x + y)) - φ ∈ Y := by
  induction k with
  | zero =>
    intro m φ hinv hsupp y
    have hφ : ∀ x, φ x = φ 0 * ballInd K m x := by
      intro x
      by_cases hx : x ∈ piBall K m
      · rw [show ballInd K m x = 1 by simp [ballInd, hx], mul_one, ← zero_add x]
        exact hinv 0 x hx
      · rw [show ballInd K m x = 0 by simp [ballInd, hx], mul_zero]
        exact hsupp x (by simpa using hx)
    have e : (fun x => φ (x + y)) - φ = φ 0 • fun x => ballInd K m (x + y) - ballInd K m x := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hφ (x + y), hφ x]
      ring
    rw [e]
    exact Y.smul_mem _ (he m y)
  | succ k ih =>
    intro m φ hinv hsupp y
    set n := m - ((k + 1 : ℕ) : ℤ) with hn
    have hn1 : n + 1 = m - k := by rw [hn]; push_cast; ring
    let θ : BallQuot K n → K → ℂ := fun q w => φ (w - ballRep q) * ballInd K (n + 1) w
    have hθ : ∀ q, (fun x => θ q (x + y)) - θ q ∈ Y := by
      intro q
      refine ih m (θ q) (fun x z hz => ?_) (fun x hx => ?_) y
      · have hz' : z ∈ piBall K (n + 1) := piBall_antitone (by omega) hz
        simp only [θ, ballInd_add x hz', show x + z - ballRep q = (x - ballRep q) + z by ring,
          hinv _ _ hz]
      · simp only [θ]
        rw [show ballInd K (n + 1) x = 0 by simp [ballInd, hn1, hx], mul_zero]
    have hsum := hY.sum_mem (Y.sub_mem (hY.1 _ (hθ 0) 0) (hθ 0)) n
    have hmem : (fun x => ∑ q : BallQuot K n, ((fun x => θ q (x + y)) - θ q) (x + ballRep q)) ∈
        Y := by
      have e : (fun x => ∑ q : BallQuot K n, ((fun x => θ q (x + y)) - θ q) (x + ballRep q)) =
          ∑ q : BallQuot K n, fun x => ((fun x => θ q (x + y)) - θ q) (x + ballRep q) := by
        funext x
        simp [Finset.sum_apply]
      rw [e]
      exact Submodule.sum_mem _ fun q _ => hY.1 _ (hθ q) _
    clear hsum
    have hφn : ∀ w, φ w * ballInd K n w = φ w := by
      intro w
      by_cases hw : w ∈ piBall K n
      · simp [ballInd, hw]
      · rw [hsupp w hw, zero_mul]
    have e : (fun x => φ (x + y)) - φ =
        fun x => ∑ q : BallQuot K n, ((fun x => θ q (x + y)) - θ q) (x + ballRep q) := by
      funext x
      simp only [Pi.sub_apply, θ, Finset.sum_sub_distrib, add_sub_cancel_right,
        ← Finset.mul_sum, show ∀ q : BallQuot K n, x + ballRep q + y = (x + y) + ballRep q from
          fun q => by ring, sum_ballInd, hφn]
    rw [e]
    exact hmem

/-- Let $Y$ be a space of functions on $K$ that is stable under translations and dilations and contains a nonzero test function. Then $\varphi(\cdot + y) - \varphi$ is in $Y$ for each test function $\varphi$ and each $y \in K$. -/
theorem IsAffineStable.translate_sub_mem (hY : IsAffineStable K Y)
    (h0 : ∃ φ ∈ Y, φ ≠ 0 ∧ IsTestFun K φ) {φ : K → ℂ} (hφ : IsTestFun K φ) (y : K) :
    (fun x => φ (x + y)) - φ ∈ Y := by
  classical
  obtain ⟨π, hπ0, hπ⟩ := exists_valuation_eq_uniformizer (K := K)
  -- a nonzero function of `Y` that is invariant under `𝒪` and vanishes outside a ball
  have hP : ∃ R : ℕ, ∃ g ∈ Y, g ≠ 0 ∧ (∀ x z, z ∈ piBall K 0 → g (x + z) = g x) ∧
      ∀ x, x ∉ piBall K (-(R : ℤ)) → g x = 0 := by
    obtain ⟨φ₀, hφ₀Y, hφ₀, ⟨m, hm⟩, ⟨n, hn⟩⟩ := h0
    have ha : valuation K (π ^ m) = uniformizer K ^ m := by rw [map_zpow₀, hπ]
    have ha0 : π ^ m ≠ 0 := zpow_ne_zero _ hπ0
    refine ⟨(m - n).toNat, fun x => φ₀ (x * π ^ m), hY.2 _ hφ₀Y _ ha0, fun h => hφ₀ ?_,
      fun x z hz => ?_, fun x hx => hn _ fun h => hx ?_⟩
    · funext x
      have := congrFun h (x * (π ^ m)⁻¹)
      simpa [mul_assoc, inv_mul_cancel₀ ha0] using this
    · show φ₀ ((x + z) * π ^ m) = φ₀ (x * π ^ m)
      rw [add_mul]
      refine hm _ _ ?_
      rw [mul_mem_piBall_iff ha, sub_self]
      exact hz
    · rw [mul_mem_piBall_iff ha] at h
      exact piBall_antitone (by omega) h
  -- the minimal radius
  set R₀ := Nat.find hP with hR₀
  obtain ⟨g₀, hg₀Y, hg₀, hg₀O, hg₀S⟩ := Nat.find_spec hP
  have hmin : ∀ R < R₀, ∀ h ∈ Y, (∀ x z, z ∈ piBall K 0 → h (x + z) = h x) →
      (∀ x, x ∉ piBall K (-(R : ℤ)) → h x = 0) → h = 0 := by
    intro R hR h hh hO hS
    by_contra hne
    exact Nat.find_min hP hR ⟨h, hh, hne, hO, hS⟩
  have hF : ∃ α : ℂ, ballInd K 0 - α • ballInd K (-1) ∈ Y := by
    have hS0 : ∀ x, x ∉ piBall K (-(R₀ : ℤ)) → g₀ x = 0 := hg₀S
    rcases Nat.lt_or_ge R₀ 2 with hR | hR
    · obtain hR₀' | hR₀' : R₀ = 0 ∨ R₀ = 1 := by omega
      · -- radius `0`
        rw [hR₀'] at hS0
        have hS : ∀ x, x ∉ piBall K 0 → g₀ x = 0 := fun x hx => hS0 x (by simpa using hx)
        have hφ : ∀ x, g₀ x = g₀ 0 * ballInd K 0 x := by
          intro x
          by_cases hx : x ∈ piBall K 0
          · rw [show ballInd K 0 x = 1 by simp [ballInd, hx], mul_one, ← zero_add x]
            exact hg₀O 0 x hx
          · rw [show ballInd K 0 x = 0 by simp [ballInd, hx], mul_zero]
            exact hS x hx
        have h00 : g₀ 0 ≠ 0 := fun h => hg₀ (funext fun x => by rw [hφ x, h, zero_mul]; rfl)
        refine ⟨0, ?_⟩
        have e : ballInd K 0 - (0 : ℂ) • ballInd K (-1) = (g₀ 0)⁻¹ • g₀ := by
          funext x
          simp only [zero_smul, sub_zero, Pi.smul_apply, smul_eq_mul, hφ x]
          field_simp
        rw [e]
        exact Y.smul_mem _ hg₀Y
      · -- radius `1`
        rw [hR₀'] at hS0
        refine ⟨_, hY.ballInd_sub_mem_of_one (fun h hh hO hS => hmin 0 (by omega) h hh hO
          (by simpa using hS)) hg₀Y hg₀O (fun x hx => hS0 x (by simpa using hx)) hg₀⟩
    · exfalso
      refine hg₀ (hY.eq_zero_of_min (n := -(R₀ : ℤ)) (by omega) (fun h hh hO hS => ?_) hg₀Y
        hg₀O hg₀S)
      refine hmin (R₀ - 1) (by omega) h hh hO fun x hx => hS x ?_
      rwa [show -(R₀ : ℤ) + 1 = -((R₀ - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : 1 ≤ R₀)]; ring]
  obtain ⟨α, hα⟩ := hF
  have he := hY.ballInd_translate_sub_mem hα
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hφ
  refine hY.translate_sub_mem_of_ballInd he (max m n - n).toNat (max m n) φ
    (fun x z hz => hm x z (piBall_antitone (le_max_left m n) hz)) (fun x hx => hn x ?_) y
  rwa [show max m n - ((max m n - n).toNat : ℤ) = n by omega] at hx

end TestFunctions

section Unipotent

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The matrix $\mathrm{diag}(a, a^{-1})$ is the product $n(a) \bar n(-a^{-1}) n(a) \cdot n(-1) \bar n(1) n(-1)$ of upper and lower unipotent matrices. -/
theorem diagTorus_eq_unip_mul (a : Kˣ) :
    ((diagTorus K a a⁻¹ : torus K) : GL (Fin 2) K) =
      unip (a : K) * lowerUnip (-(a : K)⁻¹) * unip (a : K) *
        (unip (-1) * lowerUnip 1 * unip (-1)) := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  apply Units.ext
  change !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] =
    !![1, (a : K); 0, 1] * !![1, 0; -(a : K)⁻¹, 1] * !![1, (a : K); 0, 1] *
      (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -1; 0, 1])
  simp only [Matrix.mul_fin_two, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- For $G$-stable subspaces $W$ and $U$ of a representation of $GL_2(K)$, the subgroup of the elements $g$ with $g v - v \in U$ for each $v \in W$. -/
def relStab (π : SmoothRep (GL (Fin 2) K)) (W U : Submodule ℂ π.V)
    (hW : IsStableSubspace π.ρ W) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∀ v ∈ W, π.ρ g v - v ∈ U}
  mul_mem' {g h} hg hh v hv := by
    have e : π.ρ (g * h) v - v = (π.ρ g (π.ρ h v) - π.ρ h v) + (π.ρ h v - v) := by
      rw [map_mul, Module.End.mul_apply]
      abel
    rw [e]
    exact U.add_mem (hg _ (hW h hv)) (hh v hv)
  one_mem' v _ := by simp
  inv_mem' {g} hg v hv := by
    have e : π.ρ g⁻¹ v - v = -(π.ρ g (π.ρ g⁻¹ v) - π.ρ g⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      abel
    rw [e]
    exact U.neg_mem (hg _ (hW g⁻¹ hv))

/-- Membership in `relStab`. -/
theorem mem_relStab {π : SmoothRep (GL (Fin 2) K)} {W U : Submodule ℂ π.V}
    {hW : IsStableSubspace π.ρ W} {g : GL (Fin 2) K} :
    g ∈ relStab π W U hW ↔ ∀ v ∈ W, π.ρ g v - v ∈ U :=
  Iff.rfl

/-- If the subgroup `relStab` contains each upper unipotent matrix $n(x)$, then it contains each matrix $\mathrm{diag}(a, a^{-1})$. Conjugation by the Weyl element $w$ keeps `relStab`, so it contains the lower unipotent matrices $\bar n(x) = w n(x) w$. -/
theorem diagTorus_mem_relStab {π : SmoothRep (GL (Fin 2) K)} {W U : Submodule ℂ π.V}
    (hW : IsStableSubspace π.ρ W) (hU : IsStableSubspace π.ρ U)
    (h : ∀ x : K, unip x ∈ relStab π W U hW) (a : Kˣ) :
    ((diagTorus K a a⁻¹ : torus K) : GL (Fin 2) K) ∈ relStab π W U hW := by
  have hconj : ∀ g ∈ relStab π W U hW, weyl * g * weyl ∈ relStab π W U hW := by
    intro g hg v hv
    have hw : π.ρ weyl (π.ρ weyl v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, weyl_mul_weyl, map_one, Module.End.one_apply]
    have e : π.ρ (weyl * g * weyl) v - v = π.ρ weyl (π.ρ g (π.ρ weyl v) - π.ρ weyl v) := by
      rw [map_sub, hw, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    rw [e]
    exact hU weyl (hg _ (hW weyl hv))
  have hl : ∀ x : K, lowerUnip x ∈ relStab π W U hW := fun x => by
    rw [← weyl_mul_unip_mul_weyl]
    exact hconj _ (h x)
  rw [diagTorus_eq_unip_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (h _) (hl _)) (h _))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (h _) (hl _)) (h _))

end Unipotent

section Representation

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 ValuativeRel

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

local notation "Vw" => principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂

local notation "Ww" => bigCellJacquetKer χ₁ χ₂ hχ₁ hχ₂

/-- For $f \in V_w$ the function $\varphi_f$ is a test function: it is invariant under a ball, because $f$ is smooth, and it vanishes outside a ball. -/
theorem isTestFun_bigCellFun {f : (Ψ).V} (hf : f ∈ Vw) : IsTestFun K (bigCellFun f) := by
  refine ⟨?_, ?_⟩
  · have hO : IsOpen (unip ⁻¹' (vecStabilizer (Ψ).ρ f : Set (GL (Fin 2) K))) :=
      continuous_unip.isOpen_preimage _ ((Ψ).smooth f)
    have h0 : (0 : K) ∈ unip ⁻¹' (vecStabilizer (Ψ).ρ f : Set (GL (Fin 2) K)) := by
      rw [Set.mem_preimage, unip_zero]
      exact (vecStabilizer _ _).one_mem
    obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.1 (hO.mem_nhds h0)
    obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using hc.symm)
    obtain ⟨m, hm⟩ := exists_valuation_eq_zpow hc0
    refine ⟨m + 1, fun x z hz => ?_⟩
    have hz' : unip z ∈ vecStabilizer (Ψ).ρ f := by
      refine hγ (show valuation K (z - 0) < γ from ?_)
      rw [sub_zero, ← hc, hm, lt_uniformizer_zpow_iff]
      exact hz
    rw [mem_vecStabilizer] at hz'
    rw [← bigCellFun_ρ_unip, hz']
  · obtain ⟨n, hn⟩ := bigCellFun_eventually_zero hf
    exact ⟨n, fun x hx => hn x (not_le.1 fun h => hx (mem_piBall.2 h))⟩

/-- Let $W$ be a $G$-stable subspace of the principal series. The functions $\varphi_f$ with $f \in W \cap V_w$ form a space that is stable under translations and dilations. -/
theorem isAffineStable_bigCellFun {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W) :
    IsAffineStable K ((W ⊓ Vw).map bigCellFun) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩ y
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.1 hf
    refine ⟨(Ψ).ρ (unip y) f, Submodule.mem_inf.2 ⟨hW _ hf1,
      ρ_mem_principalSeriesBigCell hf2 (unipotent_le_borel (unip_mem y))⟩, ?_⟩
    funext x
    exact bigCellFun_ρ_unip f x y
  · rintro _ ⟨f, hf, rfl⟩ a ha
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.1 hf
    set t : torus K := diagTorus K 1 (Units.mk0 a ha)
    have h11 : (t : GL (Fin 2) K).1 1 1 = a := by simp [t, diagTorus]
    have h00 : (t : GL (Fin 2) K).1 0 0 = 1 := by simp [t, diagTorus]
    obtain ⟨c, hc, hct⟩ : ∃ c : ℂ, c ≠ 0 ∧
        ∀ x, bigCellFun ((Ψ).ρ t f) x = c * bigCellFun f (x * a) :=
      ⟨_, mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun x => by
        rw [bigCellFun_ρ_torus, h11, h00, div_one]⟩
    refine ⟨c⁻¹ • (Ψ).ρ t f, Submodule.mem_inf.2 ⟨W.smul_mem _ (hW _ hf1),
      Submodule.smul_mem _ _ (ρ_mem_principalSeriesBigCell hf2 (torus_le_borel t.2))⟩, ?_⟩
    funext x
    rw [map_smul, Pi.smul_apply, hct, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Let $W$ be a $G$-stable subspace of the principal series with $W \cap V_w \neq 0$. Then $W$ contains $V_w(N)$. -/
theorem bigCellJacquetKer_le_of_inf_ne_bot {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hWw : W ⊓ Vw ≠ ⊥) : Ww ≤ W := by
  have hY := isAffineStable_bigCellFun hW
  have h0 : ∃ φ ∈ (W ⊓ Vw).map bigCellFun, φ ≠ 0 ∧ IsTestFun K φ := by
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWw
    have hf2 := (Submodule.mem_inf.1 hf).2
    refine ⟨bigCellFun f, ⟨f, hf, rfl⟩, fun h => hf0 ?_, isTestFun_bigCellFun hf2⟩
    exact bigCellFun_inj hf2 (zero_mem _) (h.trans (map_zero _).symm)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, hn, g, hg, rfl⟩
  obtain ⟨h, hh, he⟩ := hY.translate_sub_mem h0 (isTestFun_bigCellFun hg) (n.1 0 1)
  have hng : (Ψ).ρ n g - g ∈ Vw :=
    sub_mem (ρ_mem_principalSeriesBigCell hg (unipotent_le_borel hn)) hg
  have e : h = (Ψ).ρ n g - g := by
    refine bigCellFun_inj (Submodule.mem_inf.1 hh).2 hng ?_
    rw [he]
    funext x
    rw [map_sub, Pi.sub_apply, Pi.sub_apply, bigCellFun_ρ_of_mem g hn]
  rw [← e]
  exact (Submodule.mem_inf.1 hh).1

/-- Let $W$ be a $G$-stable subspace of the principal series with $W \cap V_w \neq 0$. Then $W$ contains $V(N)$: a vector of $V(N)$ vanishes at $1$, so it is in $V_w(N)$. -/
theorem jacquetKer_le_of_inf_ne_bot {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hWw : W ⊓ Vw ≠ ⊥) :
    (Ψ).jacquetKer (unipotent K) ≤ W := fun _ hv =>
  bigCellJacquetKer_le_of_inf_ne_bot hW hWw
    (mem_bigCellJacquetKer_of_mem_jacquetKer (principalSeriesInd_eval_eq_zero_of_mem hv) hv)

/-- Let $W \neq 0$ be a $G$-stable subspace of the principal series with $W \cap V_w = 0$. Then $\chi_1 = \chi_2$. Each $f \in W$ is fixed by $N$, so by the lower unipotent matrices and by $\mathrm{diag}(a, a^{-1})$, and $f(\mathrm{diag}(a, a^{-1})) = \chi_1(a)\chi_2(a)^{-1} f(1)$. -/
theorem eq_of_inf_principalSeriesBigCell_eq_bot {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥) (hWw : W ⊓ Vw = ⊥) : χ₁ = χ₂ := by
  have hbot : IsStableSubspace (Ψ).ρ (⊥ : Submodule ℂ (Ψ).V) := fun _ => bot_le
  have hS : ∀ x : K, unip x ∈ relStab (Ψ) W ⊥ hW := by
    intro x v hv
    have h1 : (Ψ).ρ (unip x) v - v ∈ W := W.sub_mem (hW _ hv) hv
    have h2 : (Ψ).ρ (unip x) v - v ∈ Vw :=
      principalSeriesInd_eval_eq_zero_of_mem ((Ψ).sub_mem_jacquetKer (unip_mem x) v)
    rw [← hWw]
    exact Submodule.mem_inf.2 ⟨h1, h2⟩
  obtain ⟨f, hf, hf1⟩ := principalSeriesInd_exists_mem_ne_zero hW hW0
  have hc : (SmoothRep.ind.toFun f 1).down ≠ 0 := fun h => hf1 (ULift.ext h)
  refine MonoidHom.ext fun a => ?_
  set s : torus K := diagTorus K a a⁻¹
  have hs := diagTorus_mem_relStab hW hbot hS a f hf
  rw [Submodule.mem_bot, sub_eq_zero] at hs
  have h3 : SmoothRep.ind.toFun ((Ψ).ρ s f) 1 = SmoothRep.ind.toFun f 1 := by rw [hs]
  change SmoothRep.ind.toFun f (1 * (s : GL (Fin 2) K)) = _ at h3
  rw [one_mul, ← mul_one (s : GL (Fin 2) K),
    show (s : GL (Fin 2) K) = ((⟨s, torus_le_borel s.2⟩ : GL2.borel K) : GL (Fin 2) K) from rfl,
    principalSeriesInd_mul_left] at h3
  have h4 : (torusChar χ₁ χ₂ s : ℂ) * (SmoothRep.ind.toFun f 1).down =
      (SmoothRep.ind.toFun f 1).down :=
    congrArg ULift.down h3
  rw [torusChar_diagTorus] at h4
  have h5 : ((χ₁ a * χ₂ a⁻¹ : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hc (h4.trans (one_mul _).symm)
  have h6 : χ₁ a * χ₂ a⁻¹ = 1 := Units.ext h5
  rwa [map_inv, mul_inv_eq_one] at h6

/-- Let $U \neq 0$ be a $G$-stable subspace of the principal series that contains $V(N)$. If the character `bigCellChar` is not trivial on some $\mathrm{diag}(a, a^{-1})$, then $U$ is the whole space. The group generated by $N$ and the lower unipotent matrices acts trivially on $V / U$, and the vector $y_1$ of $V_N$ has the eigenvalue `bigCellChar` under $T$. -/
theorem eq_top_of_jacquetKer_le {U : Submodule ℂ (Ψ).V} (hU : IsStableSubspace (Ψ).ρ U)
    (hU0 : U ≠ ⊥) (hN : (Ψ).jacquetKer (unipotent K) ≤ U)
    (hβ : ∃ a : Kˣ, bigCellChar χ₁ χ₂ (diagTorus K a a⁻¹) ≠ 1) : U = ⊤ := by
  obtain ⟨a, ha⟩ := hβ
  have htop : IsStableSubspace (Ψ).ρ (⊤ : Submodule ℂ (Ψ).V) := fun _ => le_top
  have hS : ∀ x : K, unip x ∈ relStab (Ψ) ⊤ U htop := fun x v _ =>
    hN ((Ψ).sub_mem_jacquetKer (unip_mem x) v)
  set s : torus K := diagTorus K a a⁻¹
  have hs : ∀ v, (Ψ).ρ s v - v ∈ U := fun v =>
    diagTorus_mem_relStab htop hU hS a v Submodule.mem_top
  obtain ⟨x₀, y₁, -, hy0, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
  set mk : (Ψ).V →ₗ[ℂ] (principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂).V :=
    (Ψ).jacquetMk (unipotent K) (torus K) torus_le_normalizer_unipotent
  have hmk : ∀ v w, mk v = mk w → w ∈ U → v ∈ U := by
    intro v w h hw
    have h1 : v - w ∈ (Ψ).jacquetKer (unipotent K) :=
      ((Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent _).1 (by rw [map_sub]; exact sub_eq_zero.2 h)
    simpa using U.add_mem (hN h1) hw
  obtain ⟨Y₁, rfl⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent y₁
  set β : ℂ := (bigCellChar χ₁ χ₂ s : ℂ)
  have hY : (Ψ).ρ s Y₁ - β • Y₁ ∈ U := by
    refine hN (((Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent _).1 ?_)
    have e : mk ((Ψ).ρ s Y₁) = β • mk Y₁ := hρy s
    rw [map_sub, map_smul]
    exact sub_eq_zero.2 e
  have hY₁ : Y₁ ∈ U := by
    have h := U.sub_mem (hs Y₁) hY
    have e : (Ψ).ρ s Y₁ - Y₁ - ((Ψ).ρ s Y₁ - β • Y₁) = (β - 1) • Y₁ := by
      rw [sub_smul, one_smul]
      abel
    rw [e] at h
    have hβ1 : β - 1 ≠ 0 := sub_ne_zero.2 fun h => ha (Units.ext h)
    simpa [smul_smul, inv_mul_cancel₀ hβ1] using U.smul_mem (β - 1)⁻¹ h
  obtain ⟨f, hf, hf1⟩ := principalSeriesInd_exists_mem_ne_zero hU hU0
  set e : ℂ := (SmoothRep.ind.toFun f 1).down
  have he : e ≠ 0 := fun h => hf1 (ULift.ext h)
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨c, hc⟩ := hspan (mk v)
  obtain ⟨d, hd⟩ := hspan (mk f)
  set a' : ℂ := (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂ (mk v)).down
  have hd' : mk f = e • x₀ + d • mk Y₁ := hd
  refine hmk v ((a' / e) • f + (c - a' / e * d) • Y₁) ?_
    (U.add_mem (U.smul_mem _ hf) (U.smul_mem _ hY₁))
  have hc' : mk v = a' • x₀ + c • mk Y₁ := hc
  rw [map_add, map_smul, map_smul, hd', hc']
  match_scalars <;> field_simp <;> ring

/-- The principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ is irreducible if $\chi_1 \neq \chi_2$ and the character `bigCellChar` is not trivial on some $\mathrm{diag}(a, a^{-1})$, that is, if $\chi_1 \neq \chi_2$ and $\chi_1 \neq \chi_2 |\cdot|^2$. -/
theorem principalSeriesInd_isIrreducible (h₁ : χ₁ ≠ χ₂)
    (h₂ : ∃ a : Kˣ, bigCellChar χ₁ χ₂ (diagTorus K a a⁻¹) ≠ 1) : (Ψ).IsIrreducible := by
  refine ⟨principalSeriesInd_nontrivial hχ₁ hχ₂, fun W hW => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  refine Or.inr ?_
  by_cases hWw : W ⊓ Vw = ⊥
  · exact absurd (eq_of_inf_principalSeriesBigCell_eq_bot hW hW0 hWw) h₁
  · exact eq_top_of_jacquetKer_le hW hW0 (jacquetKer_le_of_inf_ne_bot hW hWw) h₂

/-- Let $W \neq V$ be a $G$-stable subspace of the principal series. Then $W + V(N) \neq V$. If $W \cap V_w \neq 0$, then $V(N) \le W$. If $W \cap V_w = 0$, then a lift of $y_1$ is not in $W + V(N)$, since each vector of $W \cap V_w$ is $0$. -/
theorem sup_jacquetKer_lt_top {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W)
    (hWt : W ≠ ⊤) : W ⊔ (Ψ).jacquetKer (unipotent K) < ⊤ := by
  rw [lt_top_iff_ne_top]
  by_cases hWw : W ⊓ Vw = ⊥
  · intro htop
    obtain ⟨-, y₁, -, hy0, hy₁, -, -⟩ := principalSeriesJacquet_exists_basis
      (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
    set mk := (Ψ).jacquetMk (unipotent K) (torus K) torus_le_normalizer_unipotent
    obtain ⟨Y₁, rfl⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent y₁
    have hmem : Y₁ ∈ W ⊔ (Ψ).jacquetKer (unipotent K) := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, k, hk, hwk⟩ := Submodule.mem_sup.1 hmem
    have hmkw : mk Y₁ = mk w := by
      rw [← hwk, map_add, ((Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent k).2 hk,
        add_zero]
    have hw1 : w ∈ Vw := by
      rw [hmkw] at hy₁
      exact hy₁
    have hw0 : w = 0 := by
      have : w ∈ W ⊓ Vw := Submodule.mem_inf.2 ⟨hw, hw1⟩
      rwa [hWw, Submodule.mem_bot] at this
    exact hy0 (by rw [hmkw, hw0, map_zero]; rfl)
  · intro htop
    exact hWt ((sup_eq_left.2 (jacquetKer_le_of_inf_ne_bot hW hWw)).symm.trans htop)

/-- Let $W \neq V$ be a $G$-stable subspace of the principal series. Then the quotient $Q = V / W$ has $Q_N \neq 0$. A nonzero linear form on $V$ that vanishes on $W + V(N)$ gives a nonzero linear form on $Q_N$. -/
theorem principalSeriesInd_quotient_jacquet_nontrivial {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hWt : W ≠ ⊤) :
    Nontrivial (((Ψ).quotient W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V := by
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (sup_jacquetKer_lt_top hW hWt)
  set Q := (Ψ).quotient W hW
  let μ : Q.V →ₗ[ℂ] ℂ := W.liftQ l (le_sup_left.trans hl)
  have hle : Q.jacquetKer (unipotent K) ≤ LinearMap.ker μ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨n, q⟩, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W q
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    change l ((Ψ).ρ n v) - l v = 0
    rw [← map_sub]
    exact hl (Submodule.mem_sup_right ((Ψ).sub_mem_jacquetKer n.2 v))
  by_contra hQ
  rw [not_nontrivial_iff_subsingleton] at hQ
  refine hl0 (LinearMap.ext fun v => ?_)
  have h1 : Q.jacquetMk _ _ torus_le_normalizer_unipotent (show Q.V from Submodule.Quotient.mk v) = 0 :=
    Subsingleton.elim _ _
  exact hle ((Q.jacquetMk_eq_zero_iff torus_le_normalizer_unipotent _).1 h1)

end Representation

section NormalizedCriterion

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- If $\chi_2 \neq \chi_1 |\cdot|$, then $\chi_1 |\cdot|^{1/2} \neq \chi_2 |\cdot|^{-1/2}$. -/
theorem mul_sqrtAbsChar_ne (h : χ₂ ≠ χ₁ * absChar K) :
    χ₁ * sqrtAbsChar K ≠ χ₂ * (sqrtAbsChar K)⁻¹ := by
  intro e
  apply h
  calc χ₂ = χ₂ * (sqrtAbsChar K)⁻¹ * sqrtAbsChar K := by ext x; simp
    _ = χ₁ * sqrtAbsChar K * sqrtAbsChar K := by rw [e]
    _ = χ₁ * absChar K := by rw [← sqrtAbsChar_sq]; ext x; simp [pow_two, mul_assoc]

/-- If $\chi_1 \neq \chi_2 |\cdot|$, then `bigCellChar` of $(\chi_1 |\cdot|^{1/2}, \chi_2 |\cdot|^{-1/2})$ is not trivial on some $\mathrm{diag}(a, a^{-1})$. Its value there is $\chi_2(a) |a| \chi_1(a)^{-1}$. -/
theorem exists_bigCellChar_ne_one (h : χ₁ ≠ χ₂ * absChar K) :
    ∃ a : Kˣ, bigCellChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹)
      (diagTorus K a a⁻¹) ≠ 1 := by
  by_contra hall
  push Not at hall
  apply h
  refine MonoidHom.ext fun a => ?_
  have h1 := congrArg Units.val (hall a)
  rw [bigCellChar, mul_sqrtAbsChar_inv_mul_absChar, mul_sqrtAbsChar_mul_absChar_inv,
    torusChar_diagTorus] at h1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_one] at h1
  refine Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, ← sqrtAbsChar_sq, pow_two, MonoidHom.mul_apply,
    Units.val_mul]
  have hχ : (χ₁ a : ℂ) ≠ 0 := Units.ne_zero _
  have hs : (sqrtAbsChar K a : ℂ) ≠ 0 := Units.ne_zero _
  field_simp at h1
  first
  | linear_combination h1
  | linear_combination -h1

/-- A nonzero quotient $Q$ of the normalized principal series has $Q_N \neq 0$. This holds for all $\chi_1, \chi_2$. -/
theorem normPrincipalSeries_quotient_jacquet_nontrivial {W : Submodule ℂ (Π).V}
    (hW : IsStableSubspace (Π).ρ W) (hWt : W ≠ ⊤) :
    Nontrivial (((Π).quotient W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V := by
  have key : ∀ π : SmoothRep (GL (Fin 2) K), π = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) → ∀ (W : Submodule ℂ π.V)
      (hW : IsStableSubspace π.ρ W), W ≠ ⊤ →
      Nontrivial ((π.quotient W hW).jacquet (unipotent K) (torus K)
        torus_le_normalizer_unipotent).V := by
    intro π hπ
    subst hπ
    exact fun W hW hWt => principalSeriesInd_quotient_jacquet_nontrivial hW hWt
  exact key _ (normPrincipalSeries_eq hχ₁ hχ₂) W hW hWt

/-- The irreducibility criterion: if $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$, that is, $\chi_1 \neq \chi_2 |\cdot|$ and $\chi_2 \neq \chi_1 |\cdot|$, then the normalized principal series of $(\chi_1, \chi_2)$ is irreducible. -/
theorem normPrincipalSeries_irreducible (h₁ : χ₁ ≠ χ₂ * absChar K)
    (h₂ : χ₂ ≠ χ₁ * absChar K) : (Π).IsIrreducible := by
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact principalSeriesInd_isIrreducible (mul_sqrtAbsChar_ne h₂) (exists_bigCellChar_ne_one h₁)

/-- A nonzero map of representations from an irreducible representation is injective: its kernel is a stable subspace. -/
theorem SmoothRep.IsIrreducible.injective {G : Type u} [Group G] [TopologicalSpace G]
    {π σ : SmoothRep G} (hπ : π.IsIrreducible) (Φ : IntertwiningMap π.ρ σ.ρ) (hΦ : Φ ≠ 0) :
    Function.Injective Φ := by
  have hk : IsStableSubspace π.ρ (LinearMap.ker Φ.toLinearMap) := by
    intro g v hv
    rw [Submodule.mem_comap, LinearMap.mem_ker, IntertwiningMap.coe_toLinearMap,
      IntertwiningMap.isIntertwining]
    rw [LinearMap.mem_ker, IntertwiningMap.coe_toLinearMap] at hv
    rw [hv, map_zero]
  rcases hπ.2 _ hk with h | h
  · rw [← IntertwiningMap.coe_toLinearMap, ← LinearMap.ker_eq_bot]
    exact h
  · refine absurd (IntertwiningMap.ext (LinearMap.ext fun v => ?_)) hΦ
    have hv : v ∈ LinearMap.ker Φ.toLinearMap := h ▸ Submodule.mem_top
    exact hv

/-- If $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$, each nonzero map of representations of $G$ from the normalized principal series of $(\chi_1, \chi_2)$ to that of $(\chi_2, \chi_1)$ is injective. -/
theorem normPrincipalSeries_hom_injective (h₁ : χ₁ ≠ χ₂ * absChar K)
    (h₂ : χ₂ ≠ χ₁ * absChar K)
    (Φ : IntertwiningMap (Π).ρ (normPrincipalSeries χ₂ χ₁ hχ₂ hχ₁).ρ) (hΦ : Φ ≠ 0) :
    Function.Injective Φ :=
  (normPrincipalSeries_irreducible h₁ h₂).injective Φ hΦ

end NormalizedCriterion

end Langlands
