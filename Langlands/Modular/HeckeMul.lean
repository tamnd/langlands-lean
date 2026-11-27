/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.NatDivisors
import Langlands.Modular.Hecke

/-!
# Multiplicativity of the coefficients of a normalized Hecke eigenform

Let $f = \sum a_n q^n$ be a cusp form of weight $k$ on $\Gamma_0(N)$ that is an eigenvector of each operator $T_p$ of `Langlands/Modular/Hecke.lean`, with $a_1 = 1$. This file proves that the coefficients are multiplicative, $a_{mn} = a_m a_n$ for coprime $m$ and $n$. With the results `good` and `bad` of `Langlands/Modular/Hecke.lean`, this gives all the fields of `Langlands.IsNormalizedEigenform`. The file also defines the operators $T_n$ for all $n \ge 1$ on coefficient sequences and proves that $T_n$ acts on the coefficients of $f$ by multiplication with $a_n$.

## Main definitions

* `Langlands.Modular.IsHeckeEigenSeq`: the sequence $a$ satisfies $a_{mp} + p^{k-1} a_{m/p} = a_p a_m$ for each prime $p$ and each $m$, where the second term is present only for $p \nmid N$ and $p \mid m$.
* `Langlands.Modular.heckeSeq`: the operator $(T_n a)_m = \sum_{d} d^{k-1} a_{mn/d^2}$ on coefficient sequences, where $d$ runs over the common divisors of $m$ and $n$ that are coprime to $N$.

## Main results

* `Langlands.Modular.cuspHeckeT_add` and `Langlands.Modular.cuspHeckeT_smul`: the operator $T_p$ on cusp forms is linear.
* `Langlands.Modular.IsHeckeEigenSeq.pow_mul`: $a_{p^r m} = a_{p^r} a_m$ for $p \nmid m$.
* `Langlands.Modular.IsHeckeEigenSeq.mul`: $a_{mn} = a_m a_n$ for coprime $m$ and $n$.
* `Langlands.Modular.IsHeckeEigenSeq.heckeSeq_eq`: $(T_n a)_m = a_n a_m$ for $n, m \ge 1$.
* `Langlands.Modular.IsNormalizedHeckeEigenform.mul`: a normalized Hecke eigenform satisfies the field `mul` of `Langlands.IsNormalizedEigenform`.
* `Langlands.Modular.IsNormalizedHeckeEigenform.toIsNormalizedEigenform`: a normalized Hecke eigenform satisfies `Langlands.IsNormalizedEigenform`.
* `Langlands.Modular.IsNormalizedHeckeEigenform.heckeSeq_qCoeff`: for $n \ge 1$ and all $m$, $\sum_{d} d^{k-1} a_{mn/d^2} = a_n a_m$.

## Proof

The proof uses only the coefficients. The eigenvalue equation of $T_p$ at $m$ with $p \nmid m$ gives $a_{mp} = a_p a_m$. The eigenvalue equations at $p^{r+1} m$ and at $p^{r+1}$ give the same recursion for $a_{p^{r+2} m}$ and for $a_{p^{r+2}} a_m$, so $a_{p^r m} = a_{p^r} a_m$ for $p \nmid m$ by induction on $r$. Then $a_{mn} = a_m a_n$ for coprime $m$ and $n$ follows by induction on the factorization of $n$. For the operators $T_n$, the case $n = p^\beta$ reduces to the identity $a_{p^\alpha} a_{p^\beta} = \sum_{j \le \min(\alpha, \beta)} c^j a_{p^{\alpha + \beta - 2j}}$, with $c = p^{k-1}$ for $p \nmid N$ and $c = 0$ for $p \mid N$. The case of coprime $x$ and $y$ uses the bijection $(d_1, d_2) \mapsto d_1 d_2$ from the divisors of $x$ and of $y$ to the divisors of $xy$.

## What is left

The operator `heckeSeq` is defined on coefficient sequences, not on modular forms. The file does not define $T_n$ on modular forms by double cosets, and it does not prove $T_{mn} = T_m T_n$ as operators.

## References

* F. Diamond and J. Shurman, A first course in modular forms, chapter 5, section 5.3.
-/

namespace Langlands.Modular

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "Γ₀" N => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

section Linear

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] {k : ℤ}

/-- The operator `T_p` on cusp forms is additive. -/
theorem cuspHeckeT_add (f g : CuspForm (Γ₀ N) k) :
    cuspHeckeT p N (f + g) = cuspHeckeT p N f + cuspHeckeT p N g := by
  ext τ
  simp only [add_apply, coe_cuspHeckeT]
  by_cases hpN : p ∣ N
  · simp only [heckeT_apply_of_dvd p N _ hpN, add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [heckeT_apply_of_not_dvd p N _ hpN, add_apply, mul_add,
      Finset.sum_add_distrib]
    ring

/-- The operator `T_p` on cusp forms commutes with scalar multiplication. -/
theorem cuspHeckeT_smul (c : ℂ) (f : CuspForm (Γ₀ N) k) :
    cuspHeckeT p N (c • f) = c • cuspHeckeT p N f := by
  ext τ
  simp only [smul_apply, coe_cuspHeckeT, smul_eq_mul]
  by_cases hpN : p ∣ N
  · simp only [heckeT_apply_of_dvd p N _ hpN, smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  · simp only [heckeT_apply_of_not_dvd p N _ hpN, smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_add]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring

end Linear

section Sequence

/-- The sequence `a` satisfies the eigenvalue equations of all the operators `T_p` on coefficient sequences, with eigenvalue `a_p`: for each prime `p` and each `m`, `a_{m p} + p^(k - 1) a_{m / p} = a_p a_m`, where the second term is present only for `p ∤ N` and `p ∣ m`. -/
def IsHeckeEigenSeq (N : ℕ) (k : ℤ) (a : ℕ → ℂ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m : ℕ,
    a (m * p) + (if ¬ p ∣ N ∧ p ∣ m then (p : ℂ) ^ (k - 1) * a (m / p) else 0) = a p * a m

variable {N : ℕ} {k : ℤ} {a : ℕ → ℂ}

/-- If `a` satisfies the eigenvalue equations with `a_1 = 1` and `p ∤ m`, then `a_{p^r m} = a_{p^r} a_m`. -/
theorem IsHeckeEigenSeq.pow_mul (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) (r : ℕ) : a (p ^ r * m) = a (p ^ r) * a m := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  match r, ih with
  | 0, _ => simp [h1]
  | 1, _ =>
    have h := ha p hp m
    simp only [hpm, and_false, ↓reduceIte, add_zero] at h
    rw [pow_one, mul_comm, h]
  | r + 2, ih =>
    have h₁ := ha p hp (p ^ (r + 1) * m)
    have h₂ := ha p hp (p ^ (r + 1))
    have hd₁ : p ∣ p ^ (r + 1) * m := (dvd_pow_self p r.succ_ne_zero).mul_right m
    have hd₂ : p ∣ p ^ (r + 1) := dvd_pow_self p r.succ_ne_zero
    have hq₁ : p ^ (r + 1) * m / p = p ^ r * m := by
      rw [pow_succ, mul_right_comm, Nat.mul_div_cancel _ hp.pos]
    have hq₂ : p ^ (r + 1) / p = p ^ r := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    have hm₁ : p ^ (r + 1) * m * p = p ^ (r + 2) * m := by ring
    have hm₂ : p ^ (r + 1) * p = p ^ (r + 2) := by ring
    rw [hm₁, hq₁, ih (r + 1) (by omega)] at h₁
    rw [hm₂, hq₂] at h₂
    have e₀ := ih r (by omega)
    by_cases hpN : p ∣ N
    · simp only [hpN, not_true_eq_false, false_and, ↓reduceIte, add_zero] at h₁ h₂
      rw [h₁, h₂]; ring
    · simp only [hpN, hd₁, hd₂, not_false_eq_true, and_self, ↓reduceIte] at h₁ h₂
      rw [e₀] at h₁
      linear_combination h₁ - a m * h₂

/-- **Multiplicativity**: if `a` satisfies the eigenvalue equations of all `T_p` with `a_1 = 1`, then `a_{m n} = a_m a_n` for coprime `m` and `n`. -/
theorem IsHeckeEigenSeq.mul (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m n
  induction n using Nat.recOnPosPrimePosCoprime generalizing m with
  | prime_pow p r hp hr =>
    intro hm
    have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.coprime_dvd_right (dvd_pow_self p hr.ne') hm).symm
    rw [mul_comm, ha.pow_mul h1 hp hpm, mul_comm]
  | zero =>
    intro hm
    rw [(Nat.coprime_zero_right m).1 hm]
    simp [h1]
  | one => intro _; simp [h1]
  | coprime x y _ _ hxy hx hy =>
    intro hm
    have hmx : m.Coprime x := hm.coprime_dvd_right (dvd_mul_right x y)
    have hmy : m.Coprime y := hm.coprime_dvd_right (dvd_mul_left y x)
    rw [← mul_assoc, hy (m * x) (Nat.coprime_mul_iff_left.2 ⟨hmy, hxy⟩), hx m hmx, hy x hxy]
    ring

end Sequence

section HeckeSeq

/-- The operator `T_n` on coefficient sequences: `(T_n a)_m = ∑ d^(k - 1) a_{m n / d^2}`, where `d` runs over the common divisors of `m` and `n` that are coprime to `N`. -/
noncomputable def heckeSeq (N : ℕ) (k : ℤ) (n : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, if d.Coprime N ∧ d ∣ m then (d : ℂ) ^ (k - 1) * a (m * n / (d * d)) else 0

variable {N : ℕ} {k : ℤ} {a : ℕ → ℂ}

/-- The eigenvalue equation at `p^(e + 1)`: `a_{p^(e+2)} + c a_{p^e} = a_p a_{p^(e+1)}`, with `c = p^(k - 1)` for `p ∤ N` and `c = 0` for `p ∣ N`. -/
lemma IsHeckeEigenSeq.pow_succ_succ (ha : IsHeckeEigenSeq N k a) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a (p ^ (e + 2)) + (if p ∣ N then 0 else (p : ℂ) ^ (k - 1)) * a (p ^ e) =
      a p * a (p ^ (e + 1)) := by
  have h := ha p hp (p ^ (e + 1))
  have hd : p ∣ p ^ (e + 1) := dvd_pow_self p e.succ_ne_zero
  have hq : p ^ (e + 1) / p = p ^ e := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [← pow_succ, hq] at h
  by_cases hpN : p ∣ N
  · simpa [hpN] using h
  · simpa [hpN, hd] using h

/-- For a prime `p`: `a_{p^(α+1)} a_{p^(β+1)} = a_{p^(α+β+2)} + c a_{p^α} a_{p^β}`, with `c` as in `IsHeckeEigenSeq.pow_succ_succ`. -/
lemma IsHeckeEigenSeq.pow_succ_mul_pow_succ (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1)
    {p : ℕ} (hp : p.Prime) (β : ℕ) : ∀ α : ℕ, a (p ^ (α + 1)) * a (p ^ (β + 1)) =
      a (p ^ (α + β + 2)) + (if p ∣ N then 0 else (p : ℂ) ^ (k - 1)) * (a (p ^ α) * a (p ^ β)) := by
  induction β with
  | zero =>
    intro α
    have h := ha.pow_succ_succ hp α
    rw [zero_add, pow_one, pow_zero, h1, add_zero]
    linear_combination -h
  | succ β ih =>
    intro α
    have hα := ha.pow_succ_succ hp α
    have hβ := ha.pow_succ_succ hp β
    have hi := ih (α + 1)
    rw [show α + 1 + β + 2 = α + β + 1 + 2 by omega] at hi
    rw [show β + 1 + 1 = β + 2 by omega]
    linear_combination a (p ^ (α + 1)) * hβ + hi - a (p ^ (β + 1)) * hα

/-- For a prime `p`: `a_{p^α} a_{p^β} = ∑_{j ≤ min(α, β)} c^j a_{p^(α+β-2j)}`, with `c` as in `IsHeckeEigenSeq.pow_succ_succ`. -/
lemma IsHeckeEigenSeq.sum_range_min (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1)
    {p : ℕ} (hp : p.Prime) (α : ℕ) : ∀ β : ℕ,
      ∑ j ∈ Finset.range (min α β + 1),
        (if p ∣ N then 0 else (p : ℂ) ^ (k - 1)) ^ j * a (p ^ (α + β - 2 * j)) =
      a (p ^ α) * a (p ^ β) := by
  induction α with
  | zero => intro β; simp [h1]
  | succ α ih =>
    intro β
    cases β with
    | zero => simp [h1]
    | succ β =>
      rw [show min (α + 1) (β + 1) = min α β + 1 by omega, Finset.sum_range_succ',
        ha.pow_succ_mul_pow_succ h1 hp β α, ← ih β, Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero,
        show α + 1 + (β + 1) = α + β + 2 by omega]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show α + β + 2 - 2 * (j + 1) = α + β - 2 * j by omega, pow_succ]
      ring

/-- The factor `d^(k - 1)` at `d = p^j`, for the divisors coprime to `N`, is `c^j`. -/
lemma ite_coprime_pow_zpow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (if (p ^ j).Coprime N then ((p ^ j : ℕ) : ℂ) ^ (k - 1) else 0) =
      (if p ∣ N then 0 else (p : ℂ) ^ (k - 1)) ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.coprime_pow_left_iff (Nat.succ_pos j), Nat.Prime.coprime_iff_not_dvd hp]
    by_cases hpN : p ∣ N
    · simp [hpN]
    · simp only [hpN, not_false_eq_true, ↓reduceIte]
      push_cast
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- The operator `T_{p^β}` on the coefficients of an eigensequence, at `m ≠ 0`. -/
lemma IsHeckeEigenSeq.heckeSeq_prime_pow (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1)
    {p : ℕ} (hp : p.Prime) (β : ℕ) {m : ℕ} (hm : m ≠ 0) :
    heckeSeq N k (p ^ β) a m = a (p ^ β) * a m := by
  obtain ⟨α, m', hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  have hcop : ∀ j, (p ^ j).Coprime m' := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  rw [heckeSeq, Nat.sum_divisors_prime_pow hp, ha.pow_mul h1 hp hpm,
    ← mul_assoc, mul_comm (a (p ^ β)), ← ha.sum_range_min h1 hp α β, Finset.sum_mul,
    min_comm]
  rw [← Finset.sum_range_add_sum_Ico _ (show min β α + 1 ≤ β + 1 by omega)]
  have h0 : ∑ j ∈ Finset.Ico (min β α + 1) (β + 1), (if (p ^ j).Coprime N ∧ p ^ j ∣ p ^ α * m' then
      ((p ^ j : ℕ) : ℂ) ^ (k - 1) * a (p ^ α * m' * p ^ β / (p ^ j * p ^ j)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    split_ifs with h
    · obtain ⟨_, hd⟩ := h
      rw [(hcop j).dvd_mul_right, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
      omega
    · rfl
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjα : j ≤ α := by omega
  have hjβ : j ≤ β := by omega
  have hd : p ^ j ∣ p ^ α * m' := (pow_dvd_pow p hjα).mul_right m'
  have hq : p ^ α * m' * p ^ β / (p ^ j * p ^ j) = p ^ (α + β - 2 * j) * m' := by
    refine Nat.div_eq_of_eq_mul_left (Nat.mul_pos (pow_pos hp.pos j) (pow_pos hp.pos j)) ?_
    rw [show p ^ α * m' * p ^ β = p ^ (α + β) * m' by ring]
    rw [show p ^ (α + β - 2 * j) * m' * (p ^ j * p ^ j) = p ^ (α + β - 2 * j + j + j) * m' by ring,
      show α + β - 2 * j + j + j = α + β by omega]
  rw [hq, ha.pow_mul h1 hp (by omega), ← ite_coprime_pow_zpow (N := N) hp j]
  by_cases hc : (p ^ j).Coprime N
  · simp only [eq_true hc, eq_true hd, and_self, ↓reduceIte]
    ring
  · simp [hc]

/-- The operator `T_{x y}` on the coefficients of an eigensequence, for coprime `x` and `y`, follows from `T_x` and `T_y`. -/
lemma IsHeckeEigenSeq.heckeSeq_mul (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1) {x y : ℕ}
    (hxy : x.Coprime y) (hx : x ≠ 0)
    (ihx : ∀ m, m ≠ 0 → heckeSeq N k x a m = a x * a m)
    (ihy : ∀ m, m ≠ 0 → heckeSeq N k y a m = a y * a m) {m : ℕ} (hm : m ≠ 0) :
    heckeSeq N k (x * y) a m = a (x * y) * a m := by
  rw [heckeSeq, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image (fun u hu v hv h => hxy.mul_injOn_divisors hu hv h), Finset.sum_product,
    ha.mul h1 x y hxy, mul_comm (a x), mul_assoc, ← ihx m hm, heckeSeq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  have hd₁x : d₁ ∣ x := Nat.dvd_of_mem_divisors hd₁
  have hd₁pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  by_cases hc : d₁.Coprime N ∧ d₁ ∣ m
  · obtain ⟨hcN, m₁, hm₁⟩ := hc
    obtain ⟨x₁, hx₁⟩ := hd₁x
    have hq : m * x / (d₁ * d₁) = m₁ * x₁ :=
      Nat.div_eq_of_eq_mul_left (Nat.mul_pos hd₁pos hd₁pos) (by rw [hm₁, hx₁]; ring)
    have hmx : m₁ * x₁ ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hm (by rw [hm₁, mul_zero])
      · rintro rfl; exact hx (by rw [hx₁, mul_zero])
    simp only [eq_true hcN, eq_true (Dvd.intro m₁ hm₁.symm), and_self, ↓reduceIte]
    rw [hq, mul_left_comm (a y), ← ihy (m₁ * x₁) hmx, heckeSeq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
    have hd₂y : d₂ ∣ y := Nat.dvd_of_mem_divisors hd₂
    have hd₂pos : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
    have hcop : d₂.Coprime x₁ :=
      ((Nat.Coprime.coprime_dvd_left (Dvd.intro_left d₁ hx₁.symm) hxy).coprime_dvd_right hd₂y).symm
    have hiff : ((d₁ * d₂).Coprime N ∧ d₁ * d₂ ∣ m) ↔ (d₂.Coprime N ∧ d₂ ∣ m₁ * x₁) := by
      rw [Nat.coprime_mul_iff_left, hm₁, Nat.mul_dvd_mul_iff_left hd₁pos, hcop.dvd_mul_right]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hcN, h.1⟩, h.2⟩⟩
    by_cases hd : d₂.Coprime N ∧ d₂ ∣ m₁ * x₁
    · have hd' := hiff.2 hd
      obtain ⟨m₂, hm₂⟩ := hcop.dvd_mul_right.1 hd.2
      obtain ⟨y₁, hy₁⟩ := hd₂y
      have hq₁ : m * (x * y) / (d₁ * d₂ * (d₁ * d₂)) = m₂ * x₁ * y₁ :=
        Nat.div_eq_of_eq_mul_left (by positivity) (by rw [hm₁, hm₂, hx₁, hy₁]; ring)
      have hq₂ : m₁ * x₁ * y / (d₂ * d₂) = m₂ * x₁ * y₁ :=
        Nat.div_eq_of_eq_mul_left (by positivity) (by rw [hm₂, hy₁]; ring)
      simp only [eq_true hd, eq_true hd', ↓reduceIte]
      rw [hq₁, hq₂]
      push_cast
      rw [mul_zpow]
      ring
    · have hd' : ¬ ((d₁ * d₂).Coprime N ∧ d₁ * d₂ ∣ m) := fun h => hd (hiff.1 h)
      simp only [eq_false hd, eq_false hd', ↓reduceIte, mul_zero]
  · simp only [eq_false hc, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero fun d₂ _ => ?_
    have hd : ¬ ((d₁ * d₂).Coprime N ∧ d₁ * d₂ ∣ m) := fun h =>
      hc ⟨(Nat.coprime_mul_iff_left.1 h.1).1, (dvd_mul_right d₁ d₂).trans h.2⟩
    simp only [eq_false hd, ↓reduceIte]

/-- **The operators `T_n` on an eigensequence**: if `a` satisfies the eigenvalue equations of all `T_p` with `a_1 = 1`, then `(T_n a)_m = a_n a_m` for all `n, m ≥ 1`, that is, `a_m a_n = ∑ d^(k - 1) a_{m n / d^2}` over the common divisors `d` of `m` and `n` coprime to `N`. -/
theorem IsHeckeEigenSeq.heckeSeq_eq (ha : IsHeckeEigenSeq N k a) (h1 : a 1 = 1) {n : ℕ}
    (hn : n ≠ 0) {m : ℕ} (hm : m ≠ 0) : heckeSeq N k n a m = a n * a m := by
  induction n using Nat.recOnPosPrimePosCoprime generalizing m with
  | prime_pow p r hp _ => exact ha.heckeSeq_prime_pow h1 hp r hm
  | zero => exact absurd rfl hn
  | one => simp [heckeSeq, h1]
  | coprime x y hx hy hxy ihx ihy =>
    exact ha.heckeSeq_mul h1 hxy (by omega) (fun m hm => ihx (by omega) hm)
      (fun m hm => ihy (by omega) hm) hm

end HeckeSeq

section Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The coefficients of a normalized Hecke eigenform satisfy the eigenvalue equations of all the operators `T_p` with eigenvalue `a_p`. -/
theorem IsNormalizedHeckeEigenform.isHeckeEigenSeq {f : CuspForm (Γ₀ N) k}
    (hf : IsNormalizedHeckeEigenform N f) : IsHeckeEigenSeq N k (qCoeff f) := by
  intro p hp m
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hf.eigen.2 p
  have h := heckeCoeff_qCoeff_of_eigenvector p N hc m
  rw [eigenvalue_eq_qCoeff p N hc hf.one] at h
  exact h

/-- **Multiplicativity**: a normalized Hecke eigenform satisfies the `mul` field of `Langlands.IsNormalizedEigenform`, that is, `a_{m n} = a_m a_n` for coprime `m` and `n`. -/
theorem IsNormalizedHeckeEigenform.mul {f : CuspForm (Γ₀ N) k}
    (hf : IsNormalizedHeckeEigenform N f) (m n : ℕ) (hmn : m.Coprime n) :
    qCoeff f (m * n) = qCoeff f m * qCoeff f n :=
  hf.isHeckeEigenSeq.mul hf.one m n hmn

/-- A normalized Hecke eigenform, an eigenvector of every `T_p` with `a_1 = 1`, satisfies all the fields of `Langlands.IsNormalizedEigenform`. -/
theorem IsNormalizedHeckeEigenform.toIsNormalizedEigenform {f : CuspForm (Γ₀ N) k}
    (hf : IsNormalizedHeckeEigenform N f) : IsNormalizedEigenform f where
  one := hf.one
  mul := hf.mul
  good := hf.good
  bad := hf.bad

omit [NeZero N] in
/-- The constant coefficient of a cusp form on `Γ₀(N)` is zero. -/
lemma qCoeff_zero (f : CuspForm (Γ₀ N) k) : qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods N)

/-- **The operators `T_n` on a normalized Hecke eigenform**: for `n ≥ 1` and all `m`, `a_n a_m = ∑ d^(k - 1) a_{m n / d^2}`, where `d` runs over the common divisors of `m` and `n` that are coprime to `N`. This is the `q`-expansion form of `T_n f = a_n f`. -/
theorem IsNormalizedHeckeEigenform.heckeSeq_qCoeff {f : CuspForm (Γ₀ N) k}
    (hf : IsNormalizedHeckeEigenform N f) {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    heckeSeq N k n (qCoeff f) m = qCoeff f n * qCoeff f m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [heckeSeq, qCoeff_zero]
  · exact hf.isHeckeEigenSeq.heckeSeq_eq hf.one hn hm

end Eigenform

end Langlands.Modular
