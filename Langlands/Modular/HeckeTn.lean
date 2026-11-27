/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Modular.HeckeMul

/-!
# The Hecke operators $T_n$ on cusp forms and the level raising maps

Let $N \ge 1$ and let $k$ be an integer. This file defines the Hecke operators $T_n$ for all $n \ge 1$ on the cusp forms of weight $k$ on $\Gamma_0(N)$, from the operators $T_p$ of `Langlands/Modular/Hecke.lean`. It proves that the operators $T_n$ commute, that $T_{mn} = T_m T_n$ for coprime $m$ and $n$, and the formula $a_m(T_n f) = \sum_{d} d^{k-1} a_{mn/d^2}(f)$ for all $m$, where $d$ runs over the common divisors of $m$ and $n$ that are coprime to $N$. It also defines the level raising maps $B_d$, with $(B_d f)(\tau) = f(d \tau)$, from level $M$ to level $dM$, computes their $q$-expansions, and defines the oldspace.

## Main definitions

* `Langlands.Modular.heckeOp`: the operator $T_p$ on `CuspForm Γ₀(N) k` as a linear map, for a prime $p$.
* `Langlands.Modular.heckePow`: the operators $T_{p^r}$, with $T_1 = 1$ and $T_{p^{r+2}} = T_p T_{p^{r+1}} - c_p T_{p^r}$, where $c_p = p^{k-1}$ for $p \nmid N$ and $c_p = 0$ for $p \mid N$.
* `Langlands.Modular.heckeTn`: the operator $T_n = \prod_{p \mid n} T_{p^{v_p(n)}}$. The empty product gives $T_0 = 1$, as a convention.
* `Langlands.Modular.raiseMat`: the matrix $\mathrm{diag}(d, 1)$ in $\mathrm{GL}_2(\mathbb{R})$.
* `Langlands.Modular.levelRaiseMF` and `Langlands.Modular.levelRaise`: the linear maps $B_d f = d^{1-k} f |_k \mathrm{diag}(d, 1)$ from modular forms (or cusp forms) of level $M$ to level $dM$.
* `Langlands.Modular.cuspRestrict`: the inclusion of the cusp forms of level $L$ in the cusp forms of level $N$, for $L \mid N$.
* `Langlands.Modular.oldSpace`: the span of the images of $B_d$ from level $M$ to level $N$, over the pairs $(M, d)$ with $dM \mid N$ and $M < N$.

## Main results

* `Langlands.Modular.heckeTn_comm`: $T_m T_n = T_n T_m$ for all $m$ and $n$.
* `Langlands.Modular.heckeTn_one`: $T_1 = 1$.
* `Langlands.Modular.heckeTn_prime`: $T_p$ is the operator `cuspHeckeT p N` of `Langlands/Modular/Hecke.lean`.
* `Langlands.Modular.heckeTn_mul`: $T_{mn} = T_m T_n$ for coprime $m$ and $n$.
* `Langlands.Modular.heckeTn_prime_pow_succ_succ_of_not_dvd`: $T_{p^{r+2}} = T_p T_{p^{r+1}} - p^{k-1} T_{p^r}$ for $p \nmid N$.
* `Langlands.Modular.heckeTn_prime_pow_of_dvd`: $T_{p^r} = T_p^r$ for $p \mid N$.
* `Langlands.Modular.qCoeff_heckeTn_apply`: $a_m(T_n f) = \sum_{d} d^{k-1} a_{mn/d^2}(f)$ for $n \ge 1$ and all $m$, where $d$ runs over the divisors of $n$ that divide $m$ and are coprime to $N$.
* `Langlands.Modular.qCoeff_heckeTn_of_coprime`: $a_m(T_n f) = a_{mn}(f)$ for coprime $m$ and $n$.
* `Langlands.Modular.qCoeff_heckeTn_one`: $a_1(T_n f) = a_n(f)$.
* `Langlands.Modular.IsNormalizedHeckeEigenform.heckeTn_eq`: $T_n f = a_n(f) f$ for a normalized Hecke eigenform $f$ and $n \ge 1$.
* `Langlands.Modular.levelRaise_apply`: $(B_d f)(\tau) = f(d \tau)$.
* `Langlands.Modular.coeff_levelRaiseMF` and `Langlands.Modular.qCoeff_levelRaise`: $a_m(B_d f) = a_{m/d}(f)$ for $d \mid m$, and $a_m(B_d f) = 0$ for $d \nmid m$.
* `Langlands.Modular.levelRaise_mem_oldSpace`: $B_d f$ is in the oldspace of level $N$.

## Proof

Two cusp forms with the same $q$-coefficients are equal, because each cusp form is the sum of its $q$-expansion. The operators $T_p$ for primes $p$ commute, because their actions on the coefficients commute (`Langlands.Modular.heckeCoeff_comm`). Each $T_{p^r}$ is a polynomial in $T_p$, so each operator that commutes with all $T_p$ commutes with all $T_{p^r}$ and with all $T_n$. This gives that the $T_n$ commute, and it makes the product over the prime factors of $n$ well defined. The coefficient formula follows from the recursion for the sequences `Langlands.Modular.heckeSeq` of `Langlands/Modular/HeckeMul.lean`: this file proves the same recursion in $r$ for `heckeSeq N k (p ^ r)` and the identity `heckeSeq N k (x * y) = heckeSeq N k x ∘ heckeSeq N k y` for coprime $x$ and $y$. For $B_d$, the inclusion $\Gamma_0(dM) \subseteq \mathrm{diag}(d, 1)^{-1} \Gamma_0(M) \mathrm{diag}(d, 1)$ lets the translate of $f$ by $\mathrm{diag}(d, 1)$ be a form of level $dM$. The $q$-expansion of $f(d \tau)$ comes from the substitution $q \mapsto q^d$ in the $q$-expansion of $f$, and the uniqueness of $q$-expansions.

## What is left

The operators $T_n$ are defined from the operators $T_p$, not by double cosets. The file does not define $T_n$ on modular forms that are not cusp forms. It does not prove that the oldspace is stable under the $T_n$, it does not define the newspace, and it does not prove the decomposition of the cusp forms into the oldspace and the newspace.

## References

* F. Diamond and J. Shurman, A first course in modular forms, chapter 5, sections 5.2, 5.3 and 5.6.
-/

namespace Langlands.Modular

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "Γ₀" N => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

section Sequence

/-- The constant `c_p` of the recursion of `T_{p^r}`: `c_p = p^(k - 1)` for `p ∤ N` and `c_p = 0` for `p ∣ N`. -/
noncomputable def heckeConst (N : ℕ) (k : ℤ) (p : ℕ) : ℂ :=
  if p ∣ N then 0 else (p : ℂ) ^ (k - 1)

variable {N : ℕ} {k : ℤ}

/-- The operator `T_p` on coefficient sequences, written with the constant `c_p`. -/
lemma heckeCoeff_eq (p : ℕ) (a : ℕ → ℂ) (m : ℕ) :
    heckeCoeff p N k a m = a (m * p) + heckeConst N k p * if p ∣ m then a (m / p) else 0 := by
  unfold heckeCoeff heckeConst
  by_cases hpN : p ∣ N <;> by_cases hpm : p ∣ m <;> simp [hpN, hpm]

/-- The operator `T_1` on coefficient sequences is the identity. -/
@[simp]
lemma heckeSeq_one (a : ℕ → ℂ) : heckeSeq N k 1 a = a := by
  funext m
  simp [heckeSeq]

/-- The operator `T_0` on coefficient sequences is zero. -/
@[simp]
lemma heckeSeq_zero (a : ℕ → ℂ) : heckeSeq N k 0 a = 0 := by
  funext m
  simp [heckeSeq]

/-- The operator `T_{p^r}` on coefficient sequences, for a prime `p`: `(T_{p^r} a)_m = ∑_{j ≤ r, p^j ∣ m} c_p^j a_{m p^r / p^(2j)}`. -/
lemma heckeSeq_prime_pow {p : ℕ} (hp : p.Prime) (r : ℕ) (a : ℕ → ℂ) (m : ℕ) :
    heckeSeq N k (p ^ r) a m = ∑ j ∈ Finset.range (r + 1),
      if p ^ j ∣ m then heckeConst N k p ^ j * a (m * p ^ r / (p ^ j * p ^ j)) else 0 := by
  rw [heckeSeq, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ite_coprime_pow_zpow (N := N) (k := k) hp j
  rw [← heckeConst] at h
  rw [← h]
  by_cases hc : (p ^ j).Coprime N <;> by_cases hd : p ^ j ∣ m <;> simp [hc, hd]

/-- The recursion `(T_{p^(r+1)} a)_m = a_{m p^(r+1)} + c_p (T_{p^r} a)_{m / p}`, where the second term is present only for `p ∣ m`. -/
lemma heckeSeq_prime_pow_succ {p : ℕ} (hp : p.Prime) (r : ℕ) (a : ℕ → ℂ) (m : ℕ) :
    heckeSeq N k (p ^ (r + 1)) a m = a (m * p ^ (r + 1)) +
      heckeConst N k p * if p ∣ m then heckeSeq N k (p ^ r) a (m / p) else 0 := by
  rw [heckeSeq_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero, one_dvd, ↓reduceIte, one_mul, Nat.div_one, mul_one]
  rw [add_comm]
  congr 1
  split_ifs with hpm
  · obtain ⟨t, rfl⟩ := hpm
    rw [heckeSeq_prime_pow hp, Finset.mul_sum, Nat.mul_div_cancel_left _ hp.pos]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdvd : p ^ (j + 1) ∣ p * t ↔ p ^ j ∣ t := by
      rw [pow_succ, mul_comm (p ^ j) p, Nat.mul_dvd_mul_iff_left hp.pos]
    have hq : p * t * p ^ (r + 1) / (p ^ (j + 1) * p ^ (j + 1)) = t * p ^ r / (p ^ j * p ^ j) := by
      rw [show p * t * p ^ (r + 1) = t * p ^ r * (p * p) by ring,
        show p ^ (j + 1) * p ^ (j + 1) = p ^ j * p ^ j * (p * p) by ring,
        Nat.mul_div_mul_right _ _ (Nat.mul_pos hp.pos hp.pos)]
    simp only [hdvd, hq]
    split_ifs <;> ring
  · rw [mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ p ^ (j + 1) ∣ m := fun h => hpm ((dvd_pow_self p j.succ_ne_zero).trans h)
    simp [this]

/-- The operator `T_p` on coefficient sequences is `heckeCoeff p N k`, for a prime `p`. -/
lemma heckeSeq_prime {p : ℕ} (hp : p.Prime) (a : ℕ → ℂ) : heckeSeq N k p a = heckeCoeff p N k a := by
  funext m
  have h := heckeSeq_prime_pow_succ (N := N) (k := k) hp 0 a m
  rw [zero_add, pow_one, pow_zero, heckeSeq_one] at h
  rw [h, heckeCoeff_eq]

/-- The recursion `T_{p^(r+2)} = T_p T_{p^(r+1)} - c_p T_{p^r}` on coefficient sequences, for a prime `p`. -/
lemma heckeSeq_prime_pow_succ_succ {p : ℕ} (hp : p.Prime) (r : ℕ) (a : ℕ → ℂ) (m : ℕ) :
    heckeSeq N k (p ^ (r + 2)) a m = heckeCoeff p N k (heckeSeq N k (p ^ (r + 1)) a) m -
      heckeConst N k p * heckeSeq N k (p ^ r) a m := by
  rw [heckeCoeff_eq, heckeSeq_prime_pow_succ hp (r + 1), heckeSeq_prime_pow_succ hp r (m := m * p),
    Nat.mul_div_cancel _ hp.pos]
  simp only [dvd_mul_left, ↓reduceIte]
  rw [show m * p * p ^ (r + 1) = m * p ^ (r + 1 + 1) by ring]
  ring

/-- The relation `T_{x y} = T_x T_y` on coefficient sequences, for coprime `x` and `y`. -/
lemma heckeSeq_mul {x y : ℕ} (hxy : x.Coprime y) (a : ℕ → ℂ) :
    heckeSeq N k (x * y) a = heckeSeq N k x (heckeSeq N k y a) := by
  funext m
  rw [heckeSeq, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image (fun u hu v hv h => hxy.mul_injOn_divisors hu hv h), Finset.sum_product,
    heckeSeq]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  have hd₁x : d₁ ∣ x := Nat.dvd_of_mem_divisors hd₁
  have hd₁pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  by_cases hc : d₁.Coprime N ∧ d₁ ∣ m
  · obtain ⟨hcN, m₁, hm₁⟩ := hc
    obtain ⟨x₁, hx₁⟩ := hd₁x
    have hq : m * x / (d₁ * d₁) = m₁ * x₁ :=
      Nat.div_eq_of_eq_mul_left (Nat.mul_pos hd₁pos hd₁pos) (by rw [hm₁, hx₁]; ring)
    simp only [eq_true hcN, eq_true (Dvd.intro m₁ hm₁.symm), and_self, ↓reduceIte]
    rw [hq, heckeSeq, Finset.mul_sum]
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
  · simp only [eq_false hc, ↓reduceIte]
    refine Finset.sum_eq_zero fun d₂ _ => ?_
    have hd : ¬ ((d₁ * d₂).Coprime N ∧ d₁ * d₂ ∣ m) := fun h =>
      hc ⟨(Nat.coprime_mul_iff_left.1 h.1).1, (dvd_mul_right d₁ d₂).trans h.2⟩
    simp only [eq_false hd, ↓reduceIte]

end Sequence

section Operator

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- A cusp form on `Γ₀(N)` is determined by its `q`-expansion coefficients. -/
theorem cuspForm_ext_qCoeff {f g : CuspForm (Γ₀ N) k} (h : ∀ m, qCoeff f m = qCoeff g m) :
    f = g := by
  ext τ
  have hf := ModularForm.hasSum_qExpansion f one_pos (one_mem_strictPeriods N) τ
  have hg := ModularForm.hasSum_qExpansion g one_pos (one_mem_strictPeriods N) τ
  have h' : ∀ m, (qExpansion 1 f).coeff m = (qExpansion 1 g).coeff m := h
  simp only [h'] at hf
  exact hf.unique hg

variable {N k}

omit [NeZero N] in
/-- The coefficient map `f ↦ a_m(f)` commutes with subtraction. -/
lemma qCoeff_sub (f g : CuspForm (Γ₀ N) k) (m : ℕ) : qCoeff (f - g) m = qCoeff f m - qCoeff g m := by
  simp only [qCoeff, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods N) f g,
    map_sub]

omit [NeZero N] in
/-- The coefficient map `f ↦ a_m(f)` commutes with scalar multiplication. -/
lemma qCoeff_smul (c : ℂ) (f : CuspForm (Γ₀ N) k) (m : ℕ) : qCoeff (c • f) m = c * qCoeff f m := by
  simp only [qCoeff, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f,
    PowerSeries.coeff_smul, smul_eq_mul]

variable (N k)

/-- The operator `T_p` of `Langlands.Modular.cuspHeckeT` as a linear map on `CuspForm Γ₀(N) k`. For `p` not prime it is zero by convention. -/
noncomputable def heckeOp (p : ℕ) : Module.End ℂ (CuspForm (Γ₀ N) k) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    { toFun := fun f => cuspHeckeT p N f
      map_add' := fun f g => cuspHeckeT_add p N f g
      map_smul' := fun c f => cuspHeckeT_smul p N c f }
  else 0

/-- The operator `T_{p^r}` for a prime `p`, defined by `T_1 = 1`, `T_p = heckeOp N k p` and `T_{p^(r+2)} = T_p T_{p^(r+1)} - c_p T_{p^r}`, with `c_p = p^(k - 1)` for `p ∤ N` and `c_p = 0` for `p ∣ N`. -/
noncomputable def heckePow (p : ℕ) : ℕ → Module.End ℂ (CuspForm (Γ₀ N) k)
  | 0 => 1
  | 1 => heckeOp N k p
  | r + 2 => heckeOp N k p * heckePow p (r + 1) - heckeConst N k p • heckePow p r

variable {N k}

/-- The linear map `heckeOp N k p` is `cuspHeckeT p N` for a prime `p`. -/
lemma heckeOp_apply (p : ℕ) [Fact p.Prime] (f : CuspForm (Γ₀ N) k) :
    heckeOp N k p f = cuspHeckeT p N f := by
  unfold heckeOp
  split_ifs with hp
  · rfl
  · exact absurd Fact.out hp

/-- The coefficients of `T_p f` are `heckeCoeff p N k` of the coefficients of `f`. -/
lemma qCoeff_heckeOp {p : ℕ} (hp : p.Prime) (f : CuspForm (Γ₀ N) k) :
    qCoeff (heckeOp N k p f) = heckeCoeff p N k (qCoeff f) := by
  have : Fact p.Prime := ⟨hp⟩
  funext m
  rw [heckeOp_apply, qCoeff, coe_cuspHeckeT]
  exact coeff_heckeT p N f m

/-- The operators `T_p` and `T_q` commute. -/
lemma commute_heckeOp (p q : ℕ) : Commute (heckeOp N k p) (heckeOp N k q) := by
  by_cases hp : p.Prime
  · by_cases hq : q.Prime
    · by_cases hpq : p = q
      · subst hpq; exact Commute.refl _
      · refine LinearMap.ext fun f => cuspForm_ext_qCoeff N k fun m => ?_
        simp only [Module.End.mul_apply]
        rw [qCoeff_heckeOp hp, qCoeff_heckeOp hq, qCoeff_heckeOp hq, qCoeff_heckeOp hp,
          heckeCoeff_comm p N q hp hq hpq]
    · simp [heckeOp, hq]
  · simp [heckeOp, hp]

/-- An operator that commutes with each `T_p` commutes with each `T_{p^r}`. -/
lemma commute_heckePow {B : Module.End ℂ (CuspForm (Γ₀ N) k)}
    (hB : ∀ q, Commute B (heckeOp N k q)) (p r : ℕ) : Commute B (heckePow N k p r) := by
  have h : ∀ r, Commute B (heckePow N k p r) ∧ Commute B (heckePow N k p (r + 1)) := by
    intro r
    induction r with
    | zero => exact ⟨Commute.one_right B, hB p⟩
    | succ r ih =>
      refine ⟨ih.2, ?_⟩
      exact ((hB p).mul_right ih.2).sub_right (ih.1.smul_right _)
  exact (h r).1

/-- The operators `T_{p^r}` and `T_{q^s}` commute. -/
lemma commute_heckePow_heckePow (p r q s : ℕ) :
    Commute (heckePow N k p r) (heckePow N k q s) :=
  commute_heckePow (fun t => (commute_heckePow (fun u => commute_heckeOp t u) p r).symm) q s

/-- The operators `T_{p^(r_p)}` commute pairwise. -/
lemma pairwise_commute_heckePow (s : Set ℕ) (r : ℕ → ℕ) :
    s.Pairwise (Function.onFun Commute fun p => heckePow N k p (r p)) :=
  fun p _ q _ _ => commute_heckePow_heckePow p _ q _

variable (N k)

/-- **The Hecke operator `T_n`** on cusp forms of weight `k` for `Γ₀(N)`: the product of the operators `T_{p^r}` of `Langlands.Modular.heckePow` over the prime powers `p^r` that exactly divide `n`. For `n = 0` it is the identity by convention. -/
noncomputable def heckeTn (n : ℕ) : Module.End ℂ (CuspForm (Γ₀ N) k) :=
  n.primeFactors.noncommProd (fun p => heckePow N k p (n.factorization p))
    (pairwise_commute_heckePow _ _)

variable {N k}

/-- An operator that commutes with each `T_p` commutes with each `T_n`. -/
lemma commute_heckeTn {B : Module.End ℂ (CuspForm (Γ₀ N) k)}
    (hB : ∀ q, Commute B (heckeOp N k q)) (n : ℕ) : Commute B (heckeTn N k n) :=
  Finset.noncommProd_commute _ _ _ _ fun p _ => commute_heckePow hB p _

/-- **Commutation of the Hecke operators**: `T_m T_n = T_n T_m` for all `m` and `n`. -/
theorem heckeTn_comm (m n : ℕ) : Commute (heckeTn N k m) (heckeTn N k n) :=
  commute_heckeTn (fun q => (commute_heckeTn (fun u => commute_heckeOp q u) m).symm) n

/-- The relation `T_1 = 1`. -/
@[simp]
theorem heckeTn_one : heckeTn N k 1 = 1 := by
  rw [heckeTn, Finset.noncommProd_congr Nat.primeFactors_one (fun _ _ => rfl)]
  exact Finset.noncommProd_empty _ _

/-- The operator `T_{p^r}` of `heckeTn` is the operator `heckePow N k p r` of the recursion. -/
theorem heckeTn_prime_pow {p : ℕ} (hp : p.Prime) (r : ℕ) : heckeTn N k (p ^ r) = heckePow N k p r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [heckePow]
  · rw [heckeTn, Finset.noncommProd_congr (Nat.primeFactors_prime_pow hr.ne' hp) (fun _ _ => rfl),
      Finset.noncommProd_singleton, hp.factorization_pow, Finsupp.single_eq_same]

/-- The operator `T_p` of `heckeTn` is the operator `cuspHeckeT p N` of `Langlands/Modular/Hecke.lean`. -/
theorem heckeTn_prime (p : ℕ) [Fact p.Prime] (f : CuspForm (Γ₀ N) k) :
    heckeTn N k p f = cuspHeckeT p N f := by
  have h := heckeTn_prime_pow (N := N) (k := k) (Fact.out : p.Prime) 1
  rw [pow_one] at h
  rw [h, heckePow, heckeOp_apply]

/-- The relation `T_{p^(r+2)} = T_p T_{p^(r+1)} - p^(k-1) T_{p^r}` for a prime `p ∤ N`. -/
theorem heckeTn_prime_pow_succ_succ_of_not_dvd {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (r : ℕ) :
    heckeTn N k (p ^ (r + 2)) =
      heckeTn N k p * heckeTn N k (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) • heckeTn N k (p ^ r) := by
  rw [heckeTn_prime_pow hp, heckeTn_prime_pow hp, heckeTn_prime_pow hp,
    ← pow_one p, heckeTn_prime_pow hp, pow_one]
  simp only [heckePow, heckeConst, hpN, ite_false]

/-- The relation `T_{p^(r+1)} = T_p T_{p^r}` for a prime `p ∣ N`, so that `T_{p^r}` is the power `U_p^r`. -/
theorem heckeTn_prime_pow_succ_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ) :
    heckeTn N k (p ^ (r + 1)) = heckeTn N k p * heckeTn N k (p ^ r) := by
  rw [heckeTn_prime_pow hp, heckeTn_prime_pow hp, ← pow_one p, heckeTn_prime_pow hp, pow_one]
  cases r with
  | zero => simp [heckePow]
  | succ r => simp [heckePow, heckeConst, hpN]

/-- For a prime `p ∣ N`, the operator `T_{p^r}` is `U_p^r`. -/
theorem heckeTn_prime_pow_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ) :
    heckeTn N k (p ^ r) = heckeTn N k p ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [heckeTn_prime_pow_succ_of_dvd hp hpN, ih, pow_succ']

/-- **Multiplicativity of the Hecke operators**: `T_{m n} = T_m T_n` for coprime `m` and `n`. -/
theorem heckeTn_mul {m n : ℕ} (hmn : m.Coprime n) :
    heckeTn N k (m * n) = heckeTn N k m * heckeTn N k n := by
  rw [heckeTn, Finset.noncommProd_congr hmn.primeFactors_mul (fun _ _ => rfl)]
  refine (Finset.noncommProd_union_of_disjoint hmn.disjoint_primeFactors _ _).trans ?_
  have hfac := Nat.factorization_mul_of_coprime hmn
  congr 1
  · refine Finset.noncommProd_congr rfl (fun p hp => ?_) _
    have : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
      rw [Nat.support_factorization]
      exact Finset.disjoint_left.mp hmn.disjoint_primeFactors hp)
    rw [hfac, Finsupp.add_apply, this, add_zero]
  · refine Finset.noncommProd_congr rfl (fun p hp => ?_) _
    have : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
      rw [Nat.support_factorization]
      exact Finset.disjoint_right.mp hmn.disjoint_primeFactors hp)
    rw [hfac, Finsupp.add_apply, this, zero_add]

/-- The coefficients of `T_{p^r} f` are `heckeSeq N k (p^r)` of the coefficients of `f`. -/
lemma qCoeff_heckePow {p : ℕ} (hp : p.Prime) (r : ℕ) (f : CuspForm (Γ₀ N) k) :
    qCoeff (heckePow N k p r f) = heckeSeq N k (p ^ r) (qCoeff f) := by
  have h : ∀ r, qCoeff (heckePow N k p r f) = heckeSeq N k (p ^ r) (qCoeff f) ∧
      qCoeff (heckePow N k p (r + 1) f) = heckeSeq N k (p ^ (r + 1)) (qCoeff f) := by
    intro r
    induction r with
    | zero =>
      refine ⟨by simp [heckePow], ?_⟩
      rw [zero_add, pow_one, heckeSeq_prime hp, heckePow, qCoeff_heckeOp hp]
    | succ r ih =>
      refine ⟨ih.2, ?_⟩
      funext m
      rw [heckeSeq_prime_pow_succ_succ hp, heckePow, LinearMap.sub_apply, qCoeff_sub,
        Module.End.mul_apply, qCoeff_heckeOp hp, ih.2, LinearMap.smul_apply, qCoeff_smul, ih.1]
  exact (h r).1

/-- **The `q`-expansion of `T_n f`**: for `n ≥ 1`, the coefficients of `T_n f` are `heckeSeq N k n` of the coefficients of `f`, that is, `a_m(T_n f) = ∑ d^(k - 1) a_{m n / d^2}(f)`, where `d` runs over the common divisors of `m` and `n` that are coprime to `N`. -/
theorem qCoeff_heckeTn {n : ℕ} (hn : n ≠ 0) (f : CuspForm (Γ₀ N) k) :
    qCoeff (heckeTn N k n f) = heckeSeq N k n (qCoeff f) := by
  induction n using Nat.recOnPosPrimePosCoprime generalizing f with
  | prime_pow p r hp _ => rw [heckeTn_prime_pow hp, qCoeff_heckePow hp]
  | zero => exact absurd rfl hn
  | one => simp
  | coprime x y hx hy hxy ihx ihy =>
    rw [heckeTn_mul hxy, Module.End.mul_apply, ihx (by omega), ihy (by omega), heckeSeq_mul hxy]

/-- The coefficient formula `a_m(T_n f) = ∑_{d ∣ gcd(m, n), gcd(d, N) = 1} d^(k - 1) a_{m n / d^2}(f)` for `n ≥ 1`. -/
theorem qCoeff_heckeTn_apply {n : ℕ} (hn : n ≠ 0) (f : CuspForm (Γ₀ N) k) (m : ℕ) :
    qCoeff (heckeTn N k n f) m = ∑ d ∈ n.divisors,
      if d.Coprime N ∧ d ∣ m then (d : ℂ) ^ (k - 1) * qCoeff f (m * n / (d * d)) else 0 := by
  rw [qCoeff_heckeTn hn, heckeSeq]

/-- For coprime `m` and `n ≥ 1`: `a_m(T_n f) = a_{m n}(f)`. -/
theorem qCoeff_heckeTn_of_coprime {m n : ℕ} (hn : n ≠ 0) (hmn : m.Coprime n)
    (f : CuspForm (Γ₀ N) k) : qCoeff (heckeTn N k n f) m = qCoeff f (m * n) := by
  rw [qCoeff_heckeTn_apply hn, Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have : ¬ d ∣ m := fun h => hd1 (Nat.eq_one_of_dvd_coprimes hmn h (Nat.dvd_of_mem_divisors hd))
    simp [this]
  · intro h
    exact absurd (Nat.one_mem_divisors.mpr hn) h

/-- For `n ≥ 1`: `a_1(T_n f) = a_n(f)`. -/
theorem qCoeff_heckeTn_one {n : ℕ} (hn : n ≠ 0) (f : CuspForm (Γ₀ N) k) :
    qCoeff (heckeTn N k n f) 1 = qCoeff f n := by
  rw [qCoeff_heckeTn_of_coprime hn (Nat.coprime_one_left n), one_mul]

/-- A normalized Hecke eigenform is an eigenvector of each `T_n` with `n ≥ 1`, with eigenvalue `a_n`. -/
theorem IsNormalizedHeckeEigenform.heckeTn_eq {f : CuspForm (Γ₀ N) k}
    (hf : IsNormalizedHeckeEigenform N f) {n : ℕ} (hn : n ≠ 0) :
    heckeTn N k n f = qCoeff f n • f := by
  refine cuspForm_ext_qCoeff N k fun m => ?_
  rw [qCoeff_heckeTn hn, hf.heckeSeq_qCoeff hn, qCoeff_smul]

end Operator

section LevelRaise

open ConjAct Pointwise Complex Function

local notation "𝕢" => Periodic.qParam

variable (d : ℕ) [NeZero d]

/-- The matrix `diag(d, 1)` in `GL(2, ℝ)`. -/
noncomputable def raiseMat : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℝ), 0; 0, 1]
    (by simp [Matrix.det_fin_two_of, NeZero.ne d])

/-- The matrix of `raiseMat d` is `diag(d, 1)`. -/
lemma raiseMat_coe : (raiseMat d : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] := rfl

/-- The matrix `diag(d, 1)` acts on `ℍ` by `τ ↦ d τ`. -/
lemma coe_raiseMat_smul (τ : ℍ) : ((raiseMat d • τ : ℍ) : ℂ) = d * τ := by
  rw [coe_smul_upper (raiseMat_coe d) (by exact_mod_cast Nat.pos_of_neZero d) one_pos]
  simp

/-- The formula `(f ∣[k] diag(d, 1))(τ) = d^(k - 1) f(d τ)`. -/
lemma slash_raiseMat_apply {k : ℤ} (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] raiseMat d) τ = (d : ℂ) ^ (k - 1) * f (raiseMat d • τ) := by
  rw [slash_upper_apply (raiseMat_coe d) (by exact_mod_cast Nat.pos_of_neZero d) one_pos]
  push_cast
  simp [mul_comm]

/-- The group `Γ₀(d M)` is contained in `diag(d, 1)⁻¹ Γ₀(M) diag(d, 1)`. -/
lemma gamma0_le_conj_raiseMat (M : ℕ) :
    (Γ₀ (d * M)) ≤ toConjAct (raiseMat d)⁻¹ • (Γ₀ M) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  rw [SetLike.mem_coe, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have hδ : (!![γ 0 0, d * γ 0 1; M * t, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    rw [ht] at hdet
    push_cast at hdet
    linear_combination hdet
  let γ' : SL(2, ℤ) := ⟨_, hδ⟩
  refine ⟨γ', ?_, ?_⟩
  · rw [SetLike.mem_coe, Gamma0_mem]
    change ((M * t : ℤ) : ZMod M) = 0
    simp
  · rw [eq_mul_inv_iff_mul_eq]
    ext i j
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply, raiseMat_coe]
    fin_cases i <;> fin_cases j <;> simp [γ', ht] <;> ring

/-- The group `Γ₀(N)` is contained in `Γ₀(L)` for `L ∣ N`. -/
lemma gamma0_le_of_dvd {L N : ℕ} (h : L ∣ N) : (Γ₀ N) ≤ (Γ₀ L) := by
  refine Subgroup.map_mono fun γ hγ => ?_
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (Int.natCast_dvd_natCast.2 h).trans hγ

/-- The `n`-th power of `q` at `d τ` is the `n d`-th power of `q` at `τ`. -/
lemma qParam_raiseMat_pow (τ : ℍ) (n : ℕ) :
    𝕢 1 (raiseMat d • τ : ℍ) ^ n = 𝕢 1 τ ^ (n * d) := by
  have h : 𝕢 1 (raiseMat d • τ : ℍ) = 𝕢 1 τ ^ d := by
    rw [Periodic.qParam, Periodic.qParam, coe_raiseMat_smul, ← exp_nat_mul]
    congr 1
    ring
  rw [h, ← pow_mul, mul_comm]

/-- The `q`-expansion of `τ ↦ f(d τ)` is `∑ a_{m / d} qᵐ`, with `a_{m / d} = 0` for `d ∤ m`. -/
lemma hasSum_raise (a : ℕ → ℂ) (f : ℍ → ℂ) (hf : ∀ z : ℍ, HasSum (fun n => a n * 𝕢 1 z ^ n) (f z))
    (τ : ℍ) : HasSum (fun m => (if d ∣ m then a (m / d) else 0) * 𝕢 1 τ ^ m)
      (f (raiseMat d • τ)) := by
  have hd : d ≠ 0 := NeZero.ne d
  have h := hf (raiseMat d • τ)
  simp only [qParam_raiseMat_pow] at h
  rw [← hasSum_extend_zero (mul_left_injective₀ hd : Injective (· * d))] at h
  convert h using 1
  funext m
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := hm
    rw [mul_comm d n, (mul_left_injective₀ hd).extend_apply, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd)]
  · rw [extend_apply' _ _ _ (fun ⟨n, hn⟩ => hm ⟨n, by rw [← hn, mul_comm]⟩)]
    simp

variable {k : ℤ} (M : ℕ)

/-- The translate of a modular form by `diag(d, 1)`, restricted to `Γ₀(d M)`, is `τ ↦ d^(k - 1) f(d τ)`. -/
@[simp]
lemma restrict_translate_raiseMat_apply (f : ModularForm (Γ₀ M) k) (τ : ℍ) :
    ModularForm.restrict (gamma0_le_conj_raiseMat d M) (ModularForm.translate f (raiseMat d)) τ =
      (d : ℂ) ^ (k - 1) * f (raiseMat d • τ) := by
  rw [ModularForm.coe_restrict, ModularForm.coe_translate]
  exact slash_raiseMat_apply d f τ

/-- The translate of a cusp form by `diag(d, 1)`, restricted to `Γ₀(d M)`, is `τ ↦ d^(k - 1) f(d τ)`. -/
@[simp]
lemma cuspRestrict_translate_raiseMat_apply (f : CuspForm (Γ₀ M) k) (τ : ℍ) :
    CuspForm.restrict (gamma0_le_conj_raiseMat d M) (CuspForm.translate f (raiseMat d)) τ =
      (d : ℂ) ^ (k - 1) * f (raiseMat d • τ) := by
  rw [CuspForm.coe_restrict, CuspForm.coe_translate]
  exact slash_raiseMat_apply d f τ

/-- The function `f ↦ d^(1 - k) f ∣[k] diag(d, 1)` from modular forms of level `M` to modular forms of level `d M`. -/
noncomputable def levelRaiseMFFun (f : ModularForm (Γ₀ M) k) : ModularForm (Γ₀ (d * M)) k :=
  (d : ℂ) ^ (1 - k) •
    ModularForm.restrict (gamma0_le_conj_raiseMat d M) (ModularForm.translate f (raiseMat d))

/-- The function `f ↦ d^(1 - k) f ∣[k] diag(d, 1)` from cusp forms of level `M` to cusp forms of level `d M`. -/
noncomputable def levelRaiseFun (f : CuspForm (Γ₀ M) k) : CuspForm (Γ₀ (d * M)) k :=
  (d : ℂ) ^ (1 - k) •
    CuspForm.restrict (gamma0_le_conj_raiseMat d M) (CuspForm.translate f (raiseMat d))

/-- The formula `(levelRaiseMFFun d M f)(τ) = f(d τ)`. -/
lemma levelRaiseMFFun_apply (f : ModularForm (Γ₀ M) k) (τ : ℍ) :
    levelRaiseMFFun d M f τ = f (raiseMat d • τ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  change (d : ℂ) ^ (1 - k) * _ = _
  erw [restrict_translate_raiseMat_apply]
  rw [← mul_assoc, ← zpow_add₀ hd]
  simp

/-- The formula `(levelRaiseFun d M f)(τ) = f(d τ)`. -/
lemma levelRaiseFun_apply (f : CuspForm (Γ₀ M) k) (τ : ℍ) :
    levelRaiseFun d M f τ = f (raiseMat d • τ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  change (d : ℂ) ^ (1 - k) * _ = _
  erw [cuspRestrict_translate_raiseMat_apply]
  rw [← mul_assoc, ← zpow_add₀ hd]
  simp

/-- The level raising map `B_d` on modular forms: `(B_d f)(τ) = f(d τ)`, from `ModularForm Γ₀(M) k` to `ModularForm Γ₀(d M) k`. It is `d^(1 - k) f ∣[k] diag(d, 1)`. -/
noncomputable def levelRaiseMF : ModularForm (Γ₀ M) k →ₗ[ℂ] ModularForm (Γ₀ (d * M)) k where
  toFun := levelRaiseMFFun d M
  map_add' f g := by
    ext τ
    simp [levelRaiseMFFun_apply]
  map_smul' c f := by
    ext τ
    simp [levelRaiseMFFun_apply]

/-- The level raising map `B_d` on cusp forms: `(B_d f)(τ) = f(d τ)`, from `CuspForm Γ₀(M) k` to `CuspForm Γ₀(d M) k`. It is `d^(1 - k) f ∣[k] diag(d, 1)`. -/
noncomputable def levelRaise : CuspForm (Γ₀ M) k →ₗ[ℂ] CuspForm (Γ₀ (d * M)) k where
  toFun := levelRaiseFun d M
  map_add' f g := by
    ext τ
    simp [levelRaiseFun_apply]
  map_smul' c f := by
    ext τ
    simp [levelRaiseFun_apply]

/-- The formula `(B_d f)(τ) = f(d τ)` on modular forms. -/
theorem levelRaiseMF_apply (f : ModularForm (Γ₀ M) k) (τ : ℍ) :
    levelRaiseMF d M f τ = f (raiseMat d • τ) :=
  levelRaiseMFFun_apply d M f τ

/-- The formula `(B_d f)(τ) = f(d τ)` on cusp forms. -/
theorem levelRaise_apply (f : CuspForm (Γ₀ M) k) (τ : ℍ) :
    levelRaise d M f τ = f (raiseMat d • τ) :=
  levelRaiseFun_apply d M f τ

/-- **The `q`-expansion of `B_d f`** for a modular form `f`: `a_m(B_d f) = a_{m / d}(f)` for `d ∣ m`, and `a_m(B_d f) = 0` for `d ∤ m`. -/
theorem coeff_levelRaiseMF [NeZero M] (f : ModularForm (Γ₀ M) k) (m : ℕ) :
    (qExpansion 1 (levelRaiseMF d M f)).coeff m =
      if d ∣ m then (qExpansion 1 f).coeff (m / d) else 0 := by
  have hf : ∀ z : ℍ, HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 z ^ n) (f z) :=
    fun z => ModularForm.hasSum_qExpansion f one_pos (one_mem_strictPeriods M) z
  exact (ModularFormClass.qExpansion_coeff_unique (c := fun m => if d ∣ m then (qExpansion 1 f).coeff (m / d) else 0)
    one_pos (one_mem_strictPeriods (d * M))
    (fun τ => by simpa only [smul_eq_mul, levelRaiseMF_apply] using hasSum_raise d _ _ hf τ) m).symm

/-- **The `q`-expansion of `B_d f`** for a cusp form `f`: `a_m(B_d f) = a_{m / d}(f)` for `d ∣ m`, and `a_m(B_d f) = 0` for `d ∤ m`. -/
theorem qCoeff_levelRaise [NeZero M] (f : CuspForm (Γ₀ M) k) (m : ℕ) :
    qCoeff (levelRaise d M f) m = if d ∣ m then qCoeff f (m / d) else 0 := by
  have hf : ∀ z : ℍ, HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 z ^ n) (f z) :=
    fun z => ModularForm.hasSum_qExpansion f one_pos (one_mem_strictPeriods M) z
  show (qExpansion 1 (levelRaise d M f)).coeff m = _
  exact (ModularFormClass.qExpansion_coeff_unique (c := fun m => if d ∣ m then (qExpansion 1 f).coeff (m / d) else 0)
    one_pos (one_mem_strictPeriods (d * M))
    (fun τ => by simpa only [smul_eq_mul, levelRaise_apply] using hasSum_raise d _ _ hf τ) m).symm

end LevelRaise

section OldSpace

/-- The restriction of a cusp form of level `L` to a cusp form of level `N`, for `L ∣ N`, as a linear map. -/
noncomputable def cuspRestrict {k : ℤ} {L N : ℕ} (h : L ∣ N) : CuspForm (Γ₀ L) k →ₗ[ℂ] CuspForm (Γ₀ N) k where
  toFun := CuspForm.restrict (gamma0_le_of_dvd h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (N : ℕ) (k : ℤ)

/-- **The oldspace** of level `N`: the span of the images of the maps `B_d` from `CuspForm Γ₀(M) k` to `CuspForm Γ₀(N) k`, over the pairs `(M, d)` with `d ≥ 1`, `d M ∣ N` and `M < N`. -/
noncomputable def oldSpace : Submodule ℂ (CuspForm (Γ₀ N) k) :=
  ⨆ (M : ℕ) (d : ℕ) (_ : NeZero d) (h : d * M ∣ N) (_ : M < N),
    LinearMap.range ((cuspRestrict h).comp (levelRaise d M))

variable {N k}

/-- The form `B_d f` is in the oldspace of level `N`, for `f` of level `M` with `d M ∣ N` and `M < N`. -/
theorem levelRaise_mem_oldSpace {M d : ℕ} [NeZero d] (h : d * M ∣ N) (hM : M < N)
    (f : CuspForm (Γ₀ M) k) : cuspRestrict h (levelRaise d M f) ∈ oldSpace N k := by
  refine Submodule.mem_iSup_of_mem M (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem
    inferInstance (Submodule.mem_iSup_of_mem h (Submodule.mem_iSup_of_mem hM ?_))))
  exact ⟨f, rfl⟩

end OldSpace

end Langlands.Modular
