/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.Semistable

/-!
# The functional equation of $\log [\cdot]$ in $A_{cris}$

This file proves $\log [a b] = \log [a] + \log [b]$ in $A_{cris}(R)$ for $a$, $b$ of untilt $1$. It gives $\varphi(t) = p t$ for $t = \log [\varepsilon]$ and the cocycle relation of the Kummer element $\log [\eta_\sigma]$.

## Main definitions

* `logPoly`: the truncated logarithm series $\sum_{j < N} a_j q^{j+1}$ in $A[X]$.
* `logDefect`: the defect $\mathrm{logPoly}((1 + x X)(1 + y X) - 1) - \mathrm{logPoly}(x X) - \mathrm{logPoly}(y X)$.
* `dpowLoc`: the divided power $w^k / k!$ in the localization $W(R^\flat)[1/p]$.
* `logCoeff`: the coefficient $(-1)^j j! / (j+1)!$ of the logarithm series.
* `pPowAcrisZero`: the subgroup $p^m A^0$ of $W(R^\flat)[1/p]$.

## Main results

* `logTrunc_defect_mem`: the defect of the truncated logarithm at $X = 1$ is in an additive subgroup $J$ if all its terms of degree more than $N$ are in $J$.
* `logPartial_mul_sub_mem`: for $N > 2 p m$, the defect of the partial sums of $\log$ is in $p^m A^0$.
* `logTeich_mul`: the functional equation $\log [a b] = \log [a] + \log [b]$ in $A_{cris}(R)$.
* `logTeich_one`: $\log [1] = 0$.
* `logTeich_pow`: $\log [\varepsilon^n] = n \log [\varepsilon]$.
* `acrisFrob_logTeich_eq`: $\varphi(\log [\varepsilon]) = p \log [\varepsilon]$.
* `kummerLog_mul`: the cocycle relation $\log [\eta_{\sigma \tau}] = \sigma \log [\eta_\tau] + \log [\eta_\sigma]$.
* `kummerLog_one`: $\log [\eta_1] = 0$.

## Implementation notes

The proof of `logTeich_mul` works with polynomials over $W(R^\flat)[1/p]$. The derivative of the defect is divisible by $X^N$, so its coefficients of degree at most $N$ are zero. Each coefficient of degree more than $N$ is in $p^m A^0$ by the divided power estimate `logCoeff_mul_mem`. Thus the defect of the partial sums goes to $0$ in the $p$-adic topology.

The relation $g t = \chi(g) t$ for the cyclotomic character $\chi$ is not proved here. It needs $\log [\varepsilon^a] = a \log [\varepsilon]$ for $a \in \mathbb{Z}_p$, thus a continuity argument. This file only proves the case $a \in \mathbb{N}$.

The statement $t \neq 0$ is not proved here.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

section Defect

open Polynomial

variable {A : Type*} [CommRing A] (a : ℕ → A) (N : ℕ)

/-- The truncated logarithm $\sum_{j < N} a_j q^{j+1}$ of a polynomial $q$. -/
noncomputable def logPoly (q : A[X]) : A[X] :=
  ∑ j ∈ Finset.range N, C (a j) * q ^ (j + 1)

/-- If $a_j (j + 1) = (-1)^j$, then the derivative of the truncated logarithm of $q$ is $q' \sum_{j < N} (-q)^j$. -/
theorem derivative_logPoly (ha : ∀ j, a j * ((j + 1 : ℕ) : A) = (-1) ^ j) (q : A[X]) :
    derivative (logPoly a N q) = derivative q * ∑ j ∈ Finset.range N, (-q) ^ j := by
  rw [logPoly, derivative_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg C (ha j)
  rw [map_mul, map_pow, map_neg, map_one] at h
  rw [derivative_C_mul, derivative_pow, Nat.add_sub_cancel, neg_pow]
  linear_combination (q ^ j * derivative q) * h

/-- The geometric sum $(\sum_{j < N} (-q)^j)(1 + q) = 1 - (-q)^N$. -/
theorem geom_neg_mul (q : A) :
    (∑ j ∈ Finset.range N, (-q) ^ j) * (1 + q) = 1 - (-q) ^ N := by
  linear_combination -(geom_sum_mul (-q) N)

/-- The defect $\ell_N((1 + x X)(1 + y X) - 1) - \ell_N(x X) - \ell_N(y X)$ of the truncated logarithm $\ell_N$. -/
noncomputable def logDefect (x y : A) : A[X] :=
  logPoly a N ((1 + C x * X) * (1 + C y * X) - 1) - logPoly a N (C x * X) -
    logPoly a N (C y * X)

/-- The power $X^N$ divides the derivative of the defect of the truncated logarithm. -/
theorem X_pow_dvd_derivative_logDefect (ha : ∀ j, a j * ((j + 1 : ℕ) : A) = (-1) ^ j)
    (x y : A) : X ^ N ∣ derivative (logDefect a N x y) := by
  have hG : derivative (logDefect a N x y) =
      derivative ((1 + C x * X) * (1 + C y * X) - 1) *
        ∑ j ∈ Finset.range N, (-((1 + C x * X) * (1 + C y * X) - 1)) ^ j -
      C x * ∑ j ∈ Finset.range N, (-(C x * X)) ^ j -
      C y * ∑ j ∈ Finset.range N, (-(C y * X)) ^ j := by
    rw [logDefect, derivative_sub, derivative_sub, derivative_logPoly a N ha,
      derivative_logPoly a N ha, derivative_logPoly a N ha, derivative_C_mul_X,
      derivative_C_mul_X]
  have hdz : derivative ((1 + C x * X) * (1 + C y * X) - 1) =
      C x * (1 + C y * X) + (1 + C x * X) * C y := by
    simp only [derivative_sub, derivative_mul, derivative_add, derivative_one, derivative_C,
      derivative_X]
    ring
  have h1 := geom_neg_mul N ((1 + C x * X) * (1 + C y * X) - 1)
  have h2 := geom_neg_mul N (C x * X)
  have h3 := geom_neg_mul N (C y * X)
  have hz : (-((1 + C x * X) * (1 + C y * X) - 1)) ^ N =
      X ^ N * (-(C x + C y + C x * C y * X)) ^ N := by
    rw [← mul_pow]
    ring_nf
  have hα : (-(C x * X)) ^ N = X ^ N * (-C x) ^ N := by
    rw [← mul_pow]
    ring_nf
  have hβ : (-(C y * X)) ^ N = X ^ N * (-C y) ^ N := by
    rw [← mul_pow]
    ring_nf
  set G' := derivative (logDefect a N x y)
  set dz := derivative ((1 + C x * X) * (1 + C y * X) - 1)
  set Sz := ∑ j ∈ Finset.range N, (-((1 + C x * X) * (1 + C y * X) - 1)) ^ j
  set Su := ∑ j ∈ Finset.range N, (-(C x * X)) ^ j
  set Sv := ∑ j ∈ Finset.range N, (-(C y * X)) ^ j
  have key : (1 + C x * X) * (1 + C y * X) * G' = X ^ N *
      (-dz * (-(C x + C y + C x * C y * X)) ^ N + C x * (1 + C y * X) * (-C x) ^ N +
        C y * (1 + C x * X) * (-C y) ^ N) := by
    linear_combination ((1 + C x * X) * (1 + C y * X)) * hG + dz * h1 - (C x * (1 + C y * X)) * h2 -
      (C y * (1 + C x * X)) * h3 + hdz -
      dz * hz + (C x * (1 + C y * X)) * hα + (C y * (1 + C x * X)) * hβ
  have hsplit : G' = Su * Sv * ((1 + C x * X) * (1 + C y * X) * G') +
      X ^ N * (((-C x) ^ N + (-C y) ^ N - X ^ N * (-C x) ^ N * (-C y) ^ N) * G') := by
    linear_combination -(Sv * (1 + C y * X) * G') * h2 - ((1 - (-(C x * X)) ^ N) * G') * h3 +
      (G' * (1 - (-(C y * X)) ^ N)) * hα + (G' * (1 - X ^ N * (-C x) ^ N)) * hβ
  rw [hsplit, key]
  exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) (dvd_mul_right _ _)

/-- If $a_j (j + 1) = (-1)^j$ and the integers $1, \dots, N$ are units, then the coefficients of degree at most $N$ of the defect of the truncated logarithm are zero. -/
theorem coeff_logDefect_eq_zero (ha : ∀ j, a j * ((j + 1 : ℕ) : A) = (-1) ^ j)
    (hu : ∀ k < N, IsUnit ((k + 1 : ℕ) : A)) (x y : A) {d : ℕ} (hd : d ≤ N) :
    (logDefect a N x y).coeff d = 0 := by
  rcases d with _ | k
  · rw [coeff_zero_eq_eval_zero]
    simp [logDefect, logPoly, eval_finsetSum]
  · obtain ⟨Q, hQ⟩ := X_pow_dvd_derivative_logDefect a N ha x y
    have h := congrArg (fun P => P.coeff k) hQ
    simp only [coeff_derivative, coeff_X_pow_mul', show ¬N ≤ k by omega, ↓reduceIte] at h
    have hk := hu k (by omega)
    push_cast at hk
    exact (hk.mul_left_eq_zero).1 h

/-- The power $((1 + x X)(1 + y X) - 1)^n$ as a sum of monomials. -/
theorem pow_eq_sum_monomial (x y : A) (n : ℕ) :
    ((1 + C x * X) * (1 + C y * X) - 1) ^ n = ∑ k ∈ Finset.range (n + 1),
      C ((x * y) ^ k * (x + y) ^ (n - k) * (n.choose k : A)) * X ^ (n + k) := by
  have : (1 + C x * X) * (1 + C y * X) - 1 = X * (C (x * y) * X + C (x + y)) := by
    simp only [map_mul, map_add]
    ring
  rw [this, mul_pow, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_pow, map_natCast, pow_add, mul_pow]
  ring

/-- Let $J$ be an additive subgroup of $A$. If the terms $a_j \binom{j+1}{k} (x y)^k (x + y)^{j+1-k}$ with $j < N$, $k \le j + 1$ and $j + 1 + k = d$ are in $J$, then the coefficient of degree $d > N$ of the defect is in $J$. -/
theorem coeff_logDefect_mem (x y : A) (J : AddSubgroup A) {d : ℕ} (hd : N < d)
    (h : ∀ j < N, ∀ k ≤ j + 1, j + 1 + k = d →
      a j * ((x * y) ^ k * (x + y) ^ (j + 1 - k) * ((j + 1).choose k : A)) ∈ J) :
    (logDefect a N x y).coeff d ∈ J := by
  have hlin : ∀ (z : A) (j : ℕ), j < N → ((C z * X) ^ (j + 1)).coeff d = 0 := by
    intro z j hj
    rw [mul_pow, ← map_pow, coeff_C_mul_X_pow]
    simp [show d ≠ j + 1 by omega]
  simp only [logDefect, logPoly, coeff_sub, finsetSum_coeff, coeff_C_mul]
  have hx : ∑ j ∈ Finset.range N, a j * ((C x * X) ^ (j + 1)).coeff d = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hlin x j (Finset.mem_range.1 hj), mul_zero]
  have hy : ∑ j ∈ Finset.range N, a j * ((C y * X) ^ (j + 1)).coeff d = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hlin y j (Finset.mem_range.1 hj), mul_zero]
  rw [hx, hy, sub_zero, sub_zero]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  rw [pow_eq_sum_monomial, finsetSum_coeff, Finset.mul_sum]
  refine AddSubgroup.sum_mem _ fun k hk => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with hdk
  · exact h j (Finset.mem_range.1 hj) k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hdk.symm
  · rw [mul_zero]
    exact J.zero_mem

/-- The value at $1$ of the defect of the truncated logarithm. -/
theorem eval_one_logDefect (x y : A) :
    (logDefect a N x y).eval 1 = ∑ j ∈ Finset.range N, a j * ((1 + x) * (1 + y) - 1) ^ (j + 1) -
      ∑ j ∈ Finset.range N, a j * x ^ (j + 1) -
        ∑ j ∈ Finset.range N, a j * y ^ (j + 1) := by
  simp [logDefect, logPoly, eval_finsetSum]

/-- The truncated functional equation of the logarithm. Assume $a_j (j + 1) = (-1)^j$ and that $1, \dots, N$ are units. Let $J$ be an additive subgroup of $A$ that contains the terms $a_j \binom{j+1}{k} (x y)^k (x + y)^{j+1-k}$ with $j < N$, $k \le j + 1$ and $N < j + 1 + k$. Then $J$ contains $\ell_N((1 + x)(1 + y) - 1) - \ell_N(x) - \ell_N(y)$, where $\ell_N(w) = \sum_{j < N} a_j w^{j+1}$. -/
theorem logTrunc_defect_mem (ha : ∀ j, a j * ((j + 1 : ℕ) : A) = (-1) ^ j)
    (hu : ∀ k < N, IsUnit ((k + 1 : ℕ) : A)) (x y : A) (J : AddSubgroup A)
    (h : ∀ j < N, ∀ k ≤ j + 1, N < j + 1 + k →
      a j * ((x * y) ^ k * (x + y) ^ (j + 1 - k) * ((j + 1).choose k : A)) ∈ J) :
    ∑ j ∈ Finset.range N, a j * ((1 + x) * (1 + y) - 1) ^ (j + 1) -
      ∑ j ∈ Finset.range N, a j * x ^ (j + 1) -
        ∑ j ∈ Finset.range N, a j * y ^ (j + 1) ∈ J := by
  rw [← eval_one_logDefect, eval_eq_sum_range]
  refine AddSubgroup.sum_mem _ fun d _ => ?_
  rw [one_pow, mul_one]
  rcases le_or_gt d N with hd | hd
  · rw [coeff_logDefect_eq_zero a N ha hu x y hd]
    exact J.zero_mem
  · exact coeff_logDefect_mem a N x y J hd fun j hj k hk hjk => h j hj k hk (by omega)

end Defect

set_option hygiene false in
/-- The ring $W(R^\flat)[1/p]$. -/
local notation "LocW[" R ", " p "]" => Localization.Away (p : WittVector p (PreTilt R p))

section LogMul

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- The divided power $w^k / k!$ in $W(R^\flat)[1/p]$ of $w \in W(R^\flat)$. -/
noncomputable def dpowLoc (w : WittVector p (PreTilt R p)) (k : ℕ) : LocW[R, p] :=
  (((isUnit_factorial_loc (R := R) k).unit)⁻¹ : (LocW[R, p])ˣ) * algebraMap _ _ w ^ k

omit [IsAdicComplete (span {(p : R)}) R] in
/-- The defining property of the divided power: $k! \cdot w^{[k]} = w^k$. -/
theorem factorial_mul_dpowLoc (w : WittVector p (PreTilt R p)) (k : ℕ) :
    (k.factorial : LocW[R, p]) * dpowLoc w k = algebraMap _ _ w ^ k :=
  Units.mul_inv_cancel_left ((isUnit_factorial_loc (R := R) k).unit) _

/-- For $w \in \ker \theta$, the divided power $w^k / k!$ is in $A_{cris}^0(R)$. -/
theorem dpowLoc_mem {w : WittVector p (PreTilt R p)} (hw : w ∈ RingHom.ker (fontaineTheta R p))
    (k : ℕ) : dpowLoc w k ∈ acrisZero R p :=
  Algebra.subset_adjoin ⟨w, hw, k, factorial_mul_dpowLoc w k⟩

variable (R p) in
/-- The coefficient $a_j = (-1)^j j! / (j+1)! = (-1)^j / (j + 1)$ of the series of the logarithm, in $W(R^\flat)[1/p]$. -/
noncomputable def logCoeff (j : ℕ) : LocW[R, p] :=
  (-1) ^ j * (j.factorial : LocW[R, p]) *
    (((isUnit_factorial_loc (R := R) (j + 1)).unit)⁻¹ : (LocW[R, p])ˣ)

omit [IsAdicComplete (span {(p : R)}) R] in
/-- The relation $a_j (j + 1)! = (-1)^j j!$. -/
theorem logCoeff_mul_factorial (j : ℕ) :
    logCoeff R p j * ((j + 1).factorial : LocW[R, p]) = (-1) ^ j * (j.factorial : LocW[R, p]) := by
  have h := Units.inv_mul ((isUnit_factorial_loc (R := R) (p := p) (j + 1)).unit)
  rw [IsUnit.unit_spec] at h
  rw [logCoeff]
  linear_combination ((-1) ^ j * (j.factorial : LocW[R, p])) * h

omit [IsAdicComplete (span {(p : R)}) R] in
/-- The relation $a_j (j + 1) = (-1)^j$. -/
theorem logCoeff_mul (j : ℕ) : logCoeff R p j * ((j + 1 : ℕ) : LocW[R, p]) = (-1) ^ j := by
  have h := Units.inv_mul ((isUnit_factorial_loc (R := R) (p := p) (j + 1)).unit)
  rw [IsUnit.unit_spec] at h
  have e : ((j + 1).factorial : LocW[R, p]) = ((j + 1 : ℕ) : LocW[R, p]) * j.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  rw [logCoeff]
  linear_combination (-1 : LocW[R, p]) ^ j * h - ((-1 : LocW[R, p]) ^ j *
    (((isUnit_factorial_loc (R := R) (p := p) (j + 1)).unit⁻¹ : (LocW[R, p])ˣ) :
      LocW[R, p])) * e

omit [IsAdicComplete (span {(p : R)}) R] in
/-- Each integer $k + 1$ is a unit in $W(R^\flat)[1/p]$. -/
theorem isUnit_succ_loc (k : ℕ) : IsUnit ((k + 1 : ℕ) : LocW[R, p]) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_factorial k.succ_pos le_rfl))
    (isUnit_factorial_loc (R := R) (k + 1))

/-- The $j$-th term of the series of $\log [\varepsilon]$ is $a_j ([\varepsilon] - 1)^{j+1}$. -/
theorem coe_logTerm {ε : PreTilt R p} (hε : ε.untilt = 1) (j : ℕ) :
    (logTerm hε j : LocW[R, p]) =
      logCoeff R p j * algebraMap _ _ (teichmuller p ε - 1) ^ (j + 1) := by
  change (-1) ^ j * (j.factorial : LocW[R, p]) * logDiv ε (j + 1) = _
  rw [logDiv, logCoeff]
  ring

variable (R p) in
/-- The additive subgroup $p^m A_{cris}^0(R)$ of $W(R^\flat)[1/p]$. -/
noncomputable def pPowAcrisZero (m : ℕ) : AddSubgroup (LocW[R, p]) where
  carrier := {w | ∃ c ∈ acrisZero R p, w = (p : LocW[R, p]) ^ m * c}
  zero_mem' := ⟨0, Subalgebra.zero_mem _, (mul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', Subalgebra.add_mem _ hc hc', (mul_add _ _ _).symm⟩
  neg_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨-c, Subalgebra.neg_mem _ hc, (mul_neg _ _).symm⟩

/-- For $p m \le j$ and $k \le j + 1$, the term $a_j \binom{j+1}{k} (x y)^k (x + y)^{j+1-k}$ with $x = [a] - 1$ and $y = [b] - 1$ is in $p^m A_{cris}^0(R)$. -/
theorem logCoeff_mul_mem {a b : PreTilt R p} (ha : a.untilt = 1) (hb : b.untilt = 1)
    {m j k : ℕ} (hj : p * m ≤ j) (hk : k ≤ j + 1) :
    logCoeff R p j * ((algebraMap _ _ (teichmuller p a - 1) *
      algebraMap _ _ (teichmuller p b - 1)) ^ k * (algebraMap _ _ (teichmuller p a - 1) +
        algebraMap _ _ (teichmuller p b - 1)) ^ (j + 1 - k) *
          ((j + 1).choose k : LocW[R, p])) ∈ pPowAcrisZero R p m := by
  obtain ⟨c, hc⟩ := p_pow_dvd_factorial p hj
  set x : WittVector p (PreTilt R p) := teichmuller p a - 1
  set y : WittVector p (PreTilt R p) := teichmuller p b - 1
  have hx : x ∈ RingHom.ker (fontaineTheta R p) := teichmuller_sub_one_mem_ker ha
  have hy : y ∈ RingHom.ker (fontaineTheta R p) := teichmuller_sub_one_mem_ker hb
  refine ⟨(-1) ^ j * (c : LocW[R, p]) * dpowLoc x k * dpowLoc (x + y) (j + 1 - k) *
    algebraMap _ _ y ^ k, ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _
        (Subalgebra.one_mem _)) _) (Subalgebra.natCast_mem _ _)) (dpowLoc_mem hx k))
          (dpowLoc_mem (Ideal.add_mem _ hx hy) _)) ?_
    exact Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _
  · have f1 := factorial_mul_dpowLoc x k
    have f2 := factorial_mul_dpowLoc (x + y) (j + 1 - k)
    rw [map_add] at f2
    have f3 : ((j + 1).choose k : LocW[R, p]) * (k.factorial : LocW[R, p]) *
        ((j + 1 - k).factorial : LocW[R, p]) = ((j + 1).factorial : LocW[R, p]) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hk]
    have f4 := logCoeff_mul_factorial (R := R) (p := p) j
    have f5 : (j.factorial : LocW[R, p]) = (p : LocW[R, p]) ^ m * c := by
      rw [hc, Nat.cast_mul, Nat.cast_pow]
    set X1 := algebraMap (WittVector p (PreTilt R p)) (LocW[R, p]) x
    set Y1 := algebraMap (WittVector p (PreTilt R p)) (LocW[R, p]) y
    set Γ := dpowLoc x k
    set Γ' := dpowLoc (x + y) (j + 1 - k)
    set C := ((j + 1).choose k : LocW[R, p])
    set A := logCoeff R p j
    linear_combination (-(A * C * Y1 ^ k * (X1 + Y1) ^ (j + 1 - k))) * f1 -
      (A * C * Y1 ^ k * (k.factorial : LocW[R, p]) * Γ) * f2 + (A * Y1 ^ k * Γ * Γ') * f3 +
      (Y1 ^ k * Γ * Γ') * f4 + ((-1) ^ j * Y1 ^ k * Γ * Γ') * f5

/-- The truncated functional equation in $A_{cris}^0(R)$: if $2 p m < N$, then $s_N(a b) - s_N(a) - s_N(b) \in p^m A_{cris}^0(R)$, where $s_N(\varepsilon)$ is the $N$-th partial sum of the series of $\log [\varepsilon]$. -/
theorem logPartial_mul_sub_mem {a b : PreTilt R p} (ha : a.untilt = 1) (hb : b.untilt = 1)
    (hab : (a * b).untilt = 1) {m N : ℕ} (hN : 2 * (p * m) < N) :
    logPartial hab N - logPartial ha N - logPartial hb N ∈
      (span {(p : acrisZero R p)} ^ m • ⊤ : Submodule (acrisZero R p) (acrisZero R p)) := by
  set x := algebraMap (WittVector p (PreTilt R p)) (LocW[R, p]) (teichmuller p a - 1)
  set y := algebraMap (WittVector p (PreTilt R p)) (LocW[R, p]) (teichmuller p b - 1)
  have hz : algebraMap (WittVector p (PreTilt R p)) (LocW[R, p]) (teichmuller p (a * b) - 1) =
      (1 + x) * (1 + y) - 1 := by
    simp only [x, y, map_mul, map_sub, map_one]
    ring
  have e : ((logPartial hab N - logPartial ha N - logPartial hb N : acrisZero R p) :
      LocW[R, p]) = ∑ j ∈ Finset.range N, logCoeff R p j * ((1 + x) * (1 + y) - 1) ^ (j + 1) -
        ∑ j ∈ Finset.range N, logCoeff R p j * x ^ (j + 1) -
          ∑ j ∈ Finset.range N, logCoeff R p j * y ^ (j + 1) := by
    simp only [logPartial, Subalgebra.coe_sub, AddSubmonoidClass.coe_finsetSum, coe_logTerm, hz]
    rfl
  have hmem : ((logPartial hab N - logPartial ha N - logPartial hb N : acrisZero R p) :
      LocW[R, p]) ∈ pPowAcrisZero R p m := by
    rw [e]
    refine logTrunc_defect_mem (logCoeff R p) N logCoeff_mul (fun k _ => isUnit_succ_loc k) x y
      _ fun j _ k hk hjk => logCoeff_mul_mem ha hb ?_ hk
    generalize p * m = r at hN
    omega
  obtain ⟨c, hc, hce⟩ := hmem
  have : logPartial hab N - logPartial ha N - logPartial hb N =
      (p : acrisZero R p) ^ m * ⟨c, hc⟩ := Subtype.ext (by rw [hce]; rfl)
  rw [this]
  exact @mem_span_p_pow_smul_top (acrisZero R p) (Subalgebra.toCommRing _) p m _

/-- The functional equation of the logarithm in $A_{cris}(R)$: $\log [a b] = \log [a] + \log [b]$ for $a, b \in R^\flat$ with untilt $1$. -/
theorem logTeich_mul {a b : PreTilt R p} (ha : a.untilt = 1) (hb : b.untilt = 1)
    (hab : (a * b).untilt = 1) : logTeich hab = logTeich ha + logTeich hb := by
  have h0 := AdicCompletion.mk_zero_of (span {(p : acrisZero R p)}) (acrisZero R p)
    (⟨_, isAdicCauchy_logPartial hab⟩ - ⟨_, isAdicCauchy_logPartial ha⟩ -
      ⟨_, isAdicCauchy_logPartial hb⟩) ⟨0, fun n _ => ⟨2 * n + 1, by omega, n, le_rfl,
        logPartial_mul_sub_mem ha hb hab (by
          have hp := (Fact.out : p.Prime).two_le
          nlinarith)⟩⟩
  rw [← sub_eq_zero, ← sub_sub]
  exact h0

end LogMul

section LogConsequences

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- The element $\log [\varepsilon]$ depends only on $\varepsilon$. -/
theorem logTeich_congr {ε ε' : PreTilt R p} (h : ε = ε') (hε : ε.untilt = 1)
    (hε' : ε'.untilt = 1) : logTeich hε = logTeich hε' := by
  subst h
  rfl

/-- The relation $\log [1] = 0$. -/
theorem logTeich_one (h : (1 : PreTilt R p).untilt = 1) : logTeich h = 0 := by
  have h1 : ((1 : PreTilt R p) * 1).untilt = 1 := by rw [mul_one]; exact h
  have := logTeich_mul h h h1
  rw [logTeich_congr (mul_one 1) h1 h] at this
  exact left_eq_add.1 this

/-- The relation $\log [\varepsilon^n] = n \log [\varepsilon]$. -/
theorem logTeich_pow {ε : PreTilt R p} (hε : ε.untilt = 1) (n : ℕ) (hn : (ε ^ n).untilt = 1) :
    logTeich hn = n • logTeich hε := by
  induction n with
  | zero =>
    rw [zero_smul]
    exact (logTeich_congr (pow_zero ε) hn (by rw [map_one])).trans (logTeich_one _)
  | succ n ih =>
    have hn' : (ε ^ n).untilt = 1 := by rw [map_pow, hε, one_pow]
    have hm : (ε ^ n * ε).untilt = 1 := by rw [map_mul, hn', hε, one_mul]
    rw [logTeich_congr (pow_succ ε n) hn hm, logTeich_mul hn' hε hm, ih hn', succ_nsmul]

/-- The Frobenius of $A_{cris}(R)$ sends $t = \log [\varepsilon]$ to $p t$. -/
theorem acrisFrob_logTeich_eq {ε : PreTilt R p} (hε : ε.untilt = 1) :
    acrisFrob R p (logTeich hε) = (p : Acris R p) * logTeich hε := by
  rw [acrisFrob_logTeich, logTeich_pow hε p, nsmul_eq_mul]

end LogConsequences

section KummerCocycle

variable {p : ℕ} [Fact p.Prime]

/-- The cocycle relation $\log [\eta_{\sigma \tau}] = \sigma(\log [\eta_\tau]) + \log [\eta_\sigma]$ in $A_{cris}(\mathcal{O}_{\mathbb{C}_p})$. -/
theorem kummerLog_mul (σ τ : Field.absoluteGaloisGroup ℚ_[p]) :
    kummerLog (σ * τ) = σ • kummerLog τ + kummerLog σ := by
  have h1 := untilt_preTiltMap_eq_one
    (MulSemiringAction.toRingHom _ (PadicComplexInt p) σ) (untilt_kummerFlat τ)
  have h2 : (preTiltMap p (MulSemiringAction.toRingHom _ (PadicComplexInt p) σ) (kummerFlat τ) *
      kummerFlat σ).untilt = 1 := by rw [map_mul, h1, untilt_kummerFlat, one_mul]
  rw [kummerLog, logTeich_congr (kummerFlat_mul σ τ) _ h2, logTeich_mul h1 (untilt_kummerFlat σ),
    kummerLog, smul_logTeich]
  rfl

/-- The relation $\log [\eta_1] = 0$. -/
theorem kummerLog_one : kummerLog (1 : Field.absoluteGaloisGroup ℚ_[p]) = 0 := by
  have := kummerLog_mul (1 : Field.absoluteGaloisGroup ℚ_[p]) 1
  rw [mul_one, one_smul] at this
  exact left_eq_add.1 this

end KummerCocycle

end Langlands.Padic
