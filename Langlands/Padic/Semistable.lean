/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.Crystalline
import Langlands.Padic.DeRhamNonzero
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Towards semistable representations: the elements $\varepsilon$, $\log [\varepsilon]$ and the Kummer cocycle

This file collects the first facts on the way to the ring $B_{st}$ and to semistable representations of $G_{\mathbb{Q}_p}$.

## Main definitions

* `kummerRoots`: the roots of unity $\sigma(p^{1/p^n}) / p^{1/p^n}$ in $\mathbb{C}_p$.
* `kummerInt`: the same roots of unity as elements of $\mathcal{O}_{\mathbb{C}_p}$.
* `kummerFlat`: the Kummer element $\eta_\sigma = \sigma(p^\flat) / p^\flat$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$.
* `kummerLog`: the element $\log [\eta_\sigma]$ of $A_{cris}(\mathcal{O}_{\mathbb{C}_p})$.

## Main results

* `epsCp_ne_one`: the element $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \dots)$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$ is not $1$.
* `adicMap_mk`: the map of adic completions sends the class of a Cauchy sequence to the class of its image.
* `acrisMap_logTeich`: a ring map $f : R \to S$ sends $\log [\varepsilon]$ to $\log [f(\varepsilon)]$.
* `smul_logTeich`: the Galois action sends $\log [\varepsilon]$ to $\log [g \varepsilon]$.
* `acrisFrob_logTeich`: the Frobenius of $A_{cris}(R)$ sends $\log [\varepsilon]$ to $\log [\varepsilon^p]$.
* `preTiltMap_pFlat`: $\sigma(p^\flat) = \eta_\sigma p^\flat$.
* `kummerFlat_mul`: the cocycle relation $\eta_{\sigma \tau} = \sigma(\eta_\tau) \eta_\sigma$.

## Implementation notes

The functional equation $\log [a b] = \log [a] + \log [b]$ in $A_{cris}$ is not proved here. Without it, this file does not prove $\varphi(t) = p t$, $g t = \chi(g) t$, or $\log [\eta_\sigma] = c(\sigma) t$.

The statement $t \neq 0$ is not proved here. Thus the nontriviality of $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ stays open.

This file does not define $B_{st}$, its Frobenius, its Galois action, `IsSemistableQp` or `IsPotentiallySemistableQp`. These need the functional equation of $\log$.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

set_option hygiene false in
/-- The ring $W(R^\flat)[1/p]$. -/
local notation "LocW[" R ", " p "]" => Localization.Away (p : WittVector p (PreTilt R p))

section EpsNeOne

variable {p : ℕ} [Fact p.Prime]

/-- If $x \equiv 1$ modulo $p$ in $\mathcal{O}_{\mathbb{C}_p}$, then $x^p \equiv 1$ modulo $p^2$. -/
theorem pow_p_sub_one_mem {x : PadicComplexInt p} (hx : x - 1 ∈ span {(p : PadicComplexInt p)}) :
    x ^ p - 1 ∈ span {(p : PadicComplexInt p)} ^ 2 := by
  set I := span {(p : PadicComplexInt p)}
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by ring⟩
  have hy : y ∈ I := by simpa using hx
  rw [add_pow, Finset.sum_range_succ', pow_zero, one_pow, Nat.choose_zero_right, Nat.cast_one,
    mul_one, mul_one, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [one_pow, mul_one]
  have hi : i + 1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.1 hi)
  rcases hi.lt_or_eq with hlt | heq
  · have hdvd : p ∣ p.choose (i + 1) :=
      Nat.Prime.dvd_choose_self (Fact.out : p.Prime) i.succ_ne_zero hlt
    have hc : ((p.choose (i + 1) : ℕ) : PadicComplexInt p) ∈ I := by
      obtain ⟨m, hm⟩ := hdvd
      rw [hm, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [pow_two, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hy) hc
  · rw [heq, Nat.choose_self, Nat.cast_one, mul_one]
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact Ideal.pow_le_pow_right h2 (Ideal.pow_mem_pow hy p)

/-- The element $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \ldots)$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$ is not $1$. If $\varepsilon = 1$, then $\zeta_{p^2} \equiv 1$ modulo $p$, so $\zeta_p = \zeta_{p^2}^p \equiv 1$ modulo $p^2$, and $p = \sum_{i < p} (1 - \zeta_p^i)$ is in $p^2 \mathcal{O}_{\mathbb{C}_p}$. -/
theorem epsCp_ne_one : epsCp p ≠ 1 := by
  intro h
  set I := span {(p : PadicComplexInt p)}
  have h2 : Ideal.Quotient.mk I (epsRootsInt p 2) = Ideal.Quotient.mk I 1 := by
    have := congrArg (Perfection.coeff (ModP (PadicComplexInt p) p) p 2) h
    exact this.trans ((Perfection.coeff _ p 2).map_one.trans (map_one _).symm)
  have hz2 : epsRootsInt p 2 - 1 ∈ I := Ideal.Quotient.eq.1 h2
  have hz1 : epsRootsInt p 1 - 1 ∈ I ^ 2 := by
    have : epsRootsInt p 2 ^ p = epsRootsInt p 1 := Subtype.ext (by
      push_cast
      exact epsRoots_succ_pow 1)
    rw [← this]
    exact pow_p_sub_one_mem hz2
  have hpow (i : ℕ) : epsRootsInt p 1 ^ i - 1 ∈ I ^ 2 := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (epsRootsInt p 1) 1 i
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ hz1
  have hsum : ∑ i ∈ Finset.range p, epsRootsInt p 1 ^ i = 0 := Subtype.ext (by
    push_cast
    exact (isPrimitiveRoot_zetaCp (p := p)).geom_sum_eq_zero (Fact.out : p.Prime).one_lt)
  have hp : (p : PadicComplexInt p) ∈ I ^ 2 := by
    have : (p : PadicComplexInt p) =
        -∑ i ∈ Finset.range p, (epsRootsInt p 1 ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    rw [this]
    exact (Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ fun i _ => hpow i)
  have hp' : (p : PadicComplexInt p) ∈ (I ^ 2 • ⊤ : Ideal (PadicComplexInt p)) := by
    rwa [smul_eq_mul, Ideal.mul_top]
  have hn := (mem_span_p_pow_iff 2 _).1 hp'
  rw [show ((p : PadicComplexInt p) : ℂ_[p]) = (p : ℂ_[p]) from rfl, norm_p_cp] at hn
  have h1 : (p : ℝ)⁻¹ ^ 2 < (p : ℝ)⁻¹ :=
    pow_lt_self_of_lt_one₀ (inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos))
      (inv_p_lt_one (p := p)) one_lt_two
  exact h1.not_ge hn

end EpsNeOne

section AdicMk

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The image of an $I$-adic Cauchy sequence under $\varphi : A \to B$ with $\varphi(I) \subseteq J$ is a $J$-adic Cauchy sequence. -/
theorem isAdicCauchy_map (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ)
    {f : ℕ → A} (hf : AdicCompletion.IsAdicCauchy I A f) :
    AdicCompletion.IsAdicCauchy J B (fun n => φ (f n)) := by
  intro m n hmn
  have hm := hf hmn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hm ⊢
  rw [← map_sub]
  exact pow_le_comap_pow h m hm

/-- The map of adic completions sends the limit of a Cauchy sequence to the limit of its image. -/
theorem adicMap_mk (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ)
    (f : AdicCompletion.AdicCauchySequence I A) :
    adicMap φ I J h (AdicCompletion.mk I A f) =
      AdicCompletion.mk J B ⟨fun n => φ (f.1 n), isAdicCauchy_map φ I J h f.2⟩ := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_adicMap]
  simp only [AdicCompletion.evalₐ_mk]
  rfl

end AdicMk

section LogMap

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S : Type u} [CommRing S]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- A ring homomorphism $\psi : A_{cris}^0(R) \to A_{cris}^0(S)$ with $\psi(p) \in p A_{cris}^0(S)$ that sends the terms of the series of $\log [\varepsilon]$ to the terms of the series of $\log [\varepsilon']$ sends $\log [\varepsilon]$ to $\log [\varepsilon']$. -/
theorem adicMap_logTeich (ψ : acrisZero R p →+* acrisZero S p)
    (hψ : span {(p : acrisZero R p)} ≤ (span {(p : acrisZero S p)}).comap ψ)
    {ε : PreTilt R p} (hε : ε.untilt = 1) {ε' : PreTilt S p} (hε' : ε'.untilt = 1)
    (h : ∀ j, ψ (logTerm hε j) = logTerm hε' j) :
    @adicMap (acrisZero R p) (acrisZero S p) (Subalgebra.toCommRing _) (Subalgebra.toCommRing _)
      ψ _ _ hψ (logTeich hε) = logTeich hε' := by
  unfold logTeich
  refine (@adicMap_mk (acrisZero R p) (acrisZero S p) (Subalgebra.toCommRing _)
    (Subalgebra.toCommRing _) ψ _ _ hψ _).trans ?_
  congr 1
  refine Subtype.ext (funext fun k => ?_)
  simp only [logPartial, map_sum, h]

omit [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S] in
/-- The map of $W(\cdot^\flat)[1/p]$ sends the divided powers of $[\varepsilon] - 1$ to the divided powers of $[f^\flat(\varepsilon)] - 1$. -/
theorem locMap_logDiv (f : R →+* S) (ε : PreTilt R p) (j : ℕ) :
    locMap p f (logDiv ε j) = logDiv (preTiltMap p f ε) j := by
  refine (isUnit_factorial_loc (R := S) j).mul_left_cancel ?_
  rw [factorial_mul_logDiv, ← map_natCast (locMap p f), ← map_mul, factorial_mul_logDiv,
    map_pow, locMap_algebraMap, map_sub, map_one, wittMap, WittVector.map_teichmuller]

/-- The untilt of $f^\flat(\varepsilon)$ is $1$ if the untilt of $\varepsilon$ is $1$. -/
theorem untilt_preTiltMap_eq_one (f : R →+* S) {ε : PreTilt R p} (hε : ε.untilt = 1) :
    (preTiltMap p f ε).untilt = 1 := by
  rw [untilt_preTiltMap, hε, map_one]

/-- The map of $A_{cris}^0$ sends the terms of the series of $\log [\varepsilon]$ to the terms of the series of $\log [f^\flat(\varepsilon)]$. -/
theorem acrisZeroMap_logTerm (f : R →+* S) {ε : PreTilt R p} (hε : ε.untilt = 1) (j : ℕ) :
    acrisZeroMap p f (logTerm hε j) = logTerm (untilt_preTiltMap_eq_one f hε) j := by
  apply Subtype.ext
  rw [coe_acrisZeroMap]
  change locMap p f ((-1) ^ j * (j.factorial : LocW[R, p]) * logDiv ε (j + 1)) =
    (-1) ^ j * (j.factorial : LocW[S, p]) * logDiv (preTiltMap p f ε) (j + 1)
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, locMap_logDiv]

/-- The map of $A_{cris}$ of $f : R \to S$ sends $\log [\varepsilon]$ to $\log [f^\flat(\varepsilon)]$. -/
theorem acrisMap_logTeich (f : R →+* S) {ε : PreTilt R p} (hε : ε.untilt = 1) :
    acrisMap p f (logTeich hε) = logTeich (untilt_preTiltMap_eq_one f hε) :=
  adicMap_logTeich _ _ hε _ (acrisZeroMap_logTerm f hε)

omit [IsAdicComplete (span {(p : R)}) R] in
/-- The Frobenius of $W(R^\flat)[1/p]$ sends the divided powers of $[\varepsilon] - 1$ to the divided powers of $[\varepsilon^p] - 1$. -/
theorem locFrob_logDiv (ε : PreTilt R p) (j : ℕ) :
    locFrob R p (logDiv ε j) = logDiv (ε ^ p) j := by
  refine (isUnit_factorial_loc (R := R) j).mul_left_cancel ?_
  rw [factorial_mul_logDiv, ← map_natCast (locFrob R p), ← map_mul, factorial_mul_logDiv,
    map_pow, locFrob_algebraMap, map_sub, map_one, frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, frobenius_def]

/-- The untilt of $\varepsilon^p$ is $1$ if the untilt of $\varepsilon$ is $1$. -/
theorem untilt_pow_eq_one {ε : PreTilt R p} (hε : ε.untilt = 1) : (ε ^ p).untilt = 1 := by
  rw [map_pow, hε, one_pow]

/-- The Frobenius of $A_{cris}^0$ sends the terms of the series of $\log [\varepsilon]$ to the terms of the series of $\log [\varepsilon^p]$. -/
theorem acrisZeroFrob_logTerm {ε : PreTilt R p} (hε : ε.untilt = 1) (j : ℕ) :
    acrisZeroFrob R p (logTerm hε j) = logTerm (untilt_pow_eq_one hε) j := by
  apply Subtype.ext
  rw [coe_acrisZeroFrob]
  change locFrob R p ((-1) ^ j * (j.factorial : LocW[R, p]) * logDiv ε (j + 1)) =
    (-1) ^ j * (j.factorial : LocW[R, p]) * logDiv (ε ^ p) (j + 1)
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, locFrob_logDiv]

/-- The Frobenius of $A_{cris}(R)$ sends $\log [\varepsilon]$ to $\log [\varepsilon^p]$. -/
theorem acrisFrob_logTeich {ε : PreTilt R p} (hε : ε.untilt = 1) :
    acrisFrob R p (logTeich hε) = logTeich (untilt_pow_eq_one hε) :=
  adicMap_logTeich _ _ hε _ (acrisZeroFrob_logTerm hε)

end LogMap

section LogSmul

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] {M : Type*} [Monoid M] [MulSemiringAction M R]

/-- The action of $g \in M$ on $A_{cris}(R)$ sends $\log [\varepsilon]$ to $\log [g \varepsilon]$. -/
theorem smul_logTeich (g : M) {ε : PreTilt R p} (hε : ε.untilt = 1) :
    g • logTeich hε =
      logTeich (untilt_preTiltMap_eq_one (MulSemiringAction.toRingHom M R g) hε) :=
  acrisMap_logTeich _ hε

end LogSmul

section Kummer

variable {p : ℕ} [Fact p.Prime]

/-- The $p$-power roots $p^{1/p^n}$ of $p$ in $\mathbb{C}_p$ are not zero. -/
theorem pRoots_ne_zero (n : ℕ) : pRoots p n ≠ 0 := by
  intro h
  have := pRoots_pow (p := p) n
  rw [h, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at this
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this.symm

/-- The $p^n$-th root of unity $\sigma(p^{1/p^n}) / p^{1/p^n}$ in $\mathbb{C}_p$. -/
noncomputable def kummerRoots (σ : Field.absoluteGaloisGroup ℚ_[p]) (n : ℕ) : ℂ_[p] :=
  galoisCp p σ (pRoots p n) / pRoots p n

/-- The relation $\eta_{n+1}^p = \eta_n$. -/
theorem kummerRoots_succ_pow (σ : Field.absoluteGaloisGroup ℚ_[p]) (n : ℕ) :
    kummerRoots σ (n + 1) ^ p = kummerRoots σ n := by
  rw [kummerRoots, kummerRoots, div_pow, ← map_pow, pRoots_succ_pow]

/-- The relation $\eta_n^{p^n} = 1$. -/
theorem kummerRoots_pow (σ : Field.absoluteGaloisGroup ℚ_[p]) (n : ℕ) :
    kummerRoots σ n ^ p ^ n = 1 := by
  rw [kummerRoots, div_pow, ← map_pow, pRoots_pow, map_natCast]
  exact div_self (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

/-- Each $\eta_n$ has norm $1$. -/
theorem norm_kummerRoots (σ : Field.absoluteGaloisGroup ℚ_[p]) (n : ℕ) :
    ‖kummerRoots σ n‖ = 1 := by
  rw [kummerRoots, norm_div, norm_galoisCp, div_self (norm_ne_zero_iff.2 (pRoots_ne_zero n))]

/-- The element $\eta_n$ of $\mathcal{O}_{\mathbb{C}_p}$. -/
noncomputable def kummerInt (σ : Field.absoluteGaloisGroup ℚ_[p]) (n : ℕ)
    : PadicComplexInt p :=
  ⟨kummerRoots σ n, (mem_padicComplexInt_iff _).2 (norm_kummerRoots σ n).le⟩

/-- The Kummer element $\eta_\sigma = \sigma(p^\flat) / p^\flat = (\sigma(p^{1/p^n}) / p^{1/p^n})_n$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$. -/
noncomputable def kummerFlat (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    PreTilt (PadicComplexInt p) p :=
  ⟨fun n => Ideal.Quotient.mk _ (kummerInt σ n), fun n => by
    change Ideal.Quotient.mk _ (kummerInt σ (n + 1)) ^ p = _
    rw [← map_pow]
    exact congrArg _ (Subtype.ext (kummerRoots_succ_pow σ n))⟩

/-- The untilt of the Kummer element $\eta_\sigma$ is $1$. -/
theorem untilt_kummerFlat (σ : Field.absoluteGaloisGroup ℚ_[p])
    : (kummerFlat σ).untilt = 1 := by
  refine Perfection.teichmuller_spec fun n => ⟨kummerInt σ n, rfl, ?_⟩
  have : kummerInt σ n ^ p ^ n = 1 := Subtype.ext (by push_cast; exact kummerRoots_pow σ n)
  rw [this]

/-- The Galois action on $\mathcal{O}_{\mathbb{C}_p}^\flat$ sends $p^\flat$ to $\eta_\sigma p^\flat$. -/
theorem preTiltMap_pFlat (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    preTiltMap p (MulSemiringAction.toRingHom _ (PadicComplexInt p) σ) (pFlat p) =
      kummerFlat σ * pFlat p := by
  refine Perfection.ext fun n => ?_
  change Ideal.Quotient.mk _ (σ • pRootsInt p n) =
    Ideal.Quotient.mk _ (kummerInt σ n) * Ideal.Quotient.mk _ (pRootsInt p n)
  rw [← map_mul]
  refine congrArg _ (Subtype.ext ?_)
  change galoisCp p σ (pRoots p n) = kummerRoots σ n * pRoots p n
  rw [kummerRoots, div_mul_cancel₀ _ (pRoots_ne_zero n)]

/-- The cocycle relation $\eta_{\sigma \tau} = \sigma(\eta_\tau) \, \eta_\sigma$ in $\mathcal{O}_{\mathbb{C}_p}^\flat$. -/
theorem kummerFlat_mul (σ τ : Field.absoluteGaloisGroup ℚ_[p]) :
    kummerFlat (σ * τ) =
      preTiltMap p (MulSemiringAction.toRingHom _ (PadicComplexInt p) σ) (kummerFlat τ) *
        kummerFlat σ := by
  refine Perfection.ext fun n => ?_
  change Ideal.Quotient.mk _ (kummerInt (σ * τ) n) =
    Ideal.Quotient.mk _ (σ • kummerInt τ n) * Ideal.Quotient.mk _ (kummerInt σ n)
  rw [← map_mul]
  refine congrArg _ (Subtype.ext ?_)
  change kummerRoots (σ * τ) n = galoisCp p σ (kummerRoots τ n) * kummerRoots σ n
  have hσ : galoisCp p σ (pRoots p n) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_galoisCp, norm_ne_zero_iff]
    exact pRoots_ne_zero n
  rw [kummerRoots, kummerRoots, kummerRoots, galoisCp_mul, RingHom.comp_apply, map_div₀,
    div_mul_div_comm, mul_comm (galoisCp p σ (pRoots p n)) (pRoots p n),
    mul_div_mul_right _ _ hσ]

/-- The Kummer element $\log [\eta_\sigma]$ of $A_{cris}(\mathcal{O}_{\mathbb{C}_p})$. With the functional equation of $\log$ it is $c(\sigma) t$ for the Kummer cocycle $c$ of $p^\flat$; this file does not prove that. -/
noncomputable def kummerLog (σ : Field.absoluteGaloisGroup ℚ_[p])
    : Acris (PadicComplexInt p) p :=
  logTeich (untilt_kummerFlat σ)

end Kummer

end Langlands.Padic
