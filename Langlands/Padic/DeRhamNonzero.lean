/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.DeRhamQp

/-!
# The ring $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring

This file shows that $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring. The ring $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$ is a domain, and the element $\xi = p - [p^\flat]$ is a nonzero element of $\ker \theta$. Thus $\ker \theta[1/p]$ is a nonzero proper ideal of a domain, and no power of it is in the next power. It follows that the trivial representation of $G_{\mathbb{Q}_p}$ is de Rham, with no hypothesis.

## Main definitions

* `Langlands.Padic.pRoots`: a sequence of $p$-power roots of $p$ in $\mathbb{C}_p$.
* `Langlands.Padic.pFlat`: the element $p^\flat = (p, p^{1/p}, p^{1/p^2}, \dots)$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$.
* `Langlands.Padic.xiCp`: the element $\xi = p - [p^\flat]$ of $W(\mathcal{O}_{\mathbb{C}_p}^\flat)$.

## Main results

* `Langlands.Padic.nontrivial_bdr`: if $W(R^\flat)[1/p]$ is a domain and $\ker \theta[1/p] \ne 0$, then $B_{dR}(R)$ is not the zero ring.
* `Langlands.Padic.untilt_pFlat`: the untilt of $p^\flat$ is $p$.
* `Langlands.Padic.ker_fontaineThetaInvertP_ne_bot`: $\ker \theta[1/p] \ne 0$ for $\mathcal{O}_{\mathbb{C}_p}$.
* `Langlands.Padic.nontrivial_bdr_padicComplexInt`: $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring.
* `Langlands.Padic.isDeRhamQp_trivial`: the trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is de Rham.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

section General

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- The map $\theta[1/p]$ extends $\theta$. -/
theorem fontaineThetaInvertP_algebraMap (x : WittVector p (PreTilt R p)) :
    fontaineThetaInvertP R p (algebraMap _ _ x) = algebraMap _ _ (fontaineTheta R p x) := by
  rw [fontaineThetaInvertP]
  exact IsLocalization.lift_eq _ _

/-- If $R[1/p]$ is not the zero ring, $\ker \theta[1/p]$ is not zero and $W(R^\flat)[1/p]$ is a domain, then the submonoid that $B_{dR}(R)$ inverts does not contain $0$. -/
theorem zero_notMem_bdrSubmonoid [Nontrivial (Localization.Away (p : R))]
    [IsDomain (Localization.Away (p : WittVector p (PreTilt R p)))]
    (hI : RingHom.ker (fontaineThetaInvertP R p) ≠ ⊥) :
    (0 : BDeRhamPlus R p) ∉ bdrSubmonoid R p := by
  set I := RingHom.ker (fontaineThetaInvertP R p) with hIdef
  have hItop : I ≠ ⊤ := RingHom.ker_ne_top _
  have key : ∀ s ∈ bdrSubmonoid R p, ∃ b : Localization.Away (p : WittVector p (PreTilt R p)),
      b ≠ 0 ∧ (∃ k : ℕ, span {b} = I ^ k) ∧ s = AdicCompletion.of I _ b := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨a, ha, rfl⟩ := hs
      have ha' : I = span {a} := ha
      refine ⟨a, fun h0 => hI ?_, ⟨1, by rw [pow_one, ha']⟩, rfl⟩
      rw [ha', h0, Ideal.span_singleton_eq_bot]
    | one =>
      exact ⟨1, one_ne_zero,
        ⟨0, by rw [pow_zero, Ideal.span_singleton_one, Ideal.one_eq_top]⟩, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨b, hb, ⟨k, hk⟩, rfl⟩ := hx
      obtain ⟨c, hc, ⟨l, hl⟩, rfl⟩ := hy
      refine ⟨b * c, mul_ne_zero hb hc, ⟨k + l, ?_⟩, ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton, hk, hl, pow_add]
      · exact (map_mul (algebraMap _ (AdicCompletion I
          (Localization.Away (p : WittVector p (PreTilt R p))))) b c).symm
  intro h0
  obtain ⟨b, hb, ⟨k, hk⟩, hb0⟩ := key 0 h0
  have hb0' : AdicCompletion.of I _ b = (0 : AdicCompletion I _) := hb0.symm
  have h1 : Ideal.Quotient.mk (I ^ (k + 1)) b = 0 := by
    rw [← AdicCompletion.evalₐ_of, hb0', map_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_succ, ← hk, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨c, hc, hbc⟩ := h1
  have hc1 : c = 1 := by
    have : b * (1 - c) = 0 := by rw [mul_sub, mul_one, hbc, sub_self]
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb)).symm
  exact hItop ((Ideal.eq_top_iff_one _).2 (hc1 ▸ hc))

/-- If $R[1/p]$ is not the zero ring, $\ker \theta[1/p]$ is not zero and $W(R^\flat)[1/p]$ is a domain, then $B_{dR}(R)$ is not the zero ring. -/
theorem nontrivial_bdr [Nontrivial (Localization.Away (p : R))]
    [IsDomain (Localization.Away (p : WittVector p (PreTilt R p)))]
    (hI : RingHom.ker (fontaineThetaInvertP R p) ≠ ⊥) : Nontrivial (BDeRham R p) := by
  rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := bdrSubmonoid R p)]
  exact zero_notMem_bdrSubmonoid hI

/-- If $R[1/p]$ is not the zero ring, then $p \neq 0$ in $W(R^\flat)$. -/
theorem natCast_witt_ne_zero [Nontrivial (Localization.Away (p : R))] :
    (p : WittVector p (PreTilt R p)) ≠ 0 := by
  have : Nontrivial (Localization.Away (p : WittVector p (PreTilt R p))) :=
    (fontaineThetaInvertP R p).domain_nontrivial
  intro h
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (p : WittVector p (PreTilt R p))) (p : WittVector p (PreTilt R p))
  have h' := congrArg (algebraMap (WittVector p (PreTilt R p))
    (Localization.Away (p : WittVector p (PreTilt R p)))) h
  rw [map_zero] at h'
  rw [h'] at hu
  exact not_isUnit_zero hu

/-- If $R^\flat$ is a domain and $R[1/p]$ is not the zero ring, then $W(R^\flat)[1/p]$ is a domain. -/
theorem isDomain_locWitt [IsDomain (PreTilt R p)] [Nontrivial (Localization.Away (p : R))] :
    IsDomain (Localization.Away (p : WittVector p (PreTilt R p))) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors natCast_witt_ne_zero)

/-- If $R^\flat$ is a domain and $R[1/p]$ is not the zero ring, then the map $W(R^\flat) \to W(R^\flat)[1/p]$ is injective. -/
theorem algebraMap_locWitt_injective [IsDomain (PreTilt R p)]
    [Nontrivial (Localization.Away (p : R))] :
    Function.Injective (algebraMap (WittVector p (PreTilt R p))
      (Localization.Away (p : WittVector p (PreTilt R p)))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors natCast_witt_ne_zero)

end General

section Compatible

variable {p : ℕ} [Fact p.Prime]

/-- A sequence of $p$-power roots of $p$ in $\mathbb{C}_p$: $y_0 = p$ and $y_{n+1}^p = y_n$. -/
noncomputable def pRoots (p : ℕ) [Fact p.Prime] : ℕ → ℂ_[p]
  | 0 => p
  | n + 1 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (pRoots p n)
      (Fact.out : p.Prime).pos)

/-- The first term of the sequence is $p$. -/
theorem pRoots_zero : pRoots p 0 = p := rfl

/-- Each term of the sequence is the $p$-th power of the next term. -/
theorem pRoots_succ_pow (n : ℕ) : pRoots p (n + 1) ^ p = pRoots p n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (pRoots p n) (Fact.out : p.Prime).pos)

/-- The $p^n$-th power of the $n$-th term is $p$. -/
theorem pRoots_pow (n : ℕ) : pRoots p n ^ p ^ n = p := by
  induction n with
  | zero => simp [pRoots_zero]
  | succ n ih => rw [pow_succ', pow_mul, pRoots_succ_pow, ih]

/-- Each term of the sequence has norm at most $1$. -/
theorem norm_pRoots_le_one (n : ℕ) : ‖pRoots p n‖ ≤ 1 := by
  have h : ‖pRoots p n‖ ^ p ^ n = (p : ℝ)⁻¹ := by rw [← norm_pow, pRoots_pow, norm_p_cp]
  by_contra! h'
  have := one_lt_pow₀ h' (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  rw [h] at this
  exact (inv_p_lt_one (p := p)).not_gt this

/-- The norm of $p^{1/p}$ is more than $1/p$. -/
theorem norm_pRoots_one_gt : (p : ℝ)⁻¹ < ‖pRoots p 1‖ := by
  have h : ‖pRoots p 1‖ ^ p = (p : ℝ)⁻¹ := by
    rw [← norm_pow, pRoots_succ_pow, pRoots_zero, norm_p_cp]
  by_contra! h'
  have h1 : ‖pRoots p 1‖ ^ p ≤ (p : ℝ)⁻¹ ^ p := pow_le_pow_left₀ (norm_nonneg _) h' p
  have h2 : (p : ℝ)⁻¹ ^ p < (p : ℝ)⁻¹ :=
    pow_lt_self_of_lt_one₀
      (inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)) (inv_p_lt_one (p := p))
      (Fact.out : p.Prime).one_lt
  rw [h] at h1
  exact h2.not_ge h1

/-- The $p$-power roots of $p$ as elements of $\mathcal{O}_{\mathbb{C}_p}$. -/
noncomputable def pRootsInt (p : ℕ) [Fact p.Prime] (n : ℕ) : PadicComplexInt p :=
  ⟨pRoots p n, (mem_padicComplexInt_iff _).2 (norm_pRoots_le_one n)⟩

/-- The element $p^\flat = (p, p^{1/p}, p^{1/p^2}, \dots)$ of the tilt of $\mathcal{O}_{\mathbb{C}_p}$. -/
noncomputable def pFlat (p : ℕ) [Fact p.Prime] : PreTilt (PadicComplexInt p) p :=
  ⟨fun n => Ideal.Quotient.mk _ (pRootsInt p n), fun n => by
    rw [← map_pow]
    congr 1
    exact Subtype.ext (pRoots_succ_pow n)⟩

/-- The untilt of $p^\flat$ is $p$. -/
theorem untilt_pFlat : (pFlat p).untilt = p := by
  refine Perfection.teichmuller_spec fun n => ⟨pRootsInt p n, rfl, ?_⟩
  have : pRootsInt p n ^ p ^ n = p := Subtype.ext (by push_cast; exact pRoots_pow n)
  rw [this]

/-- The element $p^\flat$ is not zero. -/
theorem pFlat_ne_zero : pFlat p ≠ 0 := by
  intro h
  have h1 : PreTilt.coeff 1 (pFlat p) = 0 := by rw [h, map_zero]
  change Ideal.Quotient.mk _ (pRootsInt p 1) = 0 at h1
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : pRootsInt p 1 ∈ (span {(p : PadicComplexInt p)} ^ 1 • ⊤ :
      Ideal (PadicComplexInt p)) := by
    rw [smul_eq_mul, Ideal.mul_top, pow_one]
    exact h1
  rw [mem_span_p_pow_iff, pow_one] at h2
  exact (norm_pRoots_one_gt (p := p)).not_ge h2

end Compatible

section Cp

variable {p : ℕ} [Fact p.Prime]

/-- The tilt of $\mathcal{O}_{\mathbb{C}_p}$ is a domain. -/
instance isDomain_preTilt_padicComplexInt : IsDomain (PreTilt (PadicComplexInt p) p) :=
  PreTilt.isDomain ℂ_[p] (PadicComplex.valued p).v (PadicComplexInt p)
    (PadicComplexInt.integers p) p

/-- The ring $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$ is a domain. -/
instance isDomain_locWitt_padicComplexInt :
    IsDomain (Localization.Away (p : WittVector p (PreTilt (PadicComplexInt p) p))) :=
  isDomain_locWitt

variable (p) in
/-- The element $\xi = p - [p^\flat]$ of $W(\mathcal{O}_{\mathbb{C}_p}^\flat)$. -/
noncomputable def xiCp : WittVector p (PreTilt (PadicComplexInt p) p) :=
  (p : WittVector p (PreTilt (PadicComplexInt p) p)) - teichmuller p (pFlat p)

/-- The element $\xi$ is in the kernel of $\theta$. -/
theorem fontaineTheta_xiCp : fontaineTheta (PadicComplexInt p) p (xiCp p) = 0 := by
  rw [xiCp, map_sub, map_natCast, fontaineTheta_teichmuller, untilt_pFlat, sub_self]

/-- The element $\xi$ is not zero. -/
theorem xiCp_ne_zero : xiCp p ≠ 0 := by
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := p)) h
  rw [xiCp, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, map_zero, neg_eq_zero,
    constantCoeff_apply, teichmuller_coeff_zero] at h1
  exact pFlat_ne_zero h1

/-- The kernel of $\theta[1/p]$ for $\mathcal{O}_{\mathbb{C}_p}$ is not zero, because it contains $\xi$. -/
theorem ker_fontaineThetaInvertP_ne_bot :
    RingHom.ker (fontaineThetaInvertP (PadicComplexInt p) p) ≠ ⊥ := by
  intro h
  have hmem : algebraMap _ (Localization.Away (p : WittVector p (PreTilt (PadicComplexInt p) p)))
      (xiCp p) ∈ RingHom.ker (fontaineThetaInvertP (PadicComplexInt p) p) := by
    rw [RingHom.mem_ker, fontaineThetaInvertP_algebraMap, fontaineTheta_xiCp, map_zero]
  rw [h, Ideal.mem_bot, ← map_zero (algebraMap (WittVector p (PreTilt (PadicComplexInt p) p))
    (Localization.Away (p : WittVector p (PreTilt (PadicComplexInt p) p))))] at hmem
  exact xiCp_ne_zero (algebraMap_locWitt_injective hmem)

/-- The ring $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring. -/
instance nontrivial_bdr_padicComplexInt : Nontrivial (BDeRham (PadicComplexInt p) p) :=
  nontrivial_bdr ker_fontaineThetaInvertP_ne_bot

/-- The trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is de Rham. -/
theorem isDeRhamQp_trivial :
    IsDeRhamQp (Representation.trivial ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) ℚ_[p]) :=
  isDeRhamQp_trivial_of_nontrivial

end Cp

end Langlands.Padic
