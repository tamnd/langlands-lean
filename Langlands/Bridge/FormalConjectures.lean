/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.FormalConjectures.Wikipedia
import Langlands.Statements.Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Langlands.Fidelity.Modularity
import Mathlib.NumberTheory.PrimeCounting

/-!
# Bridges to formal-conjectures

This file compares the statements of the project with the statements of formal-conjectures (spec 06.4). The statements of formal-conjectures are in `Langlands/Ported/FormalConjectures/Wikipedia.lean`.

* `Langlands.Bridge.hasseWeil_rat_of_hasseWeilEllipticQ`: `HasseWeilEllipticQ` implies the statement `exists_hasAnalyticContinuation_rat` of formal-conjectures. The proof divides the completed L-function by the gamma factor. The function $1/\Gamma$ is entire, so the quotient is entire.
* `Langlands.Bridge.not_modularityConjecture`: the statement `modularityConjecture` of formal-conjectures is false for every elliptic curve over $\mathbb{Q}$.
* `Langlands.Bridge.satoTate_conjecture_of_satoTate`: `SatoTate` implies the statement `satoTate_conjecture` of formal-conjectures. The proof takes two hypotheses on each curve: the coefficient `ap` of formal-conjectures agrees with $a_p$ of `WeierstrassCurve.LFunction` at almost all primes (`ApAgree`), and the Hasse bound holds at almost all primes (`HasseBound`). Both are theorems that Mathlib does not have yet.
* `Langlands.Bridge.ramanujan_petersson_of_ramanujanPeterssonHolomorphic`: `RamanujanPeterssonHolomorphic` implies the statement `ramanujan_petersson` of formal-conjectures for $\tau$. The proof takes the hypothesis `DeltaIsEigenform`: the power series $\Delta$ of formal-conjectures is the $q$-expansion of a normalized eigenform of weight 12 and level 1.

## The statement of Sato-Tate in formal-conjectures

The statement of formal-conjectures counts the primes $p < N$ with $a \le a_p / (2 \sqrt{p}) \le b$ for $-1 \le a \le b \le 1$. The project statement counts the primes $p \le x$ with $\theta_p \in [\alpha, \beta]$ for $0 \le \alpha \le \beta \le \pi$. The bridge takes $\alpha = \arccos b$ and $\beta = \arccos a$. Because $\arccos$ is strictly decreasing on $[-1, 1]$, the two conditions on $p$ agree when $|a_p| \le 2 \sqrt{p}$. The change of variable $t = \cos \theta$ takes the measure $\frac{2}{\pi} \sin^2 \theta \, d\theta$ to the measure of `satoTateCDF` (`satoTateMeasure_eq`). The two counts differ at most at the finitely many primes below a bound $P_0$, and the number of primes tends to infinity, so the two limits are equal (`tendsto_density_congr`).

## The statement of modularity in formal-conjectures

The coefficient `modularFormAn n f` of formal-conjectures is the coefficient of the $q$-expansion `qExpansion N f`, with the parameter $q_N = e^{2 \pi i \tau / N}$. The width of the cusp $\infty$ of $\Gamma_0(N)$ is 1, so a form $f = \sum a_n e^{2 \pi i n \tau}$ has the expansion $\sum a_n q_N^{nN}$ in this parameter. For $N \ge 2$ the coefficient of $q_N$ is 0 (`coeff_one_qExpansion_eq_zero`), so no form satisfies the condition `modularFormAn 1 f = 1`. For $N = 1$ there is no nonzero cusp form of weight 2. So no curve satisfies `modularityConjecture`, and the theorem `modularity_conjecture` of formal-conjectures is false as stated.

The repair is to use the width 1: `qExpansion 1 f`. The project statement `Langlands.ModularityEllipticQ` uses this parameter. The report to formal-conjectures is a decision of the owner.
-/

namespace Langlands.Bridge

open UpperHalfPlane Function.Periodic Complex
open scoped MatrixGroups Real

section HasseWeil

/-- `HasseWeilEllipticQ` implies the Hasse-Weil statement over $\mathbb{Q}$ of formal-conjectures. -/
theorem hasseWeil_rat_of_hasseWeilEllipticQ (h : HasseWeilEllipticQ) :
    Ported.FormalConjectures.HasseWeil.exists_hasAnalyticContinuation_rat := by
  intro E _
  obtain ⟨N, ε, Λ, hN, -, hΛ, hL, -⟩ := h E
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2pi : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  refine ⟨fun s => Λ s * (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ =>
        Λ s * (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹ := by
      have h1 : Differentiable ℂ fun s : ℂ => (Complex.Gamma s)⁻¹ := by
        simpa [one_div] using Complex.differentiable_one_div_Gamma
      have h2 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(s / 2)) := fun s =>
        ((differentiableAt_id.div_const 2).neg).const_cpow (Or.inl hN0)
      have h3 : Differentiable ℂ fun s : ℂ => (2 * π : ℂ) ^ s := fun s =>
        differentiableAt_id.const_cpow (Or.inl h2pi)
      exact ((hΛ.mul h2).mul h3).mul h1
    exact fun z => hd.analyticAt z
  · intro s hs
    beta_reduce
    rw [hL s hs]
    have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have e1 : (N : ℂ) ^ (s / 2) * (N : ℂ) ^ (-(s / 2)) = 1 := by
      rw [← Complex.cpow_add _ _ hN0]; simp
    have e2 : (2 * π : ℂ) ^ (-s) * (2 * π : ℂ) ^ s = 1 := by
      rw [← Complex.cpow_add _ _ h2pi]; simp
    calc (N : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Complex.Gamma s * E.LSeries s *
          (N : ℂ) ^ (-(s / 2)) * (2 * π : ℂ) ^ s * (Complex.Gamma s)⁻¹
        = ((N : ℂ) ^ (s / 2) * (N : ℂ) ^ (-(s / 2))) * ((2 * π : ℂ) ^ (-s) * (2 * π : ℂ) ^ s) *
            (Complex.Gamma s * (Complex.Gamma s)⁻¹) * E.LSeries s := by ring
      _ = E.LSeries s := by rw [e1, e2, mul_inv_cancel₀ hG]; ring

end HasseWeil

section Modularity

variable {N : ℕ} {k : ℤ}

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem natCast_mem_strictPeriods_Gamma0 (N : ℕ) :
    (N : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp only [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨N, by simp⟩

/-- In the parameter $q_N$, the cusp function of a form on $\Gamma_0(N)$ is the cusp function in the parameter $q_1$, composed with $q \mapsto q^N$. -/
theorem cuspFunction_natCast_eq (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.cuspFunction (N : ℝ) f = UpperHalfPlane.cuspFunction 1 f ∘ fun q => q ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma0 N)
  funext q
  by_cases hq : q = 0
  · subst hq
    rw [Function.comp_apply, zero_pow hN.ne', CuspFormClass.cuspFunction_apply_zero f hNpos
      (natCast_mem_strictPeriods_Gamma0 N), CuspFormClass.cuspFunction_apply_zero f one_pos
      (one_mem_strictPeriods_Gamma0 N)]
  · have hqN : q ^ N ≠ 0 := pow_ne_zero _ hq
    simp only [Function.comp_apply, UpperHalfPlane.cuspFunction,
      Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.Periodic.cuspFunction_eq_of_nonzero _ _ hqN]
    have hinv : invQParam (N : ℝ) q = (N : ℂ) * invQParam 1 q := by
      simp only [invQParam]; push_cast; ring
    have hexp : qParam 1 (invQParam (N : ℝ) q) = qParam 1 (invQParam 1 (q ^ N)) := by
      rw [qParam_right_inv one_ne_zero hqN, hinv]
      calc qParam 1 ((N : ℂ) * invQParam 1 q) = (qParam 1 (invQParam 1 q)) ^ N := by
            simp only [qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
        _ = q ^ N := by rw [qParam_right_inv one_ne_zero hq]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hw : invQParam (N : ℝ) q = invQParam 1 (q ^ N) + n := by
      simp only [Complex.ofReal_one, div_one] at hn
      exact mul_left_cancel₀ h2pi (by rw [hn]; ring)
    rw [hw]
    simpa using (hper.int_mul n) (invQParam 1 (q ^ N))

/-- For $N \ge 2$, the coefficient of $q_N$ in the expansion `qExpansion N f` of a cusp form on $\Gamma_0(N)$ is 0. -/
theorem coeff_one_qExpansion_eq_zero (hN : 2 ≤ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (qExpansion (N : ℝ) f).coeff 1 = 0 := by
  have hG : DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 :=
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0 N)).differentiableAt
  have hG' : HasDerivAt (UpperHalfPlane.cuspFunction 1 f)
      (deriv (UpperHalfPlane.cuspFunction 1 f) 0) ((fun q : ℂ => q ^ N) 0) := by
    simpa [zero_pow (by omega : N ≠ 0)] using hG.hasDerivAt
  have hcomp : HasDerivAt (UpperHalfPlane.cuspFunction 1 f ∘ fun q : ℂ => q ^ N)
      (deriv (UpperHalfPlane.cuspFunction 1 f) 0 * ((N : ℂ) * 0 ^ (N - 1))) 0 :=
    hG'.comp (0 : ℂ) (hasDerivAt_pow N 0)
  rw [qExpansion_coeff, cuspFunction_natCast_eq (by omega) f]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedDeriv_one]
  rw [hcomp.deriv, zero_pow (by omega : N - 1 ≠ 0)]
  simp

theorem gamma0_one_eq : (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  have h : CongruenceSubgroup.Gamma0 1 = ⊤ := by
    ext A; simp [CongruenceSubgroup.Gamma0_mem, Subsingleton.elim _ (0 : ZMod 1)]
  change Subgroup.map _ (CongruenceSubgroup.Gamma0 1) = _
  rw [h, MonoidHom.range_eq_map]

theorem cuspForm_weight_two_eq_zero_of_eq {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ = 𝒮ℒ)
    (f : CuspForm Γ 2) : f = 0 := by
  subst hΓ
  exact rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) f

/-- For each $N \ge 1$, the coefficient `modularFormAn 1 f` of formal-conjectures is 0 for each cusp form of weight 2 on $\Gamma_0(N)$. -/
theorem modularFormAn_one_eq_zero (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    Ported.FormalConjectures.ModularityConjecture.modularFormAn 1 f = 0 := by
  unfold Ported.FormalConjectures.ModularityConjecture.modularFormAn
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    rw [cuspForm_weight_two_eq_zero_of_eq gamma0_one_eq f]
    simp [qExpansion_coeff, UpperHalfPlane.cuspFunction]
  · exact coeff_one_qExpansion_eq_zero h f

/-- **The statement of modularity in formal-conjectures is false.** No elliptic curve over $\mathbb{Q}$ satisfies `modularityConjecture`, because the condition `modularFormAn 1 f = 1` fails for every cusp form of weight 2. -/
theorem not_modularityConjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ Ported.FormalConjectures.ModularityConjecture.modularityConjecture E := by
  rintro ⟨N, f, ⟨h1, -⟩, -⟩
  rw [modularFormAn_one_eq_zero N.pos f] at h1
  exact zero_ne_one h1

/-- The theorem `modularity_conjecture` of formal-conjectures is false as stated. -/
theorem not_modularity_conjecture :
    ¬ Ported.FormalConjectures.ModularityConjecture.modularity_conjecture := fun h =>
  not_modularityConjecture Fidelity.congruentNumberCurve (h _)

end Modularity

section SatoTate

open Langlands.Ported.FormalConjectures Real Filter Topology

/-- The Sato-Tate measure of $[a, b] \subseteq [-1, 1]$ in the variable $\cos \theta$ is the measure of $[\arccos b, \arccos a]$ in the variable $\theta$. -/
theorem satoTateMeasure_eq {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    SatoTateConjecture.satoTateMeasure a b = (2 / π) * ∫ θ in (arccos b)..(arccos a), Real.sin θ ^ 2 := by
  rw [integral_sin_sq, sin_arccos, sin_arccos, cos_arccos ha ha', cos_arccos hb hb',
    arccos_eq_pi_div_two_sub_arcsin, arccos_eq_pi_div_two_sub_arcsin]
  simp only [SatoTateConjecture.satoTateMeasure, SatoTateConjecture.satoTateCDF]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- The number of primes $p \le N$ with a property, as a count over `Nat.primesBelow (N + 1)`. -/
theorem card_primes_le_eq (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    Nat.card {p : ℕ // p.Prime ∧ p ≤ N ∧ Q p} = ((Nat.primesBelow (N + 1)).filter Q).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
    simp [Nat.primesBelow, and_assoc, and_left_comm])

theorem card_primes_le_eq' (N : ℕ) :
    Nat.card {p : ℕ // p.Prime ∧ p ≤ N} = (Nat.primesBelow (N + 1)).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
    simp [Nat.primesBelow, and_comm])

/-- If two properties agree on the primes $p \ge P_0$, then their densities among the primes have the same limit. -/
theorem tendsto_density_congr {Q Q' : ℕ → Prop} [DecidablePred Q] [DecidablePred Q'] (P₀ : ℕ)
    (hQ : ∀ p, P₀ ≤ p → p.Prime → (Q p ↔ Q' p)) {L : ℝ}
    (h : Tendsto (fun N : ℕ => (((Nat.primesBelow N).filter Q).card : ℝ) / (Nat.primesBelow N).card)
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (((Nat.primesBelow N).filter Q').card : ℝ) / (Nat.primesBelow N).card)
      atTop (𝓝 L) := by
  have hden : Tendsto (fun N : ℕ => ((Nat.primesBelow N).card : ℝ)) atTop atTop := by
    simp only [Nat.primesBelow_card_eq_primeCounting']
    exact tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting'
  have hbound : ∀ N, |(((Nat.primesBelow N).filter Q').card : ℝ) - ((Nat.primesBelow N).filter Q).card| ≤ P₀ := by
    intro N
    have key : ∀ (R R' : ℕ → Prop) [DecidablePred R] [DecidablePred R'],
        (∀ p, P₀ ≤ p → p.Prime → (R p ↔ R' p)) →
        ((Nat.primesBelow N).filter R).card ≤ ((Nat.primesBelow N).filter R').card + P₀ := by
      intro R R' _ _ hR
      calc ((Nat.primesBelow N).filter R).card
          ≤ ((Nat.primesBelow N).filter R' ∪ Finset.range P₀).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp
            simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_range]
            by_cases hp0 : P₀ ≤ p
            · exact Or.inl ⟨hp.1, (hR p hp0 hp.1.2).mp hp.2⟩
            · exact Or.inr (not_le.mp hp0)
        _ ≤ ((Nat.primesBelow N).filter R').card + (Finset.range P₀).card := Finset.card_union_le _ _
        _ = _ := by rw [Finset.card_range]
    have h1 := key Q Q' hQ
    have h2 := key Q' Q (fun p hp hpr => (hQ p hp hpr).symm)
    have h1' : (((Nat.primesBelow N).filter Q).card : ℝ) ≤ ((Nat.primesBelow N).filter Q').card + P₀ := by
      exact_mod_cast h1
    have h2' : (((Nat.primesBelow N).filter Q').card : ℝ) ≤ ((Nat.primesBelow N).filter Q).card + P₀ := by
      exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith
  have hdiff : Tendsto (fun N : ℕ => ((((Nat.primesBelow N).filter Q').card : ℝ) - ((Nat.primesBelow N).filter Q).card) / (Nat.primesBelow N).card) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => (P₀ : ℝ) / (Nat.primesBelow N).card) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hden.eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right (hbound N) hN.le
  have := h.add hdiff
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with N hN
  field_simp
  ring

/-- At the primes of good reduction of a minimal model, the coefficient `ModularityConjecture.WeierstrassCurve.ap` of formal-conjectures, computed from the given equation, is the coefficient $a_p$ of `WeierstrassCurve.LFunction`. The two agree at all but finitely many primes, because a Weierstrass equation is minimal and has good reduction at all but finitely many primes. -/
def ApAgree (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ P₀ : ℕ, ∀ p, P₀ ≤ p → p.Prime → (ModularityConjecture.WeierstrassCurve.ap E p : ℝ) = E.LFunction p

/-- The Hasse bound $|a_p| \le 2 \sqrt{p}$ at all but finitely many primes. Mathlib does not have it yet. -/
def HasseBound (E : WeierstrassCurve ℚ) : Prop :=
  ∃ P₀ : ℕ, ∀ p, P₀ ≤ p → p.Prime → |(E.LFunction p : ℝ)| ≤ 2 * √p

theorem hasCM_iff_hasCMOverQ (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    SatoTateConjecture.HasCM E ↔ HasCMOverQ E := by
  simp [SatoTateConjecture.HasCM, HasCMOverQ, SatoTateConjecture.cmJInvariants, cmJInvariants]

/-- **The Sato-Tate bridge.** With the Hasse bound and the agreement of the two definitions of $a_p$, `SatoTate` implies the statement `satoTate_conjecture` of formal-conjectures. The change of variable $t = \cos \theta$ takes the measure $\frac{2}{\pi} \sin^2 \theta \, d\theta$ to the measure of `satoTateCDF`. -/
theorem satoTate_conjecture_of_satoTate
    (hE : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ApAgree E ∧ HasseBound E)
    (h : SatoTate) : SatoTateConjecture.satoTate_conjecture := by
  intro E _ hCM a b ha hab hb
  obtain ⟨⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩⟩ := hE E
  have hST := h E ((hasCM_iff_hasCMOverQ E).not.mp hCM) (arccos b) (arccos a) (arccos_nonneg _)
    (strictAntiOn_arccos.antitoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab) (arccos_le_pi _)
  rw [satoTateMeasure_eq ha (hab.trans hb) (ha.trans hab) hb]
  classical
  have hST' : Tendsto (fun N : ℕ => (((Nat.primesBelow N).filter
      (fun p => satoTateAngle E p ∈ Set.Icc (arccos b) (arccos a))).card : ℝ) / (Nat.primesBelow N).card)
      atTop (𝓝 ((2 / π) * ∫ θ in (arccos b)..(arccos a), Real.sin θ ^ 2)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hST.congr fun N => ?_
    rw [card_primes_le_eq, card_primes_le_eq']
  refine tendsto_density_congr (max P₁ P₂) (fun p hp hpr => ?_) hST'
  have hap := hP₁ p (le_of_max_le_left hp) hpr
  have hbd := hP₂ p (le_of_max_le_right hp) hpr
  have hsq : 0 < 2 * √(p : ℝ) := by positivity [hpr.pos]
  set x := (E.LFunction p : ℝ) / (2 * √p) with hx
  have hx1 : -1 ≤ x ∧ x ≤ 1 := by
    rw [hx, le_div_iff₀ hsq, div_le_iff₀ hsq]
    constructor <;> linarith [abs_le.mp hbd]
  have hnorm : SatoTateConjecture.normalisedAp E p = x := by
    rw [SatoTateConjecture.normalisedAp, hap]
  simp only [hnorm, satoTateAngle, ← hx, Set.mem_Icc]
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := hx1
  have haI : a ∈ Set.Icc (-1 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Set.Icc (-1 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  rw [strictAntiOn_arccos.le_iff_ge hbI hxI, strictAntiOn_arccos.le_iff_ge hxI haI]
  exact and_comm

end SatoTate

section Ramanujan

open Langlands.Ported.FormalConjectures

/-- The discriminant form is a normalized Hecke eigenform of weight 12 and level 1 whose $q$-expansion has the coefficients $\tau(n)$ of the power series `RamanujanTau.Δ`. This is a theorem of Mordell and of Hecke. Mathlib does not have it yet, so the bridge takes it as a hypothesis. -/
def DeltaIsEigenform : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) 12,
    IsNormalizedEigenform f ∧ ∀ n : ℕ, qCoeff f n = (RamanujanTau.τ n : ℂ)

/-- **The Ramanujan bridge.** With `DeltaIsEigenform`, `RamanujanPeterssonHolomorphic` implies the statement `ramanujan_petersson` of formal-conjectures. This is the case $N = 1$ and $k = 12$, with $(12 - 1)/2 = 11/2$. -/
theorem ramanujan_petersson_of_ramanujanPeterssonHolomorphic (hΔ : DeltaIsEigenform)
    (h : RamanujanPeterssonHolomorphic) : RamanujanTau.ramanujan_petersson := by
  obtain ⟨f, hf, hτ⟩ := hΔ
  intro p hp
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have := h 1 12 f one_pos hf p hp' (fun hd => hp'.one_lt.ne' (Nat.dvd_one.mp hd))
  rw [hτ, Complex.norm_intCast] at this
  push_cast
  convert this using 3
  norm_num

end Ramanujan

end Langlands.Bridge
