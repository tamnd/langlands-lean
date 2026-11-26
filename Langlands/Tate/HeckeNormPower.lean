/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeTrivial

/-!
# Hecke's theorem for the characters $\|\cdot\|^{s_0}$

Let $K$ be a number field and let $\chi$ be a Hecke character with $\chi(x) = \|x\|^{s_0}$ for each idele $x$, where $\|\cdot\|$ is the idele norm and $s_0$ is a complex number. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi$. These are the characters for which the completed $L$-function has poles, so this file completes the polar case of Hecke's theorem.

The proof reduces each part of the statement to the case $\chi = 1$ of `Langlands/Tate/HeckeTrivial.lean`. The local components are $\chi_v(x) = |\iota(x)|^{m_v s_0}$ at an infinite place and $\chi_v(y) = |y|_v^{s_0}$ at a finite place. Thus the archimedean parameters are $n = 0$ and $t = s_0$, the character is unramified everywhere, and the local factor at $v$ is $(1 - N(v)^{-(s + s_0)})^{-1}$. It follows that $\Lambda(s, \chi) = \Lambda_K(s + s_0)$ for $\mathrm{Re}(s + s_0) > 1$, where $\Lambda_K$ is `Langlands.Tate.heckeLambdaOne`. The constants are $\sigma = \mathrm{Re}\, s_0$ and $W = |d_K|^{\sigma - s_0}$, and the poles are at $-s_0$ and $1 - s_0$.

## Main results

* `Langlands.Tate.ideleNorm_ofCompletion` and `Langlands.Tate.ideleNorm_ofAdicCompletion`: the norm of an idele with one nontrivial component.
* `Langlands.Tate.isArchimedeanParameter_of_normPower`: the archimedean parameters of $\|\cdot\|^{s_0}$ are $n = 0$ and $t = s_0$.
* `Langlands.Tate.conductor_of_normPower`: the conductor of $\|\cdot\|^{s_0}$ is $(1)$.
* `Langlands.Tate.completedLFunction_of_normPower`: $\Lambda(s, \|\cdot\|^{s_0}) = \Lambda_K(s + s_0)$.
* `Langlands.Tate.heckeFunctionalEquationAt_normPower`: the conclusion of `HeckeFunctionalEquationAt K` for $\chi = \|\cdot\|^{s_0}$.
-/

namespace Langlands.Tate

open NumberField InfinitePlace Complex IsDedekindDomain Filter Topology

variable {K : Type*} [Field K] [NumberField K]

section IdeleNorm

theorem ideleNorm_ofCompletion (v : InfinitePlace K) (x : v.Completionˣ) :
    ideleNorm K (IdeleGroup.ofCompletion (𝓞 K) K v x) =
      ‖Completion.extensionEmbedding v x‖ ^ v.mult := by
  classical
  rw [ideleNorm, show ((IdeleGroup.ofCompletion (𝓞 K) K v x : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K) = AdeleRing.ofCompletion (𝓞 K) K v (x : v.Completion) from rfl,
    AdeleRing.ofCompletion_apply, AdeleRing.norm_def]
  dsimp only
  rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_def]
  simp only [InfiniteAdeleRing.ofCompletion_apply]
  rw [Finset.prod_eq_single v (fun w _ hw => by rw [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ v) h), Pi.mulSingle_eq_same]
  have h1 : ∏' w : HeightOneSpectrum (𝓞 K), ‖(1 : FiniteAdeleRing (𝓞 K) K) w‖ = 1 := by
    simp only [show ∀ w, (1 : FiniteAdeleRing (𝓞 K) K) w = 1 from fun _ => rfl, norm_one, tprod_one]
  rw [h1, mul_one, (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]

theorem ideleNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    ideleNorm K (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = ‖(y : v.adicCompletion K)‖ := by
  classical
  rw [ideleNorm, show ((IdeleGroup.ofAdicCompletion (𝓞 K) K v y : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K) = AdeleRing.ofAdicCompletion (𝓞 K) K v (y : v.adicCompletion K) from rfl,
    AdeleRing.ofAdicCompletion_apply, AdeleRing.norm_def]
  dsimp only
  rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_def]
  have h1 : ∏ w : InfinitePlace K, ‖(1 : InfiniteAdeleRing K) w‖ ^ w.mult = 1 := by
    simp only [show ∀ w, (1 : InfiniteAdeleRing K) w = 1 from fun _ => rfl, norm_one, one_pow,
      Finset.prod_const_one]
  rw [h1, one_mul, tprod_eq_mulSingle v (fun w hw => by
    change ‖(Pi.mulSingle v (y : v.adicCompletion K) w : w.adicCompletion K)‖ = 1
    rw [Pi.mulSingle_eq_of_ne hw, norm_one])]
  change ‖(Pi.mulSingle v (y : v.adicCompletion K) v : v.adicCompletion K)‖ = _
  rw [Pi.mulSingle_eq_same]

theorem norm_localUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ‖((localUniformizer K v : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have h := (v.valuation_exists_uniformizer K).choose_spec
  have := FinitePlace.norm_embedding' (K := K) v (uniformizer K v)
  change ‖FinitePlace.embedding v (uniformizer K v)‖ = _
  rw [this, uniformizer, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    WithZero.log_exp]
  simp

/-- The norm of an idele is positive. -/
theorem ideleNorm_pos (x : IdeleGroup (𝓞 K) K) : 0 < ideleNorm K x := by
  have hx : IsUnit (x : AdeleRing (𝓞 K) K) := x.isUnit
  rw [ideleNorm, AdeleRing.norm_apply_of_isUnit hx]
  obtain ⟨h1, h2, -⟩ := AdeleRing.isUnit_iff.1 hx
  exact mul_pos (Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (h1 v)) _)
    (lt_of_le_of_ne (finprod_nonneg fun v => norm_nonneg _)
      (finprod_ne_zero fun v => norm_ne_zero_iff.2 (h2 v)).symm)

end IdeleNorm

section NormPower

/-- For $r > 0$, $(r^m)^s = r^{m s}$. -/
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 < r) (m : ℕ) (s : ℂ) :
    ((r ^ m : ℝ) : ℂ) ^ s = (r : ℂ) ^ ((m : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (pow_pos hr m).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.2 hr.ne'), ← ofReal_log (pow_pos hr m).le,
    ← ofReal_log hr.le, Real.log_pow]
  push_cast
  ring_nf

omit [NumberField K] in
/-- If $(\iota(x) / |\iota(x)|)^n |\iota(x)|^{m_v t} = 1$ for each unit $x$ of $K_v$, and $n$ is $0$ or $1$ at a real place, then $n = 0$ and $t = 0$. -/
theorem eq_zero_of_forall_param_eq_one {v : InfinitePlace K} {n : ℤ} {t : ℂ}
    (hv : v.IsReal → n = 0 ∨ n = 1)
    (h : ∀ x : v.Completionˣ, (Completion.extensionEmbedding v x /
        (‖Completion.extensionEmbedding v x‖ : ℂ)) ^ n *
      (‖Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * t) = 1) :
    n = 0 ∧ t = 0 := by
  have ht : t = 0 := by
    have hm : (v.mult : ℂ) ≠ 0 := by exact_mod_cast (mult_pos (w := v)).ne'
    suffices (v.mult : ℂ) * t = 0 by simpa [hm] using this
    refine eq_zero_of_exp_mul_eq_one fun y _ => ?_
    obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq
      (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne') (exists_extensionEmbedding_eq_ofReal v (Real.exp y))
    have h1 := h x
    have hn : ‖Completion.extensionEmbedding v x‖ = Real.exp y := by
      rw [hx, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
    rw [hn, hx, div_self (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'), one_zpow, one_mul,
      cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'),
      ← ofReal_log (Real.exp_pos y).le, Real.log_exp] at h1
    exact h1
  refine ⟨?_, ht⟩
  have h1 (x : v.Completionˣ) : (1 : ℂ) = (Completion.extensionEmbedding v x /
      (‖Completion.extensionEmbedding v x‖ : ℂ)) ^ n := by
    simpa [ht] using (h x).symm
  by_cases hr : v.IsReal
  · rcases hv hr with hn | hn
    · exact hn
    · have := h1 (-1)
      simp [hn] at this
      norm_num at this
  · have hc := not_isReal_iff_isComplex.1 hr
    suffices (n : ℂ) * I = 0 by simpa using this
    refine eq_zero_of_exp_mul_eq_one fun y _ => ?_
    obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq (exp_ne_zero (y * I))
      (Completion.surjective_extensionEmbedding_of_isComplex hc (exp (y * I)))
    have h2 := h1 x
    have hn : ‖Completion.extensionEmbedding v x‖ = 1 := by
      rw [hx, norm_exp_ofReal_mul_I]
    rw [hn, hx, ofReal_one, div_one, ← exp_int_mul] at h2
    rw [show (y : ℂ) * (n * I) = n * (y * I) by ring]
    exact h2.symm

variable {χ : HeckeCharacter K} {s₀ : ℂ}

/-- The component at an infinite place of $\chi = \|\cdot\|^{s_0}$ is $\chi_v(x) = |\iota(x)|^{m_v s_0}$. -/
theorem infiniteComponent_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (v : InfinitePlace K) (x : v.Completionˣ) :
    (χ.infiniteComponent v x : ℂ) =
      (‖Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * s₀) := by
  have h := hχ (IdeleGroup.ofCompletion (𝓞 K) K v x)
  rw [ideleNorm_ofCompletion, ofReal_pow_cpow (norm_pos_iff.2 ((map_ne_zero _).2 x.ne_zero))] at h
  exact h

/-- The archimedean parameters of $\chi = \|\cdot\|^{s_0}$ are $n = 0$ and $t = s_0$. -/
theorem isArchimedeanParameter_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    {v : InfinitePlace K} {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v n t) :
    n = 0 ∧ t = s₀ := by
  have key := eq_zero_of_forall_param_eq_one (t := t - s₀) h.isReal fun x => by
    have hx : (‖Completion.extensionEmbedding v x‖ : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (norm_ne_zero_iff.2 ((map_ne_zero _).2 x.ne_zero))
    have e := h.eq x
    rw [infiniteComponent_of_normPower hχ] at e
    rw [mul_sub, cpow_sub _ _ hx, ← mul_div_assoc, ← e,
      div_self (Complex.cpow_ne_zero_iff.2 (Or.inl hx))]
  exact ⟨key.1, sub_eq_zero.1 key.2⟩

/-- The component at a finite place of $\chi = \|\cdot\|^{s_0}$ is $\chi_v(y) = |y|_v^{s_0}$. -/
theorem finiteComponent_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    (χ.finiteComponent v y : ℂ) = (‖(y : v.adicCompletion K)‖ : ℂ) ^ s₀ := by
  have h := hχ (IdeleGroup.ofAdicCompletion (𝓞 K) K v y)
  rw [ideleNorm_ofAdicCompletion] at h
  exact h

/-- The character $\|\cdot\|^{s_0}$ is trivial on the units of $\mathcal{O}_v$. -/
theorem isTrivialOnHigherUnits_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) : χ.IsTrivialOnHigherUnits v m := by
  intro x hx _
  refine Units.ext ?_
  rw [finiteComponent_of_normPower hχ, (Valued.toNormedField.norm_eq_one_iff).mpr hx]
  simp

/-- The conductor of $\|\cdot\|^{s_0}$ is the unit ideal. -/
theorem conductor_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) :
    χ.conductor = 1 := by
  have h (v : HeightOneSpectrum (𝓞 K)) : χ.conductorExponent v = 0 :=
    Nat.sInf_eq_zero.mpr (Or.inl (isTrivialOnHigherUnits_of_normPower hχ v 0))
  simp only [HeckeCharacter.conductor, h, pow_zero]
  exact finprod_one

/-- The local factor of $\|\cdot\|^{s_0}$ at $v$ is the local factor of $\chi = 1$ at $s + s_0$. -/
theorem localFactor_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    χ.localFactor v s = (1 : HeckeCharacter K).localFactor v (s + s₀) := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have harg : (Ideal.absNorm v.asIdeal : ℂ).arg ≠ Real.pi := by
    rw [natCast_arg]
    exact Real.pi_ne_zero.symm
  have hu : χ.IsUnramifiedAt v := isTrivialOnHigherUnits_of_normPower hχ v 0
  rw [localFactor_one]
  simp only [HeckeCharacter.localFactor, hu, ↓reduceIte]
  rw [finiteComponent_of_normPower hχ, norm_localUniformizer, ofReal_inv, ofReal_natCast,
    inv_cpow _ _ harg, ← cpow_neg, ← cpow_add _ _ hN, show -s₀ + -s = -(s + s₀) by ring]

/-- For $\mathrm{Re}(s + s_0) > 1$, the finite L-function of $\|\cdot\|^{s_0}$ is $\zeta_K(s + s_0)$. -/
theorem finiteLFunction_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    {s : ℂ} (hs : 1 < (s + s₀).re) :
    χ.finiteLFunction s = dedekindZeta K (s + s₀) := by
  rw [← finiteLFunction_one K hs, HeckeCharacter.finiteLFunction, HeckeCharacter.finiteLFunction]
  exact tprod_congr fun v => localFactor_of_normPower hχ v s

variable (K) in
/-- A constant parameter $t = s_0$ moves the archimedean factor by $s_0$. -/
theorem gammaFactor_const (s₀ s : ℂ) :
    gammaFactor K 0 (fun _ => s₀) s = gammaFactor K 0 0 (s + s₀) := by
  simp [gammaFactor]

/-- For $\mathrm{Re}(s + s_0) > 1$, the completed L-function of $\|\cdot\|^{s_0}$ is $\Lambda(s + s_0)$, where $\Lambda$ is the completed Dedekind zeta function of `heckeLambdaOne`. -/
theorem completedLFunction_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v)) {s : ℂ} (hs : 1 < (s + s₀).re) :
    χ.completedLFunction n t s = heckeLambdaOne K (s + s₀) := by
  have hn0 : n = 0 := funext fun v => (isArchimedeanParameter_of_normPower hχ (hn v)).1
  have ht0 : t = fun _ => s₀ := funext fun v => (isArchimedeanParameter_of_normPower hχ (hn v)).2
  subst hn0 ht0
  rw [HeckeCharacter.completedLFunction, gammaFactor_const, gammaFactor_zero,
    finiteLFunction_of_normPower hχ hs, heckeLambdaOne_eq K hs]

/-- If $\chi = \|\cdot\|^{s_0}$, then $\chi^{-1} = \|\cdot\|^{-s_0}$. -/
theorem inv_of_normPower
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (x : IdeleGroup (𝓞 K) K) : (χ⁻¹ x : ℂ) = (ideleNorm K x : ℂ) ^ (-s₀) := by
  rw [cpow_neg, ← hχ x]
  exact Units.val_inv_eq_inv_val (χ x)

/-- **Hecke's theorem for the characters $\|\cdot\|^{s_0}$.** This is the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi = \|\cdot\|^{s_0}$, with $\sigma = \mathrm{Re}\, s_0$, $\Lambda(s) = \Lambda_K(s + s_0)$ and $W = |d_K|^{\sigma - s_0}$. -/
theorem heckeFunctionalEquationAt_normPower (χ : HeckeCharacter K) (s₀ : ℂ)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(χ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = χ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = χ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  have hχ' := inv_of_normPower hχ
  have hD : (((|discr K| : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast abs_ne_zero.2 (discr_ne_zero K)
  have hD' : (0 : ℝ) < ((|discr K| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.2 (discr_ne_zero K)
  refine ⟨s₀.re, fun x => ?_, fun s => heckeLambdaOne K (s + s₀),
    fun u => heckeLambdaOne' K (u - s₀), ((|discr K| : ℤ) : ℂ) ^ ((s₀.re : ℂ) - s₀),
    fun s _ => ?_, fun s _ => ?_, fun s hs => ?_, fun s hs => ?_, ?_, fun s => ?_,
    Or.inr ⟨s₀, hχ, fun s h0 h1 => ?_, ?_, ?_⟩⟩
  · rw [hχ, norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x)]
  · exact meromorphicAt_fun_comp_add_const_iff_meromorphicAt.2
      (meromorphicOn_heckeLambdaOne K _ trivial)
  · exact meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.2
      (meromorphicOn_heckeLambdaOne' K _ trivial)
  · exact (completedLFunction_of_normPower hχ hn (by rw [add_re]; linarith)).symm
  · have h1 : 1 < (s - s₀).re := by rw [sub_re]; linarith
    dsimp only
    rw [completedLFunction_of_normPower hχ' hn' (by rwa [← sub_eq_add_neg]), ← sub_eq_add_neg,
      heckeLambdaOne_eq K h1, heckeLambdaOne'_eq K h1]
  · rw [← Complex.ofReal_intCast, norm_cpow_eq_rpow_re_of_pos hD']
    simp
  · dsimp only
    rw [conductor_of_normPower hχ, map_one, Nat.cast_one, mul_one, heckeLambdaOne_eq_discr_cpow_mul K,
      ← cpow_add _ _ hD]
    congr 2
    all_goals ring
  · exact AnalyticAt.comp (g := heckeLambdaOne K) (f := fun s => s + s₀)
      (analyticAt_heckeLambdaOne K (fun h => h0 (eq_neg_of_add_eq_zero_left h))
        (fun h => h1 (eq_sub_of_add_eq h))) (by fun_prop)
  · rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, neg_add_cancel]
    exact meromorphicOrderAt_heckeLambdaOne_zero K
  · rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, sub_add_cancel]
    exact meromorphicOrderAt_heckeLambdaOne_one K

end NormPower

end Langlands.Tate
