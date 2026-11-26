/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeUnramified

/-!
# Hecke's theorem for the twists of class group characters

Let $K$ be a number field, let $\chi$ be a Hecke character of class group type (`Langlands.Tate.IsClassType`), with class group character $\psi$, and let $s_0$ be a complex number. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each Hecke character $\xi$ with $\xi(x) = \chi(x) \|x\|^{s_0}$ for each idele $x$. It also shows that these are exactly the Hecke characters that are unramified at each finite place and equal to $|\cdot|_w^{s_0}$ at each infinite place $w$, for one $s_0$.

## Main definitions

* `Langlands.Tate.ideleNormPow`: the homomorphism $x \mapsto \|x\|^{s}$ from the idele group to $\mathbb{C}^\times$.
* `Langlands.Tate.normPowerChar`: the Hecke character $\|\cdot\|^{s}$.

## Main results

* `Langlands.Tate.localFactor_of_twist`, `Langlands.Tate.conductor_of_twist`, `Langlands.Tate.isArchimedeanParameter_of_twist`, `Langlands.Tate.completedLFunction_of_twist`: the local data of a twist $\xi = \chi \|\cdot\|^{s_0}$ of any Hecke character $\chi$.
* `Langlands.Tate.heckeFunctionalEquation_of_twist`: the conclusion of `HeckeFunctionalEquationAt K` for $\chi$ gives the conclusion for $\xi = \chi \|\cdot\|^{s_0}$.
* `Langlands.Tate.IsClassType.localFactor_twist`: the local factor of $\xi$ is $(1 - \psi([\mathfrak{p}_v]) N(\mathfrak{p}_v)^{-s - s_0})^{-1}$.
* `Langlands.Tate.IsClassType.isArchimedeanParameter_twist`: the archimedean parameters of $\xi$ are $n = 0$ and $t = s_0$.
* `Langlands.Tate.IsClassType.completedLFunction_twist`: $\Lambda(s, \xi) = \Lambda(s + s_0, \chi)$.
* `Langlands.Tate.IsClassType.heckeFunctionalEquation_twist`: the conclusion of `HeckeFunctionalEquationAt K` for $\xi$.
* `Langlands.Tate.continuous_ideleNorm`: the norm of ideles is continuous.
* `Langlands.Tate.exists_isClassType_twist_iff`: the characterization of the twists $\chi \|\cdot\|^{s_0}$.
* `Langlands.Tate.heckeFunctionalEquation_of_unramified`: the conclusion of `HeckeFunctionalEquationAt K` for each Hecke character that is unramified at each finite place and equal to $|\cdot|_w^{s_0}$ at each infinite place $w$.

## Proof

The character $\|\cdot\|^{s_0}$ is trivial on $\mathcal{O}_v^\times$ and has the value $N(\mathfrak{p}_v)^{-s_0}$ at the uniformizer. Thus $\xi$ and $\chi$ have the same conductor, the local factor of $\xi$ at $s$ is the local factor of $\chi$ at $s + s_0$, and the archimedean parameters $(n, t)$ of $\xi$ are the parameters $(n, t - s_0)$ of $\chi$. It follows that $\Lambda(s, \xi) = \Lambda(s + s_0, \chi)$ for each $s$. The functional equation of $\chi$ at $s + s_0$ is then the functional equation of $\xi$ at $s$, with $\sigma_\xi = \sigma_\chi + \mathrm{Re}\, s_0$ and $W_\xi = W_\chi (|d_K| N(\mathfrak{f}_\chi))^{\mathrm{Re}\, s_0 - s_0}$. For $\chi$ of class group type the functional equation of $\chi$ is `IsClassType.heckeFunctionalEquation`. If $\psi = 1$, then $\chi = 1$ and $\xi = \|\cdot\|^{s_0}$, and $\Lambda(s, \xi) = \Lambda_K(s + s_0)$ has simple poles at $-s_0$ and $1 - s_0$, as in `Langlands.Tate.heckeFunctionalEquationAt_normPower`. If $\psi \neq 1$, then $\Lambda(s, \xi) = 2^{r_2} |d_K|^{-(s + s_0)/2} \xi(s + s_0, \psi)$ is entire.

For the characterization, the norm of ideles is continuous because it is a homomorphism and it is equal to the norm of the infinite part near $1$. Thus $\|\cdot\|^{-s_0}$ is a Hecke character, and $\chi = \xi \|\cdot\|^{-s_0}$ is of class group type.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in Algebraic number theory (Cassels and Frohlich, eds.), 1967.
* J. Neukirch, Algebraic number theory, chapter VII, section 8.
-/

namespace Langlands.Tate

open NumberField InfinitePlace Complex IsDedekindDomain Filter Topology

variable {K : Type*} [Field K] [NumberField K]

section Twist

variable {χ ξ : HeckeCharacter K} {s₀ : ℂ}

/-- The component at an infinite place of the twist $\xi = \chi \|\cdot\|^{s_0}$ is $\xi_v(x) = \chi_v(x) |\iota(x)|^{m_v s_0}$. -/
theorem infiniteComponent_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : InfinitePlace K) (x : v.Completionˣ) :
    (ξ.infiniteComponent v x : ℂ) = (χ.infiniteComponent v x : ℂ) *
      (‖Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * s₀) := by
  have h := hξ (IdeleGroup.ofCompletion (𝓞 K) K v x)
  rw [ideleNorm_ofCompletion, ofReal_pow_cpow (norm_pos_iff.2 ((map_ne_zero _).2 x.ne_zero))] at h
  exact h

/-- The component at a finite place of the twist $\xi = \chi \|\cdot\|^{s_0}$ is $\xi_v(y) = \chi_v(y) |y|_v^{s_0}$. -/
theorem finiteComponent_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    (ξ.finiteComponent v y : ℂ) =
      (χ.finiteComponent v y : ℂ) * (‖(y : v.adicCompletion K)‖ : ℂ) ^ s₀ := by
  have h := hξ (IdeleGroup.ofAdicCompletion (𝓞 K) K v y)
  rw [ideleNorm_ofAdicCompletion] at h
  exact h

/-- The twist $\xi = \chi \|\cdot\|^{s_0}$ is trivial on $1 + \mathfrak{p}_v^m$ if and only if $\chi$ is trivial on $1 + \mathfrak{p}_v^m$. -/
theorem isTrivialOnHigherUnits_twist_iff
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ξ.IsTrivialOnHigherUnits v m ↔ χ.IsTrivialOnHigherUnits v m := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 →
      ξ.finiteComponent v x = χ.finiteComponent v x := fun x hx => Units.ext (by
    rw [finiteComponent_of_twist hξ, (Valued.toNormedField.norm_eq_one_iff).mpr hx]
    simp)
  exact ⟨fun h x hx hm => (key x hx).symm.trans (h x hx hm),
    fun h x hx hm => (key x hx).trans (h x hx hm)⟩

/-- The twist $\xi = \chi \|\cdot\|^{s_0}$ is unramified at $v$ if and only if $\chi$ is unramified at $v$. -/
theorem isUnramifiedAt_twist_iff
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) : ξ.IsUnramifiedAt v ↔ χ.IsUnramifiedAt v :=
  isTrivialOnHigherUnits_twist_iff hξ v 0

/-- The conductor of the twist $\xi = \chi \|\cdot\|^{s_0}$ is the conductor of $\chi$. -/
theorem conductor_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀) :
    ξ.conductor = χ.conductor := by
  have h (v : HeightOneSpectrum (𝓞 K)) : ξ.conductorExponent v = χ.conductorExponent v := by
    simp only [HeckeCharacter.conductorExponent, isTrivialOnHigherUnits_twist_iff hξ]
  simp only [HeckeCharacter.conductor, h]

/-- The local factor of the twist $\xi = \chi \|\cdot\|^{s_0}$ at $v$ is the local factor of $\chi$ at $s + s_0$. -/
theorem localFactor_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ξ.localFactor v s = χ.localFactor v (s + s₀) := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have harg : (Ideal.absNorm v.asIdeal : ℂ).arg ≠ Real.pi := by
    rw [natCast_arg]
    exact Real.pi_ne_zero.symm
  by_cases hu : χ.IsUnramifiedAt v
  · simp only [HeckeCharacter.localFactor, (isUnramifiedAt_twist_iff hξ v).2 hu, hu, ↓reduceIte]
    rw [finiteComponent_of_twist hξ, norm_localUniformizer, ofReal_inv, ofReal_natCast,
      inv_cpow _ _ harg, ← cpow_neg, mul_assoc, ← cpow_add _ _ hN,
      show -s₀ + -s = -(s + s₀) by ring]
  · simp only [HeckeCharacter.localFactor, mt (isUnramifiedAt_twist_iff hξ v).1 hu, hu,
      ↓reduceIte]

/-- The finite L-function of the twist $\xi = \chi \|\cdot\|^{s_0}$ is $L(s, \xi) = L(s + s_0, \chi)$, as an identity of Euler products at each $s$. -/
theorem finiteLFunction_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (s : ℂ) : ξ.finiteLFunction s = χ.finiteLFunction (s + s₀) :=
  tprod_congr fun v => localFactor_of_twist hξ v s

/-- If $(n, t)$ are archimedean parameters of the twist $\xi = \chi \|\cdot\|^{s_0}$ at $v$, then $(n, t - s_0)$ are archimedean parameters of $\chi$ at $v$. -/
theorem isArchimedeanParameter_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    {v : InfinitePlace K} {n : ℤ} {t : ℂ} (h : ξ.IsArchimedeanParameter v n t) :
    χ.IsArchimedeanParameter v n (t - s₀) := by
  refine ⟨h.isReal, fun x => ?_⟩
  have hx : (‖Completion.extensionEmbedding v x‖ : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (norm_ne_zero_iff.2 ((map_ne_zero _).2 x.ne_zero))
  have hc : (‖Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * s₀) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl hx)
  have e := h.eq x
  rw [infiniteComponent_of_twist hξ] at e
  rw [mul_sub, cpow_sub _ _ hx, ← mul_div_assoc, ← e, mul_div_cancel_right₀ _ hc]

variable (K) in
/-- A shift of the parameters $t_v$ by $-s_0$ moves the archimedean factor by $s_0$. -/
theorem gammaFactor_shift (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) (s₀ s : ℂ) :
    gammaFactor K n (fun v => t v - s₀) (s + s₀) = gammaFactor K n t s := by
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show s + s₀ + (t v - s₀) = s + t v by ring]

/-- The completed L-function of the twist $\xi = \chi \|\cdot\|^{s_0}$ is $\Lambda(s, \xi) = \Lambda(s + s_0, \chi)$, where the parameters of $\chi$ are $(n, t - s_0)$. -/
theorem completedLFunction_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) (s : ℂ) :
    ξ.completedLFunction n t s = χ.completedLFunction n (fun v => t v - s₀) (s + s₀) := by
  rw [HeckeCharacter.completedLFunction, HeckeCharacter.completedLFunction, gammaFactor_shift,
    finiteLFunction_of_twist hξ]

/-- If $\xi = \chi \|\cdot\|^{s_0}$, then $\xi^{-1} = \chi^{-1} \|\cdot\|^{-s_0}$. -/
theorem inv_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (x : IdeleGroup (𝓞 K) K) :
    (ξ⁻¹ x : ℂ) = (χ⁻¹ x : ℂ) * (ideleNorm K x : ℂ) ^ (-s₀) := by
  change (((ξ x)⁻¹ : ℂˣ) : ℂ) = (((χ x)⁻¹ : ℂˣ) : ℂ) * _
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hξ, mul_inv, cpow_neg]

/-- The conductor of a Hecke character is a nonzero ideal. -/
theorem conductor_ne_bot (χ : HeckeCharacter K) : χ.conductor ≠ ⊥ :=
  finprod_induction (fun I : Ideal (𝓞 K) => I ≠ ⊥) one_ne_zero
    (fun _ _ hI hJ => mul_ne_zero hI hJ) fun v => pow_ne_zero _ v.ne_bot

end Twist

section Shift

variable {χ ξ : HeckeCharacter K} {s₀ : ℂ}

/-- **The shift argument.** Let $\xi = \chi \|\cdot\|^{s_0}$ and let $(n, t)$ and $(n', t')$ be archimedean parameters for $\xi$ and $\xi^{-1}$. If the conclusion of `Langlands.HeckeFunctionalEquationAt K` holds for $\chi$ with the parameters $(n, t - s_0)$ and $(n', t' + s_0)$, then it holds for $\xi$ with the parameters $(n, t)$ and $(n', t')$. The constants are $\sigma_\xi = \sigma_\chi + \mathrm{Re}\, s_0$, $\Lambda_\xi(s) = \Lambda_\chi(s + s_0)$, $\Lambda'_\xi(u) = \Lambda'_\chi(u - s_0)$ and $W_\xi = W_\chi D^{\mathrm{Re}\, s_0 - s_0}$, where $D = |d_K| N(\mathfrak{f}_\chi)$. -/
theorem heckeFunctionalEquation_of_twist
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (h : ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(χ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
      ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
        MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
        (∀ s : ℂ, 1 - σ < s.re → Λ s = χ.completedLFunction n (fun v => t v - s₀) s) ∧
        (∀ s : ℂ, 1 + σ < s.re → Λ' s = χ⁻¹.completedLFunction n' (fun v => t' v + s₀) s) ∧
        ‖W‖ = 1 ∧
        (∀ s : ℂ, Λ s =
          W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
            Λ' (1 - s)) ∧
        ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
          ∃ s₁ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₁) ∧
            (∀ s : ℂ, s ≠ -s₁ → s ≠ 1 - s₁ → AnalyticAt ℂ Λ s) ∧
            meromorphicOrderAt Λ (-s₁) = -1 ∧ meromorphicOrderAt Λ (1 - s₁) = -1)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(ξ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = ξ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = ξ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm ξ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  obtain ⟨σ, hσ, Λ, Λ', W, hm, hm', hΛ, hΛ', hW, hfe, hpole⟩ := h
  have hξ' := inv_of_twist hξ
  set r : ℝ := ((|discr K| : ℤ) : ℝ) * (Ideal.absNorm χ.conductor : ℝ) with hr
  have hr0 : 0 < r := mul_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero K))
    (by exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.2 (conductor_ne_bot χ)))
  have hD : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) = (r : ℂ) := by
    rw [hr, ofReal_mul, ofReal_intCast, ofReal_natCast]
  have hD0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr0.ne'
  refine ⟨σ + s₀.re, fun x => ?_, fun s => Λ (s + s₀), fun u => Λ' (u - s₀),
    W * (r : ℂ) ^ ((s₀.re : ℂ) - s₀), fun s _ => ?_, fun s _ => ?_, fun s hs => ?_,
    fun s hs => ?_, ?_, fun s => ?_, ?_⟩
  · rw [hξ, norm_mul, hσ, norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x),
      Real.rpow_add (ideleNorm_pos x)]
  · exact meromorphicAt_fun_comp_add_const_iff_meromorphicAt.2 (hm _ trivial)
  · exact meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.2 (hm' _ trivial)
  · rw [completedLFunction_of_twist hξ]
    exact hΛ _ (by rw [add_re]; linarith)
  · have e := completedLFunction_of_twist hξ' n' t' s
    simp only [sub_neg_eq_add, ← sub_eq_add_neg] at e
    rw [e]
    exact hΛ' _ (by rw [sub_re]; linarith)
  · rw [norm_mul, hW, one_mul, norm_cpow_eq_rpow_re_of_pos hr0]
    simp
  · dsimp only
    rw [conductor_of_twist hξ, hD, hfe, hD, show 1 - (s + s₀) = 1 - s - s₀ by ring,
      show (1 / 2 - (s + s₀) - (σ : ℂ)) =
        ((s₀.re : ℂ) - s₀) + (1 / 2 - s - ((σ + s₀.re : ℝ) : ℂ)) by push_cast; ring,
      cpow_add _ _ hD0]
    ring
  · rcases hpole with hent | ⟨s₁, h1, h2, h3, h4⟩
    · exact Or.inl fun s => AnalyticAt.comp (g := Λ) (f := fun s => s + s₀) (hent _)
        (by fun_prop)
    · refine Or.inr ⟨s₁ + s₀, fun x => ?_, fun s hs0 hs1 => ?_, ?_, ?_⟩
      · rw [hξ, h1, ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne')]
      · exact AnalyticAt.comp (g := Λ) (f := fun s => s + s₀)
          (h2 _ (fun h => hs0 (by linear_combination h)) (fun h => hs1 (by linear_combination h)))
          (by fun_prop)
      · rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt,
          show -(s₁ + s₀) + s₀ = -s₁ by ring]
        exact h3
      · rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt,
          show 1 - (s₁ + s₀) + s₀ = 1 - s₁ by ring]
        exact h4

end Shift

section ClassTwist

variable {χ ξ : HeckeCharacter K} {s₀ : ℂ}

/-- **Step 1.** The twist $\xi = \chi \|\cdot\|^{s_0}$ of a character $\chi$ of class group type is unramified at each finite place. -/
theorem IsClassType.isUnramifiedAt_twist (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) : ξ.IsUnramifiedAt v :=
  (isUnramifiedAt_twist_iff hξ v).2 (hχ.unramified v)

/-- **Step 1.** The local factor of the twist $\xi = \chi \|\cdot\|^{s_0}$ at $v$ is $(1 - \psi([\mathfrak{p}_v]) N(\mathfrak{p}_v)^{-s - s_0})^{-1}$, where $\psi$ is the class group character of $\chi$. -/
theorem IsClassType.localFactor_twist (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ξ.localFactor v s = (1 - (classChar χ hχ (ClassGroup.mk0 (primeNZ v)) : ℂ) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s - s₀))⁻¹ := by
  rw [localFactor_of_twist hξ, hχ.localFactor_eq, hχ.classChar_mk0_primeNZ, neg_add']

/-- **Step 2.** The archimedean parameters of the twist $\xi = \chi \|\cdot\|^{s_0}$ of a character $\chi$ of class group type are $n = 0$ and $t = s_0$. -/
theorem IsClassType.isArchimedeanParameter_twist (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    {v : InfinitePlace K} {n : ℤ} {t : ℂ} (h : ξ.IsArchimedeanParameter v n t) :
    n = 0 ∧ t = s₀ := by
  have h' := hχ.isArchimedeanParameter (isArchimedeanParameter_of_twist hξ h)
  exact ⟨h'.1, sub_eq_zero.1 h'.2⟩

/-- A character of class group type has the archimedean parameters $n = 0$ and $t = 0$ at each infinite place. -/
theorem IsClassType.isArchimedeanParameter_zero (hχ : IsClassType χ) (v : InfinitePlace K) :
    χ.IsArchimedeanParameter v ((0 : InfinitePlace K → ℤ) v) ((0 : InfinitePlace K → ℂ) v) :=
  ⟨fun _ => Or.inl rfl, fun x => by simp [hχ.trivial_inf v x]⟩

/-- **Step 3.** The completed L-function of the twist $\xi = \chi \|\cdot\|^{s_0}$ is the completed L-function of $\chi$ at $s + s_0$, with the parameters $n = 0$ and $t = 0$ of $\chi$. -/
theorem IsClassType.completedLFunction_twist (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v)) (s : ℂ) :
    ξ.completedLFunction n t s = χ.completedLFunction 0 0 (s + s₀) := by
  obtain rfl : n = 0 := funext fun v => (hχ.isArchimedeanParameter_twist hξ (hn v)).1
  obtain rfl : t = fun _ => s₀ := funext fun v => (hχ.isArchimedeanParameter_twist hξ (hn v)).2
  rw [completedLFunction_of_twist hξ]
  congr 1
  funext v
  exact sub_self s₀

/-- **Step 3.** For $\psi \neq 1$ and $\mathrm{Re}(s + s_0) > 1$, the completed L-function of the twist $\xi = \chi \|\cdot\|^{s_0}$ is $2^{r_2} |d_K|^{-(s + s_0)/2} \xi(s + s_0, \psi)$, where $\xi(u, \psi)$ is the entire function `classCharLambda ψ`. -/
theorem IsClassType.completedLFunction_twist_eq_classCharLambda (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (hψ : classChar χ hχ ≠ 1) {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v)) {s : ℂ} (hs : 1 < (s + s₀).re) :
    ξ.completedLFunction n t s = 2 ^ nrComplexPlaces K *
      ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s + s₀)) * classCharLambda (classChar χ hχ) (s + s₀) := by
  rw [hχ.completedLFunction_twist hξ hn,
    hχ.completedLFunction_eq_classCharLambda hψ hχ.isArchimedeanParameter_zero hs]

/-- **Step 4. Hecke's theorem for the twists of class group characters.** Let $\chi$ be a Hecke character of class group type, let $s_0 \in \mathbb{C}$, and let $\xi$ be a Hecke character with $\xi(x) = \chi(x) \|x\|^{s_0}$ for each idele $x$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt K` holds for $\xi$. The proof shifts the functional equation `IsClassType.heckeFunctionalEquation` of $\chi$ by $s_0$ with `heckeFunctionalEquation_of_twist`. If $\psi = 1$, then $\chi = 1$ and $\Lambda$ has simple poles at $-s_0$ and $1 - s_0$; otherwise $\Lambda$ is entire. -/
theorem IsClassType.heckeFunctionalEquation_twist (hχ : IsClassType χ)
    (hξ : ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(ξ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = ξ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = ξ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm ξ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  have hξ' := inv_of_twist hξ
  refine heckeFunctionalEquation_of_twist hξ n n' t t' (hχ.heckeFunctionalEquation n n' _ _
    (fun v => isArchimedeanParameter_of_twist hξ (hn v)) (fun v => ?_))
  have h := isArchimedeanParameter_of_twist hξ' (hn' v)
  rwa [sub_neg_eq_add] at h

end ClassTwist

section NormCharacter

variable (K)

/-- The norm of ideles is multiplicative: $\|a b\| = \|a\| \|b\|$. -/
theorem ideleNorm_mul (a b : IdeleGroup (𝓞 K) K) :
    ideleNorm K (a * b) = ideleNorm K a * ideleNorm K b := by
  have hfa : Function.HasFiniteMulSupport (fun v => ‖(a : AdeleRing (𝓞 K) K).2 v‖) :=
    FiniteAdeleRing.hasFiniteMulSupport_norm
      (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom a)
  have hfb : Function.HasFiniteMulSupport (fun v => ‖(b : AdeleRing (𝓞 K) K).2 v‖) :=
    FiniteAdeleRing.hasFiniteMulSupport_norm
      (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom b)
  rw [ideleNorm, ideleNorm, ideleNorm, AdeleRing.norm_apply_of_isUnit (a * b).isUnit,
    AdeleRing.norm_apply_of_isUnit a.isUnit, AdeleRing.norm_apply_of_isUnit b.isUnit]
  have h1 : (∏ w, ‖((a * b : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) =
      (∏ w, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
        ∏ w, ‖(b : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by rw [← mul_pow, ← norm_mul]; rfl
  have h2 : (∏ᶠ v, ‖((a * b : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v‖) =
      (∏ᶠ v, ‖(a : AdeleRing (𝓞 K) K).2 v‖) * ∏ᶠ v, ‖(b : AdeleRing (𝓞 K) K).2 v‖ := by
    rw [← finprod_mul_distrib hfa hfb]
    exact finprod_congr fun v => by rw [← norm_mul]; rfl
  rw [h1, h2]
  ring

/-- **The product formula.** The norm of a principal idele is $1$. -/
theorem ideleNorm_unitEmbedding (x : Kˣ) :
    ideleNorm K (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 :=
  AdeleRing.norm_algebraMap_eq_one_of_ne_zero x.ne_zero

/-- The norm of the idele $1$ is $1$. -/
theorem ideleNorm_one : ideleNorm K 1 = 1 := by
  simpa using ideleNorm_unitEmbedding K 1

/-- The norm of ideles as a homomorphism to the multiplicative monoid of $\mathbb{R}$. -/
noncomputable def ideleNormHom : IdeleGroup (𝓞 K) K →* ℝ where
  toFun := ideleNorm K
  map_one' := ideleNorm_one K
  map_mul' := ideleNorm_mul K

/-- The norm of ideles is continuous. Near $1$ the finite components are units of $\mathcal{O}_v$, so the norm is the product of the infinite components. -/
theorem continuous_ideleNorm : Continuous (ideleNorm K) := by
  have hg : Continuous fun x : IdeleGroup (𝓞 K) K => ‖(x : AdeleRing (𝓞 K) K).1‖ := by
    simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finsetProd _ fun v _ =>
      (((continuous_apply v).comp (continuous_fst.comp Units.continuous_val)).norm).pow _
  have hA : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  have hO := RestrictedProduct.isOpen_forall_mem hA
  have h1 : {x : IdeleGroup (𝓞 K) K | ∀ v, (x : AdeleRing (𝓞 K) K).2 v ∈
      v.adicCompletionIntegers K} ∈ 𝓝 1 :=
    (hO.preimage (continuous_snd.comp Units.continuous_val :
      Continuous fun x : IdeleGroup (𝓞 K) K => (x : AdeleRing (𝓞 K) K).2)).mem_nhds
      fun v => one_mem _
  have h2 : {x : IdeleGroup (𝓞 K) K | ∀ v, ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v ∈
      v.adicCompletionIntegers K} ∈ 𝓝 1 :=
    (hO.preimage (continuous_snd.comp Units.continuous_coe_inv :
      Continuous fun x : IdeleGroup (𝓞 K) K =>
        ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2)).mem_nhds
      fun v => one_mem _
  have hV : (fun x : IdeleGroup (𝓞 K) K => ‖(x : AdeleRing (𝓞 K) K).1‖) =ᶠ[𝓝 1]
      ideleNormHom K := by
    filter_upwards [h1, h2] with x hx1 hx2
    have hv : ∀ v, ‖(x : AdeleRing (𝓞 K) K).2 v‖ = 1 := fun v => by
      have e := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) (Units.mul_inv x)
      change (x : AdeleRing (𝓞 K) K).2 v *
        ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v = 1 at e
      have ha := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx1 v)
      have hb := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx2 v)
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      refine (Valued.toNormedField.norm_eq_one_iff).mpr (le_antisymm ha ?_)
      simpa using e'.symm.le.trans (mul_le_mul_right hb _)
    change _ = ‖(x : AdeleRing (𝓞 K) K)‖
    rw [AdeleRing.norm_def, FiniteAdeleRing.norm_def, tprod_congr hv, tprod_one, mul_one]
  exact continuous_of_continuousAt_one (ideleNormHom K) (hg.continuousAt.congr hV)

/-- The homomorphism $x \mapsto \|x\|^{s}$ from the idele group to $\mathbb{C}^\times$. -/
noncomputable def ideleNormPow (s : ℂ) : IdeleGroup (𝓞 K) K →* ℂˣ where
  toFun x := Units.mk0 ((ideleNorm K x : ℂ) ^ s)
    (Complex.cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 (ideleNorm_pos x).ne')))
  map_one' := Units.ext (by simp [ideleNorm_one])
  map_mul' a b := Units.ext (by
    simp only [Units.val_mk0, Units.val_mul, ideleNorm_mul, ofReal_mul]
    exact mul_cpow_ofReal_nonneg (ideleNorm_pos a).le (ideleNorm_pos b).le s)

/-- The homomorphism $x \mapsto \|x\|^{s}$ is continuous. -/
theorem continuous_ideleNormPow (s : ℂ) : Continuous (ideleNormPow K s) := by
  have hc : Continuous fun x : IdeleGroup (𝓞 K) K => (ideleNorm K x : ℂ) :=
    continuous_ofReal.comp (continuous_ideleNorm K)
  have hslit : ∀ x : IdeleGroup (𝓞 K) K, (ideleNorm K x : ℂ) ∈ slitPlane :=
    fun x => ofReal_mem_slitPlane.2 (ideleNorm_pos x)
  have hp : Continuous fun x : IdeleGroup (𝓞 K) K => (ideleNorm K x : ℂ) ^ s :=
    hc.cpow continuous_const hslit
  refine Units.continuous_iff.2 ⟨hp, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hp.inv₀ fun x =>
    Complex.cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 (ideleNorm_pos x).ne'))

/-- The Hecke character $\|\cdot\|^{s}$. It is well defined on the idele class group by the product formula. -/
noncomputable def normPowerChar (s : ℂ) : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift _ (ideleNormPow K s) (by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    change (ideleNorm K (IdeleGroup.unitEmbedding (𝓞 K) K x) : ℂ) ^ s = 1
    rw [ideleNorm_unitEmbedding, ofReal_one, one_cpow])
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleNormPow K s)

/-- The value of $\|\cdot\|^{s}$ at an idele $x$ is $\|x\|^{s}$. -/
theorem normPowerChar_apply (s : ℂ) (x : IdeleGroup (𝓞 K) K) :
    (normPowerChar K s x : ℂ) = (ideleNorm K x : ℂ) ^ s := rfl

end NormCharacter

section Characterization

variable {χ ξ : HeckeCharacter K} {s₀ : ℂ}

/-- The twist $\chi \|\cdot\|^{s_0}$, as a product of Hecke characters, satisfies the hypothesis of the results of this file. -/
theorem mul_normPowerChar_apply (χ : HeckeCharacter K) (s₀ : ℂ) (x : IdeleGroup (𝓞 K) K) :
    ((χ * normPowerChar K s₀) x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀ := rfl

/-- **Step 5. The characterization.** A Hecke character $\xi$ is a twist $\chi \|\cdot\|^{s_0}$ of a character $\chi$ of class group type if and only if $\xi$ is unramified at each finite place and $\xi_w(y) = |\iota(y)|^{m_w s_0}$ at each infinite place $w$, that is $\xi_w = |\cdot|_w^{s_0}$ with the normalized absolute value $|\cdot|_w$. -/
theorem exists_isClassType_twist_iff (ξ : HeckeCharacter K) (s₀ : ℂ) :
    ((∀ v, ξ.IsUnramifiedAt v) ∧ ∀ (w : InfinitePlace K) (y : w.Completionˣ),
      (ξ.infiniteComponent w y : ℂ) =
        (‖Completion.extensionEmbedding w y‖ : ℂ) ^ ((w.mult : ℂ) * s₀)) ↔
    ∃ χ : HeckeCharacter K, IsClassType χ ∧
      ∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ s₀ := by
  constructor
  · rintro ⟨hu, hinf⟩
    have hχ : ∀ x : IdeleGroup (𝓞 K) K,
        (ξ x : ℂ) = ((ξ * normPowerChar K (-s₀)) x : ℂ) * (ideleNorm K x : ℂ) ^ s₀ := fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]
    refine ⟨ξ * normPowerChar K (-s₀), ⟨fun v => (isUnramifiedAt_twist_iff hχ v).1 (hu v),
      fun w y => Units.ext ?_⟩, hχ⟩
    have hc : (‖Completion.extensionEmbedding w y‖ : ℂ) ^ ((w.mult : ℂ) * s₀) ≠ 0 :=
      Complex.cpow_ne_zero_iff.2
        (Or.inl (ofReal_ne_zero.2 (norm_ne_zero_iff.2 ((map_ne_zero _).2 y.ne_zero))))
    have h := infiniteComponent_of_twist hχ w y
    rw [hinf] at h
    rw [Units.val_one]
    exact mul_right_cancel₀ hc (h.symm.trans (one_mul _).symm)
  · rintro ⟨χ, hχ, hξ⟩
    refine ⟨hχ.isUnramifiedAt_twist hξ, fun w y => ?_⟩
    rw [infiniteComponent_of_twist hξ, hχ.trivial_inf w y, Units.val_one, one_mul]

/-- **Hecke's theorem for the characters $\chi \|\cdot\|^{s_0}$.** For a character $\chi$ of class group type and $s_0 \in \mathbb{C}$, the conclusion of `Langlands.HeckeFunctionalEquationAt K` holds for the Hecke character $\chi \|\cdot\|^{s_0}$. -/
theorem IsClassType.heckeFunctionalEquation_mul_normPowerChar (hχ : IsClassType χ) (s₀ : ℂ)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, (χ * normPowerChar K s₀).IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, (χ * normPowerChar K s₀)⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖((χ * normPowerChar K s₀) x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = (χ * normPowerChar K s₀).completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = (χ * normPowerChar K s₀)⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) *
          (Ideal.absNorm (χ * normPowerChar K s₀).conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₁ : ℂ, (∀ x : IdeleGroup (𝓞 K) K,
            ((χ * normPowerChar K s₀) x : ℂ) = (ideleNorm K x : ℂ) ^ s₁) ∧
          (∀ s : ℂ, s ≠ -s₁ → s ≠ 1 - s₁ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₁) = -1 ∧ meromorphicOrderAt Λ (1 - s₁) = -1) :=
  hχ.heckeFunctionalEquation_twist (mul_normPowerChar_apply χ s₀) n n' t t' hn hn'

/-- **Hecke's theorem for the unramified characters with equal infinite exponents.** Let $\xi$ be a Hecke character that is unramified at each finite place, with $\xi_w = |\cdot|_w^{s_0}$ at each infinite place $w$ for one $s_0 \in \mathbb{C}$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt K` holds for $\xi$. -/
theorem heckeFunctionalEquation_of_unramified (ξ : HeckeCharacter K) (s₀ : ℂ)
    (hu : ∀ v, ξ.IsUnramifiedAt v)
    (hinf : ∀ (w : InfinitePlace K) (y : w.Completionˣ), (ξ.infiniteComponent w y : ℂ) =
      (‖Completion.extensionEmbedding w y‖ : ℂ) ^ ((w.mult : ℂ) * s₀))
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(ξ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = ξ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = ξ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm ξ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (ξ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1) := by
  obtain ⟨χ, hχ, hξ⟩ := (exists_isClassType_twist_iff ξ s₀).1 ⟨hu, hinf⟩
  exact hχ.heckeFunctionalEquation_twist hξ n n' t t' hn hn'

end Characterization

end Langlands.Tate
