/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.Hecke
import Langlands.Tate.DedekindMellin

/-!
# The trivial Hecke character

This file computes the data of `Langlands.HeckeFunctionalEquationAt` for the trivial Hecke character $\chi = 1$ of a number field $K$. The archimedean parameters $(n_v, t_v)$ of $\chi = 1$ are $0$ at each infinite place $v$. The archimedean factor for these parameters is $\Gamma_\mathbb{R}(s)^{r_1} \Gamma_\mathbb{C}(s)^{r_2} = 2^{r_2} \Gamma_K(s)$, with the function $\Gamma_K$ of `Langlands/Tate/DedekindMellin.lean`. The local factor at a finite place $v$ is $(1 - N(v)^{-s})^{-1}$.

## Main results

* `Langlands.Tate.isArchimedeanParameter_one_iff`: the parameters $(n, t)$ of $\chi = 1$ at $v$ are $n = 0$ and $t = 0$.
* `Langlands.Tate.gammaFactor_zero`: the archimedean factor for the parameters $0$ is $2^{r_2} \Gamma_K(s)$.
* `Langlands.Tate.localFactor_one`: the local factor of $\chi = 1$ at $v$ is $(1 - N(v)^{-s})^{-1}$.

## Implementation notes

The proof that $t = 0$ uses the elements $x$ of $K_v$ with $\iota(x) = e^y$ for all $y > 0$. The proof that $n = 0$ uses $x = -1$ at a real place, and the elements $x$ with $\iota(x) = e^{i y}$ at a complex place. Both proofs use `Langlands.Tate.eq_zero_of_exp_mul_eq_one`: if $e^{y z} = 1$ for each $y > 0$, then $z = 0$.
-/

namespace Langlands.Tate

open NumberField InfinitePlace Complex IsDedekindDomain

open scoped Real

variable {K : Type*} [Field K] [NumberField K]

/-- If $e^{y z} = 1$ for each real $y > 0$, then $z = 0$. -/
theorem eq_zero_of_exp_mul_eq_one {z : ℂ} (h : ∀ y : ℝ, 0 < y → exp (y * z) = 1) : z = 0 := by
  by_contra hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨k, hk⟩ := exp_eq_one_iff.1 (h ‖z‖⁻¹ (inv_pos.2 hpos))
  have h1 : ‖((‖z‖⁻¹ : ℝ) : ℂ) * z‖ = 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
  have h2 : ‖(k : ℂ) * (2 * π * I)‖ = |(k : ℝ)| * (2 * π) := by
    rw [norm_mul, norm_intCast, norm_mul, norm_I, mul_one, norm_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [hk, h2] at h1
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h1
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk0
  nlinarith [Real.pi_gt_three]

omit [NumberField K] in
/-- Each real number is the image of an element of the completion $K_v$ under the embedding $\iota : K_v \to \mathbb{C}$. -/
theorem exists_extensionEmbedding_eq_ofReal (v : InfinitePlace K) (r : ℝ) :
    ∃ x : v.Completion, Completion.extensionEmbedding v x = r := by
  by_cases hv : v.IsReal
  · obtain ⟨x, hx⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv r
    exact ⟨x, by rw [← Completion.extensionEmbeddingOfIsReal_apply hv, hx]⟩
  · exact Completion.surjective_extensionEmbedding_of_isComplex (not_isReal_iff_isComplex.1 hv) r

omit [NumberField K] in
/-- A unit $x$ of $K_v$ with a given nonzero image under $\iota$. -/
theorem exists_unit_extensionEmbedding_eq {v : InfinitePlace K} {z : ℂ} (hz : z ≠ 0)
    (h : ∃ x : v.Completion, Completion.extensionEmbedding v x = z) :
    ∃ x : v.Completionˣ, Completion.extensionEmbedding v x = z := by
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact hz hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

/-- The identity of the parameters of the trivial character at one unit $x$. -/
theorem one_eq_of_isArchimedeanParameter_one {v : InfinitePlace K} {n : ℤ} {t : ℂ}
    (h : (1 : HeckeCharacter K).IsArchimedeanParameter v n t) (x : v.Completionˣ) :
    (1 : ℂ) = (Completion.extensionEmbedding v x /
        (‖Completion.extensionEmbedding v x‖ : ℂ)) ^ n *
      (‖Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * t) := by
  rw [← h.eq x]
  simp [HeckeCharacter.infiniteComponent]

/-- The parameter $t$ of the trivial character is $0$. -/
theorem eq_zero_of_isArchimedeanParameter_one {v : InfinitePlace K} {n : ℤ} {t : ℂ}
    (h : (1 : HeckeCharacter K).IsArchimedeanParameter v n t) : t = 0 := by
  have hm : (v.mult : ℂ) ≠ 0 := by exact_mod_cast (mult_pos (w := v)).ne'
  suffices (v.mult : ℂ) * t = 0 by simpa [hm] using this
  refine eq_zero_of_exp_mul_eq_one fun y _ => ?_
  obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne')
    (exists_extensionEmbedding_eq_ofReal v (Real.exp y))
  have h1 := one_eq_of_isArchimedeanParameter_one h x
  have hn : ‖Completion.extensionEmbedding v x‖ = Real.exp y := by
    rw [hx, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
  rw [hn, hx, div_self (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'), one_zpow, one_mul,
    cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'), ← ofReal_log (Real.exp_pos y).le,
    Real.log_exp] at h1
  exact h1.symm

/-- The parameter $n$ of the trivial character is $0$. -/
theorem eq_zero_of_isArchimedeanParameter_one' {v : InfinitePlace K} {n : ℤ} {t : ℂ}
    (h : (1 : HeckeCharacter K).IsArchimedeanParameter v n t) : n = 0 := by
  have ht := eq_zero_of_isArchimedeanParameter_one h
  have h1 (x : v.Completionˣ) : (1 : ℂ) = (Completion.extensionEmbedding v x /
      (‖Completion.extensionEmbedding v x‖ : ℂ)) ^ n := by
    simpa [ht] using one_eq_of_isArchimedeanParameter_one h x
  by_cases hv : v.IsReal
  · rcases h.isReal hv with hn | hn
    · exact hn
    · have := h1 (-1)
      simp [hn] at this
      norm_num at this
  · have hc := not_isReal_iff_isComplex.1 hv
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

/-- **The parameters of the trivial character.** The archimedean parameters $(n, t)$ of $\chi = 1$ at an infinite place are $n = 0$ and $t = 0$. -/
theorem isArchimedeanParameter_one_iff (v : InfinitePlace K) (n : ℤ) (t : ℂ) :
    (1 : HeckeCharacter K).IsArchimedeanParameter v n t ↔ n = 0 ∧ t = 0 := by
  refine ⟨fun h => ⟨eq_zero_of_isArchimedeanParameter_one' h,
    eq_zero_of_isArchimedeanParameter_one h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact HeckeCharacter.isArchimedeanParameter_one K v

open scoped Classical in
variable (K) in
/-- The archimedean factor for the parameters $0$ is $\Gamma_\mathbb{R}(s)^{r_1} \Gamma_\mathbb{C}(s)^{r_2} = 2^{r_2} \Gamma_K(s)$. -/
theorem gammaFactor_zero (s : ℂ) :
    gammaFactor K 0 0 s = 2 ^ nrComplexPlaces K * gammaK K s := by
  rw [gammaK_eq, gammaFactor, Finset.prod_ite]
  simp only [Pi.zero_apply, add_zero, Int.cast_zero, abs_zero, zero_div, Finset.prod_const]
  rw [nrRealPlaces, nrComplexPlaces, Fintype.card_subtype, Fintype.card_subtype, div_pow]
  have hc : (Finset.univ.filter fun w : InfinitePlace K => ¬ w.IsReal) =
      Finset.univ.filter fun w : InfinitePlace K => w.IsComplex := by
    ext w
    simp [not_isReal_iff_isComplex]
  rw [hc]
  have h2 : (2 : ℂ) ^ (Finset.univ.filter fun w : InfinitePlace K => w.IsComplex).card ≠ 0 :=
    pow_ne_zero _ two_ne_zero
  field_simp

/-- The local factor of the trivial character at a finite place $v$ is $(1 - N(v)^{-s})^{-1}$. -/
theorem localFactor_one (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    (1 : HeckeCharacter K).localFactor v s = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp [HeckeCharacter.localFactor, HeckeCharacter.isUnramifiedAt_one, HeckeCharacter.finiteComponent]

end Langlands.Tate
