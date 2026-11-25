/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Hecke
import Langlands.Tate.ArchimedeanFourier

/-!
# The archimedean local theory for a Hecke character

This file connects the local theory at the real and complex places to the Hecke characters of `Langlands.Statements.Hecke`. It gives the facts that a global proof of Hecke's functional equation needs at the infinite places of a number field $K$.

## Parameters

Let $\chi$ be a Hecke character with archimedean parameters $(n_v, t_v)$, in the sense of `Langlands.HeckeCharacter.IsArchimedeanParameter`. With $\iota_v : K_v \to \mathbb{C}$ the embedding of the completion, this means $\chi_v(x) = (\iota_v(x) / |\iota_v(x)|)^{n_v} |\iota_v(x)|^{m_v t_v}$, where $m_v$ is $1$ at a real place and $2$ at a complex place. This is the function `Langlands.Tate.archChar` of `Langlands.Tate.ArchimedeanZeta`, evaluated at $\iota_v(x)$ (`Langlands.HeckeCharacter.IsArchimedeanParameter.eq_archChar`).

The character $\chi^{-1}$ has the parameters $(n_v, -t_v)$ at a real place and $(-n_v, -t_v)$ at a complex place (`Langlands.HeckeCharacter.IsArchimedeanParameter.inv`). At a real place the sign character is its own inverse, because $\iota_v(x)$ is real.

## The Gamma factor

The function `Langlands.gammaFactor` is the product of the local factors `Langlands.Tate.archGamma`. Its inverse is entire (`Langlands.Tate.differentiable_gammaFactor_inv`), so it is meromorphic on $\mathbb{C}$ and analytic at every point where it does not vanish. It does not vanish on the half plane where $\mathrm{Re}(s + t_v) > 0$ for all $v$.

## Products of local zeta integrals

For each infinite place $v$ let $f_v$ be the standard test function of $\chi_v$ and let $Z_v(s) = Z(f_v, \chi_v, s)$ (`Langlands.Tate.archZeta`). Let $\hat Z_v(s) = Z(\hat f_v, \chi_v^{-1}, 1 - s)$ (`Langlands.Tate.archDualZeta`). Then:

* `Langlands.Tate.prod_archZeta`: $\prod_v Z_v(s) = \pi^{r_2} L_\infty(s, \chi)$, where $L_\infty$ is `Langlands.gammaFactor` and $r_2$ is the number of complex places.
* `Langlands.Tate.prod_archDualZeta`: $\prod_v \hat Z_v(s) = W_\infty \pi^{r_2} L_\infty(1 - s, \chi^{-1})$, where $W_\infty = \prod_v \varepsilon_v$ is the product of the local root numbers (`Langlands.Tate.archRootNumber`). It has absolute value one (`Langlands.Tate.norm_prod_archRootNumber`).
* `Langlands.Tate.prod_archDualZeta_eq`: the product of the local functional equations, $\prod_v \hat Z_v(s) = W_\infty \frac{L_\infty(1 - s, \chi^{-1})}{L_\infty(s, \chi)} \prod_v Z_v(s)$.

All these hold for $0 < \mathrm{Re}(s + t_v) < 1$ at every place, where both sides are given by convergent integrals.
-/

namespace Langlands

open NumberField Complex

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable {χ : HeckeCharacter K} {v : InfinitePlace K} {n : ℤ} {t : ℂ}

/-- The local component of a Hecke character is the quasi-character `Langlands.Tate.archChar` of its parameters, evaluated at $\iota_v(x)$. -/
theorem IsArchimedeanParameter.eq_archChar (h : χ.IsArchimedeanParameter v n t)
    (x : v.Completionˣ) :
    (χ.infiniteComponent v x : ℂ) =
      Tate.archChar v.mult n t (InfinitePlace.Completion.extensionEmbedding v x) :=
  h.eq x

/-- The local component of $\chi^{-1}$ is the inverse of the local component of $\chi$. -/
theorem infiniteComponent_inv (χ : HeckeCharacter K) (v : InfinitePlace K) (x : v.Completionˣ) :
    (χ⁻¹.infiniteComponent v x : ℂ) = (χ.infiniteComponent v x : ℂ)⁻¹ := by
  simp only [HeckeCharacter.infiniteComponent, MonoidHom.comp_apply]
  exact Units.val_inv_eq_inv_val _

omit [NumberField K] in
/-- The embedding $\iota_v$ of the completion maps units to nonzero numbers. -/
theorem extensionEmbedding_units_ne_zero (x : v.Completionˣ) :
    InfinitePlace.Completion.extensionEmbedding v x ≠ 0 :=
  (x.isUnit.map _).ne_zero

end HeckeCharacter

namespace Tate

/-- The quasi-character with parameters $(-n, -t)$ is the inverse of the quasi-character with parameters $(n, t)$ on $\mathbb{C}^\times$. -/
theorem archChar_neg_mul_archChar (m : ℕ) (n : ℤ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    archChar m (-n) (-t) z * archChar m n t z = 1 := by
  have h2 : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have h1 : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz h2
  simp only [archChar]
  rw [zpow_neg, mul_mul_mul_comm, inv_mul_cancel₀ (zpow_ne_zero n h1), ← cpow_add _ _ h2]
  simp

/-- The quasi-character with parameters $(-n, -t)$ is the inverse of the quasi-character with parameters $(n, t)$. -/
theorem archChar_neg (m : ℕ) (n : ℤ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    archChar m (-n) (-t) z = (archChar m n t z)⁻¹ :=
  eq_inv_of_mul_eq_one_left (archChar_neg_mul_archChar m n t hz)

/-- On real numbers the sign character is its own inverse: $\mathrm{sgn}(x)^{-n} = \mathrm{sgn}(x)^n$. -/
theorem archChar_neg_ofReal (m : ℕ) (n : ℤ) (t : ℂ) (r : ℝ) :
    archChar m (-n) t r = archChar m n t r := by
  have h : ((r : ℂ) / (‖(r : ℂ)‖ : ℂ))⁻¹ = (r : ℂ) / (‖(r : ℂ)‖ : ℂ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, inv_div]
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg hr, ofReal_neg, div_neg, neg_div]
  simp only [archChar]
  rw [zpow_neg, ← inv_zpow, h]

end Tate

namespace HeckeCharacter

variable {χ : HeckeCharacter K} {v : InfinitePlace K} {n : ℤ} {t : ℂ}

/-- The parameters of $\chi^{-1}$: if $\chi$ has the parameters $(n, t)$ at $v$, then $\chi^{-1}$ has the parameters $(n, -t)$ at a real place and $(-n, -t)$ at a complex place. -/
theorem IsArchimedeanParameter.inv (h : χ.IsArchimedeanParameter v n t) :
    χ⁻¹.IsArchimedeanParameter v (if v.IsReal then n else -n) (-t) where
  isReal hv := by
    rw [ite_eq_left hv]
    exact h.isReal hv
  eq x := by
    change _ = Tate.archChar v.mult _ _ _
    rw [infiniteComponent_inv, h.eq_archChar,
      ← Tate.archChar_neg _ _ _ (extensionEmbedding_units_ne_zero x)]
    split_ifs with hv
    · rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Tate.archChar_neg_ofReal]
    · rfl

end HeckeCharacter

namespace Tate

/-! ### The Gamma factor -/

/-- The local Gamma factor at an infinite place $v$: $\Gamma_\mathbb{R}(s + t + n)$ at a real place and $\Gamma_\mathbb{C}(s + t + |n| / 2)$ at a complex place. -/
noncomputable def archGamma (v : InfinitePlace K) (n : ℤ) (t s : ℂ) : ℂ :=
  if v.IsReal then Gammaℝ (s + t + n) else Gammaℂ (s + t + ((|n| : ℤ) : ℂ) / 2)

/-- The Gamma factor $L_\infty$ is the product of the local Gamma factors. -/
theorem gammaFactor_eq_prod (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) (s : ℂ) :
    gammaFactor K n t s = ∏ v, archGamma v (n v) (t v) s := by
  rw [gammaFactor]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [archGamma]

/-- The real part of $|n| / 2$ is not negative. -/
theorem re_abs_div_two_nonneg (n : ℤ) : 0 ≤ (((|n| : ℤ) : ℂ) / 2).re := by
  rw [← Int.natCast_natAbs, Int.cast_natCast]
  have h : (((n.natAbs : ℕ) : ℂ) / 2).re = (n.natAbs : ℝ) / 2 := by simp
  rw [h]
  positivity

omit [NumberField K] in
/-- The inverse of a local Gamma factor is entire. -/
theorem differentiable_archGamma_inv (v : InfinitePlace K) (n : ℤ) (t : ℂ) :
    Differentiable ℂ (fun s => (archGamma v n t s)⁻¹) := by
  by_cases hv : v.IsReal
  · simp only [archGamma, hv, ↓reduceIte]
    exact differentiable_Gammaℝ_inv.comp (by fun_prop)
  · simp only [archGamma, hv, ↓reduceIte]
    exact differentiable_Gammaℂ_inv.comp (by fun_prop)

omit [NumberField K] in
/-- The local Gamma factor does not vanish for $\mathrm{Re}(s + t) > 0$, if $n \geq 0$ at a real place. -/
theorem archGamma_ne_zero {v : InfinitePlace K} {n : ℤ} {t s : ℂ} (hn : v.IsReal → 0 ≤ n)
    (hs : 0 < (s + t).re) : archGamma v n t s ≠ 0 := by
  rw [archGamma]
  split_ifs with hv
  · apply Gammaℝ_ne_zero_of_re_pos
    have := hn hv
    simp only [add_re, intCast_re] at hs ⊢
    have : (0 : ℝ) ≤ n := by exact_mod_cast this
    linarith
  · apply Gammaℂ_ne_zero_of_re_pos
    rw [add_re]
    linarith [re_abs_div_two_nonneg n]

/-- The inverse of the Gamma factor $L_\infty$ is entire. -/
theorem differentiable_gammaFactor_inv (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) :
    Differentiable ℂ (fun s => (gammaFactor K n t s)⁻¹) := by
  simp only [gammaFactor_eq_prod, ← Finset.prod_inv_distrib]
  exact Differentiable.fun_finsetProd fun v _ => differentiable_archGamma_inv v (n v) (t v)

/-- The Gamma factor $L_\infty$ is meromorphic on $\mathbb{C}$. -/
theorem meromorphicOn_gammaFactor (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ)
    (U : Set ℂ) : MeromorphicOn (gammaFactor K n t) U :=
  meromorphicOn_of_differentiable_inv (differentiable_gammaFactor_inv n t) U

/-- The Gamma factor $L_\infty$ is analytic at each point where it does not vanish. -/
theorem analyticAt_gammaFactor {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ} {s : ℂ}
    (hs : gammaFactor K n t s ≠ 0) : AnalyticAt ℂ (gammaFactor K n t) s :=
  analyticAt_of_differentiable_inv (differentiable_gammaFactor_inv n t) hs

/-- The Gamma factor $L_\infty$ does not vanish when $\mathrm{Re}(s + t_v) > 0$ for all $v$, if $n_v \geq 0$ at the real places. -/
theorem gammaFactor_ne_zero {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ} {s : ℂ}
    (hn : ∀ v : InfinitePlace K, v.IsReal → 0 ≤ n v) (hs : ∀ v, 0 < (s + t v).re) :
    gammaFactor K n t s ≠ 0 := by
  rw [gammaFactor_eq_prod, Finset.prod_ne_zero_iff]
  exact fun v _ => archGamma_ne_zero (hn v) (hs v)

/-! ### Local zeta integrals at the infinite places -/

/-- The zeta integral $Z(f_v, \chi_v, s)$ of the standard test function at an infinite place $v$, for the parameters $(n, t)$. -/
noncomputable def archZeta (v : InfinitePlace K) (n : ℤ) (t s : ℂ) : ℂ :=
  if v.IsReal then realZeta (realTest n) n t s else complexZeta (complexTest n) n t s

/-- The zeta integral $Z(\hat f_v, \chi_v^{-1}, 1 - s)$ of the Fourier transform of the standard test function at an infinite place $v$, for the parameters $(n, t)$ of $\chi_v$. -/
noncomputable def archDualZeta (v : InfinitePlace K) (n : ℤ) (t s : ℂ) : ℂ :=
  if v.IsReal then realZeta (realFourier (realTest n)) n (-t) (1 - s)
  else complexZeta (complexFourier (complexTest n)) (-n) (-t) (1 - s)

/-- The local root number at an infinite place: $(-i)^n$ at a real place and $(-i)^{|n|}$ at a complex place. -/
noncomputable def archRootNumber (v : InfinitePlace K) (n : ℤ) : ℂ :=
  if v.IsReal then realRootNumber n else complexRootNumber n

omit [NumberField K] in
/-- The local root number at an infinite place has absolute value one. -/
theorem norm_archRootNumber (v : InfinitePlace K) (n : ℤ) : ‖archRootNumber v n‖ = 1 := by
  rw [archRootNumber]
  split_ifs
  · exact norm_realRootNumber n
  · exact norm_complexRootNumber n

/-- The product of the local root numbers at the infinite places has absolute value one. -/
theorem norm_prod_archRootNumber (n : InfinitePlace K → ℤ) :
    ‖∏ v, archRootNumber v (n v)‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_archRootNumber v (n v)

omit [NumberField K] in
/-- The value of the local zeta integral: $Z_v(s) = \Gamma_\mathbb{R}(s + t + n)$ at a real place and $Z_v(s) = \pi \Gamma_\mathbb{C}(s + t + |n| / 2)$ at a complex place. -/
theorem archZeta_eq {v : InfinitePlace K} {n : ℤ} {t s : ℂ} (hn : v.IsReal → n = 0 ∨ n = 1)
    (hs : 0 < (s + t).re) :
    archZeta v n t s = (if v.IsReal then 1 else (Real.pi : ℂ)) * archGamma v n t s := by
  rw [archZeta, archGamma]
  split_ifs with hv
  · rw [realZeta_realTest (hn hv) hs, one_mul]
  · rw [complexZeta_complexTest n hs]

omit [NumberField K] in
/-- The local functional equation at an infinite place, for $0 < \mathrm{Re}(s + t) < 1$: $\hat Z_v(s) = \varepsilon_v \frac{\Gamma_v(1 - s, \chi_v^{-1})}{\Gamma_v(s, \chi_v)} Z_v(s)$. -/
theorem archDualZeta_eq {v : InfinitePlace K} {n : ℤ} {t s : ℂ} (hn : v.IsReal → n = 0 ∨ n = 1)
    (h0 : 0 < (s + t).re) (h1 : (s + t).re < 1) :
    archDualZeta v n t s = archRootNumber v n *
      (archGamma v (if v.IsReal then n else -n) (-t) (1 - s) / archGamma v n t s) *
        archZeta v n t s := by
  rw [archDualZeta, archRootNumber, archGamma, archGamma, archZeta]
  split_ifs with hv
  · rw [real_local_functional_equation (hn hv) h0 h1, ← sub_eq_add_neg]
  · rw [complex_local_functional_equation n h0 h1, ← sub_eq_add_neg, abs_neg]

omit [NumberField K] in
/-- The value of the dual local zeta integral: $\hat Z_v(s) = \varepsilon_v \Gamma_v(1 - s, \chi_v^{-1})$, up to the factor $\pi$ at a complex place, for $\mathrm{Re}(s + t) < 1$. -/
theorem archDualZeta_eq_gamma {v : InfinitePlace K} {n : ℤ} {t s : ℂ}
    (hn : v.IsReal → n = 0 ∨ n = 1) (h1 : (s + t).re < 1) :
    archDualZeta v n t s = archRootNumber v n * ((if v.IsReal then 1 else (Real.pi : ℂ)) *
      archGamma v (if v.IsReal then n else -n) (-t) (1 - s)) := by
  rw [archDualZeta, archRootNumber, archGamma]
  split_ifs with hv
  · rw [realZeta_realFourier_realTest (hn hv) h1, one_mul, ← sub_eq_add_neg]
  · rw [complexZeta_complexFourier_complexTest n h1, ← sub_eq_add_neg, abs_neg]

/-- The product of the factors $\pi$ at the complex places is $\pi^{r_2}$. -/
theorem prod_pi_complex :
    ∏ v : InfinitePlace K, (if v.IsReal then 1 else (Real.pi : ℂ)) =
      (Real.pi : ℂ) ^ InfinitePlace.nrComplexPlaces K := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    InfinitePlace.nrComplexPlaces, Fintype.card_subtype]
  congr 2
  ext v
  simp [InfinitePlace.not_isReal_iff_isComplex]

/-- The product of the standard local zeta integrals at the infinite places: $\prod_v Z_v(s) = \pi^{r_2} L_\infty(s, \chi)$, for $\mathrm{Re}(s + t_v) > 0$ at every place. -/
theorem prod_archZeta {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ} {s : ℂ}
    (hn : ∀ v : InfinitePlace K, v.IsReal → n v = 0 ∨ n v = 1) (hs : ∀ v, 0 < (s + t v).re) :
    ∏ v, archZeta v (n v) (t v) s =
      (Real.pi : ℂ) ^ InfinitePlace.nrComplexPlaces K * gammaFactor K n t s := by
  rw [Finset.prod_congr rfl fun v _ => archZeta_eq (hn v) (hs v), Finset.prod_mul_distrib,
    prod_pi_complex, gammaFactor_eq_prod]

/-- The product of the dual local zeta integrals at the infinite places: $\prod_v \hat Z_v(s) = W_\infty \pi^{r_2} L_\infty(1 - s, \chi^{-1})$, for $\mathrm{Re}(s + t_v) < 1$ at every place. Here $\chi^{-1}$ has the parameters $(n_v, -t_v)$ at the real places and $(-n_v, -t_v)$ at the complex places. -/
theorem prod_archDualZeta {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ} {s : ℂ}
    (hn : ∀ v : InfinitePlace K, v.IsReal → n v = 0 ∨ n v = 1) (hs : ∀ v, (s + t v).re < 1) :
    ∏ v, archDualZeta v (n v) (t v) s =
      (∏ v, archRootNumber v (n v)) * ((Real.pi : ℂ) ^ InfinitePlace.nrComplexPlaces K *
        gammaFactor K (fun v => if v.IsReal then n v else -n v) (fun v => -t v) (1 - s)) := by
  rw [Finset.prod_congr rfl fun v _ => archDualZeta_eq_gamma (hn v) (hs v),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_pi_complex, gammaFactor_eq_prod]

/-- The product of the local functional equations at the infinite places: for $0 < \mathrm{Re}(s + t_v) < 1$ at every place, $$\prod_v \hat Z_v(s) = W_\infty \frac{L_\infty(1 - s, \chi^{-1})}{L_\infty(s, \chi)} \prod_v Z_v(s),$$ where $W_\infty$ is the product of the local root numbers. -/
theorem prod_archDualZeta_eq {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ} {s : ℂ}
    (hn : ∀ v : InfinitePlace K, v.IsReal → n v = 0 ∨ n v = 1) (h0 : ∀ v, 0 < (s + t v).re)
    (h1 : ∀ v, (s + t v).re < 1) :
    ∏ v, archDualZeta v (n v) (t v) s =
      (∏ v, archRootNumber v (n v)) *
        (gammaFactor K (fun v => if v.IsReal then n v else -n v) (fun v => -t v) (1 - s) /
          gammaFactor K n t s) * ∏ v, archZeta v (n v) (t v) s := by
  have hne : gammaFactor K n t s ≠ 0 := gammaFactor_ne_zero
    (fun v hv => by rcases hn v hv with h | h <;> omega) h0
  rw [prod_archDualZeta hn h1, prod_archZeta hn h0]
  field_simp

end Tate

end Langlands
