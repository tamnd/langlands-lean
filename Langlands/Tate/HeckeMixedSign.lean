/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeMixedSignFE
import Langlands.Tate.HeckeGeneralUnramified

/-!
# Hecke's functional equation for the unramified characters with mixed signs

Let $K$ be a number field of degree $n$ with $r_2$ complex places, and let $\chi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n_w, 0)$ at each infinite place $w$ and $n \neq 0$. The file `Langlands/Tate/HeckeGeneralUnramified.lean` proves the functional equation if $n_w \ge 0$ for all $w$. Here the integers $n_w$ at the complex places can have arbitrary signs.

Let $p$ and $k$ be the weights of $|n|$ and let $\varepsilon_w$ be true if and only if $n_w < 0$. At a complex place the phase of $\chi$ is $(\sigma_w(x) / |\sigma_w(x)|)^{n_w}$. The signed phase is $(\overline{\sigma_w(x)} / |\sigma_w(x)|)^{|n_w|}$ for $n_w \ge 0$ and $(\sigma_w(x) / |\sigma_w(x)|)^{|n_w|}$ for $n_w < 0$. So the product of the two phases is $1$ in both cases, and reciprocity gives $\chi_{\mathrm{id}}((x)) = \chi^{\varepsilon, p, k}_\infty(x)$ for $x \in K^\times$ (`Langlands.Tate.idealChar_toPrincipalIdeal_eq_signInfinityWeight`). The archimedean factor of $(n, 0)$ is the archimedean factor of $(|n|, 0)$, so the Gamma factors of `Langlands/Tate/HeckeGeneralUnramified.lean` apply to $|n|$. The rest of the proof is the proof of `Langlands/Tate/HeckeGeneralUnramified.lean` with the completed partial Hecke sums of `Langlands/Tate/HeckeMixedSignFE.lean`.

The final result is Hecke's functional equation for each Hecke character $\xi$ that is unramified at each finite place, with the archimedean parameters $(n_v, t_v)$, where $t_v = t_0$ for all $v$ and the signs of the $n_w$ are arbitrary. The twist by $\|\cdot\|^{-t_0}$ moves $\xi$ to the case $t = 0$.

## Main definitions

* `Langlands.Tate.absParam`, `Langlands.Tate.paramSign`: the absolute values $|n_w|$ and the signs $\varepsilon_w$ of a family $n$ of parameters.
* `Langlands.Tate.signCompletedPartialHeckeConj`: the conjugate completed partial Hecke sum of the signed weight.
* `Langlands.Tate.signHeckeClassCompleted`, `Langlands.Tate.signHeckeClassCompletedConj`: the completed class sums of $\chi$ and $\chi^{-1}$.
* `Langlands.Tate.signHeckeCompleted`, `Langlands.Tate.signHeckeCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$ as finite sums over the ideal classes.

## Main results

* `Langlands.Tate.infChar_mul_signInfinityWeight`: $\chi_\infty(x) \, \chi^{\varepsilon, p, k}_\infty(x) = 1$ for $x \in K^\times$.
* `Langlands.Tate.signInfinityWeight_unit_eq_one`: the signed infinity type is trivial on the units.
* `Langlands.Tate.gammaFactor_absParam`: the archimedean factors of $(n, 0)$ and $(|n|, 0)$ are equal.
* `Langlands.Tate.signHeckeClassCompleted_eq_conj`: the functional equation of one class sum.
* `Langlands.Tate.entireFunctionalEquation_unramified_sign`: the entire functional equation for $t = 0$ and arbitrary signs.
* `Langlands.Tate.heckeFunctionalEquation_of_unramified_const_shift`: Hecke's functional equation for unramified characters with $t_v = t_0$ for all $v$ and arbitrary signs.

## Open parts

The case of unequal shifts $t_v$ is not done. If $\xi$ is unramified with the parameters $(n_v, t_v)$, then after the twist by $\|\cdot\|^{-t_0}$ the character has the extra archimedean factor $\prod_v |x|_v^{m_v (t_v - t_0)}$ with $\sum_v m_v (t_v - t_0) = 0$. This factor is a character of the unit-norm torus $\{y \in \prod_v \mathbb{R}_{>0} : \prod_v y_v^{m_v} = 1\}$ that is trivial on the image of the units. The proof needs the theta series twisted by this character and a Mellin transform over the torus modulo the units, in place of the unit cube average of `Langlands/Tate/HeckeMellinUnits.lean`. It also needs the Gamma factor $\prod_v \Gamma_{\mathbb{R}}(s + t_v + n_v)$ or $\Gamma_{\mathbb{C}}(s + t_v + |n_v| / 2)$ with different shifts from the Mellin transform at each place. These steps are not formalized.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  IsDedekindDomain
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Conj

variable {K : Type*} [Field K] [NumberField K]
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

variable (K ε p k) in
/-- The conjugate completed partial Hecke sum $\Lambda^*_{\mathfrak{a}}(s) = \overline{\Lambda_{\mathfrak{a}}(\bar{s})}$. -/
noncomputable def signCompletedPartialHeckeConj (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  conj (signCompletedPartialHecke K ε p k a (conj s))

/-- **The conjugate completed partial Hecke sum is entire.** -/
theorem differentiable_signCompletedPartialHeckeConj (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (signCompletedPartialHeckeConj K ε p k a) := fun s => by
  have e := (differentiable_signCompletedPartialHecke (ε := ε) (a := a) hp h (conj s)).conj_conj
  rw [Complex.conj_conj] at e
  exact e

/-- **The conjugate completed partial Hecke sum as a series of the conjugate infinity type.** If $(p, k) \neq 0$, $\chi_\infty$ is trivial on all units and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda^*_{\mathfrak{a}}(s) = \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} w_K \, \Gamma_{p, k}(s') \, \overline{\chi_\infty(\alpha)} \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_signCompletedPartialHeckeConj (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        conj (signInfinityWeight ε p k (orbitRep a I : K)) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (signCompletedPartialHeckeConj K ε p k a s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have e := (hasSum_signCompletedPartialHecke (a := a) h hχ hs').map (starRingEnd ℂ) continuous_conj
  have hc : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hc, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_heckeGamma]

/-- **The functional equation in the variable of the $L$-function.** Under the hypotheses of `Langlands.Tate.signCompletedPartialHecke_sub`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(n s / 2) = \varepsilon_{\mathfrak{a}} \, \lambda^{-n (1 - s) / 2} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(n (1 - s) / 2).$$ -/
theorem signCompletedPartialHecke_one_sub (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, signInfinityWeight ε p k (u : K) = 1) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (s : ℂ) :
    signCompletedPartialHecke K ε p k a ((finrank ℚ K : ℂ) * s / 2) =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (-((finrank ℚ K : ℂ) * (1 - s) / 2)) *
        signCompletedPartialHeckeConj K ε p k (dualUnit K a) ((finrank ℚ K : ℂ) * (1 - s) / 2) := by
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring]
  exact signCompletedPartialHecke_sub hp h hχ _

end Conj

section Character

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (K) in
/-- The absolute values $|n_w|$ of a family $n$ of archimedean parameters. -/
def absParam (n : InfinitePlace K → ℤ) : InfinitePlace K → ℤ :=
  fun w => |n w|

variable (K) in
/-- The signs of a family $n$ of archimedean parameters at the complex places: $\varepsilon_w$ is true if and only if $n_w < 0$. -/
def paramSign (n : InfinitePlace K → ℤ) : {w : InfinitePlace K // IsComplex w} → Bool :=
  fun w => decide (n w.1 < 0)

omit [NumberField K] in
/-- The absolute values $|n_w|$ are not negative. -/
theorem absParam_nonneg (n : InfinitePlace K → ℤ) (w : InfinitePlace K) : 0 ≤ absParam K n w :=
  abs_nonneg _

omit [NumberField K] in
/-- If $n \neq 0$, then $|n| \neq 0$. -/
theorem absParam_ne_zero {n : InfinitePlace K → ℤ} (hne : ∃ w, n w ≠ 0) :
    ∃ w, absParam K n w ≠ 0 := by
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, abs_ne_zero.2 hw⟩

/-- **The infinite type and the signed infinity type.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place, with arbitrary signs of the $n_w$. Then $\chi_\infty(x) \, \chi^{\varepsilon, p, k}_\infty(x) = 1$ for each $x \in K^\times$, where $p$ and $k$ are the weights of $|n|$ and $\varepsilon$ is the sign of $n$. -/
theorem infChar_mul_signInfinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (x : Kˣ) :
    (infChar χ x : ℂ) * signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) (x : K) = 1 := by
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Units.coe_prod, signInfinityWeight,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  have hx : w (x : K) ≠ 0 := (map_ne_zero w).2 x.ne_zero
  have hx' : ((w (x : K) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  rw [(hn w).eq, extensionEmbedding_ideleInf_unitEmbedding, mul_zero, cpow_zero, mul_one,
    norm_embedding_eq]
  unfold signPlacePhase
  split_ifs with hw
  · rcases (hn w).isReal hw with h | h
    · have e : realWeight K (absParam K n) ⟨w, hw⟩ = 0 := by
        simp only [realWeight, absParam, h, abs_zero, Int.toNat_zero]
      rw [h, e, zpow_zero, pow_zero, one_mul]
    · have e : realWeight K (absParam K n) ⟨w, hw⟩ = 1 := by
        simp only [realWeight, absParam, h, abs_one, Int.toNat_one]
      rw [h, e, zpow_one, pow_one, ← embedding_of_isReal_apply hw]
      have h2 : (embedding_of_isReal hw (x : K)) ^ 2 = w (x : K) ^ 2 := by
        rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, sq_abs]
      have h2' : ((embedding_of_isReal hw (x : K) : ℝ) : ℂ) ^ 2 = ((w (x : K) : ℝ) : ℂ) ^ 2 := by
        exact_mod_cast h2
      rw [Complex.ofReal_div, div_mul_div_comm, ← sq, ← sq, h2', div_self (pow_ne_zero _ hx')]
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 hw
    have hs : signEmbedding (paramSign K n) w (x : K) =
        flipConj (paramSign K n ⟨w, hc⟩) (w.embedding (x : K)) :=
      signEmbedding_apply (paramSign K n) ⟨w, hc⟩ (x : K)
    have hk : ((complexWeight K (absParam K n) ⟨w, hc⟩ : ℕ) : ℤ) = |n w| :=
      Int.toNat_of_nonneg (abs_nonneg (n w))
    have huv : (w.embedding (x : K) / ((w (x : K) : ℝ) : ℂ)) *
        (conj (w.embedding (x : K)) / ((w (x : K) : ℝ) : ℂ)) = 1 := by
      rw [div_mul_div_comm, Complex.mul_conj', norm_embedding_eq, ← sq,
        div_self (pow_ne_zero _ hx')]
    rw [hs]
    generalize complexWeight K (absParam K n) ⟨w, hc⟩ = m at hk
    by_cases hneg : n w < 0
    · have e : paramSign K n ⟨w, hc⟩ = true := decide_eq_true hneg
      have hm : n w = -(m : ℤ) := by rw [hk, abs_of_neg hneg, neg_neg]
      rw [e, flipConj_true, Complex.conj_conj, hm, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ (left_ne_zero_of_mul_eq_one huv))]
    · have e : paramSign K n ⟨w, hc⟩ = false := decide_eq_false hneg
      have hm : n w = (m : ℤ) := by rw [hk, abs_of_nonneg (not_lt.1 hneg)]
      rw [e, flipConj_false, hm, zpow_natCast, ← mul_pow, huv, one_pow]

/-- **The ideal character on principal ideals.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place and arbitrary signs of the $n_w$. Then $\chi_{\mathrm{id}}((x)) = \chi^{\varepsilon, p, k}_\infty(x)$ for each $x \in K^\times$, where $p$ and $k$ are the weights of $|n|$ and $\varepsilon$ is the sign of $n$. -/
theorem idealChar_toPrincipalIdeal_eq_signInfinityWeight (h0 : ramifiedSet χ = ∅)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (x : Kˣ) :
    (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) =
      signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
        (complexWeight K (absParam K n)) (x : K) := by
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) x (by simp [h0])
  rw [h0, Finset.prod_empty, mul_one, periodicChar_apply] at e
  have e' := congrArg (fun z : ℂˣ => (z : ℂ)) e
  simp only [Units.val_mul, Units.val_one] at e'
  calc (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) =
        (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) * ((infChar χ x : ℂ) *
          signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
            (complexWeight K (absParam K n)) (x : K)) := by
        rw [infChar_mul_signInfinityWeight hn, mul_one]
    _ = _ := by rw [← mul_assoc, e', one_mul]

/-- **The signed infinity type is trivial on the units.** Under the hypotheses of `Langlands.Tate.idealChar_toPrincipalIdeal_eq_signInfinityWeight`, $\chi^{\varepsilon, p, k}_\infty(u) = 1$ for each unit $u$ of $\mathcal{O}_K$. -/
theorem signInfinityWeight_unit_eq_one (h0 : ramifiedSet χ = ∅)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (u : (𝓞 K)ˣ) :
    signInfinityWeight (paramSign K n) (realWeight K (absParam K n))
      (complexWeight K (absParam K n)) (u : K) = 1 := by
  have e := idealChar_toPrincipalIdeal_eq_signInfinityWeight h0 hn
    (Units.map (algebraMap (𝓞 K) K) u)
  have h1 : toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) = 1 := by
    rw [toPrincipalIdeal_eq_iff, Units.coe_map, Units.val_one]
    change FractionalIdeal.spanSingleton _ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit,
      FractionalIdeal.coeIdeal_top]
  rw [h1, map_one, Units.val_one] at e
  exact e.symm

/-- The weight at the real places of $|n|$ is at most $1$ for a family $n$ of parameters. -/
theorem realWeight_absParam_le_one {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w)) (v : {w : InfinitePlace K // IsReal w}) :
    realWeight K (absParam K n) v ≤ 1 := by
  rcases (hn v.1).isReal v.2 with h | h <;> simp [realWeight, absParam, h]

/-- The archimedean factor of the parameters $(n_w, 0)$ does not change if $n$ is replaced by $|n|$. -/
theorem gammaFactor_absParam {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w)) (s : ℂ) :
    gammaFactor K (absParam K n) 0 s = gammaFactor K n 0 s := by
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : IsReal w
  · have e : absParam K n w = n w := by
      rcases (hn w).isReal hw with h | h <;> simp [absParam, h]
    simp only [hw, ite_true, e]
  · simp only [hw, ite_false, absParam, abs_abs]

end Character

section Classes

variable {K : Type*} [Field K] [NumberField K]

variable {χ : HeckeCharacter K}

variable (χ) in
/-- The completed class sum $\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{a})^{-1} N(\mathfrak{a})^s \Lambda_{\mathfrak{a}}(n s / 2)$ of the weight $(p, k)$ of $n$. -/
noncomputable def signHeckeClassCompleted (n : InfinitePlace K → ℤ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (s : ℂ) : ℂ :=
  (idealChar χ a : ℂ)⁻¹ * ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    signCompletedPartialHecke K (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) a ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1}) = \chi^{-1}_{\mathrm{id}}(\mathfrak{b})^{-1} N(\mathfrak{b})^s \Lambda^*_{\mathfrak{b}}(n s / 2)$ of the weight $(p, k)$ of $n$. -/
noncomputable def signHeckeClassCompletedConj (n : InfinitePlace K → ℤ)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (idealChar χ⁻¹ b : ℂ)⁻¹ * ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    signCompletedPartialHeckeConj K (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) b ((finrank ℚ K : ℂ) * s / 2)

/-- **The class sum as a Dirichlet series.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, arbitrary signs of the $n_w$ and $n \neq 0$, and let $\mathrm{Re}\, s > 1$. Then $\Lambda_{\mathfrak{a}}(s, \chi)$ is the sum over the integral ideals $I$ in the class $[\mathfrak{a}]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_signHeckeClassCompleted (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hne : ∃ w, n w ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then
        (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
          rayWeight χ s I else 0)
      (signHeckeClassCompleted χ n a s) := by
  have h := hasSum_signCompletedPartialHecke (a := a) (weight_ne_zero (absParam_nonneg n) (absParam_ne_zero hne))
    (signInfinityWeight_unit_eq_one h0 hn) (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [signHeckeClassCompleted]
  exact hasSum_rayWeight_class h0
    (fun x => (idealChar_toPrincipalIdeal_eq_signInfinityWeight h0 hn x).symm) a h

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_signHeckeClassCompleted`, $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[\mathfrak{b}]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi^{-1}_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_signHeckeClassCompletedConj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hne : ∃ w, n w ≠ 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K b)⁻¹ then
        (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
          rayWeight χ⁻¹ s I else 0)
      (signHeckeClassCompletedConj χ n b s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_signCompletedPartialHeckeConj (weight_ne_zero (absParam_nonneg n) (absParam_ne_zero hne))
    (signInfinityWeight_unit_eq_one h0 hn) b (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [signHeckeClassCompletedConj]
  refine hasSum_rayWeight_class (ψ := χ⁻¹)
    (f := fun x => conj (signInfinityWeight (paramSign K n) (realWeight K (absParam K n)) (complexWeight K (absParam K n)) x))
    (by rw [ramifiedSet_inv, h0]) (fun x => ?_) b h
  rw [← idealChar_toPrincipalIdeal_eq_signInfinityWeight h0 hn x, idealChar_inv,
    Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_idealChar_of_unitary hu _)]

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The $L$-function as a sum over the ideal classes.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, arbitrary signs of the $n_w$ and $n \neq 0$. For $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi),$$ where $\mathfrak{a}_C$ is the chosen fractional ideal of the class $C$. -/
theorem signHeckeGamma_mul_finiteLFunction (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hne : ∃ w, n w ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
        χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), signHeckeClassCompleted χ n (classRepUnit K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_signHeckeClassCompleted h0 hn hne (classRepUnit K C) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (classRepUnit K C))⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_classRepUnit]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.signHeckeGamma_mul_finiteLFunction`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1}).$$ -/
theorem signHeckeGamma_mul_finiteLFunction_inv (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hne : ∃ w, n w ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K (absParam K n)) (complexWeight K (absParam K n)) s *
        χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), signHeckeClassCompletedConj χ n (dualUnit K (classRepUnit K C)) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_signHeckeClassCompletedConj h0 hn hne (dualUnit K (classRepUnit K C)) hs)
  rw [finiteLFunction_eq_of_unitary hu hs, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk K (dualUnit K (classRepUnit K C)))⁻¹) ↔
        ((dualClass K).symm (ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk_dualUnit_classRepUnit, Equiv.symm_apply_eq]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end LFunction

section Gamma

variable {K : Type*} [Field K] [NumberField K]

end Gamma

section ClassFE

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The functional equation of one class sum.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, arbitrary signs of the $n_w$ and $n \neq 0$. Then for all complex $s$, $$\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_v p_v + \sum_w k_w} \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, |d_K|^{1/2 - s} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(1 - s, \chi^{-1}).$$ -/
theorem signHeckeClassCompleted_eq_conj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hne : ∃ w, n w ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    signHeckeClassCompleted χ n a s = (idealChar χ (differentUnit K) : ℂ) *
      (-I) ^ (∑ v, realWeight K (absParam K n) v + ∑ w, complexWeight K (absParam K n) w) *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (1 / 2 - s) *
      signHeckeClassCompletedConj χ n (dualUnit K a) (1 - s) := by
  have hc : (idealChar χ (dualUnit K a) : ℂ) =
      ((idealChar χ a : ℂ) * idealChar χ (differentUnit K))⁻¹ := by
    rw [dualUnit_eq, map_inv, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
  unfold signHeckeClassCompleted signHeckeClassCompletedConj
  rw [signCompletedPartialHecke_one_sub (realWeight_absParam_le_one hn) (weight_ne_zero (absParam_nonneg n) (absParam_ne_zero hne))
    (signInfinityWeight_unit_eq_one h0 hn) a s, heckeScale_cpow, heckeRootConst,
    absNorm_dualUnit, idealChar_inv, Units.val_inv_eq_inv_val, inv_inv, hc]
  set A : ℝ := (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  set D : ℝ := |(discr K : ℝ)|
  have hA : 0 < A := absNorm_pos K a
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hA0 : (A : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  have hD0 : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD.ne'
  have hB : (((A * D)⁻¹ : ℝ) : ℂ) ^ (1 - s) = ((A : ℂ) / A ^ s * ((D : ℂ) / D ^ s))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_ne_zero.symm), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hA.le hD.le, cpow_sub _ _ hA0, cpow_sub _ _ hD0, cpow_one,
      cpow_one]
  have hsq : ((√D : ℝ) : ℂ) = (D : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hD.le]
    push_cast
    rfl
  have hsq2 : (D : ℂ) ^ (1 / 2 : ℂ) * (D : ℂ) ^ (1 / 2 : ℂ) = D := by
    rw [← cpow_add _ _ hD0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, cpow_one]
  have hX : (D : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hAs : (A : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hA0)
  have hDs : (D : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hD0)
  have hχa : (idealChar χ a : ℂ) ≠ 0 := Units.ne_zero _
  have hχd : (idealChar χ (differentUnit K) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hB, cpow_sub _ _ hD0, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_mul, hsq,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [inv_pow]
  field_simp
  rw [sq, hsq2]
  ring

end ClassFE
section Entire

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, 0)$, with $A$ = `Langlands.Tate.archRatio`. -/
noncomputable def signHeckeCompleted (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s *
    ∑ C : ClassGroup (𝓞 K), signHeckeClassCompleted χ n (classRepUnit K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1})$ of the parameters $(n_w, 0)$. -/
noncomputable def signHeckeCompletedConj (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K (absParam K n) s *
    ∑ C : ClassGroup (𝓞 K), signHeckeClassCompletedConj χ n (dualUnit K (classRepUnit K C)) s

/-- **The completed $L$-functions are entire.** -/
theorem differentiable_signHeckeCompleted {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w))
    (hne : ∃ w, n w ≠ 0) :
    Differentiable ℂ (signHeckeCompleted χ n) ∧ Differentiable ℂ (signHeckeCompletedConj χ n) := by
  have hp := realWeight_absParam_le_one hn
  have hw := weight_ne_zero (absParam_nonneg n) (absParam_ne_zero hne)
  have hb : ∀ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Differentiable ℂ fun s : ℂ =>
        ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := fun b =>
    differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 (absNorm_pos K b).ne'))
  have hm : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2 :=
    (differentiable_id.const_mul _).div_const 2
  refine ⟨((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (Differentiable.fun_sum fun C _ => ?_),
    ((differentiable_const _).mul (differentiable_archRatio (absParam K n))).mul
      (Differentiable.fun_sum fun C _ => ?_)⟩
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_signCompletedPartialHecke hp hw).comp hm)
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_signCompletedPartialHeckeConj hp hw _).comp hm)

/-- **The entire functional equation for unramified characters with mixed signs.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, arbitrary signs of the $n_w$ and $n \neq 0$, and let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w |n_w|}$. -/
theorem entireFunctionalEquation_unramified_sign (h0 : ramifiedSet χ = ∅)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = 0) (hne : ∃ w, n w ≠ 0) :
    EntireFunctionalEquation χ n n' t t' := by
  have ht0 : t = 0 := funext ht
  subst ht0
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := hn
  have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w = 0 := fun w => by
    have e := isArchimedeanParameter_unique (hn' w) (hp0 w).inv
    rwa [neg_zero] at e
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hp0)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hc : Ideal.absNorm χ.conductor = 1 := by
    rw [conductor_eq_prod, h0, Finset.prod_empty, Ideal.one_eq_top, Ideal.absNorm_top]
  obtain ⟨hd, hd'⟩ := differentiable_signHeckeCompleted hn hne
  refine ⟨signHeckeCompleted χ n, signHeckeCompletedConj χ n, (idealChar χ (differentUnit K) : ℂ) *
    (-I) ^ (∑ v, realWeight K (absParam K n) v + ∑ w, complexWeight K (absParam K n) w), hd, hd', fun s hs => ?_,
    fun s hs => ?_, ?_, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, ← gammaFactor_absParam hp0, gammaFactor_eq_archRatio_mul (absParam_nonneg n), signHeckeCompleted,
      ← signHeckeGamma_mul_finiteLFunction h0 hp0 hne hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_eq_of_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      ← gammaFactor_absParam hp0, gammaFactor_eq_archRatio_mul (absParam_nonneg n), signHeckeCompletedConj,
      ← signHeckeGamma_mul_finiteLFunction_inv h0 hp0 hne hs]
    field_simp
  · rw [norm_mul, norm_idealChar_of_unitary hu, norm_pow, norm_neg, Complex.norm_I, one_pow,
      mul_one]
  · have hD : (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) =
        ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [hc, Nat.cast_one, mul_one, ← Complex.ofReal_intCast, Int.cast_abs]
    rw [hD, signHeckeCompletedConj, ← archRatio_mul (absParam K n) s, signHeckeCompleted]
    simp_rw [signHeckeClassCompleted_eq_conj h0 hp0 hne]
    rw [← Finset.mul_sum]
    ring

end Entire

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the unramified characters with one shift.** Let $\xi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n, t)$, where $t_v = t_0$ for all $v$. The integers $n_w$ at the complex places can have arbitrary signs. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. For $n \neq 0$ the function $\Lambda$ is entire and the root number is $\chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w |n_w|}$ for the unitary twist $\chi$ of $\xi$. For $n = 0$ this is `Langlands.Tate.heckeFunctionalEquation_of_unramified`. -/
theorem heckeFunctionalEquation_of_unramified_const_shift (ξ : HeckeCharacter K)
    (hu : ∀ v, ξ.IsUnramifiedAt v) (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) (t₀ : ℂ) (ht : ∀ v, t v = t₀) :
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
  by_cases hne : ∃ w, n w ≠ 0
  swap
  · push Not at hne
    refine heckeFunctionalEquation_of_unramified ξ t₀ hu (fun w y => ?_) n n' t t' hn hn'
    rw [(hn w).eq y, hne w, zpow_zero, one_mul, ht w]
  obtain ⟨χ, hξ⟩ : ∃ χ : HeckeCharacter K, ∀ x : IdeleGroup (𝓞 K) K,
      (ξ x : ℂ) = (χ x : ℂ) * (ideleNorm K x : ℂ) ^ t₀ :=
    ⟨ξ * normPowerChar K (-t₀), fun x => by
      rw [mul_normPowerChar_apply, mul_assoc,
        ← cpow_add _ _ (ofReal_ne_zero.2 (ideleNorm_pos x).ne'), neg_add_cancel, cpow_zero,
        mul_one]⟩
  have hξ' := inv_of_twist hξ
  have hp : ∀ v, χ.IsArchimedeanParameter v (n v) (t v - t₀) := fun v =>
    isArchimedeanParameter_of_twist hξ (hn v)
  have hp' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v + t₀) := fun v => by
    have h := isArchimedeanParameter_of_twist hξ' (hn' v)
    rwa [sub_neg_eq_add] at h
  have ht0 : ∀ v, t v - t₀ = 0 := fun v => by rw [ht v, sub_self]
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := fun w => by
    rw [← ht0 w]
    exact hp w
  have hχu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hp0)
  have h0χ : ramifiedSet χ = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun v hv =>
    mem_ramifiedSet.1 hv ((isUnramifiedAt_twist_iff hξ v).1 (hu v))
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) :=
    entireFunctionalEquation_unramified_sign h0χ hp hp' ht0 hne
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

end Assembly

end Langlands.Tate
