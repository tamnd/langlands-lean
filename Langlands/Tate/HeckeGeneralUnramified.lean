/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeDualSum
import Langlands.Tate.DedekindFE
import Langlands.Tate.HeckeWeightFE
import Langlands.Tate.HeckeClassTwist

/-!
# Hecke's functional equation for unramified characters of a general number field

Let $K$ be a number field of degree $n$ with $r_2$ complex places, let $\mathfrak{d}$ be the different, and let $\chi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n_w, 0)$ at each infinite place $w$. Suppose that $n_w \ge 0$ for all $w$ and $n \neq 0$. Let $(p, k)$ be the weight with $p_v = n_v$ at the real places and $k_w = n_w$ at the complex places. This file assembles the completed partial Hecke sums of `Langlands/Tate/HeckeDualSum.lean` into the completed Hecke $L$-function of $\chi$ and proves its functional equation.

First, the dual side of `Langlands.Tate.completedPartialHecke_sub` is the conjugate completed partial sum $\Lambda^*_{\mathfrak{b}}(s) = \overline{\Lambda_{\mathfrak{b}}(\bar{s})}$. It is entire, and for $\mathrm{Re}\, s > n / 2$ it is the partial sum of the conjugate infinity type $\overline{\chi^{p, k}_\infty}$ with the same Gamma factor $\Gamma_{p, k}$, since $\overline{\Gamma_{p, k}(\bar{s})} = \Gamma_{p, k}(s)$.

Second, reciprocity gives $\chi_{\mathrm{id}}((x)) = \chi^{p, k}_\infty(x)$ for $x \in K^\times$. So $\chi^{p, k}_\infty$ is trivial on the units, and $\overline{\chi^{p, k}_\infty(x)} = \chi^{-1}_{\mathrm{id}}((x))$. With $\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{a})^{-1} N(\mathfrak{a})^s \Lambda_{\mathfrak{a}}(n s / 2)$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi), \qquad w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1})$$ for $\mathrm{Re}\, s > 1$, where $\mathfrak{a}_C$ is the chosen fractional ideal of the class $C$.

Third, $L_\infty(s) = A(s) \Gamma_{p, k}(s)$ with $A(s) = \prod_{w \text{ complex}} 2^{1 - s - n_w / 2}$, and $A(s) \, 2^{r_2} \lambda^{-n (1 - s) / 2} = A(1 - s)$ with $\lambda = 2^{4 r_2 / n}$. With these steps, $\Lambda(s, \chi) = W |d_K|^{1/2 - s} \Lambda(1 - s, \chi^{-1})$ with $W = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w n_w}$.

## Main definitions

* `Langlands.Tate.completedPartialHeckeConj`: the conjugate completed partial Hecke sum $\Lambda^*_{\mathfrak{b}}$.
* `Langlands.Tate.realWeight`, `Langlands.Tate.complexWeight`: the weight $(p, k)$ of a family $n$ of parameters.
* `Langlands.Tate.heckeClassCompleted`, `Langlands.Tate.heckeClassCompletedConj`: the completed class sums $\Lambda_{\mathfrak{a}}(s, \chi)$ and $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1})$.
* `Langlands.Tate.archRatio`: the ratio $A(s)$ of the two Gamma factors.
* `Langlands.Tate.heckeCompleted`, `Langlands.Tate.heckeCompletedConj`: the completed $L$-functions of $\chi$ and $\chi^{-1}$ as finite sums over the ideal classes.

## Main results

* `Langlands.Tate.hasSum_completedPartialHeckeConj`, `Langlands.Tate.completedPartialHecke_one_sub`: the dual side as the partial sum of the conjugate infinity type.
* `Langlands.Tate.idealChar_toPrincipalIdeal_eq_infinityWeight`, `Langlands.Tate.infinityWeight_unit_eq_one`: the link between $\chi$ and the weight $(p, k)$.
* `Langlands.Tate.heckeGamma_mul_finiteLFunction`, `Langlands.Tate.heckeGamma_mul_finiteLFunction_inv`: the $L$-functions of $\chi$ and $\chi^{-1}$ as sums over the ideal classes.
* `Langlands.Tate.gammaFactor_eq_archRatio_mul`, `Langlands.Tate.archRatio_mul`: the comparison of the Gamma factors.
* `Langlands.Tate.heckeClassCompleted_eq_conj`: the functional equation of one class sum.
* `Langlands.Tate.isArchimedeanParameter_unique`: the archimedean parameters are unique.
* `Langlands.Tate.entireFunctionalEquation_unramified`: the entire functional equation for $n_w \ge 0$ and $n \neq 0$.
* `Langlands.Tate.heckeFunctionalEquation_of_unramified_parallel`: the conclusion of `Langlands.HeckeFunctionalEquationAt` for an unramified $\xi$ with $t_v = t_0$ for all $v$ and with the $n_w$ at the complex places all of one sign.
* `Langlands.Tate.heckeFunctionalEquation_of_unramified_of_subsingleton`: the same conclusion for each unramified $\xi$ if $K$ has one infinite place.

## Proof

The twist $\xi = \chi \|\cdot\|^{t_0}$ reduces the general case to $t = 0$ with `Langlands.Tate.heckeFunctionalEquation_of_twist`. If the $n_w$ at the complex places are $\le 0$, then $\chi^{-1}$ has the parameters $(n_v, 0)$ at the real places and $(-n_w, 0)$ at the complex places, and `Langlands.Tate.EntireFunctionalEquation.of_inv` applies. The case $n = 0$ is `Langlands.Tate.heckeFunctionalEquation_of_unramified`. The class sums use `Langlands.Tate.mem_orbits_iff`, `Langlands.Tate.abs_norm_orbitRep` and the bijection `Langlands.Tate.dualClass` of the class group.

## Open parts

The file does not treat a character with different exponents $t_v$ at different infinite places, and it does not treat a character whose $n_w$ at the complex places have mixed signs. In the second case the infinity type is not of the form $\chi^{p, k}_\infty$ of `Langlands/Tate/HeckeMellinUnits.lean`, because that form uses $\overline{\sigma_w(\alpha)}$ at each complex place. The ramified characters are not treated, so `Langlands.HeckeFunctionalEquationAt K` is not proved for a general $K$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 5 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  IsDedekindDomain
open scoped Real Classical nonZeroDivisors

namespace Langlands.Tate

section Conj

variable {K : Type*} [Field K] [NumberField K]
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}

/-- The Gamma factor of a weight is real on the real axis: $\overline{\Gamma_{p, k}(\bar{s})} = \Gamma_{p, k}(s)$. -/
theorem conj_heckeGamma (s : ℂ) : conj (heckeGamma p k (conj s)) = heckeGamma p k s := by
  have he : ∀ w, heckeExp p k (conj s) w = conj (heckeExp p k s w) := fun w => by
    simp [heckeExp, map_div₀, map_ofNat]
  simp only [heckeGamma, map_prod, map_mul, he, ← map_neg, conj_ofReal_cpow Real.pi_pos.le,
    Complex.Gamma_conj, Complex.conj_conj]

variable (K p k) in
/-- The conjugate completed partial Hecke sum $\Lambda^*_{\mathfrak{a}}(s) = \overline{\Lambda_{\mathfrak{a}}(\bar{s})}$. -/
noncomputable def completedPartialHeckeConj (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  conj (completedPartialHecke K p k a (conj s))

/-- **The conjugate completed partial Hecke sum is entire.** -/
theorem differentiable_completedPartialHeckeConj (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (completedPartialHeckeConj K p k a) := fun s => by
  have e := (differentiable_completedPartialHecke (a := a) hp h (conj s)).conj_conj
  rw [Complex.conj_conj] at e
  exact e

/-- **The conjugate completed partial Hecke sum as a series of the conjugate infinity type.** If $(p, k) \neq 0$, $\chi_\infty$ is trivial on all units and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda^*_{\mathfrak{a}}(s) = \sum_{\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times} w_K \, \Gamma_{p, k}(s') \, \overline{\chi_\infty(\alpha)} \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_completedPartialHeckeConj (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (heckeGamma p k (2 * s / finrank ℚ K) *
        conj (infinityWeight p k (orbitRep a I : K)) *
          ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s / finrank ℚ K))))
      (completedPartialHeckeConj K p k a s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have e := (hasSum_completedPartialHecke (a := a) h hχ hs').map (starRingEnd ℂ) continuous_conj
  have hc : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hc, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_heckeGamma]

/-- **The functional equation in the variable of the $L$-function.** Under the hypotheses of `Langlands.Tate.completedPartialHecke_sub`, for all complex $s$, $$\Lambda_{\mathfrak{a}}(n s / 2) = \varepsilon_{\mathfrak{a}} \, \lambda^{-n (1 - s) / 2} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(n (1 - s) / 2).$$ -/
theorem completedPartialHecke_one_sub (hp : ∀ v, p v ≤ 1) (h : p ≠ 0 ∨ k ≠ 0)
    (hχ : ∀ u : (𝓞 K)ˣ, infinityWeight p k (u : K) = 1) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (s : ℂ) :
    completedPartialHecke K p k a ((finrank ℚ K : ℂ) * s / 2) =
      heckeRootConst K p k a * (heckeScale K : ℂ) ^ (-((finrank ℚ K : ℂ) * (1 - s) / 2)) *
        completedPartialHeckeConj K p k (dualUnit K a) ((finrank ℚ K : ℂ) * (1 - s) / 2) := by
  rw [show (finrank ℚ K : ℂ) * s / 2 = finrank ℚ K / 2 - (finrank ℚ K : ℂ) * (1 - s) / 2 by ring]
  exact completedPartialHecke_sub hp h hχ _

end Conj

section Character

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (K) in
/-- The weight at the real places of a family $n$ of archimedean parameters: $p_v = n_v$ for $n_v \ge 0$. -/
def realWeight (n : InfinitePlace K → ℤ) : {w : InfinitePlace K // IsReal w} → ℕ :=
  fun v => (n v.1).toNat

variable (K) in
/-- The weight at the complex places of a family $n$ of archimedean parameters: $k_w = n_w$ for $n_w \ge 0$. -/
def complexWeight (n : InfinitePlace K → ℤ) : {w : InfinitePlace K // IsComplex w} → ℕ :=
  fun w => (n w.1).toNat

omit [NumberField K] in
/-- The exponent $q_w$ of the weight of $n$ is $n_w$ for $n_w \ge 0$. -/
theorem weightExp_realWeight (n : InfinitePlace K → ℤ) (w : InfinitePlace K) :
    weightExp (realWeight K n) (complexWeight K n) w = (n w).toNat := by
  unfold weightExp
  split_ifs <;> rfl

/-- **The infinite type and the infinity type of the weight.** Let $\chi$ have the parameters $(n_w, 0)$ at each infinite place, with $n_w \ge 0$. Then $\chi_\infty(x) \, \chi^{p, k}_\infty(x) = 1$ for each $x \in K^\times$, where $(p, k)$ is the weight of $n$. -/
theorem infChar_mul_infinityWeight {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (x : Kˣ) :
    (infChar χ x : ℂ) * infinityWeight (realWeight K n) (complexWeight K n) (x : K) = 1 := by
  rw [infChar_apply, ideleChar_infinitePart_eq_prod, Units.coe_prod, infinityWeight,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  have hx : w (x : K) ≠ 0 := (map_ne_zero w).2 x.ne_zero
  have hx' : ((w (x : K) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  rw [(hn w).eq, extensionEmbedding_ideleInf_unitEmbedding, mul_zero, cpow_zero, mul_one,
    norm_embedding_eq, ← Int.toNat_of_nonneg (hn0 w), zpow_natCast]
  unfold placePhase
  split_ifs with hw
  · change _ * _ ^ (n w).toNat = 1
    rw [← mul_pow, ← embedding_of_isReal_apply hw]
    have h2 : (embedding_of_isReal hw (x : K)) ^ 2 = w (x : K) ^ 2 := by
      rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, sq_abs]
    have h2' : ((embedding_of_isReal hw (x : K) : ℝ) : ℂ) ^ 2 = ((w (x : K) : ℝ) : ℂ) ^ 2 := by
      exact_mod_cast h2
    rw [Complex.ofReal_div, div_mul_div_comm, ← sq, ← sq, h2', div_self (pow_ne_zero _ hx'),
      one_pow]
  · change _ * _ ^ (n w).toNat = 1
    rw [← mul_pow, div_mul_div_comm, Complex.mul_conj', norm_embedding_eq, ← sq,
      div_self (pow_ne_zero _ hx'), one_pow]

/-- **The ideal character on principal ideals.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place and $n_w \ge 0$. Then $\chi_{\mathrm{id}}((x)) = \chi^{p, k}_\infty(x)$ for each $x \in K^\times$, where $(p, k)$ is the weight of $n$. -/
theorem idealChar_toPrincipalIdeal_eq_infinityWeight (h0 : ramifiedSet χ = ∅)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (hn0 : ∀ w, 0 ≤ n w) (x : Kˣ) :
    (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) =
      infinityWeight (realWeight K n) (complexWeight K n) (x : K) := by
  have e := periodicChar_mul_prod_finiteComponent (χ := χ) x (by simp [h0])
  rw [h0, Finset.prod_empty, mul_one, periodicChar_apply] at e
  have e' := congrArg (fun z : ℂˣ => (z : ℂ)) e
  simp only [Units.val_mul, Units.val_one] at e'
  calc (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) =
        (idealChar χ (toPrincipalIdeal (𝓞 K) K x) : ℂ) * ((infChar χ x : ℂ) *
          infinityWeight (realWeight K n) (complexWeight K n) (x : K)) := by
        rw [infChar_mul_infinityWeight hn hn0, mul_one]
    _ = _ := by rw [← mul_assoc, e', one_mul]

/-- **The infinity type is trivial on the units.** Under the hypotheses of `Langlands.Tate.idealChar_toPrincipalIdeal_eq_infinityWeight`, $\chi^{p, k}_\infty(u) = 1$ for each unit $u$ of $\mathcal{O}_K$. -/
theorem infinityWeight_unit_eq_one (h0 : ramifiedSet χ = ∅)
    {n : InfinitePlace K → ℤ} (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0)
    (hn0 : ∀ w, 0 ≤ n w) (u : (𝓞 K)ˣ) :
    infinityWeight (realWeight K n) (complexWeight K n) (u : K) = 1 := by
  have e := idealChar_toPrincipalIdeal_eq_infinityWeight h0 hn hn0
    (Units.map (algebraMap (𝓞 K) K) u)
  have h1 : toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) = 1 := by
    rw [toPrincipalIdeal_eq_iff, Units.coe_map, Units.val_one]
    change FractionalIdeal.spanSingleton _ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit,
      FractionalIdeal.coeIdeal_top]
  rw [h1, map_one, Units.val_one] at e
  exact e.symm

end Character

section Classes

variable {K : Type*} [Field K] [NumberField K]

/-- **From the orbits to the ideals.** Let $\psi$ be unramified at each finite place and let $f(x) = \psi_{\mathrm{id}}((x))$ for $x \in K^\times$. If the series over $\alpha \in (\mathfrak{a} \setminus 0) / \mathcal{O}_K^\times$ of $w_K \, c \, f(\alpha) \, |N(\alpha)|^{-s}$ has the sum $L$, then the series over the integral ideals $I$ in the class $[\mathfrak{a}]^{-1}$ of $w_K \, c \, \psi_{\mathrm{id}}(I) N(I)^{-s}$ has the sum $\psi_{\mathrm{id}}(\mathfrak{a})^{-1} N(\mathfrak{a})^s L$. -/
theorem hasSum_rayWeight_class {ψ : HeckeCharacter K} (h0 : ramifiedSet ψ = ∅) {f : K → ℂ}
    (hf : ∀ x : Kˣ, f x = idealChar ψ (toPrincipalIdeal (𝓞 K) K x))
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c s L : ℂ}
    (h : HasSum (fun I : Orbits a => (torsionOrder K : ℂ) * (c * f (orbitRep a I : K) *
        ((|(Algebra.norm ℚ (orbitRep a I : K) : ℝ)| : ℝ) : ℂ) ^ (-s))) L) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then
        (torsionOrder K : ℂ) * c * rayWeight ψ s I else 0)
      ((idealChar ψ a : ℂ)⁻¹ *
        ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s * L) := by
  set g : (Ideal (𝓞 K))⁰ → ℂ := fun I => (torsionOrder K : ℂ) * c * rayWeight ψ s I with hg
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    absNorm_pos K a
  have hN0 : ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 hN.ne'))
  have h1 : HasSum (g ∘ ((↑) : Orbits a → (Ideal (𝓞 K))⁰)) ((idealChar ψ a : ℂ)⁻¹ *
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s * L) := by
    refine (h.mul_left _).congr_fun fun I => ?_
    have hu : toPrincipalIdeal (𝓞 K) K (Units.mk0 (orbitRep a I : K) (orbitRep a I).2) =
        a * FractionalIdeal.mk0 K (I : (Ideal (𝓞 K))⁰) := by
      refine Units.ext ?_
      rw [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_mk0,
        spanSingleton_eq_mul_idealOf, idealOf_orbitRep]
    have hf' := hf (Units.mk0 (orbitRep a I : K) (orbitRep a I).2)
    rw [Units.val_mk0, hu, map_mul, Units.val_mul] at hf'
    simp only [Function.comp_apply, hg, rayWeight_apply, h0, Finset.notMem_empty,
      IsEmpty.forall_iff, implies_true, ite_true, one_mul, hf', abs_norm_orbitRep,
      Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg hN.le (Nat.cast_nonneg _), Complex.ofReal_natCast,
      cpow_neg _ s, cpow_neg _ s]
    field_simp
  have h2 := (hasSum_subtype_iff_indicator (s := Orbits a)).1 h1
  convert h2 using 1
  funext I
  by_cases hI : I ∈ Orbits a
  · rw [Set.indicator_of_mem hI, ite_eq_left ((mem_orbits_iff a I).1 hI)]
  · rw [Set.indicator_of_notMem hI, ite_eq_right (fun h => hI ((mem_orbits_iff a I).2 h))]

variable {χ : HeckeCharacter K}

variable (χ) in
/-- The completed class sum $\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{a})^{-1} N(\mathfrak{a})^s \Lambda_{\mathfrak{a}}(n s / 2)$ of the weight $(p, k)$ of $n$. -/
noncomputable def heckeClassCompleted (n : InfinitePlace K → ℤ) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (s : ℂ) : ℂ :=
  (idealChar χ a : ℂ)⁻¹ * ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    completedPartialHecke K (realWeight K n) (complexWeight K n) a ((finrank ℚ K : ℂ) * s / 2)

variable (χ) in
/-- The dual completed class sum $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1}) = \chi^{-1}_{\mathrm{id}}(\mathfrak{b})^{-1} N(\mathfrak{b})^s \Lambda^*_{\mathfrak{b}}(n s / 2)$ of the weight $(p, k)$ of $n$. -/
noncomputable def heckeClassCompletedConj (n : InfinitePlace K → ℤ)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (idealChar χ⁻¹ b : ℂ)⁻¹ * ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s *
    completedPartialHeckeConj K (realWeight K n) (complexWeight K n) b ((finrank ℚ K : ℂ) * s / 2)

omit [NumberField K] in
/-- The weight of a family $n \neq 0$ of parameters with $n_w \ge 0$ is not zero. -/
theorem weight_ne_zero {n : InfinitePlace K → ℤ} (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0) :
    realWeight K n ≠ 0 ∨ complexWeight K n ≠ 0 := by
  obtain ⟨w, hw⟩ := hne
  by_cases hr : IsReal w
  · refine Or.inl fun h => hw ?_
    have e := congrFun h ⟨w, hr⟩
    simp only [realWeight, Pi.zero_apply] at e
    have := hn0 w
    omega
  · refine Or.inr fun h => hw ?_
    have e := congrFun h ⟨w, not_isReal_iff_isComplex.1 hr⟩
    simp only [complexWeight, Pi.zero_apply] at e
    have := hn0 w
    omega

/-- The weight at the real places of a family of parameters is at most $1$. -/
theorem realWeight_le_one {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w)) (v : {w : InfinitePlace K // IsReal w}) :
    realWeight K n v ≤ 1 := by
  rcases (hn v.1).isReal v.2 with h | h <;> simp [realWeight, h]

/-- **The class sum as a Dirichlet series.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, $n_w \ge 0$ and $n \neq 0$, and let $\mathrm{Re}\, s > 1$. Then $\Lambda_{\mathfrak{a}}(s, \chi)$ is the sum over the integral ideals $I$ in the class $[\mathfrak{a}]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_heckeClassCompleted (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K a)⁻¹ then
        (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
          rayWeight χ s I else 0)
      (heckeClassCompleted χ n a s) := by
  have h := hasSum_completedPartialHecke (a := a) (weight_ne_zero hn0 hne)
    (infinityWeight_unit_eq_one h0 hn hn0) (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [heckeClassCompleted]
  exact hasSum_rayWeight_class h0
    (fun x => (idealChar_toPrincipalIdeal_eq_infinityWeight h0 hn hn0 x).symm) a h

/-- **The dual class sum as a Dirichlet series.** Under the hypotheses of `Langlands.Tate.hasSum_heckeClassCompleted`, $\Lambda^*_{\mathfrak{b}}(s, \chi^{-1})$ is the sum over the integral ideals $I$ in the class $[\mathfrak{b}]^{-1}$ of $w_K \, \Gamma_{p, k}(s) \, \chi^{-1}_{\mathrm{id}}(I) N(I)^{-s}$. -/
theorem hasSum_heckeClassCompletedConj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => if ClassGroup.mk0 I = (ClassGroup.mk K b)⁻¹ then
        (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
          rayWeight χ⁻¹ s I else 0)
      (heckeClassCompletedConj χ n b s) := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h := hasSum_completedPartialHeckeConj (weight_ne_zero hn0 hne)
    (infinityWeight_unit_eq_one h0 hn hn0) b (lt_re_of_one_lt_re hs)
  rw [two_mul_div_finrank] at h
  rw [heckeClassCompletedConj]
  refine hasSum_rayWeight_class (ψ := χ⁻¹)
    (f := fun x => conj (infinityWeight (realWeight K n) (complexWeight K n) x))
    (by rw [ramifiedSet_inv, h0]) (fun x => ?_) b h
  rw [← idealChar_toPrincipalIdeal_eq_infinityWeight h0 hn hn0 x, idealChar_inv,
    Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_idealChar_of_unitary hu _)]

end Classes

section LFunction

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The $L$-function as a sum over the ideal classes.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, $n_w \ge 0$ and $n \neq 0$. For $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi) = \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi),$$ where $\mathfrak{a}_C$ is the chosen fractional ideal of the class $C$. -/
theorem heckeGamma_mul_finiteLFunction (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
        χ.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), heckeClassCompleted χ n (classRepUnit K C) s := by
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn)
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_heckeClassCompleted h0 hn hn0 hne (classRepUnit K C) hs)
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

/-- **The $L$-function of $\chi^{-1}$ as a sum over the ideal classes.** Under the hypotheses of `Langlands.Tate.heckeGamma_mul_finiteLFunction`, for $\mathrm{Re}\, s > 1$, $$w_K \, \Gamma_{p, k}(s) \, L(s, \chi^{-1}) = \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1}).$$ -/
theorem heckeGamma_mul_finiteLFunction_inv (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K : ℂ) * heckeGamma (realWeight K n) (complexWeight K n) s *
        χ⁻¹.finiteLFunction s =
      ∑ C : ClassGroup (𝓞 K), heckeClassCompletedConj χ n (dualUnit K (classRepUnit K C)) s := by
  have hu := norm_ideleChar_inv (norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hn))
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_heckeClassCompletedConj h0 hn hn0 hne (dualUnit K (classRepUnit K C)) hs)
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

variable (K) in
/-- The ratio of the two Gamma factors: $\prod_{w \text{ complex}} 2^{1 - s - n_w / 2}$. -/
noncomputable def archRatio (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K, if IsReal w then 1 else (2 : ℂ) ^ (1 - (s + (n w : ℂ) / 2))

/-- **The archimedean factor and the Gamma factor of the weight.** If $n_w \ge 0$ for all $w$, then $L_\infty(s) = \prod_{w \text{ complex}} 2^{1 - s - n_w / 2} \cdot \Gamma_{p, k}(s)$ for the parameters $(n_w, 0)$, where $(p, k)$ is the weight of $n$. -/
theorem gammaFactor_eq_archRatio_mul {n : InfinitePlace K → ℤ} (hn0 : ∀ w, 0 ≤ n w) (s : ℂ) :
    gammaFactor K n 0 s =
      archRatio K n s * heckeGamma (realWeight K n) (complexWeight K n) s := by
  rw [gammaFactor, archRatio, heckeGamma, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hq : ((weightExp (realWeight K n) (complexWeight K n) w : ℕ) : ℂ) = (n w : ℂ) := by
    rw [weightExp_realWeight]
    exact_mod_cast Int.toNat_of_nonneg (hn0 w)
  simp only [heckeExp, hq, Pi.zero_apply, add_zero]
  by_cases hw : IsReal w
  · rw [ite_eq_left hw, ite_eq_left hw, mult, ite_eq_left hw, Nat.cast_one, one_mul, one_mul,
      Gammaℝ_def, neg_div]
  · rw [ite_eq_right hw, ite_eq_right hw, mult, ite_eq_right hw, abs_of_nonneg (hn0 w),
      gammaℂ_eq_two_cpow_mul, Gammaℝ_def, show -(2 * (s + (n w : ℂ) / 2)) / 2 = -(((2 : ℕ) : ℂ) * s + n w) / 2 by
        push_cast; ring,
      show 2 * (s + (n w : ℂ) / 2) / 2 = (((2 : ℕ) : ℂ) * s + n w) / 2 by push_cast; ring,
      neg_div]

/-- The archimedean factors of the parameters $(n_w, 0)$ do not change if $n_w$ is replaced by $-n_w$ at the complex places. -/
theorem gammaFactor_eq_of_inv {n n' : InfinitePlace K → ℤ} {t' : InfinitePlace K → ℂ}
    (hn' : ∀ w, n' w = if IsReal w then n w else -n w) (ht' : ∀ w, t' w = 0) (s : ℂ) :
    gammaFactor K n' t' s = gammaFactor K n 0 s := by
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [hn', ht', Pi.zero_apply]
  by_cases hw : IsReal w
  · simp only [hw, ite_true]
  · simp only [hw, ite_false, abs_neg]

/-- **The scale factor.** $\lambda^{-n (1 - s) / 2} = 2^{-2 r_2 (1 - s)}$, with $\lambda = 2^{4 r_2 / n}$. -/
theorem heckeScale_cpow (s : ℂ) :
    (heckeScale K : ℂ) ^ (-((finrank ℚ K : ℂ) * (1 - s) / 2)) =
      (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s))) := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  have him : (Complex.log 2 * (((4 * nrComplexPlaces K : ℝ) / finrank ℚ K : ℝ) : ℂ)).im = 0 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      ← Complex.ofReal_mul, Complex.ofReal_im]
  rw [heckeScale, Complex.ofReal_cpow (by norm_num), Complex.ofReal_ofNat,
    ← cpow_mul _ (by rw [him]; exact neg_lt_zero.2 Real.pi_pos) (by rw [him]; exact Real.pi_pos.le)]
  congr 1
  push_cast
  field_simp
  ring

/-- **The ratio of the Gamma factors at $s$ and $1 - s$.** $A(s) \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} = A(1 - s)$, with $A$ = `Langlands.Tate.archRatio`. -/
theorem archRatio_mul (n : InfinitePlace K → ℤ) (s : ℂ) :
    archRatio K n s * ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) *
      (1 - s)))) = archRatio K n (1 - s) := by
  have h2 : (2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s))) =
      ∏ w : InfinitePlace K, if IsReal w then 1 else (2 : ℂ) ^ (2 * s - 1) := by
    rw [prod_eq_prod_mul_prod]
    have e1 : ∏ w : {w : InfinitePlace K // IsReal w},
        (if IsReal w.1 then (1 : ℂ) else (2 : ℂ) ^ (2 * s - 1)) = 1 :=
      Finset.prod_eq_one fun w _ => ite_eq_left w.2
    have e2 : ∏ w : {w : InfinitePlace K // IsComplex w},
        (if IsReal w.1 then (1 : ℂ) else (2 : ℂ) ^ (2 * s - 1)) =
          ((2 : ℂ) ^ (2 * s - 1)) ^ nrComplexPlaces K := by
      rw [Finset.prod_congr rfl fun w _ => ite_eq_right (not_isReal_iff_isComplex.2 w.2),
        Finset.prod_const, Finset.card_univ]
    rw [e1, e2, one_mul, ← cpow_nat_mul, ← cpow_natCast, ← cpow_add _ _ two_ne_zero]
    congr 1
    ring
  rw [h2, archRatio, archRatio, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : IsReal w
  · simp only [hw, ite_true, mul_one]
  · simp only [hw, ite_false]
    rw [← cpow_add _ _ two_ne_zero]
    congr 1
    ring

end Gamma

section ClassFE

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- **The functional equation of one class sum.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, $n_w \ge 0$ and $n \neq 0$. Then for all complex $s$, $$\Lambda_{\mathfrak{a}}(s, \chi) = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_v p_v + \sum_w k_w} \, 2^{r_2} \, 2^{-2 r_2 (1 - s)} \, |d_K|^{1/2 - s} \, \Lambda^*_{(\mathfrak{a} \mathfrak{d})^{-1}}(1 - s, \chi^{-1}).$$ -/
theorem heckeClassCompleted_eq_conj (h0 : ramifiedSet χ = ∅) {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    heckeClassCompleted χ n a s = (idealChar χ (differentUnit K) : ℂ) *
      (-I) ^ (∑ v, realWeight K n v + ∑ w, complexWeight K n w) *
      ((2 : ℂ) ^ nrComplexPlaces K * (2 : ℂ) ^ (-(2 * (nrComplexPlaces K : ℂ) * (1 - s)))) *
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (1 / 2 - s) *
      heckeClassCompletedConj χ n (dualUnit K a) (1 - s) := by
  have hc : (idealChar χ (dualUnit K a) : ℂ) =
      ((idealChar χ a : ℂ) * idealChar χ (differentUnit K))⁻¹ := by
    rw [dualUnit_eq, map_inv, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
  unfold heckeClassCompleted heckeClassCompletedConj
  rw [completedPartialHecke_one_sub (realWeight_le_one hn) (weight_ne_zero hn0 hne)
    (infinityWeight_unit_eq_one h0 hn hn0) a s, heckeScale_cpow, heckeRootConst,
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

section Parameters

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The archimedean parameters $(n, t)$ and $(m, s)$ of $\chi$ at a place $v$ are equal if $n - m$ is $0$ or $1$ at a real place. -/
theorem isArchimedeanParameter_unique_aux {v : InfinitePlace K} {n m : ℤ} {t s : ℂ}
    (h1 : χ.IsArchimedeanParameter v n t) (h2 : χ.IsArchimedeanParameter v m s)
    (hv : v.IsReal → n - m = 0 ∨ n - m = 1) : n = m ∧ t = s := by
  have h := eq_zero_of_forall_param_eq_one (v := v) (n := n - m) (t := t - s) hv fun x => by
      have hz : InfinitePlace.Completion.extensionEmbedding v x ≠ 0 := (x.isUnit.map _).ne_zero
      have hn : (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ) ≠ 0 :=
        ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
      have hq : InfinitePlace.Completion.extensionEmbedding v x /
          (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ) ≠ 0 := div_ne_zero hz hn
      have e := (h1.eq x).symm.trans (h2.eq x)
      have h0 : (InfinitePlace.Completion.extensionEmbedding v x /
          (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ)) ^ m *
          (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * s) ≠ 0 :=
        mul_ne_zero (zpow_ne_zero _ hq) (cpow_ne_zero_iff.2 (Or.inl hn))
      rw [zpow_sub₀ hq, mul_sub, cpow_sub _ _ hn, div_mul_div_comm, e, div_self h0]
  exact ⟨sub_eq_zero.1 h.1, sub_eq_zero.1 h.2⟩

/-- **The archimedean parameters are unique.** If $\chi$ has the parameters $(n, t)$ and $(m, s)$ at an infinite place, then $n = m$ and $t = s$. -/
theorem isArchimedeanParameter_unique {v : InfinitePlace K} {n m : ℤ} {t s : ℂ}
    (h1 : χ.IsArchimedeanParameter v n t) (h2 : χ.IsArchimedeanParameter v m s) :
    n = m ∧ t = s := by
  by_cases hv : v.IsReal
  · rcases h1.isReal hv with hn | hn <;> rcases h2.isReal hv with hm | hm
    · exact isArchimedeanParameter_unique_aux h1 h2 fun _ => Or.inl (by omega)
    · obtain ⟨e1, e2⟩ := isArchimedeanParameter_unique_aux h2 h1 fun _ => Or.inr (by omega)
      exact ⟨e1.symm, e2.symm⟩
    · exact isArchimedeanParameter_unique_aux h1 h2 fun _ => Or.inr (by omega)
    · exact isArchimedeanParameter_unique_aux h1 h2 fun _ => Or.inl (by omega)
  · exact isArchimedeanParameter_unique_aux h1 h2 fun h => absurd h hv

end Parameters

section Entire

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi) = w_K^{-1} A(s) \sum_C \Lambda_{\mathfrak{a}_C}(s, \chi)$ of the parameters $(n_w, 0)$, with $A$ = `Langlands.Tate.archRatio`. -/
noncomputable def heckeCompleted (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K n s *
    ∑ C : ClassGroup (𝓞 K), heckeClassCompleted χ n (classRepUnit K C) s

variable (χ) in
/-- The completed $L$-function $\Lambda(s, \chi^{-1}) = w_K^{-1} A(s) \sum_C \Lambda^*_{(\mathfrak{a}_C \mathfrak{d})^{-1}}(s, \chi^{-1})$ of the parameters $(n_w, 0)$. -/
noncomputable def heckeCompletedConj (n : InfinitePlace K → ℤ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ * archRatio K n s *
    ∑ C : ClassGroup (𝓞 K), heckeClassCompletedConj χ n (dualUnit K (classRepUnit K C)) s

/-- The ratio $A(s)$ of the Gamma factors is entire. -/
theorem differentiable_archRatio (n : InfinitePlace K → ℤ) : Differentiable ℂ (archRatio K n) := by
  unfold archRatio
  refine Differentiable.fun_finsetProd fun w _ => ?_
  by_cases hw : IsReal w
  · simp only [hw, ite_true]
    exact differentiable_const _
  · simp only [hw, ite_false]
    exact ((differentiable_id.add_const _).const_sub 1).const_cpow (Or.inl two_ne_zero)

/-- **The completed $L$-functions are entire.** -/
theorem differentiable_heckeCompleted {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) (t w)) (hn0 : ∀ w, 0 ≤ n w)
    (hne : ∃ w, n w ≠ 0) :
    Differentiable ℂ (heckeCompleted χ n) ∧ Differentiable ℂ (heckeCompletedConj χ n) := by
  have hp := realWeight_le_one hn
  have hw := weight_ne_zero hn0 hne
  have hb : ∀ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Differentiable ℂ fun s : ℂ =>
        ((FractionalIdeal.absNorm (b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s := fun b =>
    differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 (absNorm_pos K b).ne'))
  have hm : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2 :=
    (differentiable_id.const_mul _).div_const 2
  refine ⟨((differentiable_const _).mul (differentiable_archRatio n)).mul
      (Differentiable.fun_sum fun C _ => ?_),
    ((differentiable_const _).mul (differentiable_archRatio n)).mul
      (Differentiable.fun_sum fun C _ => ?_)⟩
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_completedPartialHecke hp hw).comp hm)
  · exact ((differentiable_const _).mul (hb _)).mul
      ((differentiable_completedPartialHeckeConj hp hw _).comp hm)

/-- **The entire functional equation for unramified characters of nonnegative weight.** Let $\chi$ be unramified at each finite place, with the parameters $(n_w, 0)$ at each infinite place, $n_w \ge 0$ and $n \neq 0$, and let $(n', t')$ be parameters of $\chi^{-1}$. Then `Langlands.Tate.EntireFunctionalEquation` holds for $\chi$, with the root number $W = \chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w n_w}$. -/
theorem entireFunctionalEquation_unramified (h0 : ramifiedSet χ = ∅)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (ht : ∀ v, t v = 0) (hn0 : ∀ w, 0 ≤ n w) (hne : ∃ w, n w ≠ 0) :
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
  obtain ⟨hd, hd'⟩ := differentiable_heckeCompleted hn hn0 hne
  refine ⟨heckeCompleted χ n, heckeCompletedConj χ n, (idealChar χ (differentUnit K) : ℂ) *
    (-I) ^ (∑ v, realWeight K n v + ∑ w, complexWeight K n w), hd, hd', fun s hs => ?_,
    fun s hs => ?_, ?_, fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_eq_archRatio_mul hn0, heckeCompleted,
      ← heckeGamma_mul_finiteLFunction h0 hp0 hn0 hne hs]
    field_simp
  · rw [HeckeCharacter.completedLFunction,
      gammaFactor_eq_of_inv (fun w => (hinv w).1) (fun w => (hinv w).2),
      gammaFactor_eq_archRatio_mul hn0, heckeCompletedConj,
      ← heckeGamma_mul_finiteLFunction_inv h0 hp0 hn0 hne hs]
    field_simp
  · rw [norm_mul, norm_idealChar_of_unitary hu, norm_pow, norm_neg, Complex.norm_I, one_pow,
      mul_one]
  · have hD : (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) =
        ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [hc, Nat.cast_one, mul_one, ← Complex.ofReal_intCast, Int.cast_abs]
    rw [hD, heckeCompletedConj, ← archRatio_mul n s, heckeCompleted]
    simp_rw [heckeClassCompleted_eq_conj h0 hp0 hn0 hne]
    rw [← Finset.mul_sum]
    ring

end Entire

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- **Hecke's functional equation for the unramified characters with parallel weight.** Let $\xi$ be a Hecke character that is unramified at each finite place, with the archimedean parameters $(n, t)$, where $t_v = t_0$ for all $v$ and the integers $n_w$ at the complex places are all $\ge 0$ or all $\le 0$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. For $n \neq 0$ the function $\Lambda$ is entire and the root number is $\chi_{\mathrm{id}}(\mathfrak{d}) (-i)^{\sum_w |n_w|}$ for the unitary twist $\chi$ of $\xi$ or of $\xi^{-1}$. For $n = 0$ this is `Langlands.Tate.heckeFunctionalEquation_of_unramified`. -/
theorem heckeFunctionalEquation_of_unramified_parallel (ξ : HeckeCharacter K)
    (hu : ∀ v, ξ.IsUnramifiedAt v) (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) (t₀ : ℂ) (ht : ∀ v, t v = t₀)
    (hsign : (∀ w, ¬ IsReal w → 0 ≤ n w) ∨ (∀ w, ¬ IsReal w → n w ≤ 0)) :
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
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) := by
    rcases hsign with hs | hs
    · have hn0 : ∀ w, 0 ≤ n w := fun w => by
        by_cases hw : IsReal w
        · rcases (hn w).isReal hw with h | h <;> omega
        · exact hs w hw
      exact entireFunctionalEquation_unramified h0χ hp hp' ht0 hn0 hne
    · have hinv : ∀ w, n' w = (if IsReal w then n w else -n w) ∧ t' w + t₀ = 0 := fun w => by
        have e := isArchimedeanParameter_unique (hp' w) (hp w).inv
        rwa [ht0, neg_zero] at e
      have hn0 : ∀ w, 0 ≤ n' w := fun w => by
        rw [(hinv w).1]
        by_cases hw : IsReal w
        · rw [ite_eq_left hw]
          rcases (hn w).isReal hw with h | h <;> omega
        · rw [ite_eq_right hw]
          have := hs w hw
          omega
      have hne' : ∃ w, n' w ≠ 0 := by
        obtain ⟨w, hw⟩ := hne
        refine ⟨w, ?_⟩
        rw [(hinv w).1]
        split_ifs <;> omega
      have hpi : ∀ v, χ⁻¹⁻¹.IsArchimedeanParameter v (n v) (t v - t₀) := by
        rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
        exact hp
      exact EntireFunctionalEquation.of_inv (entireFunctionalEquation_unramified
        (by rw [ramifiedSet_inv, h0χ]) hp' hpi (fun w => (hinv w).2) hn0 hne')
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hχu)

/-- **Hecke's functional equation for the unramified characters of a field with one infinite place.** If $K$ has exactly one infinite place, as for $\mathbb{Q}$ and the imaginary quadratic fields, then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for each Hecke character $\xi$ that is unramified at each finite place. -/
theorem heckeFunctionalEquation_of_unramified_of_subsingleton [Subsingleton (InfinitePlace K)]
    (ξ : HeckeCharacter K) (hu : ∀ v, ξ.IsUnramifiedAt v) (n n' : InfinitePlace K → ℤ)
    (t t' : InfinitePlace K → ℂ) (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
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
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  refine heckeFunctionalEquation_of_unramified_parallel ξ hu n n' t t' hn hn' (t w₀)
    (fun v => by rw [Subsingleton.elim v w₀]) ?_
  rcases le_total 0 (n w₀) with h | h
  · exact Or.inl fun w _ => by rwa [Subsingleton.elim w w₀]
  · exact Or.inr fun w _ => by rwa [Subsingleton.elim w w₀]

end Assembly

end Langlands.Tate
