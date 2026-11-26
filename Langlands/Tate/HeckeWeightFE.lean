/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.PeriodicGauss
import Langlands.Tate.RayClassHecke
import Langlands.Tate.ArchimedeanParameter

/-!
# Hecke's functional equation for characters of weight $n \neq 0$ of an imaginary quadratic field

Let $K$ be an imaginary quadratic field, let $\sigma$ be the embedding of its complex place, and let $\chi$ be a Hecke character with the archimedean parameters $(n, t)$ at the complex place and conductor $\mathfrak{f}$. This file proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each $\chi$ with $n \neq 0$ that is ramified at one finite place. With the case $n = 0$ of `Langlands.Tate.RayClassHecke`, it then holds for each Hecke character of $K$ that is ramified at one finite place.

## Main definitions

* `Langlands.Tate.weightTerm`: the term $\gamma^k |\gamma|^{-s}$ of the weighted series, with $\gamma = \sqrt 2 \sigma(\beta)$.
* `Langlands.Tate.weightClassCompleted`: the function $\Lambda^k_J(s) = \sum_x c_J(\xi_x) \Lambda^k_{\sqrt 2 \sigma(\mathfrak{f} J)}(\sqrt 2 \sigma(\xi_x), 0; s)$, a finite sum of weighted Epstein zeta functions over the residues $x$ modulo $\mathfrak{f} J$.
* `Langlands.Tate.EntireFunctionalEquation`: the functional equation with entire functions $\Lambda$ and $\Lambda'$ and $\sigma = 0$.

## Main results

* `differentiable_weightClassCompleted`: for $k \neq 0$, the function $\Lambda^k_J$ is entire.
* `gammaℝ_mul_finiteLFunction_weight`: for a unitary $\chi$ with the parameters $(k, 0)$ and $\mathrm{Re}\, u > 1$, $\Gamma_\mathbb{R}(2u + k) L(u, \chi) = \frac{1}{w} \sum_C (2 N(J_C))^u \Lambda^k_{J_C}(2u + k)$.
* `hasSum_weightClassCompleted_sub`: for $\mathrm{Re}\, u > 1$, the value $\Lambda^k_J(2 (1 - u) + k)$ is a sum over the ideals $I$ in the class of $\mathfrak{f} J \mathfrak{d}$ of the terms of the $L$-series of $\chi^{-1}$.
* `periodicGaussSum_eq_one`: the periodic Gauss sum $\tau_J(\chi)$ does not depend on $J$.
* `weight_dual_eq_completed`: the dual side gives $2^{1 - u} \Gamma_\mathbb{R}(2u + k) L(u, \chi^{-1})$, with the root number $W = (-i)^k \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$.
* `entireFunctionalEquation_weight`: the functional equation with entire functions for a unitary ramified $\chi$ with the parameters $(k, 0)$, $k \neq 0$.
* `EntireFunctionalEquation.of_inv` and `EntireFunctionalEquation.heckeFunctionalEquation`: the swap of $\chi$ and $\chi^{-1}$, and the conclusion of `Langlands.HeckeFunctionalEquationAt` from the entire form.
* `heckeFunctionalEquation_of_isQuadratic_of_weight`: the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each Hecke character that is ramified at one finite place and has $n \neq 0$.
* `heckeFunctionalEquation_of_isQuadratic_of_ramified`: the same for each Hecke character that is ramified at one finite place.

## Proofs

Let $\chi$ be unitary and ramified at one place, with the parameters $(k, 0)$ at the complex place and $k \neq 0$. By `rayCoeff_eq_periodicCoeff_mul_quad`, the term of the partial $L$-series of the class of $J^{-1}$ at $(\alpha) J^{-1}$ is $c_J(\alpha) \bar\gamma^k |\gamma|^{-k - 2u}$ up to a power of $2$, with $\gamma = \sqrt 2 \sigma(\alpha)$. We sort the $\alpha$ by the residue modulo $\mathfrak{f} J$, on which $c_J$ depends. This writes the partial $L$-series through $\Lambda^k_J(2u + k)$, and the sum over the classes gives $\Gamma_\mathbb{R}(2u + k) L(u, \chi)$. The archimedean factor is $\Gamma_\mathbb{C}(s + k/2) = 2^{1 - s} 2^{-k/2} \Gamma_\mathbb{R}(2s + k)$ by `gammaFactor_weight`. We use $$\Lambda(s) = 2^{1 - s} 2^{-k/2} \frac{1}{w} \sum_C (2 N(J_C))^s \Lambda^k_{J_C}(2s + k),$$ which is entire, and $\Lambda'(s) = W^{-1} (|d_K| N(\mathfrak{f}))^{1/2 - s} \Lambda(1 - s)$. Then the functional equation holds by definition, and $|W| = 1$ by `norm_periodicGaussSum_sq`.

For the dual side, the weighted theta relation `completedWeightZeta_quadLattice_sub` gives $(-i)^k (N(\mathfrak{f}) N(J) \sqrt{|d_K|})^{-1}$ times a series over the nonzero $\beta \in (\mathfrak{f} J)^\vee$ with the periodic Gauss coefficients $G_J(\beta)$. We sort the terms by the integral ideal $I = (\beta) \mathfrak{f} J \mathfrak{d}$ with `dualEquiv`. By `IsRayGaussPair.periodicGaussCoeff_eq` and the identity $\gamma^k \overline{\chi_\infty(\beta)} = |\gamma|^k$, each term is $\tau_1(\chi) (2 / (N(\mathfrak{f}) N(J) |d_K|))^{-u} \chi^{-1}(I) N(I)^{-u}$, and each fiber has $w$ elements. The constants then combine as in `scalar_mul_eq`.

For a general $\xi$ with $n \neq 0$, put $\chi = \xi \|\cdot\|^{-t}$. Then $\chi$ has the parameters $(n, 0)$, so it is unitary, and it has the same ramification. If $n > 0$, the result above applies to $\chi$. If $n < 0$, it applies to $\chi^{-1}$ with the parameters $(-n, 0)$, and `EntireFunctionalEquation.of_inv` moves it back to $\chi$. The twist back to $\xi$ is `heckeFunctionalEquation_of_twist`.

## Open parts

`Langlands.HeckeFunctionalEquationAt K` for an imaginary quadratic field $K$ is still open for the characters with $n \neq 0$ that are unramified at all finite places. This file uses the ramified place in the steps on the residues and on the Gauss sums, which come from `Langlands.Tate.PeriodicGauss`. For the unramified characters, these steps are not done for $\mathfrak{f} = 1$. The other number fields are as in `Langlands.Tate.RayClassHecke`.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open Module Filter Topology Set Complex
open NumberField IsDedekindDomain InfinitePlace NumberField.Units NumberField.mixedEmbedding
open scoped nonZeroDivisors Classical ComplexConjugate

namespace Langlands.Tate

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

section Unitary

/-- **A unitary criterion.** If $|\chi_w(y)| = 1$ at each infinite place $w$, then $|\chi(x)| = 1$ for each idele $x$. -/
theorem norm_ideleChar_of_norm_infiniteComponent
    (h : ∀ (w : InfinitePlace K) (y : w.Completionˣ), ‖(χ.infiniteComponent w y : ℂ)‖ = 1)
    (x : IdeleGroup (𝓞 K) K) : ‖(ideleChar χ x : ℂ)‖ = 1 := by
  have hc : IsClassType (normChar χ) :=
    { unramified := fun v y hy _ => by
        refine Units.ext ?_
        change ((‖(χ.finiteComponent v y : ℂ)‖ : ℝ) : ℂ) = 1
        rw [norm_finiteComponent_of_valued_eq_one χ v y hy, Complex.ofReal_one]
      trivial_inf := fun w y => by
        refine Units.ext ?_
        change ((‖(χ.infiniteComponent w y : ℂ)‖ : ℝ) : ℂ) = 1
        rw [h w y]
        simp }
  have h' := hc.norm_apply x
  change ‖((‖(χ (x : IdeleClassGroup (𝓞 K) K) : ℂ)‖ : ℝ) : ℂ)‖ = 1 at h'
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_norm] at h'

/-- If $\chi$ has the archimedean parameters $(n_w, 0)$ at each infinite place $w$, then $|\chi_w(y)| = 1$. -/
theorem norm_infiniteComponent_of_isArchimedeanParameter {n : InfinitePlace K → ℤ}
    (hn : ∀ w, χ.IsArchimedeanParameter w (n w) 0) (w : InfinitePlace K) (y : w.Completionˣ) :
    ‖(χ.infiniteComponent w y : ℂ)‖ = 1 := by
  have h0 : InfinitePlace.Completion.extensionEmbedding w y ≠ 0 := (y.isUnit.map _).ne_zero
  rw [(hn w).eq y, mul_zero, cpow_zero, mul_one, norm_zpow, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]

end Unitary

section Residues

variable [IsTotallyComplex K]

set_option hygiene false in
/-- The bijection $J \to \varphi(J)$. -/
local notation "𝔢[" J "]" => globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

set_option hygiene false in
/-- The finite quotient $\varphi(J) / \varphi(\mathfrak{f} J)$. -/
local notation "𝔔[" χ ", " J "]" => traceLattice K (FractionalIdeal.mk0 K J) ⧸
  subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)

/-- The term of the weighted series: $T_k(\beta; s) = \Gamma_\mathbb{R}(s) \overline{\gamma}^k |\gamma|^{-s}$ with $\gamma = \sqrt 2 \, \sigma(\beta)$, and $T_k(0; s) = 0$. -/
noncomputable def weightTerm (hK : finrank ℚ K = 2) (k : ℕ) (s : ℂ) (β : K) : ℂ :=
  if β = 0 then 0 else
    Complex.Gammaℝ s * ((conj (quadEmbed K hK β)) ^ k * ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-s))

/-- **The completed partial $L$-function of weight $k$.** For a nonzero integral ideal $J$, $$\Lambda^k_J(s) = \sum_{x \in J / \mathfrak{f} J} c_J(\xi_x) \Lambda^k_{\sqrt 2 \sigma(\mathfrak{f} J)}(\sqrt 2 \sigma(\xi_x), 0; s),$$ where $c_J$ is the periodic coefficient and $\xi_x \in J$ is the representative of the class $x$. -/
noncomputable def weightClassCompleted (χ : HeckeCharacter K) (hK : finrank ℚ K = 2) (k : ℕ)
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ∑ q : 𝔔[χ, J], periodicLatticeCoeff χ J q.out *
    completedWeightZeta (quadLattice K hK (FractionalIdeal.mk0 K (conductorNZ χ * J))) k
      (quadEmbed K hK (𝔢[J].symm q.out : K)) 0 s

/-- For $k \neq 0$, the function $\Lambda^k_J$ is entire. -/
theorem differentiable_weightClassCompleted (hK : finrank ℚ K = 2) {k : ℕ} (hk : k ≠ 0)
    (J : (Ideal (𝓞 K))⁰) : Differentiable ℂ (weightClassCompleted χ hK k J) := by
  unfold weightClassCompleted
  exact Differentiable.fun_sum fun q _ =>
    (differentiable_completedWeightZeta _ hk _ _).const_mul _

omit [IsTotallyComplex K] in
/-- The translate of a point of $\varphi(J)$ by a point of $\varphi(\mathfrak{f} J)$. -/
theorem symm_add_globalLatticeEquiv (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) (α : 𝔣[conductorNZ χ * J]) :
    (𝔢[J].symm (ℓ + ⟨_, rayLattice_le χ J (𝔢[conductorNZ χ * J] α).2⟩) : K) =
      (𝔢[J].symm ℓ : K) + α := by
  have h : 𝔢[J].symm (ℓ + ⟨_, rayLattice_le χ J (𝔢[conductorNZ χ * J] α).2⟩) =
      ⟨(𝔢[J].symm ℓ : K) + α, add_mem (𝔢[J].symm ℓ).2 (mem_of_mem_conductor_mul J α.2)⟩ := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    change (ℓ : euclidean.mixedSpace K) + globalEmbedding K _ (α : K) =
      globalEmbedding K _ ((𝔢[J].symm ℓ : K) + α)
    rw [map_add]
    congr 1
    rw [← coe_globalLatticeEquiv, Equiv.apply_symm_apply]
  rw [h]

omit [IsTotallyComplex K] in
/-- If $\chi$ is unitary, then the periodic coefficient has absolute value at most $1$. -/
theorem norm_periodicCoeff_le (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ‖periodicCoeff χ J α‖ ≤ 1 := by
  by_cases h : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · rw [norm_periodicCoeff_of_cond hu J h]
  · rw [periodicCoeff_eq_zero_of_not J h, norm_zero]
    exact zero_le_one

/-- **The completed partial $L$-function of weight $k$ as a series.** Let $\chi$ be unitary and ramified at one place. For $\mathrm{Re}\, s > k + 2$, $$\Lambda^k_J(s) = \sum_{\beta \in J} c_J(\beta) T_k(\beta; s).$$ -/
theorem hasSum_weightClassCompleted (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) (k : ℕ)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun β : 𝔣[J] =>
        periodicCoeff χ (FractionalIdeal.mk0 K J) β * weightTerm hK k s β)
      (weightClassCompleted χ hK k J s) := by
  have h0 : Summable fun α : 𝔣[J] => weightTerm hK k s α := by
    have h := hasSum_completedWeightZeta_quadLattice K hK k (FractionalIdeal.mk0 K J) 0 hs
    simp only [zero_add] at h
    exact h.summable
  have h1 : Summable fun α : 𝔣[J] =>
      periodicCoeff χ (FractionalIdeal.mk0 K J) α * weightTerm hK k s α := by
    refine Summable.of_norm_bounded (summable_norm_iff.2 h0) fun α => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_periodicCoeff_le hu _ _)
  refine (𝔢[J].symm.hasSum_iff).1 ?_
  have hsum := (𝔢[J].symm.summable_iff).2 h1
  have hfib : ∀ q : 𝔔[χ, J],
      HasSum (fun ℓ : {ℓ : traceLattice K (FractionalIdeal.mk0 K J) //
          (ℓ : 𝔔[χ, J]) = q} =>
          periodicCoeff χ (FractionalIdeal.mk0 K J) (𝔢[J].symm ℓ : K) *
            weightTerm hK k s (𝔢[J].symm ℓ : K))
        (periodicLatticeCoeff χ J q.out *
          completedWeightZeta (quadLattice K hK (FractionalIdeal.mk0 K (conductorNZ χ * J))) k
            (quadEmbed K hK (𝔢[J].symm q.out : K)) 0 s) := by
    intro q
    rw [← (fiberEquiv _ _ (rayLattice_le χ J) q).symm.hasSum_iff,
      ← (𝔢[conductorNZ χ * J] : _ ≃ rayLattice χ J).hasSum_iff]
    convert (hasSum_completedWeightZeta_quadLattice K hK k
      (FractionalIdeal.mk0 K (conductorNZ χ * J)) (𝔢[J].symm q.out : K) hs).mul_left
      (periodicLatticeCoeff χ J q.out) using 1
    funext α
    change periodicLatticeCoeff χ J (q.out + ⟨_, rayLattice_le χ J (𝔢[conductorNZ χ * J] α).2⟩) *
      weightTerm hK k s (𝔢[J].symm (q.out +
        ⟨_, rayLattice_le χ J (𝔢[conductorNZ χ * J] α).2⟩) : K) = _
    rw [periodicLatticeCoeff_add hS J, symm_add_globalLatticeEquiv]
    rfl
  have h2 := ((Equiv.sigmaFiberEquiv (fun ℓ : traceLattice K (FractionalIdeal.mk0 K J) =>
    (ℓ : 𝔔[χ, J]))).hasSum_iff.2 hsum.hasSum).sigma hfib
  have h3 := h2.unique (hasSum_fintype _)
  rw [weightClassCompleted, ← h3]
  exact hsum.hasSum

end Residues

section Direct

/-- If $\chi$ is unitary, then the coefficient `Langlands.Tate.rayCoeff` has absolute value at most $1$. -/
theorem norm_rayCoeff_le_of_unitary (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ‖rayCoeff χ J α‖ ≤ 1 := by
  rw [rayCoeff]
  split_ifs
  · rw [Units.val_mul, norm_mul, norm_idealChar_of_unitary hχ, Units.val_inv_eq_inv_val, norm_inv,
      norm_idealChar_of_unitary hχ, inv_one, mul_one]
  · simp

/-- If $\chi$ is unitary, then $|\chi(I) N(I)^{-s}| \leq |N(I)^{-s}|$. -/
theorem norm_rayWeight_le_of_unitary (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖rayWeight χ s I‖ ≤ ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖ := by
  rw [rayWeight_apply, norm_mul, norm_mul, norm_idealChar_of_unitary hχ, mul_one]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  split_ifs <;> simp

/-- **The Dirichlet series of a unitary character.** For a unitary Hecke character $\chi$ and $\mathrm{Re}\, s > 1$, $L(s, \chi) = \sum_I \chi(I) N(I)^{-s}$, where $I$ runs over the nonzero ideals prime to the ramified places. -/
theorem finiteLFunction_eq_of_unitary (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    {s : ℂ} (hs : 1 < s.re) : χ.finiteLFunction s = ∑' I, rayWeight χ s I := by
  refine HasProd.tprod_eq ?_
  convert hasProd_of_norm_le (rayWeight χ s) hs (norm_rayWeight_le_of_unitary hχ s) using 1
  funext v
  by_cases hv : v ∈ ramifiedSet χ
  · rw [NonArchimedean.localFactor_eq_one_of_not_isUnramifiedAt v χ (mem_ramifiedSet.1 hv),
      rayWeight_primeNZ_of_mem s hv, sub_zero, inv_one]
  · rw [HeckeCharacter.localFactor, ite_eq_left (not_not.1 (mt mem_ramifiedSet.2 hv)),
      rayWeight_primeNZ_of_notMem s hv, primeValue]

variable [IsTotallyComplex K]

/-- **The series over $J$ sorted by ideals.** Let $\chi$ be unitary. For $\mathrm{Re}\, u > 1$, the series $\sum_{\beta \in J, \, \beta \neq 0} \chi((\beta) J^{-1}) (2 |N(\beta)|)^{-u}$ is the sum over the integral ideals $I$ of the class $[J]^{-1}$ of $w (2 N(J))^{-u} \chi(I) N(I)^{-u}$. -/
theorem hasSum_rayCoeff_ideals_of_unitary
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2)
    (J : (Ideal (𝓞 K))⁰) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      (if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then (torsionOrder K : ℂ) else 0) *
        (((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u) * rayWeight χ u I))
      (∑' β : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K),
        rayCoeff χ (FractionalIdeal.mk0 K J) β * if (β : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u))) := by
  have hs := two_lt_re_two_mul hu
  set g : ↥(FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) → ℂ := fun β =>
    rayCoeff χ (FractionalIdeal.mk0 K J) β * if (β : K) = 0 then (0 : ℂ) else
      ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u)) with hg
  have hsum : Summable g := by
    refine Summable.of_norm_bounded (summable_quadraticTerm K hK _ hs).norm fun β => ?_
    rw [hg, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_rayCoeff_le_of_unitary hχ _ _)
  have h2 := (hasSum_subtype_iff_of_support_subset (s := {β | (β : K) ≠ 0}) (f := g)
    (fun β hβ h0 => hβ (by simp only [hg, h0, ite_true, mul_zero]))).2 hsum.hasSum
  have h3 := (nonzeroEquiv K J).hasSum_iff.2 h2
  have h4 := (elementEquiv K J).symm.hasSum_iff.2 h3
  refine h4.sigma fun I => ?_
  have := finite_generators K hK J I
  have := Fintype.ofFinite {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I}
  set X : ℂ := ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u) * rayWeight χ u I with hX
  have hv : ∀ c : {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I},
      g ⟨((c.1 : 𝓞 K) : K), ((nonzeroEquiv K J) ((elementEquiv K J).symm ⟨I, c⟩)).1.2⟩ = X :=
      fun c => by
    have hc0 : ((c.1 : 𝓞 K) : K) ≠ 0 := by
      exact_mod_cast ne_zero_of_span_eq_mul K J I c.2
    simp only [hg, ite_eq_right hc0]
    rw [abs_norm_eq_of_span_eq_mul K J I c.2, show -(2 * u) = 2 * -u by ring,
      sqrt_cpow_two_mul (by positivity), ← mul_assoc, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), hX,
      ← rayCoeff_mul_cpow J I c.2 u, Complex.ofReal_natCast (Ideal.absNorm (I : Ideal (𝓞 K)))]
    ring
  have h5 := hasSum_fintype (fun _ : {α : 𝓞 K // Ideal.span {α} = (J : Ideal (𝓞 K)) * I} => X)
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
    natCard_generators K hK J I, Nat.cast_ite, Nat.cast_zero] at h5
  exact h5.congr_fun fun c => hv c

/-- **The term of weight $k$ and the coefficient of the $L$-series.** Let $\chi$ have the parameters $(k, 0)$ at the complex place. For $\beta \neq 0$, $$c_J(\beta) T_k(\beta; 2u + k) = \Gamma_\mathbb{R}(2u + k) \chi((\beta) J^{-1}) (2 |N(\beta)|)^{-u}.$$ -/
theorem periodicCoeff_mul_weightTerm (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {β : K} (hβ : β ≠ 0) (u : ℂ) :
    periodicCoeff χ J β * weightTerm hK k (2 * u + k) β = Complex.Gammaℝ (2 * u + k) *
      (rayCoeff χ J β * ((√(2 * |(Algebra.norm ℚ β : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u))) := by
  have hq0 : quadEmbed K hK β ≠ 0 := mt (quadEmbed_eq_zero_iff K hK).1 hβ
  have hn0 : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 hq0
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 := by simp
  have hq : conj (quadEmbed K hK β) / ((‖quadEmbed K hK β‖ : ℝ) : ℂ) =
      conj ((quadPlace K hK).1.embedding β) / (‖(quadPlace K hK).1.embedding β‖ : ℂ) := by
    rw [quadEmbed_apply, map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.ofReal_mul,
      mul_div_mul_left _ _ h2]
  rw [weightTerm, ite_eq_right hβ, rayCoeff_eq_periodicCoeff_mul_quad K hK h J hβ, ← norm_quadEmbed K hK,
    ← hq, show -(2 * u + k) = -(2 * u) + -(k : ℂ) by ring, cpow_add _ _ hn0, cpow_neg _ (k : ℂ),
    cpow_natCast, zpow_natCast, mul_zero, neg_zero, cpow_zero, mul_one, div_pow]
  ring

/-- **The partial $L$-series of weight $k$.** Let $\chi$ be unitary, ramified at one place, with the parameters $(k, 0)$ at the complex place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u + k) \sum_{[I] = [J]^{-1}} \chi(I) N(I)^{-u} = \frac{(2 N(J))^u}{w} \Lambda^k_J(2u + k).$$ -/
theorem hasSum_weight_partialLSeries (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) (J : (Ideal (𝓞 K))⁰)
    {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then
        Complex.Gammaℝ (2 * u + k) * rayWeight χ u I else 0)
      ((torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        weightClassCompleted χ hK k J (2 * u + k)) := by
  have hs : (k + 2 : ℝ) < (2 * u + k).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re]
    linarith
  have h1 := hasSum_weightClassCompleted hS hχ hK k J hs
  have e : (fun β : ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =>
      periodicCoeff χ (FractionalIdeal.mk0 K J) β * weightTerm hK k (2 * u + k) β) =
      fun β : ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =>
        Complex.Gammaℝ (2 * u + k) * (rayCoeff χ (FractionalIdeal.mk0 K J) (β : K) *
        if (β : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u))) := by
    funext β
    by_cases hβ : (β : K) = 0
    · simp [hβ, weightTerm]
    · rw [periodicCoeff_mul_weightTerm hK h _ hβ, ite_eq_right hβ]
  rw [e] at h1
  have h2 := hasSum_rayCoeff_ideals_of_unitary hχ hK J hu
  have h3 : weightClassCompleted χ hK k J (2 * u + k) = Complex.Gammaℝ (2 * u + k) *
      ∑' β : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K),
        rayCoeff χ (FractionalIdeal.mk0 K J) β * if (β : K) = 0 then (0 : ℂ) else
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-(2 * u)) := by
    rw [← h1.tsum_eq, tsum_mul_left]
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hN : (0 : ℝ) < 2 * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    have : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := Nat.cast_pos.2 (Nat.pos_of_ne_zero
      fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    positivity
  have hA : ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hN.ne'))
  rw [h3]
  have h4 := h2.mul_left ((torsionOrder K : ℂ)⁻¹ *
    ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u * Complex.Gammaℝ (2 * u + k))
  rw [show (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
      Complex.Gammaℝ (2 * u + k) * _ = _ from (mul_assoc _ _ _)] at h4
  refine h4.congr_fun fun I => ?_
  rw [Complex.cpow_neg]
  split_ifs
  · field_simp
  · ring

/-- **The $L$-series of weight $k$ as a sum over the ideal classes.** Let $\chi$ be unitary, ramified at one place, with the parameters $(k, 0)$ at the complex place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u + k) L(u, \chi) = \frac{1}{w} \sum_{C} (2 N(J_C))^u \Lambda^k_{J_C}(2u + k),$$ where $J_C$ is an integral ideal of the class $C$. -/
theorem gammaℝ_mul_finiteLFunction_weight (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {u : ℂ} (hu : 1 < u.re) :
    Complex.Gammaℝ (2 * u + k) * χ.finiteLFunction u = ∑ C : ClassGroup (𝓞 K),
      (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        weightClassCompleted χ hK k (classIdeal K C) (2 * u + k) := by
  have h1 := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hasSum_weight_partialLSeries hS hχ hK h (classIdeal K C) hu)
  rw [finiteLFunction_eq_of_unitary hχ hu, ← tsum_mul_left]
  refine (h1.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk0 (classIdeal K C))⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk0_classIdeal]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

end Direct

section Dual

variable [IsTotallyComplex K]

set_option hygiene false in
/-- The bijection $J \to \varphi(J)$. -/
local notation "𝔢[" J "]" => globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)

set_option hygiene false in
/-- The nonzero ideal $J$ as a fractional ideal. -/
local notation "𝔣[" J "]" =>
  ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

set_option hygiene false in
/-- The finite quotient $\varphi(J) / \varphi(\mathfrak{f} J)$. -/
local notation "𝔔[" χ ", " J "]" => traceLattice K (FractionalIdeal.mk0 K J) ⧸
  subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)

/-- **The dual side of weight $k$ as a Dirichlet series.** For $\mathrm{Re}\, s > k + 2$, the sum $\sum_x c_J(\xi_x) \Lambda^k_{(\sqrt 2 \sigma(\mathfrak{f} J))^\vee}(0, \sqrt 2 \sigma(\xi_x); s)$ is the sum over the nonzero $\beta \in (\mathfrak{f} J)^\vee$ of $\Gamma_\mathbb{R}(s) \gamma^k G_J(\beta) |\gamma|^{-s}$, where $\gamma = \sqrt 2 \, \sigma(\beta)$ and $G_J$ is the periodic Gauss sum. -/
theorem hasSum_weight_dual (hK : finrank ℚ K = 2) (k : ℕ) (J : (Ideal (𝓞 K))⁰) {s : ℂ}
    (hs : (k + 2 : ℝ) < s.re) :
    HasSum (fun β : FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J] =>
      if (β : K) = 0 then (0 : ℂ) else Complex.Gammaℝ s *
        ((quadEmbed K hK β) ^ k * periodicGaussCoeff χ J β *
          ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-s)))
      (∑ q : 𝔔[χ, J], periodicLatticeCoeff χ J q.out *
        completedWeightZeta (dualLattice (quadLattice K hK
          (FractionalIdeal.mk0 K (conductorNZ χ * J)))) k 0
          (quadEmbed K hK (𝔢[J].symm q.out : K)) s) := by
  have h := hasSum_sum (fun (q : 𝔔[χ, J]) (_ : q ∈ Finset.univ) =>
    (hasSum_completedWeightZeta_dual_quadLattice K hK k
      (FractionalIdeal.mk0 K (conductorNZ χ * J)) (𝔢[J].symm q.out : K) hs).mul_left
      (periodicLatticeCoeff χ J q.out))
  refine h.congr_fun fun β => ?_
  split_ifs
  · simp
  · rw [periodicGaussCoeff_def, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [traceExp]
    ring

omit [IsTotallyComplex K] in
/-- For a unitary character, $\overline{\chi(I)} = \chi^{-1}(I)$. -/
theorem conj_idealChar_of_unitary (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    conj (idealChar χ I : ℂ) = (idealChar χ⁻¹ I : ℂ) := by
  have hc : (idealChar χ I : ℂ) * conj (idealChar χ I : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_idealChar_of_unitary hχ, one_pow,
      Complex.ofReal_one]
  rw [idealChar_inv, Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_right hc

omit [IsTotallyComplex K] in
/-- If $I = (\beta) \mathfrak{f} J \mathfrak{d}$, then $(\beta) = I (\mathfrak{f} J)^\vee$ as units. -/
theorem toPrincipalIdeal_dualFiber {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I) :
    toPrincipalIdeal (𝓞 K) K (Units.mk0 (β : K) β.ne_zero) =
      FractionalIdeal.mk0 K I * gaussDual χ J := by
  apply Units.ext
  rw [coe_toPrincipalIdeal, Units.val_mk0, Units.val_mul, coe_gaussDual]
  exact spanSingleton_eq_coeIdeal_mul_dual J β.2

omit [IsTotallyComplex K] in
/-- If $I = (\beta) \mathfrak{f} J \mathfrak{d}$ is prime to $\mathfrak{f}$, then $c_D(\beta) = \chi(I) \chi_\infty(\beta)$ for $D = (\mathfrak{f} J)^\vee$. -/
theorem periodicCoeff_gaussDual_dualFiber {J I : (Ideal (𝓞 K))⁰} (β : DualFiber χ J I)
    (hI : (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤) :
    periodicCoeff χ (gaussDual χ J) β = (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) *
      (infChar χ (Units.mk0 (β : K) β.ne_zero) : ℂ) := by
  rw [IsRayGaussPair.periodicCoeff_gaussDual (I := I) ⟨β.2, hI⟩, periodicChar_apply,
    toPrincipalIdeal_dualFiber β, map_mul, mul_right_comm _ (infChar χ _), mul_inv_cancel_right,
    Units.val_mul]

/-- Let $\chi$ have the parameters $(k, 0)$ at the complex place. For $\beta \neq 0$, $\gamma^k \overline{\chi_\infty(\beta)} = |\gamma|^k$ with $\gamma = \sqrt 2 \, \sigma(\beta)$. -/
theorem quadEmbed_pow_mul_conj_infChar (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {β : K} (hβ : β ≠ 0) :
    quadEmbed K hK β ^ k * conj (infChar χ (Units.mk0 β hβ) : ℂ) =
      ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k := by
  have hz : (quadPlace K hK).1.embedding β ≠ 0 := by simpa using hβ
  have hn : ((‖(quadPlace K hK).1.embedding β‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
  rw [infChar_apply_of_isArchimedeanParameter K hK h, Units.val_mk0, mul_zero, cpow_zero, mul_one,
    zpow_natCast, map_pow, ← mul_pow, map_div₀, Complex.conj_ofReal, quadEmbed_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  rw [mul_assoc, mul_div_assoc', Complex.mul_conj', Complex.ofReal_mul]
  field_simp

/-- **The terms of the dual series of weight $k$.** Let $\chi$ be unitary, ramified at one place, with the parameters $(k, 0)$ at the complex place, and let $I = (\beta) \mathfrak{f} J \mathfrak{d}$. Then $$\gamma^k G_J(\beta) |\gamma|^{-(2u + k)} = \tau_J(\chi) \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u},$$ with $\gamma = \sqrt 2 \, \sigma(\beta)$, where $\chi^{-1}(I) = 0$ if $I$ is not prime to $\mathfrak{f}$. -/
theorem weight_periodicGaussCoeff_mul_cpow (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {J I : (Ideal (𝓞 K))⁰}
    (β : DualFiber χ J I) (u : ℂ) :
    quadEmbed K hK β ^ k * periodicGaussCoeff χ J β *
        ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k)) =
      periodicGaussSum χ J * ((2 / ((Ideal.absNorm χ.conductor : ℝ) *
        Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
          rayWeight χ⁻¹ u I := by
  have hq0 : quadEmbed K hK β ≠ 0 := mt (quadEmbed_eq_zero_iff K hK).1 β.ne_zero
  have hn0 : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hq0
  have hc := conductor_mul_absNorm_mul_discr_pos χ J
  have hn : 2 * |(Algebra.norm ℚ (β : K) : ℝ)| = 2 / ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) * Ideal.absNorm (I : Ideal (𝓞 K)) := by
    rw [← β.abs_norm_mul, div_mul_eq_mul_div, eq_div_iff hc.ne']
    ring
  have hpow : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k)) =
      ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u)) * (((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k)⁻¹ := by
    rw [show -(2 * u + k) = -(2 * u) + -(k : ℂ) by ring, cpow_add _ _ hn0, cpow_neg _ (k : ℂ),
      cpow_natCast]
  have hnorm : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u)) =
      ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
        |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u) := by
    rw [norm_quadEmbed K hK, show -(2 * u) = 2 * -u by ring, sqrt_cpow_two_mul (by positivity), hn,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_natCast]
  rw [hpow, hnorm, rayWeight_apply, ramifiedSet_inv]
  by_cases hI : (I : Ideal (𝓞 K)) ⊔ χ.conductor = ⊤
  · rw [IsRayGaussPair.periodicGaussCoeff_eq hS hχ (I := I) ⟨β.2, hI⟩,
      periodicCoeff_gaussDual_dualFiber β hI, map_mul (starRingEnd ℂ), conj_idealChar_of_unitary hχ,
      ite_eq_left ((sup_conductor_eq_top_iff I).1 hI)]
    have e := quadEmbed_pow_mul_conj_infChar hK h β.ne_zero
    have hk : ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ hn0
    calc _ = periodicGaussSum χ J * (idealChar χ⁻¹ (FractionalIdeal.mk0 K I) : ℂ) *
          (quadEmbed K hK β ^ k * conj (infChar χ (Units.mk0 (β : K) β.ne_zero) : ℂ)) *
          (((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ k)⁻¹ *
          (((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
            |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
              (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-u)) := by ring
      _ = _ := by
        rw [e, mul_inv_cancel_right₀ hk]
        ring
  · rw [periodicGaussCoeff_eq_zero J (I : Ideal (𝓞 K)) β.2 hI,
      ite_eq_right (mt (sup_conductor_eq_top_iff I).2 hI)]
    ring

omit [IsTotallyComplex K] in
/-- The units identity $J (\mathfrak{f} J)^\vee = \mathfrak{f}^\vee$. -/
theorem mk0_mul_gaussDual (J : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.mk0 K J * gaussDual χ J = gaussDual χ 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_gaussDual, coe_gaussDual,
    ← inv_inv (FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * J]), inv_dual_conductor_mul J,
    ← inv_inv (FractionalIdeal.dual ℤ ℚ 𝔣[conductorNZ χ * 1]), inv_dual_conductor_mul 1,
    coe_mk0_conductorNZ_mul, coe_mk0_conductorNZ_mul, coe_mk0_one, mul_one]
  have hJ : 𝔣[J] ≠ 0 := Units.ne_zero _
  rw [show (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * 𝔣[J] *
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) =
      𝔣[J] * ((χ.conductor : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) by ring, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hJ, one_mul]

omit [IsTotallyComplex K] in
/-- **The periodic Gauss sum does not depend on $J$.** Let $\chi$ be unitary and ramified at one place. Then $\tau_J(\chi) = \tau_1(\chi)$ for each nonzero integral ideal $J$. -/
theorem periodicGaussSum_eq_one (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (J : (Ideal (𝓞 K))⁰) :
    periodicGaussSum χ J = periodicGaussSum χ 1 := by
  obtain ⟨β, I, h⟩ := exists_isRayGaussPair hS J
  obtain ⟨t, T, hT, hTf⟩ := exists_spanSingleton_eq_coeIdeal_mul (χ := χ) hS J
  obtain ⟨h', ha⟩ := h.periodicGaussCoeff_eq_mul_one hS hu hT hTf
  have hc := cond_of_spanSingleton_eq hT hTf
  rw [periodicGaussSum_eq hS h, periodicGaussSum_eq hS h', ha, h.periodicCoeff_gaussDual,
    h'.periodicCoeff_gaussDual, periodicCoeff_of_cond _ hc, ← periodicChar_apply, mul_assoc,
    ← Units.val_mul]
  congr 2
  rw [show Units.mk0 (β * t) h'.ne_zero = Units.mk0 β h.ne_zero * Units.mk0 t hc.1 from
    Units.ext rfl, map_mul, ← mk0_mul_gaussDual J, map_mul, mul_inv]
  ac_rfl

omit [IsTotallyComplex K] in
/-- **The parameters at a complex place are unique.** If $(n, t)$ and $(m, s)$ are archimedean parameters of $\chi$ at a place $v$ that is not real, then $n = m$ and $t = s$. -/
theorem eq_of_isArchimedeanParameter {v : InfinitePlace K} (hv : ¬ v.IsReal) {n m : ℤ}
    {t s : ℂ} (h1 : χ.IsArchimedeanParameter v n t) (h2 : χ.IsArchimedeanParameter v m s) :
    n = m ∧ t = s := by
  have h := eq_zero_of_forall_param_eq_one (v := v) (n := n - m) (t := t - s)
    (fun h => absurd h hv) fun x => by
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

/-- **The dual side of weight $k$.** Let $\chi$ be unitary, ramified at one place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$, and let $\mathrm{Re}\, u > 1$. Then $\Lambda^k_J(2 (1 - u) + k)$ is the sum over the integral ideals $I$ in the class of $\mathfrak{f} J \mathfrak{d}$ of $$\frac{(-i)^k}{N(\mathfrak{f}) N(J) \sqrt{|d_K|}} w \, \Gamma_\mathbb{R}(2u + k) \tau_1(\chi) \Big(\frac{2}{N(\mathfrak{f}) N(J) |d_K|}\Big)^{-u} \chi^{-1}(I) N(I)^{-u}.$$ -/
theorem hasSum_weightClassCompleted_sub (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0)
    (J : (Ideal (𝓞 K))⁰) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun A : (Ideal (𝓞 K))⁰ => ((-Complex.I) ^ k *
        ((((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
          √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ)) *
        if ClassGroup.mk0 (conductorNZ χ * J * differentNZ K) = ClassGroup.mk0 A then
          (torsionOrder K : ℂ) * (Complex.Gammaℝ (2 * u + k) * (periodicGaussSum χ 1 *
            ((2 / ((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
              |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) * rayWeight χ⁻¹ u A))
        else 0)
      (weightClassCompleted χ hK k J (2 * (1 - u) + k)) := by
  have hs : (k + 2 : ℝ) < (2 * u + k).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re]
    linarith
  have h1 := hasSum_weight_dual (χ := χ) hK k J hs
  rw [← hasSum_subtype_iff_of_support_subset (s := {β : FractionalIdeal.dual ℤ ℚ
      𝔣[conductorNZ χ * J] | (β : K) ≠ 0}) fun β hβ h0 => hβ (ite_eq_left h0)] at h1
  replace h1 := ((dualEquiv χ J).symm.hasSum_iff (f := fun β : {β : FractionalIdeal.dual ℤ ℚ
      𝔣[conductorNZ χ * J] // (β : K) ≠ 0} => if (β : K) = 0 then (0 : ℂ) else
      Complex.Gammaℝ (2 * u + k) * ((quadEmbed K hK β) ^ k * periodicGaussCoeff χ J β *
        ((‖quadEmbed K hK β‖ : ℝ) : ℂ) ^ (-(2 * u + k))))).2 h1
  have hN : ((FractionalIdeal.absNorm 𝔣[conductorNZ χ * J] : ℚ) : ℝ) =
      (Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Submonoid.coe_mul, map_mul]
    push_cast
    rfl
  have e : weightClassCompleted χ hK k J (2 * (1 - u) + k) = ((-Complex.I) ^ k *
      ((((Ideal.absNorm χ.conductor : ℝ) * Ideal.absNorm (J : Ideal (𝓞 K)) *
        √|(discr K : ℝ)|)⁻¹ : ℝ) : ℂ)) * ∑ q : 𝔔[χ, J], periodicLatticeCoeff χ J q.out *
        completedWeightZeta (dualLattice (quadLattice K hK
          (FractionalIdeal.mk0 K (conductorNZ χ * J)))) k 0
          (quadEmbed K hK (𝔢[J].symm q.out : K)) (2 * u + k) := by
    rw [weightClassCompleted, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show 2 * (1 - u) + (k : ℂ) = 2 * k + 2 - (2 * u + k) by ring,
      completedWeightZeta_quadLattice_sub K hK hk, hN]
    ring
  rw [e]
  refine HasSum.mul_left _ (h1.sigma fun A => ?_)
  have := finite_dualFiber (χ := χ) hK J A
  have := Fintype.ofFinite (DualFiber χ J A)
  convert hasSum_fintype fun _ : DualFiber χ J A => Complex.Gammaℝ (2 * u + k) *
    (periodicGaussSum χ 1 * ((2 / ((Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * |(discr K : ℝ)|) : ℝ) : ℂ) ^ (-u) *
        rayWeight χ⁻¹ u A) using 1
  · funext c
    refine (ite_eq_right c.ne_zero).trans (congrArg _ ?_)
    exact (weight_periodicGaussCoeff_mul_cpow hS hχ hK h c u).trans
      (by rw [periodicGaussSum_eq_one hS hχ J])
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_dualFiber hK,
      nsmul_eq_mul]
    split_ifs <;> simp

/-- **The functional equation of weight $k$ on the half plane.** Let $\chi$ be unitary, ramified at one place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$, and let $W = (-i)^k \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$. For $\mathrm{Re}\, u > 1$, $$W^{-1} (|d_K| N(\mathfrak{f}))^{1/2 - u} 2^{u} \frac{1}{w} \sum_C (2 N(J_C))^{1 - u} \Lambda^k_{J_C}(2 (1 - u) + k) = 2^{1 - u} \Gamma_\mathbb{R}(2u + k) L(u, \chi^{-1}).$$ -/
theorem weight_dual_eq_completed (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) (h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0) {u : ℂ}
    (hu : 1 < u.re) :
    ((-Complex.I) ^ k * periodicGaussSum χ 1 /
        ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
        (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - u) *
          ((2 : ℂ) ^ (1 - (1 - u)) * ∑ C : ClassGroup (𝓞 K), (torsionOrder K : ℂ)⁻¹ *
            ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u) *
              weightClassCompleted χ hK k (classIdeal K C) (2 * (1 - u) + k)) =
      (2 : ℂ) ^ (1 - u) * Complex.Gammaℝ (2 * u + k) * χ⁻¹.finiteLFunction u := by
  have hχ' : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ⁻¹ x : ℂ)‖ = 1 := fun x => by
    change ‖(((ideleChar χ x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hχ, inv_one]
  have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hτ : (-Complex.I) ^ k * periodicGaussSum χ 1 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) fun h0 => ?_
    have h2 := norm_periodicGaussSum_sq hS hχ 1
    rw [h0, norm_zero, zero_pow two_ne_zero] at h2
    exact hc.ne' (by exact_mod_cast h2.symm)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) =
      ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [finiteLFunction_eq_of_unitary hχ' hu, ← tsum_mul_left, hX]
  have h1 := hasSum_sum fun C (_ : C ∈ Finset.univ) =>
    (hasSum_weightClassCompleted_sub hS hχ hK hk h (classIdeal K C) hu).mul_left
      ((torsionOrder K : ℂ)⁻¹ *
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (1 - u))
  refine (HasSum.tsum_eq ?_).symm
  convert h1.mul_left (((-Complex.I) ^ k * periodicGaussSum χ 1 /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
    ((|(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ^ (1 / 2 - u) *
      (2 : ℂ) ^ (1 - (1 - u))) using 1
  · funext A
    simp only [mul_ite, mul_zero]
    simp_rw [mk0_conductor_mul_classIdeal_iff]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    have hb : ∀ J : (Ideal (𝓞 K))⁰, (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := fun J =>
      Nat.cast_pos.2 (Nat.pos_of_ne_zero
        fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
    rw [← scalar_mul_eq hc (hb (classIdeal K (ClassGroup.mk0 A *
      (ClassGroup.mk0 (conductorNZ χ) * ClassGroup.mk0 (differentNZ K))⁻¹))) hd hτ hw u
        (Complex.Gammaℝ (2 * u + k)) (rayWeight χ⁻¹ u A)]
    ring
  · ring

end Dual

section Assembly

/-- If $\chi$ is unitary, then $\chi^{-1}$ is unitary. -/
theorem norm_ideleChar_inv (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    (x : IdeleGroup (𝓞 K) K) : ‖(ideleChar χ⁻¹ x : ℂ)‖ = 1 := by
  change ‖(((ideleChar χ x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, hχ, inv_one]

/-- The functional equation with entire functions. There are entire functions $\Lambda$ and $\Lambda'$ that agree with $\Lambda(s, \chi)$ and $\Lambda(s, \chi^{-1})$ for $\mathrm{Re}\, s > 1$, and a number $W$ with $|W| = 1$, such that $\Lambda(s) = W (|d_K| N(\mathfrak{f}))^{1/2 - s} \Lambda'(1 - s)$ for all $s$. -/
def EntireFunctionalEquation (χ : HeckeCharacter K) (n n' : InfinitePlace K → ℤ)
    (t t' : InfinitePlace K → ℂ) : Prop :=
  ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ), Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
    (∀ s : ℂ, 1 < s.re → Λ s = χ.completedLFunction n t s) ∧
    (∀ s : ℂ, 1 < s.re → Λ' s = χ⁻¹.completedLFunction n' t' s) ∧
    ‖W‖ = 1 ∧
    ∀ s : ℂ, Λ s =
      W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) * Λ' (1 - s)

/-- **The swap of $\chi$ and $\chi^{-1}$.** If the functional equation with entire functions holds for $\chi^{-1}$, then it holds for $\chi$, with $W$ replaced by $W^{-1}$. -/
theorem EntireFunctionalEquation.of_inv {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (h : EntireFunctionalEquation χ⁻¹ n' n t' t) : EntireFunctionalEquation χ n n' t t' := by
  obtain ⟨Λ, Λ', W, hd, hd', hΛ, hΛ', hW, hfe⟩ := h
  rw [show χ⁻¹⁻¹ = χ from inv_inv χ] at hΛ'
  rw [conductor_inv] at hfe
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.2 (abs_ne_zero.2 (discr_ne_zero K)))
      (Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hW0 : W ≠ 0 := by
    rintro rfl
    simp at hW
  refine ⟨Λ', Λ, W⁻¹, hd', hd, hΛ', hΛ, by rw [norm_inv, hW, inv_one], fun s => ?_⟩
  rw [hfe (1 - s), sub_sub_cancel]
  calc Λ' s = (W⁻¹ * W) * ((((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
        (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - (1 - s))) *
          Λ' s := by
        rw [inv_mul_cancel₀ hW0, ← cpow_add _ _ hX, show 1 / 2 - s + (1 / 2 - (1 - s)) = 0 by ring,
          cpow_zero, one_mul, one_mul]
    _ = _ := by ring

/-- **The conclusion of Hecke's theorem from the entire form.** Let $\chi$ be unitary. If the functional equation with entire functions holds for $\chi$, then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\chi$, with $\sigma = 0$ and an entire function $\Lambda$. -/
theorem EntireFunctionalEquation.heckeFunctionalEquation
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
    {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (h : EntireFunctionalEquation χ n n' t t') :
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
  obtain ⟨Λ, Λ', W, hd, hd', hΛ, hΛ', hW, hfe⟩ := h
  refine ⟨0, fun x => by rw [Real.rpow_zero]; exact hχ x, Λ, Λ', W,
    fun s _ => (hd.analyticAt s).meromorphicAt, fun s _ => (hd'.analyticAt s).meromorphicAt,
    fun s hs => hΛ s (by simpa using hs), fun s hs => hΛ' s (by simpa using hs), hW,
    fun s => by rw [ofReal_zero, sub_zero]; exact hfe s, Or.inl fun s => hd.analyticAt s⟩

variable [IsTotallyComplex K]

/-- **The archimedean factor of weight $k$.** Let $K$ be imaginary quadratic, and let $|n_w| = k$ and $t_w = 0$ at the complex place $w$. Then $\Gamma_\infty(s) = 2^{1 - s} 2^{-k/2} \Gamma_\mathbb{R}(2s + k)$. -/
theorem gammaFactor_weight (hK : finrank ℚ K = 2) {k : ℕ} {n : InfinitePlace K → ℤ}
    {t : InfinitePlace K → ℂ} (hn : |n (quadPlace K hK).1| = (k : ℤ))
    (ht : t (quadPlace K hK).1 = 0) (s : ℂ) :
    gammaFactor K n t s = (2 : ℂ) ^ (1 - s) *
      ((2 : ℂ) ^ (-(k : ℂ) / 2) * Complex.Gammaℝ (2 * s + k)) := by
  rw [gammaFactor, Fintype.prod_eq_single (quadPlace K hK).1
      fun w hw => absurd (eq_quadPlace K hK w) hw,
    ite_eq_right (not_isReal_iff_isComplex.2 (quadPlace K hK).2), ht, hn, gammaℂ_eq_two_cpow_mul,
    show 1 - (s + 0 + ((k : ℤ) : ℂ) / 2) = (1 - s) + -(k : ℂ) / 2 by push_cast; ring,
    cpow_add _ _ two_ne_zero, show 2 * (s + 0 + ((k : ℤ) : ℂ) / 2) = 2 * s + k by push_cast; ring,
    mul_assoc]

/-- **Hecke's functional equation of weight $k$.** Let $K$ be imaginary quadratic and let $\chi$ be a unitary Hecke character that is ramified at one finite place, with the parameters $(k, 0)$ at the complex place, $k \neq 0$. Then the functional equation with entire functions holds for $\chi$, with $W = (-i)^k \tau_1(\chi) / \sqrt{N(\mathfrak{f})}$. -/
theorem entireFunctionalEquation_weight (hS : (ramifiedSet χ).Nonempty)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hK : finrank ℚ K = 2) {k : ℕ}
    (hk : k ≠ 0) {n n' : InfinitePlace K → ℤ} {t t' : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (hq : n (quadPlace K hK).1 = k) (ht : t (quadPlace K hK).1 = 0) :
    EntireFunctionalEquation χ n n' t t' := by
  have hnr : ¬ (quadPlace K hK).1.IsReal := not_isReal_iff_isComplex.2 (quadPlace K hK).2
  have h : χ.IsArchimedeanParameter (quadPlace K hK).1 (k : ℤ) 0 := by
    rw [← hq, ← ht]
    exact hn _
  obtain ⟨hq', ht'⟩ := eq_of_isArchimedeanParameter hnr (hn' (quadPlace K hK).1) h.inv
  rw [ite_eq_right hnr, neg_zero] at *
  have hg : |n (quadPlace K hK).1| = (k : ℤ) := by rw [hq, Nat.abs_cast]
  have hg' : |n' (quadPlace K hK).1| = (k : ℤ) := by rw [hq', abs_neg, Nat.abs_cast]
  have hc : (0 : ℝ) < Ideal.absNorm χ.conductor := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hτ : periodicGaussSum χ 1 ≠ 0 := fun h0 => by
    have h2 := norm_periodicGaussSum_sq hS hχ 1
    rw [h0, norm_zero, zero_pow two_ne_zero] at h2
    exact hc.ne' (by exact_mod_cast h2.symm)
  have hX : ((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.2 (abs_ne_zero.2 (discr_ne_zero K)))
      (Nat.cast_ne_zero.2 fun h0 => conductor_ne_zero χ (Ideal.absNorm_eq_zero_iff.1 h0))
  have hW : (-Complex.I) ^ k * periodicGaussSum χ 1 /
      ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) hτ)
      (ofReal_ne_zero.2 (Real.sqrt_pos.2 hc).ne')
  let Λ : ℂ → ℂ := fun z => (2 : ℂ) ^ (1 - z) * ((2 : ℂ) ^ (-(k : ℂ) / 2) *
    ∑ C : ClassGroup (𝓞 K), (torsionOrder K : ℂ)⁻¹ *
      ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ z *
        weightClassCompleted χ hK k (classIdeal K C) (2 * z + k))
  have hd : Differentiable ℂ Λ := by
    have hb : ∀ C : ClassGroup (𝓞 K),
        ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := fun C =>
      ofReal_ne_zero.2 (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 fun h0 =>
        nonZeroDivisors.coe_ne_zero _ (Ideal.absNorm_eq_zero_iff.1 h0)))
    refine ((differentiable_id.const_sub 1).const_cpow (Or.inl two_ne_zero)).mul
      ((differentiable_const _).mul (Differentiable.fun_sum fun C _ => ?_))
    exact ((differentiable_const _).mul (differentiable_id.const_cpow (Or.inl (hb C)))).mul
      ((differentiable_weightClassCompleted hK hk (classIdeal K C)).comp
        ((differentiable_id.const_mul 2).add_const _))
  let Λ' : ℂ → ℂ := fun z => ((-Complex.I) ^ k * periodicGaussSum χ 1 /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹ *
      (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - z) * Λ (1 - z)
  have hd' : Differentiable ℂ Λ' :=
    ((differentiable_const _).mul ((differentiable_id.const_sub _).const_cpow (Or.inl hX))).mul
      (hd.comp (differentiable_id.const_sub 1))
  refine ⟨Λ, Λ', (-Complex.I) ^ k * periodicGaussSum χ 1 /
    ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ), hd, hd', fun s hs => ?_, fun s hs => ?_, ?_,
    fun s => ?_⟩
  · rw [HeckeCharacter.completedLFunction, gammaFactor_weight hK hg ht, mul_assoc, mul_assoc,
      gammaℝ_mul_finiteLFunction_weight hS hχ hK h hs]
  · rw [HeckeCharacter.completedLFunction, gammaFactor_weight hK hg' ht',
      show (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (-(k : ℂ) / 2) * Complex.Gammaℝ (2 * s + k)) *
        χ⁻¹.finiteLFunction s = (2 : ℂ) ^ (-(k : ℂ) / 2) * ((2 : ℂ) ^ (1 - s) *
          Complex.Gammaℝ (2 * s + k) * χ⁻¹.finiteLFunction s) by ring,
      ← weight_dual_eq_completed hS hχ hK hk h hs]
    simp only [Λ', Λ]
    ring
  · have h2 := norm_periodicGaussSum_sq hS hχ 1
    rw [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← h2,
      Real.sqrt_sq (norm_nonneg _), div_self (norm_ne_zero_iff.2 hτ)]
  · simp only [Λ', sub_sub_cancel]
    calc Λ s = (((-Complex.I) ^ k * periodicGaussSum χ 1 /
          ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ)) * ((-Complex.I) ^ k *
            periodicGaussSum χ 1 / ((√(Ideal.absNorm χ.conductor : ℝ) : ℝ) : ℂ))⁻¹) *
        ((((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s) *
          (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - (1 - s))) *
            Λ s := by
          rw [mul_inv_cancel₀ hW, ← cpow_add _ _ hX, show 1 / 2 - s + (1 / 2 - (1 - s)) = 0 by ring,
            cpow_zero, one_mul, one_mul]
      _ = _ := by ring

/-- **Hecke's functional equation for ramified characters of weight $n \neq 0$ of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\xi$ be a Hecke character that is ramified at one finite place, with the archimedean parameters $(n, t)$, where $n \neq 0$ at the complex place. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. The function $\Lambda$ is entire. -/
theorem heckeFunctionalEquation_of_isQuadratic_of_weight (hK : finrank ℚ K = 2)
    (ξ : HeckeCharacter K) (hS : (ramifiedSet ξ).Nonempty)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, ξ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, ξ⁻¹.IsArchimedeanParameter v (n' v) (t' v))
    (h0 : n (quadPlace K hK).1 ≠ 0) :
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
  have hnr : ¬ (quadPlace K hK).1.IsReal := not_isReal_iff_isComplex.2 (quadPlace K hK).2
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℂ, t (quadPlace K hK).1 = t₀ := ⟨_, rfl⟩
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
  have hq0 : t (quadPlace K hK).1 - t₀ = 0 := by rw [ht₀, sub_self]
  have hp0 : ∀ w, χ.IsArchimedeanParameter w (n w) 0 := fun w => by
    rw [eq_quadPlace K hK w, ← hq0]
    exact hp _
  have hu := norm_ideleChar_of_norm_infiniteComponent
    (norm_infiniteComponent_of_isArchimedeanParameter hp0)
  have hSχ : (ramifiedSet χ).Nonempty := by
    obtain ⟨v, hv⟩ := hS
    exact ⟨v, mem_ramifiedSet.2 fun h => mem_ramifiedSet.1 hv ((isUnramifiedAt_twist_iff hξ v).2 h)⟩
  have hE : EntireFunctionalEquation χ n n' (fun v => t v - t₀) (fun v => t' v + t₀) := by
    rcases lt_or_gt_of_ne h0 with hlt | hgt
    · obtain ⟨hq', ht'⟩ := eq_of_isArchimedeanParameter hnr (hp' (quadPlace K hK).1)
        (hp (quadPlace K hK).1).inv
      rw [ite_eq_right hnr, hq0, neg_zero] at *
      have hpi : ∀ v, χ⁻¹⁻¹.IsArchimedeanParameter v (n v) (t v - t₀) := by
        rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
        exact hp
      refine EntireFunctionalEquation.of_inv (entireFunctionalEquation_weight
        (ramifiedSet_inv χ ▸ hSχ) (norm_ideleChar_inv hu) hK (k := (-n (quadPlace K hK).1).toNat)
        (by omega) hp' hpi (by rw [hq']; omega) ht')
    · exact entireFunctionalEquation_weight hSχ hu hK (k := (n (quadPlace K hK).1).toNat)
        (by omega) hp hp' (by omega) hq0
  exact heckeFunctionalEquation_of_twist hξ n n' t t' (hE.heckeFunctionalEquation hu)

/-- **Hecke's functional equation for ramified characters of an imaginary quadratic field.** Let $K$ be imaginary quadratic and let $\xi$ be a Hecke character that is ramified at one finite place, with the archimedean parameters $(n, t)$. Then the conclusion of `Langlands.HeckeFunctionalEquationAt` holds for $\xi$. The case $n = 0$ is `Langlands.Tate.heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent`, and the case $n \neq 0$ is `Langlands.Tate.heckeFunctionalEquation_of_isQuadratic_of_weight`. -/
theorem heckeFunctionalEquation_of_isQuadratic_of_ramified (hK : finrank ℚ K = 2)
    (ξ : HeckeCharacter K) (hS : (ramifiedSet ξ).Nonempty)
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
  by_cases h0 : n (quadPlace K hK).1 = 0
  · refine heckeFunctionalEquation_of_isQuadratic_of_infiniteComponent hK ξ
      (t (quadPlace K hK).1) (fun w y => ?_) n n' t t' hn hn'
    obtain rfl := eq_quadPlace K hK w
    rw [(hn _).eq y, h0, zpow_zero, one_mul]
  · exact heckeFunctionalEquation_of_isQuadratic_of_weight hK ξ hS n n' t t' hn hn' h0

end Assembly

end Langlands.Tate
