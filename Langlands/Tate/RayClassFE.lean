/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassQuadratic
import Langlands.Tate.QuadraticDedekind

/-!
# The partial L-functions of a ray class character of an imaginary quadratic field

Let $\chi$ be a Hecke character of ray class type of an imaginary quadratic field $K$, with conductor $\mathfrak{f}$, and suppose that $\chi$ is ramified at one place at least. Let $J$ be a nonzero integral ideal, and let $\varphi : K \to V$ be the Minkowski embedding of `Langlands.Tate.traceLattice`, with $|\varphi(\beta)|^2 = 2 |N(\beta)|$. This file writes the partial $L$-series of the class $[J]^{-1}$ as a finite combination of the shifted Epstein zeta functions $Z_{\varphi(\mathfrak{f} J)}(x, 0; 2u)$ over $x \in \varphi(J) / \varphi(\mathfrak{f} J)$, gives the functional equation of this combination, and writes the dual side as a Dirichlet series over the dual ideal $(\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$ with finite Gauss sums as coefficients.

## Main definitions

* `Langlands.Tate.rayCoeff`: the coefficient $c_J(\alpha)$, which is $\chi((\alpha) J^{-1})$ if $(\alpha) J^{-1}$ is prime to $\mathfrak{f}$ at each ramified place, and $0$ if not.
* `Langlands.Tate.rayLattice`: the lattice $\varphi(\mathfrak{f} J)$.
* `Langlands.Tate.rayLatticeCoeff`: the coefficient $c_J$ as a function on the lattice $\varphi(J)$.
* `Langlands.Tate.rayClassCompleted`: the completed partial $L$-function $\Lambda_J(s) = \sum_{x} c_J(x) \Lambda_{\varphi(\mathfrak{f} J)}(x, 0; s)$.
* `Langlands.Tate.rayGaussCoeff`: the Gauss sum $G_J(\beta) = \sum_{x} c_J(x) e^{2 \pi i \mathrm{Tr}(\beta \xi_x)}$.

## Main results

* `hasSum_residues`: a lattice sum with a coefficient that is periodic modulo a sublattice $M$ is a finite combination of the functions $Z_M(x, 0; s)$.
* `IsRayClassType.rayCoeff_eq_of_sub_mem`: the coefficient $c_J$ is periodic modulo $\mathfrak{f} J$.
* `rayCoeff_mul_cpow`: if $(\alpha) = J I$, then $c_J(\alpha) N(I)^{-s}$ is the weight $\chi(I) N(I)^{-s}$ of the $L$-series.
* `natCard_rayQuotient`: the quotient $\varphi(J) / \varphi(\mathfrak{f} J)$ has $N(\mathfrak{f})$ elements.
* `IsRayClassType.hasSum_partialLSeries`: for $\mathrm{Re}\, u > 1$, $\sum_{[I] = [J]^{-1}} \chi(I) N(I)^{-u} = w^{-1} (2 N(J))^u \sum_x c_J(x) Z_{\varphi(\mathfrak{f} J)}(x, 0; 2u)$.
* `IsRayClassType.hasSum_completed_partialLSeries`: the same identity with $\Gamma_\mathbb{R}(2u)$ and $\Lambda_J(2u)$.
* `IsRayClassType.gammaℝ_mul_finiteLFunction`: for $\mathrm{Re}\, u > 1$, $\Gamma_\mathbb{R}(2u) L(u, \chi) = w^{-1} \sum_C (2 N(J_C))^u \Lambda_{J_C}(2u)$.
* `rayClassCompleted_two_sub`: $\Lambda_J(2 - s) = \mathrm{covol}(\varphi(\mathfrak{f} J))^{-1} \sum_x c_J(x) \Lambda_{\varphi(\mathfrak{f} J)^\vee}(0, x; s)$, with the covolume $N(\mathfrak{f}) N(J) \sqrt{|d_K|}$ of `covolume_rayLattice`.
* `hasSum_completedShiftEpsteinZeta_dual`: the dual lattice function $\Lambda_{\varphi(\mathfrak{f} J)^\vee}(0, \varphi(\xi); s)$ is the series over $\beta \in (\mathfrak{f} J)^\vee$ of $\Gamma_\mathbb{R}(s) e^{2 \pi i \mathrm{Tr}(\beta \xi)} (2 |N(\beta)|)^{-s/2}$.
* `hasSum_rayClass_dual`: the dual side of the functional equation is $\sum_{\beta \in (\mathfrak{f} J)^\vee, \, \beta \neq 0} \Gamma_\mathbb{R}(s) G_J(\beta) (2 |N(\beta)|)^{-s/2}$.
* `IsRayClassType.differentiable_rayClassCompleted`: if $\sum_x c_J(x) = 0$, then $\Lambda_J$ is entire.

## Proofs

The nonzero elements of $J$ are sorted by the ideal $I$ with $(\alpha) = J I$, as in `Langlands.Tate.hasSum_quadraticTerm`. The coefficient $c_J$ is constant on each fibre by `rayCoeff_mul_cpow`. The periodicity of $c_J$ comes from the ultrametric inequality and `Langlands.Tate.IsRayClassType.idealChar_toPrincipalIdeal_eq`. This uses one ramified place, because it gives $\beta \neq 0$ for $\beta \equiv \alpha \bmod \mathfrak{f} J$. The lattice sum is then sorted by the classes of $\varphi(J) / \varphi(\mathfrak{f} J)$ with `HasSum.sigma`. The quotient is finite because the ratio of the covolumes is the index. The functional equation is `Langlands.Tate.completedShiftEpsteinZeta_sub` with $y = 0$. The dual lattice is identified with $(\mathfrak{f} J)^\vee$ by `Langlands.Tate.globalDualEquiv`, and the inner product is the trace by `Langlands.Tate.trace_eq_inner`. For the poles, $\Lambda_M(x, 0; s)$ is an entire function minus $c_M(x) / (s/2)$ minus $\mathrm{covol}(M)^{-1} / (1 - s/2)$. The first polar part vanishes because $c_J = 0$ on $\mathfrak{f} J$, and the second polar part has the coefficient $\sum_x c_J(x)$.

## Open parts

This file does not prove `Langlands.HeckeFunctionalEquationAt` for a Hecke character of ray class type of an imaginary quadratic field. These steps are still open. First, the vanishing $\sum_{x \in J / \mathfrak{f} J} c_J(x) = 0$, which is the hypothesis of `IsRayClassType.differentiable_rayClassCompleted`. It needs that the character of $(\mathcal{O}_K / \mathfrak{f})^\times$ induced by $\chi$ is not trivial, and this needs the comparison of $\chi$ on principal ideals with the local components of $\chi$ by strong approximation. Second, the evaluation of the Gauss sum $G_J(\beta) = \tau(\chi) \overline{\chi}((\beta) \mathfrak{f} J \mathfrak{d})$ for $\beta \in (\mathfrak{f} J)^\vee$, with $G_J(\beta) = 0$ if $(\beta) \mathfrak{f} J \mathfrak{d}$ is not prime to $\mathfrak{f}$, and the identity $|\tau(\chi)|^2 = N(\mathfrak{f})$ for a primitive $\chi$. Third, the assembly of the dual series into the partial $L$-series of $\chi^{-1}$, the sum over the classes, and the root number $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$, with the comparison of $\Gamma_\mathbb{R}(2u)$ with the gamma factor `Langlands.gammaFactor` and the archimedean parameters of $\chi$. The unramified case, where $\chi$ is a class group character, is not treated here.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open MeasureTheory Module Filter Topology Set Complex
open scoped RealInnerProductSpace Classical

namespace Langlands.Tate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Residues

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The sublattice $M$ as a subgroup of the lattice $L$. -/
noncomputable abbrev subLattice (L M : Submodule ℤ V) : AddSubgroup L :=
  M.toAddSubgroup.addSubgroupOf L.toAddSubgroup

/-- The points of a fibre of $L \to L / M$ are the translates of the points of $M$. -/
noncomputable def fiberEquiv (L M : Submodule ℤ V) (hML : M ≤ L) (q : L ⧸ subLattice L M) :
    {ℓ : L // (ℓ : L ⧸ subLattice L M) = q} ≃ M where
  toFun ℓ := ⟨((ℓ.1 - q.out : L) : V), by
    have h : ((q.out : L) : L ⧸ subLattice L M) = ℓ.1 := by
      rw [ℓ.2, QuotientAddGroup.out_eq']
    have h2 := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 h)
    have e : ℓ.1 - q.out = -q.out + ℓ.1 := by abel
    rw [e]
    exact h2⟩
  invFun μ := ⟨q.out + ⟨μ, hML μ.2⟩, by
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (⟨μ, hML μ.2⟩ : L)).2
      (AddSubgroup.mem_addSubgroupOf.2 μ.2), add_zero, QuotientAddGroup.out_eq']⟩
  left_inv ℓ := by ext; simp
  right_inv μ := by ext; simp

/-- **The sum over a lattice sorted by the classes modulo a sublattice.** Let $M \subseteq L$ be lattices with $L / M$ finite and let $c$ be a bounded function on $L$ that is periodic modulo $M$. For $\mathrm{Re}\, s > n$, $$\sum_{\ell \in L, \, \ell \neq 0} c(\ell) |\ell|^{-s} = \sum_{x \in L / M} c(x) Z_M(x, 0; s).$$ -/
theorem hasSum_residues (L M : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology M] [IsZLattice ℝ M] (hML : M ≤ L) [Fintype (L ⧸ subLattice L M)]
    (c : L → ℂ) (hc : ∀ (ℓ : L) (μ : M), c (ℓ + ⟨μ, hML μ.2⟩) = c ℓ) {B : ℝ}
    (hB : ∀ ℓ, ‖c ℓ‖ ≤ B) {s : ℂ} (hs : (finrank ℝ V : ℝ) < s.re) :
    HasSum (fun ℓ : L => c ℓ * if (ℓ : V) = 0 then 0 else ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s))
      (∑ q : L ⧸ subLattice L M, c q.out * shiftEpsteinZeta M (q.out : V) 0 s) := by
  set F : L → ℂ := fun ℓ => c ℓ * if (ℓ : V) = 0 then 0 else ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s)
    with hF
  have h0 : Summable fun ℓ : L =>
      if (ℓ : V) = 0 then (0 : ℂ) else ((‖(ℓ : V)‖ : ℝ) : ℂ) ^ (-s) := by
    refine (summable_shiftEpsteinZeta L 0 0 hs).congr fun ℓ => ?_
    simp
  have hsum : Summable F := by
    refine Summable.of_norm_bounded (h0.norm.mul_left B) fun ℓ => ?_
    rw [hF, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB ℓ) (norm_nonneg _)
  have hfib : ∀ q : L ⧸ subLattice L M,
      HasSum (fun ℓ : {ℓ : L // (ℓ : L ⧸ subLattice L M) = q} => F ℓ)
        (c q.out * shiftEpsteinZeta M (q.out : V) 0 s) := by
    intro q
    rw [← (fiberEquiv L M hML q).symm.hasSum_iff]
    have := ((summable_shiftEpsteinZeta M (q.out : V) 0 hs).hasSum).mul_left (c q.out)
    convert this using 1
    · have e : ∀ μ' : L, (q.out + μ' = 0) ↔ ((q.out : V) + (μ' : V) = 0) := fun μ' =>
        Subtype.ext_iff.trans (by rw [Submodule.coe_add, Submodule.coe_zero])
      funext μ
      simp [hF, fiberEquiv, hc]
      simp only [e]
    · simp [shiftEpsteinZeta]
  have h1 := ((Equiv.sigmaFiberEquiv (fun ℓ : L => (ℓ : L ⧸ subLattice L M))).hasSum_iff.2
    hsum.hasSum).sigma hfib
  have h2 := h1.unique (hasSum_fintype _)
  rw [← h2]
  exact hsum.hasSum

omit [Nontrivial V] in
/-- A sublattice of a lattice has finite index. -/
theorem finite_quotient_subLattice (L M : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology M] [IsZLattice ℝ M] (hML : M ≤ L) : Finite (L ⧸ subLattice L M) := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex' M L hML
  have hpos : 0 < ZLattice.covolume M / ZLattice.covolume L :=
    div_pos (ZLattice.covolume_pos M) (ZLattice.covolume_pos L)
  refine AddSubgroup.index_ne_zero_iff_finite.1 fun h0 => ?_
  change M.toAddSubgroup.relIndex L.toAddSubgroup = 0 at h0
  rw [h0, Nat.cast_zero] at h
  linarith

omit [Nontrivial V] in
/-- The number of classes of $L / M$ is $\mathrm{covol}(M) / \mathrm{covol}(L)$. -/
theorem natCard_quotient_subLattice (L M : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology M] [IsZLattice ℝ M] (hML : M ≤ L) :
    (Nat.card (L ⧸ subLattice L M) : ℝ) = ZLattice.covolume M / ZLattice.covolume L :=
  (ZLattice.covolume_div_covolume_eq_relIndex' M L hML).symm

end Residues

section Coefficient

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The conductor is a nonzero ideal. -/
theorem conductor_ne_zero (χ : HeckeCharacter K) : χ.conductor ≠ 0 := by
  rw [conductor_eq_prod]
  exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by
    rw [Submodule.zero_eq_bot]; exact v.ne_bot)

/-- The conductor as a fractional ideal is nonzero. -/
theorem coeIdeal_conductor_ne_zero (χ : HeckeCharacter K) :
    (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 (by rw [← Submodule.zero_eq_bot]; exact conductor_ne_zero χ)

/-- The exponent of $\mathfrak{p}_v$ in the conductor is at least $a_v$. -/
theorem le_count_conductor (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (χ.conductorExponent v : ℤ) ≤
      FractionalIdeal.count K v (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) := by
  have hd : v.asIdeal ^ χ.conductorExponent v ∣ χ.conductor := by
    by_cases hv : v ∈ ramifiedSet χ
    · rw [conductor_eq_prod]
      exact Finset.dvd_prod_of_mem _ hv
    · rw [(conductorExponent_eq_zero_iff χ v).2 (not_not.1 (mt mem_ramifiedSet.2 hv)), pow_zero]
      exact one_dvd _
  have hle : (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((v.asIdeal ^ χ.conductorExponent v : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).2 (Ideal.le_of_dvd hd)
  have h := FractionalIdeal.count_mono K v (coeIdeal_conductor_ne_zero χ) hle
  rwa [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at h

/-- For a nonzero ideal $I$, the exponent of $\mathfrak{p}_v$ in $I$ is $0$ if and only if $\mathfrak{p}_v \nmid I$. -/
theorem count_eq_zero_iff_not_dvd (v : HeightOneSpectrum (𝓞 K)) (I : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.count K v ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 ↔
      ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
  have hI := nonZeroDivisors.coe_ne_zero I
  rw [FractionalIdeal.count_coe K v hI, Nat.cast_eq_zero,
    ← Associates.count_ne_zero_iff_dvd hI v.irreducible, not_not]

/-- The coefficient of the partial $L$-series of the class of $J^{-1}$: for $\alpha \in K^\times$ with $v((\alpha)) = v(J)$ at each ramified place $v$, it is $\chi((\alpha) J^{-1})$, and it is $0$ for the other $\alpha$. -/
noncomputable def rayCoeff (χ : HeckeCharacter K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ℂ :=
  if h : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) then
    ((idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 α h.1)) * (idealChar χ J)⁻¹ : ℂˣ) : ℂ)
  else 0

/-- The coefficient has absolute value at most $1$. -/
theorem IsRayClassType.norm_rayCoeff_le (hχ : IsRayClassType χ)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) : ‖rayCoeff χ J α‖ ≤ 1 := by
  rw [rayCoeff]
  split_ifs
  · rw [Units.val_mul, norm_mul, hχ.norm_idealChar, Units.val_inv_eq_inv_val, norm_inv,
      hχ.norm_idealChar, inv_one, mul_one]
  · simp

/-- If $\alpha - \beta \in \mathfrak{f} J$, then $v(\alpha - \beta) \leq e^{-a_v} e^{-v(J)}$ at each finite place $v$. -/
theorem valuation_sub_le (χ : HeckeCharacter K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α β : K}
    (h : α - β ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K))
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (α - β) ≤ WithZero.exp (-(χ.conductorExponent v : ℤ)) *
      WithZero.exp (-FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := by
  by_cases h0 : α - β = 0
  · rw [h0, map_zero]
    exact zero_le
  have hmem := (FractionalIdeal.spanSingleton_le_iff_mem).2 h
  have hc := FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 h0) hmem
  rw [FractionalIdeal.count_mul K v (coeIdeal_conductor_ne_zero χ) J.ne_zero] at hc
  have h1 := valuation_eq_exp_neg_count v (Units.mk0 _ h0)
  rw [Units.val_mk0] at h1
  rw [h1, ← WithZero.exp_add, WithZero.exp_le_exp]
  have := le_count_conductor χ v
  omega

/-- If $\alpha$ satisfies the condition of `Langlands.Tate.rayCoeff` and $\alpha - \beta \in \mathfrak{f} J$, then $\beta$ satisfies it, and $\chi((\beta)) = \chi((\alpha))$. This needs one ramified place. -/
theorem IsRayClassType.rayCoeff_cond_of_sub_mem (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α β : K}
    (h : α - β ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K))
    (hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ hβ : β ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K),
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 β hβ.1)) =
        idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 α hα.1)) := by
  have hva : ∀ v ∈ ramifiedSet χ, v.valuation K α =
      WithZero.exp (-FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := fun v hv => by
    have h1 := valuation_eq_exp_neg_count v (Units.mk0 _ hα.1)
    rw [Units.val_mk0] at h1
    rw [h1, hα.2 v hv]
  have hlt : ∀ v ∈ ramifiedSet χ, v.valuation K (β - α) < v.valuation K α := fun v hv => by
    rw [Valuation.map_sub_swap, hva v hv]
    refine (valuation_sub_le χ J h v).trans_lt ?_
    have ha : χ.conductorExponent v ≠ 0 :=
      fun h0 => mem_ramifiedSet.1 hv ((conductorExponent_eq_zero_iff χ v).1 h0)
    rw [← WithZero.exp_add, WithZero.exp_lt_exp]
    omega
  have hvβ : ∀ v ∈ ramifiedSet χ, v.valuation K β = v.valuation K α := fun v hv => by
    have := Valuation.map_add_eq_of_lt_left _ (hlt v hv)
    rwa [add_sub_cancel] at this
  obtain ⟨v₀, hv₀⟩ := hS
  have hβ0 : β ≠ 0 := fun h0 => by
    have := hvβ v₀ hv₀
    rw [h0, map_zero, hva v₀ hv₀] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨⟨hβ0, fun v hv' => ?_⟩, ?_⟩
  · have h1 := valuation_eq_exp_neg_count v (Units.mk0 _ hβ0)
    rw [Units.val_mk0, hvβ v hv', hva v hv'] at h1
    exact neg_injective (WithZero.exp_injective h1).symm
  · refine hχ.idealChar_toPrincipalIdeal_eq _ _ fun v hv' => ?_
    rw [Units.val_mk0, Units.val_mk0, Valuation.map_sub_swap, hva v hv', ← hα.2 v hv']
    have := valuation_sub_le χ J h v
    rwa [← hα.2 v hv'] at this

/-- **Periodicity of the coefficient.** If $\chi$ is ramified at one place and $\alpha - \beta \in \mathfrak{f} J$, then the coefficients of $\alpha$ and $\beta$ are equal. -/
theorem IsRayClassType.rayCoeff_eq_of_sub_mem (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α β : K}
    (h : α - β ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) :
    rayCoeff χ J α = rayCoeff χ J β := by
  have h' : β - α ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← neg_sub]
    exact Submodule.neg_mem _ h
  by_cases hα : α ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · obtain ⟨hβ, he⟩ := hχ.rayCoeff_cond_of_sub_mem hS J h hα
    rw [rayCoeff, rayCoeff, dite_eq_left hα, dite_eq_left hβ, he]
  · by_cases hβ : β ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ β) =
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
    · exact absurd (hχ.rayCoeff_cond_of_sub_mem hS J h' hβ).1 hα
    · rw [rayCoeff, rayCoeff, dite_eq_right hα, dite_eq_right hβ]

/-- If $\chi$ is ramified at one place, the coefficient is $0$ on $\mathfrak{f} J$. -/
theorem IsRayClassType.rayCoeff_eq_zero_of_mem (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {α : K}
    (h : α ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) :
    rayCoeff χ J α = 0 := by
  rw [hχ.rayCoeff_eq_of_sub_mem hS J (β := 0) (by rwa [sub_zero]), rayCoeff, dite_eq_right]
  exact fun h0 => h0.1 rfl

/-- **The coefficient and the weight of the $L$-series.** If $(\alpha) = J I$ for nonzero integral ideals $J$ and $I$, then the coefficient of $\alpha$ times $N(I)^{-s}$ is $\chi(I) N(I)^{-s}$, with $\chi(I) = 0$ for $I$ not prime to the conductor. -/
theorem rayCoeff_mul_cpow (J I : (Ideal (𝓞 K))⁰) {α : 𝓞 K}
    (h : Ideal.span {α} = (J : Ideal (𝓞 K)) * I) (s : ℂ) :
    rayCoeff χ (FractionalIdeal.mk0 K J) (α : K) * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      rayWeight χ s I := by
  have hα : (α : K) ≠ 0 := by exact_mod_cast ne_zero_of_span_eq_mul K J I h
  have hJ0 : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero J)
  have hI0 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by rw [← Submodule.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero I)
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) =
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdeal_mul, ← h, FractionalIdeal.coeIdeal_span_singleton]
  have hprin : toPrincipalIdeal (𝓞 K) K (Units.mk0 (α : K) hα) =
      FractionalIdeal.mk0 K J * FractionalIdeal.mk0 K I := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
      Units.val_mk0]
    exact hspan
  have hiff : (∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K)) =
        FractionalIdeal.count K v ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K)) ↔
      ∀ v ∈ ramifiedSet χ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    refine forall₂_congr fun v _ => ?_
    rw [FractionalIdeal.coe_mk0, hspan, FractionalIdeal.count_mul K v hJ0 hI0,
      ← count_eq_zero_iff_not_dvd]
    omega
  rw [rayWeight_apply, rayCoeff]
  by_cases hc : ∀ v ∈ ramifiedSet χ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K))
  · rw [dite_eq_left ⟨hα, hiff.2 hc⟩, ite_eq_left hc, hprin, map_mul,
      mul_comm (idealChar χ (FractionalIdeal.mk0 K J)), mul_inv_cancel_right, one_mul]
  · rw [dite_eq_right (fun h' => hc (hiff.1 h'.2)), ite_eq_right hc]
    simp

end Coefficient

section Partial

open NumberField IsDedekindDomain InfinitePlace NumberField.mixedEmbedding NumberField.Units
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The conductor $\mathfrak{f}$ as a nonzero ideal. -/
noncomputable def conductorNZ (χ : HeckeCharacter K) : (Ideal (𝓞 K))⁰ :=
  ⟨χ.conductor, mem_nonZeroDivisors_of_ne_zero (conductor_ne_zero χ)⟩

/-- The lattice $\varphi(\mathfrak{f} J)$ of the ideal $\mathfrak{f} J$ in the euclidean mixed space. -/
noncomputable abbrev rayLattice (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  traceLattice K (FractionalIdeal.mk0 K (conductorNZ χ * J))

/-- An element of the ideal $\mathfrak{f} J$ is an element of the product of fractional ideals $\mathfrak{f} \cdot J$. -/
theorem mem_conductor_mul_of_mem (J : (Ideal (𝓞 K))⁰) {γ : K}
    (h : γ ∈ ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) :
    γ ∈ (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) *
      ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.coe_mk0, Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul] at h
  rw [FractionalIdeal.coe_mk0]
  exact h

/-- An element of the ideal $\mathfrak{f} J$ is an element of $J$. -/
theorem mem_of_mem_conductor_mul (J : (Ideal (𝓞 K))⁰) {γ : K}
    (h : γ ∈ ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) :
    γ ∈ ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hle : ((conductorNZ χ * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤ (J : Ideal (𝓞 K)) := by
    rw [Submonoid.coe_mul]
    exact Ideal.mul_le_right
  rw [FractionalIdeal.coe_mk0] at h ⊢
  exact (FractionalIdeal.coeIdeal_le_coeIdeal K).2 hle h

/-- The lattice of $\mathfrak{f} J$ is a sublattice of the lattice of $J$. -/
theorem rayLattice_le (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    rayLattice χ J ≤ traceLattice K (FractionalIdeal.mk0 K J) := by
  intro y hy
  obtain ⟨α, hα, rfl⟩ := (mem_globalLattice K _ _).1 hy
  exact globalEmbedding_mem K _ _ (mem_of_mem_conductor_mul J hα)

/-- The quotient $\varphi(J) / \varphi(\mathfrak{f} J)$ is finite. -/
noncomputable instance (J : (Ideal (𝓞 K))⁰) :
    Fintype (traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)) :=
  have := finite_quotient_subLattice _ _ (rayLattice_le χ J)
  Fintype.ofFinite _

/-- The coefficient `Langlands.Tate.rayCoeff` as a function on the lattice $\varphi(J)$. -/
noncomputable def rayLatticeCoeff (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) : ℂ :=
  rayCoeff χ (FractionalIdeal.mk0 K J)
    ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K)

/-- The coefficient on the lattice $\varphi(J)$ is periodic modulo $\varphi(\mathfrak{f} J)$, if $\chi$ is ramified at one place. -/
theorem IsRayClassType.rayLatticeCoeff_add (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) (μ : rayLattice χ J) :
    rayLatticeCoeff χ J (ℓ + ⟨μ, rayLattice_le χ J μ.2⟩) = rayLatticeCoeff χ J ℓ := by
  obtain ⟨γ, hγ, hμ⟩ := (mem_globalLattice K _ _).1 μ.2
  set e := globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J) with he
  have hγ' := mem_of_mem_conductor_mul J hγ
  have hs : e.symm (ℓ + ⟨μ, rayLattice_le χ J μ.2⟩) = ⟨((e.symm ℓ : _) : K) + γ,
      add_mem (e.symm ℓ).2 hγ'⟩ := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [he, coe_globalLatticeEquiv, map_add, hμ]
    change (ℓ : euclidean.mixedSpace K) + μ = _ + μ
    congr 1
    rw [← coe_globalLatticeEquiv, ← he]
    congr 1
    exact (e.apply_symm_apply ℓ).symm
  rw [rayLatticeCoeff, rayLatticeCoeff, ← he, hs]
  refine hχ.rayCoeff_eq_of_sub_mem hS _ ?_
  rw [add_sub_cancel_left]
  exact mem_conductor_mul_of_mem J hγ

variable [IsTotallyComplex K]

/-- **The series over $J$ as a sum over the classes of $J / \mathfrak{f} J$.** If $\chi$ is ramified at one place, then for $\mathrm{Re}\, s > 2$, $$\sum_{\beta \in J, \, \beta \neq 0} c(\beta) (2 |N(\beta)|)^{-s/2} = \sum_{x \in \varphi(J) / \varphi(\mathfrak{f} J)} c(x) Z_{\varphi(\mathfrak{f} J)}(x, 0; s),$$ where $c$ is the coefficient `Langlands.Tate.rayCoeff`. -/
theorem IsRayClassType.hasSum_rayCoeff_residues (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰)
    {s : ℂ} (hs : 2 < s.re) :
    HasSum (fun β : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) =>
      rayCoeff χ (FractionalIdeal.mk0 K J) β * if (β : K) = 0 then (0 : ℂ) else
        ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s))
      (∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
          subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out *
          shiftEpsteinZeta (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0 s) := by
  have hs' : (finrank ℝ (euclidean.mixedSpace K) : ℝ) < s.re := by
    rw [finrank_euclidean_mixedSpace, hK]
    exact_mod_cast hs
  have h := hasSum_residues _ _ (rayLattice_le χ J) (rayLatticeCoeff χ J)
    (hχ.rayLatticeCoeff_add hS J) (B := 1) (fun ℓ => hχ.norm_rayCoeff_le _ _) hs'
  rw [← (globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).hasSum_iff] at h
  refine h.congr_fun fun β => ?_
  have h0 : (globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J) β :
      euclidean.mixedSpace K) = 0 ↔ (β : K) = 0 := by
    rw [coe_globalLatticeEquiv]
    constructor
    · intro h
      exact globalEmbedding_injective K (traceScale K) (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  simp only [Function.comp_apply, h0, rayLatticeCoeff, Equiv.symm_apply_apply]
  split_ifs
  · rfl
  · rw [← sum_mult_sq_eq_of_isQuadratic K hK, coe_globalLatticeEquiv,
      ← norm_globalEmbedding_traceScale_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **The series over $J$ sorted by ideals.** For $\mathrm{Re}\, u > 1$, the series $\sum_{\beta \in J, \, \beta \neq 0} c(\beta) (2 |N(\beta)|)^{-u}$ is the sum over the integral ideals $I$ of the class $[J]^{-1}$ of $w (2 N(J))^{-u} \chi(I) N(I)^{-u}$. -/
theorem IsRayClassType.hasSum_rayCoeff_ideals (hχ : IsRayClassType χ) (hK : finrank ℚ K = 2)
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
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ.norm_rayCoeff_le _ _)
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

/-- **The partial $L$-series of an ideal class.** Let $\chi$ be a Hecke character of ray class type of an imaginary quadratic field $K$, ramified at one place, and let $J$ be a nonzero integral ideal. For $\mathrm{Re}\, u > 1$, $$\sum_{[I] = [J]^{-1}} \chi(I) N(I)^{-u} = \frac{(2 N(J))^u}{w} \sum_{x \in \varphi(J) / \varphi(\mathfrak{f} J)} c(x) Z_{\varphi(\mathfrak{f} J)}(x, 0; 2u),$$ where $w$ is the number of roots of unity and $c$ is the coefficient `Langlands.Tate.rayLatticeCoeff`. -/
theorem IsRayClassType.hasSum_partialLSeries (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰)
    {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then rayWeight χ u I else 0)
      ((torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
            subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
          rayLatticeCoeff χ J q.out *
            shiftEpsteinZeta (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0 (2 * u)) := by
  have h1 := hχ.hasSum_rayCoeff_ideals hK J hu
  rw [(hχ.hasSum_rayCoeff_residues hS hK J (two_lt_re_two_mul hu)).tsum_eq] at h1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos K).ne'
  have hN : (0 : ℝ) < 2 * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    have : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := Nat.cast_pos.2 (Nat.pos_of_ne_zero
      fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
    positivity
  have hA : ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hN.ne'))
  have h2 := h1.mul_left ((torsionOrder K : ℂ)⁻¹ *
    ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u)
  refine h2.congr_fun fun I => ?_
  rw [Complex.cpow_neg]
  split_ifs
  · field_simp
  · ring

end Partial

section Dual

open NumberField IsDedekindDomain InfinitePlace NumberField.mixedEmbedding NumberField.Units
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The number of classes of $\varphi(J) / \varphi(\mathfrak{f} J)$ is $N(\mathfrak{f})$. -/
theorem natCard_rayQuotient (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    Nat.card (traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)) =
        Ideal.absNorm χ.conductor := by
  have h := natCard_quotient_subLattice _ _ (rayLattice_le χ J)
  have hN : ∀ I : (Ideal (𝓞 K))⁰, (FractionalIdeal.absNorm
      ((FractionalIdeal.mk0 K I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := fun I => by
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [covolume_traceLattice, covolume_traceLattice, hN, hN, Submonoid.coe_mul, map_mul] at h
  have hJ : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 K)) := Nat.cast_pos.2 (Nat.pos_of_ne_zero
    fun h0 => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd := sqrt_abs_discr_pos K
  have : (Nat.card (traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)) : ℝ) =
        (Ideal.absNorm χ.conductor : ℝ) := by
    rw [h]
    push_cast
    field_simp
    rfl
  exact_mod_cast this

/-- The covolume of the lattice of $\mathfrak{f} J$ is $N(\mathfrak{f}) N(J) \sqrt{|d_K|}$. -/
theorem covolume_rayLattice (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (rayLattice χ J) = (Ideal.absNorm χ.conductor : ℝ) *
      Ideal.absNorm (J : Ideal (𝓞 K)) * √|(discr K : ℝ)| := by
  rw [covolume_traceLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    Submonoid.coe_mul, map_mul]
  push_cast
  rfl

/-- If the point $\ell$ of $\varphi(J)$ is in $\varphi(\mathfrak{f} J)$, then its coefficient is $0$. -/
theorem IsRayClassType.rayLatticeCoeff_eq_zero (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J))
    (h : (ℓ : euclidean.mixedSpace K) ∈ rayLattice χ J) : rayLatticeCoeff χ J ℓ = 0 := by
  obtain ⟨γ, hγ, hγℓ⟩ := (mem_globalLattice K _ _).1 h
  have he : (((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : _) : K) =
      γ := globalEmbedding_injective K (traceScale K) (by
    rw [hγℓ, ← coe_globalLatticeEquiv, Equiv.apply_symm_apply])
  rw [rayLatticeCoeff, he]
  exact hχ.rayCoeff_eq_zero_of_mem hS _ (mem_conductor_mul_of_mem J hγ)

/-- The completed partial $L$-function of the class $[J]^{-1}$: $$\Lambda_J(s) = \sum_{x \in \varphi(J) / \varphi(\mathfrak{f} J)} c(x) \Lambda_{\varphi(\mathfrak{f} J)}(x, 0; s).$$ For $\mathrm{Re}\, u > 1$, $\Lambda_J(2u)$ is $w (2 N(J))^{-u} \Gamma_\mathbb{R}(2u)$ times the partial $L$-series of the class $[J]^{-1}$. -/
noncomputable def rayClassCompleted (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
    rayLatticeCoeff χ J q.out *
      completedShiftEpsteinZeta (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0 s

/-- The point $\varphi(\xi_x)$ of a class representative, with $\xi_x \in J$. -/
theorem coe_out_eq_globalEmbedding (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    (ℓ : euclidean.mixedSpace K) = globalEmbedding K (fun w => (traceScale K w : ℝ))
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K) := by
  rw [← coe_globalLatticeEquiv, Equiv.apply_symm_apply]

/-- **The functional equation of the completed partial $L$-function.** For a field of degree $2$, $$\Lambda_J(2 - s) = \mathrm{covol}(\varphi(\mathfrak{f} J))^{-1} \sum_{x} c(x) \Lambda_{\varphi(\mathfrak{f} J)^\vee}(0, x; s),$$ and $\mathrm{covol}(\varphi(\mathfrak{f} J)) = N(\mathfrak{f}) N(J) \sqrt{|d_K|}$ by `Langlands.Tate.covolume_rayLattice`. -/
theorem rayClassCompleted_two_sub (hK : finrank ℚ K = 2) (χ : HeckeCharacter K)
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    rayClassCompleted χ J (2 - s) = ((ZLattice.covolume (rayLattice χ J))⁻¹ : ℝ) *
      ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
          subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out * completedShiftEpsteinZeta (dualLattice (rayLattice χ J)) 0
          (q.out : euclidean.mixedSpace K) s := by
  have h2 : (2 : ℂ) - s = (finrank ℝ (euclidean.mixedSpace K) : ℂ) - s := by
    rw [finrank_euclidean_mixedSpace, hK]
    norm_num
  rw [rayClassCompleted, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h2, completedShiftEpsteinZeta_sub, inner_zero_right, neg_zero]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  ring

variable [IsTotallyComplex K]

/-- **The completed partial $L$-series.** Let $\chi$ be ramified at one place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u) \sum_{[I] = [J]^{-1}} \chi(I) N(I)^{-u} = \frac{(2 N(J))^u}{w} \Lambda_J(2u).$$ -/
theorem IsRayClassType.hasSum_completed_partialLSeries (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : finrank ℚ K = 2) (J : (Ideal (𝓞 K))⁰)
    {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ =>
      if ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ then Complex.Gammaℝ (2 * u) * rayWeight χ u I
        else 0)
      ((torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        rayClassCompleted χ J (2 * u)) := by
  have hs' : (finrank ℝ (euclidean.mixedSpace K) : ℝ) < (2 * u).re := by
    rw [finrank_euclidean_mixedSpace, hK]
    exact_mod_cast two_lt_re_two_mul hu
  have h := (hχ.hasSum_partialLSeries hS hK J hu).mul_left (Complex.Gammaℝ (2 * u))
  have e : rayClassCompleted χ J (2 * u) = Complex.Gammaℝ (2 * u) *
      ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
          subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out *
          shiftEpsteinZeta (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0 (2 * u) := by
    rw [rayClassCompleted, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [completedShiftEpsteinZeta_eq _ _ _ hs']
    ring
  rw [e]
  convert h using 1
  · funext I
    split_ifs <;> simp
  · ring

/-- **The $L$-series as a sum over the ideal classes.** Let $\chi$ be a Hecke character of ray class type of an imaginary quadratic field, ramified at one place. For $\mathrm{Re}\, u > 1$, $$\Gamma_\mathbb{R}(2u) L(u, \chi) = \frac{1}{w} \sum_{C} (2 N(J_C))^u \Lambda_{J_C}(2u),$$ where $J_C$ is an integral ideal of the class $C$. -/
theorem IsRayClassType.gammaℝ_mul_finiteLFunction (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (hK : finrank ℚ K = 2) {u : ℂ} (hu : 1 < u.re) :
    Complex.Gammaℝ (2 * u) * χ.finiteLFunction u = ∑ C : ClassGroup (𝓞 K),
      (torsionOrder K : ℂ)⁻¹ * ((2 * Ideal.absNorm (classIdeal K C : Ideal (𝓞 K)) : ℝ) : ℂ) ^ u *
        rayClassCompleted χ (classIdeal K C) (2 * u) := by
  have hu' : 1 < u.re := hu
  have h := hasSum_sum (fun C (_ : C ∈ Finset.univ) =>
    hχ.hasSum_completed_partialLSeries hS hK (classIdeal K C) hu)
  rw [hχ.finiteLFunction_eq hu', ← tsum_mul_left]
  refine (h.congr_fun fun I => ?_).tsum_eq
  have key : ∀ C : ClassGroup (𝓞 K),
      (ClassGroup.mk0 I = (ClassGroup.mk0 (classIdeal K C))⁻¹) ↔ ((ClassGroup.mk0 I)⁻¹ = C) :=
    fun C => by
      rw [mk0_classIdeal]
      exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [← h, inv_inv]⟩
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- **The dual Dirichlet series.** For $\xi \in K$ and $\mathrm{Re}\, s > 2$, $$\Lambda_{\varphi(\mathfrak{f} J)^\vee}(0, \varphi(\xi); s) = \sum_{\beta \in (\mathfrak{f} J)^\vee, \, \beta \neq 0} \Gamma_\mathbb{R}(s) e^{2 \pi i \mathrm{Tr}(\beta \xi)} (2 |N(\beta)|)^{-s/2},$$ where $(\mathfrak{f} J)^\vee = (\mathfrak{f} J \mathfrak{d})^{-1}$ is the dual for the trace form. -/
theorem hasSum_completedShiftEpsteinZeta_dual (hK : finrank ℚ K = 2) (χ : HeckeCharacter K)
    (J : (Ideal (𝓞 K))⁰) (ξ : K) {s : ℂ} (hs : 2 < s.re) :
    HasSum (fun β : FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) =>
      if (β : K) = 0 then (0 : ℂ) else Complex.Gammaℝ s *
        (cexp (2 * Real.pi * I * ((Algebra.trace ℚ K ((β : K) * ξ) : ℚ) : ℝ)) *
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)))
      (completedShiftEpsteinZeta (dualLattice (rayLattice χ J)) 0
        (globalEmbedding K (fun w => (traceScale K w : ℝ)) ξ) s) := by
  have hs' : (finrank ℝ (euclidean.mixedSpace K) : ℝ) < s.re := by
    rw [finrank_euclidean_mixedSpace, hK]
    exact_mod_cast hs
  have h := hasSum_completedShiftEpsteinZeta (dualLattice (rayLattice χ J)) 0
    (globalEmbedding K (fun w => (traceScale K w : ℝ)) ξ) hs'
  rw [← (globalDualEquiv K (traceScale K) _ (traceScale K)
    (traceScale_mul_traceScale K)).hasSum_iff] at h
  refine h.congr_fun fun β => ?_
  have h0 : globalConjEmbedding K (fun w => (traceScale K w : ℝ)) (β : K) = 0 ↔ (β : K) = 0 := by
    constructor
    · intro h
      exact globalConjEmbedding_injective K (traceScale K) (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  simp only [Function.comp_apply, zero_add, coe_globalDualEquiv, h0]
  split_ifs
  · rfl
  · rw [trace_eq_inner K _ _ (traceScale_mul_traceScale K), ← sum_mult_sq_eq_of_isQuadratic K hK,
      ← norm_globalConjEmbedding_traceScale_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The coefficient of the dual series: $$G_J(\beta) = \sum_{x \in J / \mathfrak{f} J} c(x) e^{2 \pi i \mathrm{Tr}(\beta \xi_x)},$$ where $\xi_x \in J$ is the representative of the class $x$. It is a finite Gauss sum. -/
noncomputable def rayGaussCoeff (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰) (β : K) : ℂ :=
  ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
    rayLatticeCoeff χ J q.out * cexp (2 * Real.pi * I *
      ((Algebra.trace ℚ K (β *
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm q.out : K)) : ℚ) :
          ℝ))

/-- **The dual side of the functional equation as a Dirichlet series.** For $\mathrm{Re}\, s > 2$, $$\sum_x c(x) \Lambda_{\varphi(\mathfrak{f} J)^\vee}(0, x; s) = \sum_{\beta \in (\mathfrak{f} J)^\vee, \, \beta \neq 0} \Gamma_\mathbb{R}(s) \, G_J(\beta) \, (2 |N(\beta)|)^{-s/2}.$$ -/
theorem hasSum_rayClass_dual (hK : finrank ℚ K = 2) (χ : HeckeCharacter K)
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 2 < s.re) :
    HasSum (fun β : FractionalIdeal.dual ℤ ℚ
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) =>
      if (β : K) = 0 then (0 : ℂ) else Complex.Gammaℝ s * (rayGaussCoeff χ J β *
          ((√(2 * |(Algebra.norm ℚ (β : K) : ℝ)|) : ℝ) : ℂ) ^ (-s)))
      (∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
          subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out * completedShiftEpsteinZeta (dualLattice (rayLattice χ J)) 0
          (q.out : euclidean.mixedSpace K) s) := by
  have h := hasSum_sum (fun (q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J))
      (_ : q ∈ Finset.univ) => (hasSum_completedShiftEpsteinZeta_dual hK χ J
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm q.out : K)
      hs).mul_left (rayLatticeCoeff χ J q.out))
  simp only [← coe_out_eq_globalEmbedding] at h
  refine h.congr_fun fun β => ?_
  split_ifs
  · simp
  · rw [rayGaussCoeff, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

omit [IsTotallyComplex K] in
/-- The completed shifted Epstein zeta function as the sum of its entire part and of its polar parts, for the shift $y = 0$. -/
theorem completedShiftEpsteinZeta_zero_eq (χ : HeckeCharacter K) (J : (Ideal (𝓞 K))⁰)
    (x : euclidean.mixedSpace K) (s : ℂ) :
    completedShiftEpsteinZeta (rayLattice χ J) x 0 s =
      (shiftThetaFEPair (rayLattice χ J) x 0).Λ₀ (s / 2) -
        (1 / (s / 2)) * shiftConst (rayLattice χ J) x -
        ((ZLattice.covolume (rayLattice χ J))⁻¹ : ℝ) /
          ((finrank ℝ (euclidean.mixedSpace K) : ℂ) / 2 - s / 2) := by
  rw [completedShiftEpsteinZeta, WeakFEPair.Λ, smul_eq_mul, smul_eq_mul]
  simp [shiftThetaFEPair, shiftConst, zero_mem]

omit [IsTotallyComplex K] in
/-- **The completed partial $L$-function is entire if the coefficients have sum $0$.** Let $\chi$ be ramified at one place. If $\sum_{x \in J / \mathfrak{f} J} c(x) = 0$, then $\Lambda_J$ is an entire function. -/
theorem IsRayClassType.differentiable_rayClassCompleted (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰)
    (h0 : ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out = 0) :
    Differentiable ℂ (rayClassCompleted χ J) := by
  have key : rayClassCompleted χ J = fun s => ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out *
          (shiftThetaFEPair (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0).Λ₀ (s / 2) := by
    funext s
    have hq : ∀ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
        subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out * shiftConst (rayLattice χ J) (q.out : euclidean.mixedSpace K) =
          0 := fun q => by
      rw [shiftConst]
      split_ifs with h
      · rw [hχ.rayLatticeCoeff_eq_zero hS J _ h, zero_mul]
      · rw [mul_zero]
    have e : ∀ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
        subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out *
          completedShiftEpsteinZeta (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0 s =
        rayLatticeCoeff χ J q.out *
          (shiftThetaFEPair (rayLattice χ J) (q.out : euclidean.mixedSpace K) 0).Λ₀ (s / 2) -
        rayLatticeCoeff χ J q.out * (((ZLattice.covolume (rayLattice χ J))⁻¹ : ℝ) /
          ((finrank ℝ (euclidean.mixedSpace K) : ℂ) / 2 - s / 2)) := fun q => by
      rw [completedShiftEpsteinZeta_zero_eq]
      linear_combination (-(1 / (s / 2))) * hq q
    rw [rayClassCompleted, Finset.sum_congr rfl fun q _ => e q, Finset.sum_sub_distrib,
      ← Finset.sum_mul, h0, zero_mul, sub_zero]
  rw [key]
  exact Differentiable.fun_sum fun q _ => (((shiftThetaFEPair _ _ _).differentiable_Λ₀.comp
    (differentiable_id.div_const 2)).const_mul _)

end Dual

end Langlands.Tate
