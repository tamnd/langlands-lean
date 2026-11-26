/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.RayClassFE

/-!
# The vanishing of the coefficient sum and the twist of the Gauss sum for a ray class character

Let $\chi$ be a Hecke character of ray class type of a number field $K$, with conductor $\mathfrak{f}$, and suppose that $\chi$ is ramified at one place at least. Let $J$ be a nonzero integral ideal. This file proves that the coefficients $c_J$ of `Langlands.Tate.rayLatticeCoeff` have sum $0$ over $\varphi(J) / \varphi(\mathfrak{f} J)$. Thus the completed partial $L$-function $\Lambda_J$ of `Langlands.Tate.rayClassCompleted` is entire with no extra hypothesis. The file also proves the twist relation $G_J(\beta) = \chi((u)) G_J(u \beta)$ of the Gauss sum `Langlands.Tate.rayGaussCoeff`.

## Main definitions

* `Langlands.Tate.rayMulMap`: the multiplication by $u \in \mathcal{O}_K$ on the lattice $\varphi(J)$.

## Main results

* `finiteComponent_eq_of_valued_sub_le`: at a ramified place $v$, $\chi_v(z) = \chi_v(y)$ if $|y|_v = 1$ and $v(z - y) \geq a_v$.
* `IsRayClassType.idealChar_mul_prod_finiteComponent`: for $x \in K^\times$ prime to the ramified places, $\chi((x)) \prod_{v \mid \mathfrak{f}} \chi_v(x) = 1$.
* `exists_integer_approx`: an integer of $K$ that is near to a given point of $\mathcal{O}_{v_0}$ and near to $1$ at a finite set of other places.
* `IsRayClassType.exists_idealChar_ne_one`: there is an integer $u$, prime to the ramified places, with $\chi((u)) \neq 1$. So the character of $(\mathcal{O}_K / \mathfrak{f})^\times$ induced by $\chi$ is not trivial.
* `sum_out_map_eq`: a sum over a finite quotient $G / H$ is invariant under an endomorphism $T$ of $G$ with $T^{-1}(H) = H$.
* `sum_out_eq_zero_of_map`: if moreover $c(T g) = z c(g)$ with $z \neq 1$, then $\sum_{q \in G / H} c(q) = 0$.
* `mem_of_coe_mul_mem`: if $u$ is prime to the ramified places, $\xi \in J$ and $u \xi \in \mathfrak{f} J$, then $\xi \in \mathfrak{f} J$.
* `rayCoeff_coe_mul`: if $u$ is prime to the ramified places, then $c_J(u \xi) = \chi((u)) c_J(\xi)$.
* `IsRayClassType.sum_rayLatticeCoeff_eq_zero`: $\sum_{x \in \varphi(J) / \varphi(\mathfrak{f} J)} c_J(x) = 0$.
* `IsRayClassType.differentiable_rayClassCompleted_of_nonempty`: $\Lambda_J$ is an entire function.
* `IsRayClassType.rayGaussCoeff_eq_mul`: for $\beta \in (\mathfrak{f} J)^\vee$ and $u$ prime to the ramified places, $G_J(\beta) = \chi((u)) G_J(u \beta)$.

## Proofs

For $x \in K^\times$, the idele character is trivial on the principal idele of $x$. If $x$ is prime to the ramified places, the unramified components give $\chi((x))$, and the archimedean components are trivial because $\chi$ is of ray class type. Let $v_0$ be a ramified place. Then $\chi_{v_0}$ is not trivial on the units $y$ of $K_{v_0}$, because $a_{v_0} \neq 0$. The density of $K$ in $K_{v_0}$ and the Chinese remainder theorem give an integer $u$ with $u \equiv y \bmod \mathfrak{p}_{v_0}^{a_{v_0}}$ and $u \equiv 1 \bmod \mathfrak{p}_w^{a_w}$ for the other ramified places $w$. The formula above then gives $\chi((u)) = \chi_{v_0}(y)^{-1} \neq 1$. The multiplication by $u$ is a bijection of $\varphi(J) / \varphi(\mathfrak{f} J)$, because $(u)$ is prime to $\mathfrak{f}$. It multiplies $c_J$ by $\chi((u))$. So the sum $S$ of the coefficients satisfies $S = \chi((u)) S$, and $S = 0$. The same bijection gives the twist of the Gauss sum, because $e^{2 \pi i \mathrm{Tr}(\beta \xi)}$ is periodic modulo $\mathfrak{f} J$ for $\beta \in (\mathfrak{f} J)^\vee$.

## Open parts

These steps are still open. First, the evaluation $G_J(\beta) = \tau(\chi) \overline{\chi}((\beta) \mathfrak{f} J \mathfrak{d})$ for $\beta \in (\mathfrak{f} J)^\vee$, with $G_J(\beta) = 0$ if $(\beta) \mathfrak{f} J \mathfrak{d}$ is not prime to $\mathfrak{f}$. The twist relation `IsRayClassType.rayGaussCoeff_eq_mul` is one part of this. The vanishing needs an integer $u \equiv 1 \bmod \mathfrak{f} \mathfrak{p}^{-1}$ with $\chi((u)) \neq 1$ for each prime $\mathfrak{p} \mid \mathfrak{f}$ that divides $(\beta) \mathfrak{f} J \mathfrak{d}$, and this uses the minimality of the conductor exponent. The evaluation needs that $(\mathfrak{f} J)^\vee / \mathfrak{d}^{-1} J^{-1}$ is a cyclic module over $\mathcal{O}_K / \mathfrak{f}$. Second, the identity $|\tau(\chi)|^2 = N(\mathfrak{f})$ for a primitive $\chi$. Third, the assembly into `Langlands.HeckeFunctionalEquationAt` for an imaginary quadratic field: the dual series as the partial $L$-series of $\chi^{-1}$, the sum over the classes, the root number $W = \tau(\chi) / \sqrt{N(\mathfrak{f})}$, and the comparison of $\Gamma_\mathbb{R}(2u)$ with the gamma factor `Langlands.gammaFactor` and the archimedean parameters of $\chi$.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VII, sections 6 to 8.
-/

open Module Filter Topology Set Complex
open scoped Classical

namespace Langlands.Tate

section Local

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- If $v$ is ramified, $|y|_v = 1$ and $v(z - y) \geq a_v$, then $\chi_v(z) = \chi_v(y)$. -/
theorem finiteComponent_eq_of_valued_sub_le (χ : HeckeCharacter K) {v : HeightOneSpectrum (𝓞 K)}
    (hv : χ.conductorExponent v ≠ 0) {y z : (v.adicCompletion K)ˣ}
    (hy : Valued.v (y : v.adicCompletion K) = 1)
    (h : Valued.v ((z : v.adicCompletion K) - y) ≤ WithZero.exp (-(χ.conductorExponent v : ℤ))) :
    χ.finiteComponent v z = χ.finiteComponent v y := by
  have hlt : Valued.v ((z : v.adicCompletion K) - y) < Valued.v (y : v.adicCompletion K) :=
    h.trans_lt (by rw [hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hz : Valued.v (z : v.adicCompletion K) = 1 := by
    have := Valuation.map_add_eq_of_lt_left Valued.v hlt
    rwa [add_sub_cancel, hy] at this
  have ht : χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) :=
    Nat.sInf_mem (s := {m | χ.IsTrivialOnHigherUnits v m})
      (NonArchimedean.exists_isTrivialOnHigherUnits v χ)
  have hy0 : (y : v.adicCompletion K) ≠ 0 := y.ne_zero
  have h1 := ht (z * y⁻¹) (by
    rw [Units.val_mul, map_mul, hz, Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one, mul_one]) (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val,
      show (z : v.adicCompletion K) * (y : v.adicCompletion K)⁻¹ - 1 =
        ((z : v.adicCompletion K) - y) * (y : v.adicCompletion K)⁻¹ by field_simp,
      map_mul, map_inv₀, hy, inv_one, mul_one]
    exact h)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

/-- **The ideal character on principal ideals and the local components.** Let $\chi$ be of ray class type, with ramified set $R$. If $x \in K^\times$ is a unit at each $v \in R$, then $\chi((x)) \prod_{v \in R} \chi_v(x) = 1$. -/
theorem IsRayClassType.idealChar_mul_prod_finiteComponent (hχ : IsRayClassType χ) (x : Kˣ)
    (hx : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K x) * ∏ v ∈ ramifiedSet χ,
      χ.finiteComponent v (ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x)) = 1 := by
  have hfin := Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = WithZero.exp
          (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) :=
    fun v => by rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count]
  set S := hfin.toFinset ∪ ramifiedSet χ with hSdef
  have hS : ∀ v ∉ S,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    rw [hval, show FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0
      by simpa using fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h)),
      neg_zero, WithZero.exp_zero]
  have hR : ∀ v ∉ S, χ.IsUnramifiedAt v := fun v hv =>
    not_not.1 fun h => hv (Finset.mem_union_right _ (mem_ramifiedSet.2 h))
  have h := hχ.ideleChar_eq_prod _ S hS hR
  rw [ideleChar_unitEmbedding] at h
  rw [idealChar_apply, coe_toPrincipalIdeal, finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · have hRS : S ∩ ramifiedSet χ = ramifiedSet χ :=
      Finset.inter_eq_right.2 Finset.subset_union_right
    rw [h, ← hRS, ← Finset.prod_ite_mem, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v ∈ ramifiedSet χ
    · rw [hx v hv, zpow_zero, one_mul, ite_eq_left hv]
    · rw [ite_eq_right hv, mul_one, finiteComponent_eq_zpow_of_isUnramifiedAt
        (not_not.1 (mt mem_ramifiedSet.2 hv)), hval, WithZero.log_exp, neg_neg]
  · intro v hv
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl fun h0 => hv (by simp only [h0, zpow_zero])

/-- **Approximation of a local unit by an integer.** Let $v_0$ be a finite place, let $y \in \mathcal{O}_{v_0}^\times$, and let $e_w$ be natural numbers for the places $w$ of a finite set $R$. There is $u \in \mathcal{O}_K$ with $v_0(u - y) \geq e_{v_0}$ and $w(u - 1) \geq e_w$ for each $w \in R$ with $w \neq v_0$. -/
theorem exists_integer_approx (R : Finset (HeightOneSpectrum (𝓞 K))) (e : HeightOneSpectrum (𝓞 K) → ℕ)
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ R) (y : v₀.adicCompletion K)
    (hy : Valued.v y ≤ 1) :
    ∃ u : 𝓞 K, Valued.v (algebraMap K (v₀.adicCompletion K) (u : K) - y) ≤
        WithZero.exp (-(e v₀ : ℤ)) ∧
      ∀ w ∈ R, w ≠ v₀ → w.valuation K ((u : K) - 1) ≤ WithZero.exp (-(e w : ℤ)) := by
  have hr : (NonArchimedean.q v₀)⁻¹ ^ e v₀ ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (NonArchimedean.q_pos v₀).ne')
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap K v₀).exists_mem_open
    (IsUltrametricDist.isOpen_closedBall y hr)
    ⟨y, Metric.mem_closedBall_self (pow_nonneg (inv_nonneg.2 (NonArchimedean.q_pos v₀).le) _)⟩
  rw [Metric.mem_closedBall, dist_eq_norm, NonArchimedean.norm_le_inv_q_pow_iff] at hk
  have hk1 : v₀.valuation K k ≤ 1 := by
    rw [← valued_algebraMap, ← sub_add_cancel (algebraMap K (v₀.adicCompletion K) k) y]
    refine (Valuation.map_add _ _ _).trans (max_le (hk.trans ?_) hy)
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := v₀.exists_valuation_sub_lt_of_integer hk1
    (Units.mk0 (WithZero.exp (-(e v₀ : ℤ))) WithZero.exp_ne_zero)
  obtain ⟨u, hu⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := R)
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) e (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun i => if (i : HeightOneSpectrum (𝓞 K)) = v₀ then a else 1)
  have hval : ∀ w ∈ R, w.valuation K ((u : K) -
      ((if w = v₀ then a else 1 : 𝓞 K) : K)) ≤ WithZero.exp (-(e w : ℤ)) := fun w hw => by
    have := hu w hw
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at this
    rw [← map_sub, HeightOneSpectrum.valuation_of_algebraMap]
    exact this
  refine ⟨u, ?_, fun w hw hne => ?_⟩
  · have h1 := hval v₀ hv₀
    rw [ite_eq_left rfl] at h1
    rw [show algebraMap K (v₀.adicCompletion K) (u : K) - y =
      algebraMap K (v₀.adicCompletion K) ((u : K) - a) +
        (algebraMap K (v₀.adicCompletion K) ((a : K) - k) +
          (algebraMap K (v₀.adicCompletion K) k - y)) by simp only [map_sub]; ring]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((Valuation.map_add _ _ _).trans
      (max_le ?_ hk)))
    · rw [valued_algebraMap]
      exact h1
    · rw [valued_algebraMap]
      exact ha.le
  · have h1 := hval w hw
    rw [ite_eq_right hne] at h1
    simpa using h1

/-- A place of the ramified set has conductor exponent at least $1$. -/
theorem conductorExponent_ne_zero_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ ramifiedSet χ) :
    χ.conductorExponent v ≠ 0 :=
  NonArchimedean.conductorExponent_ne_zero v χ (mem_ramifiedSet.1 hv)

/-- If $v(x) = 1$ for $x \in K^\times$, then the exponent of $\mathfrak{p}_v$ in $(x)$ is $0$. -/
theorem count_eq_zero_of_valuation_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ)
    (h : v.valuation K (x : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  rw [valuation_eq_exp_neg_count, ← WithZero.exp_zero] at h
  exact neg_eq_zero.1 (WithZero.exp_injective h)

/-- If $w(x - 1) \geq e$ with $e \geq 1$, then $w(x) = 1$. -/
theorem valuation_eq_one_of_sub_one_le (w : HeightOneSpectrum (𝓞 K)) {x : K} {e : ℕ}
    (he : e ≠ 0) (h : w.valuation K (x - 1) ≤ WithZero.exp (-(e : ℤ))) : w.valuation K x = 1 := by
  have hlt : w.valuation K (x - 1) < w.valuation K 1 := h.trans_lt (by
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have := Valuation.map_add_eq_of_lt_left _ hlt
  rwa [add_sub_cancel, map_one] at this

/-- **An integer with a prescribed local component.** Let $\chi$ be of ray class type, with ramified set $R$, let $v_0 \in R$ and let $y \in \mathcal{O}_{v_0}^\times$. There is a nonzero $u \in \mathcal{O}_K$ with $v_0(u - y) \geq a_{v_0}$ and $w(u - 1) \geq a_w$ for the other $w \in R$. Such a $u$ is a unit at each $v \in R$, and $\chi((u)) = \chi_{v_0}(y)^{-1}$. -/
theorem IsRayClassType.exists_integer_idealChar (hχ : IsRayClassType χ)
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ ramifiedSet χ) (y : (v₀.adicCompletion K)ˣ)
    (hy : Valued.v (y : v₀.adicCompletion K) = 1) :
    ∃ (u : 𝓞 K) (hu : (u : K) ≠ 0),
      Valued.v (algebraMap K (v₀.adicCompletion K) (u : K) - y) ≤
        WithZero.exp (-(χ.conductorExponent v₀ : ℤ)) ∧
      (∀ w ∈ ramifiedSet χ, w ≠ v₀ →
        w.valuation K ((u : K) - 1) ≤ WithZero.exp (-(χ.conductorExponent w : ℤ))) ∧
      (∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) ∧
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu)) =
        (χ.finiteComponent v₀ y)⁻¹ := by
  obtain ⟨u, hu1, hu2⟩ := exists_integer_approx (ramifiedSet χ) χ.conductorExponent hv₀
    (y : v₀.adicCompletion K) hy.le
  have ha₀ := conductorExponent_ne_zero_of_mem hv₀
  have hv₀u : v₀.valuation K (u : K) = 1 := by
    have hlt : Valued.v (algebraMap K (v₀.adicCompletion K) (u : K) - y) <
        Valued.v (y : v₀.adicCompletion K) :=
      hu1.trans_lt (by rw [hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have := Valuation.map_add_eq_of_lt_left Valued.v hlt
    rwa [add_sub_cancel, hy, valued_algebraMap] at this
  have hu0 : (u : K) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv₀u
    exact zero_ne_one hv₀u
  have hval : ∀ v ∈ ramifiedSet χ, v.valuation K (u : K) = 1 := fun v hv => by
    by_cases hv' : v = v₀
    · rw [hv']
      exact hv₀u
    · exact valuation_eq_one_of_sub_one_le v (conductorExponent_ne_zero_of_mem hv) (hu2 v hv hv')
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0 :=
    fun v hv => count_eq_zero_of_valuation_eq_one v (Units.mk0 _ hu0) (hval v hv)
  refine ⟨u, hu0, hu1, hu2, hcount, ?_⟩
  have h := hχ.idealChar_mul_prod_finiteComponent (Units.mk0 _ hu0) hcount
  rw [Finset.prod_eq_single v₀ (fun w hw hne => ?_) (fun h => absurd hv₀ h)] at h
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← h]
    congr 1
    exact (finiteComponent_eq_of_valued_sub_le χ ha₀ hy (by
      rw [ideleFin_unitEmbedding, Units.val_mk0]
      exact hu1)).symm
  · rw [finiteComponent_eq_of_valued_sub_le χ (conductorExponent_ne_zero_of_mem hw)
      (y := 1) (by simp) (by
        rw [ideleFin_unitEmbedding, Units.val_mk0, Units.val_one, ← map_one (algebraMap K _),
          ← map_sub, valued_algebraMap]
        exact hu2 w hw hne), map_one]

/-- **The character of $(\mathcal{O}_K / \mathfrak{f})^\times$ is not trivial.** Let $\chi$ be of ray class type and ramified at one place. There is a nonzero $u \in \mathcal{O}_K$ that is a unit at each ramified place, with $\chi((u)) \neq 1$. -/
theorem IsRayClassType.exists_idealChar_ne_one (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) :
    ∃ (u : 𝓞 K) (hu : (u : K) ≠ 0),
      (∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) ∧
      idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu)) ≠ 1 := by
  obtain ⟨v₀, hv₀⟩ := hS
  have hram := mem_ramifiedSet.1 hv₀
  simp only [HeckeCharacter.IsUnramifiedAt, HeckeCharacter.IsTrivialOnHigherUnits,
    not_forall] at hram
  obtain ⟨y, hy, -, hχy⟩ := hram
  obtain ⟨u, hu0, -, -, hcount, he⟩ := hχ.exists_integer_idealChar hv₀ y hy
  exact ⟨u, hu0, hcount, by rw [he]; exact inv_ne_one.2 hχy⟩

end Local

section Vanishing

/-- **A sum over a finite quotient is invariant under an automorphism.** Let $H$ be a subgroup of finite index of an abelian group $G$, let $f$ be a function on $G$ that is periodic modulo $H$, and let $T$ be an endomorphism of $G$ with $T^{-1}(H) = H$. Then $\sum_{q \in G / H} f(T q) = \sum_{q \in G / H} f(q)$. -/
theorem sum_out_map_eq {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    [Fintype (G ⧸ H)] (f : G → ℂ) (hf : ∀ g h, h ∈ H → f (g + h) = f g) (T : G →+ G)
    (hT : H ≤ H.comap T) (hT' : H.comap T ≤ H) :
    ∑ q : G ⧸ H, f (T q.out) = ∑ q : G ⧸ H, f q.out := by
  have hcq : ∀ g g' : G, (g : G ⧸ H) = g' → f g' = f g := fun g g' h => by
    have := hf g (-g + g') (QuotientAddGroup.eq.1 h)
    rwa [add_neg_cancel_left] at this
  set σ : G ⧸ H →+ G ⧸ H := QuotientAddGroup.map H H T hT with hσ
  have hinj : Function.Injective σ := by
    refine (injective_iff_map_eq_zero σ).2 fun q hq => ?_
    induction q using QuotientAddGroup.induction_on with
    | H g =>
      rw [hσ, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hq
      exact (QuotientAddGroup.eq_zero_iff g).2 (hT' hq)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  have h2 : ∀ q : G ⧸ H, f (σ q).out = f (T q.out) := fun q => by
    refine hcq _ _ ?_
    rw [QuotientAddGroup.out_eq']
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  rw [← Finset.sum_congr rfl fun q _ => h2 q]
  exact Fintype.sum_bijective σ hbij (fun q => f (σ q).out) (fun q => f q.out) fun q => rfl

/-- **A twisted sum over a finite quotient vanishes.** Let $H$ be a subgroup of finite index of an abelian group $G$, let $c$ be a function on $G$ that is periodic modulo $H$, and let $T$ be an endomorphism of $G$ with $T^{-1}(H) = H$. If $c(T g) = z c(g)$ for each $g$ and $z \neq 1$, then $\sum_{q \in G / H} c(q) = 0$. -/
theorem sum_out_eq_zero_of_map {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    [Fintype (G ⧸ H)] (c : G → ℂ) (hc : ∀ g h, h ∈ H → c (g + h) = c g) (T : G →+ G)
    (hT : H ≤ H.comap T) (hT' : H.comap T ≤ H) {z : ℂ} (hz : z ≠ 1)
    (hcT : ∀ g, c (T g) = z * c g) :
    ∑ q : G ⧸ H, c q.out = 0 := by
  have h1 := sum_out_map_eq H c hc T hT hT'
  rw [Finset.sum_congr rfl fun q _ => hcT q.out, ← Finset.mul_sum] at h1
  have h3 : (z - 1) * ∑ q : G ⧸ H, c q.out = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hz)

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}

/-- The element of $J$ of a point of the lattice $\varphi(J)$ is additive in the point. -/
theorem symm_globalLatticeEquiv_add (J : (Ideal (𝓞 K))⁰)
    (a b : traceLattice K (FractionalIdeal.mk0 K J)) :
    (((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm (a + b) : _) : K) =
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm a : K) +
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm b : K) :=
by
  have h : (globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm (a + b) =
      ⟨((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm a : K) +
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm b : K),
        add_mem ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm a).2
          ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm b).2⟩ := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_globalLatticeEquiv, map_add, ← coe_globalLatticeEquiv, ← coe_globalLatticeEquiv,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [h]

omit [NumberField K] in
/-- A fractional ideal is stable under multiplication by an integer. -/
theorem coe_mul_mem (I : FractionalIdeal (𝓞 K)⁰ K) (u : 𝓞 K) {ξ : K} (h : ξ ∈ I) :
    (u : K) * ξ ∈ I := by
  have := Submodule.smul_mem (I : Submodule (𝓞 K) K) u h
  rwa [Algebra.smul_def] at this

/-- The multiplication by $u \in \mathcal{O}_K$ on the lattice $\varphi(J)$. -/
noncomputable def rayMulMap (J : (Ideal (𝓞 K))⁰) (u : 𝓞 K) :
    traceLattice K (FractionalIdeal.mk0 K J) →+ traceLattice K (FractionalIdeal.mk0 K J) :=
  AddMonoidHom.mk' (fun ℓ => globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)
    ⟨(u : K) * ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K),
      coe_mul_mem _ u ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ).2⟩)
    fun a b => Subtype.ext (by
      simp only [AddMemClass.coe_add, coe_globalLatticeEquiv]
      rw [symm_globalLatticeEquiv_add, mul_add, map_add])

/-- The element of $J$ of the point $u \cdot \ell$ is $u \xi_\ell$. -/
theorem coe_symm_rayMulMap (J : (Ideal (𝓞 K))⁰) (u : 𝓞 K)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    (((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm (rayMulMap J u ℓ) :
      _) : K) = (u : K) *
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K) := by
  rw [rayMulMap, AddMonoidHom.mk'_apply, Equiv.symm_apply_apply]

/-- A point of $\varphi(J)$ is in $\varphi(\mathfrak{f} J)$ if and only if its element of $J$ is in $\mathfrak{f} J$. -/
theorem mem_rayLattice_iff (J : (Ideal (𝓞 K))⁰) (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    ℓ.1 ∈ rayLattice χ J ↔
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K) ∈
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  constructor
  · intro h
    obtain ⟨γ, hγ, hγℓ⟩ := (mem_globalLattice K _ _).1 h
    have he : (globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ =
        ⟨γ, mem_of_mem_conductor_mul J hγ⟩ := by
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      rw [coe_globalLatticeEquiv]
      exact hγℓ.symm
    rw [he]
    exact hγ
  · intro h
    have he : ℓ.1 = globalEmbedding K (fun w => (traceScale K w : ℝ))
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K) := by
      rw [← coe_globalLatticeEquiv, Equiv.apply_symm_apply]
    rw [he]
    exact globalEmbedding_mem K _ _ h

/-- A point of $\varphi(J)$ is in the subgroup $\varphi(\mathfrak{f} J)$ if and only if its element of $J$ is in $\mathfrak{f} J$. -/
theorem mem_subLattice_rayLattice_iff (J : (Ideal (𝓞 K))⁰)
    (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    ℓ ∈ subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J) ↔
      ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K) ∈
        ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  rw [subLattice, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, mem_rayLattice_iff]

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, then the ideal $(u)$ is prime to the conductor. -/
theorem span_sup_conductor_eq_top {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) :
    Ideal.span {u} ⊔ χ.conductor = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq, conductor_eq_prod]
  refine IsCoprime.prod_right fun v hv => IsCoprime.pow_right ?_
  have hu' : u ∉ v.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    have h := valuation_eq_exp_neg_count v (Units.mk0 _ hu0)
    rw [Units.val_mk0, hu v hv, neg_zero, WithZero.exp_zero] at h
    rw [h]
    exact lt_irrefl 1
  obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hu'
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup]
  exact ⟨y * u, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u), i, hi, hyi⟩

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, $\xi \in J$ and $u \xi \in \mathfrak{f} J$, then $\xi \in \mathfrak{f} J$. -/
theorem mem_of_coe_mul_mem {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (Ideal (𝓞 K))⁰) {ξ : K}
    (hξ : ξ ∈ ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
    (h : (u : K) * ξ ∈ ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) :
    ξ ∈ ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hξ h ⊢
  obtain ⟨ξ', hξ', rfl⟩ := hξ
  obtain ⟨t, ht, hte⟩ := h
  have htu : t = u * ξ' := IsFractionRing.injective (𝓞 K) K (by rw [hte, map_mul])
  subst htu
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
    ((span_sup_conductor_eq_top hu0 hu).symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ _)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨ξ', ?_, rfl⟩
  have he : ξ' = r * (u * ξ') + z * ξ' := by linear_combination (-ξ') * hyz
  rw [he]
  rw [Submonoid.coe_mul] at ht ⊢
  exact add_mem (Ideal.mul_mem_left _ r ht) (Ideal.mul_mem_mul hz hξ')

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, then $c_J(u \xi) = \chi((u)) c_J(\xi)$. -/
theorem rayCoeff_coe_mul {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ξ : K) :
    rayCoeff χ J ((u : K) * ξ) =
      (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) : ℂ) * rayCoeff χ J ξ := by
  have hcnt : ∀ v, ξ ≠ 0 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * ξ)) =
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) +
          FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ξ) := fun v hξ => by
    rw [map_mul, FractionalIdeal.count_mul K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hu0)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ)]
  rw [rayCoeff, rayCoeff]
  by_cases hξ : ξ ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ξ) =
        FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  · have hc : (u : K) * ξ ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * ξ)) =
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) :=
      ⟨mul_ne_zero hu0 hξ.1, fun v hv => by rw [hcnt v hξ.1, hu v hv, zero_add, hξ.2 v hv]⟩
    rw [dite_eq_left hc, dite_eq_left hξ]
    have hm : Units.mk0 ((u : K) * ξ) hc.1 = Units.mk0 (u : K) hu0 * Units.mk0 ξ hξ.1 :=
      Units.ext rfl
    rw [hm, map_mul, map_mul]
    push_cast
    ring
  · have hc : ¬ ((u : K) * ξ ≠ 0 ∧ ∀ v ∈ ramifiedSet χ,
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * ξ)) =
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) := fun h => by
      have hξ0 : ξ ≠ 0 := fun h0 => h.1 (by rw [h0, mul_zero])
      refine hξ ⟨hξ0, fun v hv => ?_⟩
      have := h.2 v hv
      rwa [hcnt v hξ0, hu v hv, zero_add] at this
    rw [dite_eq_right hc, dite_eq_right hξ, mul_zero]

/-- The multiplication by $u$ maps $\varphi(\mathfrak{f} J)$ into itself. -/
theorem subLattice_le_comap_rayMulMap (J : (Ideal (𝓞 K))⁰) (u : 𝓞 K) :
    subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J) ≤
      (subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)).comap
        (rayMulMap J u) := fun h hh => by
  rw [mem_subLattice_rayLattice_iff] at hh
  rw [AddSubgroup.mem_comap, mem_subLattice_rayLattice_iff, coe_symm_rayMulMap]
  exact coe_mul_mem _ u hh

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, then a point $\ell$ of $\varphi(J)$ with $u \ell \in \varphi(\mathfrak{f} J)$ is in $\varphi(\mathfrak{f} J)$. -/
theorem comap_rayMulMap_le {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (Ideal (𝓞 K))⁰) :
    (subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)).comap
        (rayMulMap J u) ≤
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J) := fun h hh => by
  rw [AddSubgroup.mem_comap, mem_subLattice_rayLattice_iff, coe_symm_rayMulMap] at hh
  rw [mem_subLattice_rayLattice_iff]
  exact mem_of_coe_mul_mem hu0 hu J
    ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm h).2 hh

/-- If $u \in \mathcal{O}_K$ is a unit at each ramified place, then $c_J(u \ell) = \chi((u)) c_J(\ell)$ on the lattice $\varphi(J)$. -/
theorem rayLatticeCoeff_rayMulMap {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0)
    (J : (Ideal (𝓞 K))⁰) (ℓ : traceLattice K (FractionalIdeal.mk0 K J)) :
    rayLatticeCoeff χ J (rayMulMap J u ℓ) =
      (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) : ℂ) *
        rayLatticeCoeff χ J ℓ := by
  rw [rayLatticeCoeff, rayLatticeCoeff, coe_symm_rayMulMap]
  exact rayCoeff_coe_mul hu0 hu _ _

/-- **Step 1. The coefficients of the partial $L$-function have sum $0$.** Let $\chi$ be of ray class type and ramified at one place. Then $\sum_{x \in J / \mathfrak{f} J} c_J(x) = 0$. -/
theorem IsRayClassType.sum_rayLatticeCoeff_eq_zero (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    ∑ q : traceLattice K (FractionalIdeal.mk0 K J) ⧸
      subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J),
        rayLatticeCoeff χ J q.out = 0 := by
  obtain ⟨u, hu0, hcount, hne⟩ := hχ.exists_idealChar_ne_one hS
  exact sum_out_eq_zero_of_map _ (rayLatticeCoeff χ J)
    (fun g h hh => hχ.rayLatticeCoeff_add hS J g ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩)
    (rayMulMap J u) (subLattice_le_comap_rayMulMap J u) (comap_rayMulMap_le hu0 hcount J)
    (z := (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) : ℂ))
    (fun h => hne (Units.ext h)) (rayLatticeCoeff_rayMulMap hu0 hcount J)

/-- **The completed partial $L$-function is entire.** Let $\chi$ be of ray class type and ramified at one place. Then $\Lambda_J$ is an entire function. -/
theorem IsRayClassType.differentiable_rayClassCompleted_of_nonempty (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) :
    Differentiable ℂ (rayClassCompleted χ J) :=
  hχ.differentiable_rayClassCompleted hS J (hχ.sum_rayLatticeCoeff_eq_zero hS J)

/-- For $\beta \in (\mathfrak{f} J)^\vee$, the character $\xi \mapsto e^{2 \pi i \mathrm{Tr}(\beta \xi)}$ is periodic modulo $\mathfrak{f} J$. -/
theorem cexp_trace_add (J : (Ideal (𝓞 K))⁰) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K))
    (ℓ h : traceLattice K (FractionalIdeal.mk0 K J))
    (hh : h ∈ subLattice (traceLattice K (FractionalIdeal.mk0 K J)) (rayLattice χ J)) :
    cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (β *
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm (ℓ + h) : K)) :
          ℚ) : ℝ)) =
      cexp (2 * Real.pi * I * ((Algebra.trace ℚ K (β *
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K)) :
          ℚ) : ℝ)) := by
  have hγ := (mem_subLattice_rayLattice_iff J h).1 hh
  obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual (Units.ne_zero _)).1 hβ _ hγ
  rw [Algebra.traceForm_apply, eq_intCast] at hn
  rw [symm_globalLatticeEquiv_add, mul_add, map_add, ← hn, Rat.cast_add, Rat.cast_intCast,
    Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_intCast,
    mul_comm _ (n : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The Gauss sum under a twist.** Let $\chi$ be of ray class type and ramified at one place, let $\beta \in (\mathfrak{f} J)^\vee$, and let $u \in \mathcal{O}_K$ be a unit at each ramified place. Then $G_J(\beta) = \chi((u)) G_J(u \beta)$. -/
theorem IsRayClassType.rayGaussCoeff_eq_mul (hχ : IsRayClassType χ)
    (hS : (ramifiedSet χ).Nonempty) (J : (Ideal (𝓞 K))⁰) {u : 𝓞 K} (hu0 : (u : K) ≠ 0)
    (hu : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K)) = 0) {β : K}
    (hβ : β ∈ FractionalIdeal.dual ℤ ℚ
      ((FractionalIdeal.mk0 K (conductorNZ χ * J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) :
    rayGaussCoeff χ J β =
      (idealChar χ (toPrincipalIdeal (𝓞 K) K (Units.mk0 (u : K) hu0)) : ℂ) *
        rayGaussCoeff χ J ((u : K) * β) := by
  rw [rayGaussCoeff, rayGaussCoeff, Finset.mul_sum]
  refine (sum_out_map_eq _ (fun ℓ => rayLatticeCoeff χ J ℓ * cexp (2 * Real.pi * I *
      ((Algebra.trace ℚ K (β *
        ((globalLatticeEquiv K (traceScale K) (FractionalIdeal.mk0 K J)).symm ℓ : K)) : ℚ) :
          ℝ))) (fun g h hh => ?_) (rayMulMap J u) (subLattice_le_comap_rayMulMap J u)
      (comap_rayMulMap_le hu0 hu J)).symm.trans (Finset.sum_congr rfl fun q _ => ?_)
  · beta_reduce
    rw [hχ.rayLatticeCoeff_add hS J g ⟨h.1, AddSubgroup.mem_addSubgroupOf.1 hh⟩,
      cexp_trace_add J hβ g h hh]
  · beta_reduce
    rw [rayLatticeCoeff_rayMulMap hu0 hu, coe_symm_rayMulMap, mul_left_comm β, mul_assoc (u : K) β]
    exact mul_assoc _ _ _

end Vanishing

end Langlands.Tate
