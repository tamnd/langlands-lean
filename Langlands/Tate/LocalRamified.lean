/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Hecke.Rational
import Langlands.Tate.NonArchimedeanLocalEquation

/-!
# The local theory at a ramified finite place

Let $v$ be a finite place of a number field $K$, with completion $K_v$, ring of integers $\mathcal{O}_v$, uniformizer $\varpi$ and residue field of size $q = N(v)$. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a character with conductor exponent $a \geq 1$, so $\chi$ is trivial on $1 + \mathfrak{p}_v^a$ but not on $1 + \mathfrak{p}_v^{a-1}$. Let $\psi$ be an additive character of conductor exponent $d$: it is trivial on $\{|x|_v \leq q^d\}$, which is the inverse different $\mathfrak{p}_v^{-d}$, and not on $\{|x|_v \leq q^{d+1}\}$.

The file `Langlands.Tate.NonArchimedeanGauss` defines the Gauss sum as an integral $G(\chi, \psi, c) = \int_{\mathcal{O}_v^\times} \chi(u) \psi(c u) \, du$. This file gives the classical finite form
$$\tau(\chi, \psi, c) = \sum_{u \in (\mathcal{O}_v / \mathfrak{p}_v^a)^\times} \chi(u) \psi(c u), \qquad |c|_v = q^{a + d},$$
for example $c = \varpi^{-(a + d)}$, so that $\psi(c u) = \psi(u / \varpi^{a + d})$. The summand does not depend on the choice of the representative $u \in \mathcal{O}_v^\times$ of a class. We prove $|\tau|^2 = q^a$, and we prove that a ramified character has sum $0$ over the units and integral $0$ over each shell $\varpi^n \mathcal{O}_v^\times$.

## Main definitions

* `Langlands.Tate.NonArchimedean.higherIdeal`: the ideal $\mathfrak{p}_v^m = \{x \in \mathcal{O}_v : |x|_v \leq q^{-m}\}$.
* `Langlands.Tate.NonArchimedean.ResidueRing`: the finite ring $\mathcal{O}_v / \mathfrak{p}_v^m$.
* `Langlands.Tate.NonArchimedean.rep`: a representative in $\mathcal{O}_v$ of a class of $\mathcal{O}_v / \mathfrak{p}_v^m$.
* `Langlands.Tate.NonArchimedean.residueChar`: the character of $(\mathcal{O}_v / \mathfrak{p}_v^m)^\times$ that $\chi$ induces.
* `Langlands.Tate.NonArchimedean.gaussSumFinite`: the finite Gauss sum $\tau(\chi, \psi, c)$.

## Main results

* `setIntegral_sphere_eq_sum`: the integral over $\mathcal{O}_v^\times$ of a function that is constant on the cosets of $1 + \mathfrak{p}_v^m$ is $q^{-m}$ times the sum over $(\mathcal{O}_v / \mathfrak{p}_v^m)^\times$.
* `gaussSum_eq_gaussSumFinite`: $G(\chi, \psi, c) = q^{-a} \tau(\chi, \psi, c)$.
* `norm_gaussSumFinite_sq`: $|\tau(\chi, \psi, c)|^2 = q^a$.
* `gaussSumFinite_mul_gaussSumFinite_inv`: $\tau(\chi, \psi, c) \tau(\chi^{-1}, \psi, -c) = q^a$.
* `norm_gaussSumFinite_uniformizer_sq`: the same for $c = \varpi^{-(a + d)}$.
* `sum_charExt_rep_eq_zero`: $\sum_{u \in (\mathcal{O}_v / \mathfrak{p}_v^m)^\times} \chi(u) = 0$ for a ramified $\chi$.
* `setIntegral_sphere_charExt_of_ramified` and `zetaIntegral_eq_zero_of_ramified`: for a ramified $\chi$ the integral of $\chi(x) |x|_v^s$ over each shell is $0$, and so is the zeta integral of every function that is invariant under $\mathcal{O}_v^\times$.
* `exists_isTrivialOnHigherUnits`: every Hecke character has a finite conductor exponent at $v$.
* `localFactor_eq_one_of_not_isUnramifiedAt`: the local factor of a Hecke character at a ramified place is $1$.
* `norm_gaussSumFinite_finiteComponent_sq`: for a Hecke character $\chi$ ramified at $v$, with $a$ the conductor exponent of `Langlands.HeckeCharacter.conductorExponent`, $|\tau(\chi_v, \psi, c)|^2 = q^a$.
* `epsilonRamified_eq_cpow` and `localFunctionalEquation_ramified_gaussSumFinite`: the local epsilon factor of Tate's test function $\mathbf{1}_{1 + \mathfrak{p}_v^a}$ is $\chi(c)^{-1} q^{(a + d)(1/2 - s)} q^{d/2} \tau(\chi^{-1}, \psi, c) / q^{a/2}$.

## Normalizations

The measure $du$ has $\int_{\mathcal{O}_v} du = 1$. The factor $q^{d/2}$ in the epsilon factor comes from this choice: the self dual measure for $\psi$ is $q^{-d/2} du$. The factor $\chi(c)^{-1}$ is $\chi(\varpi)^{a + d}$ for $c = \varpi^{-(a + d)}$. The quotient $\tau / q^{a/2}$ has absolute value $1$.

## Proofs

The ring $\mathcal{O}_v / \mathfrak{p}_v^m$ is finite because $\mathcal{O}_v$ is compact and $\mathfrak{p}_v^m$ is open. For $m \geq 1$ the sphere $\mathcal{O}_v^\times$ is the disjoint union of the balls $u + \mathfrak{p}_v^m$, one for each unit of $\mathcal{O}_v / \mathfrak{p}_v^m$, and each ball has measure $q^{-m}$. The integrand $\chi(u) \psi(c u)$ of the Gauss sum is constant on these balls, so the integral is $q^{-a}$ times the finite sum, and $|\tau|^2 = q^{2a} |G|^2 = q^a$ by `norm_gaussSum_sq`. The sum of $\chi$ over the units is $0$ because $\chi$ induces a nontrivial character of the finite group $(\mathcal{O}_v / \mathfrak{p}_v^a)^\times$. The existence of the conductor exponent uses `Langlands.HeckeRat.Top.exists_trivial_on_units`, which holds for every number field.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, section 2.4.
* J. Neukirch, Algebraic number theory, chapter VII, section 7.
-/

namespace Langlands.Tate.NonArchimedean

open NumberField IsDedekindDomain MeasureTheory Metric
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-! ### The finite ring $\mathcal{O}_v / \mathfrak{p}_v^m$ -/

/-- An element of $\mathcal{O}_v$ has absolute value at most $1$. -/
theorem norm_coe_integers_le_one (x : v.adicCompletionIntegers K) :
    ‖(x : v.adicCompletion K)‖ ≤ 1 := by
  have h : (x : v.adicCompletion K) ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    x.2
  rw [coe_adicCompletionIntegers] at h
  exact mem_closedBall_zero_iff.1 h

/-- An element of $K_v$ of absolute value at most $1$ is in $\mathcal{O}_v$. -/
theorem mem_integers_of_norm_le_one {x : v.adicCompletion K} (hx : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers K := by
  have h : x ∈ closedBall (0 : v.adicCompletion K) 1 := mem_closedBall_zero_iff.2 hx
  rw [← coe_adicCompletionIntegers] at h
  exact h

/-- The ring $\mathcal{O}_v$ is compact. -/
instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) := by
  have h : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    rw [coe_adicCompletionIntegers]
    exact isCompact_closedBall 0 1
  exact isCompact_iff_compactSpace.1 h

/-- The ideal $\mathfrak{p}_v^m$ of $\mathcal{O}_v$, as the set of $x$ with $|x|_v \leq q^{-m}$. -/
noncomputable def higherIdeal (m : ℕ) : Ideal (v.adicCompletionIntegers K) where
  carrier := {x | ‖(x : v.adicCompletion K)‖ ≤ (q v)⁻¹ ^ m}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, AddMemClass.coe_add] at hx hy ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, norm_zero]
    exact pow_nonneg (inv_nonneg.2 (q_pos v).le) m
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul] at hx ⊢
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_coe_integers_le_one v c)).trans hx

/-- The membership condition of `higherIdeal`. -/
theorem mem_higherIdeal {m : ℕ} (x : v.adicCompletionIntegers K) :
    x ∈ higherIdeal v m ↔ ‖(x : v.adicCompletion K)‖ ≤ (q v)⁻¹ ^ m :=
  Iff.rfl

/-- The finite ring $\mathcal{O}_v / \mathfrak{p}_v^m$. -/
abbrev ResidueRing (m : ℕ) : Type _ :=
  v.adicCompletionIntegers K ⧸ higherIdeal v m

/-- Two integers have the same class modulo $\mathfrak{p}_v^m$ if and only if $|x - y|_v \leq q^{-m}$. -/
theorem mk_eq_mk_iff {m : ℕ} (x y : v.adicCompletionIntegers K) :
    Ideal.Quotient.mk (higherIdeal v m) x = Ideal.Quotient.mk (higherIdeal v m) y ↔
      ‖(x : v.adicCompletion K) - y‖ ≤ (q v)⁻¹ ^ m := by
  rw [Ideal.Quotient.eq, mem_higherIdeal, AddSubgroupClass.coe_sub]

/-- The ideal $\mathfrak{p}_v^m$ is open in $\mathcal{O}_v$. -/
theorem isOpen_higherIdeal (m : ℕ) :
    IsOpen ((higherIdeal v m : Set (v.adicCompletionIntegers K))) := by
  have h : ((higherIdeal v m : Set (v.adicCompletionIntegers K))) =
      (fun x : v.adicCompletionIntegers K => (x : v.adicCompletion K)) ⁻¹'
        closedBall 0 ((q v)⁻¹ ^ m) := by
    ext x
    simp only [SetLike.mem_coe, mem_higherIdeal, Set.mem_preimage, mem_closedBall_zero_iff]
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _
    (pow_ne_zero _ (inv_ne_zero (q_pos v).ne'))).preimage continuous_subtype_val

/-- The ring $\mathcal{O}_v / \mathfrak{p}_v^m$ is finite, because $\mathcal{O}_v$ is compact and $\mathfrak{p}_v^m$ is open. -/
instance finite_residueRing (m : ℕ) : Finite (ResidueRing v m) :=
  AddSubgroup.quotient_finite_of_isOpen (higherIdeal v m).toAddSubgroup (isOpen_higherIdeal v m)

/-- A choice of a finite type structure on the unit group $(\mathcal{O}_v / \mathfrak{p}_v^m)^\times$. -/
noncomputable instance fintype_units_residueRing (m : ℕ) : Fintype (ResidueRing v m)ˣ :=
  haveI : Finite (ResidueRing v m)ˣ :=
    Finite.of_injective (fun u : (ResidueRing v m)ˣ => (u : ResidueRing v m)) fun _ _ h => Units.ext h
  Fintype.ofFinite _

/-- A representative in $\mathcal{O}_v$ of a class of $\mathcal{O}_v / \mathfrak{p}_v^m$. -/
noncomputable def lift {m : ℕ} (u : ResidueRing v m) : v.adicCompletionIntegers K :=
  Function.surjInv Ideal.Quotient.mk_surjective u

/-- The representative is in the given class. -/
theorem mk_lift {m : ℕ} (u : ResidueRing v m) : Ideal.Quotient.mk (higherIdeal v m) (lift v u) = u :=
  Function.surjInv_eq _ u

/-- The representative of a class of $\mathcal{O}_v / \mathfrak{p}_v^m$, as an element of $K_v$. -/
noncomputable def rep {m : ℕ} (u : ResidueRing v m) : v.adicCompletion K :=
  (lift v u : v.adicCompletionIntegers K)

/-- A representative has absolute value at most $1$. -/
theorem norm_rep_le_one {m : ℕ} (u : ResidueRing v m) : ‖rep v u‖ ≤ 1 :=
  norm_coe_integers_le_one v _

/-- If $|x|_v = 1$ and $|y - x|_v < 1$, then $|y|_v = 1$. -/
theorem norm_eq_one_of_norm_sub_lt {x y : v.adicCompletion K} (hx : ‖x‖ = 1) (h : ‖y - x‖ < 1) :
    ‖y‖ = 1 := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  have h1 : ‖y / x - 1‖ < 1 := by rwa [div_sub_one hx0, norm_div, hx, div_one]
  have h2 := norm_eq_one_of_norm_sub_one_lt v h1
  rwa [norm_div, hx, div_one] at h2

/-- For $m \geq 1$, the representative of a unit of $\mathcal{O}_v / \mathfrak{p}_v^m$ has absolute value $1$. -/
theorem norm_rep_unit {m : ℕ} (hm : m ≠ 0) (u : (ResidueRing v m)ˣ) :
    ‖rep v (u : ResidueRing v m)‖ = 1 := by
  have hmk : Ideal.Quotient.mk (higherIdeal v m) (lift v (u : ResidueRing v m) *
      lift v ((u⁻¹ : (ResidueRing v m)ˣ) : ResidueRing v m)) =
        Ideal.Quotient.mk (higherIdeal v m) 1 := by
    rw [map_mul, mk_lift, mk_lift, Units.mul_inv, map_one]
  rw [mk_eq_mk_iff, MulMemClass.coe_mul, OneMemClass.coe_one] at hmk
  have h1 : ‖rep v (u : ResidueRing v m) *
      rep v ((u⁻¹ : (ResidueRing v m)ˣ) : ResidueRing v m)‖ = 1 :=
    norm_eq_one_of_norm_sub_one_lt v (hmk.trans_lt (inv_q_pow_lt_one v hm))
  rw [norm_mul] at h1
  have hx := norm_rep_le_one v (u : ResidueRing v m)
  have hy := norm_rep_le_one v ((u⁻¹ : (ResidueRing v m)ˣ) : ResidueRing v m)
  refine le_antisymm hx ?_
  calc 1 = ‖rep v (u : ResidueRing v m)‖ *
        ‖rep v ((u⁻¹ : (ResidueRing v m)ˣ) : ResidueRing v m)‖ := h1.symm
    _ ≤ ‖rep v (u : ResidueRing v m)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = ‖rep v (u : ResidueRing v m)‖ := mul_one _

/-- The class of an integer of absolute value $1$ is a unit of $\mathcal{O}_v / \mathfrak{p}_v^m$. -/
theorem isUnit_mk_of_norm_eq_one {m : ℕ} (a : v.adicCompletionIntegers K)
    (ha : ‖(a : v.adicCompletion K)‖ = 1) : IsUnit (Ideal.Quotient.mk (higherIdeal v m) a) := by
  have ha0 : (a : v.adicCompletion K) ≠ 0 := norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)
  let b : v.adicCompletionIntegers K :=
    ⟨(a : v.adicCompletion K)⁻¹, mem_integers_of_norm_le_one v (by rw [norm_inv, ha, inv_one])⟩
  have hab : a * b = 1 := Subtype.ext (by
    rw [MulMemClass.coe_mul, OneMemClass.coe_one]
    exact mul_inv_cancel₀ ha0)
  exact IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) (by rw [← map_mul, hab, map_one])

/-- For $m \geq 1$, the sphere $\mathcal{O}_v^\times$ is the union of the balls $u + \mathfrak{p}_v^m$ over the units $u$ of $\mathcal{O}_v / \mathfrak{p}_v^m$. -/
theorem sphere_eq_iUnion {m : ℕ} (hm : m ≠ 0) :
    sphere (0 : v.adicCompletion K) 1 =
      ⋃ u : (ResidueRing v m)ˣ, closedBall (rep v (u : ResidueRing v m)) ((q v)⁻¹ ^ m) := by
  ext x
  simp only [Set.mem_iUnion, mem_sphere_zero_iff_norm, mem_closedBall, dist_eq_norm]
  constructor
  · intro hx
    let a : v.adicCompletionIntegers K := ⟨x, mem_integers_of_norm_le_one v hx.le⟩
    have hu := isUnit_mk_of_norm_eq_one v (m := m) a hx
    refine ⟨hu.unit, ?_⟩
    have h := (mk_eq_mk_iff v a (lift v (hu.unit : ResidueRing v m))).1
      (by rw [mk_lift, IsUnit.unit_spec])
    exact h
  · rintro ⟨u, hu⟩
    exact norm_eq_one_of_norm_sub_lt v (norm_rep_unit v hm u)
      (hu.trans_lt (inv_q_pow_lt_one v hm))

/-- The balls $u + \mathfrak{p}_v^m$ for distinct units $u$ of $\mathcal{O}_v / \mathfrak{p}_v^m$ are disjoint. -/
theorem pairwise_disjoint_closedBall_rep (m : ℕ) :
    Pairwise (Function.onFun Disjoint fun u : (ResidueRing v m)ˣ =>
      closedBall (rep v (u : ResidueRing v m)) ((q v)⁻¹ ^ m)) := by
  intro u w huw
  refine Set.disjoint_left.2 fun x hxu hxw => huw (Units.ext ?_)
  rw [mem_closedBall, dist_eq_norm] at hxu hxw
  have h := (mk_eq_mk_iff v (lift v (u : ResidueRing v m)) (lift v (w : ResidueRing v m))).2 (by
    calc ‖((lift v (u : ResidueRing v m) : v.adicCompletionIntegers K) : v.adicCompletion K) -
          (lift v (w : ResidueRing v m) : v.adicCompletionIntegers K)‖ =
          ‖-(x - rep v (u : ResidueRing v m)) + (x - rep v (w : ResidueRing v m))‖ := by
            congr 1
            simp only [rep]
            ring
      _ ≤ max ‖-(x - rep v (u : ResidueRing v m))‖ ‖x - rep v (w : ResidueRing v m)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
      _ ≤ (q v)⁻¹ ^ m := by rw [norm_neg]; exact max_le hxu hxw)
  rwa [mk_lift, mk_lift] at h

/-- Each ball $z + \mathfrak{p}_v^m$ has measure $q^{-m}$. -/
theorem haar_closedBall_center_pow (z : v.adicCompletion K) (m : ℕ) :
    haar v (closedBall z ((q v)⁻¹ ^ m)) = ENNReal.ofReal ((q v)⁻¹ ^ m) := by
  have h : closedBall z ((q v)⁻¹ ^ m) = (fun x => x + -z) ⁻¹' closedBall 0 ((q v)⁻¹ ^ m) := by
    ext x
    simp [dist_eq_norm, sub_eq_add_neg]
  rw [h, measure_preimage_add_right, haar_closedBall_pow]

/-- The integral over $\mathcal{O}_v^\times$ as a finite sum. Let $m \geq 1$ and let $g$ be constant on each ball $x + \mathfrak{p}_v^m$ with $|x|_v = 1$. Then $\int_{\mathcal{O}_v^\times} g \, du = q^{-m} \sum_{u \in (\mathcal{O}_v / \mathfrak{p}_v^m)^\times} g(u)$. -/
theorem setIntegral_sphere_eq_sum {m : ℕ} (hm : m ≠ 0) (g : v.adicCompletion K → ℂ)
    (hg : ∀ x y : v.adicCompletion K, ‖x‖ = 1 → ‖y - x‖ ≤ (q v)⁻¹ ^ m → g y = g x) :
    ∫ x in sphere 0 1, g x ∂haar v =
      (((q v)⁻¹ ^ m : ℝ) : ℂ) * ∑ u : (ResidueRing v m)ˣ, g (rep v (u : ResidueRing v m)) := by
  have hc (u : (ResidueRing v m)ˣ) : ∀ y ∈ closedBall (rep v (u : ResidueRing v m)) ((q v)⁻¹ ^ m),
      g y = g (rep v (u : ResidueRing v m)) := fun y hy =>
    hg _ y (norm_rep_unit v hm u) (by rwa [mem_closedBall, dist_eq_norm] at hy)
  have hfin (u : (ResidueRing v m)ˣ) :
      haar v (closedBall (rep v (u : ResidueRing v m)) ((q v)⁻¹ ^ m)) ≠ ⊤ := by
    rw [haar_closedBall_center_pow]
    exact ENNReal.ofReal_ne_top
  have hint (u : (ResidueRing v m)ˣ) :
      IntegrableOn g (closedBall (rep v (u : ResidueRing v m)) ((q v)⁻¹ ^ m)) (haar v) :=
    (integrableOn_const (C := g (rep v (u : ResidueRing v m))) (hfin u)).congr_fun
      (fun y hy => (hc u y hy).symm) measurableSet_closedBall
  rw [sphere_eq_iUnion v hm, integral_iUnion_fintype (fun _ => measurableSet_closedBall)
    (pairwise_disjoint_closedBall_rep v m) hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [setIntegral_congr_fun measurableSet_closedBall (hc u), setIntegral_const, measureReal_def,
    haar_closedBall_center_pow, ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.2 (q_pos v).le) _),
    Complex.real_smul]

/-! ### The finite Gauss sum -/

/-- If $\chi$ is trivial on $1 + \mathfrak{p}_v^m$ with $m \geq 1$, then $\chi$ is constant on each ball $x + \mathfrak{p}_v^m$ with $|x|_v = 1$. -/
theorem charExt_eq_of_norm_sub_le_pow {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) {x y : v.adicCompletion K} (hx : ‖x‖ = 1)
    (hxy : ‖y - x‖ ≤ (q v)⁻¹ ^ m) : charExt χ y = charExt χ x := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  have hy : ‖y‖ = 1 := norm_eq_one_of_norm_sub_lt v hx (hxy.trans_lt (inv_q_pow_lt_one v hm))
  have hy0 : y ≠ 0 := norm_ne_zero_iff.1 (by rw [hy]; exact one_ne_zero)
  have hw0 : y / x ≠ 0 := div_ne_zero hy0 hx0
  have hw : ‖y / x‖ = 1 := by rw [norm_div, hx, hy, div_one]
  have hw1 : ‖y / x - 1‖ ≤ (q v)⁻¹ ^ m := by rwa [div_sub_one hx0, norm_div, hx, div_one]
  have hχw : χ (Units.mk0 (y / x) hw0) = 1 := hχ (Units.mk0 (y / x) hw0) hw hw1
  rw [← div_mul_cancel₀ y hx0, charExt_mul χ hw0, hχw, Units.val_one, one_mul]

/-- If $\psi$ is trivial on $\{|x|_v \leq q^d\}$ and $|c|_v \leq q^{d + m}$, then $y \mapsto \psi(c y)$ is constant on each ball $x + \mathfrak{p}_v^m$. -/
theorem addChar_mul_eq_of_norm_sub_le (ψ : AddChar (v.adicCompletion K) ℂ) {d : ℤ}
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) {m : ℕ} {c : v.adicCompletion K}
    (hc : ‖c‖ ≤ q v ^ (d + m)) {x y : v.adicCompletion K} (hxy : ‖y - x‖ ≤ (q v)⁻¹ ^ m) :
    ψ (c * y) = ψ (c * x) := by
  have h : ‖c * (y - x)‖ ≤ q v ^ d := by
    rw [norm_mul]
    calc ‖c‖ * ‖y - x‖ ≤ q v ^ (d + m) * (q v)⁻¹ ^ m :=
          mul_le_mul hc hxy (norm_nonneg _) (zpow_pos (q_pos v) _).le
      _ = q v ^ d := by
          rw [zpow_add₀ (q_pos v).ne', zpow_natCast, inv_pow, mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ (q_pos v).ne'), mul_one]
  rw [show c * y = c * x + c * (y - x) by ring, AddChar.map_add_eq_mul, h1 _ h, mul_one]

/-- The finite Gauss sum $\tau(\chi, \psi, c) = \sum_{u \in (\mathcal{O}_v / \mathfrak{p}_v^m)^\times} \chi(u) \psi(c u)$, where $u$ runs over chosen representatives in $\mathcal{O}_v$. The classical choice is $m = a$, the conductor exponent of $\chi$, and $c = \varpi^{-(a + d)}$. -/
noncomputable def gaussSumFinite (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (ψ : AddChar (v.adicCompletion K) ℂ) (m : ℕ) (c : v.adicCompletion K) : ℂ :=
  ∑ u : (ResidueRing v m)ˣ, charExt χ (rep v (u : ResidueRing v m)) * ψ (c * rep v (u : ResidueRing v m))

/-- The finite Gauss sum does not depend on the choice of the representatives: any other choice $r(u)$ in the classes gives the same sum. -/
theorem gaussSumFinite_eq_sum_of_mk {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) (ψ : AddChar (v.adicCompletion K) ℂ)
    (d : ℤ) (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) {c : v.adicCompletion K}
    (hc : ‖c‖ ≤ q v ^ (d + m)) (r : (ResidueRing v m)ˣ → v.adicCompletionIntegers K)
    (hr : ∀ u, Ideal.Quotient.mk (higherIdeal v m) (r u) = u) :
    gaussSumFinite v χ ψ m c =
      ∑ u : (ResidueRing v m)ˣ, charExt χ (r u : v.adicCompletion K) *
        ψ (c * (r u : v.adicCompletion K)) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  have h : ‖((r u : v.adicCompletionIntegers K) : v.adicCompletion K) - rep v (u : ResidueRing v m)‖
      ≤ (q v)⁻¹ ^ m := (mk_eq_mk_iff v (r u) (lift v (u : ResidueRing v m))).1 (by rw [hr, mk_lift])
  rw [charExt_eq_of_norm_sub_le_pow v hχ hm (norm_rep_unit v hm u) h,
    addChar_mul_eq_of_norm_sub_le v ψ h1 hc h]

/-- The integral Gauss sum is $q^{-m}$ times the finite Gauss sum: $G(\chi, \psi, c) = q^{-m} \tau(\chi, \psi, c)$, if $\chi$ is trivial on $1 + \mathfrak{p}_v^m$ with $m \geq 1$, $\psi$ is trivial on $\{|x|_v \leq q^d\}$ and $|c|_v \leq q^{d + m}$. -/
theorem gaussSum_eq_gaussSumFinite {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) (ψ : AddChar (v.adicCompletion K) ℂ)
    (d : ℤ) (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1) {c : v.adicCompletion K}
    (hc : ‖c‖ ≤ q v ^ (d + m)) :
    gaussSum v χ ψ c = (((q v)⁻¹ ^ m : ℝ) : ℂ) * gaussSumFinite v χ ψ m c := by
  rw [gaussSum]
  exact setIntegral_sphere_eq_sum v hm _ fun x y hx hxy => by
    rw [charExt_eq_of_norm_sub_le_pow v hχ hm hx hxy, addChar_mul_eq_of_norm_sub_le v ψ h1 hc hxy]

/-- The absolute value of the finite Gauss sum: $|\tau(\chi, \psi, c)|^2 = q^a$, where $a = b + 1$ is the conductor exponent of $\chi$, $d$ is the conductor exponent of $\psi$ and $|c|_v = q^{a + d}$. -/
theorem norm_gaussSumFinite_sq {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    ‖gaussSumFinite v χ ψ (b + 1) c‖ ^ 2 = q v ^ (b + 1) := by
  have hq0 : 0 ≤ (q v)⁻¹ ^ (b + 1) := pow_nonneg (inv_nonneg.2 (q_pos v).le) _
  have hq : (q v)⁻¹ ^ (b + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero (q_pos v).ne')
  have h := norm_gaussSum_sq v hχ hχ' ψ d h1 h2 hc
  rw [gaussSum_eq_gaussSumFinite v hχ (Nat.succ_ne_zero b) ψ d h1 hc.le, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hq0, mul_pow, sq ((q v)⁻¹ ^ (b + 1)), mul_assoc] at h
  have key := mul_left_cancel₀ hq (h.trans (mul_one _).symm)
  rw [← inv_eq_of_mul_eq_one_right key, inv_pow, inv_inv]

/-- The product formula for finite Gauss sums: $\tau(\chi, \psi, c) \tau(\chi^{-1}, \psi, -c) = q^a$, where $a = b + 1$ is the conductor exponent of $\chi$ and $|c|_v = q^{a + d}$. -/
theorem gaussSumFinite_mul_gaussSumFinite_inv {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    gaussSumFinite v χ ψ (b + 1) c * gaussSumFinite v χ⁻¹ ψ (b + 1) (-c) =
      ((q v ^ (b + 1) : ℝ) : ℂ) := by
  have hq : (q v)⁻¹ ^ (b + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero (q_pos v).ne')
  have hX : (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq
  have h := gaussSum_mul_gaussSum_inv v hχ hχ' ψ d h1 h2 hc
  rw [gaussSum_eq_gaussSumFinite v hχ (Nat.succ_ne_zero b) ψ d h1 hc.le,
    gaussSum_eq_gaussSumFinite v (isTrivialOnHigherUnits_inv v hχ) (Nat.succ_ne_zero b) ψ d h1
      (by rw [norm_neg]; exact hc.le)] at h
  have key : (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) * (gaussSumFinite v χ ψ (b + 1) c *
      gaussSumFinite v χ⁻¹ ψ (b + 1) (-c)) = 1 :=
    mul_left_cancel₀ hX (by linear_combination h)
  rw [← inv_eq_of_mul_eq_one_right key, Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_inv,
    inv_pow, inv_inv]

/-- The classical normalization $c = \varpi^{-(a + d)}$, for which $\psi(c u) = \psi(u / \varpi^{a + d})$: then $|\tau(\chi, \psi, \varpi^{-(a + d)})|^2 = q^a$. -/
theorem norm_gaussSumFinite_uniformizer_sq {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1) :
    ‖gaussSumFinite v χ ψ (b + 1)
        ((localUniformizer K v : v.adicCompletion K) ^ (-(d + (b + 1 : ℕ))))‖ ^ 2 =
      q v ^ (b + 1) :=
  norm_gaussSumFinite_sq v hχ hχ' ψ d h1 h2 (norm_localUniformizer_zpow_neg v _)

/-! ### Ramified characters -/

/-- The character of $(\mathcal{O}_v / \mathfrak{p}_v^m)^\times$ that $\chi$ induces, if $\chi$ is trivial on $1 + \mathfrak{p}_v^m$ with $m \geq 1$. -/
noncomputable def residueChar (χ : (v.adicCompletion K)ˣ →* ℂˣ) {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) : (ResidueRing v m)ˣ →* ℂ where
  toFun u := charExt χ (rep v (u : ResidueRing v m))
  map_one' := by
    have h : ‖rep v ((1 : (ResidueRing v m)ˣ) : ResidueRing v m) - 1‖ ≤ (q v)⁻¹ ^ m := by
      have h' := (mk_eq_mk_iff v (lift v ((1 : (ResidueRing v m)ˣ) : ResidueRing v m)) 1).1
        (by rw [mk_lift, Units.val_one, map_one])
      rwa [OneMemClass.coe_one] at h'
    change charExt χ (rep v ((1 : (ResidueRing v m)ˣ) : ResidueRing v m)) = 1
    rw [charExt_eq_of_norm_sub_le_pow v hχ hm norm_one h,
      show (1 : v.adicCompletion K) = ((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) from rfl,
      charExt_units, map_one, Units.val_one]
  map_mul' u w := by
    change charExt χ (rep v ((u * w : (ResidueRing v m)ˣ) : ResidueRing v m)) =
      charExt χ (rep v (u : ResidueRing v m)) * charExt χ (rep v (w : ResidueRing v m))
    have hu := norm_rep_unit v hm u
    have hw := norm_rep_unit v hm w
    have hu0 : rep v (u : ResidueRing v m) ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
    have h : ‖rep v ((u * w : (ResidueRing v m)ˣ) : ResidueRing v m) -
        rep v (u : ResidueRing v m) * rep v (w : ResidueRing v m)‖ ≤ (q v)⁻¹ ^ m := by
      have h' := (mk_eq_mk_iff v (lift v ((u * w : (ResidueRing v m)ˣ) : ResidueRing v m))
        (lift v (u : ResidueRing v m) * lift v (w : ResidueRing v m))).1
        (by rw [mk_lift, map_mul, mk_lift, mk_lift, Units.val_mul])
      rwa [MulMemClass.coe_mul] at h'
    rw [charExt_eq_of_norm_sub_le_pow v hχ hm (by rw [norm_mul, hu, hw, one_mul]) h,
      charExt_mul χ hu0]
    congr 1
    simp [charExt, hu0]

/-- The value of the induced character on the class of a unit $w$ of $\mathcal{O}_v$ is $\chi(w)$. -/
theorem residueChar_mk {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) (w : (v.adicCompletion K)ˣ)
    (hw : ‖(w : v.adicCompletion K)‖ = 1) :
    residueChar v χ hχ hm (isUnit_mk_of_norm_eq_one v (m := m)
      ⟨w, mem_integers_of_norm_le_one v hw.le⟩ hw).unit = χ w := by
  change charExt χ (rep v ((isUnit_mk_of_norm_eq_one v (m := m)
      ⟨w, mem_integers_of_norm_le_one v hw.le⟩ hw).unit : ResidueRing v m)) = χ w
  have h : ‖rep v ((isUnit_mk_of_norm_eq_one v (m := m)
      ⟨w, mem_integers_of_norm_le_one v hw.le⟩ hw).unit : ResidueRing v m) - w‖ ≤ (q v)⁻¹ ^ m :=
    (mk_eq_mk_iff v _ ⟨w, mem_integers_of_norm_le_one v hw.le⟩).1
      (by rw [mk_lift, IsUnit.unit_spec])
  rw [charExt_eq_of_norm_sub_le_pow v hχ hm hw h, charExt_units]

/-- Orthogonality for a ramified character: if $\chi$ is trivial on $1 + \mathfrak{p}_v^m$ with $m \geq 1$ but not on $\mathcal{O}_v^\times$, then $\sum_{u \in (\mathcal{O}_v / \mathfrak{p}_v^m)^\times} \chi(u) = 0$. -/
theorem sum_charExt_rep_eq_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ m) (hm : m ≠ 0) (hχ0 : ¬ IsTrivialOnHigherUnits v χ 0) :
    ∑ u : (ResidueRing v m)ˣ, charExt χ (rep v (u : ResidueRing v m)) = 0 := by
  have hne : residueChar v χ hχ hm ≠ 1 := by
    intro h
    refine hχ0 fun w hw _ => ?_
    have h1 := residueChar_mk v hχ hm w hw
    rw [h, MonoidHom.one_apply] at h1
    exact Units.val_eq_one.1 h1.symm
  exact sum_hom_units_eq_zero (residueChar v χ hχ hm) hne

/-- For a ramified $\chi$, the integral of $\chi(x) |x|_v^s$ over each shell $\{|x|_v = r\}$ for $d^\times x$ is $0$. -/
theorem setIntegral_sphere_charExt_of_ramified {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ IsTrivialOnHigherUnits v χ 0) (r : ℝ) (s : ℂ) :
    ∫ x in sphere 0 r, charExt χ x * (‖x‖ : ℂ) ^ s ∂multHaar v = 0 := by
  simp only [IsTrivialOnHigherUnits, not_forall] at hχ
  obtain ⟨w, hw1, -, hχw⟩ := hχ
  refine setIntegral_multHaar_eq_zero_of_comp_mul v isClosed_sphere.measurableSet _ w.ne_zero
    (c := χ w) (fun x => by rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, norm_mul,
      hw1, one_mul]) (fun h => hχw (Units.val_eq_one.1 h)) fun x _ => ?_
  rw [charExt_mul χ w.ne_zero, Units.mk0_val, norm_mul, hw1, one_mul]
  ring

/-- For a ramified $\chi$, the zeta integral $Z(f, \chi, s)$ is $0$ for every $f$ that is invariant under $\mathcal{O}_v^\times$. So no such test function gives a nonzero local factor, and the local factor of a ramified character is $1$. -/
theorem zetaIntegral_eq_zero_of_ramified (f : v.adicCompletion K → ℂ)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : ¬ IsTrivialOnHigherUnits v χ 0)
    (hf : ∀ u x : v.adicCompletion K, ‖u‖ = 1 → f (u * x) = f x) (s : ℂ) :
    zetaIntegral v f χ s = 0 := by
  simp only [IsTrivialOnHigherUnits, not_forall] at hχ
  obtain ⟨w, hw1, -, hχw⟩ := hχ
  exact zetaIntegral_eq_zero_of_ne_one v f χ s w hw1 (fun x => hf w x hw1) hχw

/-! ### Hecke characters -/

/-- The finite component at $v$ of the idele attached to $u \in K_v^\times$ is $u$. -/
theorem ofAdicCompletion_apply_self (u : (v.adicCompletion K)ˣ) :
    ((IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).2 v = u := by
  classical
  change RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers K w) v
    (u : v.adicCompletion K) v = u
  convert RestrictedProduct.mulSingle_eq_same (fun w => HeightOneSpectrum.adicCompletionIntegers K w)
    v (u : v.adicCompletion K)

/-- The finite component at $w \neq v$ of the idele attached to $u \in K_v^\times$ is $1$. -/
theorem ofAdicCompletion_apply_of_ne (u : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) :
    ((IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).2 w = 1 := by
  classical
  change RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers K w) v
    (u : v.adicCompletion K) w = 1
  convert RestrictedProduct.mulSingle_eq_of_ne
    (fun w => HeightOneSpectrum.adicCompletionIntegers K w) (u : v.adicCompletion K) h

/-- Every Hecke character has a finite conductor exponent at $v$: the local component $\chi_v$ is trivial on $1 + \mathfrak{p}_v^m$ for some $m$. This follows from the continuity of $\chi$. -/
theorem exists_isTrivialOnHigherUnits (χ : HeckeCharacter K) :
    ∃ m, χ.IsTrivialOnHigherUnits v m := by
  obtain ⟨S, k, h⟩ := Langlands.HeckeRat.Top.exists_trivial_on_units K χ
  refine ⟨k, fun u hu hu1 => ?_⟩
  refine h (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) rfl (fun w => ?_) (fun w _ => ?_)
  · by_cases hw : w = v
    · subst hw
      rw [ofAdicCompletion_apply_self]
      exact hu
    · rw [ofAdicCompletion_apply_of_ne v u hw, map_one]
  · by_cases hw : w = v
    · subst hw
      rw [ofAdicCompletion_apply_self]
      exact hu1
    · rw [ofAdicCompletion_apply_of_ne v u hw, sub_self, map_zero]
      exact zero_le

/-- The local component $\chi_v$ is trivial on $1 + \mathfrak{p}_v^a$ for the conductor exponent $a$. -/
theorem isTrivialOnHigherUnits_conductorExponent (χ : HeckeCharacter K) :
    IsTrivialOnHigherUnits v (χ.finiteComponent v) (χ.conductorExponent v) :=
  (isTrivialOnHigherUnits_iff v χ _).1 (Nat.sInf_mem (s := {m | χ.IsTrivialOnHigherUnits v m}) (exists_isTrivialOnHigherUnits v χ))

/-- The conductor exponent of a character ramified at $v$ is at least $1$. -/
theorem conductorExponent_ne_zero (χ : HeckeCharacter K) (hχ : ¬ χ.IsUnramifiedAt v) :
    χ.conductorExponent v ≠ 0 := by
  intro h
  have h1 : χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) :=
    Nat.sInf_mem (s := {m | χ.IsTrivialOnHigherUnits v m}) (exists_isTrivialOnHigherUnits v χ)
  rw [h] at h1
  exact hχ h1

/-- The local component $\chi_v$ of a character ramified at $v$ is not trivial on $1 + \mathfrak{p}_v^{a - 1}$, where $a$ is the conductor exponent. -/
theorem not_isTrivialOnHigherUnits_conductorExponent_sub_one (χ : HeckeCharacter K)
    (hχ : ¬ χ.IsUnramifiedAt v) :
    ¬ IsTrivialOnHigherUnits v (χ.finiteComponent v) (χ.conductorExponent v - 1) := by
  rw [← isTrivialOnHigherUnits_iff]
  exact Nat.notMem_of_lt_sInf
    (Nat.sub_lt (Nat.pos_of_ne_zero (conductorExponent_ne_zero v χ hχ)) one_pos)

/-- The local factor of a Hecke character at a ramified place is $1$. -/
theorem localFactor_eq_one_of_not_isUnramifiedAt (χ : HeckeCharacter K)
    (hχ : ¬ χ.IsUnramifiedAt v) (s : ℂ) : χ.localFactor v s = 1 :=
  by simp [HeckeCharacter.localFactor, hχ]

/-- For a Hecke character $\chi$ ramified at $v$, the local component $\chi_v$ has sum $0$ over $(\mathcal{O}_v / \mathfrak{p}_v^a)^\times$, where $a$ is the conductor exponent. -/
theorem sum_finiteComponent_eq_zero (χ : HeckeCharacter K) (hχ : ¬ χ.IsUnramifiedAt v) :
    ∑ u : (ResidueRing v (χ.conductorExponent v))ˣ,
      charExt (χ.finiteComponent v) (rep v (u : ResidueRing v (χ.conductorExponent v))) = 0 :=
  sum_charExt_rep_eq_zero v (isTrivialOnHigherUnits_conductorExponent v χ)
    (conductorExponent_ne_zero v χ hχ) fun h => hχ ((isTrivialOnHigherUnits_iff v χ 0).2 h)

/-- The finite Gauss sum of a Hecke character at a ramified place. Let $a$ be the conductor exponent of $\chi$ at $v$ and let $\psi$ have conductor exponent $d$. If $|c|_v = q^{a + d}$, then $|\tau(\chi_v, \psi, c)|^2 = q^a$. -/
theorem norm_gaussSumFinite_finiteComponent_sq (χ : HeckeCharacter K) (hχ : ¬ χ.IsUnramifiedAt v)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + χ.conductorExponent v)) :
    ‖gaussSumFinite v (χ.finiteComponent v) ψ (χ.conductorExponent v) c‖ ^ 2 =
      q v ^ χ.conductorExponent v := by
  have ht := isTrivialOnHigherUnits_conductorExponent v χ
  have hnt := not_isTrivialOnHigherUnits_conductorExponent_sub_one v χ hχ
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (conductorExponent_ne_zero v χ hχ)
  rw [hb] at ht hc ⊢
  rw [hb, Nat.succ_sub_one] at hnt
  exact norm_gaussSumFinite_sq v ht hnt ψ d h1 h2 hc

/-! ### The local epsilon factor -/

/-- The ramified epsilon factor in terms of the finite Gauss sum: $\varepsilon(s, \chi, \psi) = \chi(c)^{-1} (q^{a + d})^{1 - s} q^{-a} \tau(\chi^{-1}, \psi, c)$ for $|c|_v = q^{a + d}$. -/
theorem epsilonRamified_eq_gaussSumFinite {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ) :
    epsilonRamified v χ ψ hc0 s = ((χ (Units.mk0 c hc0) : ℂˣ) : ℂ)⁻¹ *
      ((q v ^ (d + (b + 1 : ℕ)) : ℝ) : ℂ) ^ (1 - s) * (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) *
        gaussSumFinite v χ⁻¹ ψ (b + 1) c := by
  rw [epsilonRamified, gaussSum_eq_gaussSumFinite v (isTrivialOnHigherUnits_inv v hχ)
    (Nat.succ_ne_zero b) ψ d h1 hc.le, hc]
  ring

/-- The ramified epsilon factor in the classical normalization: $\varepsilon(s, \chi, \psi) = \chi(c)^{-1} q^{(a + d)(1/2 - s)} q^{d/2} \tau(\chi^{-1}, \psi, c) / q^{a/2}$, where $a = b + 1$ is the conductor exponent of $\chi$ and $|c|_v = q^{a + d}$. The factor $q^{d/2}$ comes from the measure $du$ with $\int_{\mathcal{O}_v} du = 1$, and $|\tau / q^{a/2}| = 1$. -/
theorem epsilonRamified_eq_cpow {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ) :
    epsilonRamified v χ ψ hc0 s = ((χ (Units.mk0 c hc0) : ℂˣ) : ℂ)⁻¹ *
      ((q v : ℝ) : ℂ) ^ (((d + (b + 1 : ℕ) : ℤ) : ℂ) * (1 / 2 - s)) *
        ((q v : ℝ) : ℂ) ^ ((d : ℂ) / 2) *
          (gaussSumFinite v χ⁻¹ ψ (b + 1) c / ((q v : ℝ) : ℂ) ^ (((b + 1 : ℕ) : ℂ) / 2)) := by
  have hQ : ((q v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (q_pos v).ne'
  have e1 : ((q v ^ (d + (b + 1 : ℕ)) : ℝ) : ℂ) ^ (1 - s) =
      ((q v : ℝ) : ℂ) ^ (((d + (b + 1 : ℕ) : ℤ) : ℂ) * (1 - s)) := by
    rw [← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg (q_pos v).le, Complex.ofReal_intCast]
  have e2 : (((q v)⁻¹ ^ (b + 1) : ℝ) : ℂ) = ((q v : ℝ) : ℂ) ^ (-((b + 1 : ℕ) : ℂ)) := by
    rw [Complex.cpow_neg, Complex.cpow_natCast, Complex.ofReal_pow, Complex.ofReal_inv, inv_pow]
  have e3 : ((q v : ℝ) : ℂ) ^ (((d + (b + 1 : ℕ) : ℤ) : ℂ) * (1 - s)) *
      ((q v : ℝ) : ℂ) ^ (-((b + 1 : ℕ) : ℂ)) =
      ((q v : ℝ) : ℂ) ^ (((d + (b + 1 : ℕ) : ℤ) : ℂ) * (1 / 2 - s)) *
        ((q v : ℝ) : ℂ) ^ ((d : ℂ) / 2) * ((q v : ℝ) : ℂ) ^ (-(((b + 1 : ℕ) : ℂ) / 2)) := by
    rw [← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
    congr 1
    push_cast
    ring
  rw [epsilonRamified_eq_gaussSumFinite v hχ ψ d h1 hc0 hc, e1, e2,
    div_eq_mul_inv (gaussSumFinite v χ⁻¹ ψ (b + 1) c), ← Complex.cpow_neg]
  linear_combination (((χ (Units.mk0 c hc0) : ℂˣ) : ℂ)⁻¹ * gaussSumFinite v χ⁻¹ ψ (b + 1) c) * e3

/-- The local functional equation at a ramified place with the finite Gauss sum. For Tate's test function $f = \mathbf{1}_{1 + \mathfrak{p}_v^a}$, which is $\chi^{-1} \mathbf{1}_{1 + \mathfrak{p}_v^a}$ because $\chi = 1$ there,
$$Z(\hat{f}, \chi^{-1}, 1 - s) = \chi(c)^{-1} q^{(a + d)(1/2 - s)} q^{d/2} \frac{\tau(\chi^{-1}, \psi, c)}{q^{a/2}} Z(f, \chi, s),$$
where $a = b + 1$ is the conductor exponent of $\chi$, $d$ is the conductor exponent of $\psi$ and $|c|_v = q^{a + d}$. It holds in the region $|\chi^{-1}(\varpi)| < q^{\mathrm{Re}(1 - s)}$ of convergence. -/
theorem localFunctionalEquation_ramified_gaussSumFinite {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc0 : c ≠ 0) (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) (s : ℂ)
    (hs : ‖(χ⁻¹ (localUniformizer K v) : ℂ)‖ < q v ^ (1 - s).re) :
    zetaIntegral v (fourier v ψ (testFunction v (b + 1))) χ⁻¹ (1 - s) =
      ((χ (Units.mk0 c hc0) : ℂˣ) : ℂ)⁻¹ *
        ((q v : ℝ) : ℂ) ^ (((d + (b + 1 : ℕ) : ℤ) : ℂ) * (1 / 2 - s)) *
          ((q v : ℝ) : ℂ) ^ ((d : ℂ) / 2) *
            (gaussSumFinite v χ⁻¹ ψ (b + 1) c / ((q v : ℝ) : ℂ) ^ (((b + 1 : ℕ) : ℂ) / 2)) *
              zetaIntegral v (testFunction v (b + 1)) χ s := by
  rw [localFunctionalEquation_ramified v hχ hχ' ψ d h1 h2 hc0 hc s hs,
    epsilonRamified_eq_cpow v hχ ψ d h1 hc0 hc s]

/-- The normalized Gauss sum $\tau(\chi^{-1}, \psi, c) / q^{a/2}$ in the epsilon factor has absolute value $1$. -/
theorem norm_gaussSumFinite_div_eq_one {χ : (v.adicCompletion K)ˣ →* ℂˣ} {b : ℕ}
    (hχ : IsTrivialOnHigherUnits v χ (b + 1)) (hχ' : ¬ IsTrivialOnHigherUnits v χ b)
    (ψ : AddChar (v.adicCompletion K) ℂ) (d : ℤ)
    (h1 : ∀ x : v.adicCompletion K, ‖x‖ ≤ q v ^ d → ψ x = 1)
    (h2 : ∃ x : v.adicCompletion K, ‖x‖ ≤ q v ^ (d + 1) ∧ ψ x ≠ 1)
    {c : v.adicCompletion K} (hc : ‖c‖ = q v ^ (d + (b + 1 : ℕ))) :
    ‖gaussSumFinite v χ⁻¹ ψ (b + 1) c / ((q v : ℝ) : ℂ) ^ (((b + 1 : ℕ) : ℂ) / 2)‖ = 1 := by
  have hn := norm_gaussSumFinite_sq v (isTrivialOnHigherUnits_inv v hχ)
    (fun h => hχ' ((isTrivialOnHigherUnits_inv_iff v).1 h)) ψ d h1 h2 hc
  have hq := q_pos v
  have hd : ‖((q v : ℝ) : ℂ) ^ (((b + 1 : ℕ) : ℂ) / 2)‖ = q v ^ (((b + 1 : ℕ) : ℝ) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
    congr 1
    simp
  have hs : (q v ^ (((b + 1 : ℕ) : ℝ) / 2)) ^ 2 = q v ^ (b + 1) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hpos : 0 < q v ^ (((b + 1 : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos hq _
  rw [norm_div, hd, div_eq_one_iff_eq hpos.ne']
  have h0 := norm_nonneg (gaussSumFinite v χ⁻¹ ψ (b + 1) c)
  nlinarith [sq_nonneg (‖gaussSumFinite v χ⁻¹ ψ (b + 1) c‖ - q v ^ (((b + 1 : ℕ) : ℝ) / 2)),
    sq_nonneg (‖gaussSumFinite v χ⁻¹ ψ (b + 1) c‖ + q v ^ (((b + 1 : ℕ) : ℝ) / 2))]

end Langlands.Tate.NonArchimedean
