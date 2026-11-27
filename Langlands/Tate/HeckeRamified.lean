/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeUnramified
import Langlands.Tate.LocalRamified

/-!
# Hecke characters of ray class type

Let $K$ be a number field. A Hecke character $\chi$ is of ray class type if it is trivial on the image of $K_v^\times$ for each infinite place $v$. There is no condition at the finite places, so $\chi$ can be ramified at a finite set of finite places. These characters are the characters of finite order of the ray class groups of $K$. The characters of class group type of `Langlands.Tate.HeckeUnramified` are the characters of ray class type that are unramified at every finite place.

This file proves the parts of the statement `Langlands.HeckeFunctionalEquationAt` for a character of ray class type that do not need the functional equation itself. These are the size condition with $\sigma = 0$, the archimedean parameters, the conductor and its inverse, reciprocity on the principal ideals, and the Dirichlet series of $L(s, \chi)$ for $\mathrm{Re}\, s > 1$. The meromorphic continuation and the functional equation of $\Lambda(s, \chi)$ for a ramified $\chi$ are not proved here.

## Main definitions

* `Langlands.Tate.ramifiedSet`: the finite set of the finite places at which $\chi$ is ramified.
* `Langlands.Tate.IsRayClassType`: the character is trivial at each infinite place.
* `Langlands.Tate.normChar`: the Hecke character $x \mapsto |\chi(x)|$.
* `Langlands.Tate.coprimeIndicator`: the indicator function of the ideals prime to a finite set of primes.
* `Langlands.Tate.rayWeight`: the weight $I \mapsto \chi(I) N(I)^{-s}$ of the $L$-series, with $\chi(I) = 0$ for $I$ not prime to the conductor.

## Main results

* `norm_finiteComponent_of_valued_eq_one`: each local component of each Hecke character has absolute value $1$ on $\mathcal{O}_v^\times$.
* `finite_setOf_not_isUnramifiedAt`: each Hecke character is ramified at finitely many finite places.
* `conductorExponent_eq_zero_iff`, `conductor_eq_prod`, `conductor_inv`: the conductor is $\prod_{v} \mathfrak{p}_v^{a_v}$ over the ramified places, with $a_v \geq 1$, and $\chi^{-1}$ has the same conductor.
* `IsRayClassType.ideleChar_eq_prod`: $\chi(x) = \prod_{v \in S} \chi_v(x_v)$ if $S$ contains the ramified places and $x_v$ is a unit for $v \notin S$.
* `IsRayClassType.norm_apply` and `IsRayClassType.norm_eq_ideleNorm_rpow`: $|\chi(x)| = 1 = \|x\|^0$.
* `IsRayClassType.isArchimedeanParameter`: the archimedean parameters are $n = 0$ and $t = 0$.
* `IsRayClassType.idealChar_toPrincipalIdeal`: the ideal character is trivial on $(x)$ if $v(x - 1) \geq a_v$ at each ramified place $v$.
* `IsRayClassType.hasProd_localFactor` and `IsRayClassType.finiteLFunction_eq`: for $\mathrm{Re}\, s > 1$, $L(s, \chi) = \prod_v L_v(s, \chi) = \sum_{(I, \mathfrak{f}) = 1} \chi(I) N(I)^{-s}$.

## Proofs

Each Hecke character is trivial on $1 + \mathfrak{p}_v^k$ at each finite place $v$ for one $k$, and unramified outside a finite set, by `Langlands.HeckeRat.Top.exists_trivial_on_units`. A unit $y$ of $\mathcal{O}_v$ has a power $y^N$ in $1 + \mathfrak{p}_v^k$, because $(\mathcal{O}_v / \mathfrak{p}_v^k)^\times$ is finite, so $\chi_v(y)^N = 1$ and $|\chi_v(y)| = 1$. Then $|\chi|$ is a character of class group type, and `Langlands.Tate.IsClassType.norm_apply` gives $|\chi| = 1$. The product formula for $\chi(x)$ is the proof of `Langlands.Tate.IsClassType.ideleChar_eq_prod`, with the ramified places added to $S$. For reciprocity, apply the product formula to the principal idele of $x$: the factors at the ramified places are $1$ because $x \in 1 + \mathfrak{p}_v^{a_v}$. For the Euler product, the local factor at a ramified place is $1$, which is the factor $(1 - 0)^{-1}$ of the weight that is $0$ on the ideals divisible by a ramified prime.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen.
* J. Neukirch, Algebraic number theory, chapter VI, section 1, and chapter VII, section 6.
-/

namespace Langlands.Tate

open NumberField InfinitePlace Complex IsDedekindDomain Filter Topology

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

section Local

/-- The local component of a Hecke character has absolute value $1$ on the units of $\mathcal{O}_v$. -/
theorem norm_finiteComponent_of_valued_eq_one (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) (hy : Valued.v (y : v.adicCompletion K) = 1) :
    ‖(χ.finiteComponent v y : ℂ)‖ = 1 := by
  obtain ⟨m, hm⟩ := NonArchimedean.exists_isTrivialOnHigherUnits v χ
  have hy1 : ‖(y : v.adicCompletion K)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.2 hy
  let a : v.adicCompletionIntegers K :=
    ⟨y, NonArchimedean.mem_integers_of_norm_le_one v hy1.le⟩
  obtain ⟨u, hu⟩ := NonArchimedean.isUnit_mk_of_norm_eq_one v (m := m) a hy1
  have hN : 0 < orderOf (u : (NonArchimedean.ResidueRing v m)ˣ) := orderOf_pos u
  have hmk : Ideal.Quotient.mk (NonArchimedean.higherIdeal v m) (a ^ orderOf u) =
      Ideal.Quotient.mk (NonArchimedean.higherIdeal v m) 1 := by
    rw [map_pow, ← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [NonArchimedean.mk_eq_mk_iff] at hmk
  have h1 : χ.finiteComponent v (y ^ orderOf u) = 1 := by
    refine hm _ (by rw [Units.val_pow_eq_pow_val, map_pow, hy, one_pow]) ?_
    rw [← NonArchimedean.norm_le_inv_q_pow_iff]
    simpa [a] using hmk
  rw [map_pow] at h1
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    hN.ne'

/-- If $\chi$ is unramified at $v$, then $\chi_v$ is trivial on the units of $\mathcal{O}_v$. -/
theorem finiteComponent_eq_one_of_isUnramifiedAt {χ : HeckeCharacter K}
    {v : HeightOneSpectrum (𝓞 K)} (hv : χ.IsUnramifiedAt v) {y : (v.adicCompletion K)ˣ}
    (hy : Valued.v (y : v.adicCompletion K) = 1) : χ.finiteComponent v y = 1 :=
  hv y hy (by
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (Valuation.map_sub _ _ _).trans (max_le hy.le (by simp)))

/-- A Hecke character is unramified at all finite places outside a finite set. -/
theorem finite_setOf_not_isUnramifiedAt (χ : HeckeCharacter K) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ χ.IsUnramifiedAt v}.Finite := by
  obtain ⟨S, k, h⟩ := Langlands.HeckeRat.Top.exists_trivial_on_units K χ
  refine S.finite_toSet.subset fun v hv => ?_
  by_contra hS
  refine hv fun u hu _ => h (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) rfl (fun w => ?_)
    (fun w hw => ?_)
  · by_cases hw : w = v
    · subst hw
      rw [NonArchimedean.ofAdicCompletion_apply_self]
      exact hu
    · rw [NonArchimedean.ofAdicCompletion_apply_of_ne v u hw, map_one]
  · have hwv : w ≠ v := fun h => hS (h ▸ hw)
    rw [NonArchimedean.ofAdicCompletion_apply_of_ne v u hwv, sub_self, map_zero]
    exact zero_le

/-- If $\chi$ is unramified at $v$, then $\chi_v(y) = \chi_v(\varpi_v)^{m}$, where $|y|_v = \exp(-m)$. -/
theorem finiteComponent_eq_zpow_of_isUnramifiedAt {χ : HeckeCharacter K}
    {v : HeightOneSpectrum (𝓞 K)} (hv : χ.IsUnramifiedAt v) (y : (v.adicCompletion K)ˣ) :
    χ.finiteComponent v y =
      primeValue χ v ^ (-WithZero.log (Valued.v (y : v.adicCompletion K))) := by
  set n := WithZero.log (Valued.v (y : v.adicCompletion K)) with hn
  have hy0 : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have h1 : Valued.v ((y * localUniformizer K v ^ n : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, valued_localUniformizer,
      ← WithZero.exp_log hy0, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← hn]
    simp
  have h2 := finiteComponent_eq_one_of_isUnramifiedAt hv h1
  rw [map_mul, map_zpow] at h2
  rw [zpow_neg, primeValue]
  exact eq_inv_of_mul_eq_one_left h2

/-- The character $\chi^{-1}$ is trivial on $1 + \mathfrak{p}_v^m$ if and only if $\chi$ is. -/
theorem isTrivialOnHigherUnits_inv_iff {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)}
    {m : ℕ} : χ⁻¹.IsTrivialOnHigherUnits v m ↔ χ.IsTrivialOnHigherUnits v m := by
  refine ⟨fun h x hx hx1 => ?_, fun h x hx hx1 => ?_⟩
  · have := h x hx hx1
    rwa [finiteComponent_inv, inv_eq_one] at this
  · rw [finiteComponent_inv, h x hx hx1, inv_one]

/-- The conductor exponent of $\chi^{-1}$ at $v$ is the conductor exponent of $\chi$. -/
theorem conductorExponent_inv (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ⁻¹.conductorExponent v = χ.conductorExponent v := by
  simp only [HeckeCharacter.conductorExponent, isTrivialOnHigherUnits_inv_iff]

/-- The conductor of $\chi^{-1}$ is the conductor of $\chi$. -/
theorem conductor_inv (χ : HeckeCharacter K) : χ⁻¹.conductor = χ.conductor := by
  simp only [HeckeCharacter.conductor, conductorExponent_inv]

/-- The conductor exponent of $\chi$ at $v$ is $0$ if and only if $\chi$ is unramified at $v$. -/
theorem conductorExponent_eq_zero_iff (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.conductorExponent v = 0 ↔ χ.IsUnramifiedAt v := by
  refine ⟨fun h => ?_, fun h => Nat.sInf_eq_zero.mpr (Or.inl h)⟩
  have := Nat.sInf_mem (s := {m | χ.IsTrivialOnHigherUnits v m}) (NonArchimedean.exists_isTrivialOnHigherUnits v χ)
  change χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) at this
  rwa [h] at this

end Local

section RayClass

/-- The finite set of the finite places at which $\chi$ is ramified. -/
noncomputable def ramifiedSet (χ : HeckeCharacter K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_setOf_not_isUnramifiedAt χ).toFinset

/-- A finite place is in `ramifiedSet χ` if and only if $\chi$ is ramified at it. -/
theorem mem_ramifiedSet {χ : HeckeCharacter K} {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ ramifiedSet χ ↔ ¬ χ.IsUnramifiedAt v := by
  simp [ramifiedSet]

/-- The conductor is $\mathfrak{f}_\chi = \prod_{v} \mathfrak{p}_v^{a_v}$, where $v$ runs over the finite set of the ramified places and $a_v \geq 1$. -/
theorem conductor_eq_prod (χ : HeckeCharacter K) :
    χ.conductor = ∏ v ∈ ramifiedSet χ, v.asIdeal ^ χ.conductorExponent v := by
  rw [HeckeCharacter.conductor]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  rw [Finset.mem_coe, mem_ramifiedSet, ← conductorExponent_eq_zero_iff]
  exact fun h => hv (by simp only [h, pow_zero])

/-- A Hecke character of ray class type: it is trivial on the image of $K_v^\times$ for each infinite place $v$. There is no condition at the finite places, so $\chi$ can be ramified at finitely many of them. These characters are the characters of the ray class groups of $K$. -/
structure IsRayClassType (χ : HeckeCharacter K) : Prop where
  /-- The character is trivial at each infinite place. -/
  trivial_inf : ∀ (w : InfinitePlace K) (y : w.Completionˣ), χ.infiniteComponent w y = 1

variable {χ : HeckeCharacter K}

/-- A character of class group type is of ray class type. -/
theorem IsClassType.isRayClassType (hχ : IsClassType χ) : IsRayClassType χ :=
  ⟨hχ.trivial_inf⟩

/-- If $\chi$ is of ray class type, then $\chi^{-1}$ is of ray class type. -/
theorem IsRayClassType.inv (hχ : IsRayClassType χ) : IsRayClassType χ⁻¹ :=
  ⟨fun w y => by rw [infiniteComponent_inv, hχ.trivial_inf w y, inv_one]⟩

/-- A character of ray class type that is unramified at every finite place is of class group type. -/
theorem IsRayClassType.isClassType (hχ : IsRayClassType χ) (h : ∀ v, χ.IsUnramifiedAt v) :
    IsClassType χ :=
  ⟨h, hχ.trivial_inf⟩

/-- A character of ray class type is trivial on the infinite part of an idele. -/
theorem IsRayClassType.ideleChar_infinitePart (hχ : IsRayClassType χ) (x : IdeleGroup (𝓞 K) K) :
    ideleChar χ (infinitePart x) = 1 := by
  rw [infinitePart, map_prod]
  exact Finset.prod_eq_one fun w _ => hχ.trivial_inf w _

/-- Let $\chi$ be of ray class type and let $S$ be a finite set of finite places that contains the ramified places. For an idele $x$ whose components outside $S$ are units, $\chi(x) = \prod_{v \in S} \chi_v(x_v)$. -/
theorem IsRayClassType.ideleChar_eq_prod (hχ : IsRayClassType χ) (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, Valued.v ((ideleFin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1)
    (hR : ∀ v ∉ S, χ.IsUnramifiedAt v) :
    ideleChar χ x = ∏ v ∈ S, χ.finiteComponent v (ideleFin v x) := by
  classical
  obtain ⟨T, k, hT⟩ := HeckeRat.Top.exists_trivial_on_units K χ
  set U := S ∪ T with hU
  set A := infinitePart x with hA
  set P : IdeleGroup (𝓞 K) K :=
    ∏ v ∈ U, IdeleGroup.ofAdicCompletion (𝓞 K) K v (ideleFin v x) with hP
  have hPinf : ∀ w, ideleInf w P = 1 := fun w => by
    rw [hP, map_prod]
    exact Finset.prod_eq_one fun v _ => ideleInf_ofAdicCompletion w v _
  have hPfin : ∀ v, ideleFin v P = if v ∈ U then ideleFin v x else 1 := by
    intro v
    rw [hP, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single v (fun w _ hw => ideleFin_ofAdicCompletion_of_ne hw _)
        (fun h => absurd hv h), ideleFin_ofAdicCompletion_self]
    · exact Finset.prod_eq_one fun w hw =>
        ideleFin_ofAdicCompletion_of_ne (ne_of_mem_of_not_mem hw hv) _
  set z : IdeleGroup (𝓞 K) K := x * A⁻¹ * P⁻¹ with hz
  have hzinf : ∀ w, ideleInf w z = 1 := fun w => by
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, ideleInf_infinitePart, hPinf]
    simp
  have hzfin : ∀ v, ideleFin v z = if v ∈ U then 1 else ideleFin v x := fun v => by
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, ideleFin_infinitePart, hPfin]
    split_ifs <;> simp
  have hz1 : ideleChar χ z = 1 := by
    refine hT z ?_ (fun v => ?_) (fun v hv => ?_)
    · funext w
      exact congrArg Units.val (hzinf w)
    · rw [← coe_ideleFin, hzfin]
      split_ifs with hv
      · simp
      · exact hS v fun h => hv (Finset.mem_union_left _ h)
    · rw [← coe_ideleFin, hzfin, ite_eq_left (Finset.mem_union_right _ hv)]
      simp
  have hxz : x = z * A * P := by
    rw [hz, mul_right_comm _ P⁻¹ A, inv_mul_cancel_right, inv_mul_cancel_right]
  rw [show ideleChar χ x = ideleChar χ z * ideleChar χ A * ideleChar χ P by
      rw [← map_mul, ← map_mul, ← hxz],
    hz1, one_mul, hA, hχ.ideleChar_infinitePart, one_mul, hP, map_prod]
  simp only [ideleChar_ofAdicCompletion]
  rw [hU]
  exact (Finset.prod_subset Finset.subset_union_left fun v _ hv =>
    finiteComponent_eq_one_of_isUnramifiedAt (hR v hv) (hS v hv)).symm

end RayClass

section Unitary

/-- The continuous homomorphism $z \mapsto |z|$ of $\mathbb{C}^\times$ to itself. -/
noncomputable def normUnits : ContinuousMonoidHom ℂˣ ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ : ℝ) : ℂ) (by simp)
  map_one' := by ext; simp
  map_mul' z w := by ext; simp
  continuous_toFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)
    · have h : (fun z : ℂˣ => ((Units.mk0 ((‖(z : ℂ)‖ : ℝ) : ℂ) (by simp))⁻¹ : ℂˣ).val) =
          fun z => ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := by
        funext z
        simp
      rw [h]
      exact Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_coe_inv)

/-- The value of `normUnits` at $z$ is $|z|$. -/
theorem coe_normUnits (z : ℂˣ) : (normUnits z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

/-- The Hecke character $x \mapsto |\chi(x)|$. -/
noncomputable def normChar (χ : HeckeCharacter K) : HeckeCharacter K :=
  normUnits.comp χ

variable {χ : HeckeCharacter K}

/-- If $\chi$ is of ray class type, then $|\chi|$ is of class group type. -/
theorem IsRayClassType.isClassType_normChar (hχ : IsRayClassType χ) : IsClassType (normChar χ) where
  unramified v y hy _ := by
    refine Units.ext ?_
    change ((‖(χ.finiteComponent v y : ℂ)‖ : ℝ) : ℂ) = 1
    rw [norm_finiteComponent_of_valued_eq_one χ v y hy, Complex.ofReal_one]
  trivial_inf w y := by
    refine Units.ext ?_
    change ((‖(χ.infiniteComponent w y : ℂ)‖ : ℝ) : ℂ) = 1
    rw [hχ.trivial_inf w y]
    simp

/-- **Unitarity.** A character of ray class type has absolute value $1$: $|\chi(x)| = 1$ for each idele $x$. -/
theorem IsRayClassType.norm_apply (hχ : IsRayClassType χ) (x : IdeleGroup (𝓞 K) K) :
    ‖(χ (x : IdeleClassGroup (𝓞 K) K) : ℂ)‖ = 1 := by
  have h := hχ.isClassType_normChar.norm_apply x
  change ‖((‖(χ (x : IdeleClassGroup (𝓞 K) K) : ℂ)‖ : ℝ) : ℂ)‖ = 1 at h
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_norm] at h

/-- For a character of ray class type, $|\chi_v(\varpi_v)| = 1$ at each finite place $v$. -/
theorem IsRayClassType.norm_primeValue (hχ : IsRayClassType χ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(primeValue χ v : ℂ)‖ = 1 :=
  hχ.norm_apply (IdeleGroup.ofAdicCompletion (𝓞 K) K v (localUniformizer K v))

/-- For a character of ray class type, the ideal character has absolute value $1$. -/
theorem IsRayClassType.norm_idealChar (hχ : IsRayClassType χ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ‖(idealChar χ I : ℂ)‖ = 1 := by
  rw [idealChar_apply, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_mulSupport_zpow_count (primeValue χ) (I : FractionalIdeal (𝓞 K)⁰ K)).toFinset)
    (by simp), Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, hχ.norm_primeValue, one_zpow]

/-- **The archimedean parameters.** The archimedean parameters of a character of ray class type are $n = 0$ and $t = 0$. -/
theorem IsRayClassType.isArchimedeanParameter (hχ : IsRayClassType χ) {v : InfinitePlace K}
    {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v n t) : n = 0 ∧ t = 0 :=
  eq_zero_of_forall_param_eq_one h.isReal fun x => by
    rw [← h.eq x, hχ.trivial_inf v x, Units.val_one]

/-- **The size condition of the functional equation.** A character of ray class type satisfies $|\chi(x)| = \|x\|^{\sigma}$ with $\sigma = 0$. -/
theorem IsRayClassType.norm_eq_ideleNorm_rpow (hχ : IsRayClassType χ) (x : IdeleGroup (𝓞 K) K) :
    ‖(χ x : ℂ)‖ = ideleNorm K x ^ (0 : ℝ) := by
  rw [Real.rpow_zero]
  exact hχ.norm_apply x

end Unitary

section Reciprocity

variable {χ : HeckeCharacter K}

/-- **Reciprocity.** Let $\chi$ be of ray class type with conductor $\mathfrak{f} = \prod_v \mathfrak{p}_v^{a_v}$. If $x \in K^\times$ satisfies $v(x - 1) \geq a_v$ at each ramified place $v$, then the ideal character of $\chi$ is trivial on the principal ideal $(x)$. So the ideal character is a character of the ray class group modulo $\mathfrak{f}$. -/
theorem IsRayClassType.idealChar_toPrincipalIdeal (hχ : IsRayClassType χ) (x : Kˣ)
    (hx : ∀ v ∈ ramifiedSet χ, Valued.v (algebraMap K (v.adicCompletion K) (x : K) - 1) ≤
      WithZero.exp (-(χ.conductorExponent v : ℤ))) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  classical
  have hfin := Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = WithZero.exp
          (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) :=
    fun v => by rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count]
  have hunit : ∀ v ∈ ramifiedSet χ,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    have ha : χ.conductorExponent v ≠ 0 :=
      fun h => mem_ramifiedSet.1 hv ((conductorExponent_eq_zero_iff χ v).1 h)
    have hlt : Valued.v (algebraMap K (v.adicCompletion K) (x : K) - 1) < Valued.v
        (1 : v.adicCompletion K) := by
      rw [map_one]
      refine (hx v hv).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h := Valuation.map_add_eq_of_lt_left Valued.v hlt
    rwa [add_sub_cancel, map_one] at h
  have hcount : ∀ v ∈ ramifiedSet χ,
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 :=
    fun v hv => by
      have h := (hval v).symm.trans (hunit v hv)
      rw [← WithZero.exp_zero] at h
      exact neg_eq_zero.1 (WithZero.exp_injective h)
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
  · refine (Finset.prod_congr rfl fun v _ => ?_).trans h.symm
    by_cases hv : v ∈ ramifiedSet χ
    · rw [hcount v hv, zpow_zero]
      have ht : χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) :=
        Nat.sInf_mem (s := {m | χ.IsTrivialOnHigherUnits v m}) (NonArchimedean.exists_isTrivialOnHigherUnits v χ)
      refine (ht _ (hunit v hv) ?_).symm
      rw [ideleFin_unitEmbedding]
      exact hx v hv
    · rw [finiteComponent_eq_zpow_of_isUnramifiedAt (not_not.1 (mt mem_ramifiedSet.2 hv)), hval,
        WithZero.log_exp, neg_neg]
  · intro v hv
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl fun h0 => hv (by simp only [h0, zpow_zero])

end Reciprocity

section Euler

open scoped Classical

variable {χ : HeckeCharacter K}

/-- The indicator function of the nonzero ideals prime to each $\mathfrak{p}_v$ with $v \in R$, as a homomorphism of monoids. -/
noncomputable def coprimeIndicator (R : Finset (HeightOneSpectrum (𝓞 K))) :
    (Ideal (𝓞 K))⁰ →* ℂ where
  toFun I := if ∀ v ∈ R, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) then 1 else 0
  map_one' := by
    refine ite_eq_left fun v _ h => v.isPrime.ne_top (eq_top_iff.2 (Ideal.dvd_iff_le.1 ?_))
    rw [OneMemClass.coe_one, Ideal.one_eq_top] at h
    exact h
  map_mul' I J := by
    have key : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ ((I * J : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K)) ↔ v.asIdeal ∣ (I : Ideal (𝓞 K)) ∨ v.asIdeal ∣ (J : Ideal (𝓞 K)) :=
      fun v => by
        simp only [Submonoid.coe_mul, Ideal.dvd_iff_le]
        exact v.isPrime.mul_le
    by_cases hI : ∀ v ∈ R, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K))
    · by_cases hJ : ∀ v ∈ R, ¬ v.asIdeal ∣ (J : Ideal (𝓞 K))
      · rw [ite_eq_left fun v hv => by rw [key]; exact not_or.2 ⟨hI v hv, hJ v hv⟩, ite_eq_left hI,
          ite_eq_left hJ, mul_one]
      · obtain ⟨v, hv, h⟩ : ∃ v ∈ R, v.asIdeal ∣ (J : Ideal (𝓞 K)) := by
          push Not at hJ
          exact hJ
        rw [ite_eq_right fun h' => h' v hv ((key v).2 (Or.inr h)), ite_eq_right hJ, mul_zero]
    · obtain ⟨v, hv, h⟩ : ∃ v ∈ R, v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
        push Not at hI
        exact hI
      rw [ite_eq_right fun h' => h' v hv ((key v).2 (Or.inl h)), ite_eq_right hI, zero_mul]

/-- The weight $I \mapsto \chi(I) N(I)^{-s}$ of the $L$-series of $\chi$. Here $\chi(I)$ is the ideal character for $I$ prime to the ramified places, and $\chi(I) = 0$ for the other $I$. -/
noncomputable def rayWeight (χ : HeckeCharacter K) (s : ℂ) : (Ideal (𝓞 K))⁰ →* ℂ :=
  coprimeIndicator (ramifiedSet χ) *
    (Units.coeHom ℂ).comp ((idealChar χ).comp (FractionalIdeal.mk0 K)) *
    (normCpow K s).comp (Submonoid.subtype _)

/-- The value of the weight at $I$. -/
theorem rayWeight_apply (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    rayWeight χ s I =
      (if ∀ v ∈ ramifiedSet χ, ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) then 1 else 0) *
        (idealChar χ (FractionalIdeal.mk0 K I) : ℂ) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) := rfl

/-- For a character of ray class type, $|\chi(I) N(I)^{-s}| \leq |N(I)^{-s}|$. -/
theorem IsRayClassType.norm_rayWeight_le (hχ : IsRayClassType χ) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖rayWeight χ s I‖ ≤ ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖ := by
  rw [rayWeight_apply, norm_mul, norm_mul, hχ.norm_idealChar, mul_one]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  split_ifs <;> simp

/-- The weight is $0$ at a ramified prime. -/
theorem rayWeight_primeNZ_of_mem (s : ℂ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ ramifiedSet χ) :
    rayWeight χ s (primeNZ v) = 0 := by
  rw [rayWeight_apply, ite_eq_right fun h => h v hv dvd_rfl, zero_mul, zero_mul]

/-- The weight at an unramified prime $\mathfrak{p}_v$ is $\chi_v(\varpi_v) N(\mathfrak{p}_v)^{-s}$. -/
theorem rayWeight_primeNZ_of_notMem (s : ℂ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ ramifiedSet χ) :
    rayWeight χ s (primeNZ v) =
      (primeValue χ v : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  have h : ∀ w ∈ ramifiedSet χ, ¬ w.asIdeal ∣ ((primeNZ v : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :=
    fun w hw h => hv (eq_of_asIdeal_dvd (K := K) h ▸ hw)
  rw [rayWeight_apply, ite_eq_left h, idealChar_mk0_primeNZ, one_mul, coe_primeNZ]

/-- For $\mathrm{Re}\, s > 1$, a multiplicative function $f$ on the nonzero ideals with $|f(I)| \leq |N(I)^{-s}|$, and a finite set $S$ of primes, the sum of $f(I)$ over the ideals with prime factors in $S$ is $\prod_{\mathfrak{p} \in S} (1 - f(\mathfrak{p}))^{-1}$. -/
theorem hasSum_supportedIn_of_norm_le (f : (Ideal (𝓞 K))⁰ →* ℂ) {s : ℂ} (hs : 1 < s.re)
    (hf : ∀ I, ‖f I‖ ≤ ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasSum (fun I : supportedIn K S => f I) (∏ v ∈ S, (1 - f (primeNZ v))⁻¹) := by
  have hsum : Summable fun I : (Ideal (𝓞 K))⁰ => ‖f I‖ :=
    (summable_norm_absNorm_cpow K hs).of_nonneg_of_le (fun _ => norm_nonneg _) hf
  have hp : ∀ v, ‖f (primeNZ v)‖ < 1 := fun v =>
    (hf _).trans_lt (norm_normCpow_lt_one v (s := s) (by linarith))
  induction S using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, supportedIn_empty]
    convert hasSum_singleton (1 : (Ideal (𝓞 K))⁰) (fun I : (Ideal (𝓞 K))⁰ => f I)
    all_goals simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv]
    have hg := hasSum_geometric_of_norm_lt_one (hp v)
    have hgn : Summable (fun n : ℕ => ‖f (primeNZ v) ^ n‖) :=
      (summable_geometric_of_lt_one (norm_nonneg _) (hp v)).congr fun n => (norm_pow _ _).symm
    have hJn : Summable (fun J : supportedIn K S => ‖f J‖) := hsum.comp_injective Subtype.coe_injective
    have hfg : Summable (fun p : ℕ × supportedIn K S => f (primeNZ v) ^ p.1 * f p.2) :=
      summable_mul_of_summable_norm (f := fun n : ℕ => f (primeNZ v) ^ n)
        (g := fun J : supportedIn K S => f J) hgn hJn
    have hm := hg.mul ih hfg
    rw [← (Equiv.ofBijective _ (bijective_insertMap hv)).hasSum_iff]
    convert hm using 1
    funext p
    change f (primeNZ v ^ p.1 * p.2) = _
    rw [map_mul, map_pow]

/-- **The Euler product.** For $\mathrm{Re}\, s > 1$ and a multiplicative function $f$ on the nonzero ideals with $|f(I)| \leq |N(I)^{-s}|$, $\sum_I f(I) = \prod_{\mathfrak{p}} (1 - f(\mathfrak{p}))^{-1}$. -/
theorem hasProd_of_norm_le (f : (Ideal (𝓞 K))⁰ →* ℂ) {s : ℂ} (hs : 1 < s.re)
    (hf : ∀ I, ‖f I‖ ≤ ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - f (primeNZ v))⁻¹) (∑' I, f I) := by
  have hsum : Summable fun I : (Ideal (𝓞 K))⁰ => ‖f I‖ :=
    (summable_norm_absNorm_cpow K hs).of_nonneg_of_le (fun _ => norm_nonneg _) hf
  have h1 : ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ v ∈ T, (1 - f (primeNZ v))⁻¹ =
        ∑' I : (Ideal (𝓞 K))⁰, (supportedIn K T).indicator (fun I => f I) I := by
    intro T
    rw [← tsum_subtype]
    exact (hasSum_supportedIn_of_norm_le f hs hf T).tsum_eq.symm
  change Tendsto _ atTop _
  simp_rw [h1]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I => ?_)
    (Eventually.of_forall fun T I => norm_indicator_le_norm_self _ _)
  have hfin := Ideal.finite_factors (nonZeroDivisors.coe_ne_zero I)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT
  rw [Set.indicator_of_mem]
  exact fun v hv => hT (hfin.mem_toFinset.2 hv)

/-- **The Dirichlet series.** For a character $\chi$ of ray class type and $\mathrm{Re}\, s > 1$, the Euler product of the local factors converges to $\sum_I \chi(I) N(I)^{-s}$, where $I$ runs over the nonzero ideals prime to the conductor. -/
theorem IsRayClassType.hasProd_localFactor (hχ : IsRayClassType χ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v => χ.localFactor v s) (∑' I, rayWeight χ s I) := by
  convert hasProd_of_norm_le (rayWeight χ s) hs (hχ.norm_rayWeight_le s) using 1
  funext v
  by_cases hv : v ∈ ramifiedSet χ
  · rw [NonArchimedean.localFactor_eq_one_of_not_isUnramifiedAt v χ (mem_ramifiedSet.1 hv),
      rayWeight_primeNZ_of_mem s hv, sub_zero, inv_one]
  · rw [HeckeCharacter.localFactor, ite_eq_left (not_not.1 (mt mem_ramifiedSet.2 hv)),
      rayWeight_primeNZ_of_notMem s hv, primeValue]

/-- **The Dirichlet series.** For a character $\chi$ of ray class type and $\mathrm{Re}\, s > 1$, $L(s, \chi) = \sum_I \chi(I) N(I)^{-s}$, where $I$ runs over the nonzero ideals prime to the conductor. -/
theorem IsRayClassType.finiteLFunction_eq (hχ : IsRayClassType χ) {s : ℂ} (hs : 1 < s.re) :
    χ.finiteLFunction s = ∑' I, rayWeight χ s I :=
  (hχ.hasProd_localFactor hs).tprod_eq

end Euler

end Langlands.Tate
