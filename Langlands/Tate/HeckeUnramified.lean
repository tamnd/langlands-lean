/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.ClassCharacter
import Langlands.Tate.HeckeNormPower
import Langlands.Hecke.Rational

/-!
# Hecke's theorem for the characters of class group type

Let $K$ be a number field and let $\chi$ be a Hecke character that is trivial on $\mathcal{O}_v^\times$ at each finite place $v$ and trivial on $K_v^\times$ at each infinite place $v$. This file shows that $\chi$ comes from a character $\psi$ of the class group, and it proves the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi$.

## Main definitions

* `Langlands.Tate.IsClassType`: the character is unramified at each finite place and trivial at each infinite place.
* `Langlands.Tate.idealChar`: the character $I \mapsto \prod_v \chi_v(\varpi_v)^{v(I)}$ of the group of fractional ideals.
* `Langlands.Tate.classChar`: the character $\psi$ of the class group that $\chi$ gives.
* `Langlands.Tate.ideleIdeal`: the fractional ideal $\prod_v \mathfrak{p}_v^{v(x_v)}$ of an idele $x$.

## Main results

* `Langlands.Tate.IsClassType.apply_ofAdicCompletion_localUniformizer`: $\chi(\varpi_v) = \psi([\mathfrak{p}_v])$, where $\varpi_v$ is the idele with the uniformizer at $v$ and $1$ at the other places.
* `Langlands.Tate.IsClassType.apply_eq_classChar`: $\chi(x) = \psi([I(x)])$ for each idele $x$.
* `Langlands.Tate.IsClassType.norm_apply`: $|\chi(x)| = 1$.
* `Langlands.Tate.IsClassType.isArchimedeanParameter`: the archimedean parameters of $\chi$ are $n = 0$ and $t = 0$.
* `Langlands.Tate.IsClassType.conductor_eq_one`: the conductor of $\chi$ is $(1)$.
* `Langlands.Tate.hasProd_classCharL`: the Euler product of $L(s, \psi)$.
* `Langlands.Tate.IsClassType.completedLFunction_eq`: $\Lambda(s, \chi) = 2^{r_2} \Gamma_K(s) L(s, \psi)$ for $\mathrm{Re}\, s > 1$.
* `Langlands.Tate.IsClassType.heckeFunctionalEquation_of_ne_one`: the conclusion of `HeckeFunctionalEquationAt K` for $\chi$ with $\psi \neq 1$.
* `Langlands.Tate.IsClassType.heckeFunctionalEquation`: the conclusion of `HeckeFunctionalEquationAt K` for each $\chi$ of class group type.

## Proof

Mathlib has no map from the ideles to the fractional ideals, so this file computes with the components of the ideles. The character $\chi$ is continuous, so it is trivial on the ideles that are $1$ at the infinite places, units at the finite places, and near $1$ at a finite set $T$ of places (`Langlands.HeckeRat.Top.exists_trivial_on_units`). With the local units at the places in $T$, it follows that $\chi$ is trivial on $\prod_v \mathcal{O}_v^\times$. Thus $\chi(x) = \prod_v \chi_v(\varpi_v)^{v(x_v)}$ for each idele $x$. For $x \in K^\times$ this gives that the character $I \mapsto \prod_v \chi_v(\varpi_v)^{v(I)}$ is trivial on the principal ideals, so it is a character $\psi$ of the class group. The local factor of $\chi$ at $v$ is $(1 - \psi([\mathfrak{p}_v]) N(\mathfrak{p}_v)^{-s})^{-1}$, and the Euler product of `Langlands/Tate/DedekindEuler.lean`, with the weights $\psi([I])$, gives $L(s, \chi) = L(s, \psi)$. The functional equation is then the functional equation of `Langlands/Tate/ClassCharacter.lean` for $\psi \neq 1$, and `Langlands.Tate.heckeFunctionalEquationAt_one` for $\psi = 1$, because then $\chi = 1$.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in Algebraic number theory (Cassels and Frohlich, eds.), 1967.
* J. Neukirch, Algebraic number theory, chapter VI, section 1 and chapter VII, section 8.
-/

namespace Langlands.Tate

open NumberField InfinitePlace Complex IsDedekindDomain Filter Topology

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

section Components

/-- The component of an idele at an infinite place. -/
noncomputable def ideleInf (w : InfinitePlace K) : IdeleGroup (𝓞 K) K →* w.Completionˣ :=
  Units.map ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).toMonoidHom

/-- The component of an idele at a finite place. -/
noncomputable def ideleFin (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ :=
  Units.map ((RestrictedProduct.evalRingHom _ v).comp
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).toMonoidHom

/-- The component at an infinite place, as an element of the adele ring. -/
@[simp] theorem coe_ideleInf (w : InfinitePlace K) (x : IdeleGroup (𝓞 K) K) :
    (ideleInf w x : w.Completion) = (x : AdeleRing (𝓞 K) K).1 w := rfl

/-- The component at a finite place, as an element of the adele ring. -/
@[simp] theorem coe_ideleFin (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    (ideleFin v x : v.adicCompletion K) = (x : AdeleRing (𝓞 K) K).2 v := rfl

/-- The component at $v$ of the idele with the component $y$ at $v$ is $y$. -/
theorem ideleFin_ofAdicCompletion_self (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    ideleFin v (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = y := by
  classical
  refine Units.ext ?_
  change RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers K w) v
    (y : v.adicCompletion K) v = y
  convert RestrictedProduct.mulSingle_eq_same
    (fun w => HeightOneSpectrum.adicCompletionIntegers K w) v (y : v.adicCompletion K)

/-- The component at $v$ of the idele with one nontrivial component at a place $w \neq v$ is $1$. -/
theorem ideleFin_ofAdicCompletion_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (y : (w.adicCompletion K)ˣ) : ideleFin v (IdeleGroup.ofAdicCompletion (𝓞 K) K w y) = 1 := by
  classical
  refine Units.ext ?_
  change RestrictedProduct.mulSingle (fun w => HeightOneSpectrum.adicCompletionIntegers K w) w
    (y : w.adicCompletion K) v = 1
  convert RestrictedProduct.mulSingle_eq_of_ne'
    (fun w => HeightOneSpectrum.adicCompletionIntegers K w) (y : w.adicCompletion K) h

/-- An idele with one nontrivial component at a finite place is $1$ at the infinite places. -/
theorem ideleInf_ofAdicCompletion (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) : ideleInf w (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = 1 := rfl

/-- An idele with one nontrivial component at an infinite place is $1$ at the finite places. -/
theorem ideleFin_ofCompletion (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K)
    (y : w.Completionˣ) : ideleFin v (IdeleGroup.ofCompletion (𝓞 K) K w y) = 1 := rfl

/-- The component at $w$ of the idele with the component $y$ at $w$ is $y$. -/
theorem ideleInf_ofCompletion_self (w : InfinitePlace K) (y : w.Completionˣ) :
    ideleInf w (IdeleGroup.ofCompletion (𝓞 K) K w y) = y := by
  refine Units.ext ?_
  change InfiniteAdeleRing.ofCompletion w (y : w.Completion) w = _
  rw [InfiniteAdeleRing.ofCompletion_apply]
  classical
  convert Pi.mulSingle_eq_same (M := fun v : InfinitePlace K => v.Completion) w
    (y : w.Completion)

/-- The component at $w$ of the idele with one nontrivial component at an infinite place $w' \neq w$ is $1$. -/
theorem ideleInf_ofCompletion_of_ne {w w' : InfinitePlace K} (h : w ≠ w') (y : w'.Completionˣ) :
    ideleInf w (IdeleGroup.ofCompletion (𝓞 K) K w' y) = 1 := by
  refine Units.ext ?_
  change InfiniteAdeleRing.ofCompletion w' (y : w'.Completion) w = 1
  rw [InfiniteAdeleRing.ofCompletion_apply]
  classical
  convert Pi.mulSingle_eq_of_ne (M := fun v : InfinitePlace K => v.Completion) h
    (y : w'.Completion)

/-- The component at $v$ of the principal idele of $x \in K^\times$ is the image of $x$ in $K_v$. -/
theorem ideleFin_unitEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    (ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) x := rfl

/-- Two ideles with the same components are equal. -/
theorem ext_idele {x y : IdeleGroup (𝓞 K) K} (hinf : ∀ w, ideleInf w x = ideleInf w y)
    (hfin : ∀ v, ideleFin v x = ideleFin v y) : x = y := by
  ext1
  refine Prod.ext ?_ ?_
  · funext w
    exact congrArg Units.val (hinf w)
  · exact FiniteAdeleRing.ext _ fun v =>
      congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) (hfin v)

/-- The infinite part of an idele: the idele with the same components at the infinite places and the component $1$ at each finite place. -/
noncomputable def infinitePart (x : IdeleGroup (𝓞 K) K) : IdeleGroup (𝓞 K) K :=
  ∏ w : InfinitePlace K, IdeleGroup.ofCompletion (𝓞 K) K w (ideleInf w x)

/-- The infinite part of $x$ has the components of $x$ at the infinite places. -/
theorem ideleInf_infinitePart (w : InfinitePlace K) (x : IdeleGroup (𝓞 K) K) :
    ideleInf w (infinitePart x) = ideleInf w x := by
  rw [infinitePart, map_prod, Finset.prod_eq_single w
    (fun w' _ hw' => ideleInf_ofCompletion_of_ne (Ne.symm hw') _)
    (fun h => absurd (Finset.mem_univ w) h), ideleInf_ofCompletion_self]

/-- The infinite part of $x$ is $1$ at the finite places. -/
theorem ideleFin_infinitePart (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    ideleFin v (infinitePart x) = 1 := by
  rw [infinitePart, map_prod]
  exact Finset.prod_eq_one fun w _ => ideleFin_ofCompletion v w _

/-- The components of an idele at almost all finite places are units of $\mathcal{O}_v$. -/
theorem finite_valued_ne_one (x : IdeleGroup (𝓞 K) K) :
    {v : HeightOneSpectrum (𝓞 K) |
      Valued.v ((ideleFin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 1}.Finite :=
  Filter.eventually_cofinite.1 (AdeleRing.isUnit_iff.1 x.isUnit).2.2

end Components

section Local

/-- The valuation on $K_v$ extends the valuation on $K$. -/
theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

/-- The valuation of the uniformizer is $\exp(-1)$. -/
theorem valued_localUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((localUniformizer K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1) := by
  change Valued.v (algebraMap K (v.adicCompletion K) (uniformizer K v)) = _
  rw [valued_algebraMap]
  exact (v.valuation_exists_uniformizer K).choose_spec

/-- The valuation of $x \in K^\times$ at $v$ is $\exp(-n)$, where $n$ is the exponent of $\mathfrak{p}_v$ in the fractional ideal $(x)$. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuation K (x : K) = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  classical
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ (x : K)
  have hn : n ≠ 0 := by
    rintro rfl
    apply x.ne_zero
    rw [← hnd, IsLocalization.mk'_zero]
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) (d : 𝓞 K))⁻¹ *
        ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, ← map_mul, ← hnd, IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  have hx : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).2 x.ne_zero
  rw [FractionalIdeal.count_well_defined K v hx hI, ← hnd, v.valuation_of_mk',
    v.intValuation_if_neg hn, v.intValuation_if_neg hd, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add]
  congr 1
  ring

end Local

section ClassType

/-- A Hecke character of class group type: it is unramified at every finite place, and it is trivial on the image of $K_v^\times$ for each infinite place $v$. -/
structure IsClassType (χ : HeckeCharacter K) : Prop where
  /-- The character is trivial on $\mathcal{O}_v^\times$ at each finite place. -/
  unramified : ∀ v, χ.IsUnramifiedAt v
  /-- The character is trivial at each infinite place. -/
  trivial_inf : ∀ (w : InfinitePlace K) (y : w.Completionˣ), χ.infiniteComponent w y = 1

variable {χ : HeckeCharacter K}

/-- The character $\chi$ as a function on ideles. -/
noncomputable def ideleChar (χ : HeckeCharacter K) : IdeleGroup (𝓞 K) K →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).comp (QuotientGroup.mk' _)

/-- The value of `ideleChar χ` at $x$ is $\chi$ at the class of $x$. -/
theorem ideleChar_apply (x : IdeleGroup (𝓞 K) K) :
    ideleChar χ x = χ (x : IdeleClassGroup (𝓞 K) K) := rfl

/-- On the image of $K_v^\times$, the function `ideleChar χ` is the local component $\chi_v$. -/
theorem ideleChar_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    ideleChar χ (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = χ.finiteComponent v y := rfl

/-- The function `ideleChar χ` is trivial on the principal ideles. -/
theorem ideleChar_unitEmbedding (x : Kˣ) :
    ideleChar χ (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 := by
  rw [ideleChar_apply, (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2
    (MonoidHom.mem_range.2 ⟨x, rfl⟩), map_one]

/-- A character of class group type is trivial on the infinite part of an idele. -/
theorem IsClassType.ideleChar_infinitePart (hχ : IsClassType χ) (x : IdeleGroup (𝓞 K) K) :
    ideleChar χ (infinitePart x) = 1 := by
  rw [infinitePart, map_prod]
  exact Finset.prod_eq_one fun w _ => hχ.trivial_inf w _

/-- A character of class group type is trivial on the units of $\mathcal{O}_v$. -/
theorem IsClassType.finiteComponent_eq_one (hχ : IsClassType χ) {v : HeightOneSpectrum (𝓞 K)}
    {y : (v.adicCompletion K)ˣ} (hy : Valued.v (y : v.adicCompletion K) = 1) :
    χ.finiteComponent v y = 1 :=
  hχ.unramified v y hy (by
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (Valuation.map_sub _ _ _).trans (max_le hy.le (by simp)))

/-- For a character of class group type and an idele $x$ whose components outside a finite set $S$ of finite places are units, $\chi(x) = \prod_{v \in S} \chi_v(x_v)$. -/
theorem IsClassType.ideleChar_eq_prod (hχ : IsClassType χ) (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, Valued.v ((ideleFin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1) :
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
    hχ.finiteComponent_eq_one (hS v hv)).symm

/-- The local component of $\chi^{-1}$ at a finite place is the inverse of the local component of $\chi$. -/
theorem finiteComponent_inv (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) :
    χ⁻¹.finiteComponent v y = (χ.finiteComponent v y)⁻¹ := rfl

/-- The local component of $\chi^{-1}$ at an infinite place is the inverse of the local component of $\chi$. -/
theorem infiniteComponent_inv (w : InfinitePlace K) (y : w.Completionˣ) :
    χ⁻¹.infiniteComponent w y = (χ.infiniteComponent w y)⁻¹ := rfl

/-- If $\chi$ is of class group type, then $\chi^{-1}$ is of class group type. -/
theorem IsClassType.inv (hχ : IsClassType χ) : IsClassType χ⁻¹ where
  unramified v y hy h := by
    rw [finiteComponent_inv, hχ.unramified v y hy h, inv_one]
  trivial_inf w y := by
    rw [infiniteComponent_inv, hχ.trivial_inf w y, inv_one]

end ClassType

section ClassGroupCharacter

variable {χ : HeckeCharacter K}

/-- The value $\chi_v(\varpi_v)$ of the local component at the uniformizer. -/
noncomputable def primeValue (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℂˣ :=
  χ.finiteComponent v (localUniformizer K v)

/-- The value of $\chi^{-1}$ at the uniformizer is the inverse of the value of $\chi$. -/
theorem primeValue_inv (v : HeightOneSpectrum (𝓞 K)) : primeValue χ⁻¹ v = (primeValue χ v)⁻¹ :=
  rfl

/-- For a character of class group type, $\chi_v(y) = \chi_v(\varpi_v)^{m}$, where $m$ is the valuation of $y$, so that $|y|_v = \exp(-m)$. -/
theorem IsClassType.finiteComponent_eq_zpow (hχ : IsClassType χ) (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) :
    χ.finiteComponent v y =
      primeValue χ v ^ (-WithZero.log (Valued.v (y : v.adicCompletion K))) := by
  set n := WithZero.log (Valued.v (y : v.adicCompletion K)) with hn
  have hy0 : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have h1 : Valued.v ((y * localUniformizer K v ^ n : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, valued_localUniformizer,
      ← WithZero.exp_log hy0, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← hn]
    simp
  have h2 := hχ.finiteComponent_eq_one h1
  rw [map_mul, map_zpow] at h2
  rw [zpow_neg, primeValue]
  exact eq_inv_of_mul_eq_one_left h2

/-- The function $v \mapsto a_v^{v(I)}$ has finite support for each fractional ideal $I$. -/
theorem finite_mulSupport_zpow_count (a : HeightOneSpectrum (𝓞 K) → ℂˣ)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v => a v ^ FractionalIdeal.count K v I).Finite :=
  (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h =>
    hv (by simp only [h, zpow_zero])

/-- The character $I \mapsto \prod_v \chi_v(\varpi_v)^{v(I)}$ of the group of fractional ideals. -/
noncomputable def idealChar (χ : HeckeCharacter K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂˣ where
  toFun I := ∏ᶠ v, primeValue χ v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
  map_one' := by
    simp only [Units.val_one, FractionalIdeal.count_one, zpow_zero, finprod_one]
  map_mul' I J := by
    simp only [Units.val_mul]
    rw [← finprod_mul_distrib (finite_mulSupport_zpow_count _ _)
      (finite_mulSupport_zpow_count _ _)]
    refine finprod_congr fun v => ?_
    rw [FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, zpow_add]

/-- The value of `idealChar χ` at $I$ is $\prod_v \chi_v(\varpi_v)^{v(I)}$. -/
theorem idealChar_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealChar χ I =
      ∏ᶠ v, primeValue χ v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

/-- For a character of class group type, `idealChar χ` is trivial on the principal ideals. -/
theorem IsClassType.idealChar_toPrincipalIdeal (hχ : IsClassType χ) (x : Kˣ) :
    idealChar χ (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  classical
  have hfin := Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = WithZero.exp
          (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) :=
    fun v => by rw [ideleFin_unitEmbedding, valued_algebraMap, valuation_eq_exp_neg_count]
  have hS : ∀ v ∉ hfin.toFinset,
      Valued.v ((ideleFin v (IdeleGroup.unitEmbedding (𝓞 K) K x) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := fun v hv => by
    rw [hval, show FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0
      by simpa using hv, neg_zero, WithZero.exp_zero]
  have h := hχ.ideleChar_eq_prod _ _ hS
  rw [ideleChar_unitEmbedding] at h
  rw [idealChar_apply, coe_toPrincipalIdeal,
    finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_]
  · refine (Finset.prod_congr rfl fun v _ => ?_).trans h.symm
    rw [hχ.finiteComponent_eq_zpow, hval, WithZero.log_exp, neg_neg]
  · intro v hv
    rw [Set.Finite.coe_toFinset]
    exact fun h0 => hv (by simp only [h0, zpow_zero])

/-- The character $\psi$ of the class group of a character $\chi$ of class group type: $\psi([I]) = \prod_v \chi_v(\varpi_v)^{v(I)}$. -/
noncomputable def classChar (χ : HeckeCharacter K) (hχ : IsClassType χ) :
    ClassGroup (𝓞 K) →* ℂˣ :=
  (QuotientGroup.lift (toPrincipalIdeal (𝓞 K) K).range (idealChar χ) (by
    rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_ker.2 (hχ.idealChar_toPrincipalIdeal x))).comp
    (ClassGroup.equiv K).toMonoidHom

/-- The value of $\psi$ at the class of a fractional ideal $I$ is `idealChar χ I`. -/
theorem IsClassType.classChar_mk (hχ : IsClassType χ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    classChar χ hχ (ClassGroup.mk K I) = idealChar χ I := by
  have h : ClassGroup.equiv K (ClassGroup.mk K I) = QuotientGroup.mk' _ I := by
    rw [ClassGroup.equiv_mk]
    congr 1
    refine Units.ext ?_
    rw [Units.coe_mapEquiv]
    simp [FractionalIdeal.canonicalEquiv_self]
  rw [classChar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  exact QuotientGroup.lift_mk' _ _ _

/-- The value of `idealChar χ` at the prime $\mathfrak{p}_v$ is $\chi_v(\varpi_v)$. -/
theorem idealChar_mk0_primeNZ (v : HeightOneSpectrum (𝓞 K)) :
    idealChar χ (FractionalIdeal.mk0 K (primeNZ v)) = primeValue χ v := by
  classical
  rw [idealChar_apply, FractionalIdeal.coe_mk0, coe_primeNZ, finprod_eq_single _ v fun w hw => by
    rw [FractionalIdeal.count_maximal, ite_eq_right (Ne.symm hw), zpow_zero],
    FractionalIdeal.count_maximal, ite_eq_left rfl, zpow_one]

/-- **Step 1.** The value of $\psi$ at the class of the prime $\mathfrak{p}_v$ is $\chi_v(\varpi_v)$. -/
theorem IsClassType.classChar_mk0_primeNZ (hχ : IsClassType χ) (v : HeightOneSpectrum (𝓞 K)) :
    classChar χ hχ (ClassGroup.mk0 (primeNZ v)) = primeValue χ v := by
  rw [← ClassGroup.mk_mk0 (K := K), hχ.classChar_mk, idealChar_mk0_primeNZ]

/-- **Step 1.** Let $\varpi_v$ be the idele with the uniformizer at $v$ and $1$ at the other places. Then $\chi(\varpi_v) = \psi([\mathfrak{p}_v])$. -/
theorem IsClassType.apply_ofAdicCompletion_localUniformizer (hχ : IsClassType χ)
    (v : HeightOneSpectrum (𝓞 K)) :
    χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v (localUniformizer K v)) =
      classChar χ hχ (ClassGroup.mk0 (primeNZ v)) :=
  (hχ.classChar_mk0_primeNZ v).symm

/-- The fractional ideal $\prod_v \mathfrak{p}_v^{v(x_v)}$ of an idele $x$, where $v(x_v)$ is the valuation of the component $x_v$. -/
noncomputable def ideleIdeal (x : IdeleGroup (𝓞 K) K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  ∏ v ∈ (finite_valued_ne_one x).toFinset, FractionalIdeal.mk0 K (primeNZ v) ^
    (-WithZero.log (Valued.v ((ideleFin v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)))

/-- **Step 1.** For a character of class group type, $\chi(x) = \psi([I(x)])$ for each idele $x$, where $I(x) = \prod_v \mathfrak{p}_v^{v(x_v)}$. -/
theorem IsClassType.apply_eq_classChar (hχ : IsClassType χ) (x : IdeleGroup (𝓞 K) K) :
    χ (x : IdeleClassGroup (𝓞 K) K) = classChar χ hχ (ClassGroup.mk K (ideleIdeal x)) := by
  rw [← ideleChar_apply, hχ.ideleChar_eq_prod x (finite_valued_ne_one x).toFinset
    (fun v hv => by simpa using hv), ideleIdeal, map_prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow, map_zpow, ClassGroup.mk_mk0 (K := K), hχ.classChar_mk0_primeNZ,
    hχ.finiteComponent_eq_zpow]

/-- The values of a character of the class group have absolute value $1$, because the class group is finite. -/
theorem norm_classGroupChar (φ : ClassGroup (𝓞 K) →* ℂˣ) (C : ClassGroup (𝓞 K)) :
    ‖(φ C : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card (ClassGroup (𝓞 K))) ?_
    Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

/-- For a character of class group type, $|\chi_v(\varpi_v)| = 1$. -/
theorem IsClassType.norm_primeValue (hχ : IsClassType χ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(primeValue χ v : ℂ)‖ = 1 := by
  rw [← hχ.classChar_mk0_primeNZ v]
  exact norm_classGroupChar _ _

/-- A character of class group type is unitary: $|\chi(x)| = 1$ for each idele $x$. -/
theorem IsClassType.norm_apply (hχ : IsClassType χ) (x : IdeleGroup (𝓞 K) K) :
    ‖(χ (x : IdeleClassGroup (𝓞 K) K) : ℂ)‖ = 1 := by
  rw [← ideleChar_apply, hχ.ideleChar_eq_prod x (finite_valued_ne_one x).toFinset
    (fun v hv => by simpa using hv), ← Units.coeHom_apply, map_prod, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Units.coeHom_apply, hχ.finiteComponent_eq_zpow, Units.val_zpow_eq_zpow_val, norm_zpow,
    hχ.norm_primeValue, one_zpow]

/-- If the class group character $\psi$ of $\chi$ is trivial, then $\chi$ is trivial. -/
theorem IsClassType.eq_one_of_classChar_eq_one (hχ : IsClassType χ) (h : classChar χ hχ = 1) :
    χ = 1 := by
  refine ContinuousMonoidHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [hχ.apply_eq_classChar, h, MonoidHom.one_apply]
  rfl

end ClassGroupCharacter

section LocalData

variable {χ : HeckeCharacter K}

/-- **Step 2.** The archimedean parameters of a character of class group type are $n = 0$ and $t = 0$. -/
theorem IsClassType.isArchimedeanParameter (hχ : IsClassType χ) {v : InfinitePlace K} {n : ℤ}
    {t : ℂ} (h : χ.IsArchimedeanParameter v n t) : n = 0 ∧ t = 0 :=
  eq_zero_of_forall_param_eq_one h.isReal fun x => by
    rw [← h.eq x, hχ.trivial_inf v x, Units.val_one]

/-- **Step 2.** The conductor of a character of class group type is the unit ideal. -/
theorem IsClassType.conductor_eq_one (hχ : IsClassType χ) : χ.conductor = 1 := by
  have h (v : HeightOneSpectrum (𝓞 K)) : χ.conductorExponent v = 0 :=
    Nat.sInf_eq_zero.mpr (Or.inl (hχ.unramified v))
  simp only [HeckeCharacter.conductor, h, pow_zero]
  exact finprod_one

/-- **Step 2.** The local factor of a character of class group type at $v$ is $(1 - \chi_v(\varpi_v) N(\mathfrak{p}_v)^{-s})^{-1}$. -/
theorem IsClassType.localFactor_eq (hχ : IsClassType χ) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    χ.localFactor v s =
      (1 - (primeValue χ v : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [HeckeCharacter.localFactor, ite_eq_left (hχ.unramified v), primeValue]

end LocalData

section Euler

open scoped Classical

/-- For $\mathrm{Re}\, s > 1$, a multiplicative function $f$ on the nonzero ideals with $|f(I)| = |N(I)^{-s}|$, and a finite set $S$ of primes, the sum of $f(I)$ over the ideals with prime factors in $S$ is $\prod_{\mathfrak{p} \in S} (1 - f(\mathfrak{p}))^{-1}$. -/
theorem hasSum_supportedIn_of_norm (f : (Ideal (𝓞 K))⁰ →* ℂ) {s : ℂ} (hs : 1 < s.re)
    (hf : ∀ I, ‖f I‖ = ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasSum (fun I : supportedIn K S => f I) (∏ v ∈ S, (1 - f (primeNZ v))⁻¹) := by
  have hsum : Summable fun I : (Ideal (𝓞 K))⁰ => ‖f I‖ :=
    (summable_norm_absNorm_cpow K hs).congr fun I => (hf I).symm
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
    have hJn : Summable (fun J : supportedIn K S => ‖f J‖) := hsum.subtype (supportedIn K S)
    have hfg : Summable (fun p : ℕ × supportedIn K S => f (primeNZ v) ^ p.1 * f p.2) :=
      summable_mul_of_summable_norm (f := fun n : ℕ => f (primeNZ v) ^ n)
        (g := fun J : supportedIn K S => f J) hgn hJn
    have hm := hg.mul ih hfg
    rw [← (Equiv.ofBijective _ (bijective_insertMap hv)).hasSum_iff]
    convert hm using 1
    funext p
    change f (primeNZ v ^ p.1 * p.2) = _
    rw [map_mul, map_pow]

/-- **The Euler product.** For $\mathrm{Re}\, s > 1$ and a multiplicative function $f$ on the nonzero ideals with $|f(I)| = |N(I)^{-s}|$, $\sum_I f(I) = \prod_{\mathfrak{p}} (1 - f(\mathfrak{p}))^{-1}$. -/
theorem hasProd_of_norm (f : (Ideal (𝓞 K))⁰ →* ℂ) {s : ℂ} (hs : 1 < s.re)
    (hf : ∀ I, ‖f I‖ = ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - f (primeNZ v))⁻¹) (∑' I, f I) := by
  have hsum : Summable fun I : (Ideal (𝓞 K))⁰ => ‖f I‖ :=
    (summable_norm_absNorm_cpow K hs).congr fun I => (hf I).symm
  have h1 : ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ v ∈ T, (1 - f (primeNZ v))⁻¹ =
        ∑' I : (Ideal (𝓞 K))⁰, (supportedIn K T).indicator (fun I => f I) I := by
    intro T
    rw [← tsum_subtype]
    exact (hasSum_supportedIn_of_norm f hs hf T).tsum_eq.symm
  change Tendsto _ atTop _
  simp_rw [h1]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I => ?_)
    (Eventually.of_forall fun T I => norm_indicator_le_norm_self _ _)
  have hfin := Ideal.finite_factors (nonZeroDivisors.coe_ne_zero I)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT
  rw [Set.indicator_of_mem]
  exact fun v hv => hT (hfin.mem_toFinset.2 hv)

/-- The weight $I \mapsto \varphi([I]) N(I)^{-s}$ of the $L$-series of a class group character $\varphi$, as a homomorphism of monoids. -/
noncomputable def classCharWeight (φ : ClassGroup (𝓞 K) →* ℂˣ) (s : ℂ) : (Ideal (𝓞 K))⁰ →* ℂ :=
  (Units.coeHom ℂ).comp (φ.comp ClassGroup.mk0) * (normCpow K s).comp (Submonoid.subtype _)

/-- The value of the weight at $I$ is $\varphi([I]) N(I)^{-s}$. -/
theorem classCharWeight_apply (φ : ClassGroup (𝓞 K) →* ℂˣ) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    classCharWeight φ s I =
      (φ (ClassGroup.mk0 I) : ℂ) * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) := rfl

/-- **Step 2.** The Euler product of the $L$-series of a class group character: for $\mathrm{Re}\, s > 1$, $L(s, \varphi) = \prod_{\mathfrak{p}} (1 - \varphi([\mathfrak{p}]) N(\mathfrak{p})^{-s})^{-1}$. -/
theorem hasProd_classCharL (φ : ClassGroup (𝓞 K) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (φ (ClassGroup.mk0 (primeNZ v)) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (classCharL φ s) := by
  have h := hasProd_of_norm (classCharWeight φ s) hs fun I => by
    rw [classCharWeight_apply, norm_mul, norm_classGroupChar, one_mul]
  have e : classCharL φ s = ∑' I, classCharWeight φ s I := by
    rw [classCharL]
    exact tsum_congr fun I => by rw [classCharWeight_apply, Complex.ofReal_natCast]
  rw [e]
  exact h

end Euler

section Completed

variable {χ : HeckeCharacter K}

/-- **Step 2.** Let $\chi$ be of class group type and let $\varphi$ be a class group character with $\varphi([\mathfrak{p}_v]) = \chi_v(\varpi_v)$ for each $v$. For $\mathrm{Re}\, s > 1$, the finite $L$-function of $\chi$ is $L(s, \varphi)$. -/
theorem IsClassType.finiteLFunction_eq (hχ : IsClassType χ) (φ : ClassGroup (𝓞 K) →* ℂˣ)
    (hφ : ∀ v, φ (ClassGroup.mk0 (primeNZ v)) = primeValue χ v) {s : ℂ} (hs : 1 < s.re) :
    χ.finiteLFunction s = classCharL φ s := by
  rw [HeckeCharacter.finiteLFunction]
  exact (tprod_congr fun v => by rw [hχ.localFactor_eq, ← hφ]).trans
    (hasProd_classCharL φ hs).tprod_eq

/-- **Step 2.** With $\varphi$ as in `IsClassType.finiteLFunction_eq` and archimedean parameters $(n, t)$ of $\chi$, the completed $L$-function is $\Lambda(s, \chi) = 2^{r_2} \Gamma_K(s) L(s, \varphi)$ for $\mathrm{Re}\, s > 1$. -/
theorem IsClassType.completedLFunction_eq (hχ : IsClassType χ) (φ : ClassGroup (𝓞 K) →* ℂˣ)
    (hφ : ∀ v, φ (ClassGroup.mk0 (primeNZ v)) = primeValue χ v)
    {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v)) {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction n t s = 2 ^ nrComplexPlaces K * gammaK K s * classCharL φ s := by
  obtain rfl : n = 0 := funext fun v => (hχ.isArchimedeanParameter (hn v)).1
  obtain rfl : t = 0 := funext fun v => (hχ.isArchimedeanParameter (hn v)).2
  rw [HeckeCharacter.completedLFunction, gammaFactor_zero, hχ.finiteLFunction_eq φ hφ hs]

/-- **Step 2.** For $\psi \neq 1$ and $\mathrm{Re}\, s > 1$, the completed $L$-function of $\chi$ is $2^{r_2} |d_K|^{-s/2} \xi(s, \psi)$, where $\xi(s, \psi)$ is the entire function `classCharLambda ψ`. -/
theorem IsClassType.completedLFunction_eq_classCharLambda (hχ : IsClassType χ)
    (hψ : classChar χ hχ ≠ 1) {n : InfinitePlace K → ℤ} {t : InfinitePlace K → ℂ}
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v)) {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction n t s = 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) *
      classCharLambda (classChar χ hχ) s := by
  have hc : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  rw [hχ.completedLFunction_eq _ hχ.classChar_mk0_primeNZ hn hs,
    classCharLambda_eq_classCharL _ hψ hs, Complex.cpow_neg]
  field_simp

end Completed

section Hecke

variable {χ : HeckeCharacter K}

/-- **Step 3. Hecke's theorem for the characters of class group type with $\psi \neq 1$.** This is the conclusion of `Langlands.HeckeFunctionalEquationAt K` for $\chi$, with $\sigma = 0$, $\Lambda(s) = 2^{r_2} |d_K|^{-s/2} \xi(s, \psi)$, $\Lambda'(u) = 2^{r_2} |d_K|^{-u/2} \xi(u, \psi^{-1})$ and $W = \psi([\mathfrak{d}])$, where $\mathfrak{d}$ is the different. The function $\Lambda$ is entire. -/
theorem IsClassType.heckeFunctionalEquation_of_ne_one (hχ : IsClassType χ)
    (hψ : classChar χ hχ ≠ 1) (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
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
  set ψ := classChar χ hχ with hψdef
  have hψ' : ψ⁻¹ ≠ 1 := fun h =>
    hψ (MonoidHom.ext fun C => by simpa using DFunLike.congr_fun h C)
  have hφ' : ∀ v, ψ⁻¹ (ClassGroup.mk0 (primeNZ v)) = primeValue χ⁻¹ v := fun v => by
    rw [MonoidHom.inv_apply, hψdef, hχ.classChar_mk0_primeNZ, primeValue_inv]
  have hsq (s : ℂ) : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s = 1 := by
    have hc : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
      (Complex.ofReal_ne_zero.2
        (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
    rw [Complex.cpow_neg, inv_mul_cancel₀ hc]
  have hd : Differentiable ℂ (fun s => 2 ^ nrComplexPlaces K *
      ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * classCharLambda ψ s) :=
    (differentiable_heckeFactor K).mul (differentiable_classCharLambda ψ)
  have hd' : Differentiable ℂ (fun s => 2 ^ nrComplexPlaces K *
      ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * classCharLambda ψ⁻¹ s) :=
    (differentiable_heckeFactor K).mul (differentiable_classCharLambda ψ⁻¹)
  refine ⟨0, fun x => by rw [Real.rpow_zero]; exact hχ.norm_apply x,
    fun s => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * classCharLambda ψ s,
    fun s => 2 ^ nrComplexPlaces K * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s) * classCharLambda ψ⁻¹ s,
    (ψ (ClassGroup.mk K (differentUnit K)) : ℂ),
    fun s _ => (hd.analyticAt s).meromorphicAt, fun s _ => (hd'.analyticAt s).meromorphicAt,
    fun s hs => ?_, fun s hs => ?_, norm_classGroupChar _ _, fun s => ?_,
    Or.inl fun s => hd.analyticAt s⟩
  · have hs' : 1 < s.re := by simpa using hs
    exact (hχ.completedLFunction_eq_classCharLambda hψ hn hs').symm
  · have hs' : 1 < s.re := by simpa using hs
    have hc : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
      (Complex.ofReal_ne_zero.2
        (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
    dsimp only
    rw [hχ.inv.completedLFunction_eq ψ⁻¹ hφ' hn' hs', classCharLambda_eq_classCharL _ hψ' hs',
      Complex.cpow_neg]
    field_simp
  · dsimp only
    rw [hχ.conductor_eq_one, map_one, Nat.cast_one, mul_one, Complex.ofReal_zero, sub_zero]
    have h1 := classCharLambda_one_sub ψ hψ (1 - s)
    rw [sub_sub_cancel] at h1
    rw [h1]
    linear_combination (-(2 ^ nrComplexPlaces K * (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) *
        classCharLambda ψ⁻¹ (1 - s) * ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-s))) *
        discr_cpow_mul_sqrt_cpow (K := K) s +
      (2 ^ nrComplexPlaces K * (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) *
        classCharLambda ψ⁻¹ (1 - s) * ((|discr K| : ℤ) : ℂ) ^ (1 / 2 - s) *
        ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(1 - s))) * hsq s

/-- **Step 3. Hecke's theorem for the characters of class group type.** This is the conclusion of `Langlands.HeckeFunctionalEquationAt K` for each Hecke character $\chi$ that is unramified at all finite places and trivial at all infinite places. If $\psi = 1$, then $\chi = 1$ and the result is `Langlands.Tate.heckeFunctionalEquationAt_one`. Otherwise it is `IsClassType.heckeFunctionalEquation_of_ne_one`. -/
theorem IsClassType.heckeFunctionalEquation (hχ : IsClassType χ)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ)
    (hn : ∀ v, χ.IsArchimedeanParameter v (n v) (t v))
    (hn' : ∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) :
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
  by_cases hψ : classChar χ hχ = 1
  · obtain rfl := hχ.eq_one_of_classChar_eq_one hψ
    exact heckeFunctionalEquationAt_one K n n' t t' hn hn'
  · exact hχ.heckeFunctionalEquation_of_ne_one hψ n n' t t' hn hn'

end Hecke

end Langlands.Tate
