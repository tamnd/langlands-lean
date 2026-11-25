/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The Hasse-Weil zeta function of a variety over a number field

This file states one row of 6.2.2 of the spec, `Langlands.HasseWeil`: the Hasse-Weil zeta function of a smooth proper variety over a number field continues to a meromorphic function on $\mathbb{C}$. The statement is a `def` of type `Prop`. It is an open conjecture in general. It is known for curves of genus zero and one over $\mathbb{Q}$, for abelian varieties with complex multiplication, for some Shimura varieties and in a few other cases.

## The mathematics

Let $K$ be a number field with ring of integers $\mathcal{O}_K$. For a maximal ideal $v$ of $\mathcal{O}_K$ write $k(v) = \mathcal{O}_K / v$ and $N(v) = |k(v)|$. Let $X$ be a smooth proper variety over $K$. Choose a model of $X$: a proper scheme $\mathcal{X}$ over $\mathcal{O}_K$ with generic fiber $X$. For all but finitely many $v$ the model is smooth over the local ring $\mathcal{O}_{K, v}$. These are the places of good reduction of the model.

For a good place $v$ the special fiber $\mathcal{X}_v$ is a smooth proper variety over the finite field $k(v)$. Its zeta function is
$$Z(\mathcal{X}_v, T) = \exp\Big( \sum_{m \ge 1} |\mathcal{X}_v(\mathbb{F}_{N(v)^m})| \frac{T^m}{m} \Big) = \prod_{x} (1 - T^{\deg x})^{-1},$$
where $x$ runs over the closed points of $\mathcal{X}_v$ and $\deg x = [k(x) : k(v)]$. By the work of Dwork and Grothendieck it is a rational function of $T$. By Grothendieck it is $\prod_i P_i(T)^{(-1)^{i+1}}$ with $P_i(T) = \det(1 - T \, \mathrm{Frob}_v \mid H^i_{et})$, and by Deligne the roots of $P_i$ have absolute value $N(v)^{-i/2}$.

The Hasse-Weil zeta function, in the form of Serre, is the product of these factors at $T = N(v)^{-s}$:
$$\zeta_X(s) = \prod_{v \text{ good}} Z(\mathcal{X}_v, N(v)^{-s}) = \prod_{x} (1 - N(x)^{-s})^{-1},$$
where $x$ runs over the closed points of $\mathcal{X}$ that lie over a good place and $N(x) = |k(x)|$. A closed point of $\mathcal{X}$ lies over a maximal ideal of $\mathcal{O}_K$ and has a finite residue field. The product converges absolutely for $\mathrm{Re}(s) > \dim X + 1$. This is a theorem of Lang and Serre, from the Lang-Weil estimate $|\mathcal{X}_v(\mathbb{F}_{q})| = O(q^{\dim X})$.

The conjecture of Hasse and Weil says that $\zeta_X$ continues to a meromorphic function on $\mathbb{C}$ and satisfies a functional equation under $s \mapsto \dim X + 1 - s$. For $X = \mathrm{Spec}\, K$ the function $\zeta_X$ is the Dedekind zeta function $\zeta_K$. For $X = \mathbb{P}^1_K$ it is $\zeta_K(s) \zeta_K(s - 1)$. For an elliptic curve $E$ over $\mathbb{Q}$ it is $\zeta(s) \zeta(s - 1) / L(E, s)$, so the conjecture follows from the modularity of $E$.

## Implementation notes

The variety and its model are given together as a morphism of schemes $f : \mathcal{X} \to \mathrm{Spec}\, \mathcal{O}_K$. The statement asks that $f$ is proper and that its generic fiber, the base change to $\mathrm{Spec}\, K$, is smooth. A place $v$ is good (`IsGoodPlace`) if the base change of $f$ to $\mathrm{Spec}\, \mathcal{O}_{K, v}$ is smooth. The zeta function `hasseWeilZeta` is the Euler product over the closed points of $\mathcal{X}$ over the good places, written as a `tprod`. At a closed point $x$ the residue field `X.residueField x` is finite, and its cardinality is $N(x)$.

The statement differs from the textbook form in these ways.

* It uses a proper model, not a projective one. Mathlib does not have projective morphisms. A smooth projective variety over $K$ has a projective model over $\mathcal{O}_K$, so the statement for proper models implies the statement for projective varieties.
* The set of good places depends on the model. Two models agree over a dense open subset of $\mathrm{Spec}\, \mathcal{O}_K$, so they have the same good places outside a finite set. At a finite set of places the local factor $Z(\mathcal{X}_v, N(v)^{-s})$ is a rational function of $N(v)^{-s}$ that is not zero. So the meromorphic continuation does not depend on the model. The textbook form uses at the bad places the factors $\det(1 - \mathrm{Frob}_v N(v)^{-s} \mid H^i(X_{\bar K}, \mathbb{Q}_\ell)^{I_v})^{-1}$, which differ again by a finite product of such rational functions.
* It is for the zeta function. The stronger conjecture for each $L(H^i(X), s)$ is not stated, because Mathlib does not have étale cohomology.
* It does not state the functional equation. The functional equation needs the gamma factors at the infinite places, which need the Hodge numbers of $X$, and the conductor, which needs the action of inertia on étale cohomology. These are not in Mathlib.
* It asks for some half plane $\mathrm{Re}(s) > \sigma_0$ on which the meromorphic function agrees with the Euler product. On this half plane the product converges by the theorem of Lang and Serre. Outside it the value of the `tprod` is not meaningful, because a `tprod` that does not converge is $1$ by convention.

The file proves the sanity check for $X = \mathrm{Spec}\, \mathcal{O}_K$ with the identity morphism: `hasseWeilZeta_id` says that the zeta function is the Euler product $\prod_v (1 - N(v)^{-s})^{-1}$ of the Dedekind zeta function.

## References

* J.-P. Serre, Zeta and L functions, in Arithmetical algebraic geometry, Harper and Row (1965).
* J.-P. Serre, Facteurs locaux des fonctions zêta des variétés algébriques, Séminaire Delange-Pisot-Poitou 11 (1969/70), exposé 19.
* S. Lang and A. Weil, Number of points of varieties in finite fields, Amer. J. Math. 76 (1954).
* P. Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974).
* R. Hartshorne, Algebraic geometry, appendix C.
-/

namespace Langlands

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain

universe u

section HasseWeil

variable {K : Type u} [Field K] [NumberField K] {X : Scheme.{u}}

/-- The affine scheme $\mathrm{Spec}\, \mathcal{O}_K$ of the ring of integers of a number field $K$. -/
noncomputable abbrev SpecIntegers (K : Type u) [Field K] [NumberField K] : Scheme.{u} :=
  Spec (CommRingCat.of (𝓞 K))

/-- A maximal ideal $v$ of $\mathcal{O}_K$ is a good place of the model $f : \mathcal{X} \to \mathrm{Spec}\, \mathcal{O}_K$ if the base change $\mathcal{X} \times_{\mathcal{O}_K} \mathrm{Spec}\, \mathcal{O}_{K, v}$ is smooth over the local ring $\mathcal{O}_{K, v}$. Then the special fiber at $v$ is smooth over $k(v)$. -/
def IsGoodPlace (f : X ⟶ SpecIntegers K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  Smooth (pullback.snd f
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) (Localization.AtPrime v.asIdeal)))))

/-- The generic fiber $X = \mathcal{X} \times_{\mathcal{O}_K} \mathrm{Spec}\, K$ of $f : \mathcal{X} \to \mathrm{Spec}\, \mathcal{O}_K$ is smooth over $K$. -/
def HasSmoothGenericFiber (f : X ⟶ SpecIntegers K) : Prop :=
  Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K))))

/-- The closed points $x$ of $\mathcal{X}$ whose image in $\mathrm{Spec}\, \mathcal{O}_K$ is a good place $v$. The residue field $k(x)$ is a finite extension of $k(v)$. -/
def GoodClosedPoint (f : X ⟶ SpecIntegers K) : Type u :=
  {x : X // IsClosed ({x} : Set X) ∧
    ∃ v : HeightOneSpectrum (𝓞 K), IsGoodPlace f v ∧ (f x).asIdeal = v.asIdeal}

/-- The Hasse-Weil zeta function $\zeta_X(s) = \prod_x (1 - N(x)^{-s})^{-1}$ of the model $f : \mathcal{X} \to \mathrm{Spec}\, \mathcal{O}_K$, where $x$ runs over the closed points over the good places and $N(x) = |k(x)|$. It is $\prod_{v \text{ good}} Z(\mathcal{X}_v, N(v)^{-s})$. The product converges for $\mathrm{Re}(s) > \dim X + 1$. -/
noncomputable def hasseWeilZeta (f : X ⟶ SpecIntegers K) (s : ℂ) : ℂ :=
  ∏' x : GoodClosedPoint f, (1 - (Nat.card (X.residueField x.1) : ℂ) ^ (-s))⁻¹

end HasseWeil

/-- The conjecture of Hasse and Weil, in the form of meromorphic continuation of the zeta function.

Let $K$ be a number field and let $f : \mathcal{X} \to \mathrm{Spec}\, \mathcal{O}_K$ be a proper morphism with smooth generic fiber $X$. Then there are a real number $\sigma_0$ and a meromorphic function $Z$ on $\mathbb{C}$ with $Z(s) = \zeta_X(s) = \prod_x (1 - N(x)^{-s})^{-1}$ for $\mathrm{Re}(s) > \sigma_0$. Here $x$ runs over the closed points of $\mathcal{X}$ over the places where $\mathcal{X}$ is smooth over $\mathcal{O}_{K, v}$.

The statement does not include the functional equation, and it is for the zeta function, not for the L-functions of the single cohomology groups. The module docstring explains these choices. -/
def HasseWeil : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (X : Scheme.{u}) (f : X ⟶ SpecIntegers K),
    IsProper f → HasSmoothGenericFiber f →
      ∃ (σ₀ : ℝ) (Z : ℂ → ℂ), MeromorphicOn Z Set.univ ∧
        ∀ s : ℂ, σ₀ < s.re → Z s = hasseWeilZeta f s

section Sanity

variable (K : Type u) [Field K] [NumberField K]

/-- Every place is a good place of the model $\mathrm{Spec}\, \mathcal{O}_K$ of $\mathrm{Spec}\, K$, because the identity morphism is smooth. -/
theorem isGoodPlace_id (v : HeightOneSpectrum (𝓞 K)) : IsGoodPlace (𝟙 (SpecIntegers K)) v := by
  unfold IsGoodPlace
  infer_instance

/-- The residue field of $\mathrm{Spec}\, \mathcal{O}_K$ at a maximal ideal $v$ has $N(v)$ elements. -/
theorem natCard_residueField_spec (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card ((SpecIntegers K).residueField (⟨v.asIdeal, v.isPrime⟩ : PrimeSpectrum (𝓞 K))) =
      Ideal.absNorm v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  rw [Nat.card_congr (Scheme.Spec.residueFieldIso (CommRingCat.of (𝓞 K)) ⟨v.asIdeal, v.isPrime⟩
      ).commRingCatIsoToRingEquiv.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Equiv.ofBijective _
    (v.asIdeal.bijective_algebraMap_quotient_residueField))).symm

/-- The closed points of $\mathrm{Spec}\, \mathcal{O}_K$ over good places are the maximal ideals of $\mathcal{O}_K$, that is the nonzero primes. -/
noncomputable def goodClosedPointIdEquiv :
    GoodClosedPoint (𝟙 (SpecIntegers K)) ≃ HeightOneSpectrum (𝓞 K) where
  toFun x := ⟨(x.1 : PrimeSpectrum (𝓞 K)).asIdeal, (x.1 : PrimeSpectrum (𝓞 K)).isPrime, by
    obtain ⟨v, -, hv⟩ := x.2.2
    simpa using hv ▸ v.ne_bot⟩
  invFun v := ⟨(⟨v.asIdeal, v.isPrime⟩ : PrimeSpectrum (𝓞 K)),
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 v.isMaximal,
    v, isGoodPlace_id K v, rfl⟩
  left_inv x := rfl
  right_inv v := rfl

/-- For $\mathcal{X} = \mathrm{Spec}\, \mathcal{O}_K$ the Hasse-Weil zeta function is the Euler product $\prod_v (1 - N(v)^{-s})^{-1}$ of the Dedekind zeta function $\zeta_K$. -/
theorem hasseWeilZeta_id (s : ℂ) :
    hasseWeilZeta (𝟙 (SpecIntegers K)) s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  unfold hasseWeilZeta
  rw [← (goodClosedPointIdEquiv K).symm.tprod_eq]
  congr 1
  ext v
  rw [← natCard_residueField_spec K v]
  rfl

end Sanity

end Langlands
