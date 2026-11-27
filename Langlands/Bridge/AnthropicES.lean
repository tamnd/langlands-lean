/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Definitions/Def_CuspForm_PrimitiveFormGamma1.lean
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Definitions/Def_FLTPrelim_Ramification.lean
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Definitions/Def_EllipticCurve_FrobeniusTrace.lean
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Definitions/Def_GaloisRep_Adic.lean
-- Ported from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2:Theorems/Thm_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt.lean
-- The ported definitions are Copyright 2026 Anthropic, PBC, released under the Apache License, Version 2.0.
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Langlands.Statements.Galois

/-!
# The bridge to the anthropics FLT port: Galois representations of eigenforms of weight 2

The repository anthropics/fermats-last-theorem (Apache 2.0) proves `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt`. This theorem attaches an $\ell$-adic Galois representation to a normalized eigenform of weight 2 on $\Gamma_1(M)$ with a character. This file copies the statement of that theorem and the definitions that it uses, and compares it with `Langlands.EichlerShimuraDeligne`.

The source is the commit `6e837e75355538c7f80bab5b956861e86c4eacc2` of anthropics/fermats-last-theorem, on the toolchain `v4.33.1`. The statement is in `Theorems/Thm_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt.lean`, and its proof is in `P2M/Sol/S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt.lean`. The definitions are in `Definitions/Def_CuspForm_PrimitiveFormGamma1.lean`, `Definitions/Def_FLTPrelim_Ramification.lean`, `Definitions/Def_EllipticCurve_FrobeniusTrace.lean` and `Definitions/Def_GaloisRep_Adic.lean`. The file `ATTRIBUTION.md` of the source does not list these definitions files as derived from a third party work, so their copyright holder is Anthropic, PBC, as the file `NOTICE` of the source states.

The source has no theorem for the weight $k > 2$. Thus this file proves only the weight 2 case of `Langlands.EichlerShimuraDeligne`, the theorem of Eichler and Shimura, and it does not give the theorem of Deligne.

## Main definitions

* `Langlands.Ported.AnthropicES.IsEigenformWith`: a cusp form on $\Gamma_1(M)$ is a normalized eigenform with character $\varepsilon$ if $a_1 = 1$, the coefficients satisfy the relations of $T_p$ for $p \nmid M$ and of $U_\ell$ for $\ell \mid M$, and the form has nebentypus $\varepsilon$.
* `Langlands.Ported.AnthropicES.GaloisRepAdic`: a free module of rank 2 over a local ring $A$ with an action of $G_\mathbb{Q}$ that is continuous for the topology of the maximal ideal.
* `Langlands.Ported.AnthropicES.EigenformGaloisRep`: the statement of `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt`, as a `Prop`.
* `Langlands.Bridge.EichlerShimuraWeightTwo`: the statement `Langlands.EichlerShimuraDeligne` for the weight $k = 2$.
* `Langlands.Bridge.IntegralCoefficientModel`, `Langlands.Bridge.PadicAlgClBaseChange`, `Langlands.Bridge.FrobeniusComparison` and `Langlands.Bridge.InertiaComparison`: the four hypotheses that close the gap between the two statements.

## Main results

* `Langlands.Bridge.isEigenformWith_of_isNormalizedEigenformWithCharacter`: a normalized eigenform with character in the sense of the project is an eigenform in the sense of the source. This is proved here, for each weight.
* `Langlands.Bridge.eichlerShimuraWeightTwo_of_eichlerShimuraDeligne`: the statement of the project gives its weight 2 case.
* `Langlands.Bridge.eichlerShimuraWeightTwo_of_anthropic`: the statement of the source and the four hypotheses give `EichlerShimuraWeightTwo`. This is the `proved-mod` form of the weight 2 case of 6.2.2 of the spec.

## The changes to the source

* The theorem of the source is the `def` `EigenformGaloisRep` of type `Prop`, with the same binders and the same conclusion. Its proof in the source is not ported. The theorem enters only as a hypothesis.
* The definitions are in the namespace `Langlands.Ported.AnthropicES` and have the last component of their source name: `ModularFormClass.qCoeff` is `qCoeff`, `CuspForm.HasNebentypus` is `HasNebentypus`, `CuspForm.IsEigenformWith` is `IsEigenformWith`, `ValuationSubring.LiesOverPrime` is `LiesOverPrime`, `ValuationSubring.inertiaSubgroupIn` is `inertiaSubgroupIn` and `ValuationSubring.IsFrobeniusAt` is `IsFrobeniusAt`. Thus the dot notation of the source is function application here. The names `GaloisActionIsAdicContinuous`, `GaloisRepAdic` and `GaloisRepAdic.IsUnramifiedAt` do not change.
* The other declarations of the source files (the lemmas on `IsEigenformWith`, `IsPrimitiveForm`, `EigenpacketOccursAt`, and the base change, residual and equivalence constructions on `GaloisRepAdic`) are not ported, because the statement does not use them.
* The definitions are otherwise copied without change. The source spelling `CuspForm (CongruenceSubgroup.Gamma1 M) 2` elaborates on the toolchain of the project to the same type as the spelling of `Langlands/Statements/Galois.lean`.

## The gap between the two statements

The two statements differ in these points.

1. The weight. The source gives the representation only for $k = 2$. The project asks for each $k \ge 2$. The case $k > 2$ needs the étale cohomology of the Kuga-Sato varieties, or of a local system on the modular curve, and the source does not have it. This file does not close this gap.
2. The eigenforms. The source asks for $a_1 = 1$, the relation $a_{pn} + \varepsilon(p) p^{k-1} a_{n/p} = a_p a_n$ for $p \nmid M$, the relation $a_{\ell n} = a_\ell a_n$ for $\ell \mid M$, and the nebentypus in the form $g(\gamma \tau) = \varepsilon(d) (c\tau + d)^k g(\tau)$. The project asks for $a_1 = 1$, multiplicative coefficients, the recursion at the prime powers, and the nebentypus with the slash operator. The passage is proved here, with $a_0 = 0$ for a cusp form.
3. The coefficients. The source gives the representation over an abstract complete discrete valuation ring $O''$ with finite residue field, which is finite over a ring $O'$ that the caller gives, together with a map $\varphi : R \to O'$ from a subring $R$ of $\mathbb{C}$ that contains the coefficients. The project asks for a representation into $GL_2(\overline{\mathbb{Q}}_\ell)$ that is continuous, and compares the traces with $a_p$ through $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$. The passage needs the integrality of the coefficients and the ring of integers of a finite extension of $\mathbb{Q}_\ell$ in $\overline{\mathbb{Q}}_\ell$ that contains them (`IntegralCoefficientModel`), and the base change of an adic representation along a continuous embedding (`PadicAlgClBaseChange`).
4. The places. The source uses valuation subrings of $\overline{\mathbb{Q}}$ over $p$, with their decomposition and inertia groups. The project uses maximal ideals of $\bar{\mathbb{Z}}$ over $p$. The localization of $\bar{\mathbb{Z}}$ at a maximal ideal $Q$ is a valuation subring over $p$ with residue field $\bar{\mathbb{Z}}/Q$. This gives `FrobeniusComparison` and `InertiaComparison`.

## References

* G. Shimura, Introduction to the arithmetic theory of automorphic functions, 1971, chapter 7.
* F. Diamond and J. Shurman, A first course in modular forms, 2005, chapters 6 and 9.
* P. Deligne, Formes modulaires et représentations l-adiques, Séminaire Bourbaki 355, 1969.
* J. Neukirch, Algebraic number theory, chapter II, sections 4 to 8.
-/

noncomputable section

namespace Langlands.Ported.AnthropicES

open UpperHalfPlane CongruenceSubgroup Polynomial

open scoped MatrixGroups

/-- The coefficient of $q^n$ in the $q$-expansion of $f$ with the parameter $q = e^{2 \pi i \tau}$. This is `ModularFormClass.qCoeff` of the source. -/
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

/-- A cusp form $g$ on $\Gamma_1(M)$ has nebentypus $\varepsilon$ if $g(\gamma \tau) = \varepsilon(d) (c \tau + d)^k g(\tau)$ for each $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(M)$. This is `CuspForm.HasNebentypus` of the source. -/
def HasNebentypus {M : ℕ} {k : ℤ} (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) :
    Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod M) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

/-- A cusp form $g$ of weight $k$ on $\Gamma_1(M)$ is a normalized eigenform with character $\varepsilon$ if $a_1 = 1$, $a_{pn} + \varepsilon(p) p^{k-1} a_{n/p} = a_p a_n$ for each prime $p \nmid M$ (with $a_{n/p} = 0$ if $p \nmid n$), $a_{\ell n} = a_\ell a_n$ for each prime $\ell \mid M$, and $g$ has nebentypus $\varepsilon$. This is `CuspForm.IsEigenformWith` of the source. -/
def IsEigenformWith {M : ℕ} {k : ℤ} (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) :
    Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ, qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

section ValuationSubring

variable {L : Type*} [Field L]

/-- A valuation subring $A$ of $L$ lies over the prime $q$ if $q$ is not a unit of $A$. This is `ValuationSubring.LiesOverPrime` of the source. -/
def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

variable (K : Type*) [Field K] [Algebra K L]

/-- The inertia group of the valuation subring $A$, as a subgroup of $\mathrm{Aut}(L/K)$. This is `ValuationSubring.inertiaSubgroupIn` of the source. -/
def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

variable {K}

/-- An element $\sigma$ of $\mathrm{Aut}(L/K)$ is a Frobenius at $q$ for the valuation subring $A$ if it is in the decomposition group of $A$ and acts as $x \mapsto x^q$ on the residue field of $A$. This is `ValuationSubring.IsFrobeniusAt` of the source. -/
def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

end ValuationSubring

/-- An action $\rho$ of $G_\mathbb{Q}$ on a module $V$ over a local ring $A$ is adically continuous if for each $n$ there is a finite extension $L$ of $\mathbb{Q}$ such that each $\sigma$ that fixes $L$ has $\rho(\sigma) v - v \in \mathfrak{m}_A^n V$ for each $v$. This is `GaloisActionIsAdicContinuous` of the source. -/
def GaloisActionIsAdicContinuous (A : Type) [CommRing A] [IsLocalRing A]
    {V : Type} [AddCommGroup V] [Module A V]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ∀ v : V, ρ σ v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A V)

/-- An adic Galois representation over a local ring $A$: a free $A$-module $V$ of rank 2 with an adically continuous action of $G_\mathbb{Q}$. This is `GaloisRepAdic` of the source. -/
structure GaloisRepAdic (A : Type) [CommRing A] [IsLocalRing A] : Type 1 where
  /-- The underlying module. -/
  V : Type
  /-- The additive group structure of `V`. -/
  [instAddCommGroup : AddCommGroup V]
  /-- The module structure of `V`. -/
  [instModule : Module A V]
  /-- The module `V` is free. -/
  [instFree : Module.Free A V]
  /-- The module `V` is finite. -/
  [instFinite : Module.Finite A V]
  /-- The rank of `V` is 2. -/
  finrank_eq : Module.finrank A V = 2
  /-- The action of $G_\mathbb{Q}$. -/
  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V
  /-- The action is adically continuous. -/
  isAdicContinuous : GaloisActionIsAdicContinuous A ρ

attribute [instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instModule
  GaloisRepAdic.instFree GaloisRepAdic.instFinite

/-- The representation $\rho$ is unramified at $q$ if it is trivial on the inertia group of each valuation subring of $\overline{\mathbb{Q}}$ over $q$. This is `GaloisRepAdic.IsUnramifiedAt` of the source. -/
def GaloisRepAdic.IsUnramifiedAt {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime P q →
    ∀ σ ∈ inertiaSubgroupIn ℚ P, ρ.ρ σ = 1

/-- **Galois representations of eigenforms of weight 2** (Eichler and Shimura), the statement of `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` of anthropics/fermats-last-theorem. Let $h$ be a normalized eigenform of weight 2 on $\Gamma_1(M)$ with character $\varepsilon$, let $\lambda$ be a prime in a finite set $S$, let $O'$ be a complete discrete valuation ring of characteristic zero with finite residue field and $\lambda \in \mathfrak{m}_{O'}$, and let $\varphi : R \to O'$ be a map from a subring $R$ of $\mathbb{C}$ that contains $b_\ell = a_\ell(h)$ and $e_\ell = \varepsilon(\ell)$ for $\ell \nmid M$ with $\ell \notin S$. Then there are a finite extension $O''$ of $O'$ of the same kind and a representation $\rho$ over $O''$ such that each Frobenius at a prime $\ell \nmid M$ with $\ell \notin S$ has the characteristic polynomial $X^2 - \varphi(b_\ell) X + \varphi(e_\ell) \ell$, and $\rho$ is unramified at each prime $\ell \nmid M$ with $\ell \ne \lambda$. -/
def EigenformGaloisRep : Prop :=
  ∀ {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (Gamma1 M) 2}
    (_hh : IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (_hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (_hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (_htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (_hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = qCoeff h ℓ)
    (_he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)),
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, IsFrobeniusAt A σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ)

end Langlands.Ported.AnthropicES

namespace Langlands.Bridge

open Ported.AnthropicES CongruenceSubgroup Polynomial

open scoped MatrixGroups ModularForm

/-- **The Galois representations of eigenforms of weight 2** (Eichler and Shimura). This is `Langlands.EichlerShimuraDeligne` for the weight $k = 2$: a normalized eigenform $f$ of weight 2 on $\Gamma_1(N)$ with character $\chi$ has, for each prime $\ell$ and each $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$, a continuous representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_\ell)$ that is unramified at each $p \nmid N \ell$, with $\iota(\mathrm{tr}\, \rho(\sigma)) = a_p$ and $\iota(\det \rho(\sigma)) = \chi(p) p$ for each Frobenius $\sigma$ at $p$. -/
def EichlerShimuraWeightTwo : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2),
    0 < N → IsNormalizedEigenformWithCharacter f χ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
      ∃ ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl ℓ), Continuous ρ ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
          IsUnramifiedAt ρ p ∧
          ∀ σ, Langlands.IsFrobeniusAt p σ →
            ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).trace = qCoeffGamma1 f p ∧
            ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).det =
              χ (p : ZMod N) * (p : ℂ) ^ ((2 : ℤ) - 1)

/-- The statement `Langlands.EichlerShimuraDeligne` gives its weight 2 case `EichlerShimuraWeightTwo`. -/
theorem eichlerShimuraWeightTwo_of_eichlerShimuraDeligne (h : EichlerShimuraDeligne) :
    EichlerShimuraWeightTwo :=
  fun N χ f hN hf ℓ _ ι => h N 2 χ f hN le_rfl hf ℓ ι

/-- A ring map $j : O \to \overline{\mathbb{Q}}_\ell$ from a local ring is adically continuous if $\|j(x)\| \to 0$ for $x \in \mathfrak{m}_O^n$ as $n \to \infty$. -/
def IsAdicContinuousHom {O : Type} [CommRing O] [IsLocalRing O] {ℓ : ℕ} [Fact ℓ.Prime]
    (j : O →+* PadicAlgCl ℓ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal O ^ n, ‖j x‖ < ε

/-- **Integral models of the coefficients.** For a normalized eigenform $f$ of weight 2 on $\Gamma_1(N)$ with character $\chi$, a prime $\ell$ and $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$, there are a complete discrete valuation ring $O$ of characteristic zero with finite residue field and $\ell \in \mathfrak{m}_O$, a map $\varphi$ from the ring $\mathbb{Z}[a_n(f), \chi]$ to $O$, and an injective adically continuous map $j : O \to \overline{\mathbb{Q}}_\ell$ with $\iota(j(\varphi(x))) = x$. One takes for $O$ the ring of integers of the finite extension of $\mathbb{Q}_\ell$ in $\overline{\mathbb{Q}}_\ell$ that $\iota^{-1}(a_n(f))$ and $\iota^{-1}(\chi(n))$ generate. This needs that the coefficients are algebraic integers that generate a number field. Reference: Shimura, Theorem 3.52, and Diamond and Shurman, Section 6.5. -/
def IntegralCoefficientModel : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2),
    0 < N → IsNormalizedEigenformWithCharacter f χ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
        (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
        (φ : coeffRing f χ →+* O) (j : O →+* PadicAlgCl ℓ),
        (ℓ : O) ∈ IsLocalRing.maximalIdeal O ∧ Function.Injective j ∧ IsAdicContinuousHom j ∧
          ∀ x : coeffRing f χ, ι (j (φ x)) = x

/-- **Base change of an adic representation to $\overline{\mathbb{Q}}_\ell$.** Let $O \to O'$ be a finite injective local map of complete discrete valuation rings of characteristic zero with finite residue fields, let $j : O \to \overline{\mathbb{Q}}_\ell$ be injective and adically continuous, and let $\rho$ be an adic representation over $O'$. Then $j$ extends to $j' : O' \to \overline{\mathbb{Q}}_\ell$, and there is a continuous representation $\rho' : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_\ell)$ such that the characteristic polynomial of $\rho'(\sigma)$ is the image under $j'$ of the one of $\rho(\sigma)$, and $\rho'(\sigma) = 1$ if $\rho(\sigma) = 1$. One takes for $\rho'$ the matrix of $\rho$ in a basis of $V$, with $j'$ applied to the entries. The extension $j'$ exists because $\overline{\mathbb{Q}}_\ell$ is algebraically closed, and it is continuous because a norm on a finite extension of a complete field is unique up to equivalence. Reference: Neukirch, Chapter II, Theorem 4.8. -/
def PadicAlgClBaseChange : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [CharZero O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')],
    Function.Injective (algebraMap O O') →
    ∀ j : O →+* PadicAlgCl ℓ, Function.Injective j → IsAdicContinuousHom j →
    ∀ ρ : GaloisRepAdic O',
      ∃ (j' : O' →+* PadicAlgCl ℓ) (ρ' : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl ℓ)),
        j'.comp (algebraMap O O') = j ∧ Continuous ρ' ∧
        (∀ σ, (ρ' σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).charpoly =
          (LinearMap.charpoly (ρ.ρ σ)).map j') ∧
        ∀ σ, ρ.ρ σ = 1 → ρ' σ = 1

/-- **The Frobenius elements at a maximal ideal and at a valuation subring.** Each arithmetic Frobenius $\sigma$ at a prime $p$ in the sense of `Langlands.IsFrobeniusAt` is a Frobenius at $p$ for a valuation subring of $\overline{\mathbb{Q}}$ over $p$ in the sense of the source. If $\sigma$ is a Frobenius at the maximal ideal $Q$ of $\bar{\mathbb{Z}}$, one takes the localization of $\bar{\mathbb{Z}}$ at $Q$. It is a valuation ring, because $\bar{\mathbb{Z}}$ is a Prüfer domain, and its residue field is $\bar{\mathbb{Z}}/Q$. -/
def FrobeniusComparison : Prop :=
  ∀ (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ), p.Prime → Langlands.IsFrobeniusAt p σ →
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p ∧
      Ported.AnthropicES.IsFrobeniusAt A σ p

/-- **The inertia groups at a maximal ideal and at a valuation subring.** Each element $\sigma$ of the inertia group of a maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$ is in the inertia group of a valuation subring of $\overline{\mathbb{Q}}$ over $p$ in the sense of the source. One takes the localization of $\bar{\mathbb{Z}}$ at $Q$. -/
def InertiaComparison : Prop :=
  ∀ p : ℕ, p.Prime → ∀ Q : Ideal AlgebraicIntegers, Q.IsMaximal →
    Q.LiesOver (Ideal.span {(p : ℤ)}) →
    ∀ σ ∈ Q.inertia (Field.absoluteGaloisGroup ℚ),
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p ∧ σ ∈ inertiaSubgroupIn ℚ A

/-- The relation $a_{pn} + c\, a_{n/p} = a_p a_n$ (with $a_{n/p} = 0$ if $p \nmid n$) follows from $a_0 = 0$, the multiplicativity of $a$ and the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - c\, a_{p^r}$. -/
theorem hecke_relation_of_recursion {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (c : ℂ) (h0 : a 0 = 0)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c * a (p ^ r)) (n : ℕ) :
    a (p * n) + c * (if p ∣ n then a (n / p) else 0) = a p * a n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : ∀ s : ℕ, (p ^ s).Coprime m :=
    fun s => Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  rcases r with _ | s
  · simp only [pow_zero, one_mul, hm, ite_false, mul_zero, add_zero]
    exact hmul p m ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  · have h1 : p * (p ^ (s + 1) * m) = p ^ (s + 2) * m := by ring
    have h2 : p ∣ p ^ (s + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero s)) m
    have h3 : p ^ (s + 1) * m / p = p ^ s * m := by
      rw [pow_succ, mul_comm (p ^ s) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    simp only [h1, h2, h3, ↓reduceIte]
    rw [hmul _ _ (hcop _), hmul _ _ (hcop _), hmul _ _ (hcop _), hrec s]
    ring

/-- A normalized eigenform with character $\chi$ in the sense of `Langlands.IsNormalizedEigenformWithCharacter` is an eigenform with character $\chi$ in the sense of the source. -/
theorem isEigenformWith_of_isNormalizedEigenformWithCharacter {N : ℕ} {k : ℤ}
    {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k}
    (hf : IsNormalizedEigenformWithCharacter f χ) : IsEigenformWith χ f := by
  have hT : ModularGroup.T ∈ Gamma1 N := by
    rw [Gamma1_mem]
    simp [ModularGroup.T]
  have h0 : qCoeffGamma1 f 0 = 0 := by
    have h1 : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
      exact AddSubgroup.mem_zmultiples 1
    exact CuspFormClass.qExpansion_coeff_zero f one_pos h1
  have hrel : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      qCoeffGamma1 f (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeffGamma1 f (n / p) else 0) = qCoeffGamma1 f p * qCoeffGamma1 f n :=
    fun p hp n => hecke_relation_of_recursion hp _ h0 hf.mul (fun r => hf.prime_pow p r hp) n
  refine ⟨hf.one, fun p hp _ n => hrel p hp n, fun p hp hpN n => ?_, ?_⟩
  · have hχ : χ (p : ZMod N) = 0 := by
      refine MulChar.map_nonunit χ ?_
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.dvd_iff_not_coprime hp).1 hpN
    have h := hrel p hp n
    rw [hχ, zero_mul, zero_mul, add_zero] at h
    exact h
  · intro γ hγ τ
    have h := congrFun (hf.nebentypus γ hγ) τ
    rw [ModularForm.SL_slash_apply] at h
    have hd := UpperHalfPlane.denom_ne_zero γ τ
    have hden : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
      simp [UpperHalfPlane.denom]
    rw [← hden]
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [zpow_neg, ← div_eq_mul_inv, div_eq_iff (zpow_ne_zero k hd)] at h
    rw [h]
    ring

/-- A $2 \times 2$ matrix with characteristic polynomial $X^2 - t X + d$ has trace $t$ and determinant $d$. -/
theorem trace_det_of_charpoly_eq {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K} {t d : K}
    (h : M.charpoly = X ^ 2 - C t * X + C d) : M.trace = t ∧ M.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h1 := congrArg (fun q : K[X] => q.coeff 1) h
  have h0 := congrArg (fun q : K[X] => q.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_one, coeff_C, coeff_X_zero]
    at h1 h0
  norm_num at h1 h0
  exact ⟨h1, h0⟩

/-- **The weight 2 case of Eichler, Shimura and Deligne from the anthropics FLT port**, `proved-mod` the hypotheses `IntegralCoefficientModel`, `PadicAlgClBaseChange`, `FrobeniusComparison` and `InertiaComparison`. The statement `EigenformGaloisRep` of the source enters only as a hypothesis. This is the weight 2 case of `Langlands.EichlerShimuraDeligne`, not the full statement. -/
theorem eichlerShimuraWeightTwo_of_anthropic (hS : EigenformGaloisRep)
    (hC : IntegralCoefficientModel) (hB : PadicAlgClBaseChange) (hF : FrobeniusComparison)
    (hI : InertiaComparison) : EichlerShimuraWeightTwo := by
  intro N χ f hN hf ℓ _ ι
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨O, _, _, _, _, _, _, φ, j, hℓO, hjinj, hjcont, hιj⟩ := hC N χ f hN hf ℓ ι
  let b : ℕ → coeffRing f χ := fun n => ⟨qCoeffGamma1 f n, qCoeffGamma1_mem_coeffRing f χ n⟩
  let e : ℕ → coeffRing f χ := fun n => ⟨χ (n : ZMod N), character_mem_coeffRing f χ _⟩
  obtain ⟨O'', _, _, _, _, _, _, _, _, _, hinj, ρ, hfrob, hunr⟩ :=
    hS (isEigenformWith_of_isNormalizedEigenformWithCharacter hf) ℓ {ℓ}
      (Finset.mem_singleton_self ℓ) O hℓO (coeffRing f χ) (coeffRing f χ).val
      Subtype.val_injective φ b e (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  obtain ⟨j', ρ', hj', hcont, hchar, hone⟩ := hB ℓ O O'' hinj j hjinj hjcont ρ
  refine ⟨ρ', hcont, fun p hp hpNℓ => ?_⟩
  have hpN : ¬ p ∣ N := fun h => hpNℓ (Dvd.dvd.mul_right h ℓ)
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    exact hpNℓ (Dvd.intro_left N rfl)
  refine ⟨fun Q hQ hQp σ hσ => ?_, fun σ hσ => ?_⟩
  · obtain ⟨A, hA, hσA⟩ := hI p hp Q hQ hQp σ hσ
    exact hone σ (hunr p hp hpN hpℓ A hA σ hσA)
  · obtain ⟨A, hA, hAσ⟩ := hF p σ hp hσ
    have hc := hfrob p hp hpN (by simpa using hpℓ) A hA σ hAσ
    have hjj : ∀ x : O, j' (algebraMap O O'' x) = j x := fun x => congrArg (· x) hj'
    have h := hchar σ
    rw [hc] at h
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hjj] at h
    obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq h
    refine ⟨?_, ?_⟩
    · rw [htr, hιj]
    · rw [hdet, map_mul, map_mul, map_natCast, hιj, map_natCast]
      norm_num
      exact Or.inl rfl

end Langlands.Bridge
