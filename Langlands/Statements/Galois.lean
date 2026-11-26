/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Langlands.Statements.Modularity
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.Instances.Matrix

/-!
# Galois representations of modular forms, Serre's conjecture and Artin's conjecture

This file states four rows of 6.2.2 of the spec. Each statement is a `def` of type `Prop`. A theorem that is published but not yet formalized is a `def`, never an axiom.

* `Langlands.EichlerShimuraDeligne`: a normalized newform $f$ of weight $k \ge 2$, level $N$ and character $\chi$ has, for each prime $\ell$ and each isomorphism $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$, a continuous representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_\ell)$ that is unramified at each $p \nmid N \ell$, with $\iota(\mathrm{tr}\, \rho(\mathrm{Frob}_p)) = a_p$ and $\iota(\det \rho(\mathrm{Frob}_p)) = \chi(p) p^{k-1}$. This is the theorem of Eichler, Shimura and Deligne.
* `Langlands.SerreModularityWeak`: each continuous, odd and irreducible representation $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$ is the reduction of the representation of a newform, in the sense of traces and determinants of Frobenius at almost all primes. This is the weak form of Serre's conjecture, the theorem of Khare and Wintenberger.
* `Langlands.artinLFunction`: the Artin L-function $L(s, \rho) = \prod_v \det(1 - \rho(\mathrm{Frob}_v) N(v)^{-s} \mid V^{I_v})^{-1}$ of a complex representation of $\mathrm{Gal}(L/K)$, with the factors at the ramified primes.
* `Langlands.ArtinConjecture`: for a nontrivial irreducible complex representation $\rho$ of $\mathrm{Gal}(L/K)$, the function $L(s, \rho)$ continues to an entire function. This is an open conjecture.
* `Langlands.ArtinOdd2Q`: for an odd irreducible representation $\rho : \mathrm{Gal}(L/\mathbb{Q}) \to GL_2(\mathbb{C})$, the function $L(s, \rho)$ is entire and is the L-function of a newform of weight one. This is the theorem of Khare and Wintenberger and of Kisin, with the earlier cases of Langlands, Tunnell, Buzzard, Dickinson, Shepherd-Barron, Taylor and Kassaei.

The fidelity checks of spec 06.3 for these statements are in `Langlands.Fidelity.Galois`.

## Implementation notes

The modular forms are cusp forms on $\Gamma_1(N)$ with a Dirichlet character $\chi$ modulo $N$, the nebentypus: $f |_k \gamma = \chi(d) f$ for $\gamma \in \Gamma_0(N)$ with lower right entry $d$. As in `Langlands.IsNormalizedEigenform`, the Hecke operators are replaced by the equivalent conditions on the $q$-expansion. The structure `IsNormalizedEigenformWithCharacter` asks for $a_1 = 1$, for multiplicative coefficients and for the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - \chi(p) p^{k-1} a_{p^r}$ at each prime $p$. A Dirichlet character in Mathlib is zero at the primes that divide $N$, so at these primes this is the condition for an eigenvector of $U_p$.

The statements use normalized eigenforms of level $N$, not newforms. Mathlib does not have oldforms yet. By the theory of Atkin and Lehner, the eigenvalues of $T_p$ for $p \nmid N$ of an eigenform of level $N$ are those of a newform of a level $M \mid N$. So the statements for eigenforms and for newforms are equivalent. In `ArtinOdd2Q` the equality of all the Dirichlet coefficients, at the ramified primes too, makes the eigenform a newform.

The absolute Galois group is `Field.absoluteGaloisGroup ℚ` with the Krull topology. It acts on the ring $\bar{\mathbb{Z}}$ of algebraic integers in $\overline{\mathbb{Q}}$. An element $\sigma$ is a Frobenius at $p$ (`IsFrobeniusAt`) if $\sigma(x) \equiv x^p$ modulo some maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$. This is the arithmetic Frobenius, in the form `IsArithFrobAt` of Mathlib. The inertia group at $Q$ is `Ideal.inertia`, and a representation is unramified at $p$ if it is trivial on the inertia group of each $Q$ over $p$. Then $\rho(\mathrm{Frob}_p)$ is well defined up to conjugation.

The statements use the arithmetic Frobenius, as in Diamond and Shurman, Theorem 9.6.5. With the geometric Frobenius, the representation that comes from the étale cohomology of the modular curve is the dual of $\rho$. For a representation of dimension 2 the dual is $\rho \otimes \det \rho^{-1}$, so the two statements are equivalent.

The $\ell$-adic coefficients are in the algebraic closure `PadicAlgCl ℓ` of $\mathbb{Q}_\ell$ with the topology of the spectral norm. A continuous representation of the compact group $G_\mathbb{Q}$ into $GL_2(\overline{\mathbb{Q}}_\ell)$ takes values in $GL_2(E)$ for a finite extension $E$ of $\mathbb{Q}_\ell$, by the Baire category theorem. The statement takes an explicit isomorphism of fields $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$, as decided in 6.2.3 of the spec. Such an isomorphism exists, because both fields are algebraically closed of characteristic zero and of the cardinality of the continuum. The statement is for each $\iota$.

The residual representations of `SerreModularityWeak` take values in $GL_2(\overline{\mathbb{F}}_p)$ with the discrete topology. Continuity is the condition that the kernel is open. The reduction of a newform is a ring homomorphism $\theta$ from the ring $\mathbb{Z}[a_n, \chi]$ generated by the coefficients and the values of $\chi$ to $\overline{\mathbb{F}}_p$. Such a homomorphism is the reduction modulo a prime $\lambda \mid p$ of this ring, followed by an embedding of the residue field. The condition at a prime $q \nmid Np$ is $\mathrm{tr}\, \bar\rho(\mathrm{Frob}_q) = \theta(a_q)$ and $\det \bar\rho(\mathrm{Frob}_q) = \theta(\chi(q)) q^{k-1}$. By the Chebotarev density theorem and the theorem of Brauer and Nesbitt, this is the condition that $\bar\rho$ is isomorphic to the semisimplification of the reduction of $\rho_{f, \lambda}$.

A complex conjugation is an element $c$ with $j(c(x)) = \overline{j(x)}$ for an embedding $j$ into $\mathbb{C}$. All complex conjugations are conjugate, so a representation is odd if $\det \rho(c) = -1$ for each of them.

The Artin L-function uses, at a prime $v$ of $K$, a maximal ideal $P$ of $\mathcal{O}_L$ over $v$ and an arithmetic Frobenius $\sigma$ at $P$, both chosen with `Classical.epsilon`. On the space $V^{I}$ of invariants of the inertia group $I$ of $P$, the factor is computed with the projector $e_I = |I|^{-1} \sum_{\tau \in I} \rho(\tau)$ onto $V^I$: $\det(1 - T \rho(\sigma) \mid V^I) = \det(1 - T \rho(\sigma) e_I)$ on $V$. This holds because $\rho(\sigma) e_I$ is zero on the complement $\ker e_I$ and has image in $V^I$. The value does not depend on the choice of $P$ and $\sigma$, because two Frobenius elements at $P$ differ by an element of $I$, and the primes over $v$ are conjugate. The Euler product converges absolutely for $\mathrm{Re}(s) > 1$.

## References

* P. Deligne, Formes modulaires et représentations l-adiques, Séminaire Bourbaki 355, 1969.
* G. Shimura, Introduction to the arithmetic theory of automorphic functions, 1971, chapter 7.
* F. Diamond and J. Shurman, A first course in modular forms, 2005, chapter 9.
* J.-P. Serre, Sur les représentations modulaires de degré 2 de Gal(Q̄/Q), Duke Math. J. 54 (1987).
* C. Khare and J.-P. Wintenberger, Serre's modularity conjecture (I) and (II), Invent. Math. 178 (2009).
* M. Kisin, Modularity of 2-adic Barsotti-Tate representations, Invent. Math. 178 (2009).
* E. Artin, Über eine neue Art von L-Reihen, Abh. Math. Sem. Hamburg 3 (1923), and Zur Theorie der L-Reihen mit allgemeinen Gruppencharakteren, ibid. 8 (1930).
* P. Deligne and J.-P. Serre, Formes modulaires de poids 1, Ann. Sci. ENS 7 (1974).
* J. Neukirch, Algebraic number theory, chapter VII, section 10.
-/

namespace Langlands

open NumberField IsDedekindDomain ComplexConjugate CongruenceSubgroup

open scoped MatrixGroups ModularForm

universe u

/-! ### Modular forms with a character -/

/-- The $q$-expansion of a cusp form on $\Gamma_1(N)$, at the cusp $\infty$ with width 1. -/
noncomputable def qCoeffGamma1 {N : ℕ} {k : ℤ}
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

/-- A cusp form on $\Gamma_1(N)$ has nebentypus $\chi$ if $f |_k \gamma = \chi(d) f$ for each $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N)$. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) • ⇑f

/-- A cusp form of weight $k$ on $\Gamma_1(N)$ is a normalized Hecke eigenform with character $\chi$ if it has nebentypus $\chi$ and its $q$-expansion has $a_1 = 1$, is multiplicative, and satisfies $a_{p^{r+2}} = a_p a_{p^{r+1}} - \chi(p) p^{k-1} a_{p^r}$ at each prime $p$. These are the conditions for an eigenvector of each Hecke operator $T_n$ with $a_1 = 1$. At a prime $p \mid N$ one has $\chi(p) = 0$, and the condition is the one for $U_p$. -/
structure IsNormalizedEigenformWithCharacter {N : ℕ} {k : ℤ}
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (χ : DirichletCharacter ℂ N) :
    Prop where
  nebentypus : HasNebentypus f χ
  one : qCoeffGamma1 f 1 = 1
  mul : ∀ m n : ℕ, m.Coprime n → qCoeffGamma1 f (m * n) = qCoeffGamma1 f m * qCoeffGamma1 f n
  prime_pow : ∀ p r : ℕ, p.Prime →
    qCoeffGamma1 f (p ^ (r + 2)) = qCoeffGamma1 f p * qCoeffGamma1 f (p ^ (r + 1)) -
      χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * qCoeffGamma1 f (p ^ r)

/-! ### The absolute Galois group of the rationals -/

/-- The absolute Galois group $G_\mathbb{Q}$ acts on $\overline{\mathbb{Q}}$. Instance search does not unfold `Field.absoluteGaloisGroup`, so the action is given here. -/
noncomputable instance : MulSemiringAction (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ) :=
  inferInstanceAs (MulSemiringAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) _)

/-- The ring $\bar{\mathbb{Z}}$ of algebraic integers of $\overline{\mathbb{Q}}$. The group $G_\mathbb{Q}$ acts on it. -/
abbrev AlgebraicIntegers : Type :=
  𝓞 (AlgebraicClosure ℚ)

/-- An element $\sigma \in G_\mathbb{Q}$ is an arithmetic Frobenius at the prime $p$ if there is a maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$ with $\sigma(x) \equiv x^p \pmod Q$ for each $x \in \bar{\mathbb{Z}}$. -/
def IsFrobeniusAt (p : ℕ) (σ : Field.absoluteGaloisGroup ℚ) : Prop :=
  ∃ Q : Ideal AlgebraicIntegers, Q.IsMaximal ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧
    IsArithFrobAt ℤ σ Q

/-- A homomorphism from $G_\mathbb{Q}$ is unramified at $p$ if it is trivial on the inertia group of each maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$. The inertia group of $Q$ is the group of the $\sigma$ with $\sigma(x) \equiv x \pmod Q$ for each $x$. -/
def IsUnramifiedAt {H : Type*} [Group H] (ρ : Field.absoluteGaloisGroup ℚ →* H) (p : ℕ) : Prop :=
  ∀ Q : Ideal AlgebraicIntegers, Q.IsMaximal → Q.LiesOver (Ideal.span {(p : ℤ)}) →
    ∀ σ ∈ Q.inertia (Field.absoluteGaloisGroup ℚ), ρ σ = 1

/-- An element $c \in G_\mathbb{Q}$ is a complex conjugation if $j(c(x)) = \overline{j(x)}$ for an embedding $j : \overline{\mathbb{Q}} \to \mathbb{C}$. -/
def IsComplexConjugation (c : Field.absoluteGaloisGroup ℚ) : Prop :=
  ∃ j : AlgebraicClosure ℚ →+* ℂ, ∀ x, j (c • x) = conj (j x)

/-- A representation $\rho : G \to GL_n(F)$ is irreducible if $n > 0$ and the only subspaces of $F^n$ that are stable under each $\rho(g)$ are $0$ and $F^n$. For an algebraically closed field $F$ this is absolute irreducibility. -/
def IsIrreducibleRep {F : Type*} [Field F] {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* GL (Fin n) F) : Prop :=
  0 < n ∧ ∀ W : Submodule F (Fin n → F),
    (∀ g : G, ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) F).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- A representation $\rho : G_\mathbb{Q} \to GL_2(F)$ is odd if $\det \rho(c) = -1$ for each complex conjugation $c$. -/
def IsOddRep {F : Type*} [Field F] (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) F) : Prop :=
  ∀ c, IsComplexConjugation c → (ρ c : Matrix (Fin 2) (Fin 2) F).det = -1

/-! ### Eichler, Shimura and Deligne -/

/-- **The Galois representations of modular forms** (Eichler and Shimura for $k = 2$, Deligne for $k \ge 2$). Let $f$ be a normalized eigenform of weight $k \ge 2$ on $\Gamma_1(N)$ with character $\chi$, let $\ell$ be a prime and let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ be an isomorphism of fields. Then there is a continuous representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_\ell)$ such that, at each prime $p \nmid N \ell$, $\rho$ is unramified and each arithmetic Frobenius $\sigma$ at $p$ has $\iota(\mathrm{tr}\, \rho(\sigma)) = a_p(f)$ and $\iota(\det \rho(\sigma)) = \chi(p) p^{k-1}$.

The textbook form is for a newform and a finite extension $E_\lambda$ of $\mathbb{Q}_\ell$ that contains the coefficients. The statement differs from it in these points. It is for each normalized eigenform, which has the eigenvalues of a newform at the primes $p \nmid N$. The coefficients are in $\overline{\mathbb{Q}}_\ell$, and a continuous representation of $G_\mathbb{Q}$ there takes values in a finite extension of $\mathbb{Q}_\ell$. The comparison with $\mathbb{C}$ is through an explicit $\iota$. The compatibility of the system in $\ell$ is the condition at Frobenius, for each $\ell$. -/
def EichlerShimuraDeligne : Prop :=
  ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    0 < N → 2 ≤ k → IsNormalizedEigenformWithCharacter f χ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
      ∃ ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl ℓ), Continuous ρ ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
          IsUnramifiedAt ρ p ∧
          ∀ σ, IsFrobeniusAt p σ →
            ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).trace = qCoeffGamma1 f p ∧
            ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).det =
              χ (p : ZMod N) * (p : ℂ) ^ (k - 1)

/-! ### Serre's conjecture -/

/-- The subring $\mathbb{Z}[a_n(f), \chi]$ of $\mathbb{C}$ generated by the coefficients of $f$ and the values of $\chi$. -/
def coeffRing {N : ℕ} {k : ℤ} (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ N) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ (Set.range (qCoeffGamma1 f) ∪ Set.range χ)

theorem qCoeffGamma1_mem_coeffRing {N : ℕ} {k : ℤ}
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (χ : DirichletCharacter ℂ N) (n : ℕ) :
    qCoeffGamma1 f n ∈ coeffRing f χ :=
  Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)

theorem character_mem_coeffRing {N : ℕ} {k : ℤ}
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (χ : DirichletCharacter ℂ N)
    (x : ZMod N) : χ x ∈ coeffRing f χ :=
  Algebra.subset_adjoin (Or.inr ⟨x, rfl⟩)

/-- **Serre's modularity conjecture, weak form** (Khare and Wintenberger, with Kisin for $p = 2$). Let $p$ be a prime and let $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$ be continuous (its kernel is open), irreducible and odd. Then there are a level $N \ge 1$, a weight $k \ge 2$, a character $\chi$ modulo $N$, a normalized eigenform $f$ of weight $k$ on $\Gamma_1(N)$ with character $\chi$, and a ring homomorphism $\theta : \mathbb{Z}[a_n(f), \chi] \to \overline{\mathbb{F}}_p$, such that each arithmetic Frobenius $\sigma$ at a prime $q \nmid N p$ has $\mathrm{tr}\, \bar\rho(\sigma) = \theta(a_q(f))$ and $\det \bar\rho(\sigma) = \theta(\chi(q)) q^{k-1}$.

This is the weak form of the conjecture in section 3 of the paper of Serre: some level and some weight. The strong form, with the level $N(\bar\rho)$ (the prime-to-$p$ Artin conductor) and the weight $k(\bar\rho)$ of Serre, is not stated here. Its definition needs the higher ramification groups at the primes $q \ne p$ and the restriction of $\bar\rho$ to the inertia group at $p$, with the fundamental characters of level 1 and 2 and the distinction between peu and très ramifié. The strong form follows from the weak form by the work of Ribet, Edixhoven, Carayol, Diamond and Buzzard, and Khare and Wintenberger prove both. In characteristic 2 one has $-1 = 1$, so the condition to be odd holds for each $\bar\rho$, as in the conjecture of Serre. -/
def SerreModularityWeak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (AlgebraicClosure (ZMod p))),
    IsOpen (ρ.ker : Set (Field.absoluteGaloisGroup ℚ)) → IsIrreducibleRep ρ → IsOddRep ρ →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
      (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (θ : coeffRing f χ →+* AlgebraicClosure (ZMod p)),
      0 < N ∧ 2 ≤ k ∧ IsNormalizedEigenformWithCharacter f χ ∧
      ∀ q : ℕ, q.Prime → ¬ q ∣ N * p → ∀ σ, IsFrobeniusAt q σ →
        (ρ σ : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod p))).trace =
          θ ⟨qCoeffGamma1 f q, qCoeffGamma1_mem_coeffRing f χ q⟩ ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod p))).det =
          θ ⟨χ (q : ZMod N), character_mem_coeffRing f χ q⟩ *
            (q : AlgebraicClosure (ZMod p)) ^ (k - 1)

/-! ### Artin L-functions -/

section Artin

variable {K : Type u} [Field K] [NumberField K] {L : IntermediateField K (AlgebraicClosure K)}
  {n : ℕ}

/-- A maximal ideal of $\mathcal{O}_L$ over the prime $v$ of $K$, chosen with `Classical.epsilon`. -/
noncomputable def primeAbove (L : IntermediateField K (AlgebraicClosure K))
    (v : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 L) :=
  Classical.epsilon fun P : Ideal (𝓞 L) => P.IsMaximal ∧ P.LiesOver v.asIdeal

/-- An arithmetic Frobenius in $\mathrm{Gal}(L/K)$ at `primeAbove L v`, chosen with `Classical.epsilon`. -/
noncomputable def frobeniusAbove (L : IntermediateField K (AlgebraicClosure K))
    (v : HeightOneSpectrum (𝓞 K)) : Gal(L/K) :=
  Classical.epsilon fun σ : Gal(L/K) => IsArithFrobAt (𝓞 K) σ (primeAbove L v)

/-- The projector $e_I = |I|^{-1} \sum_{\tau \in I} \rho(\tau)$ onto the invariants of the inertia group $I$ of a prime $P$ of $\mathcal{O}_L$. -/
noncomputable def inertiaProjector (ρ : Gal(L/K) →* GL (Fin n) ℂ) (P : Ideal (𝓞 L)) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Nat.card (P.inertia Gal(L/K)) : ℂ)⁻¹ •
    ∑ᶠ τ : P.inertia Gal(L/K), (ρ τ : Matrix (Fin n) (Fin n) ℂ)

/-- The local factor $\det(1 - \rho(\mathrm{Frob}_v) N(v)^{-s} \mid V^{I_v})^{-1}$ of the Artin L-function at a prime $v$ of $K$, computed as $\det(1 - N(v)^{-s} \rho(\sigma) e_I)^{-1}$ on $V = \mathbb{C}^n$. -/
noncomputable def artinLocalFactor (ρ : Gal(L/K) →* GL (Fin n) ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  ((1 : Matrix (Fin n) (Fin n) ℂ) - ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) •
      ((ρ (frobeniusAbove L v) : Matrix (Fin n) (Fin n) ℂ) *
        inertiaProjector ρ (primeAbove L v))).det⁻¹

/-- The Artin L-function $L(s, \rho) = \prod_v \det(1 - \rho(\mathrm{Frob}_v) N(v)^{-s} \mid V^{I_v})^{-1}$, the product over all the finite primes of $K$. It converges absolutely for $\mathrm{Re}(s) > 1$. -/
noncomputable def artinLFunction (ρ : Gal(L/K) →* GL (Fin n) ℂ) (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 K), artinLocalFactor ρ v s

end Artin

/-- **Artin's conjecture** (open). Let $L/K$ be a finite Galois extension of number fields and let $\rho : \mathrm{Gal}(L/K) \to GL_n(\mathbb{C})$ be an irreducible representation that is not the trivial representation. Then there is an entire function that is equal to $L(s, \rho)$ for $\mathrm{Re}(s) > 1$.

The meromorphic continuation and the functional equation are theorems of Artin and Brauer. The conjecture is that $L(s, \rho)$ has no pole. The statement is about the L-function without the archimedean factors. These factors have no zeros, so an entire completed L-function gives an entire $L(s, \rho)$. The converse uses the functional equation, because the archimedean factors have poles. An irreducible representation with $n \ge 2$ is never trivial, so the condition $\rho \ne 1$ excludes only the trivial character, whose L-function is the Dedekind zeta function. -/
def ArtinConjecture : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : IntermediateField K (AlgebraicClosure K)),
    FiniteDimensional K L → IsGalois K L →
    ∀ (n : ℕ) (ρ : Gal(L/K) →* GL (Fin n) ℂ), IsIrreducibleRep ρ → ρ ≠ 1 →
      ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 1 < s.re → F s = artinLFunction ρ s

/-- An element $c \in \mathrm{Gal}(L/\mathbb{Q})$ is a complex conjugation if $j(c(x)) = \overline{j(x)}$ for an embedding $j : L \to \mathbb{C}$. -/
def IsComplexConjugationOf {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (c : Gal(L/ℚ)) : Prop :=
  ∃ j : L →+* ℂ, ∀ x, j (c x) = conj (j x)

/-- **Artin's conjecture for odd representations of dimension 2 over $\mathbb{Q}$** (Khare and Wintenberger, Kisin; Langlands and Tunnell for solvable image). Let $L/\mathbb{Q}$ be a finite Galois extension and let $\rho : \mathrm{Gal}(L/\mathbb{Q}) \to GL_2(\mathbb{C})$ be irreducible and odd: $\det \rho(c) = -1$ for each complex conjugation $c$. Then $L(s, \rho)$ continues to an entire function, and there are a level $N \ge 1$, a character $\chi$ modulo $N$ and a normalized eigenform $f$ of weight 1 on $\Gamma_1(N)$ with character $\chi$ such that $L(s, \rho) = L(s, f) = \sum_n a_n(f) n^{-s}$ for $\mathrm{Re}(s) > 1$.

The equality of the Dirichlet series for $\mathrm{Re}(s) > 1$ is the equality of all the coefficients, at the ramified primes too. So $f$ is the newform of level the Artin conductor of $\rho$, and $\chi$ corresponds to $\det \rho$. The converse, that each newform of weight one has such a $\rho$, is the theorem of Deligne and Serre. -/
def ArtinOdd2Q : Prop :=
  ∀ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L → IsGalois ℚ L →
    ∀ ρ : Gal(L/ℚ) →* GL (Fin 2) ℂ, IsIrreducibleRep ρ →
      (∀ c : Gal(L/ℚ), IsComplexConjugationOf c → (ρ c : Matrix (Fin 2) (Fin 2) ℂ).det = -1) →
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 1 < s.re → F s = artinLFunction ρ s) ∧
      ∃ (N : ℕ) (χ : DirichletCharacter ℂ N)
        (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 1),
        0 < N ∧ IsNormalizedEigenformWithCharacter f χ ∧
        ∀ s : ℂ, 1 < s.re → artinLFunction ρ s = LSeries (qCoeffGamma1 f) s

end Langlands
