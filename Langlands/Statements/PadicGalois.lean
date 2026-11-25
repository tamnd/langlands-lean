/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Galois
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Artinian.Ring

/-!
# The Fontaine-Mazur conjecture for ordinary representations and the vocabulary of Breuil-Mézard

This file is for two rows of 6.2.2 of the spec.

* `Langlands.FontaineMazurGL2Q`: an irreducible odd representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_p)$ that is unramified at almost all primes and ordinary at $p$ of weight $k \ge 2$ comes from a modular eigenform of weight $k$, under the residual hypotheses of Kisin. This is a special form of the conjecture of Fontaine and Mazur. The condition to be de Rham at $p$ is replaced by the condition to be ordinary, which is stronger. With this condition the statement is a theorem of Kisin, and in many cases of Skinner and Wiles.
* `BreuilMezardGL2Qp`: this row is partial. The file gives the Serre weights $\mathrm{Sym}^a \otimes \det^b$ as representations of $GL_2(F)$, and the framed lifts of a residual representation $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$ to a ring $A$. It does not state the conjecture.

## The conjecture of Fontaine and Mazur

Let $p$ be a prime and let $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_p)$ be a continuous irreducible representation. The representation is geometric if it is unramified outside a finite set of primes and its restriction to a decomposition group $G_{\mathbb{Q}_p}$ at $p$ is de Rham in the sense of Fontaine. Fontaine and Mazur conjecture that a geometric representation comes from algebraic geometry. For $GL_2$ over $\mathbb{Q}$ with distinct Hodge-Tate weights and $\rho$ odd, the conjecture says that $\rho$ is the twist of the representation $\rho_f$ of a modular eigenform $f$ by a power of the cyclotomic character. Kisin proved this for $p > 2$, under two conditions on the reduction $\bar\rho$: the restriction of $\bar\rho$ to $G_{\mathbb{Q}(\zeta_p)}$ is absolutely irreducible, and the restriction of $\bar\rho$ to $G_{\mathbb{Q}_p}$ is not of the form $\begin{pmatrix} \omega \chi & * \\ 0 & \chi \end{pmatrix}$, where $\omega$ is the reduction of the cyclotomic character.

Mathlib does not have the ring $B_{dR}$ of Fontaine, so the condition to be de Rham cannot be stated. The file uses the condition to be ordinary instead. Let $\varepsilon : G_\mathbb{Q} \to \mathbb{Z}_p^\times$ be the $p$-adic cyclotomic character and let $D_Q \supset I_Q$ be the decomposition and inertia groups of a prime $Q$ of $\bar{\mathbb{Z}}$ over $p$. The representation $\rho$ is ordinary of weight $k$ at $Q$ if there is a line $L \subset \overline{\mathbb{Q}}_p^2$ that is stable under $D_Q$, such that $I_Q$ acts on $L$ by $\varepsilon^{k-1}$ and acts on $\overline{\mathbb{Q}}_p^2 / L$ trivially. Then
$$\rho|_{D_Q} \cong \begin{pmatrix} \psi_1 \varepsilon^{k-1} & * \\ 0 & \psi_2 \end{pmatrix}$$
with $\psi_1$ and $\psi_2$ unramified. The representation $\rho_f$ of an eigenform $f$ of weight $k$ whose coefficient $a_p$ is a $p$-adic unit, and whose character has conductor prime to $p$, is ordinary in this sense, by a theorem of Deligne and of Mazur and Wiles.

An ordinary representation of weight $k \ge 2$ is semistable at $p$ with Hodge-Tate weights $0$ and $k - 1$. The reason is that the extension class lies in $H^1(G_{\mathbb{Q}_p}, \psi \varepsilon^{k-1})$ with $\psi$ unramified, and the theorem of Bloch and Kato on $H^1_g$ shows that each class in this group gives a de Rham extension. So the ordinary form of the statement follows from the theorem of Kisin. The twist by a power of $\varepsilon$ in the conclusion of Kisin is trivial here, because the Hodge-Tate weights are $0$ and $k - 1$.

## The conjecture of Breuil and Mézard

Let $k$ be a finite field of characteristic $p$ and let $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$ be continuous. The framed deformation functor of $\bar\rho$ sends an Artinian local ring $A$ with residue field $k$ to the set of continuous lifts $\rho_A : G_{\mathbb{Q}_p} \to GL_2(A)$ of $\bar\rho$. It is represented by a complete local ring $R^\square(\bar\rho)$. For a Hodge-Tate type $\lambda$ and an inertial type $\tau$, Kisin constructs the quotient $R^\square(\lambda, \tau, \bar\rho)$ whose points are the potentially semistable lifts of this type. The conjecture of Breuil and Mézard says that the Hilbert-Samuel multiplicity of its special fiber is
$$e(R^\square(\lambda, \tau, \bar\rho) / \varpi) = \sum_{a, b} n_{a, b}(\lambda, \tau) \, \mu_{a, b}(\bar\rho),$$
where $n_{a, b}$ is the multiplicity of the Serre weight $\mathrm{Sym}^a k^2 \otimes \det^b$ in the reduction of the representation $\sigma(\lambda, \tau)$ of $GL_2(\mathbb{Z}_p)$ attached by Henniart to $\tau$, and $\mu_{a, b}(\bar\rho)$ are integers that depend only on $\bar\rho$ and the weight. It is a theorem of Kisin, Paškūnas, Hu and Tan for $p > 2$ in most cases.

The statement needs the universal framed deformation ring, Hilbert-Samuel multiplicities, potentially semistable representations, inertial types and the local Langlands correspondence of Henniart for the types. These are not in Mathlib. So this file does not state the conjecture. It gives the two pieces of vocabulary that can be written honestly now.

* `serreWeight a b`: the representation $\mathrm{Sym}^a \otimes \det^b$ of $GL_2(F)$ on the homogeneous polynomials of degree $a$ in two variables. For $F = \mathbb{F}_p$, $0 \le a \le p - 1$ and $0 \le b \le p - 2$ these are the irreducible representations of $GL_2(\mathbb{F}_p)$ over $\overline{\mathbb{F}}_p$, the Serre weights.
* `FramedLift p ρbar A π`: the set of framed lifts of $\bar\rho$ to a ring $A$ with a ring homomorphism $\pi : A \to k$. For an Artinian local ring $A$ with residue map $\pi$ this is the value of the framed deformation functor. The theorem `framedLift_map` gives its action on morphisms.

## Implementation notes

The Galois groups, the Frobenius elements, the inertia groups and the conditions to be unramified, odd and irreducible are those of `Langlands.Statements.Galois`. The coefficients are in `PadicAlgCl p` with the spectral norm, and the comparison with modular forms is through an isomorphism of fields $\iota : \overline{\mathbb{Q}}_p \cong \mathbb{C}$, as in `EichlerShimuraDeligne`. The eigenforms are `IsNormalizedEigenformWithCharacter`.

The decomposition group of a maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$ is the stabilizer of $Q$. It is isomorphic to $G_{\mathbb{Q}_p}$. Its inertia group is `Ideal.inertia`. The cyclotomic character is `cyclotomicCharacter` of Mathlib on $\overline{\mathbb{Q}}$, sent to $\overline{\mathbb{Q}}_p$.

The residual representation is not formed as a representation over $\overline{\mathbb{F}}_p$. The residue field of the valuation ring of $\overline{\mathbb{Q}}_p$ is $\overline{\mathbb{F}}_p$, so each condition on $\bar\rho$ can be written with congruences: $x \equiv y$ means $\|x - y\| < 1$. A conjugate $g^{-1} \rho g$ with entries of norm at most one is a lattice model of $\rho$, and its reduction is $\bar\rho$. Such a lattice exists, because $\rho$ takes values in $GL_2(E)$ for a finite extension $E$ of $\mathbb{Q}_p$ and $G_\mathbb{Q}$ is compact. The residual hypotheses are asked for each lattice model. They do not depend on the lattice: the first one makes $\bar\rho$ irreducible, so all lattices are homothetic.

* The restriction of $\bar\rho$ to $G_{\mathbb{Q}(\zeta_p)}$ is absolutely irreducible if no nonzero vector of $\overline{\mathbb{F}}_p^2$ is an eigenvector of each $\bar\rho(\sigma)$ with $\sigma(\zeta) = \zeta$ for all $p$-th roots of unity $\zeta$. For a representation of dimension two over an algebraically closed field this is irreducibility.
* The restriction of $\bar\rho$ to $D_Q$ has the form $\begin{pmatrix} \omega \chi & * \\ 0 & \chi \end{pmatrix}$ if and only if there is a stable line with character $\lambda$ such that $\lambda^2 = \omega \det \bar\rho$, because then the quotient character is $\chi = \det \bar\rho / \lambda$ and $\lambda = \omega \chi$.

The statement differs from the textbook form of the conjecture of Fontaine and Mazur in these ways.

* The condition to be de Rham is replaced by the condition to be ordinary of weight $k \ge 2$ with unramified characters $\psi_1$ and $\psi_2$. This excludes the representations that are only potentially ordinary, and all the representations that are not ordinary.
* It has the residual hypotheses of Kisin and $p > 2$. Later work of Paškūnas, Hu and Tan, and Pan removes some of these hypotheses.
* The conclusion is modularity in the sense of traces and determinants of Frobenius at the primes $\ell \nmid Np$. By the Chebotarev density theorem and the theorem of Brauer and Nesbitt this is $\rho \cong \rho_f$, because $\rho$ is irreducible.

## References

* J.-M. Fontaine and B. Mazur, Geometric Galois representations, in Elliptic curves, modular forms and Fermat's last theorem, International Press (1995).
* M. Kisin, The Fontaine-Mazur conjecture for GL2, J. Amer. Math. Soc. 22 (2009).
* M. Emerton, Local-global compatibility in the p-adic Langlands programme for GL2/Q, preprint (2011).
* C. Skinner and A. Wiles, Nearly ordinary deformations of irreducible residual representations, Ann. Fac. Sci. Toulouse Math. 10 (2001).
* S. Bloch and K. Kato, L-functions and Tamagawa numbers of motives, in The Grothendieck Festschrift I, Birkhäuser (1990).
* C. Breuil and A. Mézard, Multiplicités modulaires et représentations de GL2(Zp) et de Gal(Qp/Qp) en l = p, Duke Math. J. 115 (2002).
* M. Kisin, Potentially semi-stable deformation rings, J. Amer. Math. Soc. 21 (2008).
* V. Paškūnas, On the Breuil-Mézard conjecture, Duke Math. J. 164 (2015).
* Y. Hu and F. Tan, The Breuil-Mézard conjecture for non-scalar split residual representations, Ann. Sci. ENS 48 (2015).
* L. Pan, The Fontaine-Mazur conjecture in the residually reducible case, J. Amer. Math. Soc. 35 (2022).
-/

namespace Langlands

open NumberField CongruenceSubgroup

open scoped MatrixGroups ModularForm

section FontaineMazur

variable (p : ℕ) [Fact p.Prime]

/-- The $p$-adic cyclotomic character $\varepsilon : G_\mathbb{Q} \to \mathbb{Z}_p^\times$, with values in $\overline{\mathbb{Q}}_p$. It is defined by $\sigma(\zeta) = \zeta^{\varepsilon(\sigma)}$ for each root of unity $\zeta$ of $p$-power order. At an arithmetic Frobenius $\sigma$ at $\ell \ne p$ one has $\varepsilon(\sigma) = \ell$. -/
noncomputable def cycChar (σ : Field.absoluteGaloisGroup ℚ) : PadicAlgCl p :=
  algebraMap ℚ_[p] (PadicAlgCl p)
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p (AlgEquiv.toRingEquiv σ) : ℤ_[p]) : ℚ_[p])

/-- The decomposition group $D_Q = \{ \sigma \in G_\mathbb{Q} : \sigma(Q) \subseteq Q \}$ of a maximal ideal $Q$ of $\bar{\mathbb{Z}}$. For $Q$ over $p$ it is isomorphic to $G_{\mathbb{Q}_p}$. -/
def decompositionGroup (Q : Ideal AlgebraicIntegers) : Set (Field.absoluteGaloisGroup ℚ) :=
  {σ | ∀ x ∈ Q, σ • x ∈ Q}

/-- The subgroup $G_{\mathbb{Q}(\zeta_p)}$ of the elements of $G_\mathbb{Q}$ that fix each $p$-th root of unity. -/
def cyclotomicFixer : Set (Field.absoluteGaloisGroup ℚ) :=
  {σ | ∀ x : AlgebraicClosure ℚ, x ^ p = 1 → σ • x = x}

/-- The cyclotomic character is multiplicative: $\varepsilon(\sigma \tau) = \varepsilon(\sigma) \varepsilon(\tau)$. -/
theorem cycChar_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    cycChar p (σ * τ) = cycChar p σ * cycChar p τ := by
  simp only [cycChar, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul]
  rfl

/-- The inertia group $I_Q$ is contained in the decomposition group $D_Q$. -/
theorem inertia_subset_decompositionGroup (Q : Ideal AlgebraicIntegers) :
    (Q.inertia (Field.absoluteGaloisGroup ℚ) : Set (Field.absoluteGaloisGroup ℚ)) ⊆
      decompositionGroup Q := fun σ hσ x hx => by
  have := Ideal.mem_inertia.1 hσ x
  simpa using Q.add_mem this hx

variable {p}

/-- A vector of $\overline{\mathbb{Q}}_p^2$ is integral if its entries have norm at most one. -/
def IsIntegralVec (v : Fin 2 → PadicAlgCl p) : Prop :=
  ∀ i, ‖v i‖ ≤ 1

/-- A vector of $\overline{\mathbb{Q}}_p^2$ is primitive if it is integral and one entry has norm one. Its reduction is a nonzero vector of $\overline{\mathbb{F}}_p^2$. -/
def IsPrimitiveVec (v : Fin 2 → PadicAlgCl p) : Prop :=
  IsIntegralVec v ∧ ∃ i, ‖v i‖ = 1

/-- A representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_p)$ is integral if all entries of all $\rho(\sigma)$ have norm at most one. Then $\rho$ has a reduction $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$. -/
def IsIntegralRep (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∀ σ i j, ‖(ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl p)) i j‖ ≤ 1

/-- For an integral matrix $A$ and an integral vector $v$, the reduction of $v$ is an eigenvector of the reduction of $A$ with the eigenvalue $\bar\mu$: $\|\mu\| \le 1$ and $A v \equiv \mu v$ modulo the maximal ideal. -/
def IsResidualEigenvector (A : Matrix (Fin 2) (Fin 2) (PadicAlgCl p)) (v : Fin 2 → PadicAlgCl p)
    (μ : PadicAlgCl p) : Prop :=
  ‖μ‖ ≤ 1 ∧ ∀ i, ‖(A.mulVec v - μ • v) i‖ < 1

/-- For an integral $\rho$, the reduction $\bar\rho$ restricted to $H$ is absolutely irreducible: no nonzero vector of $\overline{\mathbb{F}}_p^2$ is an eigenvector of each $\bar\rho(\sigma)$ with $\sigma \in H$. -/
def IsResiduallyIrreducibleOn (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl p))
    (H : Set (Field.absoluteGaloisGroup ℚ)) : Prop :=
  ¬ ∃ v, IsPrimitiveVec v ∧ ∀ σ ∈ H, ∃ μ, IsResidualEigenvector (ρ σ).1 v μ

/-- The representation $\rho$ is ordinary of weight $k$ at $Q$: there is a line $L$ stable under $D_Q$, the inertia group $I_Q$ acts on $L$ by $\varepsilon^{k-1}$, and $\det \rho = \varepsilon^{k-1}$ on $I_Q$. Then $I_Q$ acts trivially on the quotient by $L$, and $\rho|_{D_Q} \cong \begin{pmatrix} \psi_1 \varepsilon^{k-1} & * \\ 0 & \psi_2 \end{pmatrix}$ with $\psi_1, \psi_2$ unramified. -/
def IsOrdinaryAt (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl p)) (k : ℕ)
    (Q : Ideal AlgebraicIntegers) : Prop :=
  ∃ v : Fin 2 → PadicAlgCl p, v ≠ 0 ∧
    (∀ σ ∈ decompositionGroup Q, ∃ μ : PadicAlgCl p, (ρ σ).1.mulVec v = μ • v) ∧
    ∀ τ ∈ Q.inertia (Field.absoluteGaloisGroup ℚ),
      (ρ τ).1.mulVec v = cycChar p τ ^ (k - 1) • v ∧ (ρ τ).1.det = cycChar p τ ^ (k - 1)

/-- For an integral $\rho$, the reduction $\bar\rho$ restricted to $D_Q$ has the form $\begin{pmatrix} \omega \chi & * \\ 0 & \chi \end{pmatrix}$ for a character $\chi$, where $\omega$ is the reduction of $\varepsilon$. This is the existence of a stable line with a character $\lambda$ such that $\lambda^2 = \omega \det \bar\rho$. -/
def HasResidualCyclotomicLine (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl p))
    (Q : Ideal AlgebraicIntegers) : Prop :=
  ∃ v, IsPrimitiveVec v ∧ ∀ σ ∈ decompositionGroup Q, ∃ μ,
    IsResidualEigenvector (ρ σ).1 v μ ∧
    ‖μ ^ 2 - cycChar p σ * (ρ σ).1.det‖ < 1

end FontaineMazur

/-- **The conjecture of Fontaine and Mazur for ordinary representations** (Kisin, and Skinner and Wiles in many cases).

Let $p > 2$ be a prime, let $\iota : \overline{\mathbb{Q}}_p \cong \mathbb{C}$ be an isomorphism of fields and let $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_p)$ be continuous, irreducible and odd, and unramified outside a finite set of primes. Let $k \ge 2$ and let $Q$ be a maximal ideal of $\bar{\mathbb{Z}}$ over $p$ such that $\rho$ is ordinary of weight $k$ at $Q$. Suppose that for each integral conjugate of $\rho$ the reduction $\bar\rho$ is absolutely irreducible on $G_{\mathbb{Q}(\zeta_p)}$ and $\bar\rho|_{D_Q}$ is not of the form $\begin{pmatrix} \omega \chi & * \\ 0 & \chi \end{pmatrix}$. Then there are a level $N \ge 1$, a character $\chi$ modulo $N$ and a normalized eigenform $f$ of weight $k$ on $\Gamma_1(N)$ with character $\chi$, such that at each prime $\ell \nmid Np$ the representation $\rho$ is unramified and each arithmetic Frobenius $\sigma$ at $\ell$ has $\iota(\mathrm{tr}\, \rho(\sigma)) = a_\ell(f)$ and $\iota(\det \rho(\sigma)) = \chi(\ell) \ell^{k-1}$.

The textbook conjecture asks only that $\rho|_{D_Q}$ is de Rham with distinct Hodge-Tate weights, and has no residual hypotheses. Here the condition to be de Rham is replaced by the stronger condition to be ordinary, and the residual hypotheses are those of the theorem of Kisin. The module docstring explains why the statement follows from the theorem of Kisin. -/
def FontaineMazurGL2Q : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : PadicAlgCl p ≃+* ℂ)
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl p)) (k : ℕ)
    (Q : Ideal AlgebraicIntegers),
    p ≠ 2 → 2 ≤ k → Continuous ρ → IsIrreducibleRep ρ → IsOddRep ρ →
    (∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → IsUnramifiedAt ρ ℓ) →
    Q.IsMaximal → Q.LiesOver (Ideal.span {(p : ℤ)}) → IsOrdinaryAt ρ k Q →
    (∀ g : GL (Fin 2) (PadicAlgCl p), IsIntegralRep ((MulAut.conj g⁻¹).toMonoidHom.comp ρ) →
      IsResiduallyIrreducibleOn ((MulAut.conj g⁻¹).toMonoidHom.comp ρ) (cyclotomicFixer p) ∧
      ¬ HasResidualCyclotomicLine ((MulAut.conj g⁻¹).toMonoidHom.comp ρ) Q) →
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N)
      (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
      0 < N ∧ IsNormalizedEigenformWithCharacter f χ ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
        IsUnramifiedAt ρ ℓ ∧ ∀ σ, IsFrobeniusAt ℓ σ →
        ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl p)).trace = qCoeffGamma1 f ℓ ∧
        ι (ρ σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl p)).det =
          χ (ℓ : ZMod N) * (ℓ : ℂ) ^ (k - 1)

section SerreWeight

open MvPolynomial

variable {F : Type*} [Field F]

/-- The linear form $g \cdot X_i = \sum_j g_{ji} X_j$. The substitution $X_i \mapsto g \cdot X_i$ is the action of $g$ on the polynomials in $X_0, X_1$, and on the linear forms it is the standard representation of $GL_2(F)$ in the basis $X_0, X_1$. -/
noncomputable def linearForm (g : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    MvPolynomial (Fin 2) F :=
  ∑ j, C (g j i) * X j

/-- The linear form $g \cdot X_i$ is homogeneous of degree one. -/
theorem isHomogeneous_linearForm (g : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    (linearForm g i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

/-- The substitution of $g$ in $h \cdot X_i$ is $(gh) \cdot X_i$. -/
theorem bind₁_linearForm (g h : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    bind₁ (linearForm g) (linearForm h i) = linearForm (g * h) i := by
  simp only [linearForm, map_sum, map_mul, bind₁_X_right, Finset.mul_sum,
    Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [bind₁_C_right]
  ring

/-- The identity matrix gives the substitution $X_i \mapsto X_i$. -/
theorem linearForm_one : linearForm (1 : Matrix (Fin 2) (Fin 2) F) = X := by
  funext i
  simp [linearForm, Matrix.one_apply]

variable (a : ℕ)

/-- The endomorphism $P(X_0, X_1) \mapsto P(g \cdot X_0, g \cdot X_1)$ of the space of homogeneous polynomials of degree $a$ in two variables. -/
noncomputable def symPowEnd (g : Matrix (Fin 2) (Fin 2) F) :
    Module.End F (homogeneousSubmodule (Fin 2) F a) :=
  (bind₁ (linearForm g)).toLinearMap.restrict fun P hP => by
    rw [mem_homogeneousSubmodule] at hP ⊢
    simpa using hP.aeval (linearForm g) (isHomogeneous_linearForm g)

/-- The representation $\mathrm{Sym}^a F^2 \otimes \det^b$ of $GL_2(F)$ on the space of homogeneous polynomials of degree $a$ in two variables: $(g P)(X_0, X_1) = \det(g)^b P(g \cdot X_0, g \cdot X_1)$. For $F = \mathbb{F}_p$, $0 \le a \le p - 1$ and $0 \le b \le p - 2$ these are the Serre weights, the irreducible representations of $GL_2(\mathbb{F}_p)$ over $\overline{\mathbb{F}}_p$. -/
noncomputable def serreWeight (b : ℕ) :
    GL (Fin 2) F →* Module.End F (homogeneousSubmodule (Fin 2) F a) where
  toFun g := (g : Matrix (Fin 2) (Fin 2) F).det ^ b • symPowEnd a g
  map_one' := by
    ext P
    simp [symPowEnd, linearForm_one]
  map_mul' g h := by
    ext P
    simp only [Units.val_mul, Matrix.det_mul, mul_pow, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.map_smul, symPowEnd, LinearMap.restrict_apply, SetLike.val_smul,
      AlgHom.toLinearMap_apply,
      bind₁_bind₁, bind₁_linearForm, smul_smul]

/-- The Serre weight $\mathrm{Sym}^0 \otimes \det^0$ is the trivial representation. -/
theorem serreWeight_zero_zero (g : GL (Fin 2) F) : serreWeight (F := F) 0 0 g = 1 := by
  ext ⟨P, hP⟩
  rw [mem_homogeneousSubmodule, ← totalDegree_zero_iff_isHomogeneous,
    totalDegree_eq_zero_iff_eq_C] at hP
  simp only [serreWeight, MonoidHom.coe_mk, OneHom.coe_mk, pow_zero, one_smul, symPowEnd,
    LinearMap.restrict_apply, AlgHom.toLinearMap_apply, Module.End.one_apply]
  rw [hP, bind₁_C_right]

end SerreWeight

section FramedLift

variable (p : ℕ) [Fact p.Prime] {k : Type*} [Field k]

/-- The framed lifts of $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$ to a ring $A$ with a ring homomorphism $\pi : A \to k$: the homomorphisms $\rho_A : G_{\mathbb{Q}_p} \to GL_2(A)$ with open kernel and $\pi \circ \rho_A = \bar\rho$. For a finite field $k$ and an Artinian local ring $A$ with a surjective $\pi$, the ring $A$ is finite and has the discrete topology, so the condition on the kernel is continuity. Then this set is the value $D^\square_{\bar\rho}(A)$ of the framed deformation functor. -/
def FramedLift (ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k) (A : Type*)
    [CommRing A]
    (π : A →+* k) : Set (Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) A) :=
  {ρ | IsOpen (ρ.ker : Set (Field.absoluteGaloisGroup ℚ_[p])) ∧
    (Matrix.GeneralLinearGroup.map π).comp ρ = ρbar}

variable {p}

/-- A continuous $\bar\rho$ is a framed lift of itself to $k$. -/
theorem mem_framedLift_self (ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k)
    (h : IsOpen (ρbar.ker : Set (Field.absoluteGaloisGroup ℚ_[p]))) :
    ρbar ∈ FramedLift p ρbar k (RingHom.id k) := by
  refine ⟨h, ?_⟩
  ext σ i j
  simp [Matrix.GeneralLinearGroup.map]

/-- The framed deformation functor on morphisms: a homomorphism $f : A \to B$ with $\pi_B \circ f = \pi_A$ sends a framed lift $\rho_A$ to the framed lift $f \circ \rho_A$. -/
theorem framedLift_map {ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k} {A B : Type*}
    [CommRing A] [CommRing B] {πA : A →+* k} {πB : B →+* k} (f : A →+* B)
    (hf : πB.comp f = πA)
    {ρ : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) A}
    (hρ : ρ ∈ FramedLift p ρbar A πA) :
    (Matrix.GeneralLinearGroup.map f).comp ρ ∈ FramedLift p ρbar B πB := by
  refine ⟨Subgroup.isOpen_mono (fun σ hσ => ?_) hρ.1, ?_⟩
  · simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply] at hσ ⊢
    rw [hσ, map_one]
  · rw [← hρ.2, ← MonoidHom.comp_assoc, ← Matrix.GeneralLinearGroup.map_comp, hf]

end FramedLift

end Langlands
