/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.GlobalGL
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Reciprocity for $GL_n$ over a global function field

This file states the theorem of L. Lafforgue: the Langlands correspondence for $GL_n$ over a global function field. Let $F$ be a global function field, that is, a finite extension of the field $\mathbb{F}_q(t)$ of rational functions over a finite field. Let $\ell$ be a prime that does not divide $q$. Lafforgue proves that there is a bijection between the cuspidal automorphic representations $\pi$ of $GL_n(\mathbb{A}_F)$ whose central character has finite order and the irreducible continuous representations $\rho : \mathrm{Gal}(F^{sep}/F) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that are unramified outside a finite set of places and whose determinant has finite order. The bijection is characterized by one condition: at each place $v$ where $\pi$ and $\rho$ are unramified, the Satake parameters of $\pi_v$ are the eigenvalues of $\rho(\mathrm{Frob}_v)$. Moreover $\pi$ and $\rho$ are unramified at the same places. Drinfeld proved the case $n = 2$. The case $n = 1$ is class field theory for $F$.

## The places and the adeles

A place of $F$ is a discrete valuation $v : F^\times \to \mathbb{Z}$ that is surjective. Each such valuation is trivial on the finite field $\mathbb{F}_q$, because the nonzero elements of a finite field are roots of unity. There is no archimedean place. The places include the places over the place $1/t$ of $\mathbb{F}_q(t)$, which are often called the places at infinity, but nothing in the definition separates them from the other places. For a place $v$ we write $F_v$ for the completion, $\mathcal{O}_v$ for its valuation ring, $\varpi_v$ for a uniformizer, $k_v$ for the residue field and $q_v = |k_v|$. The adele ring $\mathbb{A}_F$ is the restricted product of the $F_v$ with respect to the $\mathcal{O}_v$, with the restricted product topology. It contains $F$ on the diagonal, because an element of $F$ has only finitely many poles.

## Cusp forms and Hecke eigensystems

A cusp form on $GL_n$ over $F$ is a function $\varphi : GL_n(\mathbb{A}_F) \to \mathbb{C}$ that is left invariant under $GL_n(F)$, right invariant under an open subgroup, has a central character and has vanishing constant terms along the unipotent radicals of the standard maximal parabolic subgroups. At a place $v$ where $\varphi$ is right invariant under $GL_n(\mathcal{O}_v)$, the Hecke operators $T_{v,i}$ act, as in `Langlands.Statements.Automorphic`. A common eigenvector with eigenvalues $\lambda_i$ has the Satake parameters $\alpha_1, \ldots, \alpha_n$, the roots of $X^n + \sum_{i=1}^n (-1)^i q_v^{-i(n-i)/2} \lambda_i X^{n-i}$.

As in `Langlands.Statements.GlobalGL`, the automorphic side is described by Hecke eigensystems of cusp forms, not by automorphic representations. A nonzero cusp form that is a Hecke eigenvector at almost all places lies in exactly one cuspidal automorphic representation $\pi$, and two such forms lie in the same $\pi$ if and only if they have the same eigenvalues at almost all places. This is strong multiplicity one, a theorem of Piatetski-Shapiro for function fields. So the classes of such forms for this relation are the cuspidal automorphic representations.

## The Galois side

The Galois group is the group $\mathrm{Aut}(\overline{F}/F)$ of the algebraic closure. A place of $\overline{F}$ over $v$ is a valuation subring $W$ of $\overline{F}$ with $W \cap F = \mathcal{O}_v$. An element $\sigma$ is in the decomposition group of $W$ if $\sigma(W) = W$. It is in the inertia group if moreover $\sigma(x) \equiv x$ modulo the maximal ideal of $W$ for each $x \in W$. It is an arithmetic Frobenius at $W$ if $\sigma(W) = W$ and $\sigma(x) \equiv x^{q_v}$ modulo the maximal ideal of $W$ for each $x \in W$.

## Main definitions

* `Langlands.GlobalFunctionField.Place F` is the set of places of $F$, and `Langlands.GlobalFunctionField.AdeleRing F` is the adele ring $\mathbb{A}_F$.
* `Langlands.GlobalFunctionField.principalGL F n` is the subgroup $GL_n(F)$ of $GL_n(\mathbb{A}_F)$.
* `Langlands.GlobalFunctionField.IsCuspForm` is the condition to be a cusp form whose central character has finite order.
* `Langlands.GlobalFunctionField.heckeOperator v i` is the Hecke operator $T_{v,i}$, and `Langlands.GlobalFunctionField.IsHeckeEigenAt` is the condition to be an eigenvector of $T_{v,1}, \ldots, T_{v,n}$.
* `Langlands.GlobalFunctionField.AutomorphicClass F n` is the set of the classes of nonzero cuspidal Hecke eigenforms, for the relation of equal eigenvalues at almost all places.
* `Langlands.GlobalFunctionField.IsFrobeniusAt` and `Langlands.GlobalFunctionField.IsUnramifiedAt` are the arithmetic Frobenius elements and the condition to be unramified at a place.
* `Langlands.GlobalFunctionField.GaloisClass F n ℓ` is the set of the isomorphism classes of the representations of Lafforgue.
* `Langlands.GlobalFunctionField.Corresponds ι φ ρ` is the matching condition.
* `Langlands.ReciprocityFunctionFieldGL n` is the theorem of Lafforgue: there is a bijection between the two sets of classes, and it sends the class of $\varphi$ to the class of $\rho$ exactly when they match.

## Implementation notes

A place is a surjective valuation $v$ on $F$ with values in `ℤᵐ⁰`, the group $\exp(\mathbb{Z})$ with a zero, written multiplicatively. Two surjective valuations with the same valuation ring are equal, so each place has exactly one such valuation. With this choice the set of places is canonical. There is no choice of a Dedekind subring of $F$, of a separating element $t$, or of a model of the curve. The completion is `Valuation.Completion`, the uniform completion of $F$ for the topology of $v$, and $\mathcal{O}_v$ is the valuation subring of the extended valuation.

The adele ring is the restricted product `Πʳ v, [F_v, 𝒪_v]` of Mathlib, with its topology. Each $\mathcal{O}_v$ is open in $F_v$, so this is the usual topology of $\mathbb{A}_F$. Mathlib does not yet have the theorem that an element of $F$ lies in $\mathcal{O}_v$ for almost all places $v$ in this sense, so the diagonal map $F \to \mathbb{A}_F$ is not given as a ring homomorphism. In its place, `principalAdeles F` is the subring of the adeles $a$ with $a_v = x$ for all $v$ and some $x \in F$. The map $F \to \prod_v F_v$ is injective, so this subring is the image of the set of $x \in F$ with $x \in \mathcal{O}_v$ for almost all $v$. By the theorem on poles this set is all of $F$. So `principalAdeles F` is a copy of $F$, and `principalGL F n`, the image of $GL_n$ of this subring, is $GL_n(F)$. The statement uses only these subgroups and does not need the theorem.

The cusp forms have no growth condition and no continuity condition. A function that is right invariant under an open subgroup is locally constant. Over a function field a cusp form in this sense has compact support modulo $Z(\mathbb{A}_F) GL_n(F)$, by a theorem of Harder, so a growth condition would change nothing. Its central character has finite order, so it is bounded and it lies in the space of cusp forms in $L^2$. The space of such forms that are invariant under a given open compact subgroup has finite dimension. The constant term along $N_r$ is an integral over the compact group $N_r(F) \backslash N_r(\mathbb{A}_F)$. As in `Langlands.Statements.Automorphic`, the definition integrates over $(\mathbb{A}_F / F)^{n \times n}$ with each invariant probability measure. The group $\mathbb{A}_F / F$ is compact, so there is exactly one such measure.

An automorphic class is unramified at $v$ if one of its forms is a Hecke eigenvector at $v$. A nonzero vector of $\pi$ that is invariant under $GL_n(\mathcal{O}_v)$ is automatically a Hecke eigenvector at $v$, because the invariants of $\pi_v$ have dimension one. So this is the condition that $\pi_v$ is unramified. The matching condition is asked for each form of the class at each place where the form is a Hecke eigenvector.

The Galois group of Mathlib is $\mathrm{Aut}(\overline{F}/F)$. In characteristic $p$ the extension $\overline{F}/F^{sep}$ is purely inseparable, so the restriction $\mathrm{Aut}(\overline{F}/F) \to \mathrm{Gal}(F^{sep}/F)$ is an isomorphism of topological groups, and the valuation subrings of $\overline{F}$ and of $F^{sep}$ over $\mathcal{O}_v$ correspond. Valuation subrings $W$ over $\mathcal{O}_v$ exist by the extension theorem of Chevalley, and they are all conjugate. The residue field of $W$ is an algebraic closure of $k_v$. So the definitions of the decomposition group, the inertia group and the Frobenius elements are the usual ones. A representation is unramified at $v$ if it is trivial on the inertia group of each $W$ over $v$. Then $\rho(\sigma)$ for an arithmetic Frobenius $\sigma$ at $v$ is well defined up to conjugation.

The coefficients are in `PadicAlgCl ℓ`, the algebraic closure of $\mathbb{Q}_\ell$ with the topology of the spectral norm, as in `Langlands.Statements.Galois`. The comparison with the Satake parameters is through an explicit isomorphism of fields $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$. The matching condition is the equality of the Satake polynomial with the image under $\iota$ of the characteristic polynomial of $\rho(\sigma)$. Both polynomials are monic of degree $n$ and split over $\mathbb{C}$, so this is the equality of the multisets of Satake parameters and of the $\iota$-images of the eigenvalues of Frobenius.

The normalizations are the unitary Satake parameters and the arithmetic Frobenius. The unitary normalization is the right one: the central character has finite order exactly when the determinant does, and in this case Lafforgue proves that both sides have absolute value $1$. Other texts state the matching with the geometric Frobenius $\mathrm{Frob}_v^{-1}$, or with the other Satake convention. The two forms of the statement are equivalent. If $\Phi$ is a bijection for one convention, then $\pi \mapsto \Phi(\pi^\vee)$ is a bijection for the other, because the Satake parameters of the contragredient $\pi^\vee$ are the inverses of those of $\pi$, and $\pi^\vee$ is again cuspidal with a central character of finite order. On the side of eigensystems, $\pi^\vee$ is the class of the complex conjugate forms $\overline{\varphi}$, since $\pi$ is unitary.

The statement is a characterized bijection. The condition says that the graph of the bijection is exactly the matching relation, so the bijection is unique (see `Langlands.GlobalFunctionField.correspondence_unique`). By the Chebotarev density theorem and strong multiplicity one, the matching at almost all places already determines each side from the other. The bijection preserves the set of unramified places, which is part of the theorem of Lafforgue.

These parts of the theorem of Lafforgue are not in the statement: the compatibility with the local Langlands correspondence at the ramified places (through the L-functions and the $\varepsilon$-factors of pairs), and the corollaries, such as the Ramanujan conjecture and the purity of $\rho$.

The field $k$ in the statement is a finite field with $F$ finite over $k(t)$, in the sense of `FunctionField k F` of Mathlib. It need not be the full field of constants of $F$. This does not matter, because the places do not depend on $k$. The condition that $\ell$ does not divide $q$ is `(ℓ : k) ≠ 0`.

## Sanity checks

* `Langlands.GlobalFunctionField.corresponds_congr_left` and `Langlands.GlobalFunctionField.corresponds_congr_right`: the matching condition depends only on the classes.
* `Langlands.GlobalFunctionField.correspondence_unique`: there is at most one bijection with the property in the statement.
* `Langlands.GlobalFunctionField.isCuspEigenform_one` and `Langlands.GlobalFunctionField.isLafforgueRep_one`: for $n = 1$ both sides are not empty. The constant function $1$ is a cusp form and the trivial character is a representation of the Galois side.
* `Langlands.GlobalFunctionField.satakePolynomial_one_eq_charpoly_map_iff`: for $n = 1$ the matching condition at $v$ is $\iota(\rho(\sigma)) = \lambda_1$.

## References

* L. Lafforgue, Chtoucas de Drinfeld et correspondance de Langlands, Invent. Math. 147 (2002), 1-241.
* V. G. Drinfeld, Proof of the Petersson conjecture for GL(2) over a global field of characteristic p, Funct. Anal. Appl. 22 (1988).
* G. Laumon, La correspondance de Langlands sur les corps de fonctions (d'après Laurent Lafforgue), Séminaire Bourbaki 873, 2000.
* G. Harder, Chevalley groups over function fields and automorphic forms, Ann. of Math. 100 (1974).
* I. I. Piatetski-Shapiro, Multiplicity one theorems, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 1, 1979.
* H. Stichtenoth, Algebraic function fields and codes, Grad. Texts in Math. 254, 2009, chapter 1.
-/

namespace Langlands

universe u

namespace GlobalFunctionField

open scoped RestrictedProduct WithZero Multiplicative Classical

noncomputable section

/-! ### Places, completions and adeles -/

variable (F : Type u) [Field F]

/-- A place of the field $F$: a surjective valuation on $F$ with values in `ℤᵐ⁰`. Written additively, it is a surjective discrete valuation $F^\times \to \mathbb{Z}$. For a global function field these are all the places, the places over $1/t$ included. -/
def Place : Type u :=
  {v : Valuation F ℤᵐ⁰ // Function.Surjective v}

variable {F}

namespace Place

/-- The completion $F_v$ of $F$ at the place $v$. -/
abbrev Completion (v : Place F) : Type u :=
  v.1.Completion

/-- The valuation ring $\mathcal{O}_v = \{x \in F_v : |x|_v \le 1\}$ of the completion. -/
def integers (v : Place F) : ValuationSubring v.Completion :=
  Valued.v.valuationSubring

/-- The embedding $F \to F_v$. -/
def embed (v : Place F) : F →+* v.Completion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv v.1).symm.toRingHom

theorem valued_embed (v : Place F) (x : F) : Valued.v (v.embed x) = v.1 x :=
  Valued.valuedCompletion_apply _

/-- The residue field $k_v = \mathcal{O}_v / \mathfrak{m}_v$ at the place $v$. -/
abbrev ResidueField (v : Place F) : Type u :=
  IsLocalRing.ResidueField v.integers

/-- The size $q_v = |k_v|$ of the residue field. -/
def norm (v : Place F) : ℕ :=
  Nat.card v.ResidueField

/-- An element of $F$ of valuation $1$ at $v$, chosen with the surjectivity of $v$. -/
def uniformizerOfField (v : Place F) : F :=
  Classical.choose (v.2 (WithZero.exp (-1)))

theorem valuation_uniformizerOfField (v : Place F) :
    v.1 v.uniformizerOfField = WithZero.exp (-1) :=
  Classical.choose_spec (v.2 (WithZero.exp (-1)))

/-- The uniformizer $\varpi_v \in F_v$: the image of `uniformizerOfField v`. -/
def uniformizer (v : Place F) : v.Completion :=
  v.embed v.uniformizerOfField

theorem valued_uniformizer (v : Place F) : Valued.v v.uniformizer = WithZero.exp (-1) := by
  rw [uniformizer, valued_embed, valuation_uniformizerOfField]

theorem uniformizer_ne_zero (v : Place F) : v.uniformizer ≠ 0 := by
  intro h
  have := v.valued_uniformizer
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

end Place

variable (F) in
/-- The adele ring $\mathbb{A}_F$ of $F$: the restricted product of the completions $F_v$ over all places $v$, with respect to the valuation rings $\mathcal{O}_v$. -/
abbrev AdeleRing : Type u :=
  Πʳ v : Place F, [v.Completion, v.integers]

variable (F) in
/-- The principal adeles: the adeles $a$ such that $a_v$ is the image of the same $x \in F$ at each place $v$. Since $x$ has only finitely many poles, this is the image of the diagonal embedding $F \to \mathbb{A}_F$. -/
def principalAdeles : Subring (AdeleRing F) where
  carrier := {a | ∃ x : F, ∀ v, a v = v.embed x}
  mul_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, fun v ↦ by rw [RestrictedProduct.mul_apply, hx, hy, map_mul]⟩
  one_mem' := ⟨1, fun v ↦ by rw [RestrictedProduct.one_apply, map_one]⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, fun v ↦ by rw [RestrictedProduct.add_apply, hx, hy, map_add]⟩
  zero_mem' := ⟨0, fun v ↦ by rw [RestrictedProduct.zero_apply, map_zero]⟩
  neg_mem' := by
    rintro a ⟨x, hx⟩
    exact ⟨-x, fun v ↦ by rw [RestrictedProduct.neg_apply, hx, map_neg]⟩

variable (F) in
/-- The compact group $\mathbb{A}_F / F$. -/
abbrev AdeleQuotient : Type u :=
  AdeleRing F ⧸ (principalAdeles F).toAddSubgroup

variable (F) (n : ℕ) in
/-- The group $GL_n(\mathbb{A}_F)$ of invertible $n \times n$ matrices over the adele ring of $F$. It has the topology of the units of the topological ring of matrices. -/
abbrev AdelicGL : Type u :=
  GL (Fin n) (AdeleRing F)

variable {n : ℕ}

variable (F n) in
/-- The subgroup $GL_n(F)$ of $GL_n(\mathbb{A}_F)$: the image of $GL_n$ of the ring of principal adeles. -/
def principalGL : Subgroup (AdelicGL F n) :=
  (Matrix.GeneralLinearGroup.map (principalAdeles F).subtype).range

/-- The scalar matrix $z \cdot 1 \in GL_n(\mathbb{A}_F)$ for an idele $z$. -/
def adelicScalarGL (z : (AdeleRing F)ˣ) : AdelicGL F n :=
  Units.map (Matrix.scalar (Fin n) : AdeleRing F →+* _).toMonoidHom z

/-- The adele with the component $x$ at the place $v$ and $0$ at the other places. -/
def adeleSingle (v : Place F) : v.Completion →+ AdeleRing F where
  toFun x := RestrictedProduct.single (fun w : Place F ↦ w.integers) v x
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' x y := RestrictedProduct.single_add _ v x y

theorem adeleSingle_mul (v : Place F) (x y : v.Completion) :
    adeleSingle v (x * y) = adeleSingle v x * adeleSingle v y := by
  have h := RestrictedProduct.single_mul (fun w : Place F ↦ w.integers) v x
    (RestrictedProduct.single _ v y)
  rw [RestrictedProduct.single_eq_same] at h
  exact h

theorem adeleSingle_mapMatrix_mul (v : Place F) (A B : Matrix (Fin n) (Fin n) v.Completion) :
    (adeleSingle v).mapMatrix (A * B) =
      (adeleSingle v).mapMatrix A * (adeleSingle v).mapMatrix B := by
  ext i j
  simp [Matrix.mul_apply, map_sum, adeleSingle_mul]

/-- The adelic matrix with the component $M$ at the place $v$ and the identity at the other places. -/
def localMatrix (v : Place F) :
    Matrix (Fin n) (Fin n) v.Completion →* Matrix (Fin n) (Fin n) (AdeleRing F) where
  toFun M := 1 + (adeleSingle v).mapMatrix (M - 1)
  map_one' := by simp
  map_mul' M N := by
    have h : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
    rw [h, map_add, map_add, adeleSingle_mapMatrix_mul]
    noncomm_ring

/-- The embedding $GL_n(F_v) \to GL_n(\mathbb{A}_F)$ at the place $v$, with the identity at the other places. -/
def localGL (v : Place F) : GL (Fin n) v.Completion →* AdelicGL F n :=
  Units.map (localMatrix v)

/-- The matrix $\begin{pmatrix} 0 & X \\ 0 & 0 \end{pmatrix}$, where $X$ is the block of the rows $i < r$ and the columns $j \ge r$ of the given array. -/
def blockMask (r : ℕ) (X : Fin n → Fin n → AdeleRing F) : Matrix (Fin n) (Fin n) (AdeleRing F) :=
  Matrix.of fun i j ↦ if (i : ℕ) < r ∧ r ≤ (j : ℕ) then X i j else 0

theorem blockMask_mul_blockMask (r : ℕ) (X Y : Fin n → Fin n → AdeleRing F) :
    blockMask r X * blockMask r Y = 0 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [blockMask, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  split_ifs with h₁ h₂ <;> first | simp | omega

/-- The unipotent element $\begin{pmatrix} 1 & X \\ 0 & 1 \end{pmatrix}$ of the unipotent radical $N_r(\mathbb{A}_F)$ of the standard parabolic subgroup of type $(r, n - r)$. -/
def unipotentGL (r : ℕ) (X : Fin n → Fin n → AdeleRing F) : AdelicGL F n where
  val := 1 + blockMask r X
  inv := 1 - blockMask r X
  val_inv := by rw [add_mul, mul_sub, mul_sub, blockMask_mul_blockMask]; noncomm_ring
  inv_val := by rw [sub_mul, mul_add, mul_add, blockMask_mul_blockMask]; noncomm_ring

/-- The constant term of $\varphi$ along $N_r$ vanishes: for each $g \in GL_n(\mathbb{A}_F)$,
$$\int_{N_r(F) \backslash N_r(\mathbb{A}_F)} \varphi(u g) \, du = 0.$$
The integral is over $(\mathbb{A}_F / F)^{n \times n}$ with an invariant probability measure, and the integrand uses a lift of each entry to $\mathbb{A}_F$. Only the entries in the block of $N_r$ enter. -/
def HasVanishingConstantTerm (r : ℕ) (φ : AdelicGL F n → ℂ) : Prop :=
  letI : MeasurableSpace (AdeleQuotient F) := borel _
  ∀ μ : MeasureTheory.Measure (Fin n → Fin n → AdeleQuotient F),
    MeasureTheory.IsProbabilityMeasure μ → μ.IsAddLeftInvariant →
      ∀ g : AdelicGL F n,
        ∫ x, φ (unipotentGL r (fun i j ↦ (Quotient.out (x i j) : AdeleRing F)) * g) ∂μ = 0

/-- A cusp form on $GL_n$ over $F$ whose central character has finite order. It is a function $\varphi : GL_n(\mathbb{A}_F) \to \mathbb{C}$ with these properties.

* It is left invariant under $GL_n(F)$.
* It is right invariant under an open subgroup of $GL_n(\mathbb{A}_F)$. Each open subgroup contains an open compact subgroup, so this is the usual condition.
* It has a central character $\omega$ of finite order: $\varphi(g z) = \omega(z) \varphi(g)$ for the scalar matrices $z \in \mathbb{A}_F^\times$, and $\omega^m = 1$ for some $m \ge 1$.
* Its constant terms along the unipotent radicals of the standard maximal parabolic subgroups are zero. -/
structure IsCuspForm (φ : AdelicGL F n → ℂ) : Prop where
  left_invariant : ∀ γ ∈ principalGL F n, ∀ g, φ (γ * g) = φ g
  smooth : ∃ U : Subgroup (AdelicGL F n), IsOpen (U : Set (AdelicGL F n)) ∧
    ∀ k ∈ U, ∀ g, φ (g * k) = φ g
  central : ∃ ω : (AdeleRing F)ˣ → ℂ, (∃ m : ℕ, 0 < m ∧ ∀ z, ω z ^ m = 1) ∧
    ∀ z g, φ (g * adelicScalarGL z) = ω z * φ g
  cuspidal : ∀ r : ℕ, 0 < r → r < n → HasVanishingConstantTerm r φ

/-- An element of $GL_n(F_v)$ is in $GL_n(\mathcal{O}_v)$ if the entries of it and of its inverse are integral. -/
def IsIntegralGL (v : Place F) (k : GL (Fin n) v.Completion) : Prop :=
  ∀ i j, Valued.v ((k : Matrix (Fin n) (Fin n) v.Completion) i j) ≤ 1 ∧
    Valued.v ((k⁻¹ : GL (Fin n) v.Completion) i j) ≤ 1

/-- A function on $GL_n(\mathbb{A}_F)$ is spherical at $v$ if it is right invariant under $GL_n(\mathcal{O}_v)$. -/
def IsSphericalAt (φ : AdelicGL F n → ℂ) (v : Place F) : Prop :=
  ∀ k, IsIntegralGL v k → ∀ g, φ (g * localGL v k) = φ g

variable (n) in
/-- The index set of the right cosets in $GL_n(\mathcal{O}_v) \, \mathrm{diag}(\varpi_v^{(i)}, 1^{(n-i)}) \, GL_n(\mathcal{O}_v)$: a set $s$ of $i$ indices, and a residue class in $k_v$ for each position $(j, k)$ with $j < k$, $j \in s$ and $k \notin s$. -/
def HeckeCoset (v : Place F) (i : ℕ) : Type u :=
  Σ s : {s : Finset (Fin n) // s.card = i},
    {p : Fin n × Fin n // p.1 < p.2 ∧ p.1 ∈ s.1 ∧ p.2 ∉ s.1} → v.ResidueField

/-- A lift to $\mathcal{O}_v$ of an element of the residue field $k_v$, chosen with `Function.surjInv`. -/
def Place.residueLift (v : Place F) (c : v.ResidueField) : v.Completion :=
  (Function.surjInv IsLocalRing.residue_surjective c : v.integers)

/-- The coset representative: the upper triangular matrix with diagonal entries $\varpi_v$ at the indices in $s$ and $1$ at the others, and with a lift of the given residue class at each allowed position. -/
def heckeCosetMatrix (v : Place F) {i : ℕ} (c : HeckeCoset n v i) :
    Matrix (Fin n) (Fin n) v.Completion :=
  Matrix.of fun j k ↦
    if j = k then (if j ∈ c.1.1 then v.uniformizer else 1)
    else if h : j < k ∧ j ∈ c.1.1 ∧ k ∉ c.1.1 then v.residueLift (c.2 ⟨(j, k), h⟩)
    else 0

theorem heckeCosetMatrix_isUpperTriangular (v : Place F) {i : ℕ} (c : HeckeCoset n v i) :
    (heckeCosetMatrix v c).IsUpperTriangular := by
  intro j k hkj
  have h₁ : j ≠ k := (ne_of_lt hkj).symm
  have h₂ : ¬ (j < k ∧ j ∈ c.1.1 ∧ k ∉ c.1.1) := fun h ↦ (lt_asymm h.1 hkj).elim
  simp [heckeCosetMatrix, h₁, h₂]

theorem heckeCosetMatrix_det_ne_zero (v : Place F) {i : ℕ} (c : HeckeCoset n v i) :
    (heckeCosetMatrix v c).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (heckeCosetMatrix_isUpperTriangular v c)]
  refine Finset.prod_ne_zero_iff.2 fun j _ ↦ ?_
  simp only [heckeCosetMatrix, Matrix.of_apply, ite_true]
  split_ifs
  · exact v.uniformizer_ne_zero
  · exact one_ne_zero

/-- The coset representative as an element of $GL_n(F_v)$. -/
def heckeCosetGL (v : Place F) {i : ℕ} (c : HeckeCoset n v i) : GL (Fin n) v.Completion :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (heckeCosetMatrix_det_ne_zero v c)

/-- The Hecke operator $T_{v,i}$: $(T_{v,i} \varphi)(g) = \sum_c \varphi(g h_c)$, where $h_c$ runs over the representatives of $GL_n(\mathcal{O}_v) \, \mathrm{diag}(\varpi_v^{(i)}, 1^{(n-i)}) \, GL_n(\mathcal{O}_v) / GL_n(\mathcal{O}_v)$ in `heckeCosetGL`. There are finitely many, because $k_v$ is finite. -/
def heckeOperator (v : Place F) (i : ℕ) (φ : AdelicGL F n → ℂ) : AdelicGL F n → ℂ :=
  fun g ↦ ∑ᶠ c : HeckeCoset n v i, φ (g * localGL v (heckeCosetGL v c))

/-- The function $\varphi$ is spherical at $v$ and an eigenvector of $T_{v,i}$ with eigenvalue $\lambda_i$, for $1 \le i \le n$. -/
def IsHeckeEigenAt (φ : AdelicGL F n → ℂ) (v : Place F) (ev : ℕ → ℂ) : Prop :=
  IsSphericalAt φ v ∧ ∀ i, 1 ≤ i → i ≤ n → heckeOperator v i φ = ev i • φ

/-- The function $\varphi$ is a Hecke eigenform: it is a Hecke eigenvector at all places outside a finite set. -/
def IsHeckeEigenform (φ : AdelicGL F n → ℂ) : Prop :=
  ∃ S : Set (Place F), S.Finite ∧ ∀ v ∉ S, ∃ ev : ℕ → ℂ, IsHeckeEigenAt φ v ev

variable (F n) in
/-- The nonzero cusp forms on $GL_n$ over $F$ with a central character of finite order that are Hecke eigenforms. Each one lies in a unique cuspidal automorphic representation. -/
def CuspEigenform : Type u :=
  {φ : AdelicGL F n → ℂ // IsCuspForm φ ∧ φ ≠ 0 ∧ IsHeckeEigenform φ}

/-- Two cuspidal eigenforms are equivalent if they have the same Hecke eigenvalues at almost all places. By strong multiplicity one, this holds if and only if they lie in the same cuspidal automorphic representation. -/
def CuspEigenform.Equiv (φ ψ : CuspEigenform F n) : Prop :=
  ∃ S : Set (Place F), S.Finite ∧
    ∀ v ∉ S, ∃ ev : ℕ → ℂ, IsHeckeEigenAt φ.1 v ev ∧ IsHeckeEigenAt ψ.1 v ev

theorem IsHeckeEigenAt.eq_of_ne_zero {φ : AdelicGL F n → ℂ} (hφ : φ ≠ 0) {v : Place F}
    {ev ev' : ℕ → ℂ} (h : IsHeckeEigenAt φ v ev) (h' : IsHeckeEigenAt φ v ev') {i : ℕ}
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) : ev i = ev' i := by
  have e := (h.2 i hi₁ hi₂).symm.trans (h'.2 i hi₁ hi₂)
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ (funext hc)
  have := congrFun e g
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hg this

theorem IsHeckeEigenAt.congr {φ : AdelicGL F n → ℂ} {v : Place F} {ev ev' : ℕ → ℂ}
    (h : IsHeckeEigenAt φ v ev) (he : ∀ i, 1 ≤ i → i ≤ n → ev i = ev' i) :
    IsHeckeEigenAt φ v ev' :=
  ⟨h.1, fun i hi₁ hi₂ ↦ by rw [h.2 i hi₁ hi₂, he i hi₁ hi₂]⟩

variable (F n) in
/-- The relation of equal eigenvalues at almost all places is an equivalence relation. For the transitivity, the eigenvalues of a nonzero eigenvector are unique. -/
def cuspSetoid : Setoid (CuspEigenform F n) where
  r := CuspEigenform.Equiv
  iseqv := by
    refine ⟨fun φ ↦ ?_, fun ⟨S, hS, h⟩ ↦ ⟨S, hS, fun v hv ↦ ?_⟩, ?_⟩
    · obtain ⟨S, hS, h⟩ := φ.2.2.2
      exact ⟨S, hS, fun v hv ↦ (h v hv).imp fun ev h ↦ ⟨h, h⟩⟩
    · obtain ⟨ev, h₁, h₂⟩ := h v hv
      exact ⟨ev, h₂, h₁⟩
    · rintro φ ψ χ ⟨S, hS, h⟩ ⟨T, hT, h'⟩
      refine ⟨S ∪ T, hS.union hT, fun v hv ↦ ?_⟩
      obtain ⟨ev, h₁, h₂⟩ := h v fun hS' ↦ hv (Or.inl hS')
      obtain ⟨ev', h₃, h₄⟩ := h' v fun hT' ↦ hv (Or.inr hT')
      exact ⟨ev, h₁, h₄.congr fun i hi₁ hi₂ ↦ (h₂.eq_of_ne_zero ψ.2.2.1 h₃ hi₁ hi₂).symm⟩

variable (F n) in
/-- The automorphic side: the classes of nonzero cuspidal Hecke eigenforms with a central character of finite order, for the relation of equal eigenvalues at almost all places. These are the cuspidal automorphic representations of $GL_n(\mathbb{A}_F)$ whose central character has finite order. -/
def AutomorphicClass : Type u :=
  Quotient (cuspSetoid F n)

/-- The class of $\varphi$ is unramified at $v$: one of the forms of the class is a Hecke eigenvector at $v$. This is the condition that the local component $\pi_v$ has a nonzero vector invariant under $GL_n(\mathcal{O}_v)$. -/
def CuspEigenform.IsUnramifiedAt (φ : CuspEigenform F n) (v : Place F) : Prop :=
  ∃ ψ : CuspEigenform F n, ψ.Equiv φ ∧ ∃ ev, IsHeckeEigenAt ψ.1 v ev

/-! ### The Galois side -/

variable (F) in
/-- The absolute Galois group of $F$, as the group $\mathrm{Aut}(\overline{F}/F)$ with the Krull topology. It is isomorphic to $\mathrm{Gal}(F^{sep}/F)$ by restriction. -/
abbrev GaloisGroup : Type u :=
  Field.absoluteGaloisGroup F

/-- The action of the Galois group on $\overline{F}$. -/
def galoisAct (σ : GaloisGroup F) (x : AlgebraicClosure F) : AlgebraicClosure F :=
  (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from σ) x

/-- A valuation subring $W$ of $\overline{F}$ lies over the place $v$ if $W \cap F = \mathcal{O}_{F,v}$, the valuation ring of $v$ in $F$. These are the places of $\overline{F}$ over $v$. -/
def ValuationSubring.LiesOver (W : ValuationSubring (AlgebraicClosure F)) (v : Place F) : Prop :=
  W.comap (algebraMap F (AlgebraicClosure F)) = v.1.valuationSubring

/-- The element $\sigma$ is in the decomposition group of $W$: $\sigma(W) = W$. -/
def IsInDecomposition (W : ValuationSubring (AlgebraicClosure F)) (σ : GaloisGroup F) : Prop :=
  ∀ x, galoisAct σ x ∈ W ↔ x ∈ W

/-- The element $\sigma$ is in the inertia group of $W$: $\sigma(W) = W$ and $\sigma(x) \equiv x$ modulo the maximal ideal of $W$ for each $x \in W$. -/
def IsInInertia (W : ValuationSubring (AlgebraicClosure F)) (σ : GaloisGroup F) : Prop :=
  IsInDecomposition W σ ∧ ∀ x ∈ W, W.valuation (galoisAct σ x - x) < 1

/-- The element $\sigma$ is an arithmetic Frobenius at the place $v$: there is a place $W$ of $\overline{F}$ over $v$ with $\sigma(W) = W$ and $\sigma(x) \equiv x^{q_v}$ modulo the maximal ideal of $W$ for each $x \in W$. -/
def IsFrobeniusAt (v : Place F) (σ : GaloisGroup F) : Prop :=
  ∃ W : ValuationSubring (AlgebraicClosure F), ValuationSubring.LiesOver W v ∧
    IsInDecomposition W σ ∧ ∀ x ∈ W, W.valuation (galoisAct σ x - x ^ v.norm) < 1

/-- A homomorphism from the Galois group is unramified at $v$ if it is trivial on the inertia group of each place $W$ of $\overline{F}$ over $v$. -/
def IsUnramifiedAt {H : Type*} [Group H] (ρ : GaloisGroup F →* H) (v : Place F) : Prop :=
  ∀ W : ValuationSubring (AlgebraicClosure F), ValuationSubring.LiesOver W v →
    ∀ σ, IsInInertia W σ → ρ σ = 1

/-- The representations of the theorem of Lafforgue: a representation $\rho : \mathrm{Gal}(\overline{F}/F) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that is continuous, irreducible, unramified outside a finite set of places, and whose determinant has finite order. -/
structure IsLafforgueRep (ℓ : ℕ) [Fact ℓ.Prime] (ρ : GaloisGroup F →* GL (Fin n) (PadicAlgCl ℓ)) :
    Prop where
  continuous : Continuous ρ
  irreducible : IsIrreducibleRep ρ
  almost_unramified : {v : Place F | ¬ IsUnramifiedAt ρ v}.Finite
  det_finite_order : ∃ m : ℕ, 0 < m ∧
    ∀ σ, (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).det ^ m = 1

variable (F n) in
/-- The representations of the Galois side, before the passage to isomorphism classes. -/
def GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] : Type u :=
  {ρ : GaloisGroup F →* GL (Fin n) (PadicAlgCl ℓ) // IsLafforgueRep ℓ ρ}

/-- Two representations are isomorphic if they are conjugate by a matrix $A \in GL_n(\overline{\mathbb{Q}}_\ell)$. -/
def GaloisRep.Iso {ℓ : ℕ} [Fact ℓ.Prime] (ρ ρ' : GaloisRep F n ℓ) : Prop :=
  ∃ A : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, ρ'.1 σ = A * ρ.1 σ * A⁻¹

variable (F n) in
/-- Isomorphism of representations is an equivalence relation. -/
def galoisSetoid (ℓ : ℕ) [Fact ℓ.Prime] : Setoid (GaloisRep F n ℓ) where
  r := GaloisRep.Iso
  iseqv := by
    refine ⟨fun ρ ↦ ⟨1, fun σ ↦ by simp⟩, fun ⟨A, h⟩ ↦ ⟨A⁻¹, fun σ ↦ ?_⟩, ?_⟩
    · rw [h σ]
      group
    · rintro ρ ρ' ρ'' ⟨A, h⟩ ⟨B, h'⟩
      exact ⟨B * A, fun σ ↦ by rw [h' σ, h σ]; group⟩

variable (F n) in
/-- The Galois side: the isomorphism classes of the representations of Lafforgue. -/
def GaloisClass (ℓ : ℕ) [Fact ℓ.Prime] : Type u :=
  Quotient (galoisSetoid F n ℓ)

/-! ### The statement -/

/-- The matching condition between a cuspidal eigenform $\varphi$, standing for the automorphic representation $\pi$ that it generates, and a representation $\rho$.

* The class of $\varphi$ and $\rho$ are unramified at the same places.
* Let $\psi$ be a form of the class of $\varphi$ and let $v$ be a place where $\psi$ is a Hecke eigenvector with eigenvalues $\lambda_i$. Then $\rho$ is unramified at $v$ by the first condition, and for each arithmetic Frobenius $\sigma$ at $v$ the Satake polynomial $X^n + \sum_{i=1}^n (-1)^i q_v^{-i(n-i)/2} \lambda_i X^{n-i}$ is the image under $\iota$ of the characteristic polynomial of $\rho(\sigma)$. In other words, the Satake parameters of $\pi_v$ are the images under $\iota$ of the eigenvalues of $\rho(\sigma)$. -/
def Corresponds {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) (φ : CuspEigenform F n)
    (ρ : GaloisRep F n ℓ) : Prop :=
  (∀ v : Place F, φ.IsUnramifiedAt v ↔ IsUnramifiedAt ρ.1 v) ∧
  ∀ ψ : CuspEigenform F n, ψ.Equiv φ → ∀ (v : Place F) (ev : ℕ → ℂ), IsHeckeEigenAt ψ.1 v ev →
    ∀ σ, IsFrobeniusAt v σ →
      satakePolynomial n v.norm ev =
        (ρ.1 σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly.map (ι : PadicAlgCl ℓ →+* ℂ)

/-! ### Sanity checks -/

/-- The relation `Corresponds` depends on $\rho$ only up to isomorphism. -/
theorem corresponds_congr_right {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (φ : CuspEigenform F n) {ρ ρ' : GaloisRep F n ℓ} (h : ρ.Iso ρ') :
    Corresponds ι φ ρ ↔ Corresponds ι φ ρ' := by
  obtain ⟨A, hA⟩ := h
  have hu (v : Place F) : IsUnramifiedAt ρ'.1 v ↔ IsUnramifiedAt ρ.1 v := by
    simp only [IsUnramifiedAt, hA, conj_eq_one_iff]
  have hc (σ : GaloisGroup F) :
      (ρ'.1 σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly =
        (ρ.1 σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly := by
    rw [hA σ, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  simp only [Corresponds, hu, hc]

/-- The relation `Corresponds` depends on $\varphi$ only through its class. -/
theorem corresponds_congr_left {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    {φ φ' : CuspEigenform F n} (h : φ.Equiv φ') (ρ : GaloisRep F n ℓ) :
    Corresponds ι φ ρ ↔ Corresponds ι φ' ρ := by
  have e (ψ : CuspEigenform F n) : ψ.Equiv φ ↔ ψ.Equiv φ' :=
    ⟨fun h' ↦ (cuspSetoid F n).iseqv.trans h' h,
      fun h' ↦ (cuspSetoid F n).iseqv.trans h' ((cuspSetoid F n).iseqv.symm h)⟩
  simp only [Corresponds, CuspEigenform.IsUnramifiedAt, e]

/-- The matching condition determines the bijection: two bijections with the property of `ReciprocityFunctionFieldGL` are equal. -/
theorem correspondence_unique {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (Φ Φ' : AutomorphicClass F n ≃ GaloisClass F n ℓ)
    (h : ∀ φ ρ, Φ (Quotient.mk _ φ) = Quotient.mk _ ρ ↔ Corresponds ι φ ρ)
    (h' : ∀ φ ρ, Φ' (Quotient.mk _ φ) = Quotient.mk _ ρ ↔ Corresponds ι φ ρ) : Φ = Φ' := by
  refine Equiv.ext fun a ↦ ?_
  induction a using Quotient.inductionOn with
  | h φ =>
    obtain ⟨ρ, hρ⟩ := Quotient.exists_rep (Φ (Quotient.mk _ φ))
    rw [← hρ]
    exact ((h' φ ρ).2 ((h φ ρ).1 hρ.symm)).symm

/-- Each representation of dimension $1$ is irreducible. -/
theorem isIrreducibleRep_of_dim_one {K : Type*} [Field K] {G : Type*} [Group G]
    (ρ : G →* GL (Fin 1) K) : IsIrreducibleRep ρ := by
  refine ⟨one_pos, fun W _ ↦ ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  refine Or.inr (Submodule.eq_top_iff'.2 fun x ↦ ?_)
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW
  have h0 : w 0 ≠ 0 := fun h ↦ hw0 (funext fun i ↦ by rw [Subsingleton.elim i 0, h]; rfl)
  have hx : x = (x 0 / w 0) • w := funext fun i ↦ by
    rw [Subsingleton.elim i 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
  rw [hx]
  exact W.smul_mem _ hw

/-- For $n = 1$ the trivial character is an object of the Galois side. So this side is not empty. -/
theorem isLafforgueRep_one (ℓ : ℕ) [Fact ℓ.Prime] :
    IsLafforgueRep (F := F) ℓ (1 : GaloisGroup F →* GL (Fin 1) (PadicAlgCl ℓ)) where
  continuous := continuous_const
  irreducible := isIrreducibleRep_of_dim_one _
  almost_unramified := Set.finite_empty.subset fun _ hv ↦ hv fun _ _ _ _ ↦ rfl
  det_finite_order := ⟨1, one_pos, fun _ ↦ by simp⟩

instance (v : Place F) : Subsingleton (HeckeCoset 1 v 1) := by
  refine ⟨?_⟩
  rintro ⟨⟨s, hs⟩, x⟩ ⟨⟨s', hs'⟩, x'⟩
  obtain rfl : s = s' := by
    rw [Finset.eq_univ_of_card s (by simpa using hs), Finset.eq_univ_of_card s' (by simpa using hs')]
  congr
  funext p
  have h := p.2.1
  have := p.1.1.isLt
  have := p.1.2.isLt
  rw [Fin.lt_def] at h
  omega

/-- For $n = 1$ the space of cosets of $T_{v,1}$ has one element. -/
def heckeCosetOneOne (v : Place F) : HeckeCoset 1 v 1 :=
  ⟨⟨Finset.univ, by simp⟩, fun p ↦ by
    have h := p.2.1
    have := p.1.1.isLt
    have := p.1.2.isLt
    rw [Fin.lt_def] at h
    omega⟩

/-- For $n = 1$ the constant function $1$ is a nonzero cusp form with trivial central character, and it is a Hecke eigenform at every place with eigenvalue $1$. So the automorphic side is not empty. -/
theorem isCuspEigenform_one :
    IsCuspForm (F := F) (n := 1) (fun _ ↦ 1) ∧ (fun _ ↦ 1 : AdelicGL F 1 → ℂ) ≠ 0 ∧
      IsHeckeEigenform (F := F) (n := 1) (fun _ ↦ 1) := by
  refine ⟨⟨fun _ _ _ ↦ rfl, ⟨⊤, by simp, fun _ _ _ ↦ rfl⟩,
    ⟨fun _ ↦ 1, ⟨1, one_pos, fun _ ↦ by simp⟩, fun _ _ ↦ by simp⟩, fun r h₁ h₂ ↦ by omega⟩,
    fun h ↦ one_ne_zero (congrFun h 1), ∅, Set.finite_empty, fun v _ ↦ ⟨fun _ ↦ 1,
      fun _ _ _ ↦ rfl, fun i h₁ h₂ ↦ ?_⟩⟩
  obtain rfl : i = 1 := le_antisymm h₂ h₁
  let _ : Unique (HeckeCoset 1 v 1) := uniqueOfSubsingleton (heckeCosetOneOne v)
  funext g
  simp [heckeOperator, finsum_unique]

/-- For $n = 1$ the matching condition at $v$ says $\iota(\rho(\sigma)) = \lambda_1$, the eigenvalue of $T_{v,1}$. -/
theorem satakePolynomial_one_eq_charpoly_map_iff {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (q : ℕ) (ev : ℕ → ℂ) (A : Matrix (Fin 1) (Fin 1) (PadicAlgCl ℓ)) :
    satakePolynomial 1 q ev = A.charpoly.map (ι : PadicAlgCl ℓ →+* ℂ) ↔ ι (A 0 0) = ev 1 := by
  rw [satakePolynomial_one, Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, sub_right_inj, Polynomial.C_inj]
  exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

end

end GlobalFunctionField

open GlobalFunctionField in
/-- **The Langlands correspondence for $GL_n$ over a global function field** (L. Lafforgue; Drinfeld for $n = 2$). Let $n \ge 1$, let $F$ be a global function field, finite over $k(t)$ for a finite field $k$ of characteristic $p$, let $\ell \ne p$ be a prime and let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ be an isomorphism of fields. Then there is a bijection $\Phi$ from the set of cuspidal automorphic representations $\pi$ of $GL_n(\mathbb{A}_F)$ whose central character has finite order to the set of isomorphism classes of the irreducible continuous representations $\rho : \mathrm{Gal}(\overline{F}/F) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that are unramified almost everywhere and whose determinant has finite order. The bijection sends $\pi$ to $\rho$ exactly when they match: they are unramified at the same places, and at each such place $v$ the Satake parameters of $\pi_v$ are the images under $\iota$ of the eigenvalues of the arithmetic Frobenius $\rho(\mathrm{Frob}_v)$.

The automorphic side is the set of classes of cuspidal Hecke eigenforms for the relation of equal eigenvalues at almost all places. By strong multiplicity one this is the set of cuspidal automorphic representations. The statement is with the arithmetic Frobenius. The form with the geometric Frobenius is equivalent, through the contragredient (see the module docstring). The statement does not include the compatibility with the local correspondence at the ramified places. For $n = 1$ it follows from class field theory for $F$. -/
def ReciprocityFunctionFieldGL (n : ℕ) : Prop :=
  0 < n →
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra (RatFunc k) F] [FunctionField k F]
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → ∀ ι : PadicAlgCl ℓ ≃+* ℂ,
    ∃ Φ : AutomorphicClass F n ≃ GaloisClass F n ℓ,
      ∀ (φ : CuspEigenform F n) (ρ : GaloisRep F n ℓ),
        Φ (Quotient.mk _ φ) = Quotient.mk _ ρ ↔ Corresponds ι φ ρ

end Langlands
