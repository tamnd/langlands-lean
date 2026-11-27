/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.NumberFieldGL
import Mathlib.Algebra.Quaternion

/-!
# Reciprocity for $GL_n$ over a number field

This file states three global results and conjectures that relate automorphic representations and Galois representations over a number field $K$. The vocabulary is in `Langlands.Statements.NumberFieldGL`.

The reciprocity conjecture of Clozel, Fontaine and Mazur predicts a bijection between two sets. The first set consists of the cuspidal automorphic representations $\pi$ of $GL_n(\mathbb{A}_K)$ that are algebraic, a condition on the infinitesimal character of $\pi_\infty$. The second set consists of the isomorphism classes of the irreducible continuous representations $\rho : \mathrm{Gal}(\overline{K}/K) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that are geometric: unramified outside a finite set of places and de Rham at the places over $\ell$. The bijection matches the Satake parameters of $\pi_v$, twisted by $|\det|^{(1-n)/2}$, with the eigenvalues of $\rho(\mathrm{Frob}_v)$ at almost all places $v$. For $n = 1$ this is the theorem of Weil and Serre on algebraic Hecke characters, which follows from class field theory. The direction from $\pi$ to $\rho$ is known for the regular algebraic $\pi$ over a totally real or CM field, by Harris, Lan, Taylor and Thorne and by Scholze. The Galois representation of an automorphic representation is not irreducible in all cases that are known, so the theorem gives a representation without this property.

The theorem of Jacquet and Langlands compares the automorphic representations of the multiplicative group $D^\times$ of a quaternion algebra $D$ with those of $GL_2$. Let $S$ be the set of places where $D$ ramifies. Each automorphic representation $\pi'$ of $D^\times(\mathbb{A})$ of dimension greater than $1$ has a cuspidal automorphic representation $\pi$ of $GL_2(\mathbb{A})$ with $\pi_v \cong \pi'_v$ for all $v \notin S$. The image consists of the $\pi$ that are discrete series at each $v \in S$. For the definite quaternion algebra over $\mathbb{Q}$ that ramifies at one prime $p$, the theorem in weight $2$ and level $1$ on the side of $D$ is older. It is the theorem of Eichler that the Brandt matrices of a maximal order have the eigenvalues of the newforms of weight $2$ on $\Gamma_0(p)$, together with the eigenvalue $q + 1$ of the constant functions.

* `Langlands.ReciprocityGL n K`: the conjecture of Clozel, Fontaine and Mazur, in the form that is described below.
* `Langlands.AutomorphicToGalois n K`: the theorem of Harris, Lan, Taylor and Thorne and of Scholze.
* `Langlands.GlobalJacquetLanglandsGL2`: the theorem of Eichler and of Jacquet and Langlands for the definite quaternion algebra over $\mathbb{Q}$ ramified at one prime, in weight $2$.

## Quaternion algebras

The quaternion algebra $D = (a, b)_\mathbb{Q}$ has the basis $1, i, j, k$ with $i^2 = a$, $j^2 = b$ and $ij = -ji = k$. It is Mathlib's `ℍ[ℚ, a, b]`. For $a, b < 0$ the algebra $D \otimes \mathbb{R}$ is the algebra of Hamilton quaternions, so $D$ ramifies at the infinite place. An order is a subring that is a lattice, and a maximal order is an order that no larger order contains. A right ideal of an order $\mathcal{O}$ is a lattice $I$ with $I \mathcal{O} \subseteq I$, and two right ideals $I$ and $J$ are in the same class if $J = xI$ for some $x \in D^\times$. For a maximal order the set of classes is finite, and it is the double coset space $D^\times \backslash \widehat{D}^\times / \widehat{\mathcal{O}}^\times$. So the functions on it are the automorphic forms on $D^\times$ that are invariant under $\widehat{\mathcal{O}}^\times$ and trivial at the infinite place. For a prime $q$ where $D$ splits, the Hecke operator $T_q$ sends $f$ to the function $[I] \mapsto \sum_J f([J])$, where $J$ runs over the $q + 1$ right ideals $J \subseteq I$ of index $q^2$. Its matrix is the Brandt matrix $B(q)$.

* `Langlands.NumberFieldGL.IsMaximalQuaternionOrder O` says that $\mathcal{O}$ is a maximal order.
* `Langlands.NumberFieldGL.QuaternionIdealClass O` is the set of classes of right ideals.
* `Langlands.NumberFieldGL.brandtHecke O q` is the Hecke operator $T_q$.
* `Langlands.NumberFieldGL.IsSplitAt a b q` says that $(a, b)_{\mathbb{Q}_q}$ has a nonzero element of reduced norm $0$, so that it is isomorphic to $M_2(\mathbb{Q}_q)$.

## Implementation notes

The statement `ReciprocityGL` is weaker than the conjecture. Mathlib has no $p$-adic Hodge theory: there is no period ring $B_{dR}$, so the condition to be de Rham is not available. `Langlands.Statements.PadicGalois` has only the ordinary condition over $\mathbb{Q}$. The set of representations that are irreducible, continuous and unramified almost everywhere is too large, so a bijection onto it is false. For example, for $n = 1$ and $K = \mathbb{Q}$, let $\chi$ be the composite of the cyclotomic character $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathbb{Z}_\ell^\times$, the projection to $1 + \ell \mathbb{Z}_\ell$ (for odd $\ell$) and the map $x \mapsto x^s$ for some $s \in \mathbb{Z}_\ell \setminus \mathbb{Z}$. It is continuous and unramified outside $\ell$. No algebraic Hecke character matches it, because the $\ell$-adic characters of the algebraic Hecke characters of $\mathbb{Q}$ are the products of a character of finite order and an integral power of the cyclotomic character. A smaller set of representations that Mathlib can define, for example the representations with finite image, makes the map not surjective. So the statement asks for these properties.

* There is a map $\Phi$ from the algebraic classes to the classes of irreducible continuous representations that are unramified almost everywhere. It sends the class of $\varphi$ to the class of $\rho$ if and only if $\varphi$ and $\rho$ match at almost all places.
* The map $\Phi$ is injective.
* Each representation with finite image is in the image of $\Phi$.

The first point is the direction from $\pi$ to $\rho$ of the conjecture, together with the irreducibility of $\rho$. The second point follows from strong multiplicity one. The third point is the strong form of the conjecture of Artin for $K$. A representation with finite image is geometric: it is unramified almost everywhere, and it is potentially unramified, so de Rham, at the places over $\ell$. So the statement follows from the conjecture, and it does not contain the condition that the image of $\Phi$ is the set of geometric classes. The statement is not trivially true: it contains the strong conjecture of Artin, and the existence of Galois representations for the Maass forms of eigenvalue $1/4$, which is open. It is not trivially false: for $n = 1$ it is the theorem of Weil and Serre, with the trivial character on the side of finite image.

The statement `AutomorphicToGalois` is for $K$ totally real or CM. It has the matching at almost all places. The textbook form says more. The representation is unramified at each place $v \nmid \ell$ where $\pi_v$ is unramified, it is semisimple, and later work gives the compatibility with the local Langlands correspondence at the other places. The semisimplification of a representation has the same characteristic polynomials and the same unramified places, so the condition to be semisimple does not change the statement.

The statement `GlobalJacquetLanglandsGL2` is a special form of the correspondence. These are the differences from the textbook form.

* The quaternion algebra $D$ is over $\mathbb{Q}$, definite, and ramified exactly at one prime $p$ and at the infinite place. The hypotheses say that $a, b < 0$ and that $D$ splits at each prime $q \ne p$. By the reciprocity law of Hilbert, $D$ then ramifies at $p$.
* On the side of $D$ the forms are invariant under $\widehat{\mathcal{O}}^\times$ for a maximal order $\mathcal{O}$, and trivial at the infinite place. On the side of $GL_2$ these are the newforms of weight $2$ on $\Gamma_0(p)$. There are no old forms of this level, because there is no cusp form of weight $2$ on $SL_2(\mathbb{Z})$. The newforms of level $p$ are discrete series at $p$ (Steinberg or its unramified quadratic twist), so the condition at the ramified places is automatic.
* The matching is the equality of the eigenvalues of $T_q$ for all primes $q \ne p$. At these places it is equivalent to $\pi_q \cong \pi'_q$, by the Satake isomorphism.
* The representations of $D^\times$ of dimension $1$ are the characters $\chi \circ \mathrm{nrd}$. At this level only the trivial one occurs, and it has the eigenvalues $q + 1$. The statement removes this system of eigenvalues. A cusp form of weight $2$ never has these eigenvalues, by the bound $|a_q| \le 2 \sqrt{q}$.

For $p = 2$ and $a = b = -1$, the maximal order is the order of Hurwitz, its class number is $1$, and $T_q$ acts by $q + 1$. On the other side there is no cusp form of weight $2$ on $\Gamma_0(2)$. For $p = 11$ there are two classes and one newform, of the elliptic curve of conductor $11$.

## Sanity checks

* `Langlands.NumberFieldGL.reciprocity_map_unique`: the matching condition determines the map $\Phi$ of `ReciprocityGL`.
* `Langlands.NumberFieldGL.isGaloisRep_one`: for $n = 1$ the trivial character is a representation of the Galois side with finite image.
* `Langlands.NumberFieldGL.QuaternionIdealClass.nonempty`: the set of ideal classes of an order is not empty.
* In `Langlands.Statements.NumberFieldGL`: `matches_conj` and `matches_of_equiv` (the matching condition depends only on the classes), `capelliOperator_one`, `heckePolynomial_one`, `heckePolynomial_two` and `heckePolynomial_one_eq_charpoly_map_iff` (the case $n = 1$).

## References

* L. Clozel, Motifs et formes automorphes: applications du principe de fonctorialité, in Automorphic forms, Shimura varieties, and L-functions, Vol. I, Perspect. Math. 10, Academic Press, 1990, 77-159.
* J.-M. Fontaine and B. Mazur, Geometric Galois representations, in Elliptic curves, modular forms, and Fermat's last theorem, Ser. Number Theory I, International Press, 1995, 41-78.
* J.-P. Serre, Abelian $\ell$-adic representations and elliptic curves, Benjamin, 1968.
* M. Harris, K.-W. Lan, R. Taylor and J. Thorne, On the rigid cohomology of certain Shimura varieties, Res. Math. Sci. 3 (2016), Paper No. 37.
* P. Scholze, On torsion in the cohomology of locally symmetric varieties, Ann. of Math. 182 (2015), 945-1066.
* H. Jacquet and R. P. Langlands, Automorphic forms on GL(2), Lecture Notes in Math. 114, Springer, 1970, chapter 16.
* M. Eichler, The basis problem for modular forms and the traces of the Hecke operators, in Modular functions of one variable I, Lecture Notes in Math. 320, Springer, 1973, 75-152.
* B. H. Gross, Heights and the special values of L-series, in Number theory (Montreal 1985), CMS Conf. Proc. 7, 1987, 115-187.
* J. Voight, Quaternion algebras, Grad. Texts in Math. 288, Springer, 2021, chapter 41.
-/

namespace Langlands

universe u

open NumberField IsDedekindDomain NumberFieldGL
open scoped Quaternion

noncomputable section

/-! ### Quaternion algebras over $\mathbb{Q}$ -/

namespace NumberFieldGL

variable {a b : ℚ}

/-- A lattice in the quaternion algebra $D = (a, b)_\mathbb{Q}$: a finitely generated subgroup that spans $D$ over $\mathbb{Q}$. -/
def IsQuaternionLattice (L : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  L.FG ∧ Submodule.span ℚ (L : Set ℍ[ℚ, a, b]) = ⊤

/-- An order of $D$: a subring that is a lattice. -/
def IsQuaternionOrder (O : Subring ℍ[ℚ, a, b]) : Prop :=
  IsQuaternionLattice (AddSubgroup.toIntSubmodule O.toAddSubgroup)

/-- A maximal order of $D$: an order that is not contained in a larger order. -/
def IsMaximalQuaternionOrder (O : Subring ℍ[ℚ, a, b]) : Prop :=
  IsQuaternionOrder O ∧ ∀ O' : Subring ℍ[ℚ, a, b], IsQuaternionOrder O' → O ≤ O' → O' = O

/-- The right ideals of the order $\mathcal{O}$: the lattices $I$ with $I \mathcal{O} \subseteq I$. -/
def QuaternionRightIdeal (O : Subring ℍ[ℚ, a, b]) : Type :=
  {I : Submodule ℤ ℍ[ℚ, a, b] // IsQuaternionLattice I ∧ ∀ x ∈ I, ∀ y ∈ O, x * y ∈ I}

/-- Two right ideals $I$ and $J$ are in the same class if $J = x I$ for some $x \in D^\times$. -/
def quaternionIdealSetoid (O : Subring ℍ[ℚ, a, b]) : Setoid (QuaternionRightIdeal O) where
  r I J := ∃ x : (ℍ[ℚ, a, b])ˣ, ∀ z, z ∈ J.1 ↔ (↑x⁻¹ * z) ∈ I.1
  iseqv := by
    refine ⟨fun I ↦ ⟨1, fun z ↦ by simp⟩, fun ⟨x, h⟩ ↦ ⟨x⁻¹, fun z ↦ ?_⟩, ?_⟩
    · rw [h, inv_inv, Units.inv_mul_cancel_left]
    · rintro I J L ⟨x, h⟩ ⟨y, h'⟩
      refine ⟨y * x, fun z ↦ ?_⟩
      rw [h', h, mul_inv_rev, Units.val_mul, mul_assoc]

/-- The set of classes of right ideals of $\mathcal{O}$. For a maximal order it is finite, and its size is the class number of $D$. -/
def QuaternionIdealClass (O : Subring ℍ[ℚ, a, b]) : Type :=
  Quotient (quaternionIdealSetoid O)

/-- The Hecke operator $T_q$ on the functions on the ideal classes (the Brandt matrix):
$$(T_q f)([I]) = \sum_{J} f([J]),$$
where $J$ runs over the right ideals $J \subseteq I$ of index $q^2$, for a fixed representative $I$ of the class. -/
def brandtHecke (O : Subring ℍ[ℚ, a, b]) (q : ℕ) (f : QuaternionIdealClass O → ℂ) :
    QuaternionIdealClass O → ℂ :=
  fun c ↦ ∑ᶠ J : {J : QuaternionRightIdeal O // J.1 ≤ c.out.1 ∧
      (AddSubgroup.relIndex J.1.toAddSubgroup c.out.1.toAddSubgroup) = q ^ 2},
    f (Quotient.mk _ J.1)

/-- The algebra $D = (a, b)_\mathbb{Q}$ is split at the prime $q$: the quaternion algebra $(a, b)_{\mathbb{Q}_q}$ has a nonzero element of reduced norm $0$, so it is isomorphic to $M_2(\mathbb{Q}_q)$. -/
def IsSplitAt (a b : ℚ) (q : ℕ) [Fact q.Prime] : Prop :=
  ∃ x : ℍ[ℚ_[q], (a : ℚ_[q]), (b : ℚ_[q])], x ≠ 0 ∧ x * star x = 0

/-! ### Sanity checks -/

/-- The order $\mathcal{O}$ is a right ideal of itself. So the set of ideal classes is not empty, and the functions on it form a nonzero space. -/
theorem QuaternionIdealClass.nonempty {O : Subring ℍ[ℚ, a, b]} (hO : IsQuaternionOrder O) :
    Nonempty (QuaternionIdealClass O) :=
  ⟨Quotient.mk _ ⟨AddSubgroup.toIntSubmodule O.toAddSubgroup, hO, fun _ hx _ hy ↦ O.mul_mem hx hy⟩⟩

/-- Two maps with the matching property of `Langlands.ReciprocityGL` are equal. -/
theorem reciprocity_map_unique {K : Type u} [Field K] [NumberField K] {n ℓ : ℕ} [Fact ℓ.Prime]
    (ι : PadicAlgCl ℓ ≃+* ℂ)
    (Φ Φ' : {c : AutomorphicClass K n // IsAlgebraicClass c} → GaloisClass K n ℓ)
    (h : ∀ (φ : CuspEigenform K n) (hφ : IsAlgebraicClass (Quotient.mk _ φ)) (ρ : GaloisRep K n ℓ),
      Φ ⟨Quotient.mk _ φ, hφ⟩ = Quotient.mk _ ρ ↔ Matches ι φ ρ.1)
    (h' : ∀ (φ : CuspEigenform K n) (hφ : IsAlgebraicClass (Quotient.mk _ φ))
      (ρ : GaloisRep K n ℓ), Φ' ⟨Quotient.mk _ φ, hφ⟩ = Quotient.mk _ ρ ↔ Matches ι φ ρ.1) :
    Φ = Φ' := by
  funext ⟨c, hc⟩
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep c
  obtain ⟨ρ, hρ⟩ := Quotient.exists_rep (Φ ⟨Quotient.mk _ φ, hc⟩)
  rw [← hρ]
  exact ((h' φ hc ρ).2 ((h φ hc ρ).1 hρ.symm)).symm

/-- For $n = 1$ the trivial character is a representation of the Galois side with finite image. So the last condition of `Langlands.ReciprocityGL` is not empty. -/
theorem isGaloisRep_one (K : Type u) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsGaloisRep (K := K) ℓ (1 : GlobalFunctionField.GaloisGroup K →* GL (Fin 1) (PadicAlgCl ℓ)) ∧
      (Set.range (1 : GlobalFunctionField.GaloisGroup K →* GL (Fin 1) (PadicAlgCl ℓ))).Finite :=
  ⟨⟨continuous_const, GlobalFunctionField.isIrreducibleRep_of_dim_one _,
    Set.finite_empty.subset fun _ hv ↦ hv fun _ _ _ _ ↦ rfl⟩,
    (Set.finite_singleton 1).subset (Set.range_subset_iff.2 fun _ ↦ rfl)⟩

end NumberFieldGL

/-! ### The statements -/

/-- **Reciprocity for $GL_n$ over a number field** (conjecture of Clozel, Fontaine and Mazur, in a weaker form). Let $n \ge 1$, let $K$ be a number field, let $\ell$ be a prime and let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ be an isomorphism of fields. Then there is a map $\Phi$ from the set of algebraic cuspidal automorphic representations $\pi$ of $GL_n(\mathbb{A}_K)$ to the set of isomorphism classes of the irreducible continuous representations $\rho : \mathrm{Gal}(\overline{K}/K) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that are unramified almost everywhere, with these properties.

* The map sends $\pi$ to the class of $\rho$ if and only if $\pi$ and $\rho$ match at almost all places: at almost all finite places $v$, the Satake parameters of $\pi_v \otimes |\det|^{(1-n)/2}$ are the images under $\iota$ of the eigenvalues of the arithmetic Frobenius $\rho(\mathrm{Frob}_v)$.
* The map is injective.
* Each representation with finite image is in the image.

The target classes are irreducible, so the statement also says that the Galois representation of each algebraic cuspidal $\pi$ is irreducible. This is an open conjecture even for regular algebraic $\pi$. The statement uses the arithmetic Frobenius, so $\Phi(\pi)$ is the contragredient of the representation in the usual normalization with the geometric Frobenius. The two forms are equivalent. Injectivity follows from the matching condition, because the classes on the automorphic side are the classes of Hecke eigensystems at almost all places.

The automorphic side is the set of classes of cuspidal Hecke eigenforms that contain an algebraic form in the sense of Clozel, stated with the eigenvalues of the Capelli operators at the infinite places. The conjecture says more: the image of $\Phi$ is the set of the classes of geometric representations, that is, the representations that are de Rham at the places over $\ell$. Mathlib has no $p$-adic Hodge theory, so this statement keeps only the representations with finite image, which are geometric. Without the condition to be de Rham, a bijection with all the representations that are unramified almost everywhere is false already for $n = 1$. The module docstring explains this, and why the statement is neither trivially true nor trivially false. For $n = 1$ it is the theorem of Weil and Serre on algebraic Hecke characters. The statement does not include the compatibility with the local correspondence at the ramified places and at the places over $\ell$. -/
def ReciprocityGL (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  0 < n → ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
    ∃ Φ : {c : AutomorphicClass K n // IsAlgebraicClass c} → GaloisClass K n ℓ,
      Function.Injective Φ ∧
      (∀ (φ : CuspEigenform K n) (hφ : IsAlgebraicClass (Quotient.mk _ φ)) (ρ : GaloisRep K n ℓ),
        Φ ⟨Quotient.mk _ φ, hφ⟩ = Quotient.mk _ ρ ↔ Matches ι φ ρ.1) ∧
      ∀ ρ : GaloisRep K n ℓ, (Set.range ρ.1).Finite → ∃ c, Φ c = Quotient.mk _ ρ

/-- **Galois representations of regular algebraic cuspidal representations** (Harris, Lan, Taylor and Thorne; Scholze). Let $K$ be a totally real or CM number field and let $\pi$ be a regular algebraic cuspidal automorphic representation of $GL_n(\mathbb{A}_K)$. Let $\ell$ be a prime and let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ be an isomorphism of fields. Then there is a continuous representation $\rho : \mathrm{Gal}(\overline{K}/K) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that is unramified almost everywhere, such that at almost all finite places $v$ the Satake parameters of $\pi_v \otimes |\det|^{(1-n)/2}$ are the images under $\iota$ of the eigenvalues of the arithmetic Frobenius $\rho(\mathrm{Frob}_v)$.

Here $\pi$ is given by a cuspidal Hecke eigenform $\varphi$ whose class contains a regular algebraic form, and the condition on Frobenius is `Langlands.NumberFieldGL.Matches`. The theorem of Harris, Lan, Taylor and Thorne and of Scholze says more: $\rho$ is unramified at each $v \nmid \ell$ where $\pi_v$ is unramified, and $\rho$ is semisimple. The statement uses the arithmetic Frobenius. The form with the geometric Frobenius, which is the usual normalization of these papers, is equivalent through the contragredient of $\rho$. For $n = 1$ the statement is the theorem of Weil and Serre on the $\ell$-adic characters of algebraic Hecke characters, for these fields. -/
def AutomorphicToGalois (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  (IsTotallyReal K ∨ IsCMField K) →
  ∀ φ : CuspEigenform K n, IsRegularAlgebraicClass (Quotient.mk _ φ) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
    ∃ ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ),
      Continuous ρ ∧ IsAlmostUnramified ρ ∧ Matches ι φ ρ

/-- **The global Jacquet-Langlands correspondence** for the definite quaternion algebra over $\mathbb{Q}$ ramified at one prime, in weight $2$ (Eichler; Jacquet and Langlands). Let $p$ be a prime and let $D = (a, b)_\mathbb{Q}$ be a quaternion algebra with $a, b < 0$ that splits at each prime $q \ne p$. So $D$ is definite and ramifies exactly at $p$ and at the infinite place. Let $\mathcal{O}$ be a maximal order of $D$, and let $e_q \in \mathbb{C}$ for each prime $q \ne p$. Then these conditions are equivalent.

* There is a nonzero function $f$ on the set of classes of right ideals of $\mathcal{O}$ with $T_q f = e_q f$ for each prime $q \ne p$, and the system $(e_q)$ is not the system $(q + 1)$ of the constant functions.
* There is a normalized Hecke eigenform of weight $2$ on $\Gamma_0(p)$ with the coefficient $a_q = e_q$ for each prime $q \ne p$.

The functions on the classes of right ideals are the automorphic forms on $D^\times$ that are invariant under $\widehat{\mathcal{O}}^\times$ and trivial at the infinite place. The eigenforms of weight $2$ on $\Gamma_0(p)$ are newforms. So this is the global correspondence of Jacquet and Langlands for $D$ in weight $2$ and in this level, with the matching of the eigenvalues of $T_q$ at the places $q \ne p$ where $D$ splits. The representations of dimension $1$ on the side of $D$ give the system $(q + 1)$, which the statement removes. The textbook form is for each quaternion algebra over each number field and each automorphic representation of $D^\times$, and the image is the set of the cuspidal $\pi$ that are discrete series at the places where $D$ ramifies. The module docstring lists the differences. -/
def GlobalJacquetLanglandsGL2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a b : ℚ), a < 0 → b < 0 →
    (∀ q : ℕ, (hq : q.Prime) → q ≠ p → haveI := Fact.mk hq; IsSplitAt a b q) →
    ∀ O : Subring ℍ[ℚ, a, b], IsMaximalQuaternionOrder O →
    ∀ e : ℕ → ℂ,
      ((∃ f : QuaternionIdealClass O → ℂ, f ≠ 0 ∧
          ∀ q : ℕ, q.Prime → q ≠ p → brandtHecke O q f = e q • f) ∧
        ¬ ∀ q : ℕ, q.Prime → q ≠ p → e q = q + 1) ↔
      ∃ f : CuspForm (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) 2,
        IsNormalizedEigenform f ∧ ∀ q : ℕ, q.Prime → q ≠ p → qCoeff f q = e q

end

end Langlands
