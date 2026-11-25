/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.FunctionField
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Vocabulary for reciprocity for $GL_n$ over a number field

This file gives the vocabulary for the statements in `Langlands.Statements.Reciprocity`. Let $K$ be a number field. These statements compare the cuspidal automorphic representations $\pi$ of $GL_n(\mathbb{A}_K)$ with the $\ell$-adic representations $\rho$ of $\mathrm{Gal}(\overline{K}/K)$. The comparison uses the Hecke eigenvalues of $\pi$ and the Frobenius elements of $\rho$ at almost all finite places. The cusp forms and the Hecke operators $T_{v,i}$ come from `Langlands.Statements.Automorphic`. The absolute Galois group, the places of $\overline{K}$ and the inertia groups come from `Langlands.Statements.FunctionField`, where they are defined for an arbitrary field.

## Algebraic representations

Let $w$ be an infinite place of $K$ and let $\mathfrak{g}_w$ be the complexified Lie algebra of $GL_n(K_w)$. It is $\mathfrak{gl}_n(\mathbb{C})$ for a real place and $\mathfrak{gl}_n(\mathbb{C}) \times \mathfrak{gl}_n(\mathbb{C})$ for a complex place. The center $Z(\mathfrak{g}_w)$ of the universal enveloping algebra acts on the smooth vectors of $\pi_w$ by a character, the infinitesimal character. By Harish-Chandra, a character of the center of $U(\mathfrak{gl}_n(\mathbb{C}))$ is given by a multiset $\{h_1, \ldots, h_n\}$ of complex numbers. The irreducible representation of highest weight $\lambda$ has the parameter $h = \lambda + \delta$ with $\delta_i = (n + 1)/2 - i$. So $\pi_w$ has one multiset of parameters at a real place and two at a complex place.

Clozel calls $\pi$ algebraic if for each infinite place $w$, the restriction to $\mathbb{C}^\times$ of the Langlands parameter of $\pi_w \otimes |\det|^{(1-n)/2}$ has the form $z \mapsto \mathrm{diag}(z^{p_1} \bar z^{q_1}, \ldots, z^{p_n} \bar z^{q_n})$ with integers $p_i$ and $q_i$. The parameters of the infinitesimal character of $\pi_w$ are the numbers $p_i + (n-1)/2$, and at a complex place also the numbers $q_i + (n-1)/2$. At a real place the multiset of the $q_i$ is the multiset of the $p_i$. So $\pi$ is algebraic if and only if $h_i - (n-1)/2$ is an integer for each parameter $h_i$ at each infinite place. It is regular algebraic if, moreover, the parameters at each infinite place are distinct. This holds if and only if $\pi_\infty$ has the infinitesimal character of an irreducible algebraic representation of $\mathrm{Res}_{K/\mathbb{Q}} GL_n$.

This file states the condition with the Capelli determinant. For a family $D_{ij}$ of operators that satisfy the relations of the elementary matrices $E_{ij}$ of $\mathfrak{gl}_n$, let
$$C(u) = \sum_{\sigma \in S_n} \mathrm{sgn}(\sigma) \, (D + u)_{\sigma(1) 1} \, (D + u - 1)_{\sigma(2) 2} \cdots (D + u - n + 1)_{\sigma(n) n}.$$
The coefficients of the polynomial $C(u)$ generate the center of $U(\mathfrak{gl}_n)$. On the representation of highest weight $\lambda$, the operator $C(u)$ acts by $\prod_{i=1}^n (u + \lambda_i - i + 1) = \prod_{i=1}^n (u + h_i - (n-1)/2)$. So $\pi$ is algebraic if and only if, at each infinite place, each Capelli operator acts by $\prod_i (u + l_i)$ for integers $l_i$. Regular algebraic means that the $l_i$ are also distinct. For example, the constant function on $GL_2$ has $l = \{0, -1\}$ at a real place, and so does the form of a holomorphic newform of weight $2$. For $n = 1$ the operator is $C(u) = u + D_{11}$, and the condition says that a Hecke character $\chi$ has $\chi_w(x) = |x|^{l} \, \mathrm{sgn}(x)^{\epsilon}$ with $l \in \mathbb{Z}$ at a real place $w$. At a complex place there are two operators, and the condition says $\chi_w(z) = z^p \bar z^q$ with $p, q \in \mathbb{Z}$. These are the algebraic Hecke characters, of type $A_0$ in the terms of Weil.

The operators $D_{ij}$ are the derivatives of the right translation. For $X \in \mathfrak{gl}_n(K_w)$, let $(L_X \varphi)(g)$ be the derivative of $t \mapsto \varphi(g (1 + tX))$ at $t = 0$, for real $t$. At a real place $D_{ij} = L_{E_{ij}}$. At a complex place the complexification of the real Lie algebra $\mathfrak{gl}_n(\mathbb{C})$ is a product of two copies of $\mathfrak{gl}_n(\mathbb{C})$, with the elementary matrices $\frac{1}{2}(E_{ij} \otimes 1 - i E_{ij} \otimes i)$ and $\frac{1}{2}(E_{ij} \otimes 1 + i E_{ij} \otimes i)$. They give the holomorphic and the antiholomorphic operators.

* `Langlands.NumberFieldGL.archGL w` is the embedding of $GL_n(K_w)$ at an infinite place $w$, with the identity at the other places.
* `Langlands.NumberFieldGL.lieDerivative w X` is the operator $L_X$, and `Langlands.NumberFieldGL.IsArchSmooth` is the smoothness at the infinite places.
* `Langlands.NumberFieldGL.capelliOperator D u` is $C(u)$, and `Langlands.NumberFieldGL.HasCapelliRoots D φ l` says that $C(u) \varphi = \prod_i (u + l_i) \varphi$ for all $u \in \mathbb{C}$.
* `Langlands.NumberFieldGL.IsAlgebraicForm` and `Langlands.NumberFieldGL.IsRegularAlgebraicForm` are the conditions of Clozel on a smooth form.

## Classes and the matching condition

* `Langlands.NumberFieldGL.CuspEigenform K n` is the type of the nonzero cuspidal Hecke eigenforms, and `Langlands.NumberFieldGL.AutomorphicClass K n` is its quotient by the relation of equal eigenvalues at almost all places. By strong multiplicity one, the classes are the cuspidal automorphic representations. `Langlands.NumberFieldGL.IsAlgebraicClass` and `Langlands.NumberFieldGL.IsRegularAlgebraicClass` say that a class contains an algebraic or a regular algebraic form.
* `Langlands.NumberFieldGL.heckePolynomial n q λ` is the polynomial $X^n + \sum_{i=1}^n (-1)^i q^{i(i-1)/2} \lambda_i X^{n-i}$. If $\alpha_1, \ldots, \alpha_n$ are the Satake parameters of the eigenvalues $\lambda_i$, then its roots are the numbers $q^{(n-1)/2} \alpha_j$. These are the Satake parameters of $\pi_v \otimes |\det|^{(1-n)/2}$, the twist of Clozel. The coefficients contain only integral powers of $q$.
* `Langlands.NumberFieldGL.IsFrobAt v σ` says that $\sigma$ is an arithmetic Frobenius at the finite place $v$, and `Langlands.NumberFieldGL.IsUnramAt ρ v` says that $\rho$ is unramified at $v$.
* `Langlands.NumberFieldGL.Matches ι φ ρ` is the matching condition at almost all places: the Hecke polynomial of $\varphi$ at $v$ is the image under $\iota$ of the characteristic polynomial of $\rho(\sigma)$ for each arithmetic Frobenius $\sigma$ at $v$.
* `Langlands.NumberFieldGL.GaloisRep K n ℓ` is the type of the continuous irreducible representations $\mathrm{Gal}(\overline{K}/K) \to GL_n(\overline{\mathbb{Q}}_\ell)$ that are unramified almost everywhere, and `Langlands.NumberFieldGL.GaloisClass K n ℓ` is the type of their isomorphism classes.

For a newform of weight $2$ with trivial character and a prime $p$ that does not divide the level, the eigenvalues are $\lambda_1 = a_p$ and $\lambda_2 = 1$. The Hecke polynomial is $X^2 - a_p X + p$, the characteristic polynomial of the arithmetic Frobenius on the representation of `Langlands.EichlerShimuraDeligne`. For $n = 1$ the Hecke polynomial is $X - \lambda_1$.

## Implementation notes

The cusp forms of `Langlands.Statements.Automorphic` are continuous, but they need not be smooth at the infinite places. The function `deriv` of Mathlib gives $0$ at a point where a function is not differentiable. Without a smoothness condition, a form that is nowhere differentiable at the infinite places would have all $L_X \varphi = 0$, so it would satisfy the Capelli condition with $l = \{0, -1, \ldots, 1 - n\}$. For this reason `IsAlgebraicForm` contains the condition `IsArchSmooth`. The condition on a class is that it contains an algebraic form. Each cuspidal automorphic representation $\pi$ has nonzero smooth vectors that are invariant under some $K(N)$, because the smooth vectors are dense. The center of $U(\mathfrak{g}_w)$ acts on all the smooth vectors of $\pi$ by the infinitesimal character. So the condition on a class is the condition of Clozel on $\pi$.

The derivative uses the path $1 + tX$ and not $\exp(tX)$. The two paths have the same derivative at $t = 0$, and the first one needs no exponential map on matrices over $K_w$. The function `onePlusGL` gives $1$ when $1 + tX$ is not invertible. This happens only for $t$ away from $0$, so it does not change the derivative. Mathlib has no structure of an $\mathbb{R}$-algebra on $K_w$, so `realToCompletion` uses the isomorphism of $K_w$ with $\mathbb{R}$ or $\mathbb{C}$. At a complex place the other choice of the isomorphism with $\mathbb{C}$ exchanges the holomorphic and the antiholomorphic operators, and the conditions do not change. The conditions are also invariant under $l \mapsto -l$ and under a shift of all the $l_i$ by the integer $n - 1$. So they do not depend on the choice of the left or the right action, or of a representation or its contragredient.

The places of $\overline{K}$ over $v$ are the valuation subrings $W$ of $\overline{K}$ with $W \cap K = \mathcal{O}_{K,v}$, as in `Langlands.Statements.FunctionField`. The norm $q_v$ is `Ideal.absNorm v.asIdeal`. The matching condition is at almost all places, as the decision of the specification says. There is no condition at the ramified places or at the places over $\ell$.

The statements use the arithmetic Frobenius. A representation $\rho$ matches $\pi$ for the arithmetic Frobenius if and only if the contragredient $\rho^\vee$ matches $\pi$ for the geometric Frobenius, because $\rho^\vee(\sigma^{-1})$ is the transpose of $\rho(\sigma)$. The contragredient of an irreducible representation is irreducible, so the two forms of each statement are equivalent.

## References

* L. Clozel, Motifs et formes automorphes: applications du principe de fonctorialité, in Automorphic forms, Shimura varieties, and L-functions, Vol. I, Perspect. Math. 10, Academic Press, 1990, 77-159.
* K. Buzzard and T. Gee, The conjectural connections between automorphic representations and Galois representations, in Automorphic forms and Galois representations, Vol. 1, London Math. Soc. Lecture Note Ser. 414, 2014.
* A. Capelli, Über die Zurückführung der Cayley'schen Operation $\Omega$ auf gewöhnliche Polar-Operationen, Math. Ann. 29 (1887), 331-338.
* R. Howe and T. Umeda, The Capelli identity, the double commutant theorem, and multiplicity-free actions, Math. Ann. 290 (1991), 565-619.
* A. Molev, Yangians and classical Lie algebras, Math. Surveys Monogr. 143, Amer. Math. Soc., 2007, chapter 7.
* H. Jacquet and J. Shalika, On Euler products and the classification of automorphic forms II, Amer. J. Math. 103 (1981), 777-815.
-/

namespace Langlands

universe u

namespace NumberFieldGL

open NumberField IsDedekindDomain Polynomial
open scoped Classical ContDiff

noncomputable section

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-! ### The infinite places -/

variable (K) in
/-- The adele with the component $x$ at the infinite place $w$ and $0$ at the other places. -/
def archAdele (w : InfinitePlace K) : w.Completion →+ AdeleRing (𝓞 K) K where
  toFun x := ((Pi.single w x : (v : InfinitePlace K) → v.Completion), 0)
  map_zero' := Prod.ext (Pi.single_zero w) rfl
  map_add' x y := Prod.ext (Pi.single_add w x y) (add_zero 0).symm

/-- The map `archAdele K w` is multiplicative. -/
theorem archAdele_mul (w : InfinitePlace K) (x y : w.Completion) :
    archAdele K w (x * y) = archAdele K w x * archAdele K w y :=
  Prod.ext (Pi.single_mul w x y) (mul_zero 0).symm

/-- The map `archAdele K w` on matrices is multiplicative. -/
theorem archAdele_mapMatrix_mul (w : InfinitePlace K)
    (A B : Matrix (Fin n) (Fin n) w.Completion) :
    (archAdele K w).mapMatrix (A * B) =
      (archAdele K w).mapMatrix A * (archAdele K w).mapMatrix B := by
  ext i j
  simp [Matrix.mul_apply, map_sum, archAdele_mul]

/-- The adelic matrix with the component $M$ at the infinite place $w$ and the identity at the other places. -/
def archMatrix (w : InfinitePlace K) :
    Matrix (Fin n) (Fin n) w.Completion →* Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K) where
  toFun M := 1 + (archAdele K w).mapMatrix (M - 1)
  map_one' := by simp
  map_mul' M N := by
    have h : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
    rw [h, map_add, map_add, archAdele_mapMatrix_mul]
    noncomm_ring

/-- The embedding $GL_n(K_w) \to GL_n(\mathbb{A}_K)$ at the infinite place $w$, with the identity at the other places. -/
def archGL (w : InfinitePlace K) : GL (Fin n) w.Completion →* AdelicGL K n :=
  Units.map (archMatrix w)

/-- The embedding $\mathbb{R} \to K_w$. The completion $K_w$ is $\mathbb{R}$ or $\mathbb{C}$, and the embedding is the inverse of the isomorphism of Mathlib, restricted to $\mathbb{R}$ in the complex case. -/
def realToCompletion (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if h : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.1 h)).symm.toRingHom.comp Complex.ofRealHom

/-- A square root of $-1$ in $K_w$ for a complex place $w$: the image of $i \in \mathbb{C}$. At a real place it is $0$, and it is not used there. -/
def completionI (w : InfinitePlace K) : w.Completion :=
  if h : w.IsComplex then (InfinitePlace.Completion.ringEquivComplexOfIsComplex h).symm Complex.I
  else 0

/-- The element $1 + M$ of $GL_n(K_w)$ if $\det(1 + M) \ne 0$, and $1$ if not. Only small $M$ are used, and for them $1 + M$ is invertible. -/
def onePlusGL (w : InfinitePlace K) (M : Matrix (Fin n) (Fin n) w.Completion) :
    GL (Fin n) w.Completion :=
  if h : (1 + M).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

/-- The derivative of $\varphi$ along the right translation in the direction $X \in \mathfrak{gl}_n(K_w)$:
$$(L_X \varphi)(g) = \frac{d}{dt}\Big|_{t = 0} \varphi(g (1 + t X)),$$
where $t$ is real and $1 + tX$ sits at the place $w$. For a smooth $\varphi$ this is the action of the real Lie algebra $\mathfrak{gl}_n(K_w)$ by left invariant vector fields. -/
def lieDerivative (w : InfinitePlace K) (X : Matrix (Fin n) (Fin n) w.Completion)
    (φ : AdelicGL K n → ℂ) : AdelicGL K n → ℂ :=
  fun g ↦ deriv (fun t : ℝ ↦ φ (g * archGL w (onePlusGL w (realToCompletion w t • X)))) 0

/-- The function $\varphi$ is smooth at the infinite places: for each $g$, each infinite place $w$ and each finite family $X_1, \ldots, X_m$ in $\mathfrak{gl}_n(K_w)$, the function $t \mapsto \varphi(g (1 + \sum_k t_k X_k))$ of $t \in \mathbb{R}^m$ is $C^\infty$ near $0$. With a real basis of $\mathfrak{gl}_n(K_w)$ this is the smoothness of $\varphi$ in the variable of $GL_n(K_w)$. -/
def IsArchSmooth (φ : AdelicGL K n → ℂ) : Prop :=
  ∀ (w : InfinitePlace K) (g : AdelicGL K n) (m : ℕ)
    (X : Fin m → Matrix (Fin n) (Fin n) w.Completion),
    ContDiffAt ℝ ∞
      (fun t : Fin m → ℝ ↦ φ (g * archGL w (onePlusGL w (∑ k, realToCompletion w (t k) • X k)))) 0

/-! ### The Capelli operator -/

/-- The Capelli operator of a family of operators $D_{ij}$, $1 \le i, j \le n$:
$$C(u) = \sum_{\sigma \in S_n} \mathrm{sgn}(\sigma) \, (D + u)_{\sigma(1) 1} \, (D + u - 1)_{\sigma(2) 2} \cdots (D + u - n + 1)_{\sigma(n) n},$$
where $(D + c)_{ij} = D_{ij} + c \, \delta_{ij}$. The product is a composition of operators, so the factor of the column $n$ acts first. For the operators $D_{ij} = L_{E_{ij}}$ of a representation of $\mathfrak{gl}_n$, the coefficients of the polynomial $C(u)$ generate the center of the universal enveloping algebra. -/
def capelliOperator {G : Type*} (D : Fin n → Fin n → (G → ℂ) → G → ℂ) (u : ℂ) (φ : G → ℂ) :
    G → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin n ↦ fun ψ : G → ℂ ↦
      D (σ k) k ψ + if σ k = k then (u - ((k : ℕ) : ℂ)) • ψ else 0).foldr (· ∘ ·) id φ

/-- The function $\varphi$ is an eigenvector of the Capelli operator $C(u)$ for each $u \in \mathbb{C}$, with the eigenvalue $\prod_{i=1}^n (u + l_i)$ for the given multiset $\{l_1, \ldots, l_n\}$ of integers. -/
def HasCapelliRoots {G : Type*} (D : Fin n → Fin n → (G → ℂ) → G → ℂ) (φ : G → ℂ)
    (l : Multiset ℤ) : Prop :=
  Multiset.card l = n ∧ ∀ u : ℂ, capelliOperator D u φ = (l.map fun x : ℤ ↦ u + (x : ℂ)).prod • φ

/-- The operators $D_{ij} = L_{E_{ij}}$ at a real place $w$, for the elementary matrices $E_{ij}$. -/
def realGenerator (w : InfinitePlace K) (i j : Fin n) (φ : AdelicGL K n → ℂ) :
    AdelicGL K n → ℂ :=
  lieDerivative w (Matrix.single i j 1) φ

/-- The holomorphic operators $D_{ij} = \frac{1}{2}(L_{E_{ij}} - i L_{i E_{ij}})$ at a complex place $w$. -/
def holGenerator (w : InfinitePlace K) (i j : Fin n) (φ : AdelicGL K n → ℂ) :
    AdelicGL K n → ℂ :=
  (1 / 2 : ℂ) • (lieDerivative w (Matrix.single i j 1) φ -
    Complex.I • lieDerivative w (Matrix.single i j (completionI w)) φ)

/-- The antiholomorphic operators $\bar D_{ij} = \frac{1}{2}(L_{E_{ij}} + i L_{i E_{ij}})$ at a complex place $w$. -/
def antiholGenerator (w : InfinitePlace K) (i j : Fin n) (φ : AdelicGL K n → ℂ) :
    AdelicGL K n → ℂ :=
  (1 / 2 : ℂ) • (lieDerivative w (Matrix.single i j 1) φ +
    Complex.I • lieDerivative w (Matrix.single i j (completionI w)) φ)

/-- The function $\varphi$ is smooth at the infinite places, and at each infinite place its Capelli eigenvalues are given by integers $l_i$ with the property $P$. At a real place there is one Capelli operator. At a complex place there are two, a holomorphic and an antiholomorphic one. -/
def IsAlgebraicFormWith (P : Multiset ℤ → Prop) (φ : AdelicGL K n → ℂ) : Prop :=
  IsArchSmooth φ ∧ ∀ w : InfinitePlace K,
    (w.IsReal → ∃ l, P l ∧ HasCapelliRoots (realGenerator w) φ l) ∧
    (w.IsComplex → (∃ l, P l ∧ HasCapelliRoots (holGenerator w) φ l) ∧
      ∃ l, P l ∧ HasCapelliRoots (antiholGenerator w) φ l)

/-- The function $\varphi$ is algebraic in the sense of Clozel: its Capelli eigenvalues are given by integers at each infinite place. -/
def IsAlgebraicForm (φ : AdelicGL K n → ℂ) : Prop :=
  IsAlgebraicFormWith (fun _ ↦ True) φ

/-- The function $\varphi$ is regular algebraic: its Capelli eigenvalues are given by distinct integers at each infinite place. -/
def IsRegularAlgebraicForm (φ : AdelicGL K n → ℂ) : Prop :=
  IsAlgebraicFormWith Multiset.Nodup φ

/-! ### Classes of cuspidal eigenforms -/

variable (K n) in
/-- The nonzero cusp forms on $GL_n$ over $K$, of some level, that are Hecke eigenforms. -/
def CuspEigenform : Type u :=
  {φ : AdelicGL K n → ℂ // (∃ N, IsCuspForm N φ) ∧ φ ≠ 0 ∧ IsHeckeEigenform φ}

/-- Two cuspidal eigenforms are equivalent if they have the same Hecke eigenvalues at almost all finite places. By strong multiplicity one, this holds if and only if they lie in the same cuspidal automorphic representation. -/
def CuspEigenform.Equiv (φ ψ : CuspEigenform K n) : Prop :=
  ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧
    ∀ v ∉ S, ∃ ev : ℕ → ℂ, IsHeckeEigenAt φ.1 v ev ∧ IsHeckeEigenAt ψ.1 v ev

/-- The Hecke eigenvalues of a nonzero eigenvector are unique. -/
theorem heckeEigenvalue_unique {φ : AdelicGL K n → ℂ} (hφ : φ ≠ 0) {v : HeightOneSpectrum (𝓞 K)}
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

/-- The eigenvalue condition depends only on $\lambda_1, \ldots, \lambda_n$. -/
theorem isHeckeEigenAt_congr {φ : AdelicGL K n → ℂ} {v : HeightOneSpectrum (𝓞 K)}
    {ev ev' : ℕ → ℂ} (h : IsHeckeEigenAt φ v ev) (he : ∀ i, 1 ≤ i → i ≤ n → ev i = ev' i) :
    IsHeckeEigenAt φ v ev' :=
  ⟨h.1, fun i hi₁ hi₂ ↦ by rw [h.2 i hi₁ hi₂, he i hi₁ hi₂]⟩

variable (K n) in
/-- The relation of equal eigenvalues at almost all places is an equivalence relation. -/
def cuspSetoid : Setoid (CuspEigenform K n) where
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
      exact ⟨ev, h₁, isHeckeEigenAt_congr h₄ fun i hi₁ hi₂ ↦
        (heckeEigenvalue_unique ψ.2.2.1 h₂ h₃ hi₁ hi₂).symm⟩

variable (K n) in
/-- The classes of nonzero cuspidal Hecke eigenforms for the relation of equal eigenvalues at almost all places. These are the cuspidal automorphic representations of $GL_n(\mathbb{A}_K)$. -/
def AutomorphicClass : Type u :=
  Quotient (cuspSetoid K n)

/-- A class is algebraic if it contains an algebraic form. -/
def IsAlgebraicClass (c : AutomorphicClass K n) : Prop :=
  ∃ φ : CuspEigenform K n, Quotient.mk _ φ = c ∧ IsAlgebraicForm φ.1

/-- A class is regular algebraic if it contains a regular algebraic form. -/
def IsRegularAlgebraicClass (c : AutomorphicClass K n) : Prop :=
  ∃ φ : CuspEigenform K n, Quotient.mk _ φ = c ∧ IsRegularAlgebraicForm φ.1

variable (n) in
/-- The Hecke polynomial $X^n + \sum_{i=1}^n (-1)^i q^{i(i-1)/2} \lambda_i X^{n-i}$. Its roots are $q^{(n-1)/2} \alpha_j$ for the Satake parameters $\alpha_j$. -/
def heckePolynomial (q : ℕ) (ev : ℕ → ℂ) : Polynomial ℂ :=
  X ^ n + ∑ i ∈ Finset.Icc 1 n, C ((-1) ^ i * (q : ℂ) ^ i.choose 2 * ev i) * X ^ (n - i)

/-! ### The Galois side -/

/-- The finite place $v$ as a surjective discrete valuation of $K$. -/
def finitePlace (v : HeightOneSpectrum (𝓞 K)) : GlobalFunctionField.Place K :=
  ⟨v.valuation K, v.valuation_surjective K⟩

/-- The element $\sigma$ of $\mathrm{Gal}(\overline{K}/K)$ is an arithmetic Frobenius at the finite place $v$: there is a place $W$ of $\overline{K}$ over $v$ with $\sigma(W) = W$ and $\sigma(x) \equiv x^{q_v}$ modulo the maximal ideal of $W$ for each $x \in W$, where $q_v = |\mathcal{O}_K / \mathfrak{p}_v|$. -/
def IsFrobAt (v : HeightOneSpectrum (𝓞 K)) (σ : GlobalFunctionField.GaloisGroup K) : Prop :=
  ∃ W : ValuationSubring (AlgebraicClosure K),
    GlobalFunctionField.ValuationSubring.LiesOver W (finitePlace v) ∧
    GlobalFunctionField.IsInDecomposition W σ ∧
    ∀ x ∈ W, W.valuation (GlobalFunctionField.galoisAct σ x - x ^ Ideal.absNorm v.asIdeal) < 1

/-- The representation $\rho$ is unramified at the finite place $v$. -/
def IsUnramAt {H : Type*} [Group H] (ρ : GlobalFunctionField.GaloisGroup K →* H)
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  GlobalFunctionField.IsUnramifiedAt ρ (finitePlace v)

/-- The representation $\rho$ is unramified at all finite places outside a finite set. -/
def IsAlmostUnramified {H : Type*} [Group H] (ρ : GlobalFunctionField.GaloisGroup K →* H) :
    Prop :=
  {v : HeightOneSpectrum (𝓞 K) | ¬ IsUnramAt ρ v}.Finite

/-- The matching condition at almost all places between a cuspidal eigenform $\varphi$ and a representation $\rho$: there is a finite set $S$ of finite places such that, for each $v \notin S$ where $\varphi$ is a Hecke eigenvector with eigenvalues $\lambda_i$ and each arithmetic Frobenius $\sigma$ at $v$, the Hecke polynomial of the $\lambda_i$ is the image under $\iota$ of the characteristic polynomial of $\rho(\sigma)$. -/
def Matches {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) (φ : CuspEigenform K n)
    (ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ)) : Prop :=
  ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ v ∉ S, ∀ ev : ℕ → ℂ,
    IsHeckeEigenAt φ.1 v ev → ∀ σ, IsFrobAt v σ →
      heckePolynomial n (Ideal.absNorm v.asIdeal) ev =
        (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly.map (ι : PadicAlgCl ℓ →+* ℂ)

/-- The representations of the Galois side: continuous, irreducible and unramified almost everywhere. -/
structure IsGaloisRep (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ)) : Prop where
  continuous : Continuous ρ
  irreducible : IsIrreducibleRep ρ
  almost_unramified : IsAlmostUnramified ρ

variable (K n) in
/-- The representations of the Galois side, before the passage to isomorphism classes. -/
def GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] : Type u :=
  {ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ) // IsGaloisRep ℓ ρ}

/-- Two representations are isomorphic if they are conjugate by a matrix $A \in GL_n(\overline{\mathbb{Q}}_\ell)$. -/
def GaloisRep.Iso {ℓ : ℕ} [Fact ℓ.Prime] (ρ ρ' : GaloisRep K n ℓ) : Prop :=
  ∃ A : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, ρ'.1 σ = A * ρ.1 σ * A⁻¹

variable (K n) in
/-- Isomorphism of representations is an equivalence relation. -/
def galoisSetoid (ℓ : ℕ) [Fact ℓ.Prime] : Setoid (GaloisRep K n ℓ) where
  r := GaloisRep.Iso
  iseqv := by
    refine ⟨fun ρ ↦ ⟨1, fun σ ↦ by simp⟩, fun ⟨A, h⟩ ↦ ⟨A⁻¹, fun σ ↦ ?_⟩, ?_⟩
    · rw [h σ]
      group
    · rintro ρ ρ' ρ'' ⟨A, h⟩ ⟨B, h'⟩
      exact ⟨B * A, fun σ ↦ by rw [h' σ, h σ]; group⟩

variable (K n) in
/-- The Galois side: the isomorphism classes of the representations. -/
def GaloisClass (ℓ : ℕ) [Fact ℓ.Prime] : Type u :=
  Quotient (galoisSetoid K n ℓ)

/-! ### Sanity checks -/

/-- For $n = 1$ the Capelli operator is $D_{11} + u$. -/
theorem capelliOperator_one {G : Type*} (D : Fin 1 → Fin 1 → (G → ℂ) → G → ℂ) (u : ℂ)
    (φ : G → ℂ) : capelliOperator D u φ = D 0 0 φ + u • φ := by
  simp [capelliOperator]

/-- For $n = 1$ the Hecke polynomial is $X - \lambda_1$, as for the Satake polynomial. -/
theorem heckePolynomial_one (q : ℕ) (ev : ℕ → ℂ) : heckePolynomial 1 q ev = X - C (ev 1) := by
  simp [heckePolynomial, sub_eq_add_neg]

/-- For $n = 2$ the Hecke polynomial is $X^2 - \lambda_1 X + q \lambda_2$. -/
theorem heckePolynomial_two (q : ℕ) (ev : ℕ → ℂ) :
    heckePolynomial 2 q ev = X ^ 2 - C (ev 1) * X + C ((q : ℂ) * ev 2) := by
  simp [heckePolynomial, Finset.sum_Icc_succ_top, sub_eq_add_neg, add_assoc]

/-- The matching condition depends on $\rho$ only up to conjugation. -/
theorem matches_conj {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) (φ : CuspEigenform K n)
    (ρ ρ' : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ))
    (A : GL (Fin n) (PadicAlgCl ℓ)) (hA : ∀ σ, ρ' σ = A * ρ σ * A⁻¹) :
    Matches ι φ ρ ↔ Matches ι φ ρ' := by
  have hc (σ : GlobalFunctionField.GaloisGroup K) :
      (ρ' σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly =
        (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly := by
    rw [hA σ, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  simp only [Matches, hc]

/-- The Hecke polynomial depends only on $\lambda_1, \ldots, \lambda_n$. -/
theorem heckePolynomial_congr (q : ℕ) {ev ev' : ℕ → ℂ} (h : ∀ i, 1 ≤ i → i ≤ n → ev i = ev' i) :
    heckePolynomial n q ev = heckePolynomial n q ev' := by
  unfold heckePolynomial
  refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
  obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.1 hi
  rw [h i h₁ h₂]

/-- The matching condition depends on $\varphi$ only through its class. -/
theorem matches_of_equiv {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    {φ ψ : CuspEigenform K n} (h : φ.Equiv ψ)
    (ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ)) :
    Matches ι φ ρ → Matches ι ψ ρ := by
  rintro ⟨S, hS, hm⟩
  obtain ⟨T, hT, he⟩ := h
  refine ⟨S ∪ T, hS.union hT, fun v hv ev hev σ hσ ↦ ?_⟩
  obtain ⟨ev', h₁, h₂⟩ := he v fun hT' ↦ hv (Or.inr hT')
  rw [heckePolynomial_congr _ fun i hi₁ hi₂ ↦ heckeEigenvalue_unique ψ.2.2.1 hev h₂ hi₁ hi₂]
  exact hm v (fun hS' ↦ hv (Or.inl hS')) ev' h₁ σ hσ

/-- For $n = 1$ the matching condition at $v$ says $\iota(\rho(\sigma)) = \lambda_1$, the eigenvalue of $T_{v,1}$. -/
theorem heckePolynomial_one_eq_charpoly_map_iff {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (q : ℕ) (ev : ℕ → ℂ) (A : Matrix (Fin 1) (Fin 1) (PadicAlgCl ℓ)) :
    heckePolynomial 1 q ev = A.charpoly.map (ι : PadicAlgCl ℓ →+* ℂ) ↔ ι (A 0 0) = ev 1 := by
  rw [heckePolynomial_one, Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, sub_right_inj, Polynomial.C_inj]
  exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

end

end NumberFieldGL

end Langlands
