/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The fundamental lemma for unitary Lie algebras

This file states one row of 6.2.2 of the spec, `Langlands.FundamentalLemma`, in the form of Laumon and Ngô for the Lie algebras of unitary groups. The statement is a `def` of type `Prop`. It is a theorem of Laumon and Ngô for residue characteristic $p > n$, extended to all large $p$ in characteristic zero by Waldspurger. It is not formalized.

## The mathematics

Let $F$ be a nonarchimedean local field with ring of integers $\mathcal{O}_F$ and residue field $\mathbb{F}_q$. Let $E/F$ be the unramified quadratic extension, with Galois involution $\sigma$ and ring of integers $\mathcal{O}_E$. On $V = E^n$ take the hermitian form $h(x, y) = \sum_l x_l \sigma(y_l)$. The adjoint of a matrix $X$ is $X^* = {}^t\sigma(X)$. The unitary group is $G = U(n)$ with $G(F) = \{ g \in GL_n(E) : g^* g = 1 \}$, and $K = G(\mathcal{O}_F) = G(F) \cap GL_n(\mathcal{O}_E)$ is a hyperspecial maximal compact subgroup.

The Lie algebra $\mathfrak{u}(n)(F)$ is the space of matrices with $X^* = -X$. Fix a unit $\varepsilon \in \mathcal{O}_E^\times$ with $\sigma(\varepsilon) = -\varepsilon$; it exists because $E/F$ is unramified and $p$ is odd. Then $X \mapsto \varepsilon X$ is a $G(F)$-equivariant bijection from $\mathfrak{u}(n)(F)$ onto the space of hermitian matrices $A^* = A$, and it maps the lattice $\mathfrak{u}(n)(\mathcal{O}_F)$ onto the integral hermitian matrices. This file works with hermitian matrices. The characteristic polynomial of a hermitian matrix has coefficients in $F$.

A hermitian matrix $A$ is regular semisimple if its characteristic polynomial $\chi$ is separable. Its centralizer $T$ in $G$ is then a maximal torus. Two such matrices are stably conjugate if they have the same characteristic polynomial. The stable class of $\chi$ is a finite union of $G(F)$-classes, and the classes are a torsor under the group $\ker(H^1(F, T) \to H^1(F, G))$.

The orbital integral of the unit function $1_{\mathfrak{k}}$ of the lattice $\mathfrak{k} = \mathfrak{u}(n)(\mathcal{O}_F)$ at $A$ is
$$O_A(1_{\mathfrak{k}}) = \int_{T(F) \backslash G(F)} 1_{\mathfrak{k}}(g^{-1} A g) \, \frac{dg}{dt}.$$
Normalize the measures with $\mathrm{vol}(K) = 1$ and $\mathrm{vol}(T_c) = 1$, where $T_c$ is the maximal compact subgroup of $T(F)$. The map $T g K \mapsto g^{-1} A g$ is a bijection from the double cosets with $g^{-1} A g \in \mathfrak{k}$ onto the $K$-classes of integral matrices in the $G(F)$-class of $A$. The double coset $T g K$ has volume $[T'_c : T'_c \cap K]$, where $T'$ is the centralizer of $B = g^{-1} A g$. So
$$O_A(1_{\mathfrak{k}}) = \sum_{B} [T_{B, c} : T_{B, c} \cap K],$$
where $B$ runs over the $K$-classes of integral hermitian matrices in the $G(F)$-class of $A$. This sum is finite.

Write $\chi = \chi_1 \chi_2$ with $\chi_i$ monic of degree $n_i$ and $n = n_1 + n_2$. Then $V$ is the orthogonal sum of $V_1 = \ker \chi_1(A)$ and $V_2 = \ker \chi_2(A)$. The group $H = U(n_1) \times U(n_2)$ is an endoscopic group of $G$, and the pair $(\chi_1, \chi_2)$ is a stable class in its Lie algebra. The endoscopic character $\kappa$ takes on a class $B$ the value $\kappa(B) = \eta(\mathrm{disc}\, V_2)$, where $\eta : F^\times \to \{\pm 1\}$ is the quadratic character of $E/F$ and $\mathrm{disc}\, V_2$ is the determinant of the Gram matrix of $h$ on a basis of $V_2$. The $\kappa$-orbital integral is
$$O^\kappa_{\chi_1 \chi_2}(1_{\mathfrak{k}}) = \sum_B \kappa(B) [T_{B, c} : T_{B, c} \cap K]$$
over all $K$-classes of integral hermitian matrices with characteristic polynomial $\chi_1 \chi_2$. The stable orbital integral $SO_\chi$ is the same sum without the sign.

The fundamental lemma says that
$$O^\kappa_{\chi_1 \chi_2}(1_{\mathfrak{u}(n)(\mathcal{O}_F)}) = \Delta(\chi_1, \chi_2) \, SO_{\chi_1}(1_{\mathfrak{u}(n_1)(\mathcal{O}_F)}) \, SO_{\chi_2}(1_{\mathfrak{u}(n_2)(\mathcal{O}_F)}),$$
with the transfer factor $\Delta(\chi_1, \chi_2) = \eta(R) \, |R|_F^{-1} = (-q)^{r}$. Here $R = \mathrm{Res}(\chi_1, \chi_2)$ is the resultant and $r$ is its valuation. The stable orbital integral of the unit of $\mathfrak{h}(\mathcal{O}_F)$ is the product of the stable orbital integrals of the two factors.

For $n = 2$ and $n_1 = n_2 = 1$ the identity is an explicit computation with lattices in $E^2$, and both sides are $(-q)^r$.

## Implementation notes

The field $F$ is a nonarchimedean local field in the sense of `IsNonarchimedeanLocalField`, with its ring of integers `𝒪[F]`. The field $E$ is any field with an $F$-algebra structure of degree two and an $F$-automorphism $\sigma \ne 1$. The condition `IsInert` says that the maximal ideal of $\mathcal{O}_F$ stays prime in the integral closure $\mathcal{O}_E$, so $E/F$ is the unramified quadratic extension. The topology of $E$ is not used.

The orbital integrals are not written as integrals. Mathlib has Haar measures, but the measure on $T(F) \backslash G(F)$ needs the theory of quotient measures for a torus that depends on $A$. The file uses the formula above as a finite sum of indices instead. This is the standard lattice count. The sum over all $K$-classes in the stable class of $\chi$ is a `finsum` over the quotient of `HermSet` by `conjSetoid`. The index $[T_c : T_c \cap K]$ is `torusWeight`: the number of cosets $tK$ with $t$ in the centralizer of $A$ in $G(F)$ and $t$ bounded. A unitary matrix has eigenvalues of absolute value one, so $t$ lies in a compact subgroup if and only if it is conjugate to an integral matrix.

The sign $\kappa$ is `kappaSign`, the class of the discriminant of $V_2$ in $F^\times / N_{E/F}(E^\times)$. The base point of the stable class is a class with $\mathrm{disc}\, V_2$ a norm. The transfer factor is the product of the sign of the resultant, `normSign`, and the cardinality $q^r$ of $\mathcal{O}_F / (R)$. The polynomials $\chi_1$ and $\chi_2$ have coefficients in $\mathcal{O}_F$, because the stable class meets the lattice only when the characteristic polynomial is integral.

The statement differs from the textbook form in these ways.

* It is for the Lie algebra, not for the group. By the reductions of Waldspurger and Hales, the Lie algebra form implies the group form for large $p$.
* It is for unitary groups and the endoscopic groups $U(n_1) \times U(n_2)$, not for all reductive groups. This is the case of Laumon and Ngô.
* It asks for the identity for all $p$ larger than a bound $p_0(n_1, n_2)$. Laumon and Ngô prove it in equal characteristic for $p > n$. Waldspurger, and later Cluckers, Hales and Loeser, transfer it to mixed characteristic for $p$ large. So the statement with a bound is the known theorem in both characteristics.
* It uses the measures with $\mathrm{vol}(K) = \mathrm{vol}(T_c) = 1$ and the unnormalized orbital integrals. With the normalized integrals $|D(A)|^{1/2} O_A$ the transfer factor is the sign $\eta(R)$ alone, because $|D_G(A)| = |D_H(A)| \, |R|_F^2$.

## References

* G. Laumon and B. C. Ngô, Le lemme fondamental pour les groupes unitaires, Ann. of Math. 168 (2008).
* B. C. Ngô, Le lemme fondamental pour les algèbres de Lie, Publ. Math. IHÉS 111 (2010).
* J.-L. Waldspurger, Le lemme fondamental implique le transfert, Compositio Math. 105 (1997).
* J.-L. Waldspurger, Endoscopie et changement de caractéristique, J. Inst. Math. Jussieu 5 (2006).
* R. Langlands and D. Shelstad, On the definition of transfer factors, Math. Ann. 278 (1987).
* R. Cluckers, T. Hales and F. Loeser, Transfer principle for the fundamental lemma, in On the stabilization of the trace formula, International Press (2011).
* T. Hales, A statement of the fundamental lemma, in Harmonic analysis, the trace formula and Shimura varieties, Clay Math. Proc. 4 (2005).
-/

namespace Langlands

open ValuativeRel IsLocalRing Polynomial

universe u

namespace UnitaryLie

variable {F : Type u} [Field F] {E : Type u} [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ)

/-- The adjoint $X^* = {}^t\sigma(X)$ of a matrix $X$ with entries in $E$ for the hermitian form $h(x, y) = \sum_l x_l \sigma(y_l)$ on $E^n$. It satisfies $h(Xx, y) = h(x, X^* y)$. -/
def adjoint (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (X.map σ).transpose

variable {σ n} in
/-- The adjoint reverses products: $(XY)^* = Y^* X^*$. -/
theorem adjoint_mul (X Y : Matrix (Fin n) (Fin n) E) :
    adjoint σ n (X * Y) = adjoint σ n Y * adjoint σ n X := by
  simp only [adjoint, Matrix.map_mul, Matrix.transpose_mul]

variable {σ n} in
/-- The adjoint of the identity matrix is the identity matrix. -/
theorem adjoint_one : adjoint σ n 1 = 1 := by
  simp [adjoint]

/-- The unitary group $U(n)(F) = \{ g \in GL_n(E) : g^* g = 1 \}$ of the hermitian form $h(x, y) = \sum_l x_l \sigma(y_l)$ on $E^n$. -/
def unitaryGroup : Subgroup (GL (Fin n) E) where
  carrier := {g | adjoint σ n g * g = 1}
  one_mem' := by simp [adjoint_one]
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, adjoint_mul] at *
    rw [mul_assoc, ← mul_assoc (adjoint σ n g), hg, one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    have h : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = adjoint σ n g := by
      rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv hg]
    rw [h, ← adjoint_mul, ← h, Units.mul_inv, adjoint_one]

/-- A matrix $A$ is hermitian if $A^* = A$. The hermitian matrices are the space $\mathfrak{u}(n)(F)$ times a fixed element $\varepsilon \in E^\times$ with $\sigma(\varepsilon) = -\varepsilon$. -/
def IsHermitian (A : Matrix (Fin n) (Fin n) E) : Prop :=
  adjoint σ n A = A

/-- An element $a$ of $E$ is a norm if $a = z \sigma(z)$ for some $z \in E^\times$. For $a \in F^\times$ this says that $a$ lies in the subgroup $N_{E/F}(E^\times)$ of index two in $F^\times$. -/
def IsNormFrom (a : E) : Prop :=
  ∃ z : E, z ≠ 0 ∧ a = z * σ z

/-- The sign $\eta(a) \in \{1, -1\}$ of an element $a$, which is $1$ when $a$ is a norm from $E^\times$ and $-1$ otherwise. For $a \in F^\times$ this is the quadratic character $\eta_{E/F}$ of local class field theory. -/
noncomputable def normSign (a : E) : ℤ := by
  classical exact if IsNormFrom σ a then 1 else -1

/-- The Gram matrix $(h(b_i, b_j))_{i,j}$ of a family $b_1, \dots, b_m$ of vectors of $E^n$ for the hermitian form $h(x, y) = \sum_l x_l \sigma(y_l)$. -/
def gram {m : ℕ} (b : Fin m → Fin n → E) : Matrix (Fin m) (Fin m) E :=
  Matrix.of fun i j => ∑ l, b i l * σ (b j l)

variable (F) in
/-- The extension $E/F$ is inert if the maximal ideal of $\mathcal{O}_F$ generates a prime ideal of the integral closure $\mathcal{O}_E$ of $\mathcal{O}_F$ in $E$. For a quadratic extension this says that $E/F$ is unramified. -/
def IsInert [ValuativeRel F] : Prop :=
  ((maximalIdeal 𝒪[F]).map (algebraMap 𝒪[F] (integralClosure 𝒪[F] E))).IsPrime

variable [ValuativeRel F]

variable (F) in
/-- A matrix with entries in $E$ is integral if all its entries are in $\mathcal{O}_E$, the integral closure of $\mathcal{O}_F$ in $E$. -/
def IsIntegralMatrix (A : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, A i j ∈ integralClosure 𝒪[F] E

variable (F) in
/-- An element $t$ of $GL_n(E)$ is bounded if it is conjugate in $GL_n(E)$ to an integral matrix. For a unitary $t$ the eigenvalues are units, so this says that $t$ lies in a compact subgroup of $GL_n(E)$. -/
def IsBounded (t : GL (Fin n) E) : Prop :=
  ∃ g : GL (Fin n) E,
    IsIntegralMatrix F n (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      (t : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E))

/-- The hyperspecial maximal compact subgroup $K = U(n)(\mathcal{O}_F)$ of the unitary group: the unitary matrices with integral entries. The inverse of such a matrix is its adjoint, so it is integral too. -/
def integralUnitaryGroup : Subgroup (GL (Fin n) E) where
  carrier := {g | g ∈ unitaryGroup σ n ∧ IsIntegralMatrix F n (g : Matrix (Fin n) (Fin n) E)}
  one_mem' := by
    refine ⟨one_mem _, fun i j => ?_⟩
    by_cases h : i = j
    · simp [h]
    · simp [Matrix.one_apply_ne h]
  mul_mem' {g h} hg hh := by
    refine ⟨mul_mem hg.1 hh.1, fun i j => ?_⟩
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hg.2 i k) (hh.2 k j)
  inv_mem' {g} hg := by
    refine ⟨inv_mem hg.1, fun i j => ?_⟩
    have h : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = adjoint σ n g := by
      rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv hg.1]
    rw [h]
    have hx := hg.2 j i
    rw [mem_integralClosure_iff] at hx ⊢
    exact hx.map ((σ : E →ₐ[F] E).restrictScalars 𝒪[F])

/-- The set of integral hermitian matrices $A \in \mathfrak{u}(n)(\mathcal{O}_F)$ with characteristic polynomial $\chi$. When $\chi$ is separable this is the set of the elements of the stable class of $\chi$ in $\mathfrak{u}(n)(F)$ that lie in the lattice $\mathfrak{u}(n)(\mathcal{O}_F)$. -/
def HermSet (χ : 𝒪[F][X]) : Type u :=
  {A : Matrix (Fin n) (Fin n) E // IsHermitian σ n A ∧ IsIntegralMatrix F n A ∧
    A.charpoly = χ.map (algebraMap 𝒪[F] E)}

/-- Conjugation by the compact group $K = U(n)(\mathcal{O}_F)$ on the integral hermitian matrices with characteristic polynomial $\chi$: $A \sim B$ if $B = k A k^{-1}$ for some $k \in K$. -/
def conjSetoid (χ : 𝒪[F][X]) : Setoid (HermSet σ n χ) where
  r A B := ∃ k ∈ integralUnitaryGroup σ n,
    B.1 = (k : Matrix (Fin n) (Fin n) E) * A.1 * ((k⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  iseqv := {
    refl A := ⟨1, one_mem _, by simp⟩
    symm := fun ⟨k, hk, h⟩ => ⟨k⁻¹, inv_mem hk, by rw [h]; simp [mul_assoc]⟩
    trans := fun ⟨k, hk, h⟩ ⟨l, hl, h'⟩ => ⟨l * k, mul_mem hl hk, by rw [h', h]; simp [mul_assoc]⟩ }

/-- The index $[T_c : T_c \cap K]$ for a hermitian matrix $A$. Here $T$ is the centralizer of $A$ in $U(n)(F)$, which is a torus when $A$ is regular semisimple, $T_c$ is its maximal compact subgroup and $K = U(n)(\mathcal{O}_F)$. The index is the number of cosets $tK$ with $t \in T_c$. It is the inverse of the volume of $T \cap K$ when $T_c$ has volume one. -/
noncomputable def torusWeight (A : Matrix (Fin n) (Fin n) E) : ℕ :=
  Nat.card ((fun t : unitaryGroup σ n =>
      (QuotientGroup.mk t : unitaryGroup σ n ⧸ (integralUnitaryGroup σ n).subgroupOf (unitaryGroup σ n))) ''
    {t | ((t : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * A = A * (t : GL (Fin n) E) ∧
      IsBounded F n (t : GL (Fin n) E)})

/-- The kernel $V_2$ of $\chi_2(A)$ has a basis $b$ whose Gram determinant $\det(h(b_i, b_j))$ is a norm from $E^\times$. A change of basis multiplies the Gram determinant by a norm, so this is a condition on the hermitian space $V_2$: its discriminant is trivial in $F^\times / N_{E/F}(E^\times)$. -/
def IsSplitKernel (χ₂ : 𝒪[F][X]) (A : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ b : Fin χ₂.natDegree → Fin n → E, LinearIndependent E b ∧
    (∀ i, (aeval A χ₂).mulVec (b i) = 0) ∧ IsNormFrom σ (gram σ n b).det

/-- The sign $\kappa(A) \in \{1, -1\}$ of an integral hermitian matrix $A$ with characteristic polynomial $\chi_1 \chi_2$. It is $1$ if the discriminant of the hermitian space $V_2 = \ker \chi_2(A)$ is a norm and $-1$ otherwise. This is the value of the endoscopic character $\kappa$ of $H = U(n_1) \times U(n_2)$ at the invariant of the rational class of $A$ in its stable class. -/
noncomputable def kappaSign (χ₂ : 𝒪[F][X]) (A : Matrix (Fin n) (Fin n) E) : ℤ := by
  classical exact if IsSplitKernel σ n χ₂ A then 1 else -1

/-- The stable orbital integral $SO_\chi(1_{\mathfrak{u}(n)(\mathcal{O}_F)})$ of the unit of the lattice of integral hermitian matrices at the regular semisimple stable class of characteristic polynomial $\chi$. It is the sum of $[T_c : T_c \cap K]$ over the $K$-classes of integral hermitian matrices with characteristic polynomial $\chi$. With $\mathrm{vol}(K) = 1$ and $\mathrm{vol}(T_c) = 1$ this is the integral $\sum_{X'} \int_{T_{X'}(F) \backslash U(n)(F)} 1_{\mathfrak{u}(n)(\mathcal{O}_F)}(g^{-1} X' g) \, dg$ over the rational classes $X'$ in the stable class. -/
noncomputable def stableOrbitalIntegral (χ : 𝒪[F][X]) : ℕ :=
  ∑ᶠ c : Quotient (conjSetoid σ n χ), torusWeight σ n c.out.1

/-- The $\kappa$-orbital integral $O^\kappa_{\chi_1 \chi_2}(1_{\mathfrak{u}(n)(\mathcal{O}_F)})$ for the endoscopic group $H = U(n_1) \times U(n_2)$. It is the sum of $\kappa(A) [T_c : T_c \cap K]$ over the $K$-classes of integral hermitian matrices $A$ with characteristic polynomial $\chi_1 \chi_2$. -/
noncomputable def kappaOrbitalIntegral (χ₁ χ₂ : 𝒪[F][X]) : ℤ :=
  ∑ᶠ c : Quotient (conjSetoid σ n (χ₁ * χ₂)), kappaSign σ n χ₂ c.out.1 * torusWeight σ n c.out.1

end UnitaryLie

open UnitaryLie in
/-- The fundamental lemma of Laumon and Ngô for the Lie algebras of unitary groups.

For each pair $(n_1, n_2)$ there is a bound $p_0$ with this property. Let $F$ be a nonarchimedean local field with residue characteristic $p > p_0$, let $E/F$ be the unramified quadratic extension with Galois involution $\sigma$, and let $n = n_1 + n_2$. Let $\chi_1$ and $\chi_2$ be monic polynomials over $\mathcal{O}_F$ of degrees $n_1$ and $n_2$ with $\chi_1 \chi_2$ separable over $F$, and let $R = \mathrm{Res}(\chi_1, \chi_2)$. Then
$$O^\kappa_{\chi_1 \chi_2}(1_{\mathfrak{u}(n)(\mathcal{O}_F)}) = \eta(R) \, |\mathcal{O}_F / (R)| \, SO_{\chi_1}(1_{\mathfrak{u}(n_1)(\mathcal{O}_F)}) \, SO_{\chi_2}(1_{\mathfrak{u}(n_2)(\mathcal{O}_F)}).$$
The orbital integrals are the lattice sums of `kappaOrbitalIntegral` and `stableOrbitalIntegral`, with $\mathrm{vol}(K) = \mathrm{vol}(T_c) = 1$. The factor $\eta(R) \, |\mathcal{O}_F / (R)| = (-q)^{v(R)}$ is the transfer factor. In equal characteristic the theorem holds for $p > n$. In mixed characteristic the known proofs need $p$ large, so the statement asks only for some bound $p_0$. -/
def FundamentalLemma : Prop :=
  ∀ n₁ n₂ : ℕ, ∃ p₀ : ℕ, ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type u) [Field E] [Algebra F E] (σ : E ≃ₐ[F] E),
    Module.finrank F E = 2 → IsInert F (E := E) → σ ≠ AlgEquiv.refl →
    p₀ < ringChar (ResidueField 𝒪[F]) →
    ∀ χ₁ χ₂ : 𝒪[F][X], χ₁.Monic → χ₂.Monic → χ₁.natDegree = n₁ → χ₂.natDegree = n₂ →
      ((χ₁ * χ₂).map (algebraMap 𝒪[F] F)).Separable →
      kappaOrbitalIntegral σ (n₁ + n₂) χ₁ χ₂ =
        normSign σ (algebraMap 𝒪[F] E (resultant χ₁ χ₂)) *
          Nat.card (𝒪[F] ⧸ Ideal.span {resultant χ₁ χ₂}) *
          stableOrbitalIntegral σ n₁ χ₁ * stableOrbitalIntegral σ n₂ χ₂

namespace UnitaryLie

section Sanity
variable {F : Type u} [Field F] {E : Type u} [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) [ValuativeRel F]

omit [ValuativeRel F] in
/-- The unit $1$ is a norm, so its sign is $1$. -/
theorem normSign_one : normSign σ 1 = 1 := by
  unfold normSign
  split_ifs with h
  · rfl
  · exact absurd ⟨1, one_ne_zero, by simp⟩ h

/-- For $\chi_2 = 1$ the space $V_2$ is zero, its Gram determinant is $1$, and the sign $\kappa$ is $1$. -/
theorem kappaSign_one (n : ℕ) (A : Matrix (Fin n) (Fin n) E) :
    kappaSign σ n (1 : 𝒪[F][X]) A = 1 := by
  have h0 : IsEmpty (Fin (1 : 𝒪[F][X]).natDegree) := by
    rw [natDegree_one]
    infer_instance
  unfold kappaSign
  split_ifs with h
  · rfl
  · exact absurd ⟨isEmptyElim, linearIndependent_empty_type, fun i => isEmptyElim i, 1, one_ne_zero,
      by simp [Matrix.det_isEmpty]⟩ h

/-- For $n = 0$ the unitary group is trivial, so the index $[T_c : T_c \cap K]$ is $1$. -/
theorem torusWeight_zero (A : Matrix (Fin 0) (Fin 0) E) : torusWeight σ 0 A = 1 := by
  have : Subsingleton (GL (Fin 0) E) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  unfold torusWeight
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨_, t, _, ht⟩ ⟨_, s, _, hs⟩ => by subst ht hs; rw [Subsingleton.elim t s]⟩,
    ⟨⟨QuotientGroup.mk 1, 1, ⟨by simp, 1, fun i => i.elim0⟩, rfl⟩⟩⟩

/-- For $n = 0$ there is one hermitian matrix, the empty matrix, so the stable orbital integral of $U(0)$ is $1$. -/
theorem stableOrbitalIntegral_zero : stableOrbitalIntegral σ 0 (1 : 𝒪[F][X]) = 1 := by
  unfold stableOrbitalIntegral
  simp only [torusWeight_zero]
  have : Unique (Quotient (conjSetoid σ 0 (1 : 𝒪[F][X]))) := by
    refine ⟨⟨Quotient.mk _ ⟨0, ?_, fun i => i.elim0, ?_⟩⟩, fun c => ?_⟩
    · ext i; exact i.elim0
    · simp [Matrix.charpoly_isEmpty]
    · induction c using Quotient.inductionOn with
      | h A => exact Quotient.sound ⟨1, one_mem _, by ext i; exact i.elim0⟩
  rw [finsum_unique]

/-- The fundamental lemma holds for $n_2 = 0$, that is for $\chi_2 = 1$ and the trivial endoscopic group $H = U(n) \times U(0)$. Then $\kappa$ is trivial, the resultant is $1$, and the two sides are both the stable orbital integral of $U(n)$. -/
theorem fundamentalLemma_trivial (n : ℕ) (χ : 𝒪[F][X]) :
    kappaOrbitalIntegral σ (n + 0) χ 1 =
      normSign σ (algebraMap 𝒪[F] E (resultant χ 1)) *
        Nat.card (𝒪[F] ⧸ Ideal.span {resultant χ 1}) *
        stableOrbitalIntegral σ n χ * stableOrbitalIntegral σ 0 1 := by
  simp only [resultant_one_right, pow_zero, natDegree_one, map_one, normSign_one,
    Ideal.span_singleton_one, stableOrbitalIntegral_zero, Nat.add_zero]
  rw [Nat.card_eq_one_iff_unique.2 ⟨Submodule.Quotient.subsingleton_iff.2 rfl, inferInstance⟩]
  unfold kappaOrbitalIntegral stableOrbitalIntegral
  rw [mul_one χ]
  simp only [kappaSign_one, one_mul, Nat.cast_one, mul_one]
  exact ((Nat.castAddMonoidHom ℤ).map_finsum_of_injective Nat.cast_injective _).symm

end Sanity

end UnitaryLie

end Langlands
