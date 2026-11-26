/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.TorusInduced

/-!
# The local Langlands correspondence for tori

Let $K$ be a nonarchimedean local field and let $T$ be a torus over $K$. The torus is given by its character lattice $X = X^*(T)$, a free $\mathbb{Z}$-module of finite rank with a continuous action of $\mathrm{Gal}(\bar K / K)$. The action factors through $\mathrm{Gal}(L/K)$ for a finite Galois extension $L$ of $K$, a splitting field of $T$. Langlands proved that there is a natural isomorphism $\mathrm{Hom}_{cts}(T(K), \mathbb{C}^\times) \cong H^1(W_K, \hat T)$, where $\hat T = X \otimes \mathbb{C}^\times$ is the dual torus with the action of $W_K$ through $\mathrm{Gal}(L/K)$.

This file states the theorem for each torus. The split case is `Langlands.LocalLanglandsTorusSplit` and the induced case is `Langlands.LocalLanglandsTorusInduced`. The statement of this file contains both cases as conditions.

## Main definitions

* `Langlands.TorusGeneral.matPow`: for a matrix $B \in M_{\iota' \times \iota}(\mathbb{Z})$ and a commutative group $M$, the homomorphism $M^\iota \to M^{\iota'}$, $z \mapsto (\prod_j z_j^{B_{ij}})_i$. This is the map $X \otimes M \to X' \otimes M$ of the linear map $X = \mathbb{Z}^\iota \to X' = \mathbb{Z}^{\iota'}$ with matrix $B$.
* `Langlands.TorusGeneral.torusPoints`: the group $T(K)$ of a torus with lattice $X = \mathbb{Z}^\iota$ and action $A : \mathrm{Gal}(L/K) \to GL_\iota(\mathbb{Z})$. It is the group $\mathrm{Hom}_{\mathrm{Gal}(L/K)}(X, L^\times)$ of the equivariant homomorphisms, written as the subgroup of the $t \in (L^\times)^\iota$ with $\sigma(t_j) = \prod_i t_i^{A(\sigma)_{ij}}$ for each $\sigma$ and $j$.
* `Langlands.TorusGeneral.DualTorus`: the dual torus $\hat T = X \otimes \mathbb{C}^\times = (\mathbb{C}^\times)^\iota$, with the action $w \cdot z = $ `matPow` $A(\bar w)\, z$ of $W_K$, where $\bar w$ is the image of $w$ in $\mathrm{Gal}(L/K)$.
* `Langlands.TorusGeneral.TorusFamily`: a family of group isomorphisms $\mathrm{Hom}_{cts}(T(K), \mathbb{C}^\times) \cong H^1(W_K, \hat T)$, one for each lattice with an action of $\mathrm{Gal}(L/K)$.
* `Langlands.TorusGeneral.IsNaturalTorusFamily`: the family is functorial for the equivariant maps of lattices.
* `Langlands.TorusGeneral.IsSplitCompatible`: for the trivial action, the family is the correspondence `Langlands.TorusCorrespond` of the split case.
* `Langlands.TorusGeneral.IsInducedCompatible`: for the permutation lattice of $\mathrm{Res}_{E/K} \mathbb{G}_m$, $K \subseteq E \subseteq L$, the family is the correspondence of the induced case, through Shapiro's lemma.
* `Langlands.LocalLanglandsTorus`: for each finite Galois extension $L$ of $K$, there is a family with these three properties.

## Main results

* `Langlands.TorusGeneral.matPow_one` and `Langlands.TorusGeneral.matPow_mul`: the map `matPow` is a functor from matrices to homomorphisms.
* `Langlands.TorusGeneral.smul_eq_of_trivial`: for the trivial action, $W_K$ acts trivially on $\hat T$, so $H^1(W_K, \hat T)$ is the group of continuous homomorphisms $W_K \to (\mathbb{C}^\times)^\iota$, as in the split case.
* `Langlands.TorusGeneral.mem_torusPoints_one`: for the trivial action, $T(K)$ is the group of the $t \in (L^\times)^\iota$ that are fixed by $\mathrm{Gal}(L/K)$, that is $(K^\times)^\iota$.

## Implementation notes

The lattice is $\mathbb{Z}^\iota$ for a finite type $\iota$, and the action is a homomorphism $A : \mathrm{Gal}(L/K) \to GL_\iota(\mathbb{Z})$, where $A(\sigma)$ is the matrix of $\sigma$ in the basis $(e_i)$: $\sigma e_j = \sum_i A(\sigma)_{ij} e_i$. A point $f \in T(L) = \mathrm{Hom}(X, L^\times)$ is the vector $t_i = f(e_i)$. The group $\mathrm{Gal}(L/K)$ acts on $T(L)$ by $(\sigma f)(x) = \sigma(f(\sigma^{-1} x))$, so $f$ is fixed if and only if $f(\sigma e_j) = \sigma(f(e_j))$. This is the condition of `torusPoints`. The group $T(K)$ has the topology of a subspace of $(L^\times)^\iota$, where $L$ has the spectral norm over $K$.

An element $\sum_j e_j \otimes z_j$ of $X \otimes \mathbb{C}^\times$ is the vector $z$. Then $\sigma (\sum_j e_j \otimes z_j) = \sum_i e_i \otimes \prod_j z_j^{A(\sigma)_{ij}}$, which is `matPow` $A(\sigma)\, z$. The topology of $\hat T$ is the product topology. The cohomology group $H^1(W_K, \hat T)$ is `Langlands.Shapiro.H1`: continuous one-cocycles modulo coboundaries.

An equivariant linear map $X \to X'$ with matrix $B$, so that $B A(\sigma) = A'(\sigma) B$, is a morphism of tori $T' \to T$. On points it is $t' \mapsto$ `matPow` $B^{\mathsf T} t'$, and on dual tori it is `matPow` $B : \hat T \to \hat T'$. The condition `IsNaturalTorusFamily` says that the square of the two maps commutes: if $\chi' = \chi \circ (T'(K) \to T(K))$, then the class of $\chi'$ is the image of the class of $\chi$.

The conditions are stated as relations, as in `Langlands.TorusCorrespond`. In the induced case the condition does not construct the isomorphism $T(K) \cong E^\times$. It says that $\chi(t) = \chi_E(x)$ when $x = t_{\tau_0}$, where $\tau_0$ is the inclusion $E \to L$, and that the cocycle $z$ of the class of $\chi$ has $z(w)_{\tau_0} = \chi_E(x)$ for $w \in W_E$ with $[w] = \mathrm{rec}_E(x)$. The coordinate $z(w)_{\tau_0}$ for $w \in W_E$ is the image of the class of $z$ under Shapiro's isomorphism, since $W_E$ fixes the coordinate $\tau_0$ of $\hat T$.

The bijection is characterized, as decided in 6.2.3 of the spec. A theorem of Langlands, in the form of Yu, says that a natural family that agrees with local class field theory on the induced tori is unique, because each lattice is a quotient of a permutation lattice. The split condition follows from the induced condition for $E = K$ and from naturality for the projections $\mathbb{Z}^n \to \mathbb{Z}$, but it is kept for clarity.

The splitting field $L$ is fixed in the statement. A torus that $L$ splits is also split by each larger field $L'$, and the groups $T(K)$ for $L$ and $L'$ are the same. The compatibility of the families for $L$ and $L'$ is not part of the statement. The lattices are indexed by finite types in `Type`, which is no restriction, since each lattice is isomorphic to some $\mathbb{Z}^n$.

This is a full statement, not a shape.

## References

* R. P. Langlands, Representations of abelian algebraic groups, Pacific J. Math. 181 (1997), a preprint of 1968.
* J.-K. Yu, On the local Langlands correspondence for tori, in Ottawa lectures on admissible representations of reductive p-adic groups, Fields Inst. Monogr. 26 (2009).
* J. Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, part 2, 1979, section 9.
* A. Borel, Automorphic L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979, section 9.
-/

namespace Langlands

universe u

open WeilGroup WeilGroup.FiniteExt

namespace TorusGeneral

set_option linter.unusedSectionVars false

section MatPow

variable {M : Type*} [CommGroup M] {ι ι' ι'' : Type*} [Fintype ι]

omit [Fintype ι] in
/-- A power with exponent a finite sum is the product of the powers. -/
theorem zpow_finsetSum {κ : Type*} (x : M) (s : Finset κ) (f : κ → ℤ) :
    x ^ (∑ k ∈ s, f k) = ∏ k ∈ s, x ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

/-- The homomorphism $M^\iota \to M^{\iota'}$, $z \mapsto (\prod_j z_j^{B_{ij}})_i$, of a matrix $B \in M_{\iota' \times \iota}(\mathbb{Z})$. It is the map $X \otimes M \to X' \otimes M$ of the linear map $\mathbb{Z}^\iota \to \mathbb{Z}^{\iota'}$ with matrix $B$. -/
def matPow (B : Matrix ι' ι ℤ) : (ι → M) →* (ι' → M) where
  toFun z i := ∏ j, z j ^ B i j
  map_one' := by
    funext i
    simp
  map_mul' z z' := by
    funext i
    simp [mul_zpow, Finset.prod_mul_distrib]

theorem matPow_apply (B : Matrix ι' ι ℤ) (z : ι → M) (i : ι') :
    matPow B z i = ∏ j, z j ^ B i j :=
  rfl

/-- The identity matrix gives the identity map. -/
theorem matPow_one [DecidableEq ι] (z : ι → M) : matPow (1 : Matrix ι ι ℤ) z = z := by
  funext i
  rw [matPow_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The map `matPow` takes a product of matrices to the composite: `matPow (A * B) = matPow A ∘ matPow B`. -/
theorem matPow_mul [Fintype ι'] (A : Matrix ι'' ι' ℤ) (B : Matrix ι' ι ℤ) (z : ι → M) :
    matPow (A * B) z = matPow A (matPow B z) := by
  funext i
  simp only [matPow_apply, Matrix.mul_apply]
  simp_rw [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_finsetSum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

end MatPow

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L]

section Points

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The action $t \mapsto (\sigma(t_i))_i$ of $\sigma \in \mathrm{Gal}(L/K)$ on $(L^\times)^\iota$. -/
noncomputable def galMap (σ : Gal(L/K)) : (ι → Lˣ) →* (ι → Lˣ) where
  toFun t i := Units.map (σ : L →* L) (t i)
  map_one' := by
    funext i
    simp
  map_mul' t t' := by
    funext i
    simp

/-- The group $T(K) = \mathrm{Hom}_{\mathrm{Gal}(L/K)}(X, L^\times)$ of the torus with lattice $X = \mathbb{Z}^\iota$ and action $A$: the $t \in (L^\times)^\iota$ with $\sigma(t_j) = \prod_i t_i^{A(\sigma)_{ij}}$ for each $\sigma \in \mathrm{Gal}(L/K)$ and each $j$. -/
noncomputable def torusPoints (A : Gal(L/K) →* GL ι ℤ) : Subgroup (ι → Lˣ) :=
  ⨅ σ : Gal(L/K), MonoidHom.eqLocus (galMap K L σ) (matPow (A σ : Matrix ι ι ℤ).transpose)

theorem mem_torusPoints {A : Gal(L/K) →* GL ι ℤ} {t : ι → Lˣ} :
    t ∈ torusPoints K L A ↔
      ∀ σ : Gal(L/K), ∀ j, Units.map (σ : L →* L) (t j) = ∏ i, t i ^ (A σ : Matrix ι ι ℤ) i j := by
  rw [torusPoints, Subgroup.mem_iInf]
  refine forall_congr' fun σ => ?_
  change galMap K L σ t = matPow _ t ↔ _
  rw [funext_iff]
  rfl

/-- For the trivial action, $T(K)$ is the group of the $t \in (L^\times)^\iota$ that are fixed by $\mathrm{Gal}(L/K)$. -/
theorem mem_torusPoints_one {t : ι → Lˣ} :
    t ∈ torusPoints K L (1 : Gal(L/K) →* GL ι ℤ) ↔
      ∀ σ : Gal(L/K), ∀ j, Units.map (σ : L →* L) (t j) = t j := by
  rw [mem_torusPoints]
  refine forall_congr' fun σ => forall_congr' fun j => ?_
  have h := congrFun (matPow_one (M := Lˣ) t) j
  rw [matPow_apply] at h
  simp only [MonoidHom.one_apply, Units.val_one]
  rw [← Matrix.transpose_one] at h
  exact Iff.of_eq (congrArg _ (by simpa [Matrix.transpose_apply] using h))

end Points

section Dual

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The dual torus $\hat T = X \otimes \mathbb{C}^\times = (\mathbb{C}^\times)^\iota$ of the torus with lattice $\mathbb{Z}^\iota$ and action $A$, with the product topology. The action of $W_K$ is the instance below. -/
@[nolint unusedArguments]
def DualTorus (_A : Gal(L/K) →* GL ι ℤ) : Type :=
  ι → ℂˣ

variable {K L}
variable (A : Gal(L/K) →* GL ι ℤ)

instance : CommGroup (DualTorus K L A) := inferInstanceAs (CommGroup (ι → ℂˣ))

noncomputable instance : TopologicalSpace (DualTorus K L A) := inferInstanceAs (TopologicalSpace (ι → ℂˣ))

instance : IsTopologicalGroup (DualTorus K L A) := inferInstanceAs (IsTopologicalGroup (ι → ℂˣ))

/-- The action of $W_K$ on $\hat T$: $w \cdot z = $ `matPow` $A(\bar w)\, z$, where $\bar w$ is the image of $w$ in $\mathrm{Gal}(L/K)$. -/
noncomputable instance : MulDistribMulAction (WeilGroup K) (DualTorus K L A) where
  smul w z := matPow (M := ℂˣ) (A (WeilGroup.restrict K L w) : Matrix ι ι ℤ) z
  one_smul z := by
    change matPow (M := ℂˣ) (A (WeilGroup.restrict K L 1) : Matrix ι ι ℤ) z = z
    rw [map_one, map_one, Units.val_one]
    exact matPow_one z
  mul_smul w w' z := by
    change matPow (M := ℂˣ) (A (WeilGroup.restrict K L (w * w')) : Matrix ι ι ℤ) z =
      matPow (A (WeilGroup.restrict K L w) : Matrix ι ι ℤ)
        (matPow (A (WeilGroup.restrict K L w') : Matrix ι ι ℤ) z)
    rw [map_mul, map_mul, Units.val_mul]
    exact matPow_mul (M := ℂˣ) _ _ (show ι → ℂˣ from z)
  smul_mul w z z' := map_mul (matPow (M := ℂˣ) _) z z'
  smul_one w := map_one (matPow (M := ℂˣ) _)

theorem smul_def (w : WeilGroup K) (z : DualTorus K L A) :
    w • z = (matPow (M := ℂˣ) (A (WeilGroup.restrict K L w) : Matrix ι ι ℤ) z : ι → ℂˣ) :=
  rfl

/-- For the trivial action, $W_K$ acts trivially on $\hat T$. Then the coboundaries are trivial and the cocycles are the continuous homomorphisms, so $H^1(W_K, \hat T) = \mathrm{Hom}_{cts}(W_K, (\mathbb{C}^\times)^\iota)$. -/
theorem smul_eq_of_trivial (w : WeilGroup K) (z : DualTorus K L (1 : Gal(L/K) →* GL ι ℤ)) :
    w • z = z := by
  rw [smul_def, MonoidHom.one_apply, Units.val_one]
  exact matPow_one z

end Dual

/-- A family of group isomorphisms $\mathrm{Hom}_{cts}(T(K), \mathbb{C}^\times) \cong H^1(W_K, \hat T)$, one for each torus with lattice $\mathbb{Z}^\iota$ and action $A$ of $\mathrm{Gal}(L/K)$. -/
abbrev TorusFamily :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Gal(L/K) →* GL ι ℤ),
    ContinuousMonoidHom (torusPoints K L A) ℂˣ ≃* Shapiro.H1 (WeilGroup K) (DualTorus K L A)

variable {K L}

/-- The family is natural. Let $B \in M_{\iota' \times \iota}(\mathbb{Z})$ with $B A(\sigma) = A'(\sigma) B$ for each $\sigma$, an equivariant map $X \to X'$ of lattices, so a morphism of tori $T' \to T$. Let $\chi$ be a character of $T(K)$ and let $\chi' = \chi \circ (T'(K) \to T(K))$, where the map is $t' \mapsto$ `matPow` $B^{\mathsf T} t'$. Let $z$ and $z'$ be cocycles of the classes of $\chi$ and $\chi'$. Then $z'$ and `matPow` $B \circ z$ differ by a coboundary. -/
def IsNaturalTorusFamily (corr : TorusFamily K L) : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (A : Gal(L/K) →* GL ι ℤ) (A' : Gal(L/K) →* GL ι' ℤ) (B : Matrix ι' ι ℤ),
    (∀ σ, B * (A σ : Matrix ι ι ℤ) = (A' σ : Matrix ι' ι' ℤ) * B) →
    ∀ (χ : ContinuousMonoidHom (torusPoints K L A) ℂˣ)
      (χ' : ContinuousMonoidHom (torusPoints K L A') ℂˣ),
      (∀ (t : torusPoints K L A) (t' : torusPoints K L A'),
        (t : ι → Lˣ) = matPow B.transpose (t' : ι' → Lˣ) → χ' t' = χ t) →
      ∀ (z : Shapiro.ContCocycle (WeilGroup K) (DualTorus K L A))
        (z' : Shapiro.ContCocycle (WeilGroup K) (DualTorus K L A')),
        (QuotientGroup.mk z : Shapiro.H1 _ _) = corr ι A χ →
        (QuotientGroup.mk z' : Shapiro.H1 _ _) = corr ι' A' χ' →
        ∃ m : DualTorus K L A', ∀ w : WeilGroup K,
          (matPow (M := ℂˣ) B (z.1 w : ι → ℂˣ) : DualTorus K L A') = z'.1 w * (w • m / m)

/-- The family agrees with the split case `Langlands.TorusCorrespond`. For the trivial action on $\mathbb{Z}^n$ and a local Artin map $\mathrm{rec}_K$, let $\chi$ be a character of $T(K)$ and let $\chi_0$ be the character of $(K^\times)^n$ with $\chi(t) = \chi_0(x)$ when $t_i = x_i$ for each $i$. If $z$ is a cocycle of the class of $\chi$, it is a continuous homomorphism $\varphi : W_K \to (\mathbb{C}^\times)^n$ by `smul_eq_of_trivial`, and then $\chi_0$ and $\varphi$ correspond in the sense of `Langlands.TorusCorrespond`. -/
def IsSplitCompatible (corr : TorusFamily K L) : Prop :=
  ∀ (n : ℕ) (rec : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K rec →
    ∀ (χ : ContinuousMonoidHom (torusPoints K L (1 : Gal(L/K) →* GL (Fin n) ℤ)) ℂˣ)
      (χ₀ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ),
      (∀ (t : torusPoints K L (1 : Gal(L/K) →* GL (Fin n) ℤ)) (x : Fin n → Kˣ),
        (∀ i, algebraMap K (AlgebraicClosure K) (x i) = (((t : Fin n → Lˣ) i : L) : AlgebraicClosure K)) →
        χ t = χ₀ x) →
      ∀ (z : Shapiro.ContCocycle (WeilGroup K) (DualTorus K L (1 : Gal(L/K) →* GL (Fin n) ℤ))),
        (QuotientGroup.mk z : Shapiro.H1 _ _) = corr (Fin n) 1 χ →
        ∀ φ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ), (∀ w, φ w = z.1 w) →
          TorusCorrespond K rec χ₀ φ

open Classical in
/-- The family agrees with the induced case `Langlands.LocalLanglandsTorusInduced`. Let $K \subseteq E \subseteq L$ and let $\mathrm{rec}_E$ be a local Artin map of $E$. The lattice of $\mathrm{Res}_{E/K} \mathbb{G}_m$ is the permutation lattice on the set of the $K$-embeddings $\tau : E \to L$, here indexed by $\iota$ through a bijection $e$, with $\sigma e_\tau = e_{\sigma \tau}$. Let $\tau_0$ be the inclusion $E \to L$. Let $\chi$ be a character of $T(K)$ and let $\chi_E$ be the character of $E^\times$ with $\chi(t) = \chi_E(x)$ when $t_{\tau_0} = x$. If $z$ is a cocycle of the class of $\chi$, then $z(w)_{\tau_0} = \chi_E(x)$ for each $w \in W_E$ and $x \in E^\times$ with $[w] = \mathrm{rec}_E(x)$ in $W_E^{ab}$. -/
def IsInducedCompatible (corr : TorusFamily K L) : Prop :=
  ∀ (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ L) [FiniteDimensional K E]
    (recE : Eˣ ≃ₜ* WeilGroup.Ab E), IsLocalArtinMap E recE →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι ≃ (E →ₐ[K] L)) (A : Gal(L/K) →* GL ι ℤ),
      (∀ σ i j, (A σ : Matrix ι ι ℤ) i j =
        if e i = (σ : L →ₐ[K] L).comp (e j) then 1 else 0) →
      ∀ (χ : ContinuousMonoidHom (torusPoints K L A) ℂˣ) (χE : ContinuousMonoidHom Eˣ ℂˣ),
        (∀ (t : torusPoints K L A) (x : Eˣ),
          ((x : E) : AlgebraicClosure K) =
            (((t : ι → Lˣ) (e.symm (IntermediateField.inclusion hE)) : L) : AlgebraicClosure K) →
          χ t = χE x) →
        ∀ z : Shapiro.ContCocycle (WeilGroup K) (DualTorus K L A),
          (QuotientGroup.mk z : Shapiro.H1 _ _) = corr ι A χ →
          ∀ (x : Eˣ) (w : WeilGroup E), (QuotientGroup.mk w : WeilGroup.Ab E) = recE x →
            (z.1 (weilHom K E w) : ι → ℂˣ) (e.symm (IntermediateField.inclusion hE)) = χE x

end TorusGeneral

open TorusGeneral

/-- **The local Langlands correspondence for tori** (Langlands). Let $K$ be a nonarchimedean local field and let $L$ be a finite Galois extension of $K$. There is a family of group isomorphisms $\mathrm{Hom}_{cts}(T(K), \mathbb{C}^\times) \cong H^1(W_K, \hat T)$, one for each torus $T$ over $K$ that $L$ splits, given by its character lattice $\mathbb{Z}^\iota$ with an action $A$ of $\mathrm{Gal}(L/K)$. The family is natural in the lattice, it is the composite with $\mathrm{rec}_K$ for the split tori, and it is the composite of Shapiro's isomorphism with $\mathrm{rec}_E$ for the induced tori $\mathrm{Res}_{E/K} \mathbb{G}_m$ with $E \subseteq L$. By the theorem of Langlands in the form of Yu, these conditions determine the family.

This is a full statement, not a shape. -/
def LocalLanglandsTorus : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L],
    ∃ corr : TorusFamily K L,
      IsNaturalTorusFamily corr ∧ IsSplitCompatible corr ∧ IsInducedCompatible corr

end Langlands
