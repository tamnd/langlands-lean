/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Groups.SplitReductive
import Mathlib.Basic.Complex.Basic

/-!
# Pinned automorphisms, L-groups and the L-group of the unitary group

This file has three parts. First, an automorphism of a crystallographic root pairing that keeps a base gives an automorphism of the Geck Lie algebra of `Langlands.Groups.Chevalley`. This automorphism permutes the generators $e_i$, $f_i$, $h_i$ as the automorphism permutes the simple roots. It acts on the adjoint Chevalley group by conjugation, and it permutes the simple root elements. The map is a group homomorphism from the automorphisms that keep the base. Second, the file defines the L-group ${}^L G = \hat G(\mathbb{C}) \rtimes \Gamma$, with $\hat G(\mathbb{C})$ the adjoint Chevalley group over $\mathbb{C}$ and $\Gamma$ acting through pinned automorphisms. It proves that in the split case the L-group is the direct product. Third, the file defines the L-group ${}^L U(n) = \mathrm{GL}_n(\mathbb{C}) \rtimes \mathrm{Gal}(E/F)$ of the quasi-split unitary group, with the involution $\theta(g) = J (g^T)^{-1} J^{-1}$. It proves that $\theta$ is a pinned involution and that $\theta$ matches the Galois action on the root datum of $\mathrm{GL}_n$.

## Main definitions

* `Langlands.Groups.Pinned.baseAut`: the subgroup of the automorphisms of a root pairing that keep a base.
* `Langlands.Groups.Pinned.pinnedAut`: the homomorphism from `baseAut b` to the automorphisms of the Geck Lie algebra.
* `Langlands.Groups.Pinned.adjointAction`, `Langlands.Groups.Pinned.elementaryAction`: the actions of `baseAut b` on the adjoint Chevalley group $G(k)$ and on the elementary subgroup $E(k)$.
* `Langlands.Groups.LGroup.dualGroupAction`, `Langlands.Groups.LGroup.PinnedLGroup`: the action of $\Gamma$ on $\hat G(\mathbb{C})$ and the L-group $\hat G(\mathbb{C}) \rtimes \Gamma$.
* `Langlands.Groups.LGroup.IsDualPinning`: the condition that a root system over $\mathbb{C}$ with an action of $\Gamma$ is the dual of a quasi-split datum.
* `Langlands.Groups.Unitary.antiDiag`: the antidiagonal matrix $J$ with the entries $J_{a, n-1-a} = (-1)^a$.
* `Langlands.Groups.Unitary.theta`: the involution $\theta(g) = J (g^T)^{-1} J^{-1}$ of $\mathrm{GL}_n(R)$.
* `Langlands.Groups.Unitary.upperBorel`: the Borel subgroup of the upper triangular matrices.
* `Langlands.Groups.Unitary.glOuter`: the outer automorphism $x \mapsto -(x \circ \mathrm{rev})$ of the root datum of $\mathrm{GL}_n$.
* `Langlands.Groups.Unitary.unitaryDatum`: the quasi-split datum of $U(n)$ for a character $\chi : \Gamma \to \mathbb{Z}/2$.
* `Langlands.Groups.Unitary.unitaryAction`, `Langlands.Groups.Unitary.UnitaryLGroup`, `Langlands.Groups.Unitary.LUnitary`: the action of $\Gamma$ on $\mathrm{GL}_n$ through $\theta$ and the L-group ${}^L U(n) = \mathrm{GL}_n \rtimes \Gamma$.

## Main results

* `Langlands.Groups.Pinned.pinnedAut_geckE`, `Langlands.Groups.Pinned.pinnedAut_geckF`, `Langlands.Groups.Pinned.pinnedAut_geckH`: the pinned automorphism of $g$ takes $e_i$, $f_i$, $h_i$ to $e_{g(i)}$, $f_{g(i)}$, $h_{g(i)}$.
* `Langlands.Groups.Pinned.adjointAction_simpleRootElement`, `Langlands.Groups.Pinned.adjointAction_negSimpleRootElement`: the action on $G(k)$ takes $x_{\pm\alpha_i}(t)$ to $x_{\pm\alpha_{g(i)}}(t)$.
* `Langlands.Groups.Pinned.adjointAction_torusHom`: the action on $G(k)$ takes the torus element $h(t)$ to $h(t \circ g^{-1})$.
* `Langlands.Groups.LGroup.pinnedLGroupEquivProd`, `Langlands.Groups.LGroup.lGroupEquivProdOfIsSplit`: in the split case the L-group is $\hat G(\mathbb{C}) \times \Gamma$.
* `Langlands.Groups.LGroup.IsDualPinning.unique`: the action of a dual pinning is unique.
* `Langlands.Groups.Unitary.coe_theta`, `Langlands.Groups.Unitary.theta_theta`: $\theta(g) = J (g^T)^{-1} J^{-1}$ and $\theta$ is an involution.
* `Langlands.Groups.Unitary.theta_torusHom`, `Langlands.Groups.Unitary.map_theta_range_torusHom`: $\theta$ keeps the diagonal torus and acts on it by the outer map.
* `Langlands.Groups.Unitary.map_theta_upperBorel`: $\theta$ keeps the upper triangular Borel subgroup.
* `Langlands.Groups.Unitary.theta_rootElement_of_mem`: $\theta(x_{i, i+1}(t)) = x_{n-2-i, n-1-i}(t)$, so $\theta$ permutes the simple root elements.
* `Langlands.Groups.Unitary.unitaryAction_torusHom`, `Langlands.Groups.Unitary.unitaryAction_rootElement`: the action on $\mathrm{GL}_n$ matches the dual action of the datum of $U(n)$ on the torus and on the simple roots.
* `Langlands.Groups.Unitary.unitaryDatum_isSplit_iff`: the datum of $U(n)$ is split if and only if $\chi$ is trivial.
* `Langlands.Groups.Unitary.torusLGroupToUnitary_injective`: the L-group of the diagonal torus of $U(n)$ embeds in ${}^L U(n)$.

## Implementation notes

Mathlib's Geck construction has no functoriality. The pinned automorphism is the reindexing of the Geck matrices by the permutation `blockEquiv g` of $b \oplus \iota$. This file proves that the reindexing takes each generator $e_i$, $f_i$, $h_i$ to the generator of the image simple root, and so it keeps the Geck Lie algebra.

Mathlib has no extension of scalars for root pairings. So this file cannot build the root system over $\mathbb{C}$ of the dual root datum of a quasi-split datum $D$. The L-group `PinnedLGroup` takes a root system $P$ over $\mathbb{C}$ with a base $b$ and a homomorphism $\rho$ from $\Gamma$ to `baseAut b`. The predicate `IsDualPinning` states that $P$, $b$ and $\rho$ are the dual of $D$: the simple roots, the Cartan integers and the permutations of the roots agree. The adjoint Chevalley group over $\mathbb{C}$ is the dual group $\hat G$ when $\hat G$ is adjoint, that is when $G$ is simply connected. The predicate `IsDualPinning` compares only the root systems. It does not check that the cocharacter lattice of $D$ is the coroot lattice, so the condition that $G$ is simply connected is not in this file.

For the unitary group the file uses a general group $\Gamma$ with a character $\chi : \Gamma \to \mathbb{Z}/2$. For $\Gamma = \mathrm{Gal}(E/F)$ the character is the isomorphism with $\mathbb{Z}/2$. For $\Gamma$ the Weil group or the absolute Galois group of $F$, the character has the kernel of $E$. The indices are $0, \dots, n-1$, so $i \mapsto n + 1 - i$ in the indices $1, \dots, n$ is $\mathrm{rev}(i) = n - 1 - i$ here.

## References

* A. Borel, Automorphic L-functions, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979, section 2.
* R. Kottwitz, Stable trace formula: cuspidal tempered terms, Duke Math. J. 51 (1984), section 1.
* M. Geck, On the construction of semisimple Lie algebras and Chevalley groups, Proc. Amer. Math. Soc. 145 (2017).
* J. Rogawski, Automorphic representations of unitary groups in three variables, Annals of Mathematics Studies 123, 1990, section 1.8.
-/

noncomputable section

namespace Langlands.Groups.Pinned

open RootPairing GeckConstruction Langlands.Groups.Chevalley Langlands.Groups.ChevalleyRoots
  Function Set

section Invariance

variable {ι k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N}

/-- An automorphism of a root pairing takes the root $\alpha_i$ to the root $\alpha_{g(i)}$: $\alpha_{g(i)} = g(\alpha_i)$. -/
theorem root_indexEquiv (g : P.Aut) (i : ι) :
    P.root (g.indexEquiv i) = g.weightEquiv (P.root i) := by
  simp [Hom.root_weightMap_apply]

/-- An automorphism commutes with the permutations of the reflections: $g(s_i(j)) = s_{g(i)}(g(j))$. -/
theorem indexEquiv_reflectionPerm (g : P.Aut) (i j : ι) :
    g.indexEquiv (P.reflectionPerm i j) = P.reflectionPerm (g.indexEquiv i) (g.indexEquiv j) := by
  apply P.root.injective
  rw [root_indexEquiv, root_reflectionPerm, root_reflectionPerm, Equiv.weightEquiv_reflection,
    root_indexEquiv]

/-- An automorphism keeps the relation $\alpha_a = \alpha_i + \alpha_j$ between roots. -/
theorem root_indexEquiv_eq_add_iff (g : P.Aut) {a i j : ι} :
    P.root (g.indexEquiv a) = P.root (g.indexEquiv i) + P.root (g.indexEquiv j) ↔
      P.root a = P.root i + P.root j := by
  simp only [root_indexEquiv, ← map_add, g.weightEquiv.injective.eq_iff]

/-- An automorphism keeps the relation $\alpha_a = \alpha_j - \alpha_i$ between roots. -/
theorem root_indexEquiv_eq_sub_iff (g : P.Aut) {a i j : ι} :
    P.root (g.indexEquiv a) = P.root (g.indexEquiv j) - P.root (g.indexEquiv i) ↔
      P.root a = P.root j - P.root i := by
  simp only [root_indexEquiv, ← map_sub, g.weightEquiv.injective.eq_iff]

/-- A weight $x$ is a root if and only if $g(x)$ is a root. -/
theorem weightEquiv_mem_range_root_iff (g : P.Aut) (x : M) :
    g.weightEquiv x ∈ range P.root ↔ x ∈ range P.root := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨g.indexEquiv.symm m, g.weightEquiv.injective ?_⟩
    rw [← root_indexEquiv, Equiv.apply_symm_apply, hm]
  · rintro ⟨m, rfl⟩
    exact ⟨g.indexEquiv m, root_indexEquiv g m⟩

/-- Two roots are linearly independent if and only if their images under an automorphism are linearly independent. -/
theorem linearIndependent_indexEquiv_iff (g : P.Aut) (i j : ι) :
    LinearIndependent k ![P.root (g.indexEquiv i), P.root (g.indexEquiv j)] ↔
      LinearIndependent k ![P.root i, P.root j] := by
  have h : ![P.root (g.indexEquiv i), P.root (g.indexEquiv j)] =
      (g.weightEquiv : M →ₗ[k] M) ∘ ![P.root i, P.root j] := by
    ext a; fin_cases a <;> simp [root_indexEquiv, -Equiv.root_indexEquiv_eq_smul]
  rw [h, LinearMap.linearIndependent_iff _ (LinearEquiv.ker _)]

variable [Finite ι] [CharZero k] [P.IsCrystallographic]

omit [Finite ι] in
/-- An automorphism keeps the integral Cartan integers: $\langle \alpha_{g(i)}, \alpha_{g(j)}^\vee \rangle = \langle \alpha_i, \alpha_j^\vee \rangle$. -/
theorem pairingIn_indexEquiv (g : P.Aut) (i j : ι) :
    P.pairingIn ℤ (g.indexEquiv i) (g.indexEquiv j) = P.pairingIn ℤ i j :=
  FaithfulSMul.algebraMap_injective ℤ k (by simp only [algebraMap_pairingIn, Hom.pairing])

/-- An automorphism keeps the top coefficient of the root string of $\alpha_j$ through $\alpha_i$. -/
theorem chainTopCoeff_indexEquiv (g : P.Aut) (i j : ι) :
    P.chainTopCoeff (g.indexEquiv i) (g.indexEquiv j) = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent k ![P.root i, P.root j]
  · have h' := (linearIndependent_indexEquiv_iff g i j).2 h
    rw [chainTopCoeff_eq_sSup h, chainTopCoeff_eq_sSup h']
    congr 1
    ext n
    simp only [mem_ofPred_eq, root_indexEquiv, ← map_nsmul, ← map_add,
      weightEquiv_mem_range_root_iff]
  · rw [chainTopCoeff_of_not_linearIndependent h,
      chainTopCoeff_of_not_linearIndependent ((linearIndependent_indexEquiv_iff g i j).not.2 h)]

/-- An automorphism keeps the bottom coefficient of the root string of $\alpha_j$ through $\alpha_i$. -/
theorem chainBotCoeff_indexEquiv (g : P.Aut) (i j : ι) :
    P.chainBotCoeff (g.indexEquiv i) (g.indexEquiv j) = P.chainBotCoeff i j := by
  by_cases h : LinearIndependent k ![P.root i, P.root j]
  · have h' := (linearIndependent_indexEquiv_iff g i j).2 h
    rw [chainBotCoeff_eq_sSup h, chainBotCoeff_eq_sSup h']
    congr 1
    ext n
    simp only [mem_ofPred_eq, root_indexEquiv, ← map_nsmul, ← map_sub,
      weightEquiv_mem_range_root_iff]
  · rw [chainBotCoeff_of_not_linearIndependent h,
      chainBotCoeff_of_not_linearIndependent ((linearIndependent_indexEquiv_iff g i j).not.2 h)]

end Invariance

section BaseAut

variable {ι k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N}

/-- The subgroup of the automorphisms of a root pairing that keep the base $b$: the permutation of the roots takes the simple roots to the simple roots. -/
def baseAut (b : P.Base) : Subgroup P.Aut where
  carrier := {g | ∀ i, g.indexEquiv i ∈ b.support ↔ i ∈ b.support}
  mul_mem' {g g'} hg hg' i := by
    change Equiv.indexHom P (g * g') i ∈ b.support ↔ _
    rw [map_mul, Equiv.Perm.mul_apply]
    exact (hg _).trans (hg' i)
  one_mem' i := by
    change Equiv.indexHom P 1 i ∈ b.support ↔ _
    rw [map_one]
    rfl
  inv_mem' {g} hg i := by
    rw [Equiv.indexEquiv_inv, ← hg]
    change Equiv.indexHom P g ((Equiv.indexHom P g)⁻¹ i) ∈ _ ↔ _
    simp

variable {b : P.Base}

/-- An automorphism keeps the base if and only if its permutation of the roots keeps the set of simple roots. -/
theorem mem_baseAut_iff {g : P.Aut} :
    g ∈ baseAut b ↔ ∀ i, g.indexEquiv i ∈ b.support ↔ i ∈ b.support := Iff.rfl

/-- The permutation of the simple roots that an automorphism which keeps the base gives. -/
def supportEquiv (g : baseAut b) : b.support ≃ b.support :=
  (g.1.indexEquiv).subtypeEquiv fun i => (g.2 i).symm

/-- The permutation of the simple roots is the restriction of the permutation of the roots. -/
@[simp] theorem coe_supportEquiv (g : baseAut b) (i : b.support) :
    (supportEquiv g i : ι) = g.1.indexEquiv i := rfl

/-- The permutation of the index set $b \oplus \iota$ of the Geck matrices: the permutation of the simple roots on the first part, and the permutation of the roots on the second part. -/
def blockEquiv (g : baseAut b) : b.support ⊕ ι ≃ b.support ⊕ ι :=
  Equiv.sumCongr (supportEquiv g) g.1.indexEquiv

/-- The permutation `blockEquiv g` on a simple root of the first part. -/
@[simp] theorem blockEquiv_inl (g : baseAut b) (i : b.support) :
    blockEquiv g (.inl i) = .inl (supportEquiv g i) := rfl

/-- The permutation `blockEquiv g` on a root of the second part. -/
@[simp] theorem blockEquiv_inr (g : baseAut b) (i : ι) :
    blockEquiv g (.inr i) = .inr (g.1.indexEquiv i) := rfl

end BaseAut

section Generators

variable {ι k M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] {b : P.Base}

omit [Fintype ι] in
/-- The Geck matrix $h_i$ is invariant: $h_{g(i)}(g(a), g(c)) = h_i(a, c)$. -/
theorem h_blockEquiv (g : baseAut b) (i : b.support) (a c : b.support ⊕ ι) :
    h (supportEquiv g i) (blockEquiv g a) (blockEquiv g c) = (h i a c : k) := by
  rcases a with a | a <;> rcases c with c | c <;>
    simp [h_def, Matrix.diagonal_apply, pairingIn_indexEquiv]

/-- The Geck matrix $e_i$ is invariant: $e_{g(i)}(g(a), g(c)) = e_i(a, c)$. -/
theorem e_blockEquiv (g : baseAut b) (i : b.support) (a c : b.support ⊕ ι) :
    e (supportEquiv g i) (blockEquiv g a) (blockEquiv g c) = (e i a c : k) := by
  let _ := P.indexNeg
  have hneg : ∀ j : ι, -(g.1.indexEquiv j) = g.1.indexEquiv (-j) := fun j =>
    (indexEquiv_reflectionPerm g.1 j j).symm
  rcases a with a | a <;> rcases c with c | c
  · simp [e]
  · simp only [e, blockEquiv_inl, blockEquiv_inr, Matrix.fromBlocks_apply₁₂, Matrix.of_apply,
      coe_supportEquiv, hneg, (supportEquiv g).injective.eq_iff, g.1.indexEquiv.injective.eq_iff]
    congr 1
  · simp only [e, blockEquiv_inl, blockEquiv_inr, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
      g.1.indexEquiv.injective.eq_iff, Base.cartanMatrix, Base.cartanMatrixIn_def,
      coe_supportEquiv, pairingIn_indexEquiv]
    congr 1
  · simp only [e, blockEquiv_inr, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, coe_supportEquiv,
      chainBotCoeff_indexEquiv]
    congr 1
    exact propext (root_indexEquiv_eq_add_iff g.1)

/-- The Geck matrix $f_i$ is invariant: $f_{g(i)}(g(a), g(c)) = f_i(a, c)$. -/
theorem f_blockEquiv (g : baseAut b) (i : b.support) (a c : b.support ⊕ ι) :
    f (supportEquiv g i) (blockEquiv g a) (blockEquiv g c) = (f i a c : k) := by
  let _ := P.indexNeg
  have hneg : ∀ j : ι, -(g.1.indexEquiv j) = g.1.indexEquiv (-j) := fun j =>
    (indexEquiv_reflectionPerm g.1 j j).symm
  rcases a with a | a <;> rcases c with c | c
  · simp [f]
  · simp only [f, blockEquiv_inl, blockEquiv_inr, Matrix.fromBlocks_apply₁₂, Matrix.of_apply,
      coe_supportEquiv, (supportEquiv g).injective.eq_iff, g.1.indexEquiv.injective.eq_iff]
    congr 1
  · simp only [f, blockEquiv_inl, blockEquiv_inr, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
      hneg, g.1.indexEquiv.injective.eq_iff, Base.cartanMatrix, Base.cartanMatrixIn_def,
      coe_supportEquiv, pairingIn_indexEquiv]
    congr 1
  · simp only [f, blockEquiv_inr, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, coe_supportEquiv,
      chainTopCoeff_indexEquiv]
    congr 1
    exact propext (root_indexEquiv_eq_sub_iff g.1)

omit [Fintype ι] in
/-- Reindexing by `blockEquiv g` takes the Geck matrix $h_i$ to $h_{g(i)}$. -/
theorem reindex_h (g : baseAut b) (i : b.support) :
    Matrix.reindex (blockEquiv g) (blockEquiv g) (h i) = (h (supportEquiv g i) : Matrix _ _ k) := by
  ext a c
  obtain ⟨a, rfl⟩ := (blockEquiv g).surjective a
  obtain ⟨c, rfl⟩ := (blockEquiv g).surjective c
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    h_blockEquiv]

/-- Reindexing by `blockEquiv g` takes the Geck matrix $e_i$ to $e_{g(i)}$. -/
theorem reindex_e (g : baseAut b) (i : b.support) :
    Matrix.reindex (blockEquiv g) (blockEquiv g) (e i) = (e (supportEquiv g i) : Matrix _ _ k) := by
  ext a c
  obtain ⟨a, rfl⟩ := (blockEquiv g).surjective a
  obtain ⟨c, rfl⟩ := (blockEquiv g).surjective c
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    e_blockEquiv]

/-- Reindexing by `blockEquiv g` takes the Geck matrix $f_i$ to $f_{g(i)}$. -/
theorem reindex_f (g : baseAut b) (i : b.support) :
    Matrix.reindex (blockEquiv g) (blockEquiv g) (f i) = (f (supportEquiv g i) : Matrix _ _ k) := by
  ext a c
  obtain ⟨a, rfl⟩ := (blockEquiv g).surjective a
  obtain ⟨c, rfl⟩ := (blockEquiv g).surjective c
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    f_blockEquiv]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Reindexing by `blockEquiv g` takes the Geck Lie algebra to itself, because it permutes its generators. -/
theorem map_reindex_lieAlgebra (g : baseAut b) :
    (lieAlgebra b).map (Matrix.reindexLieEquiv (R := k) (blockEquiv g) : _ →ₗ⁅k⁆ _) =
      lieAlgebra b := by
  rw [lieAlgebra, LieSubalgebra.map_lieSpan]
  congr 1
  rw [image_union, image_union, ← range_comp, ← range_comp, ← range_comp]
  have h1 : (Matrix.reindexLieEquiv (R := k) (blockEquiv g) : _ →ₗ⁅k⁆ _) ∘ h =
      h ∘ supportEquiv g := funext (reindex_h g)
  have h2 : (Matrix.reindexLieEquiv (R := k) (blockEquiv g) : _ →ₗ⁅k⁆ _) ∘ e =
      e ∘ supportEquiv g := funext (reindex_e g)
  have h3 : (Matrix.reindexLieEquiv (R := k) (blockEquiv g) : _ →ₗ⁅k⁆ _) ∘ f =
      f ∘ supportEquiv g := funext (reindex_f g)
  rw [h1, h2, h3, EquivLike.range_comp, EquivLike.range_comp, EquivLike.range_comp]

/-- The automorphism of the Geck Lie algebra that an automorphism $g$ of the root pairing which keeps the base gives. It is the restriction of the reindexing of the matrices by `blockEquiv g`. -/
def pinnedAutEquiv (g : baseAut b) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  (Matrix.reindexLieEquiv (blockEquiv g)).ofSubalgebras _ _ (map_reindex_lieAlgebra g)

/-- The automorphism `pinnedAutEquiv g` reindexes the matrices by `blockEquiv g`. -/
theorem coe_pinnedAutEquiv_apply (g : baseAut b) (x : lieAlgebra b) :
    (pinnedAutEquiv g x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) =
      Matrix.reindex (blockEquiv g) (blockEquiv g) x := rfl

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] in
/-- The permutation `blockEquiv` of a product is the composition of the permutations. -/
theorem blockEquiv_mul (g g' : baseAut b) :
    blockEquiv (g * g') = (blockEquiv g').trans (blockEquiv g) := by
  ext (a | a) <;> rfl

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] in
/-- The permutation `blockEquiv` of the identity is the identity. -/
theorem blockEquiv_one : blockEquiv (1 : baseAut b) = Equiv.refl _ := by
  ext (a | a) <;> rfl

variable (b) in
/-- The pinned automorphism group action: the group homomorphism from the automorphisms of the root pairing that keep the base to the automorphisms of the Geck Lie algebra. -/
def pinnedAut : baseAut b →* (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) where
  toFun := pinnedAutEquiv
  map_one' := by
    refine LieEquiv.ext fun x => Subtype.ext ?_
    rw [coe_pinnedAutEquiv_apply, blockEquiv_one, Matrix.reindex_refl_refl]
    rfl
  map_mul' g g' := by
    refine LieEquiv.ext fun x => Subtype.ext ?_
    rw [coe_pinnedAutEquiv_apply, blockEquiv_mul, ← Matrix.reindex_trans]
    rfl

/-- The automorphism `pinnedAut b g` reindexes the matrices by `blockEquiv g`. -/
theorem coe_pinnedAut_apply (g : baseAut b) (x : lieAlgebra b) :
    (pinnedAut b g x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) =
      Matrix.reindex (blockEquiv g) (blockEquiv g) x := rfl

/-- The pinned automorphism of $g$ takes the generator $e_i$ to $e_{g(i)}$. -/
theorem pinnedAut_geckE (g : baseAut b) (i : b.support) :
    pinnedAut b g (geckE b i) = geckE b (supportEquiv g i) :=
  Subtype.ext (reindex_e g i)

/-- The pinned automorphism of $g$ takes the generator $f_i$ to $f_{g(i)}$. -/
theorem pinnedAut_geckF (g : baseAut b) (i : b.support) :
    pinnedAut b g (geckF b i) = geckF b (supportEquiv g i) :=
  Subtype.ext (reindex_f g i)

/-- The pinned automorphism of $g$ takes the generator $h_i$ to $h_{g(i)}$. -/
theorem pinnedAut_geckH (g : baseAut b) (i : b.support) :
    pinnedAut b g (geckH b i) = geckH b (supportEquiv g i) :=
  Subtype.ext (reindex_h g i)

variable [P.IsReduced]

/-- The pinned automorphism $\varphi_g$ permutes the simple root elements: $\varphi_g \, x_{\alpha_i}(t) \, \varphi_g^{-1} = x_{\alpha_{g(i)}}(t)$. -/
theorem pinnedAut_mul_simpleRootElement_mul_inv (g : baseAut b) (i : b.support) (t : k) :
    pinnedAut b g * simpleRootElement b i t * (pinnedAut b g)⁻¹ =
      simpleRootElement b (supportEquiv g i) t := by
  rw [simpleRootElement, lieEquiv_mul_expAd_mul_inv]
  exact expAd_congr (pinnedAut_geckE g i) _ _ t

/-- The pinned automorphism $\varphi_g$ permutes the negative simple root elements: $\varphi_g \, x_{-\alpha_i}(t) \, \varphi_g^{-1} = x_{-\alpha_{g(i)}}(t)$. -/
theorem pinnedAut_mul_negSimpleRootElement_mul_inv (g : baseAut b) (i : b.support) (t : k) :
    pinnedAut b g * negSimpleRootElement b i t * (pinnedAut b g)⁻¹ =
      negSimpleRootElement b (supportEquiv g i) t := by
  rw [negSimpleRootElement, lieEquiv_mul_expAd_mul_inv]
  exact expAd_congr (pinnedAut_geckF g i) _ _ t

/-- Conjugation by a pinned automorphism keeps the elementary subgroup $E(k)$. -/
theorem pinnedAut_conj_mem_elementary (g : baseAut b) {x : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b}
    (hx : x ∈ ElementaryAdjointChevalleyGroup b) :
    pinnedAut b g * x * (pinnedAut b g)⁻¹ ∈ ElementaryAdjointChevalleyGroup b := by
  have hle : ElementaryAdjointChevalleyGroup b ≤
      (ElementaryAdjointChevalleyGroup b).comap (MulAut.conj (pinnedAut b g)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨⟨i, t⟩, rfl⟩ | ⟨⟨i, t⟩, rfl⟩) <;>
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [pinnedAut_mul_simpleRootElement_mul_inv]
      exact simpleRootElement_mem b _ t
    · rw [pinnedAut_mul_negSimpleRootElement_mul_inv]
      exact negSimpleRootElement_mem b _ t
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hle hx

end Generators

section Torus

variable {ι k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N}

/-- An automorphism keeps the $\mathbb{Z}$-span of the roots. -/
theorem rootSpan_le_comap (g : P.Aut) :
    P.rootSpan ℤ ≤ (P.rootSpan ℤ).comap ((g.weightEquiv : M →ₗ[k] M).restrictScalars ℤ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_comap.2 (Submodule.subset_span ⟨g.indexEquiv i, root_indexEquiv g i⟩)

/-- An automorphism keeps the root lattice $Q$. -/
theorem rootLattice_le_comap (g : P.Aut) :
    rootLattice P ≤ (rootLattice P).comap (g.weightEquiv : M →+ M) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨g.indexEquiv i, root_indexEquiv g i⟩)

/-- The map of the $\mathbb{Z}$-span of the roots that an automorphism gives. -/
def spanMap (g : P.Aut) : P.rootSpan ℤ →+ P.rootSpan ℤ where
  toFun x := ⟨g.weightEquiv x, rootSpan_le_comap g x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The map of the root lattice $Q$ that an automorphism gives. -/
def latticeMap (g : P.Aut) : rootLattice P →+ rootLattice P where
  toFun x := ⟨g.weightEquiv x, rootLattice_le_comap g x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The map of the root lattice takes the root $\alpha_j$ to the root $\alpha_{g(j)}$. -/
theorem latticeMap_latticeRoot (g : P.Aut) (j : ι) :
    latticeMap g (latticeRoot P j) = latticeRoot P (g.indexEquiv j) :=
  Subtype.ext (root_indexEquiv g j).symm

/-- The automorphism $t \mapsto t \circ g$ of the adjoint torus $\mathrm{Hom}(Q, k^\times)$ that an automorphism $g$ gives. -/
def torusTwist (g : P.Aut) : SplitTorus (P.rootSpan ℤ) k →* SplitTorus (P.rootSpan ℤ) k :=
  SplitTorus.comap k (spanMap g)

/-- The character of the root lattice of `torusTwist g t` is the character of $t$ composed with $g$. -/
theorem torusChar_torusTwist (g : P.Aut) (t : SplitTorus (P.rootSpan ℤ) k) :
    SplitAdjoint.torusChar P (torusTwist g t) = (SplitAdjoint.torusChar P t).comp (latticeMap g) :=
  rfl

variable [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] {b : P.Base}

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] in
/-- The diagonal of a torus element, permuted by `blockEquiv g`, is the diagonal of the torus element twisted by $g^{-1}$. -/
theorem torusDiag_comp_blockEquiv_symm (g : baseAut b) (χ : rootLattice P →+ Additive kˣ) :
    torusDiag b χ ∘ (blockEquiv g).symm = torusDiag b (χ.comp (latticeMap (g⁻¹).1)) := by
  funext x
  obtain ⟨y, rfl⟩ := (blockEquiv g).surjective x
  rcases y with y | y
  · rfl
  · simp only [comp_apply, blockEquiv_inr, torusDiag_inr,
      AddMonoidHom.comp_apply, latticeMap_latticeRoot]
    congr 4

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A pinned automorphism normalizes the torus: $\varphi_g \, h(\chi) = h(\chi \circ g^{-1}) \, \varphi_g$. -/
theorem pinnedAut_mul_torusElement (g : baseAut b) (χ : rootLattice P →+ Additive kˣ) :
    pinnedAut b g * torusElement b χ =
      torusElement b (χ.comp (latticeMap (g⁻¹).1)) * pinnedAut b g := by
  refine LieEquiv.ext fun x => Subtype.ext ?_
  simp only [lieAut_mul_apply, coe_pinnedAut_apply, coe_torusElement_apply, Matrix.reindex_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv g).symm,
    ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv g).symm, Matrix.submatrix_diagonal_equiv,
    Matrix.submatrix_diagonal_equiv, torusDiag_comp_blockEquiv_symm, torusDiag_comp_blockEquiv_symm,
    AddMonoidHom.neg_comp]

end Torus

section Group

variable {ι k M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] [P.IsReduced] {b : P.Base}

omit [P.IsReduced] in
/-- A pinned automorphism normalizes the adjoint torus: $\varphi_g \, h(t) \, \varphi_g^{-1} = h(t \circ g^{-1})$. -/
theorem pinnedAut_mul_torusHom_mul_inv (g : baseAut b) (t : SplitTorus (P.rootSpan ℤ) k) :
    pinnedAut b g * SplitAdjoint.torusHom b t * (pinnedAut b g)⁻¹ =
      SplitAdjoint.torusHom b (torusTwist (g⁻¹).1 t) := by
  change pinnedAut b g * torusElement b (SplitAdjoint.torusChar P t) * _ =
    torusElement b (SplitAdjoint.torusChar P (torusTwist _ t))
  rw [pinnedAut_mul_torusElement, torusChar_torusTwist, mul_inv_cancel_right]

/-- Conjugation by a pinned automorphism keeps the adjoint Chevalley group $G(k)$. -/
theorem pinnedAut_conj_mem_adjoint (g : baseAut b) {x : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b}
    (hx : x ∈ SplitAdjoint.AdjointChevalleyGroup b) :
    pinnedAut b g * x * (pinnedAut b g)⁻¹ ∈ SplitAdjoint.AdjointChevalleyGroup b := by
  obtain ⟨t, y, hy, rfl⟩ := (SplitAdjoint.mem_adjointChevalleyGroup_iff b).1 hx
  have h : pinnedAut b g * (SplitAdjoint.torusHom b t * y) * (pinnedAut b g)⁻¹ =
      (pinnedAut b g * SplitAdjoint.torusHom b t * (pinnedAut b g)⁻¹) *
        (pinnedAut b g * y * (pinnedAut b g)⁻¹) := by
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [h, pinnedAut_mul_torusHom_mul_inv]
  exact mul_mem (SplitAdjoint.torusHom_mem b _)
    (SplitAdjoint.elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b
      (pinnedAut_conj_mem_elementary g hy))

end Group

section ConjAction

variable {A G : Type*} [Group A] [Group G]

/-- The action by conjugation on a subgroup $H$ of $G$ of a group $A$ that maps to $G$, when the conjugation keeps $H$. -/
def conjAction (H : Subgroup G) (φ : A →* G) (hφ : ∀ a, ∀ x ∈ H, φ a * x * (φ a)⁻¹ ∈ H) :
    A →* MulAut H where
  toFun a :=
    { toFun x := ⟨φ a * x * (φ a)⁻¹, hφ a x x.2⟩
      invFun x := ⟨φ a⁻¹ * x * (φ a⁻¹)⁻¹, hφ a⁻¹ x x.2⟩
      left_inv x := Subtype.ext (by simp [mul_assoc])
      right_inv x := Subtype.ext (by simp [mul_assoc])
      map_mul' x y := Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' a a' := by ext x; simp [mul_assoc]

/-- The action `conjAction` is conjugation by $\varphi(a)$. -/
@[simp] theorem coe_conjAction_apply (H : Subgroup G) (φ : A →* G)
    (hφ : ∀ a, ∀ x ∈ H, φ a * x * (φ a)⁻¹ ∈ H) (a : A) (x : H) :
    (conjAction H φ hφ a x : G) = φ a * x * (φ a)⁻¹ := rfl

end ConjAction

section Action

variable {ι k M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] [P.IsReduced]

variable (b : P.Base) in
/-- The action of the automorphisms of the root pairing that keep the base on the elementary subgroup $E(k)$, by conjugation with the pinned automorphisms. -/
def elementaryAction : baseAut b →* MulAut (ElementaryAdjointChevalleyGroup b) :=
  conjAction _ (pinnedAut b) fun g _ hx => pinnedAut_conj_mem_elementary g hx

variable (b : P.Base) in
/-- The action of the automorphisms of the root pairing that keep the base on the adjoint Chevalley group $G(k)$, by conjugation with the pinned automorphisms. -/
def adjointAction : baseAut b →* MulAut (SplitAdjoint.AdjointChevalleyGroup b) :=
  conjAction _ (pinnedAut b) fun g _ hx => pinnedAut_conj_mem_adjoint g hx

variable {b : P.Base}

/-- The action on $G(k)$ permutes the simple root elements: $g \cdot x_{\alpha_i}(t) = x_{\alpha_{g(i)}}(t)$. -/
theorem adjointAction_simpleRootElement (g : baseAut b) (i : b.support) (t : k) :
    (adjointAction b g ⟨simpleRootElement b i t,
        SplitAdjoint.elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b
          (simpleRootElement_mem b i t)⟩ : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) =
      simpleRootElement b (supportEquiv g i) t :=
  pinnedAut_mul_simpleRootElement_mul_inv g i t

/-- The action on $G(k)$ permutes the negative simple root elements: $g \cdot x_{-\alpha_i}(t) = x_{-\alpha_{g(i)}}(t)$. -/
theorem adjointAction_negSimpleRootElement (g : baseAut b) (i : b.support) (t : k) :
    (adjointAction b g ⟨negSimpleRootElement b i t,
        SplitAdjoint.elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b
          (negSimpleRootElement_mem b i t)⟩ : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) =
      negSimpleRootElement b (supportEquiv g i) t :=
  pinnedAut_mul_negSimpleRootElement_mul_inv g i t

/-- The action on $G(k)$ takes the torus element $h(t)$ to $h(t \circ g^{-1})$. -/
theorem adjointAction_torusHom (g : baseAut b) (t : SplitTorus (P.rootSpan ℤ) k) :
    (adjointAction b g ⟨SplitAdjoint.torusHom b t, SplitAdjoint.torusHom_mem b t⟩ :
        lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) = SplitAdjoint.torusHom b (torusTwist (g⁻¹).1 t) :=
  pinnedAut_mul_torusHom_mul_inv g t

end Action

section RootSystem

variable {ι k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N}

/-- For a root system, an automorphism that fixes each root is the identity. -/
theorem eq_one_of_indexEquiv [P.IsRootSystem] {g : P.Aut} (h : ∀ i, g.indexEquiv i = i) : g = 1 := by
  refine Equiv.weightHom_injective P ?_
  rw [map_one]
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P))
    fun i => ?_)
  change g.weightEquiv (P.root i) = P.root i
  rw [← root_indexEquiv, h]

end RootSystem

end Langlands.Groups.Pinned

namespace Langlands.Groups.LGroup

open RootPairing GeckConstruction Pinned Langlands.Groups.Chevalley QuasiSplitDatum

section Dual

variable {Γ : Type*} [Group Γ] {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- The action of $\Gamma$ on the dual group $\hat G(\mathbb{C})$, the adjoint Chevalley group over $\mathbb{C}$, through a homomorphism $\rho$ from $\Gamma$ to the automorphisms that keep the base and the pinned automorphisms. -/
def dualGroupAction (ρ : Γ →* baseAut b) :
    Γ →* MulAut (SplitAdjoint.AdjointChevalleyGroup b) :=
  (adjointAction b).comp ρ

/-- The L-group ${}^L G = \hat G(\mathbb{C}) \rtimes \Gamma$, with $\hat G(\mathbb{C})$ the adjoint Chevalley group over $\mathbb{C}$ of the root system $P$ and $\Gamma$ acting through `dualGroupAction b ρ`. -/
abbrev PinnedLGroup (ρ : Γ →* baseAut b) : Type _ :=
  SplitAdjoint.AdjointChevalleyGroup b ⋊[dualGroupAction b ρ] Γ

/-- For the trivial homomorphism $\rho$ the action on the dual group is trivial. -/
theorem dualGroupAction_one : dualGroupAction b (1 : Γ →* baseAut b) = 1 :=
  MonoidHom.comp_one _

/-- For the trivial homomorphism $\rho$ the L-group is the direct product $\hat G(\mathbb{C}) \times \Gamma$. -/
def pinnedLGroupEquivProd {ρ : Γ →* baseAut b} (hρ : ρ = 1) :
    PinnedLGroup b ρ ≃* SplitAdjoint.AdjointChevalleyGroup b × Γ :=
  (SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl Γ)
    (fun γ => by subst hρ; rw [dualGroupAction_one]; rfl)).trans
    (semidirectProductOneEquiv _ Γ)

/-- The equivalence `pinnedLGroupEquivProd` keeps the two components. -/
@[simp] theorem pinnedLGroupEquivProd_apply {ρ : Γ →* baseAut b} (hρ : ρ = 1)
    (g : PinnedLGroup b ρ) : pinnedLGroupEquivProd b hρ g = (g.left, g.right) := rfl

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- The condition that the root system $P$ over $\mathbb{C}$ with the base $b$ and the action $\rho$ is the dual of the quasi-split datum $D$: the simple roots are the same, the Cartan integers of $P$ are those of the dual root datum, and $\rho(\gamma)$ permutes the roots as the dual action of $\gamma$ does. -/
structure IsDualPinning (D : QuasiSplitDatum Γ ι X Y) (ρ : Γ →* baseAut b) : Prop where
  mem_support_iff (i : ι) : i ∈ b.support ↔ i ∈ D.dual.base.support
  pairingIn_eq (i j : ι) : P.pairingIn ℤ i j = D.dual.datum.pairing i j
  indexEquiv_eq (γ : Γ) : (ρ γ).1.indexEquiv = (D.dual.action γ).indexEquiv

variable {b}

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- For a dual pinning, $\rho(\gamma)$ permutes the simple roots as the dual action of $\gamma$ does. -/
theorem IsDualPinning.supportEquiv_apply {D : QuasiSplitDatum Γ ι X Y} {ρ : Γ →* baseAut b}
    (h : IsDualPinning b D ρ) (γ : Γ) (i : b.support) :
    (supportEquiv (ρ γ) i : ι) = (D.dual.action γ).indexEquiv i := by
  rw [coe_supportEquiv, h.indexEquiv_eq]

/-- For a dual pinning, $\gamma$ takes the simple root element $x_{\alpha_i}(t)$ to $x_{\alpha_j}(t)$, with $j$ the image of $i$ under the dual action of $\gamma$. -/
theorem IsDualPinning.dualGroupAction_simpleRootElement {D : QuasiSplitDatum Γ ι X Y}
    {ρ : Γ →* baseAut b} (h : IsDualPinning b D ρ) (γ : Γ) (i : b.support) (t : ℂ) :
    ∃ j : b.support, (j : ι) = (D.dual.action γ).indexEquiv i ∧
      (dualGroupAction b ρ γ ⟨simpleRootElement b i t,
        SplitAdjoint.elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b
          (simpleRootElement_mem b i t)⟩ : lieAlgebra b ≃ₗ⁅ℂ⁆ lieAlgebra b) =
        simpleRootElement b j t :=
  ⟨supportEquiv (ρ γ) i, h.supportEquiv_apply γ i, adjointAction_simpleRootElement _ i t⟩

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- For a root system, the homomorphism $\rho$ of a dual pinning is unique. -/
theorem IsDualPinning.unique [P.IsRootSystem] {D : QuasiSplitDatum Γ ι X Y}
    {ρ ρ' : Γ →* baseAut b} (h : IsDualPinning b D ρ) (h' : IsDualPinning b D ρ') : ρ = ρ' := by
  ext γ : 1
  have h1 : ((ρ γ)⁻¹ * ρ' γ).1 = 1 := by
    refine eq_one_of_indexEquiv fun i => ?_
    change Equiv.indexHom P (((ρ γ).1)⁻¹ * (ρ' γ).1) i = i
    rw [map_mul, map_inv, Equiv.Perm.mul_apply]
    change (Equiv.indexHom P (ρ γ).1)⁻¹ ((ρ' γ).1.indexEquiv i) = i
    rw [h'.indexEquiv_eq, ← h.indexEquiv_eq]
    exact (Equiv.indexHom P (ρ γ).1).symm_apply_apply i
  exact (inv_mul_eq_one.1 (Subtype.ext h1))

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- For a split datum, the homomorphism $\rho$ of a dual pinning is trivial. -/
theorem IsDualPinning.eq_one [P.IsRootSystem] {D : QuasiSplitDatum Γ ι X Y}
    {ρ : Γ →* baseAut b} (h : IsDualPinning b D ρ) (hD : D.IsSplit) : ρ = 1 := by
  ext γ : 1
  refine Subtype.ext (eq_one_of_indexEquiv fun i => ?_)
  have hD' : D.dual.action = 1 := hD.dual
  rw [h.indexEquiv_eq, hD']
  rfl

/-- For a split datum, the L-group of a dual pinning is the direct product $\hat G(\mathbb{C}) \times \Gamma$. -/
def lGroupEquivProdOfIsSplit [P.IsRootSystem] {D : QuasiSplitDatum Γ ι X Y}
    {ρ : Γ →* baseAut b} (h : IsDualPinning b D ρ) (hD : D.IsSplit) :
    PinnedLGroup b ρ ≃* SplitAdjoint.AdjointChevalleyGroup b × Γ :=
  pinnedLGroupEquivProd b (h.eq_one hD)

end Dual

end Langlands.Groups.LGroup

namespace Langlands.Groups.Unitary

open Matrix RootDatum SplitGL Function

section Involution

variable {G : Type*} [Group G]

/-- The homomorphism from $\mathbb{Z}/2$ to a group $G$ that takes the generator to an element $x$ with $x^2 = 1$. -/
def involutionHom (x : G) (hx : x * x = 1) : Multiplicative (ZMod 2) →* G :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨zmultiplesHom (Additive G) (Additive.ofMul x),
    by
      change ((2 : ℕ) : ℤ) • Additive.ofMul x = 0
      rw [Nat.cast_ofNat, two_zsmul, ← ofMul_mul, hx, ofMul_one]⟩)

/-- The homomorphism `involutionHom x hx` takes the generator of $\mathbb{Z}/2$ to $x$. -/
theorem involutionHom_ofAdd_one (x : G) (hx : x * x = 1) :
    involutionHom x hx (Multiplicative.ofAdd 1) = x := by
  change Additive.toMul (ZMod.lift 2 _ ((1 : ℤ) : ZMod 2)) = x
  rw [ZMod.lift_coe]
  simp

/-- An element of $\mathbb{Z}/2$, written multiplicatively, is $1$ or the generator. -/
theorem zmod_two_eq (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases this a.toAdd with h | h
  · exact Or.inl h
  · exact Or.inr h

end Involution

section Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The sign $\varepsilon_a = (-1)^a$ of an index $a$ of $\mathrm{Fin}\, n$. -/
def sign (a : Fin n) : R := (-1) ^ (a : ℕ)

/-- The square of a sign is $1$. -/
theorem sign_mul_self (a : Fin n) : sign (R := R) a * sign a = 1 := by
  rw [sign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- The sign of the reversed index $n - 1 - a$ is $(-1)^{n-1} \varepsilon_a$. -/
theorem sign_rev (a : Fin n) : sign (R := R) a.rev = (-1) ^ (n - 1) * sign a := by
  have h : sign (R := R) a.rev * sign a = (-1) ^ (n - 1) := by
    rw [sign, sign, ← pow_add, Fin.val_rev]
    congr 1
    omega
  calc sign (R := R) a.rev = sign a.rev * (sign a * sign a) := by rw [sign_mul_self, mul_one]
    _ = (-1) ^ (n - 1) * sign a := by rw [← mul_assoc, h]

/-- Reversing two indices does not change the product of their signs. -/
theorem sign_rev_mul_sign_rev (a c : Fin n) :
    sign (R := R) a.rev * sign c.rev = sign a * sign c := by
  rw [sign_rev, sign_rev, mul_mul_mul_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- Two consecutive indices have the product of signs $-1$. -/
theorem sign_mul_sign_succ {i j : Fin n} (h : j.val = i.val + 1) :
    sign (R := R) i * sign j = -1 := by
  rw [sign, sign, h, ← pow_add, show i.val + (i.val + 1) = 2 * i.val + 1 by omega, pow_succ,
    pow_mul, neg_one_sq, one_pow, one_mul]

variable (n R) in
/-- The antidiagonal matrix $J$ with the entries $J_{a, n-1-a} = (-1)^a$. -/
def antiDiag : Matrix (Fin n) (Fin n) R := of fun a c => if c = a.rev then sign a else 0

/-- Left multiplication by $J$: $(J A)_{ac} = \varepsilon_a A_{n-1-a, c}$. -/
theorem antiDiag_mul_apply (A : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (antiDiag n R * A) a c = sign a * A a.rev c := by
  simp [antiDiag, Matrix.mul_apply, ite_mul]

/-- Right multiplication by $J^T$: $(A J^T)_{ac} = A_{a, n-1-c} \varepsilon_c$. -/
theorem mul_antiDiag_transpose_apply (A : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (A * (antiDiag n R)ᵀ) a c = A a c.rev * sign c := by
  simp [antiDiag, Matrix.mul_apply, mul_ite]

/-- The matrix $J$ is orthogonal: $J J^T = 1$. -/
theorem antiDiag_mul_transpose : antiDiag n R * (antiDiag n R)ᵀ = 1 := by
  ext a c
  rw [antiDiag_mul_apply]
  by_cases h : a = c
  · subst h
    simp [antiDiag, sign_mul_self]
  · simp [antiDiag, h]

/-- The matrix $J$ is orthogonal: $J^T J = 1$. -/
theorem antiDiag_transpose_mul : (antiDiag n R)ᵀ * antiDiag n R = 1 :=
  mul_eq_one_comm.mp antiDiag_mul_transpose

variable (n R) in
/-- The matrix $J$ as an element of $\mathrm{GL}_n(R)$, with the inverse $J^T$. -/
def antiDiagGL : GL (Fin n) R :=
  ⟨antiDiag n R, (antiDiag n R)ᵀ, antiDiag_mul_transpose, antiDiag_transpose_mul⟩

variable (n R) in
/-- The automorphism $g \mapsto (g^{-1})^T$ of $\mathrm{GL}_n(R)$. -/
def invTranspose : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(↑g⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ, (↑g : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := Units.ext <| by simp
  map_mul' g h := Units.ext <| by simp [_root_.mul_inv_rev, transpose_mul]

variable (n R) in
/-- The involution $\theta(g) = J (g^T)^{-1} J^{-1}$ of $\mathrm{GL}_n(R)$. It is the action of the nontrivial element of $\mathrm{Gal}(E/F)$ on the dual group of the quasi-split unitary group $U(n)$. -/
def theta : GL (Fin n) R →* GL (Fin n) R :=
  (MulAut.conj (antiDiagGL n R)).toMonoidHom.comp (invTranspose n R)

/-- The matrix of $\theta(g)$ is $J (g^T)^{-1} J^{-1}$. -/
theorem coe_theta (g : GL (Fin n) R) :
    (theta n R g : Matrix (Fin n) (Fin n) R) =
      antiDiag n R * ((g : Matrix (Fin n) (Fin n) R)ᵀ)⁻¹ * (antiDiag n R)⁻¹ := by
  rw [Matrix.inv_eq_right_inv antiDiag_mul_transpose, ← transpose_nonsing_inv, ← coe_units_inv]
  rfl

/-- The entries of $\theta(g)$: $\theta(g)_{ac} = \varepsilon_a \varepsilon_c (g^{-1})_{n-1-c, n-1-a}$. -/
theorem theta_apply (g : GL (Fin n) R) (a c : Fin n) :
    (theta n R g : Matrix (Fin n) (Fin n) R) a c =
      sign a * sign c * (↑g⁻¹ : Matrix (Fin n) (Fin n) R) c.rev a.rev := by
  change (antiDiag n R * (↑g⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ * (antiDiag n R)ᵀ) a c = _
  rw [mul_antiDiag_transpose_apply, antiDiag_mul_apply, transpose_apply]
  ring

/-- The map $\theta$ is an involution: $\theta(\theta(g)) = g$. -/
theorem theta_theta (g : GL (Fin n) R) : theta n R (theta n R g) = g := by
  refine Units.ext ?_
  ext a c
  rw [theta_apply, ← map_inv, theta_apply, inv_inv, Fin.rev_rev, Fin.rev_rev,
    sign_rev_mul_sign_rev]
  have ha := sign_mul_self (R := R) a
  have hc := sign_mul_self (R := R) c
  linear_combination ((g : Matrix (Fin n) (Fin n) R) a c * sign c * sign c) * ha +
    (g : Matrix (Fin n) (Fin n) R) a c * hc

end Matrix

section Pinning

variable {n : ℕ} {R : Type*} [CommRing R]

variable (n R) in
/-- The involution $\theta$ as an automorphism of $\mathrm{GL}_n(R)$. -/
def thetaAut : MulAut (GL (Fin n) R) where
  toFun := theta n R
  invFun := theta n R
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := map_mul (theta n R)

/-- The automorphism `thetaAut n R` is $\theta$. -/
theorem thetaAut_apply (g : GL (Fin n) R) : thetaAut n R g = theta n R g := rfl

/-- The automorphism $\theta$ has order dividing $2$. -/
theorem thetaAut_mul_self : thetaAut n R * thetaAut n R = 1 :=
  MulEquiv.ext theta_theta

variable (n) in
/-- The automorphism $x \mapsto -(x \circ \mathrm{rev})$ of $\mathbb{Z}^n$, with $\mathrm{rev}(i) = n - 1 - i$. It is the action of the nontrivial element of $\mathrm{Gal}(E/F)$ on the characters of the diagonal torus of $U(n)$. -/
def outerMap : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) where
  toFun x := -(x ∘ Fin.rev)
  invFun x := -(x ∘ Fin.rev)
  map_add' x y := by ext; simp; ring
  map_smul' c x := by ext; simp
  left_inv x := by ext; simp
  right_inv x := by ext; simp

/-- The coordinates of the outer map: $(-(x \circ \mathrm{rev}))_i = -x_{n-1-i}$. -/
theorem outerMap_apply (x : Fin n → ℤ) (i : Fin n) : outerMap n x i = -x i.rev := rfl

/-- The outer map is an involution. -/
theorem outerMap_outerMap (x : Fin n → ℤ) : outerMap n (outerMap n x) = x := by
  ext i; simp [outerMap_apply]

/-- The outer map takes $e_i$ to $-e_{n-1-i}$. -/
theorem outerMap_single (i : Fin n) :
    outerMap n (Pi.single i 1) = -Pi.single i.rev 1 := by
  ext m
  simp only [outerMap_apply, Pi.neg_apply, Pi.single_apply, Fin.rev_eq_iff]

/-- The outer map is symmetric for the dot product. -/
theorem outerMap_dotProduct (x y : Fin n → ℤ) : outerMap n x ⬝ᵥ y = x ⬝ᵥ outerMap n y := by
  simp only [dotProduct, outerMap_apply, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_inj]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun m => by simp [mul_comm]

variable (n R) in
/-- The automorphism $t \mapsto t \circ \sigma$ of the torus $\mathrm{Hom}(\mathbb{Z}^n, R^\times)$, with $\sigma$ the outer map. -/
def torusTwist : SplitTorus (Fin n → ℤ) R →* SplitTorus (Fin n → ℤ) R :=
  SplitTorus.comap R (outerMap n).toLinearMap.toAddMonoidHom

/-- The diagonal entries of the twisted torus element: $\sigma(t)_i = t_{n-1-i}^{-1}$. -/
theorem torusEntry_torusTwist (t : SplitTorus (Fin n → ℤ) R) (i : Fin n) :
    torusEntry (torusTwist n R t) i = (torusEntry t i.rev)⁻¹ := by
  change t (Multiplicative.ofAdd (outerMap n (Pi.single i 1))) = _
  rw [outerMap_single, ofAdd_neg, map_inv]
  rfl

/-- The twist of the torus is an involution. -/
theorem torusTwist_torusTwist (t : SplitTorus (Fin n → ℤ) R) :
    torusTwist n R (torusTwist n R t) = t := by
  rw [← ofUnits_torusEntry (torusTwist n R (torusTwist n R t))]
  conv_rhs => rw [← ofUnits_torusEntry t]
  congr 1
  funext i
  rw [torusEntry_torusTwist, torusEntry_torusTwist, Fin.rev_rev, inv_inv]

/-- The involution $\theta$ keeps the diagonal torus and acts on it by the outer map: $\theta(\mathrm{diag}(t)) = \mathrm{diag}(t \circ \sigma)$. -/
theorem theta_torusHom (t : SplitTorus (Fin n → ℤ) R) :
    theta n R (torusHom n R t) = torusHom n R (torusTwist n R t) := by
  refine Units.ext ?_
  ext a c
  rw [theta_apply, ← map_inv, coe_torusHom, coe_torusHom, diagonal_apply, diagonal_apply,
    torusEntry_torusTwist]
  by_cases h : a = c
  · subst h
    simp [sign_mul_self]
    rfl
  · simp [h, Ne.symm h]

end Pinning

section Roots

variable {n : ℕ} {R : Type*} [CommRing R]

variable (n) in
/-- The permutation $(i, j) \mapsto (n-1-j, n-1-i)$ of the roots of $\mathrm{GL}_n$. The outer map takes the root $e_i - e_j$ to the root $e_{n-1-j} - e_{n-1-i}$. -/
def outerIndex : glIndex n ≃ glIndex n where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), fun h => p.2 (Fin.rev_injective h).symm⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), fun h => p.2 (Fin.rev_injective h).symm⟩
  left_inv p := by simp
  right_inv p := by simp

/-- The first index of `outerIndex n p`. -/
@[simp] theorem outerIndex_fst (p : glIndex n) : (outerIndex n p).1.1 = p.1.2.rev := rfl

/-- The second index of `outerIndex n p`. -/
@[simp] theorem outerIndex_snd (p : glIndex n) : (outerIndex n p).1.2 = p.1.1.rev := rfl

/-- The permutation `outerIndex n` keeps the simple roots $e_i - e_{i+1}$. -/
theorem outerIndex_mem_glSimple_iff {p : glIndex n} :
    outerIndex n p ∈ glSimple n ↔ p ∈ glSimple n := by
  rw [mem_glSimple, mem_glSimple, outerIndex_fst, outerIndex_snd, Fin.val_rev, Fin.val_rev]
  have h1 := p.1.1.isLt
  have h2 := p.1.2.isLt
  omega

/-- The root element $x_{ij}(0)$ is $1$. -/
theorem rootElement_zero (p : glIndex n) : rootElement p (0 : R) = 1 :=
  Units.ext <| by simp [coe_rootElement]

/-- The inverse of $x_{ij}(t)$ is $x_{ij}(-t)$. -/
theorem rootElement_inv (p : glIndex n) (t : R) : (rootElement p t)⁻¹ = rootElement p (-t) :=
  inv_eq_of_mul_eq_one_right <| by rw [← rootElement_add, add_neg_cancel, rootElement_zero]

/-- The involution $\theta$ on the root elements: $\theta(x_{ij}(t)) = x_{n-1-j, n-1-i}(-\varepsilon_i \varepsilon_j t)$. -/
theorem theta_rootElement (p : glIndex n) (t : R) :
    theta n R (rootElement p t) =
      rootElement (outerIndex n p) (-(sign p.1.1 * sign p.1.2) * t) := by
  refine Units.ext ?_
  ext a c
  rw [theta_apply, rootElement_inv, coe_rootElement, coe_rootElement]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, single_apply, outerIndex_fst,
    outerIndex_snd]
  by_cases h : p.1.2.rev = a ∧ p.1.1.rev = c
  · obtain ⟨rfl, rfl⟩ := h
    have hne : p.1.2.rev ≠ p.1.1.rev := fun h => p.2 (Fin.rev_injective h).symm
    have hne' : p.1.1 ≠ p.1.2 := p.2
    simp only [Fin.rev_rev, hne, hne', ite_false, and_self, ite_true, zero_add]
    rw [sign_rev_mul_sign_rev]
    ring
  · have h' : ¬ (p.1.1 = c.rev ∧ p.1.2 = a.rev) := by
      rwa [← Fin.rev_eq_iff, ← Fin.rev_eq_iff, and_comm]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
      add_zero, add_zero]
    by_cases hac : a = c
    · subst hac
      simp [sign_mul_self]
    · simp [hac, Ne.symm hac]

/-- The involution $\theta$ permutes the simple root elements: $\theta(x_{i, i+1}(t)) = x_{n-2-i, n-1-i}(t)$. -/
theorem theta_rootElement_of_mem {p : glIndex n} (hp : p ∈ glSimple n) (t : R) :
    theta n R (rootElement p t) = rootElement (outerIndex n p) t := by
  rw [theta_rootElement, sign_mul_sign_succ (mem_glSimple.1 hp), neg_neg, one_mul]

variable (n R) in
/-- The Borel subgroup of the upper triangular matrices in $\mathrm{GL}_n(R)$. -/
def upperBorel : Subgroup (GL (Fin n) R) where
  carrier := {g | BlockTriangular (g : Matrix (Fin n) (Fin n) R) id}
  mul_mem' ha hb := BlockTriangular.mul ha hb
  one_mem' := blockTriangular_one
  inv_mem' {g} hg := by
    let _ : Invertible (g : Matrix (Fin n) (Fin n) R) := invertibleOfLeftInverse _ _ g.inv_mul
    change BlockTriangular _ id
    rw [coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hg

/-- A matrix is in the Borel subgroup if and only if its entries below the diagonal are zero. -/
theorem mem_upperBorel_iff {g : GL (Fin n) R} :
    g ∈ upperBorel n R ↔ ∀ a c, c < a → (g : Matrix (Fin n) (Fin n) R) a c = 0 :=
  ⟨fun h _ _ hca => h hca, fun h _ _ hca => h _ _ hca⟩

/-- The involution $\theta$ takes an upper triangular matrix to an upper triangular matrix. -/
theorem theta_mem_upperBorel {g : GL (Fin n) R} (hg : g ∈ upperBorel n R) :
    theta n R g ∈ upperBorel n R := by
  rw [mem_upperBorel_iff]
  intro a c hca
  rw [theta_apply, mem_upperBorel_iff.1 (inv_mem hg) _ _ (Fin.rev_lt_rev.2 hca), mul_zero]

/-- The involution $\theta$ keeps the upper triangular Borel subgroup. -/
theorem map_theta_upperBorel : (upperBorel n R).map (theta n R) = upperBorel n R :=
  le_antisymm (Subgroup.map_le_iff_le_comap.2 fun _ hg => theta_mem_upperBorel hg)
    fun g hg => ⟨theta n R g, theta_mem_upperBorel hg, theta_theta g⟩

/-- The involution $\theta$ keeps the diagonal torus. -/
theorem map_theta_range_torusHom :
    (torusHom n R).range.map (theta n R) = (torusHom n R).range := by
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨torusTwist n R t, (theta_torusHom t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨torusTwist n R t, rfl⟩, by rw [theta_torusHom, torusTwist_torusTwist]⟩

end Roots

section Datum

variable {n : ℕ}

/-- The outer map takes the root $e_i - e_j$ to the root $e_{n-1-j} - e_{n-1-i}$. -/
theorem outerMap_glRoot (i j : Fin n) : outerMap n (glRoot i j) = glRoot j.rev i.rev := by
  simp only [glRoot, map_sub, outerMap_single]
  abel

variable (n) in
/-- The outer automorphism of the root datum of $\mathrm{GL}_n$: the outer map $x \mapsto -(x \circ \mathrm{rev})$ on the characters and on the cocharacters, with the permutation `outerIndex n` of the roots. -/
def glOuter : (gl n).Aut where
  weightMap := (outerMap n).toLinearMap
  coweightMap := (outerMap n).toLinearMap
  indexEquiv := outerIndex n
  weight_coweight_transpose := by
    ext y x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.dualMap_apply,
      LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap, LinearMap.flip_apply,
      gl_toLinearMap_apply, LinearEquiv.coe_coe]
    exact outerMap_dotProduct _ _
  root_weightMap := funext fun p => outerMap_glRoot p.1.1 p.1.2
  coroot_coweightMap := funext fun p => outerMap_glRoot p.1.1 p.1.2
  bijective_weightMap := (outerMap n).bijective
  bijective_coweightMap := (outerMap n).bijective

/-- The outer automorphism acts on the characters by the outer map. -/
@[simp] theorem glOuter_weightMap (x : Fin n → ℤ) : (glOuter n).weightMap x = outerMap n x := rfl

/-- The outer automorphism acts on the cocharacters by the outer map. -/
@[simp] theorem glOuter_coweightMap (x : Fin n → ℤ) :
    (glOuter n).coweightMap x = outerMap n x := rfl

/-- The outer automorphism permutes the roots by `outerIndex n`. -/
@[simp] theorem glOuter_indexEquiv : (glOuter n).indexEquiv = outerIndex n := rfl

/-- The outer automorphism of the root datum of $\mathrm{GL}_n$ is an involution. -/
theorem glOuter_mul_self : glOuter n * glOuter n = 1 := by
  ext x <;> simp [outerMap_outerMap]

end Datum

section LGroup

open QuasiSplitDatum LGroup

variable {Γ : Type*} [Group Γ] (n : ℕ) (R : Type*) [CommRing R]

/-- The quasi-split datum of the unitary group $U(n)$ for a quadratic extension $E/F$: the root datum of $\mathrm{GL}_n$ with the base $e_i - e_{i+1}$, and the action of $\Gamma$ through the character $\chi : \Gamma \to \mathbb{Z}/2$, with the nontrivial element acting by the outer automorphism. -/
def unitaryDatum (χ : Γ →* Multiplicative (ZMod 2)) :
    QuasiSplitDatum Γ (glIndex n) (Fin n → ℤ) (Fin n → ℤ) where
  datum := gl n
  base := glBase n
  action := (involutionHom (glOuter n) glOuter_mul_self).comp χ
  mem_support_iff γ p := by
    rcases zmod_two_eq (χ γ) with h | h
    · simp [h]
    · simp only [MonoidHom.comp_apply, h, involutionHom_ofAdd_one, glOuter_indexEquiv,
        glBase_support]
      exact outerIndex_mem_glSimple_iff

/-- The action of $\Gamma$ on $\mathrm{GL}_n(R)$ through the character $\chi$, with the nontrivial element acting by $\theta$. -/
def unitaryAction (χ : Γ →* Multiplicative (ZMod 2)) : Γ →* MulAut (GL (Fin n) R) :=
  (involutionHom (thetaAut n R) thetaAut_mul_self).comp χ

/-- The L-group ${}^L U(n) = \mathrm{GL}_n(R) \rtimes \Gamma$ of the quasi-split unitary group, with $\Gamma$ acting through `unitaryAction n R χ`. For $R = \mathbb{C}$ and $\Gamma = \mathrm{Gal}(E/F)$ this is the L-group of the theory. -/
abbrev UnitaryLGroup (χ : Γ →* Multiplicative (ZMod 2)) : Type _ :=
  GL (Fin n) R ⋊[unitaryAction n R χ] Γ

/-- The L-group ${}^L U(n) = \mathrm{GL}_n(\mathbb{C}) \rtimes \Gamma$ of the quasi-split unitary group over $\mathbb{C}$. -/
abbrev LUnitary (χ : Γ →* Multiplicative (ZMod 2)) : Type _ :=
  UnitaryLGroup n ℂ χ

variable {n R}

/-- An element $\gamma$ with $\chi(\gamma) = 1$ acts trivially on $\mathrm{GL}_n(R)$. -/
theorem unitaryAction_apply_of_eq_one {χ : Γ →* Multiplicative (ZMod 2)} {γ : Γ} (h : χ γ = 1)
    (g : GL (Fin n) R) : unitaryAction n R χ γ g = g := by
  simp [unitaryAction, h]

/-- An element $\gamma$ with $\chi(\gamma) \neq 1$ acts on $\mathrm{GL}_n(R)$ by $\theta$. -/
theorem unitaryAction_apply_of_ne_one {χ : Γ →* Multiplicative (ZMod 2)} {γ : Γ} (h : χ γ ≠ 1)
    (g : GL (Fin n) R) : unitaryAction n R χ γ g = theta n R g := by
  rcases zmod_two_eq (χ γ) with h' | h'
  · exact absurd h' h
  · simp only [unitaryAction, MonoidHom.comp_apply, h', involutionHom_ofAdd_one, thetaAut_apply]

/-- An element $\gamma$ with $\chi(\gamma) = 1$ acts trivially on the root datum. -/
theorem unitaryDatum_action_of_eq_one {χ : Γ →* Multiplicative (ZMod 2)} {γ : Γ} (h : χ γ = 1) :
    (unitaryDatum n χ).action γ = 1 := by
  change involutionHom (glOuter n) glOuter_mul_self (χ γ) = 1
  rw [h, map_one]

/-- An element $\gamma$ with $\chi(\gamma) \neq 1$ acts on the root datum by the outer automorphism. -/
theorem unitaryDatum_action_of_ne_one {χ : Γ →* Multiplicative (ZMod 2)} {γ : Γ} (h : χ γ ≠ 1) :
    (unitaryDatum n χ).action γ = glOuter n := by
  rcases zmod_two_eq (χ γ) with h' | h'
  · exact absurd h' h
  · change involutionHom (glOuter n) glOuter_mul_self (χ γ) = _
    rw [h', involutionHom_ofAdd_one]

/-- For $n \geq 1$ the datum of $U(n)$ is split if and only if the character $\chi$ is trivial. -/
theorem unitaryDatum_isSplit_iff [NeZero n] {χ : Γ →* Multiplicative (ZMod 2)} :
    (unitaryDatum n χ).IsSplit ↔ χ = 1 := by
  constructor
  · intro hs
    refine MonoidHom.ext fun γ => ?_
    by_contra h
    have h1 : (unitaryDatum n χ).action γ = 1 := by rw [IsSplit] at hs; rw [hs]; rfl
    rw [unitaryDatum_action_of_ne_one h] at h1
    have h2 := congrArg (fun g : (gl n).Aut => g.weightMap (Pi.single (0 : Fin n) (1 : ℤ)) 0) h1
    change outerMap n (Pi.single (0 : Fin n) (1 : ℤ)) 0 =
      (Pi.single (0 : Fin n) (1 : ℤ) : Fin n → ℤ) 0 at h2
    rw [outerMap_single, Pi.neg_apply, Pi.single_eq_same, Pi.single_apply] at h2
    split_ifs at h2; omega
  · intro hχ
    exact MonoidHom.ext fun γ => unitaryDatum_action_of_eq_one (by rw [hχ]; rfl)

/-- An element $\gamma$ with $\chi(\gamma) \neq 1$ acts on the dual torus by the twist of the outer map. -/
theorem dualTorusAction_unitaryDatum_of_ne_one {χ : Γ →* Multiplicative (ZMod 2)} {γ : Γ}
    (h : χ γ ≠ 1) (t : SplitTorus (Fin n → ℤ) R) :
    dualTorusAction R (unitaryDatum n χ) γ t = torusTwist n R t := by
  refine MonoidHom.ext fun x => ?_
  change dualTorusAction R (unitaryDatum n χ) γ t (Multiplicative.ofAdd x.toAdd) =
    t (Multiplicative.ofAdd (outerMap n x.toAdd))
  rw [dualTorusAction_apply]
  congr 2
  rw [dual_action_apply, unitaryDatum_action_of_ne_one h, LinearEquiv.symm_apply_eq]
  change x.toAdd = (glOuter n).coweightEquiv.symm (outerMap n x.toAdd)
  exact ((glOuter n).coweightEquiv.eq_symm_apply).2 rfl

/-- The action on $\mathrm{GL}_n(R)$ matches the dual action of the datum of $U(n)$ on the diagonal torus: $\gamma \cdot \mathrm{diag}(t) = \mathrm{diag}(\gamma \cdot t)$. -/
theorem unitaryAction_torusHom (χ : Γ →* Multiplicative (ZMod 2)) (γ : Γ)
    (t : SplitTorus (Fin n → ℤ) R) :
    unitaryAction n R χ γ (torusHom n R t) =
      torusHom n R (dualTorusAction R (unitaryDatum n χ) γ t) := by
  by_cases h : χ γ = 1
  · have h1 : (unitaryDatum n χ).dual.action γ = 1 := by
      rw [dual_action_apply, unitaryDatum_action_of_eq_one h]
      exact equivDual_id _
    rw [unitaryAction_apply_of_eq_one h]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change _ = dualTorusAction R (unitaryDatum n χ) γ t (Multiplicative.ofAdd x.toAdd)
    rw [dualTorusAction_apply, h1]
    exact congrArg t (congrArg Multiplicative.ofAdd
      ((RootPairing.Equiv.weightEquiv (1 : (gl n).Aut)).eq_symm_apply.2 rfl))
  · rw [unitaryAction_apply_of_ne_one h, dualTorusAction_unitaryDatum_of_ne_one h,
      theta_torusHom]

/-- The action on $\mathrm{GL}_n(R)$ matches the dual action of the datum of $U(n)$ on the simple roots: $\gamma \cdot x_\alpha(t) = x_{\gamma(\alpha)}(t)$ for each simple root $\alpha$. -/
theorem unitaryAction_rootElement (χ : Γ →* Multiplicative (ZMod 2)) (γ : Γ) {p : glIndex n}
    (hp : p ∈ glSimple n) (t : R) :
    unitaryAction n R χ γ (rootElement p t) =
      rootElement (((unitaryDatum n χ).dual.action γ).indexEquiv p) t := by
  rw [dual_action_indexEquiv]
  by_cases h : χ γ = 1
  · rw [unitaryAction_apply_of_eq_one h, unitaryDatum_action_of_eq_one h]
    rfl
  · rw [unitaryAction_apply_of_ne_one h, unitaryDatum_action_of_ne_one h, glOuter_indexEquiv,
      theta_rootElement_of_mem hp]

/-- The embedding of the L-group of the diagonal torus of $U(n)$ into the L-group of $U(n)$. It is the diagonal embedding on the dual torus and the identity on $\Gamma$. -/
def torusLGroupToUnitary (χ : Γ →* Multiplicative (ZMod 2)) :
    TorusLGroup R (unitaryDatum n χ) →* UnitaryLGroup n R χ :=
  SemidirectProduct.map (torusHom n R) (MonoidHom.id Γ) fun γ => by
    ext t : 1
    exact (unitaryAction_torusHom χ γ t).symm

/-- The embedding `torusLGroupToUnitary` is injective. -/
theorem torusLGroupToUnitary_injective (χ : Γ →* Multiplicative (ZMod 2)) :
    Injective (torusLGroupToUnitary (n := n) (R := R) χ) := by
  intro g g' h
  have h1 := congrArg SemidirectProduct.left h
  have h2 := congrArg SemidirectProduct.right h
  exact SemidirectProduct.ext (torusHom_injective h1) h2

/-- For the trivial character $\chi$ the L-group of $U(n)$ is the direct product $\mathrm{GL}_n(R) \times \Gamma$. -/
def unitaryLGroupEquivProd (χ : Γ →* Multiplicative (ZMod 2)) (hχ : χ = 1) :
    UnitaryLGroup n R χ ≃* GL (Fin n) R × Γ :=
  (SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl Γ) (fun γ => by
    ext g : 1
    simp [unitaryAction_apply_of_eq_one (show χ γ = 1 by simp [hχ])])).trans
    (semidirectProductOneEquiv (GL (Fin n) R) Γ)

end LGroup

end Langlands.Groups.Unitary
