/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Root data, dual root data and the combinatorial L-group

Let $(X, Y, \Phi, \Phi^\vee)$ be a root datum: $X$ and $Y$ are lattices in perfect pairing, $\Phi \subset X$ are the roots and $\Phi^\vee \subset Y$ are the coroots. Mathlib has root data as `RootDatum`, a `RootPairing` over $\mathbb{Z}$, with morphisms, isomorphisms, automorphisms and bases. This file uses these notions and does not define root data again. It builds the dual root datum $(Y, X, \Phi^\vee, \Phi)$ of the dual group $\hat G$, the root data of $GL_n$, $SL_2$, $PGL_2$ and of the split tori, and a combinatorial form of the L-group ${}^L G = \hat G \rtimes \Gamma$ of a quasi-split group.

A quasi-split group $G$ over $F$ gives a based root datum $(X, \Delta, Y, \Delta^\vee)$ with an action of $\Gamma = \mathrm{Gal}(\bar F / F)$ (or of the Weil group $W_F$) that keeps the base. The dual group $\hat G$ has the dual based root datum $(Y, \Delta^\vee, X, \Delta)$, and $\Gamma$ acts on it by $\gamma \mapsto (\gamma^{-1})^\vee$. The pair of the dual based root datum and this action determines ${}^L G$ up to isomorphism (Borel, Corvallis, section 2). This file formalizes this pair as `Langlands.Groups.QuasiSplitDatum.dual`.

## Main definitions

* `Langlands.Groups.RootDatum.dual`: the dual root datum, which is `RootPairing.flip`.
* `Langlands.Groups.RootDatum.homDual`, `Langlands.Groups.RootDatum.equivDual`, `Langlands.Groups.RootDatum.autDual`: the transpose of a morphism, the dual of an isomorphism and the homomorphism $\mathrm{Aut}(P) \to \mathrm{Aut}(P^\vee)$.
* `Langlands.Groups.RootDatum.gl`, `Langlands.Groups.RootDatum.glBase`: the root datum of $GL_n$ with the roots $e_i - e_j$, and its base of the simple roots $e_i - e_{i+1}$.
* `Langlands.Groups.RootDatum.sl2`, `Langlands.Groups.RootDatum.pgl2`: the root data of $SL_2$ and $PGL_2$, as cases of `Langlands.Groups.RootDatum.rankOne`.
* `Langlands.Groups.RootDatum.torusOf`, `Langlands.Groups.RootDatum.torus`: the root data of split tori.
* `Langlands.Groups.QuasiSplitDatum`: a based root datum with an action of a group $\Gamma$ that keeps the base.
* `Langlands.Groups.QuasiSplitDatum.dual`, `Langlands.Groups.QuasiSplitDatum.lgroupDatum`: the datum of the L-group.
* `Langlands.Groups.QuasiSplitDatum.split`: the datum of a split group, with the trivial action.
* `Langlands.Groups.QuasiSplitDatum.Iso`: isomorphisms of quasi-split data, with `Iso.dual`.
* `Langlands.Groups.QuasiSplitDatum.torus`: the datum of a torus with an action of $\Gamma$ on the character lattice.

## Main results

* `Langlands.Groups.RootDatum.dual_dual`: $(P^\vee)^\vee = P$.
* `Langlands.Groups.RootDatum.dual_root`, `Langlands.Groups.RootDatum.dual_coroot`: the roots and the coroots change places.
* `Langlands.Groups.RootDatum.homDual_comp`, `Langlands.Groups.RootDatum.equivDual_comp`, `Langlands.Groups.RootDatum.equivDual_equivDual`: the duality is a functor and it is involutive.
* `Langlands.Groups.RootDatum.dual_gl`: the root datum of $GL_n$ is equal to its dual, and `Langlands.Groups.RootDatum.glDualEquiv` is the isomorphism.
* `Langlands.Groups.RootDatum.dual_sl2`: the dual of the root datum of $SL_2$ is the root datum of $PGL_2$, and `Langlands.Groups.RootDatum.sl2DualEquiv` is the isomorphism.
* `Langlands.Groups.RootDatum.isEmpty_equiv_sl2_dual`: the root datum of $SL_2$ is not self-dual.
* `Langlands.Groups.RootDatum.dual_torusOf`, `Langlands.Groups.RootDatum.torusDualEquiv`: the dual of a torus is the torus of the dual lattice.
* `Langlands.Groups.QuasiSplitDatum.dual_dual`: the L-group construction is involutive.
* `Langlands.Groups.QuasiSplitDatum.pairing_action_dual_action`: the dual action is the contragredient action.
* `Langlands.Groups.QuasiSplitDatum.dual_split`, `Langlands.Groups.QuasiSplitDatum.isSplit_dual_iff`: for a split group the dual action is trivial.
* `Langlands.Groups.QuasiSplitDatum.Iso.dual_refl`, `Langlands.Groups.QuasiSplitDatum.Iso.dual_trans`: the L-group datum is functorial for isomorphisms that commute with $\Gamma$.
* `Langlands.Groups.QuasiSplitDatum.dual_split_gl`, `Langlands.Groups.QuasiSplitDatum.dual_split_sl2`: the L-group data of split $GL_n$ and $SL_2$.
* `Langlands.Groups.QuasiSplitDatum.torus_dual_action_weightMap`: the L-group of a torus, with $\Gamma$ acting on $\mathrm{Hom}(X, \mathbb{Z})$ by the contragredient action.

## Implementation notes

A morphism `RootPairing.Hom P Q` of Mathlib maps the weights of $P$ to the weights of $Q$ and the coweights of $Q$ to the coweights of $P$. Thus the transpose `homDual` reverses the direction. The dual of an isomorphism `equivDual` is the transpose of the inverse, so it keeps the direction, and `autDual` is a group homomorphism. The data in this file are combinatorial. The complex group $\hat G$ and the semidirect product $\hat G \rtimes W_F$ need a Chevalley existence theorem over $\mathbb{C}$, which Mathlib does not have.

## References

* A. Borel, Automorphic L-functions, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2 (1979), sections 1 and 2.
* T. A. Springer, Reductive groups, in the same volume, section 1.
* N. Bourbaki, Groupes et algebres de Lie, chapters IV to VI.
-/

noncomputable section

namespace Langlands.Groups

open Module Function

namespace RootDatum

variable {ι ι₂ ι₃ X Y X₂ Y₂ X₃ Y₃ : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X₂] [AddCommGroup Y₂] [AddCommGroup X₃] [AddCommGroup Y₃]

/-- The dual root datum $(Y, X, \Phi^\vee, \Phi)$ of a root datum $(X, Y, \Phi, \Phi^\vee)$. It is the flip `RootPairing.flip` of Mathlib: the roots and the coroots change places, and the pairing is transposed. -/
abbrev dual (P : RootDatum ι X Y) : RootDatum ι Y X := P.flip

/-- The dual of the dual root datum is the original root datum. This is an equality. -/
theorem dual_dual (P : RootDatum ι X Y) : dual (dual P) = P := rfl

/-- The roots of the dual root datum are the coroots of the root datum. -/
theorem dual_root (P : RootDatum ι X Y) : (dual P).root = P.coroot := rfl

/-- The coroots of the dual root datum are the roots of the root datum. -/
theorem dual_coroot (P : RootDatum ι X Y) : (dual P).coroot = P.root := rfl

/-- The Cartan integers of the dual root datum are the transposed Cartan integers: $\langle \alpha_i^\vee, \alpha_j \rangle$ for the dual is $\langle \alpha_j, \alpha_i^\vee \rangle$. -/
theorem dual_pairing (P : RootDatum ι X Y) (i j : ι) : (dual P).pairing i j = P.pairing j i := rfl

/-- The pairing of the dual root datum is the transposed pairing. -/
theorem dual_toLinearMap_apply (P : RootDatum ι X Y) (y : Y) (x : X) :
    (dual P).toLinearMap y x = P.toLinearMap x y := rfl

/-- The dual root datum has the same permutations of the index set as the root datum. -/
theorem dual_reflectionPerm (P : RootDatum ι X Y) :
    (dual P).reflectionPerm = P.reflectionPerm := rfl

/-- The reflections of the dual root datum are the coreflections of the root datum. -/
theorem dual_reflection (P : RootDatum ι X Y) (i : ι) :
    (dual P).reflection i = P.coreflection i := rfl

/-- The map that takes a root datum to its dual is injective. -/
theorem dual_injective : Injective (dual : RootDatum ι X Y → RootDatum ι Y X) :=
  fun P Q h => by rw [← dual_dual P, h, dual_dual]

variable {P : RootDatum ι X Y} {Q : RootDatum ι₂ X₂ Y₂} {S : RootDatum ι₃ X₃ Y₃}

/-- The transpose of a morphism of root data $P \to Q$ is a morphism of the dual root data $Q^\vee \to P^\vee$. The map of weights and the map of coweights change places. -/
def homDual (f : RootPairing.Hom P Q) : RootPairing.Hom (dual Q) (dual P) where
  weightMap := f.coweightMap
  coweightMap := f.weightMap
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext x y
    have h := RootPairing.Hom.weight_coweight_transpose_apply P Q y f
    have h' := LinearMap.congr_fun h x
    simp only [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap,
      LinearMap.flip_apply] at h'
    simp only [LinearMap.coe_comp, comp_apply, LinearMap.dualMap_apply,
      RootPairing.flip_toLinearMap]
    exact h'.symm
  root_weightMap := f.coroot_coweightMap
  coroot_coweightMap := by simpa using f.root_weightMap

/-- The map of weights of the transpose is the map of coweights. -/
@[simp] theorem homDual_weightMap (f : RootPairing.Hom P Q) :
    (homDual f).weightMap = f.coweightMap := rfl

/-- The map of coweights of the transpose is the map of weights. -/
@[simp] theorem homDual_coweightMap (f : RootPairing.Hom P Q) :
    (homDual f).coweightMap = f.weightMap := rfl

/-- The bijection of index sets of the transpose is the inverse bijection. -/
@[simp] theorem homDual_indexEquiv (f : RootPairing.Hom P Q) :
    (homDual f).indexEquiv = f.indexEquiv.symm := rfl

/-- The transpose of the transpose of a morphism is the morphism. -/
theorem homDual_homDual (f : RootPairing.Hom P Q) : homDual (homDual f) = f := rfl

/-- The transpose of the identity morphism is the identity morphism of the dual. -/
theorem homDual_id (P : RootDatum ι X Y) :
    homDual (RootPairing.Hom.id P) = RootPairing.Hom.id (dual P) := rfl

/-- The transpose reverses the order of composition. -/
theorem homDual_comp (g : RootPairing.Hom Q S) (f : RootPairing.Hom P Q) :
    homDual (g.comp f) = (homDual f).comp (homDual g) := rfl

/-- The transpose of an isomorphism of root data $P \cong Q$, as an isomorphism $Q^\vee \cong P^\vee$. -/
def equivFlip (e : RootPairing.Equiv P Q) : RootPairing.Equiv (dual Q) (dual P) :=
  { homDual e.toHom with
    bijective_weightMap := e.bijective_coweightMap
    bijective_coweightMap := e.bijective_weightMap }

/-- An isomorphism of root data $P \cong Q$ gives an isomorphism of the dual root data $P^\vee \cong Q^\vee$: the transpose of the inverse. On the coweights it is the inverse of the transpose of the map of weights. -/
def equivDual (e : RootPairing.Equiv P Q) : RootPairing.Equiv (dual P) (dual Q) :=
  equivFlip (RootPairing.Equiv.symm P Q e)

/-- The map of weights of the dual isomorphism is the inverse of the map of coweights. -/
@[simp] theorem equivDual_weightMap (e : RootPairing.Equiv P Q) (y : Y) :
    (equivDual e).weightMap y = e.coweightEquiv.symm y := rfl

/-- The map of coweights of the dual isomorphism is the inverse of the map of weights. -/
@[simp] theorem equivDual_coweightMap (e : RootPairing.Equiv P Q) (x : X₂) :
    (equivDual e).coweightMap x = e.weightEquiv.symm x := rfl

/-- The dual isomorphism has the same bijection of index sets. -/
@[simp] theorem equivDual_indexEquiv (e : RootPairing.Equiv P Q) :
    (equivDual e).indexEquiv = e.indexEquiv := rfl

/-- The dual of the identity isomorphism is the identity isomorphism. -/
theorem equivDual_id (P : RootDatum ι X Y) :
    equivDual (RootPairing.Equiv.id P) = RootPairing.Equiv.id (dual P) := by
  ext y
  · exact (RootPairing.Equiv.id P).coweightEquiv.symm_apply_eq.2 rfl
  · exact (RootPairing.Equiv.id P).weightEquiv.symm_apply_eq.2 rfl
  · rfl

/-- The dual of a composition of isomorphisms is the composition of the duals, in the same order. -/
theorem equivDual_comp (g : RootPairing.Equiv Q S) (f : RootPairing.Equiv P Q) :
    equivDual (g.comp f) = (equivDual g).comp (equivDual f) := by
  ext y
  · apply (g.comp f).coweightEquiv.injective
    simp [RootPairing.Equiv.comp]
  · change (g.comp f).weightEquiv.symm y = f.weightEquiv.symm (g.weightEquiv.symm y)
    rw [LinearEquiv.symm_apply_eq]
    simp [RootPairing.Equiv.comp]
  · rfl

/-- The dual of the dual of an isomorphism is the isomorphism. -/
theorem equivDual_equivDual (e : RootPairing.Equiv P Q) : equivDual (equivDual e) = e := by
  ext x
  · apply (equivDual e).coweightEquiv.injective
    simp
  · apply (equivDual e).weightEquiv.injective
    simp
  · rfl

/-- The group homomorphism $\mathrm{Aut}(P) \to \mathrm{Aut}(P^\vee)$ that takes an automorphism to its dual automorphism. -/
def autDual (P : RootDatum ι X Y) : P.Aut →* (dual P).Aut where
  toFun := equivDual
  map_one' := equivDual_id P
  map_mul' g h := equivDual_comp g h

/-- The homomorphism `autDual` takes an automorphism to its dual isomorphism. -/
@[simp] theorem autDual_apply (P : RootDatum ι X Y) (g : P.Aut) : autDual P g = equivDual g := rfl

/-- The dual of the dual of an automorphism is the automorphism. -/
theorem autDual_autDual (P : RootDatum ι X Y) (g : P.Aut) :
    autDual (dual P) (autDual P g) = g :=
  equivDual_equivDual g

/-- An automorphism and its dual automorphism keep the pairing: $\langle g x, g^\vee y \rangle = \langle x, y \rangle$. -/
theorem pairing_weightMap_autDual (P : RootDatum ι X Y) (g : P.Aut) (x : X) (y : Y) :
    P.toLinearMap (g.weightMap x) ((autDual P g).weightMap y) = P.toLinearMap x y := by
  have h := LinearMap.congr_fun
    (RootPairing.Hom.weight_coweight_transpose_apply P P (g.coweightEquiv.symm y) g.toHom) x
  simp only [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap,
    LinearMap.flip_apply] at h
  rw [autDual_apply, equivDual_weightMap, h]
  congr 1
  exact g.coweightMap_coweightEquiv_symm y

/-- The isomorphism of root data with the identity maps that an equality of root data gives. -/
def equivOfEq {P Q : RootDatum ι X Y} (h : P = Q) : RootPairing.Equiv P Q where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by subst h; ext; simp
  root_weightMap := by subst h; rfl
  coroot_coweightMap := by subst h; rfl
  bijective_weightMap := bijective_id
  bijective_coweightMap := bijective_id

section GeneralLinear

variable {n : ℕ}

/-- The index set of the roots of $GL_n$: the pairs $(i, j)$ with $i \neq j$. -/
abbrev glIndex (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The vector $e_i - e_j$ of $\mathbb{Z}^n$. -/
def glRoot (i j : Fin n) : Fin n → ℤ := Pi.single i 1 - Pi.single j 1

/-- The coordinates of $e_i - e_j$. -/
theorem glRoot_apply (i j k : Fin n) :
    glRoot i j k = (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
  simp [glRoot, Pi.single_apply]

/-- The $i$-th coordinate of $e_i - e_j$ is $1$ for $i \neq j$. -/
theorem glRoot_apply_left {i j : Fin n} (h : i ≠ j) : glRoot i j i = 1 := by
  simp [glRoot_apply, h]

/-- The $j$-th coordinate of $e_i - e_j$ is $-1$ for $i \neq j$. -/
theorem glRoot_apply_right {i j : Fin n} (h : i ≠ j) : glRoot i j j = -1 := by
  simp [glRoot_apply, h.symm]

/-- The dot product of $x$ with $e_i - e_j$ is $x_i - x_j$. -/
theorem dotProduct_glRoot (x : Fin n → ℤ) (i j : Fin n) : x ⬝ᵥ glRoot i j = x i - x j := by
  simp [glRoot, dotProduct_sub, dotProduct_single]

/-- The vector $e_i - e_j$ with $i \neq j$ determines the pair $(i, j)$. -/
theorem glRoot_injective : Injective (fun p : glIndex n => glRoot p.1.1 p.1.2) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  simp only at h hij hkl
  have h1 := congr_fun h i
  have h2 := congr_fun h j
  simp only [glRoot_apply_left hij, glRoot_apply_right hij, glRoot_apply] at h1 h2
  have hik : i = k := by
    by_contra hik
    split_ifs at h1 <;> omega
  subst hik
  have hjl : j = l := by
    by_contra hjl
    split_ifs at h2 <;> simp_all
  subst hjl
  rfl

/-- The roots $e_i - e_j$ of $GL_n$, as an embedding of the index set into $\mathbb{Z}^n$. -/
def glRootEmb (n : ℕ) : glIndex n ↪ (Fin n → ℤ) :=
  ⟨fun p => glRoot p.1.1 p.1.2, glRoot_injective⟩

/-- The reflection $x \mapsto x - (x_i - x_j)(e_i - e_j)$ permutes the coordinates by the transposition of $i$ and $j$. -/
theorem sub_smul_glRoot (x : Fin n → ℤ) (i j : Fin n) :
    x - (x i - x j) • glRoot i j = x ∘ Equiv.swap i j := by
  funext m
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, glRoot_apply, comp_apply,
    Equiv.swap_apply_def]
  by_cases hmi : m = i
  · subst hmi
    by_cases hmj : m = j
    · subst hmj; simp
    · simp [hmj]
  · by_cases hmj : m = j
    · subst hmj; simp [hmi]
    · simp [hmi, hmj]

/-- A transposition $\sigma$ of the coordinates takes $e_k - e_l$ to $e_{\sigma(k)} - e_{\sigma(l)}$. -/
theorem glRoot_comp_swap (i j k l : Fin n) :
    glRoot k l ∘ Equiv.swap i j = glRoot (Equiv.swap i j k) (Equiv.swap i j l) := by
  funext m
  simp only [comp_apply, glRoot_apply]
  congr 1 <;> congr 1 <;> exact propext Equiv.swap_apply_eq_iff

/-- The permutation of the roots of $GL_n$ by the reflection in the root $e_i - e_j$: the transposition of $i$ and $j$ on both entries. -/
def glPerm (p : glIndex n) : glIndex n ≃ glIndex n :=
  (Equiv.prodCongr (Equiv.swap p.1.1 p.1.2) (Equiv.swap p.1.1 p.1.2)).subtypeEquiv
    (fun _ => (Equiv.swap p.1.1 p.1.2).injective.ne_iff.symm)

/-- The formula for the permutation `glPerm`. -/
theorem glPerm_apply (p q : glIndex n) :
    ((glPerm p q : glIndex n) : Fin n × Fin n) =
      (Equiv.swap p.1.1 p.1.2 q.1.1, Equiv.swap p.1.1 p.1.2 q.1.2) := rfl

/-- The reflection in the root $e_i - e_j$ takes $e_k - e_l$ to the root with index `glPerm p q`. -/
theorem glRoot_reflection (p q : glIndex n) :
    glRoot q.1.1 q.1.2 - (glRoot q.1.1 q.1.2 ⬝ᵥ glRoot p.1.1 p.1.2) • glRoot p.1.1 p.1.2 =
      glRoot (glPerm p q).1.1 (glPerm p q).1.2 := by
  rw [dotProduct_glRoot, sub_smul_glRoot, glRoot_comp_swap, glPerm_apply]

/-- The root datum of $GL_n$: the character lattice and the cocharacter lattice are $\mathbb{Z}^n$ with the dot product, the roots and the coroots are the vectors $e_i - e_j$ for $i \neq j$. -/
def gl (n : ℕ) : RootDatum (glIndex n) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin n)).toLinearMap
  isPerfPair_toLinearMap := inferInstance
  root := glRootEmb n
  coroot := glRootEmb n
  root_coroot_two p := by
    change glRoot p.1.1 p.1.2 ⬝ᵥ glRoot p.1.1 p.1.2 = 2
    rw [dotProduct_glRoot, glRoot_apply_left p.2, glRoot_apply_right p.2]
    rfl
  reflectionPerm := glPerm
  reflectionPerm_root p q := glRoot_reflection p q
  reflectionPerm_coroot p q := by
    change glRoot q.1.1 q.1.2 - (glRoot p.1.1 p.1.2 ⬝ᵥ glRoot q.1.1 q.1.2) • glRoot p.1.1 p.1.2 =
      glRoot (glPerm p q).1.1 (glPerm p q).1.2
    rw [dotProduct_comm]
    exact glRoot_reflection p q

/-- The pairing of the root datum of $GL_n$ is the dot product. -/
theorem gl_toLinearMap_apply (x y : Fin n → ℤ) : (gl n).toLinearMap x y = x ⬝ᵥ y := rfl

/-- The roots of $GL_n$ are the vectors $e_i - e_j$. -/
theorem gl_root (p : glIndex n) :
    (gl n).root p = Pi.single p.1.1 1 - Pi.single p.1.2 1 := rfl

/-- The coroots of $GL_n$ are the vectors $e_i - e_j$. -/
theorem gl_coroot (p : glIndex n) :
    (gl n).coroot p = Pi.single p.1.1 1 - Pi.single p.1.2 1 := rfl

/-- The Cartan integers of $GL_n$. -/
theorem gl_pairing (p q : glIndex n) :
    (gl n).pairing p q = glRoot p.1.1 p.1.2 q.1.1 - glRoot p.1.1 p.1.2 q.1.2 :=
  dotProduct_glRoot _ _ _

/-- The root datum of $GL_n$ is self-dual: its dual is equal to it. -/
theorem dual_gl (n : ℕ) : dual (gl n) = gl n := by
  apply RootPairing.ext
  · exact LinearMap.ext₂ fun x y => dotProduct_comm y x
  · rfl
  · rfl

/-- The isomorphism from the root datum of $GL_n$ to its dual. -/
def glDualEquiv (n : ℕ) : RootPairing.Equiv (gl n) (dual (gl n)) :=
  equivOfEq (dual_gl n).symm

/-- The simple roots $e_i - e_{i+1}$ of $GL_n$, as a set of indices. -/
def glSimple (n : ℕ) : Finset (glIndex n) := Finset.univ.filter fun p => p.1.2.val = p.1.1.val + 1

/-- An index is simple if and only if it is a pair $(i, i + 1)$. -/
theorem mem_glSimple {p : glIndex n} : p ∈ glSimple n ↔ p.1.2.val = p.1.1.val + 1 := by
  simp [glSimple]

/-- The linear map $x \mapsto (\sum_{m \le k} x_m)_k$ of $\mathbb{Z}^n$. It takes $e_i - e_{i+1}$ to $e_i$. -/
def glPartialSum (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun x k := ∑ m ∈ Finset.Iic k, x m
  map_add' x y := by
    funext k
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    funext k
    simp [Finset.mul_sum]

/-- The formula for the map `glPartialSum`. -/
theorem glPartialSum_apply (x : Fin n → ℤ) (k : Fin n) :
    glPartialSum n x k = ∑ m ∈ Finset.Iic k, x m := rfl

/-- The partial sum map takes the simple root $e_i - e_{i+1}$ to $e_i$. -/
theorem glPartialSum_glRoot {p : glIndex n} (hp : p ∈ glSimple n) :
    glPartialSum n (glRoot p.1.1 p.1.2) = Pi.single p.1.1 1 := by
  rw [mem_glSimple] at hp
  funext k
  simp only [glPartialSum_apply, glRoot_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_Iic, Pi.single_apply]
  simp only [Fin.le_def, Fin.ext_iff]
  split_ifs <;> omega

/-- The simple roots of $GL_n$ are linearly independent over $\mathbb{Z}$. -/
theorem gl_linearIndepOn_root : LinearIndepOn ℤ (gl n).root (glSimple n : Set (glIndex n)) := by
  apply LinearIndepOn.of_comp (glPartialSum n)
  have heq : Set.EqOn (glPartialSum n ∘ (gl n).root) (fun p => Pi.single p.1.1 (1 : ℤ))
      (glSimple n : Set (glIndex n)) := fun p hp => glPartialSum_glRoot hp
  refine LinearIndepOn.congr ?_ heq.symm
  have hinj : Injective (fun q : (glSimple n : Set (glIndex n)) => q.1.1.1) := by
    rintro ⟨⟨⟨i, j⟩, hij⟩, hq⟩ ⟨⟨⟨k, l⟩, hkl⟩, hq'⟩ h
    simp only [Finset.mem_coe, mem_glSimple] at hq hq' h
    subst h
    have : j = l := Fin.ext (by omega)
    subst this
    rfl
  have := (Pi.basisFun ℤ (Fin n)).linearIndependent.comp _ hinj
  rw [LinearIndepOn]
  convert this using 1
  funext q
  simp

/-- For $i < j$, the root $e_i - e_j$ is a sum of simple roots. -/
theorem glRoot_mem_closure (d : ℕ) : ∀ i j : Fin n, j.val = i.val + d + 1 →
    glRoot i j ∈ AddSubmonoid.closure ((gl n).root '' (glSimple n : Set (glIndex n))) := by
  induction d with
  | zero =>
    intro i j hij
    have hne : i ≠ j := fun h => by rw [h] at hij; omega
    exact AddSubmonoid.subset_closure
      ⟨⟨(i, j), hne⟩, by rw [Finset.mem_coe, mem_glSimple]; dsimp only; omega, rfl⟩
  | succ d ih =>
    intro i j hij
    let k : Fin n := ⟨i.val + d + 1, by omega⟩
    have hk : glRoot i j = glRoot i k + glRoot k j := by simp [glRoot]
    have hne : k ≠ j := fun h => by
      rw [Fin.ext_iff] at h
      simp only [k] at h
      omega
    rw [hk]
    exact add_mem (ih i k rfl) (AddSubmonoid.subset_closure
      ⟨⟨(k, j), hne⟩, by rw [Finset.mem_coe, mem_glSimple]; dsimp only [k]; omega, rfl⟩)

/-- Each root of $GL_n$ or its negative is a sum of simple roots. -/
theorem gl_root_mem_or_neg_mem (p : glIndex n) :
    (gl n).root p ∈ AddSubmonoid.closure ((gl n).root '' (glSimple n : Set (glIndex n))) ∨
      -(gl n).root p ∈ AddSubmonoid.closure ((gl n).root '' (glSimple n : Set (glIndex n))) := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  rcases lt_or_gt_of_ne hij with h | h
  · have h : i.val < j.val := h
    exact Or.inl (glRoot_mem_closure (j.val - i.val - 1) i j (by omega))
  · have h : j.val < i.val := h
    refine Or.inr ?_
    have hneg : -(gl n).root ⟨(i, j), hij⟩ = glRoot j i := by
      simp [gl_root, glRoot]
    rw [hneg]
    exact glRoot_mem_closure (i.val - j.val - 1) j i (by omega)

/-- The base of the root datum of $GL_n$ with the simple roots $e_i - e_{i+1}$. The simple coroots are the same vectors. -/
def glBase (n : ℕ) : (gl n).Base where
  support := glSimple n
  linearIndepOn_root := gl_linearIndepOn_root
  linearIndepOn_coroot := gl_linearIndepOn_root
  root_mem_or_neg_mem := gl_root_mem_or_neg_mem
  coroot_mem_or_neg_mem := gl_root_mem_or_neg_mem

/-- The simple roots of `glBase n` are the pairs $(i, i + 1)$. -/
theorem glBase_support (n : ℕ) : (glBase n).support = glSimple n := rfl

end GeneralLinear

section RankOne

/-- The multiplication $\mathbb{Z} \times \mathbb{Z} \to \mathbb{Z}$ is a perfect pairing. -/
theorem isPerfPair_mul : (LinearMap.mul ℤ ℤ).IsPerfPair := by
  refine LinearMap.IsPerfPair.of_bijective _ ⟨fun x y h => ?_, fun f => ⟨f 1, ?_⟩⟩
  · simpa using LinearMap.congr_fun h 1
  · ext
    simp

/-- A unit $u$ of $\mathbb{Z}$ satisfies $u^2 = 1$. -/
theorem units_mul_self (u : ℤˣ) : (u : ℤ) * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- The root datum of semisimple rank one with $X = Y = \mathbb{Z}$, the roots $\pm a$ and the coroots $\pm b$, where $a b = 2$. The index set is $\mathbb{Z}^\times = \{\pm 1\}$. -/
def rankOne (a b : ℤ) (h : a * b = 2) : RootDatum ℤˣ ℤ ℤ where
  toLinearMap := LinearMap.mul ℤ ℤ
  isPerfPair_toLinearMap := isPerfPair_mul
  root := ⟨fun u => a * u, fun u v huv => Units.ext <| mul_left_cancel₀ (by
    rintro rfl; simp at h) huv⟩
  coroot := ⟨fun u => b * u, fun u v huv => Units.ext <| mul_left_cancel₀ (by
    rintro rfl; simp at h) huv⟩
  root_coroot_two u := by
    change a * u * (b * u) = 2
    linear_combination (u : ℤ) * u * h + 2 * units_mul_self u
  reflectionPerm _ := Equiv.neg ℤˣ
  reflectionPerm_root u v := by
    change a * v - (a * v * (b * u)) * (a * u) = a * ((-v : ℤˣ) : ℤ)
    rw [Units.val_neg]
    linear_combination (-(a * v * u * u)) * h + (-2 * a * v) * units_mul_self u
  reflectionPerm_coroot u v := by
    change b * v - (a * u * (b * v)) * (b * u) = b * ((-v : ℤˣ) : ℤ)
    rw [Units.val_neg]
    linear_combination (-(b * v * u * u)) * h + (-2 * b * v) * units_mul_self u

/-- The pairing of the rank one root datum is the multiplication. -/
theorem rankOne_toLinearMap_apply (a b : ℤ) (h : a * b = 2) (x y : ℤ) :
    (rankOne a b h).toLinearMap x y = x * y := rfl

/-- The roots of the rank one root datum are $\pm a$. -/
theorem rankOne_root (a b : ℤ) (h : a * b = 2) (u : ℤˣ) : (rankOne a b h).root u = a * u := rfl

/-- The coroots of the rank one root datum are $\pm b$. -/
theorem rankOne_coroot (a b : ℤ) (h : a * b = 2) (u : ℤˣ) :
    (rankOne a b h).coroot u = b * u := rfl

/-- The dual of the rank one root datum with roots $\pm a$ and coroots $\pm b$ is the rank one root datum with roots $\pm b$ and coroots $\pm a$. -/
theorem dual_rankOne (a b : ℤ) (h : a * b = 2) :
    dual (rankOne a b h) = rankOne b a (by rw [mul_comm]; exact h) := by
  apply RootPairing.ext
  · exact LinearMap.ext₂ fun x y => mul_comm y x
  · rfl
  · rfl

/-- The base of the rank one root datum with the simple root $a$. -/
def rankOneBase (a b : ℤ) (h : a * b = 2) : (rankOne a b h).Base where
  support := {1}
  linearIndepOn_root := by
    rw [Finset.coe_singleton, linearIndepOn_singleton_iff, rankOne_root]
    rintro h'
    simp only [Units.val_one, mul_one] at h'
    subst h'
    simp at h
  linearIndepOn_coroot := by
    rw [Finset.coe_singleton, linearIndepOn_singleton_iff, rankOne_coroot]
    rintro h'
    simp only [Units.val_one, mul_one] at h'
    subst h'
    simp at h
  root_mem_or_neg_mem u := by
    have hmem : (rankOne a b h).root 1 ∈
        AddSubmonoid.closure ((rankOne a b h).root '' ((({1} : Finset ℤˣ)) : Set ℤˣ)) :=
      AddSubmonoid.subset_closure ⟨1, by simp, rfl⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Or.inl hmem
    · right
      convert hmem using 1
      simp [rankOne_root]
  coroot_mem_or_neg_mem u := by
    have hmem : (rankOne a b h).coroot 1 ∈
        AddSubmonoid.closure ((rankOne a b h).coroot '' ((({1} : Finset ℤˣ)) : Set ℤˣ)) :=
      AddSubmonoid.subset_closure ⟨1, by simp, rfl⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Or.inl hmem
    · right
      convert hmem using 1
      simp [rankOne_coroot]

/-- The simple root of `rankOneBase` has the index $1$. -/
theorem rankOneBase_support (a b : ℤ) (h : a * b = 2) : (rankOneBase a b h).support = {1} := rfl

/-- The root datum of $SL_2$: $X = \mathbb{Z}$, the root $2$ and the coroot $1$. -/
def sl2 : RootDatum ℤˣ ℤ ℤ := rankOne 2 1 (by norm_num)

/-- The root datum of $PGL_2$: $X = \mathbb{Z}$, the root $1$ and the coroot $2$. -/
def pgl2 : RootDatum ℤˣ ℤ ℤ := rankOne 1 2 (by norm_num)

/-- The roots of $SL_2$ are $\pm 2$. -/
theorem sl2_root (u : ℤˣ) : sl2.root u = 2 * u := rfl

/-- The coroots of $SL_2$ are $\pm 1$. -/
theorem sl2_coroot (u : ℤˣ) : sl2.coroot u = u := one_mul _

/-- The roots of $PGL_2$ are $\pm 1$. -/
theorem pgl2_root (u : ℤˣ) : pgl2.root u = u := one_mul _

/-- The coroots of $PGL_2$ are $\pm 2$. -/
theorem pgl2_coroot (u : ℤˣ) : pgl2.coroot u = 2 * u := rfl

/-- The base of the root datum of $SL_2$ with the simple root $2$. -/
def sl2Base : sl2.Base := rankOneBase 2 1 _

/-- The base of the root datum of $PGL_2$ with the simple root $1$. -/
def pgl2Base : pgl2.Base := rankOneBase 1 2 _

/-- The dual of the root datum of $SL_2$ is the root datum of $PGL_2$. -/
theorem dual_sl2 : dual sl2 = pgl2 := dual_rankOne 2 1 _

/-- The dual of the root datum of $PGL_2$ is the root datum of $SL_2$. -/
theorem dual_pgl2 : dual pgl2 = sl2 := dual_rankOne 1 2 _

/-- The isomorphism from the dual of the root datum of $SL_2$ to the root datum of $PGL_2$. -/
def sl2DualEquiv : RootPairing.Equiv (dual sl2) pgl2 := equivOfEq dual_sl2

/-- There is no morphism of root data from $SL_2$ to $PGL_2$ in the sense of Mathlib, because the image of the root $2$ is divisible by $2$ and the roots of $PGL_2$ are $\pm 1$. -/
theorem isEmpty_hom_sl2_pgl2 : IsEmpty (RootPairing.Hom sl2 pgl2) := by
  refine ⟨fun f => ?_⟩
  have h1 := RootPairing.Hom.root_weightMap_apply sl2 pgl2 1 f
  rw [sl2_root, pgl2_root, Units.val_one, mul_one] at h1
  have h2 : f.weightMap 2 = 2 * f.weightMap 1 := by
    simpa using f.weightMap.map_smul (2 : ℤ) (1 : ℤ)
  rcases Int.units_eq_one_or (f.indexEquiv 1) with h | h <;> rw [h] at h1 <;> simp at h1 <;> omega

/-- The root datum of $SL_2$ is not self-dual: it is not isomorphic to its dual. -/
theorem isEmpty_equiv_sl2_dual : IsEmpty (RootPairing.Equiv sl2 (dual sl2)) :=
  ⟨fun e => isEmpty_hom_sl2_pgl2.false ((sl2DualEquiv.comp e).toHom)⟩

end RankOne

section Torus

/-- The root datum of a split torus with no roots, for a perfect pairing $p : X \times Y \to \mathbb{Z}$ of the character lattice and the cocharacter lattice. -/
def torusOf (p : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) [p.IsPerfPair] : RootDatum Empty X Y where
  toLinearMap := p
  root := Embedding.ofIsEmpty
  coroot := Embedding.ofIsEmpty
  root_coroot_two i := i.elim
  reflectionPerm i := i.elim
  reflectionPerm_root i := i.elim
  reflectionPerm_coroot i := i.elim

/-- The dual of the root datum of the torus with the pairing $p$ is the root datum of the torus with the transposed pairing. This is an equality. -/
theorem dual_torusOf (p : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) [p.IsPerfPair] :
    dual (torusOf p) = torusOf p.flip := rfl

variable (X) in
/-- The root datum of the split torus with the character lattice $X$: the cocharacter lattice is the dual lattice $\mathrm{Hom}(X, \mathbb{Z})$ and there are no roots. -/
abbrev torus [IsReflexive ℤ X] : RootDatum Empty X (Dual ℤ X) := torusOf (Dual.eval ℤ X)

/-- The pairing of the torus root datum is the evaluation $\langle x, f \rangle = f(x)$. -/
theorem torus_toLinearMap_apply [IsReflexive ℤ X] (x : X) (f : Dual ℤ X) :
    (torus X).toLinearMap x f = f x := rfl

variable (X) in
/-- The dual of the torus with the character lattice $X$ is isomorphic to the torus with the character lattice $\mathrm{Hom}(X, \mathbb{Z})$. The map of coweights is the inverse of the canonical isomorphism $X \cong X^{\vee\vee}$. -/
def torusDualEquiv [IsReflexive ℤ X] :
    RootPairing.Equiv (dual (torus X)) (torus (Dual ℤ X)) where
  weightMap := LinearMap.id
  coweightMap := (evalEquiv ℤ X).symm.toLinearMap
  indexEquiv := Equiv.refl Empty
  weight_coweight_transpose := by
    ext φ f
    simp only [LinearMap.coe_comp, comp_apply, LinearMap.dualMap_apply, LinearMap.id_coe, id_eq,
      LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap, LinearMap.flip_apply,
      LinearEquiv.coe_coe]
    conv_lhs => rw [← (evalEquiv ℤ X).apply_symm_apply φ]
    rfl
  root_weightMap := funext fun i => i.elim
  coroot_coweightMap := funext fun i => i.elim
  bijective_weightMap := bijective_id
  bijective_coweightMap := LinearEquiv.bijective _

/-- A linear automorphism $g$ of $X$ as an automorphism of the torus root datum. The map of coweights is the transpose of $g$. -/
def torusEquivOf [IsReflexive ℤ X] (g : X ≃ₗ[ℤ] X) : (torus X).Aut where
  weightMap := g.toLinearMap
  coweightMap := g.toLinearMap.dualMap
  indexEquiv := Equiv.refl Empty
  weight_coweight_transpose := rfl
  root_weightMap := funext fun i => i.elim
  coroot_coweightMap := funext fun i => i.elim
  bijective_weightMap := g.bijective
  bijective_coweightMap := g.dualMap.bijective

variable (X) in
/-- The group homomorphism from the linear automorphisms of $X$ to the automorphisms of the torus root datum. -/
def torusAut [IsReflexive ℤ X] : (X ≃ₗ[ℤ] X) →* (torus X).Aut where
  toFun := torusEquivOf
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The map of weights of `torusAut X g` is $g$. -/
@[simp] theorem torusAut_weightMap [IsReflexive ℤ X] (g : X ≃ₗ[ℤ] X) (x : X) :
    (torusAut X g).weightMap x = g x := rfl

/-- The map of coweights of `torusAut X g` is the transpose of $g$. -/
@[simp] theorem torusAut_coweightMap [IsReflexive ℤ X] (g : X ≃ₗ[ℤ] X) (f : Dual ℤ X) :
    (torusAut X g).coweightMap f = f.comp g.toLinearMap := rfl

/-- The homomorphism `torusAut X` is injective. -/
theorem torusAut_injective [IsReflexive ℤ X] : Injective (torusAut X) := fun _ _ hgh =>
  LinearEquiv.ext fun x => congr_arg (fun e : (torus X).Aut => e.weightMap x) hgh

/-- The dual automorphism of $g$ acts on the dual lattice by the contragredient $f \mapsto f \circ g^{-1}$. -/
theorem autDual_torusAut_weightMap [IsReflexive ℤ X] (g : X ≃ₗ[ℤ] X) (f : Dual ℤ X) :
    (autDual (torus X) (torusAut X g)).weightMap f = f.comp g.symm.toLinearMap := by
  rw [autDual_apply, equivDual_weightMap, LinearEquiv.symm_apply_eq]
  ext x
  simp

/-- The base with no simple roots of a root datum with no roots. -/
def emptyBase (P : RootDatum Empty X Y) : P.Base where
  support := ∅
  linearIndepOn_root := by simp
  linearIndepOn_coroot := by simp
  root_mem_or_neg_mem i := i.elim
  coroot_mem_or_neg_mem i := i.elim

end Torus

end RootDatum

open RootDatum

/-- Two bases of a root datum with the same simple roots are equal. -/
theorem RootDatum.base_ext {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum ι X Y}
    {b b' : P.Base} (h : b.support = b'.support) : b = b' := by
  cases b
  cases b'
  cases h
  rfl

/-- The combinatorial datum of a quasi-split reductive group: a root datum, a base, and an action of a group $\Gamma$ on the root datum by automorphisms that keep the base. Later $\Gamma$ is the Weil group $W_F$ or the absolute Galois group of $F$. -/
structure QuasiSplitDatum (Γ : Type*) [Group Γ] (ι X Y : Type*) [AddCommGroup X]
    [AddCommGroup Y] where
  datum : RootDatum ι X Y
  base : datum.Base
  action : Γ →* datum.Aut
  mem_support_iff (γ : Γ) (i : ι) : (action γ).indexEquiv i ∈ base.support ↔ i ∈ base.support

namespace QuasiSplitDatum

variable {Γ : Type*} [Group Γ] {ι ι₂ ι₃ X Y X₂ Y₂ X₃ Y₃ : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X₂] [AddCommGroup Y₂] [AddCommGroup X₃] [AddCommGroup Y₃]

/-- The action of each element of $\Gamma$ takes the base to itself, in the sense of `RootPairing.Base.map`. -/
theorem map_base (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) : D.base.map (D.action γ) = D.base := by
  classical
  apply base_ext
  rw [RootPairing.Base.support_map_eq]
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (D.mem_support_iff γ j).2 hj
  · intro hi
    refine ⟨(D.action γ).indexEquiv.symm i, ?_, Equiv.apply_symm_apply _ _⟩
    rw [← D.mem_support_iff γ, Equiv.apply_symm_apply]
    exact hi

/-- The dual quasi-split datum: the dual root datum, the dual base, and the dual action $\gamma \mapsto (\gamma^{-1})^\vee$ of $\Gamma$. This is the combinatorial datum of the L-group ${}^L G = \hat G \rtimes \Gamma$. -/
def dual (D : QuasiSplitDatum Γ ι X Y) : QuasiSplitDatum Γ ι Y X where
  datum := RootDatum.dual D.datum
  base := D.base.flip
  action := (autDual D.datum).comp D.action
  mem_support_iff := D.mem_support_iff

/-- The root datum of the dual quasi-split datum is the dual root datum. -/
@[simp] theorem dual_datum (D : QuasiSplitDatum Γ ι X Y) : D.dual.datum = RootDatum.dual D.datum :=
  rfl

/-- The dual base has the same simple indices as the base. -/
@[simp] theorem dual_base_support (D : QuasiSplitDatum Γ ι X Y) :
    D.dual.base.support = D.base.support := rfl

/-- The dual action of $\gamma$ is the dual isomorphism of the action of $\gamma$. -/
theorem dual_action_apply (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) :
    D.dual.action γ = equivDual (D.action γ) := rfl

/-- The dual action of $\gamma$ on the cocharacter lattice $Y$ is the inverse of the map of coweights of the action of $\gamma$. -/
theorem dual_action_weightMap (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) (y : Y) :
    (D.dual.action γ).weightMap y = (D.action γ).coweightEquiv.symm y := rfl

/-- The dual action permutes the roots in the same way as the action. -/
theorem dual_action_indexEquiv (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) :
    (D.dual.action γ).indexEquiv = (D.action γ).indexEquiv := rfl

/-- The action and the dual action keep the pairing: $\langle \gamma x, \gamma^\vee y \rangle = \langle x, y \rangle$. -/
theorem pairing_action_dual_action (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) (x : X) (y : Y) :
    D.datum.toLinearMap ((D.action γ).weightMap x) ((D.dual.action γ).weightMap y) =
      D.datum.toLinearMap x y :=
  pairing_weightMap_autDual D.datum (D.action γ) x y

/-- The dual of the dual quasi-split datum is the original datum. This is an equality. -/
theorem dual_dual (D : QuasiSplitDatum Γ ι X Y) : D.dual.dual = D := by
  obtain ⟨P, b, a, h⟩ := D
  change QuasiSplitDatum.mk P b ((autDual (RootDatum.dual P)).comp ((autDual P).comp a)) _ = _
  congr 1
  exact MonoidHom.ext fun γ => autDual_autDual P (a γ)

/-- The map that takes a quasi-split datum to its dual is injective. -/
theorem dual_injective : Injective (dual : QuasiSplitDatum Γ ι X Y → QuasiSplitDatum Γ ι Y X) :=
  fun D E h => by rw [← dual_dual D, h, dual_dual]

/-- The quasi-split datum of a split group: the action of $\Gamma$ is trivial. -/
def split (P : RootDatum ι X Y) (b : P.Base) : QuasiSplitDatum Γ ι X Y where
  datum := P
  base := b
  action := 1
  mem_support_iff _ _ := Iff.rfl

/-- A quasi-split datum is split if the action of $\Gamma$ is trivial. -/
def IsSplit (D : QuasiSplitDatum Γ ι X Y) : Prop := D.action = 1

/-- The datum `split P b` is split. -/
theorem isSplit_split (P : RootDatum ι X Y) (b : P.Base) : (split (Γ := Γ) P b).IsSplit := rfl

/-- The dual of a split datum is the split datum of the dual root datum with the dual base. -/
theorem dual_split (P : RootDatum ι X Y) (b : P.Base) :
    (split (Γ := Γ) P b).dual = split (RootDatum.dual P) b.flip := by
  change QuasiSplitDatum.mk (RootDatum.dual P) b.flip ((autDual P).comp 1) _ = _
  congr 1
  exact MonoidHom.comp_one _

/-- The dual of a split datum is split. -/
theorem IsSplit.dual {D : QuasiSplitDatum Γ ι X Y} (h : D.IsSplit) : D.dual.IsSplit := by
  change (autDual D.datum).comp D.action = 1
  rw [show D.action = 1 from h]
  exact MonoidHom.comp_one _

/-- A quasi-split datum is split if and only if its dual is split. -/
theorem isSplit_dual_iff {D : QuasiSplitDatum Γ ι X Y} : D.dual.IsSplit ↔ D.IsSplit :=
  ⟨fun h => dual_dual D ▸ h.dual, IsSplit.dual⟩

/-- Two split data are equal if the root data are equal and the bases have the same simple indices. -/
theorem split_congr {P Q : RootDatum ι X Y} (h : P = Q) {b : P.Base} {b' : Q.Base}
    (hb : b.support = b'.support) : split (Γ := Γ) P b = split Q b' := by
  subst h
  rw [base_ext hb]

/-- The combinatorial datum of the L-group of a quasi-split group with the datum $D$: the dual based root datum of $\hat G$ with the induced action of $\Gamma$. It is the dual `QuasiSplitDatum.dual`. -/
abbrev lgroupDatum (D : QuasiSplitDatum Γ ι X Y) : QuasiSplitDatum Γ ι Y X := D.dual

/-- An isomorphism of quasi-split data: an isomorphism of root data that takes the base to the base and commutes with the actions of $\Gamma$. -/
@[ext]
structure Iso (D₁ : QuasiSplitDatum Γ ι X Y) (D₂ : QuasiSplitDatum Γ ι₂ X₂ Y₂) where
  toEquiv : RootPairing.Equiv D₁.datum D₂.datum
  mem_support_iff (i : ι) : toEquiv.indexEquiv i ∈ D₂.base.support ↔ i ∈ D₁.base.support
  comp_action (γ : Γ) : toEquiv.comp (D₁.action γ) = (D₂.action γ).comp toEquiv

namespace Iso

variable {D₁ : QuasiSplitDatum Γ ι X Y} {D₂ : QuasiSplitDatum Γ ι₂ X₂ Y₂}
  {D₃ : QuasiSplitDatum Γ ι₃ X₃ Y₃}

/-- The identity isomorphism of a quasi-split datum. -/
def refl (D : QuasiSplitDatum Γ ι X Y) : Iso D D where
  toEquiv := RootPairing.Equiv.id D.datum
  mem_support_iff _ := Iff.rfl
  comp_action γ := by
    rw [RootPairing.Equiv.comp_id, RootPairing.Equiv.id_comp]

/-- The composition of two isomorphisms of quasi-split data. -/
def trans (e : Iso D₁ D₂) (f : Iso D₂ D₃) : Iso D₁ D₃ where
  toEquiv := f.toEquiv.comp e.toEquiv
  mem_support_iff i := (f.mem_support_iff _).trans (e.mem_support_iff i)
  comp_action γ := by
    rw [RootPairing.Equiv.comp_assoc, e.comp_action, ← RootPairing.Equiv.comp_assoc,
      f.comp_action, RootPairing.Equiv.comp_assoc]

/-- An isomorphism of quasi-split data gives an isomorphism of the dual data. Thus the L-group datum is functorial for isomorphisms that commute with the actions. -/
def dual (e : Iso D₁ D₂) : Iso D₁.dual D₂.dual where
  toEquiv := equivDual e.toEquiv
  mem_support_iff := e.mem_support_iff
  comp_action γ := by
    have h1 := equivDual_comp e.toEquiv (D₁.action γ)
    have h2 := equivDual_comp (D₂.action γ) e.toEquiv
    rw [e.comp_action] at h1
    exact h1.symm.trans h2

/-- The isomorphism of root data that underlies the dual isomorphism. -/
@[simp] theorem dual_toEquiv (e : Iso D₁ D₂) : e.dual.toEquiv = equivDual e.toEquiv := rfl

/-- The dual of the identity isomorphism is the identity isomorphism. -/
theorem dual_refl (D : QuasiSplitDatum Γ ι X Y) : (refl D).dual = refl D.dual :=
  Iso.ext (equivDual_id D.datum)

/-- The dual of a composition is the composition of the duals. -/
theorem dual_trans (e : Iso D₁ D₂) (f : Iso D₂ D₃) : (e.trans f).dual = e.dual.trans f.dual :=
  Iso.ext (equivDual_comp f.toEquiv e.toEquiv)

/-- The dual of the dual of an isomorphism has the same underlying isomorphism of root data. -/
theorem dual_dual_toEquiv (e : Iso D₁ D₂) : e.dual.dual.toEquiv = e.toEquiv :=
  equivDual_equivDual e.toEquiv

end Iso

section Examples

/-- The L-group datum of split $GL_n$ is the split datum of $GL_n$. -/
theorem dual_split_gl (n : ℕ) :
    (split (Γ := Γ) (gl n) (glBase n)).dual = split (gl n) (glBase n) := by
  rw [dual_split]
  exact split_congr (dual_gl n) rfl

/-- The L-group datum of split $SL_2$ is the split datum of $PGL_2$. -/
theorem dual_split_sl2 :
    (split (Γ := Γ) sl2 sl2Base).dual = split pgl2 pgl2Base := by
  rw [dual_split]
  exact split_congr dual_sl2 rfl

/-- The L-group datum of split $PGL_2$ is the split datum of $SL_2$. -/
theorem dual_split_pgl2 :
    (split (Γ := Γ) pgl2 pgl2Base).dual = split sl2 sl2Base := by
  rw [dual_split]
  exact split_congr dual_pgl2 rfl

variable (X) in
/-- The quasi-split datum of a torus with the character lattice $X$ and an action $\rho$ of $\Gamma$ on $X$ by linear automorphisms. -/
def torus [IsReflexive ℤ X] (ρ : Γ →* (X ≃ₗ[ℤ] X)) : QuasiSplitDatum Γ Empty X (Dual ℤ X) where
  datum := RootDatum.torus X
  base := emptyBase _
  action := (torusAut X).comp ρ
  mem_support_iff _ i := i.elim

/-- The action of $\gamma$ on the character lattice of the torus is $\rho(\gamma)$. -/
theorem torus_action_weightMap [IsReflexive ℤ X] (ρ : Γ →* (X ≃ₗ[ℤ] X)) (γ : Γ) (x : X) :
    ((torus X ρ).action γ).weightMap x = ρ γ x := rfl

/-- The L-group of a torus: the dual action of $\gamma$ on the character lattice $\mathrm{Hom}(X, \mathbb{Z})$ of the dual torus is the contragredient $f \mapsto f \circ \rho(\gamma)^{-1}$. -/
theorem torus_dual_action_weightMap [IsReflexive ℤ X] (ρ : Γ →* (X ≃ₗ[ℤ] X)) (γ : Γ)
    (f : Dual ℤ X) :
    ((torus X ρ).dual.action γ).weightMap f = f.comp (ρ γ).symm.toLinearMap :=
  autDual_torusAut_weightMap (ρ γ) f

/-- The torus datum is split if and only if the action $\rho$ is trivial. -/
theorem torus_isSplit_iff [IsReflexive ℤ X] (ρ : Γ →* (X ≃ₗ[ℤ] X)) :
    (torus X ρ).IsSplit ↔ ρ = 1 := by
  constructor
  · intro h
    ext γ x
    have hγ := congr_arg (fun e : (RootDatum.torus X).Aut => e.weightMap x)
      (DFunLike.congr_fun h γ)
    exact hγ
  · rintro rfl
    exact MonoidHom.comp_one _

end Examples

end QuasiSplitDatum

end Langlands.Groups

end
