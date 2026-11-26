/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.Smooth

/-!
# The shapes of the statements for a general reductive group

The local Langlands conjecture for a general reductive group $G$ and the principle of functoriality need reductive groups over local and global fields, their L-groups as complex groups, and the L-parameters. Mathlib does not have these notions. The combinatorial part of the L-group is in `Langlands.Groups.RootDatum`, but the complex group $\hat G$ and the semidirect product ${}^L G = \hat G \rtimes W_F$ are not.

This file writes the shapes of the two statements early. The missing notions are fields of the structures `Langlands.Shapes.ReductiveGroupData` and `Langlands.Shapes.GlobalGroupData`. These structures are only interfaces: they do not construct the objects, and the conditions that make the fields correct are not in them. Thus `Langlands.Shapes.LocalLanglands` and `Langlands.Shapes.Functoriality` are shapes and not statements. They let the handbook and the map refer to the conjectures. The specification of the project counts them as G1b shapes and not as G1 statements.

## Main definitions

* `Langlands.Shapes.ReductiveGroupData`: the interface for a quasi-split connected reductive group over a nonarchimedean local field, with its L-parameters and their component groups.
* `Langlands.Shapes.IsLocalLanglandsMap`: the conditions of Borel on a map from $\mathrm{Irr}(G(K))$ to the L-parameters that this file can state with the interface.
* `Langlands.Shapes.LocalLanglands`: the shape of the local Langlands conjecture for $G$.
* `Langlands.Shapes.GlobalGroupData`: the interface for a reductive group over a global field, with its automorphic representations and their Satake parameters at the unramified places.
* `Langlands.Shapes.LHomData`: the interface for an L-homomorphism ${}^L H \to {}^L G$, through its effect on the unramified parameters.
* `Langlands.Shapes.Functoriality`: the shape of the principle of functoriality, in the weak form at the unramified places.

## Relation to the GL statements

For $G = GL_n$ the L-parameters are the Frobenius-semisimple Weil-Deligne representations of dimension $n$, and the component groups are trivial. The statement `Langlands.LocalLanglandsGL` is then a case of this shape, with more conditions. For $G = GL_n$ and $H = GL_m$ the statement `Langlands.FunctorialityGL` is a case of `Functoriality`.

## References

* A. Borel, *Automorphic L-functions*, Proc. Sympos. Pure Math. 33, part 2 (1979), sections 8 to 10.
* R. P. Langlands, *Problems in the theory of automorphic forms*, Lecture Notes in Math. 170 (1970).
* T. Kaletha, *The local Langlands conjectures for non-quasi-split groups*, section 2, for the internal structure of the packets.
-/

universe u

namespace Langlands.Shapes

/-- The interface for a quasi-split connected reductive group $G$ over a nonarchimedean local field $K$. The fields are the notions that the local Langlands conjecture uses. The interface does not construct them from $G$. The L-parameters are the admissible homomorphisms $W_K \times SL_2(\mathbb{C}) \to {}^L G$ up to conjugation by $\hat G$. The component group of a parameter $\varphi$ is the group $S_\varphi = \pi_0(Z_{\hat G}(\varphi) / Z(\hat G)^\Gamma)$. -/
structure ReductiveGroupData (K : Type u) where
  /-- The group $G(K)$ of the points of $G$. -/
  Points : Type u
  /-- The group structure on $G(K)$. -/
  [instGroup : Group Points]
  /-- The topology on $G(K)$. -/
  [instTop : TopologicalSpace Points]
  /-- The topological group $G(K)$. -/
  [instTopGroup : IsTopologicalGroup Points]
  /-- The L-parameters of $G$ up to conjugation by $\hat G$. -/
  LParam : Type u
  /-- The isomorphism classes of the irreducible representations of the component group $S_\varphi$ of a parameter $\varphi$. -/
  IrrComp : LParam → Type u
  /-- The trivial representation of $S_\varphi$. -/
  trivialComp : (φ : LParam) → IrrComp φ
  /-- An irreducible representation of $G(K)$ is tempered. -/
  IsTempered : IrrSmooth Points → Prop
  /-- An irreducible representation of $G(K)$ is in the discrete series. -/
  IsDiscreteSeries : IrrSmooth Points → Prop
  /-- An irreducible representation of $G(K)$ is generic for the fixed Whittaker datum. -/
  IsGeneric : IrrSmooth Points → Prop
  /-- A parameter is tempered: the image of $W_K$ is bounded. -/
  IsTemperedParam : LParam → Prop
  /-- A parameter is discrete: its image is in no proper Levi subgroup of ${}^L G$. -/
  IsDiscreteParam : LParam → Prop

attribute [instance] ReductiveGroupData.instGroup ReductiveGroupData.instTop
  ReductiveGroupData.instTopGroup

variable {K : Type u}

/-- The conditions of Borel on a map $L : \mathrm{Irr}(G(K)) \to \Phi(G)$ that the interface can express. The fibers, the L-packets, are finite and not empty, since $G$ is quasi-split. A packet is tempered or discrete exactly when its parameter is. The conditions on central characters, on twists and on the L-factors and ε-factors need more data, and they are not here. -/
structure IsLocalLanglandsMap (G : ReductiveGroupData K) (L : IrrSmooth G.Points → G.LParam) :
    Prop where
  /-- Each L-packet is finite. -/
  finite_fiber : ∀ φ, (L ⁻¹' {φ}).Finite
  /-- Each L-packet is not empty. This holds since $G$ is quasi-split. -/
  surjective : Function.Surjective L
  /-- A representation is tempered exactly when its parameter is tempered. -/
  tempered : ∀ x, G.IsTempered x ↔ G.IsTemperedParam (L x)
  /-- A representation is in the discrete series exactly when its parameter is discrete. -/
  discrete : ∀ x, G.IsDiscreteSeries x ↔ G.IsDiscreteParam (L x)

/-- **The shape of the local Langlands conjecture** for a quasi-split group $G$. There is a map $L : \mathrm{Irr}(G(K)) \to \Phi(G)$ with the conditions of `IsLocalLanglandsMap`, and for each parameter $\varphi$ an injective map $\iota_\varphi$ from the packet $\Pi_\varphi$ to $\mathrm{Irr}(S_\varphi)$. If $\varphi$ is tempered, $\iota_\varphi$ sends each generic member of $\Pi_\varphi$ to the trivial representation. This is the form of Shahidi's conjecture. The maps $\iota_\varphi$ are bijective only for the union of the packets over the pure inner forms of $G$, so for $G$ alone the statement asks for injective maps. The character identities, which characterize $L$ and $\iota$, are not here. -/
def LocalLanglands (G : ReductiveGroupData K) : Prop :=
  ∃ (L : IrrSmooth G.Points → G.LParam) (ι : ∀ φ, L ⁻¹' {φ} → G.IrrComp φ),
    IsLocalLanglandsMap G L ∧ (∀ φ, Function.Injective (ι φ)) ∧
      ∀ φ, G.IsTemperedParam φ → ∀ x : L ⁻¹' {φ}, G.IsGeneric x.1 → ι φ x = G.trivialComp φ

/-- The interface for a connected reductive group $G$ over a global field $F$, with the set of places of $F$ as the index type `Place`. The fields are the automorphic representations of $G(\mathbb{A}_F)$, the places where such a representation is unramified, and its Satake parameter there. The unramified parameters at $v$ are the semisimple $\hat G$-conjugacy classes in $\hat G \rtimes \mathrm{Frob}_v$. -/
structure GlobalGroupData (Place : Type u) where
  /-- The automorphic representations of $G(\mathbb{A}_F)$, up to isomorphism. -/
  AutRep : Type u
  /-- The unramified parameters of $G$ at the place $v$. -/
  UnramParam : Place → Type u
  /-- The automorphic representation $\pi$ is unramified at $v$. -/
  IsUnramifiedAt : AutRep → Place → Prop
  /-- The Satake parameter of $\pi_v$ at a place where $\pi$ is unramified. -/
  satake : (π : AutRep) → (v : Place) → IsUnramifiedAt π v → UnramParam v
  /-- Each automorphic representation is unramified at almost all places. -/
  finite_ramified : ∀ π, {v | ¬ IsUnramifiedAt π v}.Finite

/-- The interface for an L-homomorphism $r : {}^L H \to {}^L G$ between two groups over the same global field. Only its effect on the unramified parameters is here: at a place $v$ where $H$, $G$ and $r$ are unramified, $r$ sends the class of $s \rtimes \mathrm{Frob}_v$ to the class of $r(s \rtimes \mathrm{Frob}_v)$. -/
structure LHomData {Place : Type u} (H G : GlobalGroupData Place) where
  /-- The map on the unramified parameters at $v$. -/
  onUnram : ∀ v, H.UnramParam v → G.UnramParam v

/-- **The shape of the principle of functoriality** (Langlands), in the weak form at the unramified places. For each automorphic representation $\pi$ of $H$ there is an automorphic representation $\Pi$ of $G$, named `σ` in the code, and a finite set $S$ of places such that, at each place $v \notin S$ where both are unramified, the Satake parameter of $\Pi_v$ is the image under $r$ of the Satake parameter of $\pi_v$. The strong form asks for the compatibility at all places through the local Langlands correspondence. For $GL_n \to GL_m$ this is `Langlands.FunctorialityGL`. -/
def Functoriality {Place : Type u} (H G : GlobalGroupData Place) (r : LHomData H G) : Prop :=
  ∀ π : H.AutRep, ∃ (σ : G.AutRep) (S : Set Place), S.Finite ∧
    ∀ v ∉ S, ∀ (hπ : H.IsUnramifiedAt π v) (hσ : G.IsUnramifiedAt σ v),
      G.satake σ v hσ = r.onUnram v (H.satake π v hπ)

end Langlands.Shapes
