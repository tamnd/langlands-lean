/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.Smooth
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Intertwining

/-!
# Smooth induction and Jacquet modules

Let $G$ be a topological group. This file develops the basic theory of the smooth representations of `Langlands/Statements/Smooth.lean`: smooth vectors, quotients, smooth induction with Frobenius reciprocity, and Jacquet modules with their universal property. At the end it gives the Borel subgroup $B$, its unipotent radical $N$ and the diagonal torus $T$ of $GL_2(K)$, and the principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ as a smooth induced representation.

For a subgroup $H$ of $G$ and a smooth representation $(\sigma, W)$ of $H$, the smoothly induced representation $\mathrm{Ind}_H^G \sigma$ is the space of the functions $f : G \to W$ with $f(hg) = \sigma(h) f(g)$ for each $h \in H$ that are invariant on the right under an open subgroup of $G$. The group $G$ acts by right translation $(g \cdot f)(x) = f(xg)$.

For two subgroups $M$ and $N$ of $G$ such that $M$ normalizes $N$, the Jacquet module of a smooth representation $(\pi, V)$ of $G$ is $V_N = V / V(N)$, where $V(N)$ is the span of the vectors $\pi(n) v - v$. It is a smooth representation of $M$. For a parabolic subgroup $P = MN$, $M$ is a Levi subgroup and $N$ is the unipotent radical.

## Main definitions

* `Langlands.SmoothRep.smoothPart`: the subrepresentation on the smooth vectors.
* `Langlands.SmoothRep.prod`: the direct sum $\pi \oplus \pi'$.
* `Langlands.SmoothRep.quotient`: the quotient $V / W$ by a stable subspace $W$.
* `Langlands.rightTranslation`: the right translation on the functions $G \to W$.
* `Langlands.indSpace`, `Langlands.SmoothRep.ind`: the smoothly induced representation $\mathrm{Ind}_H^G \sigma$.
* `Langlands.SmoothRep.indMap`: the map $\mathrm{Ind}_H^G \sigma \to \mathrm{Ind}_H^G \sigma'$ that a map $\sigma \to \sigma'$ gives.
* `Langlands.SmoothRep.frobenius`: the Frobenius isomorphism $\mathrm{Hom}_G(\pi, \mathrm{Ind}_H^G \sigma) \cong \mathrm{Hom}_H(\pi|_H, \sigma)$.
* `Langlands.SmoothRep.jacquetKer`: the subspace $V(N)$.
* `Langlands.SmoothRep.jacquet`: the Jacquet module $V_N$ as a smooth representation of $M$.
* `Langlands.SmoothRep.nInvariantHom`: the $M$-maps $V \to \tau$ that are invariant under $N$.
* `Langlands.SmoothRep.jacquetEquiv`: the isomorphism $\mathrm{Hom}_M(V_N, \tau) \cong$ `nInvariantHom`.
* `Langlands.SmoothRep.jacquetMap`: the map $V_N \to V'_N$ that a map $V \to V'$ gives.
* `Langlands.GL2.borel`, `Langlands.GL2.unipotent`, `Langlands.GL2.torus`: the subgroups $B$, $N$ and $T$ of $GL_2(K)$.
* `Langlands.GL2.borelChar`: the character $\chi_1 \otimes \chi_2$ of $B$.
* `Langlands.principalSeriesInd`: the principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$.
* `Langlands.principalSeriesJacquet`: its Jacquet module, as a smooth representation of $T$.

## Main results

* `Langlands.isSmooth_smoothVectors`, `Langlands.isGreatest_smoothVectors`: the smooth vectors form the largest stable subspace on which the representation is smooth.
* `Langlands.isSmooth_sup`: the sum of two smooth stable subspaces is smooth.
* `Langlands.SmoothRep.IsAdmissible.sub`: a subrepresentation of an admissible representation is admissible.
* `Langlands.SmoothRep.frobenius`: Frobenius reciprocity, as a linear isomorphism, for each smooth $\pi$.
* `Langlands.SmoothRep.indMap_injective`: smooth induction keeps injections.
* `Langlands.SmoothRep.jacquetKer_stable`: $V(N)$ is stable under $M$.
* `Langlands.SmoothRep.jacquetEquiv`: the universal property of the Jacquet module, as a linear isomorphism.
* `Langlands.SmoothRep.jacquetMap_surjective`: the Jacquet functor keeps surjections.
* `Langlands.GL2.conj_mem_unipotent`, `Langlands.GL2.borel_le_normalizer_unipotent`: $B$ normalizes $N$.
* `Langlands.GL2.isOpen_ker_borelChar`: for smooth characters $\chi_1, \chi_2$, the character $\chi_1 \otimes \chi_2$ of $B$ is smooth.

## Implementation notes

The maps of representations are the terms of `Representation.IntertwiningMap` of Mathlib, which form a complex vector space. The restriction of $\pi$ to a subgroup $H$ is the representation `π.ρ.comp H.subtype` on the same space $V$, so that a map $\pi|_H \to \sigma$ is a linear map $V \to W$.

The definition of $\mathrm{Ind}_H^G \sigma$ and the proof of Frobenius reciprocity do not use that $H$ is closed, so the file does not assume it. The condition that $M$ normalizes $N$ is the hypothesis `M ≤ Subgroup.normalizer N`. The induction is not normalized: the principal series of this file is $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ without the factor $\delta_B^{1/2}$.

## References

* I. N. Bernstein, A. V. Zelevinsky, Representations of the group GL(n, F) where F is a non-archimedean local field, Russian Math. Surveys 31 (1976).
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapters 1 and 2.
* W. Casselman, Introduction to the theory of admissible representations of p-adic reductive groups, unpublished notes, 1995.
-/

namespace Langlands

universe u v

open Representation

section SmoothVectors

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The stabilizer of a vector of a subrepresentation is the stabilizer of the vector in the ambient representation. -/
theorem vecStabilizer_subrepresentation (ρ : Representation ℂ G V) (W : Submodule ℂ V)
    (hW : IsStableSubspace ρ W) (w : W) :
    vecStabilizer (ρ.subrepresentation W hW) w = vecStabilizer ρ w := by
  ext g
  rw [mem_vecStabilizer, mem_vecStabilizer, ← Subtype.coe_inj]
  rfl

/-- The representation on the smooth vectors is smooth. -/
theorem isSmooth_smoothVectors (ρ : Representation ℂ G V) :
    IsSmooth (ρ.subrepresentation (smoothVectors ρ) (smoothVectors_stable ρ)) := by
  intro w
  rw [vecStabilizer_subrepresentation]
  exact w.2

/-- Each stable subspace on which the representation is smooth is contained in the smooth vectors. -/
theorem le_smoothVectors (ρ : Representation ℂ G V) {W : Submodule ℂ V}
    (hW : IsStableSubspace ρ W) (h : IsSmooth (ρ.subrepresentation W hW)) :
    W ≤ smoothVectors ρ := by
  intro w hw
  have := h ⟨w, hw⟩
  rwa [vecStabilizer_subrepresentation] at this

/-- The smooth vectors are the largest stable subspace on which the representation is smooth. -/
theorem isGreatest_smoothVectors (ρ : Representation ℂ G V) :
    IsGreatest {W : Submodule ℂ V | ∃ hW : IsStableSubspace ρ W,
      IsSmooth (ρ.subrepresentation W hW)} (smoothVectors ρ) :=
  ⟨⟨smoothVectors_stable ρ, isSmooth_smoothVectors ρ⟩,
    fun _ ⟨hW, h⟩ => le_smoothVectors ρ hW h⟩

/-- The sum $W_1 + W_2$ of two stable subspaces on which the representation is smooth is again smooth. -/
theorem isSmooth_sup (ρ : Representation ℂ G V) {W₁ W₂ : Submodule ℂ V}
    (h₁ : IsStableSubspace ρ W₁) (h₂ : IsStableSubspace ρ W₂) (h : IsStableSubspace ρ (W₁ ⊔ W₂))
    (hs₁ : IsSmooth (ρ.subrepresentation W₁ h₁)) (hs₂ : IsSmooth (ρ.subrepresentation W₂ h₂)) :
    IsSmooth (ρ.subrepresentation (W₁ ⊔ W₂) h) := by
  intro w
  rw [vecStabilizer_subrepresentation]
  exact sup_le (le_smoothVectors ρ h₁ hs₁) (le_smoothVectors ρ h₂ hs₂) w.2

/-- A representation is smooth exactly when each vector is smooth. -/
theorem smoothVectors_eq_top_iff (ρ : Representation ℂ G V) :
    smoothVectors ρ = ⊤ ↔ IsSmooth ρ := by
  rw [eq_top_iff]
  exact ⟨fun h v => h (Submodule.mem_top (x := v)), fun h v _ => h v⟩

end SmoothVectors

namespace SmoothRep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smooth part of a representation: the subrepresentation on the smooth vectors. -/
def smoothPart {V : Type u} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : SmoothRep G where
  V := smoothVectors ρ
  ρ := ρ.subrepresentation _ (smoothVectors_stable ρ)
  smooth := isSmooth_smoothVectors ρ

/-- The direct sum $\pi \oplus \pi'$ of two smooth representations, on $V \times V'$. -/
noncomputable def prod (π π' : SmoothRep G) : SmoothRep G where
  V := π.V × π'.V
  ρ := π.ρ.prod π'.ρ
  smooth v := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ v.1 ⊓ vecStabilizer π'.ρ v.2) ?_
      ((π.smooth v.1).inter (π'.smooth v.2))
    intro g hg
    rw [Subgroup.mem_inf, mem_vecStabilizer, mem_vecStabilizer] at hg
    rw [mem_vecStabilizer]
    exact Prod.ext hg.1 hg.2

/-- The quotient $V / W$ of a smooth representation by a stable subspace $W$. -/
def quotient (π : SmoothRep G) (W : Submodule ℂ π.V) (hW : IsStableSubspace π.ρ W) :
    SmoothRep G where
  V := π.V ⧸ W
  ρ := π.ρ.quotient W hW
  smooth x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ v) ?_ (π.smooth v)
    intro g hg
    rw [mem_vecStabilizer] at hg ⊢
    change Submodule.Quotient.mk (π.ρ g v) = _
    rw [hg]

/-- A subrepresentation of an admissible representation is admissible. -/
theorem IsAdmissible.sub {π : SmoothRep G} (hπ : π.IsAdmissible) (W : Submodule ℂ π.V)
    (hW : IsStableSubspace π.ρ W) : (π.sub W hW).IsAdmissible := by
  intro U hU
  have := hπ U hU
  let f : fixedVectors (π.sub W hW).ρ U →ₗ[ℂ] fixedVectors π.ρ U :=
    { toFun := fun w => ⟨(show W from w.1).1, fun g hg => congrArg Subtype.val (w.2 g hg)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun a b hab => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun x : fixedVectors π.ρ U => (x : π.V)) hab))

end SmoothRep

section Induction

variable {G : Type u} [Group G]

/-- The right translation $(g \cdot f)(x) = f(xg)$ on the functions $G \to W$. -/
def rightTranslation (G : Type u) [Group G] (W : Type v) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ G (G → W) where
  toFun g :=
    { toFun := fun f x => f (x * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

/-- The value of a right translate: $(g \cdot f)(x) = f(xg)$. -/
theorem rightTranslation_apply {W : Type v} [AddCommGroup W] [Module ℂ W] (g : G) (f : G → W)
    (x : G) : rightTranslation G W g f x = f (x * g) :=
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation $x \mapsto g x g^{-1}$ is continuous, so the conjugate $g^{-1} U g$ of an open subgroup is open. -/
theorem isOpen_comap_conj {U : Subgroup G} (hU : IsOpen (U : Set G)) (g : G) :
    IsOpen ((U.comap (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hc : Continuous (MulAut.conj g).toMonoidHom := by
    change Continuous fun x => g * x * g⁻¹
    fun_prop
  rw [Subgroup.coe_comap]
  exact hc.isOpen_preimage _ hU

/-- The space of the smoothly induced representation $\mathrm{Ind}_H^G \sigma$: the functions $f : G \to V_\sigma$ with $f(hg) = \sigma(h) f(g)$ for each $h \in H$, that are invariant on the right under an open subgroup of $G$. -/
def indSpace (H : Subgroup G) (σ : SmoothRep H) : Submodule ℂ (G → σ.V) where
  carrier := {f | (∀ (h : H) (g : G), f (h * g) = σ.ρ h (f g)) ∧
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, f (g * u) = f g}
  add_mem' {f f'} hf hf' := by
    refine ⟨fun h g => ?_, ?_⟩
    · simp only [Pi.add_apply, hf.1 h g, hf'.1 h g, map_add]
    · obtain ⟨U, hU, hfU⟩ := hf.2
      obtain ⟨U', hU', hfU'⟩ := hf'.2
      exact ⟨U ⊓ U', hU.inter hU', fun g u hu => by
        simp [hfU g u (Subgroup.mem_inf.1 hu).1, hfU' g u (Subgroup.mem_inf.1 hu).2]⟩
  zero_mem' := ⟨fun _ _ => by simp, ⊤, by simp, fun _ _ _ => rfl⟩
  smul_mem' c f hf := by
    refine ⟨fun h g => ?_, ?_⟩
    · simp only [Pi.smul_apply, hf.1 h g, map_smul]
    · obtain ⟨U, hU, hfU⟩ := hf.2
      exact ⟨U, hU, fun g u hu => by simp [hfU g u hu]⟩

/-- The space $\mathrm{Ind}_H^G \sigma$ is stable under right translation. -/
theorem indSpace_stable (H : Subgroup G) (σ : SmoothRep H) :
    IsStableSubspace (rightTranslation G σ.V) (indSpace H σ) := by
  intro g f hf
  refine ⟨fun h x => ?_, ?_⟩
  · change f (h * x * g) = σ.ρ h (f (x * g))
    rw [mul_assoc, hf.1 h (x * g)]
  · obtain ⟨U, hU, hfU⟩ := hf.2
    refine ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, isOpen_comap_conj hU _, fun x u hu => ?_⟩
    change f (x * u * g) = f (x * g)
    have := hfU (x * g) _ (Subgroup.mem_comap.1 hu)
    simpa [mul_assoc] using this

namespace SmoothRep

/-- The smoothly induced representation $\mathrm{Ind}_H^G \sigma$ of a smooth representation $\sigma$ of a subgroup $H$, with $G$ acting by right translation. In the usual theory $H$ is closed, but the definition and Frobenius reciprocity do not use this. -/
def ind (H : Subgroup G) (σ : SmoothRep H) : SmoothRep G where
  V := indSpace H σ
  ρ := (rightTranslation G σ.V).subrepresentation _ (indSpace_stable H σ)
  smooth f := by
    obtain ⟨U, hU, hfU⟩ := f.2.2
    refine Subgroup.isOpen_mono (H₁ := U) ?_ hU
    intro u hu
    rw [mem_vecStabilizer]
    exact Subtype.ext (funext fun g => hfU g u hu)

/-- The function $G \to V_\sigma$ of a vector of $\mathrm{Ind}_H^G \sigma$. -/
def ind.toFun {H : Subgroup G} {σ : SmoothRep H} (f : (ind H σ).V) : G → σ.V :=
  (show indSpace H σ from f).1

/-- A vector $f$ of $\mathrm{Ind}_H^G \sigma$ satisfies $f(hg) = \sigma(h) f(g)$. -/
theorem ind.toFun_mul_left {H : Subgroup G} {σ : SmoothRep H} (f : (ind H σ).V) (h : H) (g : G) :
    ind.toFun f (h * g) = σ.ρ h (ind.toFun f g) :=
  (show indSpace H σ from f).2.1 h g

/-- The group $G$ acts on $\mathrm{Ind}_H^G \sigma$ by right translation. -/
theorem ind.toFun_ρ {H : Subgroup G} {σ : SmoothRep H} (f : (ind H σ).V) (g x : G) :
    ind.toFun ((ind H σ).ρ g f) x = ind.toFun f (x * g) :=
  rfl

/-- A vector of $\mathrm{Ind}_H^G \sigma$ is determined by its function. -/
theorem ind.toFun_injective {H : Subgroup G} {σ : SmoothRep H} :
    Function.Injective (ind.toFun : (ind H σ).V → G → σ.V) :=
  fun _ _ h => Subtype.ext h

/-- The vector $g \mapsto \varphi(\pi(g) v)$ of $\mathrm{Ind}_H^G \sigma$ that an $H$-map $\varphi : \pi|_H \to \sigma$ gives. -/
def frobeniusVec (π : SmoothRep G) {H : Subgroup G} {σ : SmoothRep H}
    (φ : IntertwiningMap (π.ρ.comp H.subtype) σ.ρ) (v : π.V) : (ind H σ).V :=
  show indSpace H σ from
  ⟨fun g => φ (π.ρ g v), fun h g => by
      change φ (π.ρ ((h : G) * g) v) = _
      rw [map_mul, Module.End.mul_apply]
      exact IntertwiningMap.isIntertwining (π.ρ.comp H.subtype) σ.ρ φ h (π.ρ g v),
    ⟨vecStabilizer π.ρ v, π.smooth v, fun g u hu => by
      change φ (π.ρ (g * u) v) = φ (π.ρ g v)
      rw [map_mul, Module.End.mul_apply, (mem_vecStabilizer _ _ _).1 hu]⟩⟩

/-- The function of `frobeniusVec` is $g \mapsto \varphi(\pi(g) v)$. -/
theorem frobeniusVec_toFun (π : SmoothRep G) {H : Subgroup G} {σ : SmoothRep H}
    (φ : IntertwiningMap (π.ρ.comp H.subtype) σ.ρ) (v : π.V) (g : G) :
    ind.toFun (π.frobeniusVec φ v) g = φ (π.ρ g v) :=
  rfl

/-- Frobenius reciprocity for smooth induction: for a smooth representation $\pi$ of $G$ and a smooth representation $\sigma$ of a subgroup $H$, the map $\Phi \mapsto (v \mapsto \Phi(v)(1))$ is a linear isomorphism $\mathrm{Hom}_G(\pi, \mathrm{Ind}_H^G \sigma) \cong \mathrm{Hom}_H(\pi|_H, \sigma)$. The inverse sends $\varphi$ to $v \mapsto (g \mapsto \varphi(\pi(g) v))$. -/
def frobenius (π : SmoothRep G) (H : Subgroup G) (σ : SmoothRep H) :
    IntertwiningMap π.ρ (ind H σ).ρ ≃ₗ[ℂ]
      IntertwiningMap (π.ρ.comp H.subtype) σ.ρ where
  toFun Φ :=
    { toFun := fun v => ind.toFun (Φ v) 1
      map_add' := fun v w => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [map_smul]; rfl
      isIntertwining' := fun h => by
        ext v
        change ind.toFun (Φ (π.ρ h v)) 1 = σ.ρ h (ind.toFun (Φ v) 1)
        rw [Φ.isIntertwining, ind.toFun_ρ, one_mul, ← mul_one (h : G), ind.toFun_mul_left] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ :=
    { toFun := π.frobeniusVec φ
      map_add' := fun v w => ind.toFun_injective (funext fun g => by
        change φ (π.ρ g (v + w)) = φ (π.ρ g v) + φ (π.ρ g w)
        simp)
      map_smul' := fun c v => ind.toFun_injective (funext fun g => by
        change φ (π.ρ g (c • v)) = c • φ (π.ρ g v)
        simp)
      isIntertwining' := fun g => by
        ext v
        refine ind.toFun_injective (funext fun x => ?_)
        change φ (π.ρ x (π.ρ g v)) = φ (π.ρ (x * g) v)
        rw [map_mul, Module.End.mul_apply] }
  left_inv Φ := by
    ext v
    refine ind.toFun_injective (funext fun g => ?_)
    change ind.toFun (Φ (π.ρ g v)) 1 = ind.toFun (Φ v) g
    rw [Φ.isIntertwining, ind.toFun_ρ, one_mul]
  right_inv φ := by
    ext v
    change φ (π.ρ 1 v) = φ v
    rw [map_one, Module.End.one_apply]

/-- The Frobenius isomorphism is evaluation at $1$. -/
theorem frobenius_apply (π : SmoothRep G) (H : Subgroup G) (σ : SmoothRep H)
    (Φ : IntertwiningMap π.ρ (ind H σ).ρ) (v : π.V) :
    π.frobenius H σ Φ v = ind.toFun (Φ v) 1 :=
  rfl

/-- The inverse Frobenius isomorphism sends $\varphi$ to $v \mapsto (g \mapsto \varphi(\pi(g) v))$. -/
theorem frobenius_symm_apply (π : SmoothRep G) (H : Subgroup G) (σ : SmoothRep H)
    (φ : IntertwiningMap (π.ρ.comp H.subtype) σ.ρ) (v : π.V) (g : G) :
    ind.toFun ((π.frobenius H σ).symm φ v) g = φ (π.ρ g v) :=
  rfl

/-- The map $\mathrm{Ind}_H^G \sigma \to \mathrm{Ind}_H^G \sigma'$, $F \mapsto f \circ F$, that a map $f : \sigma \to \sigma'$ gives. -/
def indMap {H : Subgroup G} {σ σ' : SmoothRep H} (f : IntertwiningMap σ.ρ σ'.ρ) :
    IntertwiningMap (ind H σ).ρ (ind H σ').ρ where
  toFun F := show indSpace H σ' from
    ⟨fun g => f (ind.toFun F g), fun h g => by
        change f (ind.toFun F (h * g)) = σ'.ρ h (f (ind.toFun F g))
        rw [ind.toFun_mul_left]
        exact IntertwiningMap.isIntertwining σ.ρ σ'.ρ f h (ind.toFun F g),
      by
        obtain ⟨U, hU, hFU⟩ := (show indSpace H σ from F).2.2
        exact ⟨U, hU, fun g u hu => by
          change f (ind.toFun F (g * u)) = f (ind.toFun F g)
          rw [show ind.toFun F (g * u) = ind.toFun F g from hFU g u hu]⟩⟩
  map_add' F F' := ind.toFun_injective (funext fun g => by
    change f (ind.toFun (F + F') g) = f (ind.toFun F g) + f (ind.toFun F' g)
    rw [← map_add]
    rfl)
  map_smul' c F := ind.toFun_injective (funext fun g => by
    change f (ind.toFun (c • F) g) = c • f (ind.toFun F g)
    rw [← map_smul]
    rfl)
  isIntertwining' g := by
    ext F
    exact ind.toFun_injective (funext fun x => rfl)

/-- The map `indMap f` is composition with $f$. -/
theorem indMap_toFun {H : Subgroup G} {σ σ' : SmoothRep H} (f : IntertwiningMap σ.ρ σ'.ρ)
    (F : (ind H σ).V) (g : G) : ind.toFun (indMap f F) g = f (ind.toFun F g) :=
  rfl

/-- Smooth induction keeps injections: if $f : \sigma \to \sigma'$ is injective, then so is $\mathrm{Ind}_H^G f$. -/
theorem indMap_injective {H : Subgroup G} {σ σ' : SmoothRep H} (f : IntertwiningMap σ.ρ σ'.ρ)
    (hf : Function.Injective f) : Function.Injective (indMap f) := by
  intro F F' h
  refine ind.toFun_injective (funext fun g => hf ?_)
  rw [← indMap_toFun, ← indMap_toFun, h]

end SmoothRep

end Induction

section Jacquet

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- The subspace $V(N)$ of a smooth representation: the span of the vectors $\pi(n) v - v$ for $n \in N$ and $v \in V$. -/
def jacquetKer (π : SmoothRep G) (N : Subgroup G) : Submodule ℂ π.V :=
  Coinvariants.ker (π.ρ.comp N.subtype)

omit [IsTopologicalGroup G] in
/-- Each vector $\pi(n) v - v$ with $n \in N$ is in $V(N)$. -/
theorem sub_mem_jacquetKer (π : SmoothRep G) {N : Subgroup G} {n : G} (hn : n ∈ N) (v : π.V) :
    π.ρ n v - v ∈ π.jacquetKer N :=
  Coinvariants.sub_mem_ker (ρ := π.ρ.comp N.subtype) ⟨n, hn⟩ v

omit [IsTopologicalGroup G] in
/-- If $M$ normalizes $N$, then $V(N)$ is stable under $M$. -/
theorem jacquetKer_stable (π : SmoothRep G) {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    IsStableSubspace (π.ρ.comp M.subtype) (π.jacquetKer N) := by
  intro m
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨n, v⟩, rfl⟩
  have hn : (m : G) * n * (m : G)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hMN m.2) n).1 n.2
  have key :
      π.ρ m (π.ρ n v - v) = π.ρ ((m : G) * n * (m : G)⁻¹) (π.ρ m v) - π.ρ m v := by
    rw [map_sub]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  change π.ρ m (π.ρ n v - v) ∈ π.jacquetKer N
  rw [key]
  exact π.sub_mem_jacquetKer hn _

/-- The Jacquet module $V_N = V / V(N)$ of a smooth representation of $G$, as a smooth representation of a subgroup $M$ that normalizes $N$. For a parabolic subgroup $P = MN$ of a reductive group, $M$ is a Levi subgroup and $N$ is the unipotent radical. -/
def jacquet (π : SmoothRep G) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) : SmoothRep M where
  V := π.V ⧸ π.jacquetKer N
  ρ := Representation.quotient (π.ρ.comp M.subtype) _ (π.jacquetKer_stable hMN)
  smooth x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : IsOpen ((Subtype.val : M → G) ⁻¹' (vecStabilizer π.ρ v : Set G)) :=
      continuous_subtype_val.isOpen_preimage _ (π.smooth v)
    refine Subgroup.isOpen_mono (H₁ := (vecStabilizer π.ρ v).comap M.subtype) ?_ this
    intro m hm
    rw [Subgroup.mem_comap, mem_vecStabilizer] at hm
    rw [mem_vecStabilizer]
    change Submodule.Quotient.mk (π.ρ m v) = _
    rw [show π.ρ m v = v from hm]

/-- The quotient map $V \to V_N$. -/
def jacquetMk (π : SmoothRep G) (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    π.V →ₗ[ℂ] (π.jacquet N M hMN).V :=
  (π.jacquetKer N).mkQ

/-- The quotient map $V \to V_N$ is onto. -/
theorem jacquetMk_surjective (π : SmoothRep G) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    Function.Surjective (π.jacquetMk N M hMN) :=
  Submodule.mkQ_surjective _

/-- The quotient map $V \to V_N$ is invariant under $N$. -/
theorem jacquetMk_ρ_of_mem (π : SmoothRep G) {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    {n : G} (hn : n ∈ N) (v : π.V) :
    π.jacquetMk N M hMN (π.ρ n v) = π.jacquetMk N M hMN v :=
  (Submodule.Quotient.eq _).2 (π.sub_mem_jacquetKer hn v)

/-- The quotient map $V \to V_N$ is a map of representations of $M$. -/
theorem jacquetMk_ρ (π : SmoothRep G) {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (m : M)
    (v : π.V) :
    π.jacquetMk N M hMN (π.ρ m v) = (π.jacquet N M hMN).ρ m (π.jacquetMk N M hMN v) :=
  rfl

/-- The kernel of the quotient map $V \to V_N$ is $V(N)$. -/
theorem jacquetMk_eq_zero_iff (π : SmoothRep G) {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (v : π.V) : π.jacquetMk N M hMN v = 0 ↔ v ∈ π.jacquetKer N :=
  Submodule.Quotient.mk_eq_zero _

/-- The $M$-maps $\pi|_M \to \tau$ that are invariant under $N$: the maps of representations of $MN$ from $\pi$ to $\tau$ with $N$ acting trivially on $\tau$. -/
def nInvariantHom (π : SmoothRep G) (N M : Subgroup G) (τ : SmoothRep M) :
    Submodule ℂ (IntertwiningMap (π.ρ.comp M.subtype) τ.ρ) where
  carrier := {f | ∀ n ∈ N, ∀ v, f (π.ρ n v) = f v}
  add_mem' {f f'} hf hf' n hn v := by
    simp only [IntertwiningMap.coe_add, Pi.add_apply, hf n hn v, hf' n hn v]
  zero_mem' n _ v := rfl
  smul_mem' c f hf n hn v := by
    simp only [IntertwiningMap.coe_smul, Pi.smul_apply, hf n hn v]

/-- The universal property of the Jacquet module: composition with $V \to V_N$ is a linear isomorphism from $\mathrm{Hom}_M(V_N, \tau)$ to the $M$-maps $V \to \tau$ that are invariant under $N$. -/
def jacquetEquiv (π : SmoothRep G) (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (τ : SmoothRep M) :
    IntertwiningMap (π.jacquet N M hMN).ρ τ.ρ ≃ₗ[ℂ] π.nInvariantHom N M τ where
  toFun F :=
    ⟨{ toLinearMap := F.toLinearMap ∘ₗ π.jacquetMk N M hMN
       isIntertwining' := fun m => by
        ext v
        change F (π.jacquetMk N M hMN (π.ρ m v)) = τ.ρ m (F (π.jacquetMk N M hMN v))
        rw [jacquetMk_ρ, F.isIntertwining] },
      fun n hn v => by
        change F (π.jacquetMk N M hMN (π.ρ n v)) = F (π.jacquetMk N M hMN v)
        rw [π.jacquetMk_ρ_of_mem hMN hn]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    { toLinearMap := (π.jacquetKer N).liftQ f.1.toLinearMap (by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨⟨n, v⟩, rfl⟩
        change f.1 (π.ρ n v - v) = 0
        rw [map_sub, f.2 n n.2 v, sub_self])
      isIntertwining' := fun m => by
        refine Submodule.linearMap_qext (π.jacquetKer N) (LinearMap.ext fun v => ?_)
        change f.1 (π.ρ m v) = τ.ρ m (f.1 v)
        exact IntertwiningMap.isIntertwining (π.ρ.comp M.subtype) τ.ρ f.1 m v }
  left_inv F := by
    ext x
    obtain ⟨v, rfl⟩ := π.jacquetMk_surjective N M hMN x
    rfl
  right_inv f := by
    ext v
    rfl

/-- The universal property on vectors: the map of the Jacquet module that an $N$-invariant map $f$ gives sends the class of $v$ to $f(v)$. -/
theorem jacquetEquiv_symm_apply (π : SmoothRep G) {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (τ : SmoothRep M) (f : π.nInvariantHom N M τ) (v : π.V) :
    (π.jacquetEquiv N M hMN τ).symm f (π.jacquetMk N M hMN v) = f.1 v :=
  rfl

/-- The map $V_N \to V'_N$ of Jacquet modules that a map of representations $V \to V'$ gives. -/
def jacquetMap {π π' : SmoothRep G} {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (f : IntertwiningMap π.ρ π'.ρ) :
    IntertwiningMap (π.jacquet N M hMN).ρ (π'.jacquet N M hMN).ρ :=
  (π.jacquetEquiv N M hMN (π'.jacquet N M hMN)).symm
    ⟨{ toLinearMap := π'.jacquetMk N M hMN ∘ₗ f.toLinearMap
       isIntertwining' := fun m => by
        ext v
        change π'.jacquetMk N M hMN (f (π.ρ m v)) = _
        rw [f.isIntertwining]
        rfl },
      fun n hn v => by
        change π'.jacquetMk N M hMN (f (π.ρ n v)) = π'.jacquetMk N M hMN (f v)
        rw [f.isIntertwining, π'.jacquetMk_ρ_of_mem hMN hn]⟩

/-- The map $V_N \to V'_N$ sends the class of $v$ to the class of $f(v)$. -/
theorem jacquetMap_mk {π π' : SmoothRep G} {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (f : IntertwiningMap π.ρ π'.ρ) (v : π.V) :
    jacquetMap hMN f (π.jacquetMk N M hMN v) = π'.jacquetMk N M hMN (f v) :=
  rfl

/-- The Jacquet functor keeps surjections: if $V \to V'$ is onto, then so is $V_N \to V'_N$. -/
theorem jacquetMap_surjective {π π' : SmoothRep G} {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (f : IntertwiningMap π.ρ π'.ρ) (hf : Function.Surjective f) :
    Function.Surjective (jacquetMap hMN f) := by
  intro y
  obtain ⟨w, rfl⟩ := π'.jacquetMk_surjective N M hMN y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨π.jacquetMk N M hMN v, rfl⟩

end SmoothRep

end Jacquet

section GeneralLinear

open Matrix

namespace GL2

variable {K : Type u} [Field K]

/-- The inverse of an element of $GL_2(K)$ is $\det(g)^{-1}$ times the adjugate of $g$. -/
theorem val_inv (g : GL (Fin 2) K) :
    (g⁻¹).1 = (g.1.det)⁻¹ • !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']

/-- The determinant of an element of $GL_2(K)$ is not $0$. -/
theorem det_ne_zero (g : GL (Fin 2) K) : g.1.det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

variable (K)

/-- The Borel subgroup $B$ of the upper triangular matrices in $GL_2(K)$. -/
def borel : Subgroup (GL (Fin 2) K) where
  carrier := {g | g.1 1 0 = 0}
  mul_mem' {a b} ha hb := by
    change (a.1 * b.1) 1 0 = 0
    change a.1 1 0 = 0 at ha
    change b.1 1 0 = 0 at hb
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp
  inv_mem' {a} ha := by
    change (a⁻¹).1 1 0 = 0
    change a.1 1 0 = 0 at ha
    rw [val_inv]
    simp [ha]

/-- The unipotent radical $N$ of $B$: the upper triangular matrices with $1$ on the diagonal. -/
def unipotent : Subgroup (GL (Fin 2) K) where
  carrier := {g | g.1 1 0 = 0 ∧ g.1 0 0 = 1 ∧ g.1 1 1 = 1}
  mul_mem' {a b} ha hb := by
    change (a.1 * b.1) 1 0 = 0 ∧ (a.1 * b.1) 0 0 = 1 ∧ (a.1 * b.1) 1 1 = 1
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, ha3, hb1, hb2, hb3]
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧
      (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
    simp
  inv_mem' {a} ha := by
    change (a⁻¹).1 1 0 = 0 ∧ (a⁻¹).1 0 0 = 1 ∧ (a⁻¹).1 1 1 = 1
    obtain ⟨ha1, ha2, ha3⟩ := ha
    have hdet : a.1.det = 1 := by simp [Matrix.det_fin_two, ha1, ha2, ha3]
    rw [val_inv]
    simp [hdet, ha1, ha2, ha3]

/-- The diagonal torus $T$ of $GL_2(K)$. -/
def torus : Subgroup (GL (Fin 2) K) where
  carrier := {g | g.1 1 0 = 0 ∧ g.1 0 1 = 0}
  mul_mem' {a b} ha hb := by
    change (a.1 * b.1) 1 0 = 0 ∧ (a.1 * b.1) 0 1 = 0
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2]
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0
    simp
  inv_mem' {a} ha := by
    change (a⁻¹).1 1 0 = 0 ∧ (a⁻¹).1 0 1 = 0
    obtain ⟨ha1, ha2⟩ := ha
    rw [val_inv]
    simp [ha1, ha2]

variable {K}

/-- An element is in $B$ exactly when its lower left entry is $0$. -/
theorem mem_borel (g : GL (Fin 2) K) : g ∈ borel K ↔ g.1 1 0 = 0 :=
  Iff.rfl

/-- An element is in $N$ exactly when it is upper triangular with $1$ on the diagonal. -/
theorem mem_unipotent (g : GL (Fin 2) K) :
    g ∈ unipotent K ↔ g.1 1 0 = 0 ∧ g.1 0 0 = 1 ∧ g.1 1 1 = 1 :=
  Iff.rfl

/-- An element is in $T$ exactly when it is diagonal. -/
theorem mem_torus (g : GL (Fin 2) K) : g ∈ torus K ↔ g.1 1 0 = 0 ∧ g.1 0 1 = 0 :=
  Iff.rfl

/-- The unipotent radical $N$ is contained in $B$. -/
theorem unipotent_le_borel : unipotent K ≤ borel K :=
  fun _ h => h.1

/-- The torus $T$ is contained in $B$. -/
theorem torus_le_borel : torus K ≤ borel K :=
  fun _ h => h.1

/-- The upper left entry is multiplicative when the second factor is upper triangular. -/
theorem mul_val_zero_zero (a : GL (Fin 2) K) {b : GL (Fin 2) K} (hb : b ∈ borel K) :
    (a * b).1 0 0 = a.1 0 0 * b.1 0 0 := by
  rw [mem_borel] at hb
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb]

/-- The lower right entry is multiplicative when the first factor is upper triangular. -/
theorem mul_val_one_one {a : GL (Fin 2) K} (ha : a ∈ borel K) (b : GL (Fin 2) K) :
    (a * b).1 1 1 = a.1 1 1 * b.1 1 1 := by
  rw [mem_borel] at ha
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha]

/-- The Borel subgroup normalizes its unipotent radical. -/
theorem conj_mem_unipotent {b n : GL (Fin 2) K} (hb : b ∈ borel K) (hn : n ∈ unipotent K) :
    b * n * b⁻¹ ∈ unipotent K := by
  have hbn : b * n ∈ borel K := (borel K).mul_mem hb (unipotent_le_borel hn)
  have hbi : b⁻¹ ∈ borel K := (borel K).inv_mem hb
  refine ⟨(borel K).mul_mem hbn hbi, ?_, ?_⟩
  · rw [mul_val_zero_zero _ hbi, mul_val_zero_zero _ (unipotent_le_borel hn), hn.2.1, mul_one,
      ← mul_val_zero_zero _ hbi, mul_inv_cancel]
    simp
  · rw [mul_val_one_one hbn, mul_val_one_one hb, hn.2.2, mul_one, ← mul_val_one_one hb,
      mul_inv_cancel]
    simp

/-- The Borel subgroup is contained in the normalizer of its unipotent radical. -/
theorem borel_le_normalizer_unipotent :
    borel K ≤ Subgroup.normalizer (unipotent K : Set (GL (Fin 2) K)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => conj_mem_unipotent hb hn, fun hn => ?_⟩
  have := conj_mem_unipotent ((borel K).inv_mem hb) hn
  simpa [mul_assoc] using this

/-- The upper left entry of an upper triangular matrix is not $0$. -/
theorem val_zero_zero_ne_zero {b : GL (Fin 2) K} (hb : b ∈ borel K) : b.1 0 0 ≠ 0 := by
  intro h
  apply det_ne_zero b
  rw [mem_borel] at hb
  simp [Matrix.det_fin_two, h, hb]

/-- The lower right entry of an upper triangular matrix is not $0$. -/
theorem val_one_one_ne_zero {b : GL (Fin 2) K} (hb : b ∈ borel K) : b.1 1 1 ≠ 0 := by
  intro h
  apply det_ne_zero b
  rw [mem_borel] at hb
  simp [Matrix.det_fin_two, h, hb]

/-- The character $b \mapsto a$ of $B$, for $b$ with diagonal $(a, d)$. -/
noncomputable def diagFst : borel K →* Kˣ where
  toFun b := Units.mk0 (b.1.1 0 0) (val_zero_zero_ne_zero b.2)
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact mul_val_zero_zero _ b.2)

/-- The character $b \mapsto d$ of $B$, for $b$ with diagonal $(a, d)$. -/
noncomputable def diagSnd : borel K →* Kˣ where
  toFun b := Units.mk0 (b.1.1 1 1) (val_one_one_ne_zero b.2)
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact mul_val_one_one a.2 _)

/-- The value of `diagFst` is the upper left entry. -/
theorem val_diagFst (b : borel K) : (diagFst b : K) = b.1.1 0 0 :=
  rfl

/-- The value of `diagSnd` is the lower right entry. -/
theorem val_diagSnd (b : borel K) : (diagSnd b : K) = b.1.1 1 1 :=
  rfl

/-- The character $\chi_1 \otimes \chi_2 : b \mapsto \chi_1(a)\chi_2(d)$ of $B$. -/
noncomputable def borelChar (χ₁ χ₂ : Kˣ →* ℂˣ) : borel K →* ℂˣ :=
  χ₁.comp diagFst * χ₂.comp diagSnd

/-- The value $\chi_1(a)\chi_2(d)$ of $\chi_1 \otimes \chi_2$. -/
theorem borelChar_apply (χ₁ χ₂ : Kˣ →* ℂˣ) (b : borel K) :
    borelChar χ₁ χ₂ b = χ₁ (diagFst b) * χ₂ (diagSnd b) :=
  rfl

end GL2

end GeneralLinear

section PrincipalSeries

open Matrix

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

/-- The map $b \mapsto a$ from $B$ to $K^\times$ is continuous. -/
theorem continuous_diagFst : Continuous (diagFst : borel K → Kˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : Continuous fun b : borel K => (b.1 : Matrix (Fin 2) (Fin 2) K) :=
      Units.continuous_val.comp continuous_subtype_val
    exact this.matrix_elem 0 0
  · have h : (fun b : borel K => ((diagFst b)⁻¹ : Kˣ).1) =
        fun b => (b⁻¹ : borel K).1.1 0 0 := by
      funext b
      rw [← map_inv]
      rfl
    rw [h]
    have : Continuous fun b : borel K => ((b⁻¹ : borel K).1 : Matrix (Fin 2) (Fin 2) K) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
    exact this.matrix_elem 0 0

/-- The map $b \mapsto d$ from $B$ to $K^\times$ is continuous. -/
theorem continuous_diagSnd : Continuous (diagSnd : borel K → Kˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : Continuous fun b : borel K => (b.1 : Matrix (Fin 2) (Fin 2) K) :=
      Units.continuous_val.comp continuous_subtype_val
    exact this.matrix_elem 1 1
  · have h : (fun b : borel K => ((diagSnd b)⁻¹ : Kˣ).1) =
        fun b => (b⁻¹ : borel K).1.1 1 1 := by
      funext b
      rw [← map_inv]
      rfl
    rw [h]
    have : Continuous fun b : borel K => ((b⁻¹ : borel K).1 : Matrix (Fin 2) (Fin 2) K) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
    exact this.matrix_elem 1 1

/-- For smooth characters $\chi_1, \chi_2$, the character $\chi_1 \otimes \chi_2$ of $B$ has open kernel. -/
theorem isOpen_ker_borelChar {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : IsOpen ((borelChar χ₁ χ₂).ker : Set (borel K)) := by
  refine Subgroup.isOpen_mono (H₁ := (χ₁.comp diagFst).ker ⊓ (χ₂.comp diagSnd).ker) ?_
    ((continuous_diagFst.isOpen_preimage _ hχ₁).inter
      (continuous_diagSnd.isOpen_preimage _ hχ₂))
  intro b hb
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hb
  rw [MonoidHom.mem_ker, borelChar_apply]
  rw [MonoidHom.comp_apply] at hb
  rw [MonoidHom.comp_apply] at hb
  rw [hb.1, hb.2, mul_one]

end GL2

open GL2

/-- The principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ of $GL_2(K)$, by unnormalized smooth induction: the functions $f$ with $f(bg) = \chi_1(a)\chi_2(d) f(g)$ for each $b \in B$ with diagonal $(a, d)$, that are invariant on the right under an open subgroup. The normalized principal series `Langlands.principalSeries` uses the characters $\chi_1 |\cdot|^{1/2}$ and $\chi_2 |\cdot|^{-1/2}$ instead. -/
noncomputable def principalSeriesInd (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : SmoothRep (GL (Fin 2) K) :=
  SmoothRep.ind (borel K)
    (SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂))

/-- The functions of the principal series satisfy $f(bg) = \chi_1(a)\chi_2(d) f(g)$. -/
theorem principalSeriesInd_mul_left {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁}
    {hχ₂ : IsSmoothChar K χ₂} (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) (b : borel K)
    (g : GL (Fin 2) K) :
    SmoothRep.ind.toFun f (b * g) =
      ((χ₁ (diagFst b) : ℂ) * χ₂ (diagSnd b)) • SmoothRep.ind.toFun f g :=
  SmoothRep.ind.toFun_mul_left f b g

/-- The Jacquet module of the principal series with respect to the unipotent radical $N$ of $B$, as a smooth representation of the diagonal torus $T$. -/
noncomputable def principalSeriesJacquet (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : SmoothRep (torus K) :=
  (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).jacquet (unipotent K) (torus K)
    (torus_le_borel.trans borel_le_normalizer_unipotent)

end PrincipalSeries

end Langlands
