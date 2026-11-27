/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Ring.HilbertSamuel
import Langlands.Statements.PadicGalois
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.CategoryTheory.Yoneda

/-!
# Framed deformations of a residual representation

Let $\Lambda$ be a commutative ring with a $\Lambda$-algebra structure on a field $k$, for example $\Lambda = W(k)$ for a finite field $k$. Let $G$ be a topological group, for example a profinite group, and let $\bar\rho : G \to GL_n(k)$ be a homomorphism. This file defines the category of complete noetherian local $\Lambda$-algebras with residue field $k$, the framed deformation functor $D^\square_{\bar\rho}$ on it, and the universal framed deformation ring $R^\square$ that pro-represents $D^\square_{\bar\rho}$. It proves that the universal ring is unique up to a unique isomorphism. For a predicate $P$ on lifts to fields, it defines the quotient $R^\square(P)$ whose points are the points in $P$, and the Hilbert-Samuel multiplicity $e(R^\square(P)/\varpi)$ of its special fiber. These are the objects that the statement of the Breuil-Mezard conjecture uses (`Langlands/Statements/BreuilMezard.lean`).

## Main definitions

* `Langlands.CoeffAlg`: the complete noetherian local $\Lambda$-algebras $A$ with a surjection $A \to k$, with the category structure. The artinian objects are the artinian local $\Lambda$-algebras with residue field $k$.
* `Langlands.CoeffAlg.quot`: the artinian quotient $A/\mathfrak{m}_A^{N+1}$.
* `Langlands.framedLifts`: the framed lifts of $\bar\rho$ to $A$, the homomorphisms $\rho : G \to GL_n(A)$ that reduce to $\bar\rho$ and are continuous, that is the kernel of $\rho$ modulo $\mathfrak{m}_A^N$ is open for each $N$.
* `Langlands.framedDeformationFunctor`: the functor $A \mapsto D^\square_{\bar\rho}(A)$.
* `Langlands.pushforward`: the lift $f \circ \rho$ for a morphism $f$.
* `Langlands.IsUniversalFramedDeformationRing`: the pair $(R, \rho^{univ})$ is universal. Each framed lift to an artinian $A$ is $f \circ \rho^{univ}$ for a unique morphism $f : R \to A$.
* `Langlands.pointIdeal`, `Langlands.PointQuotient`: the intersection of the kernels of the points $x : R \to E$ to fields $E$ such that $x \circ \rho^{univ}$ satisfies $P$, and the quotient $R^\square(P)$ of $R$ by it.
* `Langlands.HasPoint`: there is a point in $P$.
* `Langlands.pointLift`, `Langlands.pointQuotientLift`, `Langlands.pointQuotientResidue`: a point in $P$ as a point of $R^\square(P)$, the lift $G \to GL_n(R^\square(P))$, and the residue map of $R^\square(P)$.
* `Langlands.localMultiplicity`: the Hilbert-Samuel multiplicity of a ring if it is local, and $0$ if not.
* `Langlands.SpecialFiber`, `Langlands.specialFiberMultiplicity`: the ring $R^\square(P)/\varpi$ and its Hilbert-Samuel multiplicity $e(R^\square(P)/\varpi)$, with `Langlands.hilbertSamuelMultiplicity` of `Langlands/Ring/HilbertSamuel.lean`.

## Main results

* `Langlands.mem_framedLifts_iff_of_isArtinianRing`: for an artinian $A$, a framed lift is a homomorphism with open kernel that reduces to $\bar\rho$.
* `Langlands.framedLifts_eq_framedLift`: for $G = G_{\mathbb{Q}_p}$, $n = 2$ and an artinian $A$, the framed lifts are the set `Langlands.FramedLift` of `Langlands/Statements/PadicGalois.lean`.
* `Langlands.IsUniversalFramedDeformationRing.existsUnique_of_complete`: the universal property holds for all complete noetherian local $\Lambda$-algebras with residue field $k$, and not only for the artinian ones.
* `Langlands.IsUniversalFramedDeformationRing.corepresentableBy`: the universal ring corepresents the framed deformation functor.
* `Langlands.IsUniversalFramedDeformationRing.existsUnique_iso`: two universal pairs are isomorphic by a unique isomorphism that is compatible with the universal lifts.
* `Langlands.IsUniversalFramedDeformationRing.of_iso`: the universal property moves along an isomorphism.
* `Langlands.le_pointIdeal_iff`, `Langlands.pointLift`, `Langlands.map_pointLift_comp`: $R^\square(P)$ is the largest quotient of $R$ through which each point in $P$ factors.
* `Langlands.isReduced_pointQuotient`: $R^\square(P)$ is reduced.
* `Langlands.isSMulRegular_pointQuotient`: if $\varpi$ is not zero at each point in $P$, then $\varpi$ is not a zero divisor on $R^\square(P)$. For $\Lambda = W(k)$ and $\varpi = p$ this says that $R^\square(P)$ has no $p$-torsion.
* `Langlands.isLocalRing_pointQuotient`, `Langlands.isLocalRing_specialFiber`, `Langlands.specialFiberMultiplicity_eq`: if there is a point in $P$ and $\varpi$ is zero in $k$, then $R^\square(P)$ and $R^\square(P)/\varpi$ are noetherian local rings, and `specialFiberMultiplicity` is the Hilbert-Samuel multiplicity of $R^\square(P)/\varpi$.

## Proof

For the extension of the universal property, let $A$ be complete and let $\rho$ be a framed lift to $A$. The image of $\rho$ in $GL_n(A/\mathfrak{m}_A^{N+1})$ is a framed lift to an artinian ring, so it comes from a unique morphism $g_N : R \to A/\mathfrak{m}_A^{N+1}$. The uniqueness shows that the $g_N$ are compatible. Since $A$ is complete, they come from a morphism $f : R \to A$ (`IsAdicComplete.liftAlgHom`). The lifts $f \circ \rho^{univ}$ and $\rho$ agree modulo each $\mathfrak{m}_A^N$, so they are equal because $A$ is Hausdorff. The uniqueness of $f$ also follows from the Hausdorff property. Then the uniqueness of the universal ring is the argument of Yoneda: the two morphisms $R \to R'$ and $R' \to R$ compose to morphisms that fix the universal lifts, and these are the identities.

The ideal of $R^\square(P)$ is an intersection of kernels of homomorphisms to fields. These kernels are prime ideals, so the ideal is radical and the quotient is reduced. If $\varpi a$ is zero at each point and $\varpi$ is not zero at each point, then $a$ is zero at each point. If there is a point, then the ideal is not the unit ideal, so it is in the maximal ideal and the residue map of $R$ factors through $R^\square(P)$ and through $R^\square(P)/\varpi$ when $\varpi$ is zero in $k$.

## What this file does not do

* The existence of the universal ring (Mazur) is not proved. It needs the $p$-finiteness condition on $G$, Schlessinger's criterion or a construction as a quotient of a power series ring over $\Lambda$, and the fact that a quotient of a complete noetherian local ring is complete. Mathlib does not have these results.
* The quotient $R^\square(P)$ is not shown to be complete, so it is not shown to be an object of `CoeffAlg`. The existence of the limit $e(R^\square(P)/\varpi)$ is in `Langlands/Ring/HilbertSamuelPoly.lean`, which is not imported here.
* The predicate $P$ is arbitrary. The conditions that a point has values in a finite extension of $W(k)[1/p]$, that the lift is potentially semistable of a given type, and so on, are for the user of the file to put in $P$. The points of $R^\square(P)$ in a field are not shown to be the points in $P$, only to contain them. This is the Zariski closure, as for the rings of Kisin.

## References

* B. Mazur, Deforming Galois representations, in Galois groups over Q, MSRI Publ. 16 (1989).
* M. Kisin, Potentially semi-stable deformation rings, J. Amer. Math. Soc. 21 (2008).
* M. Schlessinger, Functors of Artin rings, Trans. Amer. Math. Soc. 130 (1968).
-/

namespace Langlands

open CategoryTheory IsLocalRing

universe u

/-- A complete noetherian local `Λ`-algebra with residue field `k`: a noetherian local ring with a `Λ`-algebra structure, complete for the topology of its maximal ideal, with a surjective `Λ`-algebra homomorphism to `k`. For `Λ = W(k)` these are the coefficient rings of deformation theory. The artinian objects are the artinian local `Λ`-algebras with residue field `k`. -/
structure CoeffAlg (Λ : Type u) [CommRing Λ] (k : Type u) [Field k] [Algebra Λ k] where
  /-- The underlying type. -/
  carrier : Type u
  /-- The ring structure. -/
  [commRing : CommRing carrier]
  /-- The `Λ`-algebra structure. -/
  [algebra : Algebra Λ carrier]
  /-- The ring is local. -/
  [isLocalRing : IsLocalRing carrier]
  /-- The ring is noetherian. -/
  [isNoetherianRing : IsNoetherianRing carrier]
  /-- The ring is complete for the topology of the maximal ideal. -/
  [isAdicComplete : IsAdicComplete (maximalIdeal carrier) carrier]
  /-- The residue map to `k`. -/
  residue : carrier →ₐ[Λ] k
  /-- The residue map is surjective. -/
  residue_surjective : Function.Surjective residue

namespace CoeffAlg

attribute [instance] commRing algebra isLocalRing isNoetherianRing isAdicComplete

variable {Λ : Type u} [CommRing Λ] {k : Type u} [Field k] [Algebra Λ k]

/-- An object of the category is seen as its underlying type. -/
instance : CoeSort (CoeffAlg Λ k) (Type u) := ⟨CoeffAlg.carrier⟩

/-- A morphism of complete noetherian local `Λ`-algebras with residue field `k`. -/
@[ext]
structure Hom (A B : CoeffAlg Λ k) where
  /-- The underlying `Λ`-algebra homomorphism. -/
  toAlgHom : A →ₐ[Λ] B
  /-- The homomorphism is compatible with the residue maps. -/
  residue_comp : B.residue.comp toAlgHom = A.residue

/-- The category of complete noetherian local `Λ`-algebras with residue field `k`. The morphisms are the `Λ`-algebra homomorphisms that are compatible with the residue maps. -/
instance : Category (CoeffAlg Λ k) where
  Hom := Hom
  id A := ⟨AlgHom.id Λ A, AlgHom.comp_id _⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← AlgHom.comp_assoc, g.residue_comp, f.residue_comp]⟩
  id_comp _ := Hom.ext (AlgHom.comp_id _)
  comp_id _ := Hom.ext (AlgHom.id_comp _)
  assoc _ _ _ := Hom.ext (AlgHom.comp_assoc _ _ _).symm

/-- Two morphisms are equal if their underlying algebra homomorphisms are equal. -/
@[ext]
theorem hom_ext {A B : CoeffAlg Λ k} {f g : A ⟶ B} (h : f.toAlgHom = g.toAlgHom) : f = g :=
  Hom.ext h

/-- The algebra homomorphism of the identity morphism is the identity. -/
@[simp]
theorem id_toAlgHom (A : CoeffAlg Λ k) : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

/-- The algebra homomorphism of a composite is the composite of the algebra homomorphisms. -/
@[simp]
theorem comp_toAlgHom {A B C : CoeffAlg Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

/-- A morphism is compatible with the residue maps. -/
theorem residue_apply_hom {A B : CoeffAlg Λ k} (f : A ⟶ B) (x : A) :
    B.residue (f.toAlgHom x) = A.residue x :=
  AlgHom.congr_fun f.residue_comp x

/-- The kernel of the residue map is the maximal ideal. -/
theorem ker_residue (A : CoeffAlg Λ k) : RingHom.ker A.residue = maximalIdeal A :=
  haveI := RingHom.ker_isMaximal_of_surjective _ A.residue_surjective
  IsLocalRing.eq_maximalIdeal this

/-- An element has residue zero if and only if it is in the maximal ideal. -/
theorem residue_eq_zero_iff (A : CoeffAlg Λ k) (x : A) : A.residue x = 0 ↔ x ∈ maximalIdeal A := by
  rw [← ker_residue, RingHom.mem_ker]

/-- A morphism sends the maximal ideal into the maximal ideal. -/
theorem hom_mem_maximalIdeal {A B : CoeffAlg Λ k} (f : A ⟶ B) {x : A} (hx : x ∈ maximalIdeal A) :
    f.toAlgHom x ∈ maximalIdeal B := by
  rw [← residue_eq_zero_iff, residue_apply_hom, residue_eq_zero_iff]
  exact hx

/-- A morphism sends `m_A^N` into `m_B^N`. -/
theorem pow_le_comap {A B : CoeffAlg Λ k} (f : A ⟶ B) (N : ℕ) :
    maximalIdeal A ^ N ≤ (maximalIdeal B ^ N).comap (f.toAlgHom : A →+* B) :=
  le_trans (Ideal.pow_right_mono (fun _ hx => hom_mem_maximalIdeal f hx) N)
    (Ideal.le_comap_pow _ N)

/-- The ideal `m^(N + 1)` is not the unit ideal. -/
theorem pow_succ_ne_top (A : CoeffAlg Λ k) (N : ℕ) : maximalIdeal A ^ (N + 1) ≠ ⊤ :=
  fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self N.succ_ne_zero))

/-- The quotient `A / m^(N + 1)`, an artinian object of the category. -/
noncomputable def quot (A : CoeffAlg Λ k) (N : ℕ) : CoeffAlg Λ k :=
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (N + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (pow_succ_ne_top A N)
  haveI : IsLocalRing (A ⧸ maximalIdeal A ^ (N + 1)) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (A ⧸ maximalIdeal A ^ (N + 1)) :=
    isArtinianRing_quotient_maximalIdeal_pow A N.succ_ne_zero
  { carrier := A ⧸ maximalIdeal A ^ (N + 1)
    residue := Ideal.Quotient.liftₐ _ A.residue fun a ha =>
      (residue_eq_zero_iff A a).mpr (Ideal.pow_le_self N.succ_ne_zero ha)
    residue_surjective := by
      intro y
      obtain ⟨x, rfl⟩ := A.residue_surjective y
      exact ⟨Ideal.Quotient.mk _ x, rfl⟩ }

/-- The quotient `A / m^(N + 1)` is an artinian ring. -/
instance (A : CoeffAlg Λ k) (N : ℕ) : IsArtinianRing (A.quot N) :=
  isArtinianRing_quotient_maximalIdeal_pow A N.succ_ne_zero

/-- The projection `A → A / m^(N + 1)`. -/
noncomputable def toQuot (A : CoeffAlg Λ k) (N : ℕ) : A ⟶ A.quot N :=
  ⟨Ideal.Quotient.mkₐ Λ (maximalIdeal A ^ (N + 1)), rfl⟩

/-- The projection `A / m^(N + 1) → A / m^(M + 1)` for `M ≤ N`. -/
noncomputable def quotMap (A : CoeffAlg Λ k) {M N : ℕ} (h : M ≤ N) : A.quot N ⟶ A.quot M :=
  ⟨Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)),
    Ideal.Quotient.algHom_ext Λ (AlgHom.ext fun _ => rfl)⟩

/-- The projections to the quotients are compatible. -/
@[simp]
theorem toQuot_comp_quotMap (A : CoeffAlg Λ k) {M N : ℕ} (h : M ≤ N) :
    A.toQuot N ≫ A.quotMap h = A.toQuot M :=
  hom_ext (AlgHom.ext fun _ => rfl)

end CoeffAlg

section Lifts

open Matrix

variable {Λ : Type u} [CommRing Λ] {k : Type u} [Field k] [Algebra Λ k]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : Type u}
  [Fintype n] [DecidableEq n]
variable (ρbar : G →* GL n k)

/-- The framed lifts of `ρbar` to `A`: the homomorphisms `ρ : G → GL_n(A)` that reduce to `ρbar` and that are continuous for the topology of the maximal ideal, that is the kernel of `ρ` modulo `m^N` is open for each `N`. -/
def framedLifts (A : CoeffAlg Λ k) : Set (G →* GL n A) :=
  {ρ | (∀ N, IsOpen (((GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ N))).comp
      ρ).ker : Set G)) ∧ (GeneralLinearGroup.map (A.residue : A →+* k)).comp ρ = ρbar}

/-- The kernel of `ψ` is contained in the kernel of `φ ∘ ψ`. -/
theorem ker_le_ker_comp {H K L : Type*} [Group H] [Group K] [Group L] (φ : K →* L)
    (ψ : H →* K) : ψ.ker ≤ (φ.comp ψ).ker := fun g hg => by
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [MonoidHom.comp_apply, hg, map_one]

/-- A morphism `A → B` sends a framed lift to `A` to a framed lift to `B`. -/
theorem map_mem_framedLifts {A B : CoeffAlg Λ k} (f : A ⟶ B) {ρ : G →* GL n A}
    (hρ : ρ ∈ framedLifts ρbar A) :
    (GeneralLinearGroup.map (f.toAlgHom : A →+* B)).comp ρ ∈ framedLifts ρbar B := by
  refine ⟨fun N => ?_, ?_⟩
  · have e : (Ideal.Quotient.mk (maximalIdeal B ^ N)).comp (f.toAlgHom : A →+* B) =
        (Ideal.quotientMap _ (f.toAlgHom : A →+* B) (CoeffAlg.pow_le_comap f N)).comp
          (Ideal.Quotient.mk (maximalIdeal A ^ N)) := by
      ext x; rfl
    rw [← MonoidHom.comp_assoc, ← GeneralLinearGroup.map_comp, e, GeneralLinearGroup.map_comp,
      MonoidHom.comp_assoc]
    exact Subgroup.isOpen_mono (ker_le_ker_comp _ _) (hρ.1 N)
  · rw [← hρ.2, ← MonoidHom.comp_assoc, ← GeneralLinearGroup.map_comp]
    congr 2
    exact congrArg AlgHom.toRingHom f.residue_comp

/-- An injective ring homomorphism gives an injective group homomorphism of the general linear groups. -/
theorem map_injective {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) : Function.Injective (GeneralLinearGroup.map (n := n) f) :=
  fun _ _ h => Units.ext (Matrix.ext fun i j =>
    hf (congrArg (fun X : GL n B => (X : Matrix n n B) i j) h))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Composition with an injective ring homomorphism does not change the kernel of a homomorphism to a general linear group. -/
theorem ker_comp_map_of_injective {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) (ρ : G →* GL n A) :
    ((GeneralLinearGroup.map f).comp ρ).ker = ρ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [← (map_injective hf).eq_iff, map_one]

/-- For an artinian `A`, a framed lift is a homomorphism with open kernel that reduces to `ρbar`. -/
theorem mem_framedLifts_iff_of_isArtinianRing (A : CoeffAlg Λ k) [IsArtinianRing A]
    (ρ : G →* GL n A) :
    ρ ∈ framedLifts ρbar A ↔ IsOpen (ρ.ker : Set G) ∧
      (GeneralLinearGroup.map (A.residue : A →+* k)).comp ρ = ρbar := by
  refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨fun N => Subgroup.isOpen_mono (ker_le_ker_comp _ _) h.1,
    h.2⟩⟩
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal A ^ N)) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]
    exact hN
  rw [← ker_comp_map_of_injective hinj]
  exact h.1 N

/-- The framed deformation functor of `ρbar` on complete noetherian local `Λ`-algebras with residue field `k`. -/
def framedDeformationFunctor : CoeffAlg Λ k ⥤ Type u where
  obj A := framedLifts ρbar A
  map f := TypeCat.ofHom fun ρ => ⟨_, map_mem_framedLifts ρbar f ρ.2⟩
  map_id A := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

end Lifts

section Universal

open Matrix

variable {Λ : Type u} [CommRing Λ] {k : Type u} [Field k] [Algebra Λ k]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : Type u}
  [Fintype n] [DecidableEq n]
variable (ρbar : G →* GL n k)

/-- The image `f ∘ ρ : G → GL_n(B)` of a homomorphism `ρ : G → GL_n(A)` under a morphism `f : A → B`. -/
def pushforward {A B : CoeffAlg Λ k} (f : A ⟶ B) (ρ : G →* GL n A) : G →* GL n B :=
  (GeneralLinearGroup.map (f.toAlgHom : A →+* B)).comp ρ

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The image under a composite is the image under the second morphism of the image under the first morphism. -/
theorem pushforward_comp {A B C : CoeffAlg Λ k} (f : A ⟶ B) (g : B ⟶ C) (ρ : G →* GL n A) :
    pushforward (f ≫ g) ρ = pushforward g (pushforward f ρ) := by
  ext; rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The image under the identity morphism is the same homomorphism. -/
theorem pushforward_id {A : CoeffAlg Λ k} (ρ : G →* GL n A) : pushforward (𝟙 A) ρ = ρ := by
  ext; rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The entries of the image under `f` are the images under `f` of the entries. -/
theorem pushforward_apply {A B : CoeffAlg Λ k} (f : A ⟶ B) (ρ : G →* GL n A) (g : G) (i j : n) :
    ((pushforward f ρ g : GL n B) : Matrix n n B) i j = f.toAlgHom ((ρ g : Matrix n n A) i j) :=
  rfl

/-- The pair `(R, ρu)` is a universal framed deformation of `ρbar`: the homomorphism `ρu` is a framed lift of `ρbar` to `R`, and for each artinian local `Λ`-algebra `A` with residue field `k`, each framed lift of `ρbar` to `A` is the image of `ρu` under a unique morphism `R → A`. Thus `R` pro-represents the framed deformation functor. -/
structure IsUniversalFramedDeformationRing (R : CoeffAlg Λ k) (ρu : G →* GL n R) : Prop where
  /-- The homomorphism `ρu` is a framed lift of `ρbar`. -/
  mem : ρu ∈ framedLifts ρbar R
  /-- Each framed lift to an artinian `A` comes from a unique morphism `R → A`. -/
  existsUnique : ∀ (A : CoeffAlg Λ k) [IsArtinianRing A], ∀ ρ ∈ framedLifts ρbar A,
    ∃! f : R ⟶ A, pushforward f ρu = ρ

/-- Two elements of a complete local ring are equal if they are equal modulo each power of the maximal ideal. -/
theorem CoeffAlg.eq_of_forall_mk_eq (A : CoeffAlg Λ k) {a b : A}
    (h : ∀ N, Ideal.Quotient.mk (maximalIdeal A ^ N) a = Ideal.Quotient.mk _ b) : a = b :=
  congrFun (IsHausdorff.funext' (R := Unit) (maximalIdeal A) (f := fun _ => a) (g := fun _ => b)
    fun N _ => h N) ()

variable {ρbar}

/-- The universal property for all complete noetherian local `Λ`-algebras with residue field `k`. The definition asks for it only on the artinian ones. The proof applies the universal property to the quotients `A / m^(N + 1)` and takes the limit, with the completeness of `A`. -/
theorem IsUniversalFramedDeformationRing.existsUnique_of_complete {R : CoeffAlg Λ k}
    {ρu : G →* GL n R} (h : IsUniversalFramedDeformationRing ρbar R ρu) (A : CoeffAlg Λ k)
    {ρ : G →* GL n A} (hρ : ρ ∈ framedLifts ρbar A) :
    ∃! f : R ⟶ A, pushforward f ρu = ρ := by
  have hN : ∀ N, ∃! g : R ⟶ A.quot N, pushforward g ρu = pushforward (A.toQuot N) ρ :=
    fun N => h.existsUnique (A.quot N) _ (map_mem_framedLifts ρbar (A.toQuot N) hρ)
  choose g hg using fun N => (hN N).exists
  have hcompat : ∀ {M N : ℕ} (hMN : M ≤ N), g N ≫ A.quotMap hMN = g M := fun hMN =>
    (hN _).unique (by rw [pushforward_comp, hg, ← pushforward_comp, CoeffAlg.toQuot_comp_quotMap])
      (hg _)
  let f : ∀ N, R →ₐ[Λ] A ⧸ maximalIdeal A ^ N := fun N =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right N.le_succ)).comp (g N).toAlgHom
  have hfg : ∀ N x, f N x = Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right N.le_succ)
      ((g N).toAlgHom x) := fun _ _ => rfl
  have hf : ∀ {M N : ℕ} (hMN : M ≤ N),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hMN)).comp (f N) = f M := by
    intro M N hMN
    ext x
    rw [AlgHom.comp_apply, hfg, hfg, ← hcompat hMN, CoeffAlg.comp_toAlgHom, AlgHom.comp_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((g N).toAlgHom x)
    rw [← hy]
    rfl
  let F := IsAdicComplete.liftAlgHom (maximalIdeal A) f hf
  have hF : ∀ N x, Ideal.Quotient.mk (maximalIdeal A ^ N) (F x) = f N x :=
    fun N x => IsAdicComplete.mk_liftAlgHom _ f hf N x
  have hres : A.residue.comp F = R.residue := by
    ext x
    have h1 : A.residue (F x) = (A.quot 0).residue (Ideal.Quotient.mk _ (F x)) := rfl
    rw [AlgHom.comp_apply, h1, hF, hfg]
    change (A.quot 0).residue ((g 1 ≫ A.quotMap (Nat.zero_le 1)).toAlgHom x) = _
    rw [hcompat, CoeffAlg.residue_apply_hom]
  let Fh : R ⟶ A := ⟨F, hres⟩
  have key : ∀ (F' : R ⟶ A), pushforward F' ρu = ρ ↔ F' = Fh := by
    intro F'
    constructor
    · intro hF'
      have hq : ∀ N, F' ≫ A.toQuot N = g N := fun N =>
        (hN N).unique (by rw [pushforward_comp, hF']) (hg N)
      refine CoeffAlg.hom_ext (IsAdicComplete.algHom_ext (maximalIdeal A) fun N => ?_)
      ext x
      change Ideal.Quotient.mk _ (F'.toAlgHom x) = Ideal.Quotient.mk _ (F x)
      rw [hF, hfg, ← hq]
      rfl
    · rintro rfl
      ext σ i j
      refine A.eq_of_forall_mk_eq fun N => ?_
      have e := congrArg (fun φ : G →* GL n (A.quot N).carrier => (φ σ).1 i j)
        (hg N)
      simp only [pushforward_apply] at e
      rw [pushforward_apply]
      change Ideal.Quotient.mk _ (F _) = _
      rw [hF, hfg, e]
      rfl
  exact ⟨Fh, (key Fh).mpr rfl, fun F' hF' => (key F').mp hF'⟩

/-- The universal ring corepresents the framed deformation functor on all complete noetherian local `Λ`-algebras with residue field `k`. -/
noncomputable def IsUniversalFramedDeformationRing.corepresentableBy {R : CoeffAlg Λ k}
    {ρu : G →* GL n R} (h : IsUniversalFramedDeformationRing ρbar R ρu) :
    (framedDeformationFunctor ρbar).CorepresentableBy R where
  homEquiv {A} :=
    { toFun f := ⟨pushforward f ρu, map_mem_framedLifts ρbar f h.mem⟩
      invFun ρ := (h.existsUnique_of_complete A ρ.2).exists.choose
      left_inv f := by
        have hu := h.existsUnique_of_complete A (map_mem_framedLifts ρbar f h.mem)
        exact hu.unique hu.exists.choose_spec rfl
      right_inv ρ := Subtype.ext (h.existsUnique_of_complete A ρ.2).exists.choose_spec }
  homEquiv_comp g f := by
    apply Subtype.ext
    exact pushforward_comp f g ρu

/-- A universal framed deformation ring is unique up to a unique isomorphism that is compatible with the universal lifts. -/
theorem IsUniversalFramedDeformationRing.existsUnique_iso {R R' : CoeffAlg Λ k}
    {ρu : G →* GL n R} {ρu' : G →* GL n R'} (h : IsUniversalFramedDeformationRing ρbar R ρu)
    (h' : IsUniversalFramedDeformationRing ρbar R' ρu') :
    ∃! e : R ≅ R', pushforward e.hom ρu = ρu' := by
  obtain ⟨φ, hφ, hφu⟩ := h.existsUnique_of_complete R' h'.mem
  obtain ⟨ψ, hψ, -⟩ := h'.existsUnique_of_complete R h.mem
  have h1 : φ ≫ ψ = 𝟙 R := (h.existsUnique_of_complete R h.mem).unique
    (by rw [pushforward_comp, hφ, hψ]) (pushforward_id ρu)
  have h2 : ψ ≫ φ = 𝟙 R' := (h'.existsUnique_of_complete R' h'.mem).unique
    (by rw [pushforward_comp, hψ, hφ]) (pushforward_id ρu')
  exact ⟨⟨φ, ψ, h1, h2⟩, hφ, fun e he => Iso.ext (hφu e.hom he)⟩

/-- The universal property moves along an isomorphism. -/
theorem IsUniversalFramedDeformationRing.of_iso {R R' : CoeffAlg Λ k} {ρu : G →* GL n R}
    (h : IsUniversalFramedDeformationRing ρbar R ρu) (e : R ≅ R') :
    IsUniversalFramedDeformationRing ρbar R' (pushforward e.hom ρu) := by
  refine ⟨map_mem_framedLifts ρbar e.hom h.mem, fun A _ ρ hρ => ?_⟩
  obtain ⟨f, hf, hu⟩ := h.existsUnique A ρ hρ
  refine ⟨e.inv ≫ f, ?_, fun f' hf' => ?_⟩
  · change pushforward (e.inv ≫ f) (pushforward e.hom ρu) = ρ
    rw [← pushforward_comp, ← Category.assoc, e.hom_inv_id, Category.id_comp, hf]
  · have : e.hom ≫ f' = f := hu _ (by
      change pushforward (e.hom ≫ f') ρu = ρ
      rw [pushforward_comp]
      exact hf')
    rw [← this, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end Universal

/-- For `G = Gal(Q̄_p/Q_p)`, `n = 2` and an artinian `A`, the framed lifts are the set `FramedLift p ρbar A π` of `Langlands/Statements/PadicGalois.lean`, with `π` the residue map. -/
theorem framedLifts_eq_framedLift (p : ℕ) [Fact p.Prime] {Λ k : Type} [CommRing Λ] [Field k]
    [Algebra Λ k] (ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k) (A : CoeffAlg Λ k)
    [IsArtinianRing A] : framedLifts ρbar A = FramedLift p ρbar A (A.residue : A →+* k) := by
  ext ρ
  exact mem_framedLifts_iff_of_isArtinianRing ρbar A ρ

section Points

open Matrix

variable {Λ : Type u} [CommRing Λ] {k : Type u} [Field k] [Algebra Λ k]
variable {G : Type u} [Group G] {n : Type u} [Fintype n] [DecidableEq n]
variable (R : CoeffAlg Λ k) (ρu : G →* GL n R)
variable (P : ∀ (E : Type u) [Field E] [Algebra Λ E], (G →* GL n E) → Prop)

/-- The ideal of `R` of the elements that are zero at each point in `P`. A point is a `Λ`-algebra homomorphism `x : R → E` to a field `E` such that the lift `x ∘ ρu` satisfies `P`. It is the intersection of the kernels of these points. -/
def pointIdeal : Ideal R :=
  ⨅ (E : Type u) (_ : Field E) (_ : Algebra Λ E) (x : R →ₐ[Λ] E)
    (_ : P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)), RingHom.ker x

/-- The quotient `R^□(P)` of `R` by `pointIdeal R ρu P`. It is the largest quotient of `R` through which each point in `P` factors. -/
abbrev PointQuotient : Type u := R ⧸ pointIdeal R ρu P

/-- There is a point in `P`. -/
def HasPoint : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra Λ E) (x : R →ₐ[Λ] E),
    P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)

variable {R ρu P}

/-- An element is in `pointIdeal R ρu P` if and only if it is zero at each point in `P`. -/
theorem mem_pointIdeal {r : R} : r ∈ pointIdeal R ρu P ↔
    ∀ (E : Type u) [Field E] [Algebra Λ E] (x : R →ₐ[Λ] E),
      P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu) → x r = 0 := by
  simp [pointIdeal]

/-- The ideal `pointIdeal R ρu P` is in the kernel of each point in `P`. -/
theorem pointIdeal_le_ker {E : Type u} [Field E] [Algebra Λ E] {x : R →ₐ[Λ] E}
    (hx : P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)) :
    pointIdeal R ρu P ≤ RingHom.ker x :=
  fun _ hr => RingHom.mem_ker.mpr (mem_pointIdeal.mp hr E x hx)

/-- The ideal `pointIdeal R ρu P` is the largest ideal of `R` that is in the kernel of each point in `P`. -/
theorem le_pointIdeal_iff {J : Ideal R} : J ≤ pointIdeal R ρu P ↔
    ∀ (E : Type u) [Field E] [Algebra Λ E] (x : R →ₐ[Λ] E),
      P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu) → J ≤ RingHom.ker x := by
  refine ⟨fun h E _ _ x hx => h.trans (pointIdeal_le_ker hx), fun h r hr => ?_⟩
  exact mem_pointIdeal.mpr fun E _ _ x hx => RingHom.mem_ker.mp (h E x hx hr)

/-- A point in `P` factors through `R^□(P)`. -/
def pointLift {E : Type u} [Field E] [Algebra Λ E] {x : R →ₐ[Λ] E}
    (hx : P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)) :
    PointQuotient R ρu P →ₐ[Λ] E :=
  Ideal.Quotient.liftₐ _ x fun _ hr => mem_pointIdeal.mp hr E x hx

/-- The point of `R^□(P)` agrees with the point of `R`. -/
theorem pointLift_mk {E : Type u} [Field E] [Algebra Λ E] {x : R →ₐ[Λ] E}
    (hx : P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)) (r : R) :
    pointLift hx (Ideal.Quotient.mk _ r) = x r :=
  rfl

variable (R ρu P) in
/-- The lift `G → GL_n(R^□(P))`, the image of `ρu`. -/
def pointQuotientLift : G →* GL n (PointQuotient R ρu P) :=
  (GeneralLinearGroup.map (Ideal.Quotient.mk (pointIdeal R ρu P))).comp ρu

/-- Each lift in `P` that comes from a point of `R` comes from a point of `R^□(P)`. -/
theorem map_pointLift_comp {E : Type u} [Field E] [Algebra Λ E] {x : R →ₐ[Λ] E}
    (hx : P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu)) :
    (GeneralLinearGroup.map (pointLift hx : PointQuotient R ρu P →+* E)).comp
      (pointQuotientLift R ρu P) = (GeneralLinearGroup.map (x : R →+* E)).comp ρu := by
  ext; rfl

/-- The ideal `pointIdeal R ρu P` is radical, since it is an intersection of prime ideals. -/
theorem isRadical_pointIdeal : (pointIdeal R ρu P).IsRadical :=
  Ideal.isRadical_iInf _ fun _ => Ideal.isRadical_iInf _ fun _ => Ideal.isRadical_iInf _
    fun _ => Ideal.isRadical_iInf _ fun x => Ideal.isRadical_iInf _ fun _ =>
      (RingHom.ker_isPrime x).isRadical

/-- The ring `R^□(P)` is reduced. -/
instance isReduced_pointQuotient : IsReduced (PointQuotient R ρu P) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp isRadical_pointIdeal

/-- If `ϖ` is not zero at each point in `P`, then `ϖ` is not a zero divisor on `R^□(P)`. For `Λ = W(k)`, `ϖ = p` and points with values in fields of characteristic zero, this says that `R^□(P)` has no `p`-torsion. -/
theorem isSMulRegular_pointQuotient {ϖ : Λ}
    (hϖ : ∀ (E : Type u) [Field E] [Algebra Λ E] (x : R →ₐ[Λ] E),
      P E ((GeneralLinearGroup.map (x : R →+* E)).comp ρu) → algebraMap Λ E ϖ ≠ 0) :
    IsSMulRegular (PointQuotient R ρu P) ϖ := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Ideal.Quotient.eq]
  have h : algebraMap Λ R ϖ * (a - b) ∈ pointIdeal R ρu P := by
    have hab' : ϖ • Ideal.Quotient.mk (pointIdeal R ρu P) a =
        ϖ • Ideal.Quotient.mk (pointIdeal R ρu P) b := hab
    rw [Algebra.smul_def, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap] at hab'
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, mul_sub, sub_eq_zero]
    exact hab'
  refine mem_pointIdeal.mpr fun E _ _ x hx => ?_
  have := mem_pointIdeal.mp h E x hx
  rw [map_mul, AlgHom.commutes] at this
  exact (mul_eq_zero.mp this).resolve_left (hϖ E x hx)

/-- The ideal `pointIdeal R ρu P` is not the unit ideal if and only if there is a point in `P`. -/
theorem pointIdeal_ne_top_iff : pointIdeal R ρu P ≠ ⊤ ↔ HasPoint R ρu P := by
  constructor
  · intro h
    by_contra hP
    refine h (eq_top_iff.mpr fun r _ => mem_pointIdeal.mpr fun E _ _ x hx => ?_)
    exact (hP ⟨E, _, _, x, hx⟩).elim
  · rintro ⟨_, _, _, x, hx⟩ htop
    have := pointIdeal_le_ker hx (htop ▸ Submodule.mem_top : (1 : R) ∈ pointIdeal R ρu P)
    simp at this

/-- If there is a point in `P`, then `pointIdeal R ρu P` is in the maximal ideal. -/
theorem pointIdeal_le_maximalIdeal (hP : HasPoint R ρu P) :
    pointIdeal R ρu P ≤ maximalIdeal R :=
  IsLocalRing.le_maximalIdeal (pointIdeal_ne_top_iff.mpr hP)

/-- The residue map `R^□(P) → k`, when there is a point in `P`. -/
noncomputable def pointQuotientResidue (hP : HasPoint R ρu P) : PointQuotient R ρu P →ₐ[Λ] k :=
  Ideal.Quotient.liftₐ _ R.residue fun r hr =>
    (R.residue_eq_zero_iff r).mpr (pointIdeal_le_maximalIdeal hP hr)

/-- If there is a point in `P`, then `R^□(P)` is a local ring. -/
theorem isLocalRing_pointQuotient (hP : HasPoint R ρu P) : IsLocalRing (PointQuotient R ρu P) :=
  haveI : Nontrivial (PointQuotient R ρu P) :=
    Ideal.Quotient.nontrivial_iff.mpr (pointIdeal_ne_top_iff.mpr hP)
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The Hilbert-Samuel multiplicity of a ring `S` if `S` is a local ring, and `0` if not. -/
noncomputable def localMultiplicity (S : Type*) [CommRing S] : ℕ := by
  classical exact if h : IsLocalRing S then @hilbertSamuelMultiplicity S _ h else 0

/-- For a local ring, `localMultiplicity` is the Hilbert-Samuel multiplicity. -/
theorem localMultiplicity_eq (S : Type*) [CommRing S] [IsLocalRing S] :
    localMultiplicity S = hilbertSamuelMultiplicity S := by
  rw [localMultiplicity]
  split_ifs
  rfl

variable (R ρu P) in
/-- The special fiber `R^□(P) / ϖ`. -/
abbrev SpecialFiber (ϖ : Λ) : Type u :=
  PointQuotient R ρu P ⧸ Ideal.span {algebraMap Λ (PointQuotient R ρu P) ϖ}

variable (R ρu P) in
/-- The Hilbert-Samuel multiplicity `e(R^□(P) / ϖ)` of the special fiber. It is `0` if the special fiber is not a local ring, that is if it is the zero ring. -/
noncomputable def specialFiberMultiplicity (ϖ : Λ) : ℕ :=
  localMultiplicity (SpecialFiber R ρu P ϖ)

/-- If there is a point in `P` and `ϖ` is zero in `k`, then the special fiber is a local ring. -/
theorem isLocalRing_specialFiber (hP : HasPoint R ρu P) {ϖ : Λ} (hϖ : algebraMap Λ k ϖ = 0) :
    IsLocalRing (SpecialFiber R ρu P ϖ) := by
  have := isLocalRing_pointQuotient hP
  have hres : Ideal.span {algebraMap Λ (PointQuotient R ρu P) ϖ} ≤
      RingHom.ker (pointQuotientResidue hP) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      AlgHom.commutes, hϖ]
  have : Nontrivial (SpecialFiber R ρu P ϖ) :=
    RingHom.domain_nontrivial (Ideal.Quotient.lift _ (pointQuotientResidue hP : _ →+* k)
      fun a ha => RingHom.mem_ker.mp (hres ha))
  exact .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- If there is a point in `P` and `ϖ` is zero in `k`, then `specialFiberMultiplicity R ρu P ϖ` is the Hilbert-Samuel multiplicity of the special fiber. -/
theorem specialFiberMultiplicity_eq (hP : HasPoint R ρu P) {ϖ : Λ} (hϖ : algebraMap Λ k ϖ = 0) :
    letI := isLocalRing_specialFiber hP hϖ
    specialFiberMultiplicity R ρu P ϖ = hilbertSamuelMultiplicity (SpecialFiber R ρu P ϖ) :=
  letI := isLocalRing_specialFiber hP hϖ
  localMultiplicity_eq _

end Points

end Langlands
