/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The Weil group of a nonarchimedean local field

This file gives the vocabulary that the statements of local class field theory and of the local Langlands correspondence use. It follows option (a) of question Q-04 of the spec: the Weil group is a subgroup of the absolute Galois group, with a finer topology.

Let $K$ be a nonarchimedean local field, with ring of integers $\mathcal{O}_K$, maximal ideal $\mathfrak{m}_K$ and finite residue field $k$. Let $\bar K$ be an algebraic closure of $K$ and let $G_K = \mathrm{Gal}(\bar K / K)$.

* `Langlands.LocalField.integers` is the integral closure $\bar{\mathcal{O}}$ of $\mathcal{O}_K$ in $\bar K$.
* `Langlands.LocalField.prime` is a maximal ideal $\bar{\mathfrak{m}}$ of $\bar{\mathcal{O}}$ over $\mathfrak{m}_K$. The field $\bar k = \bar{\mathcal{O}} / \bar{\mathfrak{m}}$ is an algebraic closure of $k$, but this file does not need that fact.
* `Langlands.LocalField.residueHom` is the map from the stabilizer of $\bar{\mathfrak{m}}$ in $G_K$ to $\mathrm{Gal}(\bar k / k)$.
* `Langlands.LocalField.frobenius` is the arithmetic Frobenius $x \mapsto x^q$ of $\bar k / k$.
* `Langlands.WeilGroup K` is the group of elements of the stabilizer whose image in $\mathrm{Gal}(\bar k / k)$ is an integral power of the Frobenius.
* Its topology is the coarsest topology that makes the inclusion into $G_K$ continuous and the map to $\mathrm{Gal}(\bar k / k)$ locally constant. Thus the inertia subgroup is open, and it has the Krull topology.
* `Langlands.WeilGroup.IsGeometricFrobenius` says that an element acts on $\bar k$ as $x \mapsto x^{1/q}$. The statements of the project use the geometric normalization.
* `Langlands.WeilGroup.Ab` is the topological abelianization $W_K^{ab}$, and `Langlands.WeilGroup.Ab.restrict` is its map to the Galois group of a finite abelian extension.

## Implementation notes

The choice of $\bar{\mathfrak{m}}$ is made once, with `Classical.choose`. A different choice gives a conjugate subgroup of $G_K$. The definitions do not depend on the fact that $\bar{\mathfrak{m}}$ is unique, which is true because $\mathcal{O}_K$ is henselian.

The degree map $W_K \to \mathbb{Z}$ is not defined here. It needs the fact that the Frobenius has infinite order, which is part of milestone S1.

## References

* J. Tate, Number theoretic background, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979, section 1.
* J.-P. Serre, Local class field theory, in Algebraic number theory (Cassels and Frohlich, eds.), 1967.
-/

namespace Langlands

open ValuativeRel IsLocalRing

open scoped Pointwise

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace LocalField

/-- The absolute Galois group acts on the algebraic closure. Instance search does not unfold `Field.absoluteGaloisGroup`, so the action is given here. -/
noncomputable instance : MulSemiringAction (Field.absoluteGaloisGroup K) (AlgebraicClosure K) :=
  inferInstanceAs (MulSemiringAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _)

instance : SMulCommClass (Field.absoluteGaloisGroup K) 𝒪[K] (AlgebraicClosure K) where
  smul_comm g r x := by
    let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
    change σ (r • x) = r • σ x
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (σ x)]
    exact map_smul σ _ x

/-- The integral closure of $\mathcal{O}_K$ in $\bar K$. -/
abbrev integers : Type u :=
  integralClosure 𝒪[K] (AlgebraicClosure K)

instance : FaithfulSMul 𝒪[K] (integers K) := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h => ?_
  have h' : algebraMap 𝒪[K] (AlgebraicClosure K) a = algebraMap 𝒪[K] (AlgebraicClosure K) b :=
    congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply 𝒪[K] K (AlgebraicClosure K),
    IsScalarTower.algebraMap_apply 𝒪[K] K (AlgebraicClosure K)] at h'
  exact Subtype.ext ((algebraMap K (AlgebraicClosure K)).injective h')

theorem exists_prime : ∃ P : Ideal (integers K), P.IsMaximal ∧ P.LiesOver 𝓂[K] :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral _

/-- A maximal ideal $\bar{\mathfrak{m}}$ of the integral closure over the maximal ideal of $\mathcal{O}_K$. -/
noncomputable def prime : Ideal (integers K) :=
  (exists_prime K).choose

instance : (prime K).IsMaximal :=
  (exists_prime K).choose_spec.1

instance : (prime K).LiesOver 𝓂[K] :=
  (exists_prime K).choose_spec.2

/-- The residue field $k = \mathcal{O}_K / \mathfrak{m}_K$, as a quotient. -/
abbrev residueField : Type u :=
  𝒪[K] ⧸ 𝓂[K]

/-- The residue field $\bar k = \bar{\mathcal{O}} / \bar{\mathfrak{m}}$ of the integral closure. -/
abbrev residueFieldBar : Type u :=
  integers K ⧸ prime K

noncomputable instance : Field (residueField K) :=
  Ideal.Quotient.field _

noncomputable instance : Field (residueFieldBar K) :=
  Ideal.Quotient.field _

noncomputable instance : Fintype (residueField K) :=
  haveI : Finite (residueField K) := inferInstanceAs (Finite 𝓀[K])
  Fintype.ofFinite _

instance : Algebra.IsIntegral (residueField K) (residueFieldBar K) :=
  Ideal.Quotient.algebra_isIntegral_of_liesOver (prime K) 𝓂[K]

instance : Algebra.IsAlgebraic (residueField K) (residueFieldBar K) :=
  Algebra.IsIntegral.isAlgebraic

/-- The map from the stabilizer of $\bar{\mathfrak{m}}$ in $G_K$ to $\mathrm{Gal}(\bar k / k)$. -/
noncomputable def residueHom :
    MulAction.stabilizer (Field.absoluteGaloisGroup K) (prime K) →*
      (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) :=
  Ideal.Quotient.stabilizerHom (prime K) 𝓂[K] (Field.absoluteGaloisGroup K)

/-- The arithmetic Frobenius $x \mapsto x^q$ of $\bar k / k$, where $q$ is the order of $k$. -/
noncomputable def frobenius : residueFieldBar K ≃ₐ[residueField K] residueFieldBar K :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (residueField K) (residueFieldBar K)

/-- The Weil group as a subgroup of $G_K$: the elements of the stabilizer of $\bar{\mathfrak{m}}$ that act on $\bar k$ as an integral power of the Frobenius. -/
noncomputable def weilSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  ((Subgroup.zpowers (frobenius K)).comap (residueHom K)).map
    (MulAction.stabilizer (Field.absoluteGaloisGroup K) (prime K)).subtype

theorem weilSubgroup_le_stabilizer :
    weilSubgroup K ≤ MulAction.stabilizer (Field.absoluteGaloisGroup K) (prime K) :=
  Subgroup.map_subtype_le _

end LocalField

open LocalField

/-- The Weil group $W_K$ of a nonarchimedean local field $K$. -/
def WeilGroup : Type u :=
  LocalField.weilSubgroup K

namespace WeilGroup

noncomputable instance instGroup : Group (WeilGroup K) :=
  inferInstanceAs (Group (LocalField.weilSubgroup K))

/-- The inclusion $W_K \to G_K$. -/
noncomputable def toGalois : WeilGroup K →* Field.absoluteGaloisGroup K :=
  (LocalField.weilSubgroup K).subtype

/-- The action of $W_K$ on the residue field $\bar k$. -/
noncomputable def toResidue :
    WeilGroup K →* (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) :=
  (residueHom K).comp (Subgroup.inclusion (weilSubgroup_le_stabilizer K))

/-- The topology of $W_K$: the coarsest topology that makes `toGalois` continuous and `toResidue` locally constant. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (WeilGroup K) :=
  TopologicalSpace.induced (toGalois K) inferInstance ⊓
    TopologicalSpace.induced (toResidue K) ⊥

instance instIsTopologicalGroup : IsTopologicalGroup (WeilGroup K) := by
  let t : TopologicalSpace (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) := ⊥
  have : DiscreteTopology (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) := ⟨rfl⟩
  exact isTopologicalGroup_inf (isTopologicalGroup_induced (toGalois K))
    (isTopologicalGroup_induced (toResidue K))

theorem toGalois_injective : Function.Injective (toGalois K) :=
  Subtype.val_injective

theorem continuous_toGalois : Continuous (toGalois K) :=
  continuous_iff_le_induced.mpr inf_le_left

/-- The map to $\mathrm{Gal}(\bar k / k)$ is locally constant: each fibre is open. -/
theorem isOpen_fiber_toResidue (σ : residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) :
    IsOpen (toResidue K ⁻¹' {σ}) := by
  let t : TopologicalSpace (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) := ⊥
  have : DiscreteTopology (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) := ⟨rfl⟩
  have hc : Continuous (toResidue K) := continuous_iff_le_induced.mpr inf_le_right
  exact (isOpen_discrete {σ}).preimage hc

/-- The inertia subgroup $I_K$: the kernel of the action on $\bar k$. -/
noncomputable def inertia : Subgroup (WeilGroup K) :=
  (toResidue K).ker

theorem isOpen_inertia : IsOpen (inertia K : Set (WeilGroup K)) :=
  isOpen_fiber_toResidue K 1

/-- An element of $W_K$ is a geometric Frobenius if it acts on $\bar k$ as the inverse of $x \mapsto x^q$. -/
def IsGeometricFrobenius (w : WeilGroup K) : Prop :=
  toResidue K w = (LocalField.frobenius K)⁻¹

/-- The topological abelianization $W_K^{ab}$. -/
abbrev Ab : Type u :=
  TopologicalAbelianization (WeilGroup K)

/-- The restriction $W_K \to \mathrm{Gal}(L / K)$ for a normal extension $L$ of $K$ in $\bar K$. -/
noncomputable def restrict (L : IntermediateField K (AlgebraicClosure K)) [Normal K L] :
    WeilGroup K →* Gal(L/K) :=
  (AlgEquiv.restrictNormalHom L).comp (toGalois K)

theorem ker_restrict (L : IntermediateField K (AlgebraicClosure K)) [Normal K L] :
    (restrict K L).ker = L.fixingSubgroup.comap (toGalois K) := by
  ext w
  change AlgEquiv.restrictNormalHom L (toGalois K w) = 1 ↔
    (toGalois K w : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ∈ L.fixingSubgroup
  rw [← IntermediateField.restrictNormalHom_ker]
  exact MonoidHom.mem_ker.symm

theorem isClosed_ker_restrict (L : IntermediateField K (AlgebraicClosure K)) [Normal K L]
    [FiniteDimensional K L] : IsClosed ((restrict K L).ker : Set (WeilGroup K)) := by
  rw [ker_restrict]
  exact L.fixingSubgroup_isClosed.preimage (continuous_toGalois K)

open scoped IsMulCommutative in
/-- The restriction $W_K^{ab} \to \mathrm{Gal}(L / K)$ for a finite abelian extension $L$ of $K$ in $\bar K$. -/
noncomputable def Ab.restrict (L : IntermediateField K (AlgebraicClosure K)) [IsAbelianGalois K L]
    [FiniteDimensional K L] : Ab K →* Gal(L/K) :=
  QuotientGroup.lift _ (WeilGroup.restrict K L)
    (Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (isClosed_ker_restrict K L))

theorem Ab.restrict_mk (L : IntermediateField K (AlgebraicClosure K)) [IsAbelianGalois K L]
    [FiniteDimensional K L] (w : WeilGroup K) :
    Ab.restrict K L (QuotientGroup.mk w) = WeilGroup.restrict K L w :=
  rfl

end WeilGroup

end Langlands
