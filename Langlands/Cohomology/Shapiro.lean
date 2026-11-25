/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Shapiro's lemma in degree one for continuous cohomology

Let $G$ be a topological group, let $H$ be an open subgroup, and let $A$ be a commutative topological group with the trivial action. This file proves that $H^1(G, \mathrm{Coind}_H^G A)$ is isomorphic to the group of continuous homomorphisms $H \to A$. The local Langlands correspondence for an induced torus $\mathrm{Res}_{L/K} \mathbb{G}_m$ uses this result with $G = W_K$, $H = W_L$ and $A = \mathbb{C}^\times$.

* `Langlands.Shapiro.contCocycles`, `Langlands.Shapiro.coboundaries` and `Langlands.Shapiro.H1`: continuous one-cocycles, coboundaries and the first continuous cohomology group, in multiplicative notation.
* `Langlands.Shapiro.Coind`: the functions $f : G \to A$ with $f(hg) = f(g)$ for $h \in H$, with the action $(g \cdot f)(x) = f(xg)$.
* `Langlands.Shapiro.shapiro`: the isomorphism $H^1(G, \mathrm{Coind}_H^G A) \cong \mathrm{Hom}_{cts}(H, A)$. It sends the class of $z$ to $h \mapsto z(h)(1)$.
* `Langlands.Shapiro.shapiro_top`: for $H = G$ the isomorphism sends the constant cocycle of $\varphi$ back to $\varphi$. This is a check F2.

## Implementation notes

The inverse map uses a choice of a representative in each coset $Hx$. The openness of $H$ is used only to show that the cocycle built from these representatives is continuous.
-/

open Topology

namespace Langlands.Shapiro

set_option linter.unusedSectionVars false

section General

variable (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- The subgroup of continuous one-cocycles, namely continuous maps `z : G → M` with `z (g₁ * g₂) = z g₁ * g₁ • z g₂`. -/
def contCocycles : Subgroup (G → M) where
  carrier := {z | Continuous z ∧ ∀ g₁ g₂ : G, z (g₁ * g₂) = z g₁ * g₁ • z g₂}
  one_mem' := ⟨continuous_const, fun g₁ g₂ => by simp⟩
  mul_mem' := by
    rintro z w ⟨hz, hz'⟩ ⟨hw, hw'⟩
    refine ⟨hz.mul hw, fun g₁ g₂ => ?_⟩
    simp only [Pi.mul_apply, hz', hw', smul_mul']
    rw [mul_mul_mul_comm]
  inv_mem' := by
    rintro z ⟨hz, hz'⟩
    refine ⟨hz.inv, fun g₁ g₂ => ?_⟩
    simp only [Pi.inv_apply, hz', smul_inv', mul_inv]

/-- The type of continuous one-cocycles of `G` with values in `M`. -/
abbrev ContCocycle := ↥(contCocycles G M)

/-- The subgroup of coboundaries, namely cocycles of the form `g ↦ g • m / m` for some `m : M`. -/
def coboundaries : Subgroup (ContCocycle G M) where
  carrier := {z | ∃ m : M, ∀ g : G, z.1 g = g • m / m}
  one_mem' := ⟨1, fun g => by simp⟩
  mul_mem' := by
    rintro z w ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m * n, fun g => ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, hm, hn, smul_mul', mul_div_mul_comm]
  inv_mem' := by
    rintro z ⟨m, hm⟩
    refine ⟨m⁻¹, fun g => ?_⟩
    simp only [Subgroup.coe_inv, Pi.inv_apply, hm, smul_inv', inv_div, div_inv_eq_mul,
      inv_mul_eq_div]

/-- The first continuous cohomology group, the quotient of continuous cocycles by coboundaries. -/
abbrev H1 := ContCocycle G M ⧸ coboundaries G M

example : CommGroup (H1 G M) := inferInstance

variable {G M}

lemma ContCocycle.map_mul (z : ContCocycle G M) (g₁ g₂ : G) :
    z.1 (g₁ * g₂) = z.1 g₁ * g₁ • z.1 g₂ :=
  z.2.2 g₁ g₂

lemma ContCocycle.continuous (z : ContCocycle G M) : Continuous z.1 := z.2.1

lemma ContCocycle.map_one (z : ContCocycle G M) : z.1 1 = 1 := by
  have h := z.map_mul 1 1
  simp only [mul_one, one_smul] at h
  exact (mul_eq_left.mp h.symm)

end General

section Coind

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
  (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The coinduced module as a subgroup of `G → A`: functions invariant under left translation by `H`. -/
def coindSubgroup : Subgroup (G → A) where
  carrier := {f | ∀ h ∈ H, ∀ g : G, f (h * g) = f g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro f f' hf hf' h hh g
    simp [hf h hh g, hf' h hh g]
  inv_mem' := by
    intro f hf h hh g
    simp [hf h hh g]

/-- The coinduced module `Coind H A`, functions on `H\G` with values in `A`, with the product topology. -/
abbrev Coind := ↥(coindSubgroup H A)

variable {H A}

lemma Coind.map_left (f : Coind H A) {h : G} (hh : h ∈ H) (g : G) : f.1 (h * g) = f.1 g :=
  f.2 h hh g

/-- The right translation action of `G` on the coinduced module, `(g • f) x = f (x * g)`. -/
instance : MulDistribMulAction G (Coind H A) where
  smul g f := ⟨fun x => f.1 (x * g), fun h hh x => by simp only [mul_assoc, f.map_left hh]⟩
  one_smul f := by ext x; show f.1 (x * 1) = f.1 x; rw [mul_one]
  mul_smul g₁ g₂ f := by ext x; show f.1 (x * (g₁ * g₂)) = f.1 (x * g₁ * g₂); rw [mul_assoc]
  smul_mul g f f' := by ext x; rfl
  smul_one g := by ext x; rfl

@[simp] lemma Coind.smul_apply (g : G) (f : Coind H A) (x : G) : (g • f).1 x = f.1 (x * g) := rfl

lemma continuous_coind_iff {X : Type*} [TopologicalSpace X] (z : X → Coind H A) :
    Continuous z ↔ ∀ x : G, Continuous fun g => (z g).1 x := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff, continuous_pi_iff]
  rfl

/-- The restriction map from cocycles to homomorphisms on `H`, sending `z` to `h ↦ z h 1`. -/
def restrictHom : ContCocycle G (Coind H A) →* ContinuousMonoidHom H A where
  toFun z :=
    { toFun := fun h => (z.1 h).1 1
      map_one' := by simp [z.map_one]
      map_mul' := by
        intro h₁ h₂
        show (z.1 (h₁ * h₂)).1 1 = (z.1 h₁).1 1 * (z.1 h₂).1 1
        rw [z.map_mul]
        show (z.1 h₁).1 1 * (z.1 h₂).1 (1 * h₁) = _
        rw [one_mul, ← mul_one (h₁ : G), Coind.map_left _ h₁.2, mul_one]
      continuous_toFun :=
        ((continuous_coind_iff _).1 z.continuous 1).comp continuous_subtype_val }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma restrictHom_apply (z : ContCocycle G (Coind H A)) (h : H) :
    restrictHom z h = (z.1 h).1 1 := rfl

lemma ker_restrictHom : (restrictHom (H := H) (A := A)).ker = coboundaries G (Coind H A) := by
  ext z
  constructor
  · intro hz
    have hz1 : ∀ h : H, (z.1 h).1 1 = 1 := fun h => by
      rw [← restrictHom_apply, MonoidHom.mem_ker.mp hz]; rfl
    let n : Coind H A := ⟨fun y => (z.1 y).1 1, fun h hh y => by
      show (z.1 (h * y)).1 1 = (z.1 y).1 1
      rw [z.map_mul]
      show (z.1 h).1 1 * (z.1 y).1 (1 * h) = _
      rw [hz1 ⟨h, hh⟩, one_mul, one_mul, ← mul_one h, Coind.map_left _ hh]⟩
    refine ⟨n, fun g => ?_⟩
    ext x
    simp only [n, Subgroup.coe_div, Pi.div_apply, Coind.smul_apply, z.map_mul,
      Subgroup.coe_mul, Pi.mul_apply, one_mul]
    rw [mul_div_cancel_left]
  · rintro ⟨m, hm⟩
    rw [MonoidHom.mem_ker]
    ext h
    show (z.1 h).1 1 = 1
    rw [hm]
    show m.1 (1 * h) / m.1 1 = 1
    rw [one_mul, ← mul_one (h : G), Coind.map_left _ h.2, div_self']

section Surjective

variable (H) in
/-- A choice of representative of the right coset `H x`. -/
noncomputable def rep (x : G) : G := (Quotient.mk (QuotientGroup.rightRel H) x).out

lemma mul_rep_inv_mem (x : G) : x * (rep H x)⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel H) x)

lemma rep_mul {h : G} (hh : h ∈ H) (x : G) : rep H (h * x) = rep H x := by
  unfold rep
  congr 1
  apply Quotient.sound
  show QuotientGroup.rightRel H (h * x) x
  rw [QuotientGroup.rightRel_apply]
  simpa using H.inv_mem hh

/-- The auxiliary function `F x = φ (x * (rep x)⁻¹)`, which satisfies `F (h * x) = φ h * F x`. -/
noncomputable def auxF (φ : ContinuousMonoidHom H A) (x : G) : A :=
  φ ⟨x * (rep H x)⁻¹, mul_rep_inv_mem x⟩

lemma auxF_mul (φ : ContinuousMonoidHom H A) (h : H) (x : G) :
    auxF φ (h * x) = φ h * auxF φ x := by
  unfold auxF
  rw [← map_mul]
  congr 1
  ext
  simp [rep_mul h.2, mul_assoc]

lemma continuous_auxF (hH : IsOpen (H : Set G)) (φ : ContinuousMonoidHom H A) :
    Continuous (auxF φ) := by
  rw [continuous_iff_continuousAt]
  intro y
  let e : H → G := fun h => (h : G) * y
  have he : IsOpenEmbedding e :=
    (Homeomorph.mulRight y).isOpenEmbedding.comp hH.isOpenEmbedding_subtypeVal
  have h1 : e 1 = y := by simp [e]
  rw [← h1, ← he.continuousAt_iff]
  have : auxF φ ∘ e = fun h => φ h * auxF φ y := funext fun h => auxF_mul φ h y
  rw [this]
  exact (φ.continuous.mul continuous_const).continuousAt

/-- The cocycle attached to a continuous homomorphism `φ : H → A`, given by `z g x = F (x * g) / F x`. -/
noncomputable def cocycleOf (hH : IsOpen (H : Set G)) (φ : ContinuousMonoidHom H A) :
    ContCocycle G (Coind H A) :=
  ⟨fun g => ⟨fun x => auxF φ (x * g) / auxF φ x, fun h hh x => by
      simp only
      rw [mul_assoc, auxF_mul φ ⟨h, hh⟩, auxF_mul φ ⟨h, hh⟩, mul_div_mul_left_eq_div]⟩,
    by
      rw [continuous_coind_iff]
      intro x
      exact ((continuous_auxF hH φ).comp (continuous_const.mul continuous_id)).div'
        continuous_const,
    fun g₁ g₂ => by
      ext x
      simp only [Subgroup.coe_mul, Pi.mul_apply, Coind.smul_apply, mul_assoc]
      rw [mul_comm, div_mul_div_cancel]⟩

lemma restrictHom_cocycleOf (hH : IsOpen (H : Set G)) (φ : ContinuousMonoidHom H A) :
    restrictHom (cocycleOf hH φ) = φ := by
  ext h
  show auxF φ (1 * h) / auxF φ 1 = φ h
  have := auxF_mul φ h 1
  rw [mul_one] at this
  rw [one_mul, this, mul_div_cancel_right]

lemma restrictHom_surjective (hH : IsOpen (H : Set G)) :
    Function.Surjective (restrictHom (H := H) (A := A)) :=
  fun φ => ⟨cocycleOf hH φ, restrictHom_cocycleOf hH φ⟩

end Surjective

/-- Shapiro's lemma in degree one: for an open subgroup `H` of `G`, the first continuous cohomology of the coinduced module `Coind H A` is isomorphic to the group of continuous homomorphisms from `H` to `A`. -/
noncomputable def shapiro (hH : IsOpen (H : Set G)) :
    H1 G (Coind H A) ≃* ContinuousMonoidHom H A :=
  (QuotientGroup.quotientMulEquivOfEq ker_restrictHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictHom_surjective hH))

/-- The Shapiro isomorphism sends the class of a cocycle `z` to the homomorphism `h ↦ z h 1`. -/
@[simp] lemma shapiro_mk (hH : IsOpen (H : Set G)) (z : ContCocycle G (Coind H A)) (h : H) :
    shapiro hH (QuotientGroup.mk z) h = (z.1 h).1 1 := rfl

/-- The inverse of the Shapiro isomorphism sends `φ` to the class of the cocycle built from coset representatives. -/
lemma shapiro_symm (hH : IsOpen (H : Set G)) (φ : ContinuousMonoidHom H A) :
    (shapiro hH).symm φ = QuotientGroup.mk (cocycleOf hH φ) := by
  rw [MulEquiv.symm_apply_eq]
  ext h
  rw [shapiro_mk]
  exact (DFunLike.congr_fun (restrictHom_cocycleOf hH φ) h).symm

end Coind

section Top

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

lemma isOpen_top : IsOpen ((⊤ : Subgroup G) : Set G) := by
  rw [Subgroup.coe_top]; exact isOpen_univ

/-- For `H = ⊤`, the cocycle with constant values `g ↦ (x ↦ φ g)` attached to a continuous homomorphism `φ : G → A`. -/
def constCocycle (φ : ContinuousMonoidHom G A) : ContCocycle G (Coind (⊤ : Subgroup G) A) :=
  ⟨fun g => ⟨fun _ => φ g, fun _ _ _ => rfl⟩,
    by
      rw [continuous_coind_iff]
      intro _
      exact φ.continuous,
    fun g₁ g₂ => by
      ext x
      simp⟩

/-- Sanity check for `H = ⊤`: sending `φ` to the class of its constant cocycle and then applying Shapiro gives back `φ`. -/
theorem shapiro_top (φ : ContinuousMonoidHom G A) (g : G) :
    shapiro isOpen_top (QuotientGroup.mk (constCocycle φ)) ⟨g, Subgroup.mem_top g⟩ = φ g := rfl

/-- For `H = ⊤`, every class in `H1` is represented by a constant cocycle, so the map `φ ↦ [constCocycle φ]` composed with Shapiro is the identity. -/
theorem shapiro_symm_top (φ : ContinuousMonoidHom G A) :
    (shapiro isOpen_top).symm
      (φ.comp ⟨(⊤ : Subgroup G).subtype, continuous_subtype_val⟩) =
      QuotientGroup.mk (constCocycle φ) := by
  rw [MulEquiv.symm_apply_eq]
  ext h
  rfl

end Top

end Langlands.Shapiro
