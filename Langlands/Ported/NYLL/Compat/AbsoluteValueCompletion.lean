/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
-- Part of the port of n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565. This file is not in the source. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The API of `AbsoluteValue.Completion` of the source Mathlib

The source of the port uses a later Mathlib, in which `AbsoluteValue.Completion v` is a
one-field structure that wraps `UniformSpace.Completion (WithAbs v)`. In the Mathlib of the
project pin `AbsoluteValue.Completion v` is an abbreviation for
`UniformSpace.Completion (WithAbs v)`. This file states the part of the later API that the
ported files use, for the abbreviation: `toCompletion`, `ofCompletion` and `equiv` are
identities, and `map` is `UniformSpace.Completion.mapRingHom` of `WithAbs.map`. The names and
the statements are those of `Mathlib/Analysis/Normed/Field/WithAbs.lean` of the source Mathlib.
-/

@[expose] public section

noncomputable section

namespace AbsoluteValue.Completion

open WithAbs

variable {J K L : Type*} [Field J] [Field K] [Field L]
  [Algebra J K] [Algebra J L] [Algebra K L] [IsScalarTower J K L]
  (u : AbsoluteValue J ℝ) (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)

/-- The identity of `v.Completion` as a ring isomorphism onto the uniform-space completion. -/
def equiv : v.Completion ≃+* UniformSpace.Completion (WithAbs v) :=
  RingEquiv.refl _

variable {v}

/-- The ring homomorphism from `v.Completion` to `UniformSpace.Completion (WithAbs v)`. -/
def toCompletion : v.Completion →+* UniformSpace.Completion (WithAbs v) :=
  RingHom.id _

/-- The ring homomorphism from `UniformSpace.Completion (WithAbs v)` to `v.Completion`. -/
def ofCompletion : UniformSpace.Completion (WithAbs v) →+* v.Completion :=
  RingHom.id _

@[simp]
theorem equiv_apply (x : v.Completion) : equiv v x = toCompletion x := rfl

@[simp]
theorem equiv_symm_apply (x : UniformSpace.Completion (WithAbs v)) :
    (equiv v).symm x = ofCompletion x := rfl

@[simp]
theorem toCompletion_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    toCompletion (ofCompletion x) = x := rfl

@[simp]
theorem ofCompletion_toCompletion (x : v.Completion) : ofCompletion (toCompletion x) = x := rfl

variable (v)

theorem toCompletion_injective : Function.Injective (toCompletion (v := v)) :=
  (equiv v).injective

theorem ofCompletion_injective : Function.Injective (ofCompletion (v := v)) :=
  (equiv v).symm.injective

theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equiv v).surjective

theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equiv v).symm.surjective

variable {v}

@[simp]
theorem toCompletion_inj {x y : v.Completion} : toCompletion x = toCompletion y ↔ x = y :=
  (toCompletion_injective v).eq_iff

@[simp]
theorem ofCompletion_inj {x y : UniformSpace.Completion (WithAbs v)} :
    ofCompletion x = ofCompletion y ↔ x = y :=
  (ofCompletion_injective v).eq_iff

@[simp]
theorem norm_toCompletion (x : v.Completion) : ‖toCompletion x‖ = ‖x‖ := rfl

@[simp]
theorem norm_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl

variable (v)

theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

theorem isometry_ofCompletion : Isometry (ofCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous

theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometry_ofCompletion v).continuous

variable {v}

/-- The coercion from `WithAbs v` to `v.Completion`. -/
abbrev coe (x : WithAbs v) : v.Completion :=
  (x : UniformSpace.Completion (WithAbs v))

@[simp]
theorem toCompletion_coe (x : WithAbs v) :
    toCompletion (x : v.Completion) = (x : UniformSpace.Completion (WithAbs v)) := rfl

@[simp]
theorem ofCompletion_coe (x : WithAbs v) :
    ofCompletion (x : UniformSpace.Completion (WithAbs v)) = (x : v.Completion) := rfl

theorem coe_zero : ((0 : WithAbs v) : v.Completion) = 0 :=
  UniformSpace.Completion.coe_zero

theorem coe_one : ((1 : WithAbs v) : v.Completion) = 1 :=
  UniformSpace.Completion.coe_one _

theorem coe_add (x y : WithAbs v) : ((x + y : WithAbs v) : v.Completion) = x + y :=
  UniformSpace.Completion.coe_add x y

theorem coe_mul (x y : WithAbs v) : ((x * y : WithAbs v) : v.Completion) = x * y :=
  UniformSpace.Completion.coe_mul x y

theorem coe_neg (x : WithAbs v) : ((-x : WithAbs v) : v.Completion) = -x :=
  UniformSpace.Completion.coe_neg x

theorem coe_sub (x y : WithAbs v) : ((x - y : WithAbs v) : v.Completion) = x - y :=
  UniformSpace.Completion.coe_sub x y

theorem coe_inv (x : WithAbs v) : ((x⁻¹ : WithAbs v) : v.Completion) = (↑x)⁻¹ :=
  (UniformSpace.Completion.coe_inv x).symm

theorem norm_coe (x : WithAbs v) : ‖(x : v.Completion)‖ = v x.ofAbs :=
  UniformSpace.Completion.norm_coe x

variable (v)

theorem continuous_coe : Continuous ((↑) : WithAbs v → v.Completion) :=
  UniformSpace.Completion.continuous_coe _

theorem denseRange_coe : DenseRange ((↑) : WithAbs v → v.Completion) :=
  UniformSpace.Completion.denseRange_coe

variable {v}

/-- Induction on the completion of a field at an absolute value: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : v.Completion → Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : ∀ a : WithAbs v, p a) : p x :=
  UniformSpace.Completion.induction_on (p := p) x hp ih

/-- Two continuous functions out of `v.Completion` into a Hausdorff space that agree on `K`
are equal. -/
theorem ext {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : v.Completion → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : WithAbs v, f a = g a) : f = g :=
  (denseRange_coe v).equalizer hf hg (funext h)

variable (v)

section Algebra

variable {R : Type*} [CommSemiring R] [Algebra R (WithAbs v)]
  [UniformContinuousConstSMul R (WithAbs v)]

theorem toCompletion_algebraMap (r : R) :
    toCompletion (algebraMap R v.Completion r) =
      algebraMap R (UniformSpace.Completion (WithAbs v)) r := rfl

theorem ofCompletion_algebraMap (r : R) :
    ofCompletion (algebraMap R (UniformSpace.Completion (WithAbs v)) r) =
      algebraMap R v.Completion r := rfl

theorem algebraMap_def (r : R) :
    algebraMap R v.Completion r = (algebraMap R (WithAbs v) r : v.Completion) := rfl

end Algebra

section LiesOver

variable [v.LiesOver u] [w.LiesOver u] [w.LiesOver v]

/-- If `w` lies over `v`, the ring homomorphism `v.Completion →+* w.Completion` induced by
`algebraMap K L`. -/
def map : v.Completion →+* w.Completion :=
  UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
    (WithAbs.isometry_map v w).continuous

theorem isometry_map : Isometry (map v w) :=
  UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)

theorem continuous_map : Continuous (map v w) := (isometry_map v w).continuous

@[simp]
theorem map_coe (x : WithAbs v) :
    map v w (x : v.Completion) = WithAbs.map v w (algebraMap K L) x :=
  UniformSpace.Completion.mapRingHom_coe (WithAbs.isometry_map v w).continuous x

@[simp]
theorem map_comp_map : (map v w).comp (map u v) = map u w :=
  DFunLike.ext' <| ext ((continuous_map v w).comp (continuous_map u v)) (continuous_map u w)
    (by simp [IsScalarTower.algebraMap_apply J K L])

@[simp]
theorem map_map (x : u.Completion) : map v w (map u v x) = map u w x :=
  congr($(map_comp_map u v w) x)

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

theorem algebraMap_eq_of_liesOver : algebraMap v.Completion w.Completion = map v w :=
  algebraMap_eq v w

theorem algebraMap_apply_of_liesOver (x : v.Completion) :
    algebraMap v.Completion w.Completion x = map v w x := by
  rw [algebraMap_eq_of_liesOver]

end LiesOver

end AbsoluteValue.Completion
