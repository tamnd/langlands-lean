/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
-- Part of the port of n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565. This file is not in the source. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.Compat.InfinitePlaceCompletion

/-!
# The map `AbsoluteValue.Completion.map` between completions at infinite places

In the Mathlib of the source of the port, `InfinitePlace.Completion v` is an abbreviation for
`v.1.Completion`, so the source applies `AbsoluteValue.Completion.map v.1 w.1` to elements of
`v.Completion`. In the Mathlib of the project pin `InfinitePlace.Completion v` is a structure
over `v.1.Completion`. This file defines `absMap v w : v.Completion →+* w.Completion`, which is
`AbsoluteValue.Completion.map v.1 w.1` between `toCompletion` and `ofCompletion`, and states
the lemmas of `AbsoluteValue.Completion.map` for it.
-/

@[expose] public section

noncomputable section

namespace NumberField.InfinitePlace.Completion

section Map

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]

/-- `AbsoluteValue.Completion.map v.1 w.1` as a map between the completions at the infinite
places `v` and `w`. -/
def absMap : v.Completion →+* w.Completion :=
  ((equiv w).symm.toRingHom.comp (AbsoluteValue.Completion.map v.1 w.1)).comp
    (equiv v).toRingHom

theorem toCompletion_absMap (x : v.Completion) :
    (absMap v w x).toCompletion = AbsoluteValue.Completion.map v.1 w.1 x.toCompletion :=
  rfl

theorem absMap_ofCompletion (x : v.1.Completion) :
    absMap v w (ofCompletion x) = ofCompletion (AbsoluteValue.Completion.map v.1 w.1 x) :=
  rfl

theorem isometry_absMap : Isometry (absMap v w) :=
  Isometry.of_dist_eq fun x y ↦
    (AbsoluteValue.Completion.isometry_map v.1 w.1).dist_eq x.toCompletion y.toCompletion

theorem continuous_absMap : Continuous (absMap v w) :=
  (continuous_ofCompletion w).comp
    ((AbsoluteValue.Completion.continuous_map v.1 w.1).comp (continuous_toCompletion v))

theorem absMap_coe (x : WithAbs v.1) :
    absMap v w (x : v.Completion) = (WithAbs.map v.1 w.1 (algebraMap K L) x : w.Completion) :=
  ext (AbsoluteValue.Completion.map_coe v.1 w.1 x)

/-- `absMap` is the map `NumberField.LiesOver.completionMap` of the Mathlib of the project
pin. -/
theorem absMap_eq_completionMap (x : v.Completion) :
    absMap v w x = NumberField.LiesOver.completionMap v w x :=
  ext (toCompletion_completionMap v w x).symm

/-- The algebra structure of `w.Completion` over `v.Completion` given by `absMap`. It is the
algebra `AbsoluteValue.Completion.algebraOfLiesOver v.1 w.1` between `toCompletion` and
`ofCompletion`. -/
@[instance_reducible]
def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (absMap v w).toAlgebra

theorem algebraMap_apply_of_liesOver (x : v.Completion) :
    letI := algebraOfLiesOver v w
    algebraMap v.Completion w.Completion x = absMap v w x :=
  rfl

theorem algebraMap_eq_of_liesOver :
    letI := algebraOfLiesOver v w
    algebraMap v.Completion w.Completion = absMap v w :=
  rfl

/-- `algebraOfLiesOver` is the scoped algebra instance of `NumberField.LiesOver` of the Mathlib
of the project pin. The two are also definitionally equal, so the lemmas of the pin for that
instance apply to `algebraOfLiesOver`. -/
theorem algebraOfLiesOver_eq_toAlgebra :
    algebraOfLiesOver v w = (NumberField.LiesOver.completionMap v w).toAlgebra :=
  Algebra.algebra_ext _ _ fun x ↦ absMap_eq_completionMap v w x

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  letI := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦ ext <| by
    change algebraMap K w.1.Completion x =
      AbsoluteValue.Completion.map v.1 w.1 (algebraMap K v.1.Completion x)
    let := AbsoluteValue.Completion.algebraOfLiesOver v.1 w.1
    rw [← AbsoluteValue.Completion.algebraMap_apply_of_liesOver]
    exact IsScalarTower.algebraMap_apply K v.1.Completion w.1.Completion x

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  letI := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion (continuous_absMap v w)

end Map

section Tower

variable {J K L : Type*} [Field J] [Field K] [Field L]
  [Algebra J K] [Algebra J L] [Algebra K L] [IsScalarTower J K L]
  (u : InfinitePlace J) (v : InfinitePlace K) (w : InfinitePlace L)
  [v.1.LiesOver u.1] [w.1.LiesOver u.1] [w.1.LiesOver v.1]

theorem absMap_absMap (x : u.Completion) : absMap v w (absMap u v x) = absMap u w x :=
  ext (AbsoluteValue.Completion.map_map u.1 v.1 w.1 x.toCompletion)

end Tower

end NumberField.InfinitePlace.Completion
