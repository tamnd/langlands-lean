/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
-- Part of the port of n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565. This file is not in the source. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Langlands.Ported.NYLL.Compat.AbsoluteValueCompletion

/-!
# Completions at infinite places and completions at absolute values

In the Mathlib of the source of the port, `InfinitePlace.Completion v` is an abbreviation for
`v.1.Completion`, and the map between completions at places `w` over `v` is
`AbsoluteValue.Completion.map v.1 w.1`. In the Mathlib of the project pin,
`InfinitePlace.Completion v` is a one-field structure over `v.1.Completion`, with
`toCompletion` and `ofCompletion`, and the map between completions is
`NumberField.LiesOver.completionMap v w`. This file proves that the two maps agree under
`toCompletion`.
-/

@[expose] public section

noncomputable section

namespace NumberField.InfinitePlace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- The map `v.Completion →+* w.Completion` of the Mathlib of the project pin is
`AbsoluteValue.Completion.map v.1 w.1` under `toCompletion`. -/
theorem toCompletion_completionMap (x : v.Completion) :
    (NumberField.LiesOver.completionMap v w x).toCompletion =
      AbsoluteValue.Completion.map v.1 w.1 x.toCompletion := by
  obtain ⟨y, rfl⟩ := ofCompletion_surjective v x
  change (NumberField.LiesOver.completionMap v w (ofCompletion y)).toCompletion =
    AbsoluteValue.Completion.map v.1 w.1 y
  refine AbsoluteValue.Completion.induction_on y ?_ ?_
  · exact isClosed_eq
      ((continuous_toCompletion w).comp
        ((NumberField.LiesOver.continuous_completionMap v w).comp (continuous_ofCompletion v)))
      (AbsoluteValue.Completion.continuous_map v.1 w.1)
  · intro a
    rw [AbsoluteValue.Completion.map_coe]
    exact congrArg toCompletion (NumberField.LiesOver.completionMap_coe v w a)

/-- `NumberField.LiesOver.completionMap v w` is `AbsoluteValue.Completion.map v.1 w.1` between
`toCompletion` and `ofCompletion`. -/
theorem completionMap_eq_ofCompletion (x : v.Completion) :
    NumberField.LiesOver.completionMap v w x =
      ofCompletion (AbsoluteValue.Completion.map v.1 w.1 x.toCompletion) :=
  ext (toCompletion_completionMap v w x)

end NumberField.InfinitePlace.Completion
