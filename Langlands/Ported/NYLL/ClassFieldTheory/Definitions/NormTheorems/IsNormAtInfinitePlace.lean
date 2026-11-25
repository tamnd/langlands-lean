/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/IsNormAtInfinitePlace.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Norms at infinite places
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

namespace ClassFieldTheory

universe u v

/-- A unit of `K` is a norm at an infinite place `w` if its image in the
completion `K_w` is a determinant norm from `K_w ⊗_K L`. -/
def IsNormAtInfinitePlace
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace K) (x : Kˣ) : Prop :=
  ∃ y : (w.Completion ⊗[K] L)ˣ,
    Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
      algebraMap K w.Completion (x : K)

end ClassFieldTheory
