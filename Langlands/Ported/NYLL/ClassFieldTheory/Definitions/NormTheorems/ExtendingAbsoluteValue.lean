/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/ExtendingAbsoluteValue.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.AbsoluteValue

/-!
# Absolute values above a fixed absolute value

This index type uses only Mathlib's absolute values and algebra map.  Its
elements are precisely the absolute values on `L` extending `v` on `K`.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- An absolute value on `L` whose restriction along `K → L` is `v`. -/
abbrev ExtendingAbsoluteValue
    {K : Type u} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  { w : AbsoluteValue L ℝ // ∀ a : K, w (algebraMap K L a) = v a }

end ClassFieldTheory
