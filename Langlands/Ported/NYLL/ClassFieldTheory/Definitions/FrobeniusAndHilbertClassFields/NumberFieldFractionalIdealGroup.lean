/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/NumberFieldFractionalIdealGroup.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Fractional-ideal group of a number field
-/



@[expose] public section

open scoped NumberField
open NumberField

namespace ClassFieldTheory

universe u

/-- The group of nonzero fractional ideals of a number field. -/
abbrev NumberFieldFractionalIdealGroup
    (K : Type u) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

end ClassFieldTheory
