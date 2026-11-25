/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsEverywhereUnramified.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Unramifiedness at every place
-/



@[expose] public section

namespace ClassFieldTheory

universe u v

/-- A number-field extension is unramified at all finite and infinite places. -/
def IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  IsUnramifiedAtFinitePlaces K L ∧ IsUnramifiedAtInfinitePlaces K L

end ClassFieldTheory
