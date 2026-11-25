/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/FiniteAbelianLocalExtension.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FiniteAbelianExtension

/-!
# Finite abelian local extensions
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension of `K` inside Mathlib's chosen separable
closure.  The inherited order is field inclusion. -/
abbrev FiniteAbelianLocalExtension
    (K : Type u) [Field K] :=
  FiniteAbelianExtension K

namespace FiniteAbelianLocalExtension

variable {K : Type u} [Field K]

/-- The norm subgroup belonging to a packaged finite abelian extension. -/
def normSubgroup (E : FiniteAbelianLocalExtension K) : Subgroup Kˣ :=
  localNormSubgroup K E.1

end FiniteAbelianLocalExtension

end ClassFieldTheory
