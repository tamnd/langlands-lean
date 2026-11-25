/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FiniteAbelianExtension.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FiniteAbelianExtension
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Number-field structure on finite abelian extensions

The finite abelian carrier and its algebraic instances are shared with local
and function-field class field theory. This module adds only the number-field
structure on an extension of a number field.
-/

@[expose] public section

namespace ClassFieldTheory.FiniteAbelianExtension

universe u

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : NumberField E :=
  NumberField.of_module_finite K E

end ClassFieldTheory.FiniteAbelianExtension
