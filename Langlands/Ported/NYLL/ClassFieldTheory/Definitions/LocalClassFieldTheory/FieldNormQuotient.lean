/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormQuotient.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The field-norm quotient
-/



@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The norm quotient `Kˣ / N_{L/K}(Lˣ)`. -/
abbrev FieldNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :=
  Kˣ ⧸ localNormSubgroup K L

end ClassFieldTheory
