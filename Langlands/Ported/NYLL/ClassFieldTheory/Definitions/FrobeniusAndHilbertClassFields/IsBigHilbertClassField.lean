/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsBigHilbertClassField.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

/-!
# Big Hilbert class fields
-/



@[expose] public section

namespace ClassFieldTheory

universe u

/-- A big Hilbert class field is a finite-prime-unramified finite abelian
extension containing every finite abelian extension unramified at the finite
places.  Ramification at real places is allowed. -/
def IsBigHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Prop :=
  IsUnramifiedAtFinitePlaces K E ∧
    ∀ F : FiniteAbelianExtension K,
      IsUnramifiedAtFinitePlaces K F → Nonempty (F →ₐ[K] E)

end ClassFieldTheory
