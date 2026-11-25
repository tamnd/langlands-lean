/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ValuedFieldTheory/LocalField/Padic/Cyclotomic/TotallyRamified/IntegralTranslate.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation

/-!
# Translation of the integral ring in the totally ramified cyclotomic extension

This file records that translating `ζ` by one preserves the explicit integral closure.
-/

@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

attribute [local instance] padicCyclotomicTotallyRamifiedAlgebraPadicInt
  padicCyclotomicTotallyRamifiedScalarTowerPadicInt

/-- Translating the generator by one does not change the explicit
`ℤ_[p]`-algebra. -/
theorem padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin
    (ζ : L) :
    Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) =
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subalgebra.sub_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
      (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa using Subalgebra.add_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
      (Subalgebra.one_mem _)

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
