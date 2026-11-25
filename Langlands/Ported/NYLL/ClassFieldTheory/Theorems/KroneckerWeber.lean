/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/KroneckerWeber.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.Core

/-!
# Kronecker--Weber theorem

Let `L` be a number field that is finite abelian over `ℚ`.  Kronecker--Weber
asserts that `L` is contained in a cyclotomic extension: there is a positive
integer `n` and a `ℚ`-algebra embedding of `L` into `ℚ(ζₙ)`.  The positivity
condition excludes the degenerate order-zero cyclotomic construction.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- **Kronecker--Weber.** Every finite abelian extension of `ℚ` embeds in a
cyclotomic field of positive order. -/
theorem kroneckerWeber
    (L : Type u) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  KroneckerWeber.exists_cyclotomicEmbedding L

end ClassFieldTheory
