/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Algebraic/Evaluation.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction

/-!
# Evaluation of algebraic closed finite-index reciprocity

Since the algebraic equivalence is definitionally the underlying
multiplicative equivalence of the continuous provider, its evaluation theorem
is inherited without reconstructing the selected class-field instance tower.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type u} [Field K] [NumberField K]

/-- Evaluation of the direct non-topological reciprocity equivalence. -/
@[simp]
theorem closedFiniteIndexClassFieldGaloisEquivNormQuotient_apply
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) H hclosed σ =
      closedFiniteIndexClassFieldReciprocityValue
        (K := K) H hclosed σ :=
  closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply
    (K := K) H hclosed σ

end GlobalClassFields
end GlobalClassFieldTheory
