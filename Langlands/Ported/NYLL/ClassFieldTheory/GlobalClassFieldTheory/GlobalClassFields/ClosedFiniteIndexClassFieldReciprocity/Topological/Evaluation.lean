/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/Evaluation.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore

/-!
# Evaluation of continuous closed finite-index reciprocity

The public theorem uses the named reducible value provider and specializes
the generic transported-reciprocity calculation.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type u} [Field K] [NumberField K]

/-- Evaluation of the selected class-field equivalence is the named inverse
global norm-residue value in the quotient by the defining subgroup. -/
@[simp]
theorem
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
        (K := K) H hclosed σ =
      closedFiniteIndexClassFieldReciprocityValue
        (K := K) H hclosed σ :=
  globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply
    H
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) H hclosed)
    σ

end GlobalClassFields
end GlobalClassFieldTheory
