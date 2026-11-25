/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/EvaluationValue.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction

/-!
# Named value of closed finite-index reciprocity

The expanded inverse norm-residue expression is kept behind one reducible
value provider.  Public evaluation statements can therefore mention the
selected class-field instance tower once while remaining definitionally
equivalent to the historical formula.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity


variable {K : Type u} [Field K] [NumberField K]

/-- The quotient value prescribed by inverse global norm-residue reciprocity
for a Galois element of the selected closed finite-index class field. -/
noncomputable abbrev closedFiniteIndexClassFieldReciprocityValue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    IdeleClassGroup K ⧸ H :=
  QuotientGroup.quotientMulEquivOfEq
      (closedFiniteIndexClassField_ideleClassNorm_range
        (K := K) H hclosed)
    (Additive.toMul
      ((globalNormResidueEquiv K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).symm
        (Additive.ofMul σ)))

end GlobalClassFields
end GlobalClassFieldTheory
