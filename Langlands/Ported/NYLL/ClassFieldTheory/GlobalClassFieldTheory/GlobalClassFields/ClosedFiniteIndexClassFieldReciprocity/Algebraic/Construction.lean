/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Algebraic/Construction.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation

/-!
# Underlying algebraic closed finite-index reciprocity

The algebraic equivalence is obtained by forgetting topology from the named
continuous provider.  This avoids a second specialization of the full finite
global reciprocity instance tower.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields


variable {K : Type u} [Field K] [NumberField K]

/-- Global reciprocity for the selected class field, stated over the original
number field and directly modulo its defining subgroup. -/
noncomputable abbrev closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃*
      IdeleClassGroup K ⧸ H :=
  (closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
    (K := K) H hclosed).toMulEquiv

end GlobalClassFields
end GlobalClassFieldTheory
