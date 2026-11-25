/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/Construction.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport

/-!
# Continuous closed finite-index class-field reciprocity

The final equivalence composes finite global reciprocity with the generic
continuous transport induced by the exact norm-range equality.  Equality
elimination preserves the native quotient topology, so no discrete topology
instances are reconstructed here.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

-- Reuse the canonical quotient group already used by finite reciprocity.

variable {K : Type u} [Field K] [NumberField K]

/-- Global reciprocity for the selected class field as a homeomorphic
multiplicative equivalence `Gal(L / K) ≃ₜ* C_K / H`. -/
noncomputable def
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃ₜ*
      IdeleClassGroup K ⧸ H :=
  (globalReciprocityContinuousMulEquiv K
    (closedFiniteIndexClassField
      (K := K) H hclosed)).trans
      (QuotientGroup.quotientContinuousMulEquivOfEq
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed))

end GlobalClassFields
end GlobalClassFieldTheory
