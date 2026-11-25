/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardNormIndex.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor
public import Langlands.Ported.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
public import Langlands.Ported.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup

/-!
# Norm indices for standard finite Lubin--Tate levels

Finite local reciprocity identifies the cardinality of the norm quotient of a
finite abelian Galois extension with its field degree.  Applied to a standard
Lubin--Tate level over the canonical local-field package, this gives index
`(q - 1) * q ^ n`.
-/



@[expose] public section

noncomputable section

universe u v w

open scoped ValuativeRel

namespace LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The norm subgroup of a standard level over the canonical local-field
package has index equal to the standard Lubin--Tate degree. -/
theorem standardLubinTateNormSubgroup_index
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n : ℕ) :
    (standardLubinTateNormSubgroup hπ n).index =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  let F := standardLocalField K
  let E := standardLubinTateLevelField hπ n
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  change (localNormSubgroup K E).index = _
  calc
    (localNormSubgroup K E).index = Module.finrank K E := by
      rw [Subgroup.index_eq_card]
      exact
        LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGalois
          K E
    _ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
      simpa only [E, F, standardLocalField_residueField_natCard] using
        standardLubinTateLevelField_finrank (F := F) hπ n

/-- The preceding index formula for the canonical chosen uniformizer of
`𝒪[K]`. -/
theorem standardLubinTateCanonicalNormSubgroup_index (n : ℕ) :
    (standardLubinTateNormSubgroup
        (standardLocalFieldUniformizer_isUniformizer K) n).index =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n :=
  standardLubinTateNormSubgroup_index K
    (standardLocalFieldUniformizer_isUniformizer K) n

end LubinTate

end
