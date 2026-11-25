/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FieldNormSubgroupFiniteIndex.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin

/-!
# Finite index of the local norm subgroup

Finite local reciprocity implies that the subgroup of nonzero field norms
has finite index in the multiplicative group of the base field.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

namespace ClassFieldTheory

universe u v

/-- The norm subgroup of a finite abelian local extension has finite index. -/
theorem fieldNormSubgroup_finiteIndex
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (localNormSubgroup K L).FiniteIndex := by
  let e := Classical.choose
    (LocalClassFieldTheory.Universe.quotientEquiv_existsUnique K L).exists
  let : Finite Gal(L/K) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (FieldNormQuotient K L) :=
    Finite.of_equiv Gal(L/K) e.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end ClassFieldTheory
