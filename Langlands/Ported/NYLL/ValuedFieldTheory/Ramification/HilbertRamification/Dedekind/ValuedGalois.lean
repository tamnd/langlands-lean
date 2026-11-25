/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/ValuedGalois.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Langlands.Ported.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic

/-!
# Inertia cardinality for finite valued extensions

The ideal-theoretic inertia group has cardinality equal to the canonical
ramification index of a finite separable extension of complete discrete
valuation fields.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
variable (G : Type*) [Group G] [Finite G]
variable [MulSemiringAction G target.valuationSubring]
variable [IsGaloisGroup G base.valuationSubring target.valuationSubring]

/-- In a finite separable valued extension, ideal-theoretic inertia has
cardinality equal to the canonical ramification index. -/
theorem card_inertia_eq_ramificationIndex_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [Algebra.IsSeparable
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal)] :
    Nat.card (target.maximalIdeal.toAddSubgroup.inertia G) =
      ramificationIndex base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    maximalIdeal_liesOver base target
  rw [HilbertRamification.Dedekind.dedekindRamification_inertia_card_eq_ramificationIdxIn
    (A := base.valuationSubring) (B := target.valuationSubring)
    base.maximalIdeal target.maximalIdeal G base.maximalIdeal_ne_bot]
  simpa [ramificationIndex] using
    (Ideal.ramificationIdxIn_eq_ramificationIdx
      base.maximalIdeal target.maximalIdeal G).trans
      (Ideal.ramificationIdx'_eq_ramificationIdx
        base.maximalIdeal target.maximalIdeal base.maximalIdeal_ne_bot).symm

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
