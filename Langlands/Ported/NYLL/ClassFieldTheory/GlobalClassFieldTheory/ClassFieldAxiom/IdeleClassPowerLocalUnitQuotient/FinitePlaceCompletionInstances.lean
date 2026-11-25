/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/FinitePlaceCompletionInstances.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Langlands.Ported.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Langlands.Ported.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete

/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type u} [Field K] [NumberField K]

/-- The distinguished valuation on a finite completion of a number field is
complete discrete. -/
noncomputable instance finitePlaceAdicCompletion_isCompleteDiscrete
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ))) where
  isRankOneDiscrete := inferInstance
  isAdicComplete :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance finitePlaceAdicCompletion_charZero
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    CharZero (v₀.adicCompletion K) :=
  charZero_of_injective_algebraMap
    (algebraMap K (v₀.adicCompletion K)).injective

/-- The residue field of a finite completion of a number field is finite. -/
noncomputable instance finitePlaceAdicCompletion_residueFinite
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Finite
      (IsLocalRing.ResidueField
        (Valued.v :
          Valuation (v₀.adicCompletion K)
            (WithZero (Multiplicative ℤ))).valuationSubring) := by
  change Finite (Valued.ResidueField (v₀.adicCompletion K))
  exact _root_.finite_adicCompletion_residueField K v₀

end GlobalClassFieldTheory.ClassFieldAxiom

end
