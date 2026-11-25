/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/FinitePrimeFractionalIdeal.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.FractionalIdealFactorization

/-!
# Fractional ideal represented by a finite prime
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The nonzero fractional ideal represented by a finite prime. -/
def finitePrimeFractionalIdeal
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberFieldFractionalIdealGroup K :=
  ClassFieldTheory.FractionalIdealFactorization.prime (F := K) v

end ClassFieldTheory
