/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassPrimeToIdeals.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.FractionalIdealFactorization

/-!
# Fractional ideals prime to a ray modulus
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- The subgroup of nonzero fractional ideals prime to the finite part of a
ray modulus. -/
def rayClassPrimeToIdeals
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) :
    Subgroup (NumberFieldFractionalIdealGroup K) :=
  FractionalIdealFactorization.primeTo (F := K) m.finitePart.support

end ClassFieldTheory
