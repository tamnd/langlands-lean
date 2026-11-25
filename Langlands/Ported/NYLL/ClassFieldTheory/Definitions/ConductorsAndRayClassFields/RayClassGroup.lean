/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassGroup.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassPrimeToIdeals
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Ideal-theoretic ray class groups
-/



@[expose] public section

namespace ClassFieldTheory

universe u

/-- The ideal-theoretic ray class group of a modulus. -/
abbrev RayClassGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) :=
  rayClassPrimeToIdeals m ⧸ rayPrincipalIdealSubgroupInPrimeTo m

/-- The ideal ray class group inherits multiplication from its commutative quotient. -/
instance rayClassGroup_commGroup
    {K : Type u} [Field K] [NumberField K] (m : RayClassModulus K) :
    CommGroup (RayClassGroup m) :=
  QuotientGroup.Quotient.commGroup (rayPrincipalIdealSubgroupInPrimeTo m)

end ClassFieldTheory
