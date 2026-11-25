/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalNormResidueCommon.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationNormQuotient
public import Langlands.Ported.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Common data for the finite global norm-residue symbol

The quotient group structure and finite abstract base are chosen once, for
both general Galois reciprocity and its abelian specialization.
-/

@[expose] public section

universe u v

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

open ClassFormation KummerTheory



variable
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- A reducible presentation of the compatible finite abstract field.
Its field projection is definitionally the concrete tower subgroup, so
dependent norm-quotient types do not require opaque unfolding. -/
noncomputable abbrev numberFieldTowerReciprocityFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldTowerBaseSubgroup K L
  finite := numberFieldTowerBaseSubgroup_absoluteQuotient_finite K L

end GlobalClassFieldTheory.Reciprocity
