/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/AdeleBaseChange.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Adele.BaseChange
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# The diagonal under relative-to-ordinary scalar extension

The ring equivalence and its induced unit map share one construction.
-/

@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The relative-to-ordinary comparison sends the extension-field
diagonal to the ordinary diagonal idele. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_principalIdele
    (x : Lˣ) :
    relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L x) =
      IdeleGroup.principalIdele L x := by
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  change relativeAdeleBaseChangeRingEquiv (K := K) (L := L)
      (RelativeIdeleGroup.fieldInclusion K L (x : L)) =
    algebraMap L (NumberField.AdeleRing (𝓞 L) L) (x : L)
  exact relativeAdeleBaseChangeRingEquiv_fieldInclusion (K := K) (L := L) (x : L)
