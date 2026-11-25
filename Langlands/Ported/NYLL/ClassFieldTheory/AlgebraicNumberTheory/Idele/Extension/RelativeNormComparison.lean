/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/RelativeNormComparison.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm

/-!
# The same norm in relative and ordinary coordinates

The scalar-extension comparison preserves the determinant norm before any
cohomological properties of the norm quotient are introduced.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The relative determinant norm is the ordinary idele-class norm after
the canonical base-change equivalence. -/
@[simp]
theorem ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
    (c : RelativeIdeleGroup.ClassGroup K L) :
    _root_.ideleClassNorm K L
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) c) =
      RelativeIdeleGroup.classNorm K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rw [← QuotientGroup.mk'_apply, relativeIdeleClassBaseChangeMulEquiv_mk, _root_.ideleClassNorm_mk,
    RelativeIdeleGroup.classNorm_mk, IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]
