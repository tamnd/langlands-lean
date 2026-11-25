/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivTopology.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Adele.Equiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap

/-!
# Local continuity for transport under a number-field equivalence

The finite-completion map used by `adeleCongr` is continuous. This is the
local continuity input for transporting the restricted-product topology.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- Field-isomorphism transport is continuous on each finite completion. -/
theorem finitePlaceAdicCompletionCongrHom_continuous
    (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    Continuous (finitePlaceAdicCompletionCongrHom e W) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  unfold finitePlaceAdicCompletionCongrHom
  exact finitePlaceAdicCompletionMap_continuous K M _ _
