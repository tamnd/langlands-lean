/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityTower.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-!
# Tower compatibility of finite local reciprocity

The canonical finite local Artin maps are compatible with restriction in a
tower of finite abelian extensions. This is stronger than separately choosing
the maps supplied by the finite-level existence theorem; the proof uses the
single compatible construction in the implementation layer.
-/

noncomputable section

open LocalFieldTheory (localNormSubgroup)

universe u v w

namespace ClassFieldTheory

/-- In a finite abelian tower `K ⊆ E ⊆ L`, one can choose the two continuous
Artin maps so that restriction of the upper map equals the lower map. Both
maps retain the expected norm kernels. -/
theorem finiteAbelianLocalReciprocity_tower
    (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artinL : Kˣ →ₜ* (L ≃ₐ[K] L),
      ∃ artinE : Kˣ →ₜ* (E ≃ₐ[K] E),
        Function.Surjective artinL ∧
        Function.Surjective artinE ∧
        artinL.ker = localNormSubgroup K L ∧
        artinE.ker = localNormSubgroup K E ∧
        (AlgEquiv.restrictNormalHom E).comp artinL.toMonoidHom =
          artinE.toMonoidHom := by
  refine ⟨LocalClassFieldTheory.abelianLocalArtinMap K L,
    LocalClassFieldTheory.abelianLocalArtinMap K E,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K L,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K E,
    ?_, ?_, ?_⟩
  · exact LocalClassFieldTheory.abelianLocalArtinMap_ker K L
  · exact LocalClassFieldTheory.abelianLocalArtinMap_ker K E
  · rw [LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L,
      LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K E]
    exact LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower K E L

end ClassFieldTheory
