/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Naturality.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import Langlands.Ported.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Naturality of the actual Artin filtration

A base-linear field equivalence transports the Artin image of each principal
unit group, including its real-indexed step filtration.
-/

@[expose] public section

namespace LocalClassFieldTheory

open LocalFieldTheory

universe u v w

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping the Artin principal-unit step group along a base-linear
equivalence gives the corresponding group on the equivalent extension. -/
theorem artinPrincipalUnitStepGroup_map_autCongr
    (L : Type v) (M : Type w) [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    (e : L ≃ₐ[K] M) (t : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
        (artinPrincipalUnitStepGroup K L t) =
      artinPrincipalUnitStepGroup K M t := by
  unfold artinPrincipalUnitStepGroup RamificationTheory.natCeilStepFiltration
    artinPrincipalUnitGroup
  rw [Subgroup.map_map]
  simp only [abelianLocalArtinMonoidHom_autCongr K L M e]

end LocalClassFieldTheory
