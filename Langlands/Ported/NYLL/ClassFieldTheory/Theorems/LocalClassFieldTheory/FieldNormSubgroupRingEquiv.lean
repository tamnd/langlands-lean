/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FieldNormSubgroupRingEquiv.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnits
public import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NormUnitsBaseChange
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Norm membership under compatible field equivalences

Transporting both fields of a finite extension through compatible ring
equivalences preserves the actual field norms, not merely their index.
-/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

namespace ClassFieldTheory

universe u v w x

/-- An element is a field norm exactly when its image under a compatible
base-field equivalence is a field norm in the transported extension. -/
theorem mem_fieldNormSubgroup_iff_ringEquiv
    {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
    [Field F] [Field M] [Field F'] [Field M']
    [Algebra F M] [Algebra F' M']
    [FiniteDimensional F M] [FiniteDimensional F' M']
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (a : Fˣ) :
    a ∈ localNormSubgroup F M ↔
      (Units.mapEquiv eF.toMulEquiv) a ∈ localNormSubgroup F' M' := by
  rw [← LocalFieldTheory.localNormSubgroup_map_ringEquiv eF eM he]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end ClassFieldTheory
