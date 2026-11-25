/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/StandardGaloisNorm.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisClassNorm

/-!
# The Galois product formula on standard idele classes

Extending the actual field norm gives the product of the classes transported
by all field automorphisms. Both sides use the same standard principal quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace NumberField.IdeleClassGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Inclusion of the standard norm is the product of the actual Galois conjugates. -/
theorem fieldInclusion_norm_eq_prod_congr (c : IdeleClassGroup (𝓞 L) L) :
    fieldInclusion K L (norm K L c) =
      ∏ σ : L ≃ₐ[K] L, congr (σ.restrictScalars ℚ) c := by
  obtain ⟨d, rfl⟩ := (relativeClassComparison K L).surjective c
  rw [norm_relativeClassComparison, fieldInclusion_relativeClassComparison,
    RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_conjugates, map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  exact relativeClassComparison_conjugation K L σ d

end NumberField.IdeleClassGroup
