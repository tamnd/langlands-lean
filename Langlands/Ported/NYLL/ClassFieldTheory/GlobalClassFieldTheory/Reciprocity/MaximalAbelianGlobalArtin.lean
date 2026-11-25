/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Global Artin map for the maximal abelian extension

This module specializes the continuous infinite global Artin map to the
maximal abelian subextension of the separable closure.  It also exposes the
idele-representative evaluation and its finite Galois projections.
-/



@[expose] public section

open scoped NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type u) [Field K] [NumberField K]

/-- The continuous global Artin homomorphism from the idele class group to
the Galois group of the maximal abelian extension. -/
noncomputable def maximalAbelianGlobalArtin :
    IdeleClassGroup K →ₜ* Gal(maximalAbelianExtension K / K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom
    (K := K) (Ω := maximalAbelianExtension K)

/-- Evaluation of the maximal abelian global Artin map on an idele
representative recovers the infinite global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_mk (a : IdeleGroup K) :
    maximalAbelianGlobalArtin K
        (IdeleGroup.toStandardClass K a) =
      infiniteGlobalArtinMonoidHom K (maximalAbelianExtension K) a :=
  infiniteGlobalIdeleClassArtinMonoidHom_mk
    (K := K) (Ω := maximalAbelianExtension K) a

/-- Projection of the maximal abelian global Artin map at an idele
representative to a finite Galois intermediate field agrees with the finite
global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_finiteProjection
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    let : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (maximalAbelianGlobalArtin K
          (IdeleGroup.toStandardClass K a)) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  intro sharedOwner1
  rw [maximalAbelianGlobalArtin_mk]
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (maximalAbelianExtension K) a E

/-- The maximal abelian global Artin homomorphism is surjective. -/
theorem maximalAbelianGlobalArtin_surjective :
    Function.Surjective (maximalAbelianGlobalArtin K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    K (maximalAbelianExtension K)

end Reciprocity
end GlobalClassFieldTheory
