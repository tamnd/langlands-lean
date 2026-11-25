/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Algebra/FiniteAbelianIntermediateFieldAlgEquiv.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.IntermediateFieldAlgEquivOrderIso
public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.AbelianGaloisEquiv

/-!
# Finite abelian intermediate fields under an ambient algebra equivalence

An algebra equivalence of ambient fields transports finite-dimensionality and
the abelian Galois property of every intermediate field.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v w

variable {F : Type u} {L : Type v} {L' : Type w}
  [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
  (e : L ≃ₐ[F] L') (E : IntermediateField F L)

/-- The equivalence of intermediate fields commutes with their base-field
embeddings. -/
theorem intermediateFieldMap_commutes :
    (algebraMap F (E.map e.toAlgHom)).comp (RingEquiv.refl F).toRingHom =
      (IntermediateField.intermediateFieldMap e E).toRingHom.comp
        (algebraMap F E) := by
  apply RingHom.ext
  intro x
  exact ((IntermediateField.intermediateFieldMap e E).commutes x).symm

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its finite-dimensionality. -/
theorem finiteDimensional_intermediateField_map_algEquiv
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  exact Module.Finite.of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its abelian Galois property. -/
theorem isAbelianGalois_intermediateField_map_algEquiv
    [IsAbelianGalois F E] :
    IsAbelianGalois F (E.map e.toAlgHom) := by
  exact isAbelianGalois_of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

end ClassFieldTheory
