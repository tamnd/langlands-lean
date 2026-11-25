/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/NormalFieldRange.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Ranges of embeddings of normal extensions

This file gives the intermediate-field image of an explicit embedding of a
finite Galois extension into a separable closure, with the inherited finite
Galois instances.
-/



@[expose] public section

namespace LocalClassFieldTheory

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The embedded copy of `L` determined by an explicit embedding into the
fixed separable closure.  Keeping the embedding visible is what makes the
canonicity argument in the finite local reciprocity theorem meaningful. -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range. -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

end

end LocalClassFieldTheory
