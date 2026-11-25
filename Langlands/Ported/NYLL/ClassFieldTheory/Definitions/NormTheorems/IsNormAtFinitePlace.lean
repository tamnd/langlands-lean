/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/IsNormAtFinitePlace.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Norms at finite places
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A unit of `K` is a norm at a finite place `w` if its image in `K_w` is a
determinant norm from `K_w ⊗_K L`. -/
def IsNormAtFinitePlace
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Prop :=
  ∃ y : (w.adicCompletion K ⊗[K] L)ˣ,
    Algebra.norm (w.adicCompletion K)
        (y : w.adicCompletion K ⊗[K] L) =
      algebraMap K (w.adicCompletion K) (x : K)

end ClassFieldTheory
