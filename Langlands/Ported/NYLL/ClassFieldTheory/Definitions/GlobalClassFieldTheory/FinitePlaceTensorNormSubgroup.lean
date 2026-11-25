/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FinitePlaceTensorNormSubgroup.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite-place tensor-norm subgroup

The local algebra of `L / K` at a finite place `v` is
`K_v ⊗[K] L`.  Its determinant norm on units defines a subgroup of
`K_vˣ`.  This definition retains the whole tensor algebra, including all
factors above `v`; it does not choose a single completion of `L`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The image of the determinant norm from the unit group of the finite-place
tensor algebra `K_v ⊗[K] L` into `K_vˣ`. -/
def finitePlaceTensorNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (Units.map (Algebra.norm (v.adicCompletion K) :
    (v.adicCompletion K ⊗[K] L) →* v.adicCompletion K)).range

end ClassFieldTheory
