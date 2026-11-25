/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassSubgroupRealization.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

/-!
# Class fields attached to ray class subgroups
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A finite abelian class field realizing a subgroup of a ray class group.

The Artin map has exactly the prescribed kernel and is normalized on prime
classes by arithmetic Frobenius. -/
structure RayClassSubgroupRealization
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) where
  /-- The corresponding finite abelian extension. -/
  extension : FiniteAbelianExtension K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus :
    IsUnramifiedOutsideModulus K extension m
  /-- The Artin map attached to the extension. -/
  artin : RayClassGroup m →* (extension ≃ₐ[K] extension)
  /-- The Artin map is onto. -/
  artin_surjective : Function.Surjective artin
  /-- The prescribed subgroup is exactly the Artin kernel. -/
  artin_ker : artin.ker = H
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support)
      (w : HeightOneSpectrum (𝓞 extension)),
      w.asIdeal.LiesOver v.asIdeal →
        artin (rayClassOfFinitePrime m v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
