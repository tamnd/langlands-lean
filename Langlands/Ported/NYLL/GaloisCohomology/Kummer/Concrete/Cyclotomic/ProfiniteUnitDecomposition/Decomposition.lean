/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Decomposition.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather

/-!
# The profinite-unit product decomposition
-/



@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- Topological decomposition
`ℤ̂ˣ ≃ Multiplicative ℤ̂ × finite-product` used in the rational cyclotomic
calculation. -/
noncomputable def zHatUnitsDecomposition :
    ZHatˣ ≃ₜ* Multiplicative ZHat × CyclotomicFinitePart :=
  zHatUnitsContinuousMulEquivPrimeProduct.trans <|
    ProfiniteUnitDecomposition.Internal.localDecomposition.symm.trans <|
      ProfiniteUnitDecomposition.Internal.finiteFreeSplit.trans <|
        continuousMulEquivProdCongr
          ProfiniteUnitDecomposition.Internal.gatherFree
          (ContinuousMulEquiv.refl CyclotomicFinitePart)

end KummerTheory
