/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/FreeCoordinate.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient

/-!
# Local coordinates of the profinite-unit decomposition
-/



@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- The `p`-adic coordinate of the global free factor in
`zHatUnitsDecomposition` is exactly the free factor in the genuine
local decomposition of the `p`-adic unit coordinate. -/
@[simp]
theorem zHatUnitsDecomposition_freeCoordinate
    (u : ZHatˣ) (p : Nat.Primes) :
    zHatToPadicInt p
        (Multiplicative.toAdd
          (zHatUnitsDecomposition u).1) =
      Multiplicative.toAdd
        (((padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p)).2) := by
  let y : ProfiniteIntegerPrimeProduct :=
    fun q =>
      Multiplicative.toAdd
        (((padicUnitDecomposition q.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u q)).2)
  change
    zHatToPadicInt p
        (zHatContinuousAddEquivPrimeProduct.symm y) =
      y p
  exact
    congrFun
      (zHatContinuousAddEquivPrimeProduct.apply_symm_apply y) p

end KummerTheory
