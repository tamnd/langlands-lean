/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Gather.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree

/-!
# Compiled free-coordinate gathering stage of the profinite-unit decomposition
-/



@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation
open LocalFieldTheory.Padic

/-- Reassemble the family of local additive coordinates into `ℤ̂`. -/
noncomputable def gatherFree :
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ≃ₜ*
      Multiplicative ZHat :=
  (continuousPiMultiplicative
      (fun p : Nat.Primes => ℤ_[p.1])).symm.trans
    (continuousMultiplicativeEquivOfAddEquiv
      zHatContinuousAddEquivPrimeProduct).symm

end KummerTheory.ProfiniteUnitDecomposition.Internal
