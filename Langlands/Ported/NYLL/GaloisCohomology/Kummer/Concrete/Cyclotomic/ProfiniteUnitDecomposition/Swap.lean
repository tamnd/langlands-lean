/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Swap.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather

/-!
# Compiled final swap stage of the profinite-unit decomposition
-/



@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (
  continuousMulEquivProdComm
) in
/-- Swap the collected free and finite coordinates. -/
noncomputable def freeFiniteSwap :
    CyclotomicFinitePart × Multiplicative ZHat ≃ₜ*
      Multiplicative ZHat × CyclotomicFinitePart :=
  continuousMulEquivProdComm
    CyclotomicFinitePart (Multiplicative ZHat)

end KummerTheory.ProfiniteUnitDecomposition.Internal
