/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/TorsionQuotientMk.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv

/-!
# Evaluation of the torsion-quotient equivalence
-/



@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- The torsion-quotient equivalence evaluates a quotient class by
taking the genuine torsion-free coordinate of the chosen product
decomposition.  This is the commuting square needed to pass between an
actual cyclotomic character and the `ZHat`-coordinate of its torsion
fixed field. -/
@[simp]
theorem torsionQuotientEquivOfZHatMulDecomposition_mk
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T))
    (g : G) :
    torsionQuotientEquivOfZHatMulDecomposition
        G T E hT (QuotientGroup.mk g) =
      (E g).1 := by
  rfl

end KummerTheory
