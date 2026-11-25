/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/TopologicalGlobalReciprocity.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Topological global reciprocity

For a number field `K`, the idèle class group modulo its identity component
is topologically isomorphic to the maximal abelian quotient of the absolute
Galois group. The statement uses Mathlib's groups on both sides.
-/

@[expose] public section

open scoped NumberField

namespace ClassFieldTheory

universe u

open _root_.GlobalClassFieldTheory.Reciprocity in
/-- The topological form of global class field theory. -/
theorem topologicalGlobalReciprocity
    (K : Type u) [Field K] [NumberField K] :
    Nonempty (IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K) :=
  ⟨mathlibIdeleClassConnectedQuotientEquivAbelianization K⟩

end ClassFieldTheory
