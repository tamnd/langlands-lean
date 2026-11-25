/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/QuotientTransport.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree

/-!
# Continuous transport between equal quotient groups

Equality of normal subgroups identifies their quotient groups with the same
native quotient topology.  Eliminating the equality therefore gives the
continuous multiplicative equivalence directly; no discrete-topology
instances or domain-specific class-field tower are required.
-/



@[expose] public section

noncomputable section

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Equal normal subgroups induce a continuous multiplicative equivalence
between their quotient groups with their native quotient topologies. -/
noncomputable def quotientContinuousMulEquivOfEq
    {N H : Subgroup G} [N.Normal] [H.Normal]
    (h : N = H) :
    G ⧸ N ≃ₜ* G ⧸ H := by
  subst H
  exact ContinuousMulEquiv.refl _

/-- Forgetting topology from `quotientContinuousMulEquivOfEq` recovers the
canonical multiplicative equivalence induced by the same equality. -/
@[simp]
theorem quotientContinuousMulEquivOfEq_apply
    {N H : Subgroup G} [N.Normal] [H.Normal]
    (h : N = H) (x : G ⧸ N) :
    quotientContinuousMulEquivOfEq h x =
      QuotientGroup.quotientMulEquivOfEq h x := by
  subst H
  refine QuotientGroup.induction_on x ?_
  intro g
  exact
    (QuotientGroup.quotientMulEquivOfEq_mk
      (G := G) (M := N) (N := N) rfl g).symm

end QuotientGroup
