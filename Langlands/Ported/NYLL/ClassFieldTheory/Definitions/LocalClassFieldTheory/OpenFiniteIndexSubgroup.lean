/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/OpenFiniteIndexSubgroup.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Langlands.Ported.NYLL.ProCGroups.Topologies.OpenFiniteIndexSubgroup
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Open finite-index subgroups of a field's multiplicative group
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- An open finite-index subgroup of the multiplicative group `Kˣ`.  The
inherited order is ordinary subgroup inclusion. The underlying subgroup is
`H.1.toSubgroup`, openness is `H.1.isOpen`, and finite index is `H.2`. -/
abbrev OpenFiniteIndexSubgroup
    (K : Type u) [Field K] [TopologicalSpace K] :=
  OpenFiniteIndexGroupSubgroup Kˣ

end ClassFieldTheory
