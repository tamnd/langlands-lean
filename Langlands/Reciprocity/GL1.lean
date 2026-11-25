/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Reciprocity.Exists
import Langlands.Reciprocity.Unique

/-!
# Local class field theory as the local Langlands correspondence for GL(1)

This file proves `Langlands.LocalReciprocityGL1`. For each nonarchimedean local field $K$ there is exactly one topological isomorphism $\mathrm{rec}_K : K^\times \cong W_K^{ab}$ that sends each uniformizer to the class of a geometric Frobenius and that is compatible with the norm groups of the finite abelian extensions of $K$.

* `Langlands.exists_isLocalArtinMap` gives the existence.
* `Langlands.isLocalArtinMap_unique` gives the uniqueness.
-/

namespace Langlands

universe u

/-- **Local class field theory** (Hasse, Chevalley, Lubin-Tate). The local reciprocity map $K^\times \cong W_K^{ab}$ exists and is unique. -/
theorem localReciprocityGL1 : LocalReciprocityGL1.{u} := by
  intro K _ _ _ _
  obtain ⟨rec, hrec⟩ := exists_isLocalArtinMap K
  exact ⟨rec, hrec, fun rec' h' => isLocalArtinMap_unique K rec' rec h' hrec⟩

end Langlands
