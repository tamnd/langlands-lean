/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Langlands.Statements.Torus

/-!
# The challenge for `lake comparator`

This file states each proved top theorem of the package with its pinned statement from `Langlands/Statements/`, and with `sorry` in place of the proof. `lake comparator` checks that each theorem of the same name in `Comparator/Solution.lean` has exactly this type and uses only the permitted axioms. This is row Q4 of spec 14. The file is not in the main tree, so `scripts/scan.sh` does not scan it.
-/

namespace Langlands

universe u

theorem localReciprocityGL1 : LocalReciprocityGL1.{u} := sorry

theorem Bridge.localExistence : LocalExistence.{u} := sorry

theorem localLanglandsTorusSplit (n : ℕ) : LocalLanglandsTorusSplit.{u} n := sorry

end Langlands
