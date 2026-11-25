/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Hilbert90.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Langlands.Ported.NYLL.GaloisCohomology.Cyclic.GaloisCohomology

/-!
# Hilbert 90 and negative Tate cohomology of field units

For a finite field extension with a chosen generator of its automorphism group,
the cyclic comparison between first group cohomology and negative Tate cohomology
transports Hilbert 90 to the statement that the latter group has cardinality one.
-/

@[expose] public section

namespace LocalClassFieldTheory

open CyclicCohomology

noncomputable section

/-- The `i = -1` half of the local class-field-axiom theorem on the actual field-unit
representation.  This is Hilbert 90 transported through the cyclic
`H¹ ≃ H⁻¹` comparison. -/
theorem unitsTateHminusOne_card_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  calc
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) =
        Nat.card (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) :=
      Nat.card_congr
        (unitsH1IsoTateHminusOne K L g hg).symm.toLinearEquiv.toEquiv
    _ = 1 := Nat.card_unique

end
end LocalClassFieldTheory
