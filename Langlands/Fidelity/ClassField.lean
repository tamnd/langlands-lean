/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField

/-!
# Fidelity checks for the statements of class field theory

This file has the checks F2 (positive instances) of spec 06.3 for the statements of `Langlands.Statements.ClassField` that are available now. A positive instance is a proof of a known special case of a statement. A proof of a special case shows that the hypotheses of the statement are not contradictory in that case, and that the conclusion has the expected meaning there.

* `Langlands.Fidelity.normGroup_bot`: the norm group of the trivial extension is the full group of units.
* `Langlands.Fidelity.localExistence_top`: the conclusion of `LocalExistence` holds for the open subgroup $U = K^\times$.
* `Langlands.Fidelity.kroneckerWeber_bot`: the conclusion of `KroneckerWeber` holds for the trivial extension of $\mathbb{Q}$.

The positive instance `KroneckerWeber` from `GlobalReciprocity` of spec 06.3 needs the conductor of a character and the ray class fields of $\mathbb{Q}$. It is a target of milestone S2.
-/

namespace Langlands.Fidelity

open IntermediateField

variable (K : Type*) [Field K]

instance isAbelianGalois_bot (E : Type*) [Field E] [Algebra K E] :
    IsAbelianGalois K (⊥ : IntermediateField K E) where
  is_comm := ⟨fun σ τ => by
    have key : ∀ ρ : Gal((⊥ : IntermediateField K E)/K), ρ = 1 := fun ρ => AlgEquiv.ext fun x => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp x.2
      have hx : x = algebraMap K _ a := Subtype.ext ha.symm
      rw [hx, AlgEquiv.commutes, AlgEquiv.one_apply]
    rw [key σ, key τ]⟩

/-- The norm group of the trivial extension of $K$ is $K^\times$. -/
theorem normGroup_bot (E : Type*) [Field E] [Algebra K E] :
    normGroup K (⊥ : IntermediateField K E) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ⟨Units.map (algebraMap K (⊥ : IntermediateField K E)).toMonoidHom x, ?_⟩
  ext
  simp [Algebra.norm_algebraMap, IntermediateField.finrank_bot]

/-- The conclusion of `LocalExistence` for the subgroup $U = K^\times$: the trivial extension has norm group $K^\times$. -/
theorem localExistence_top (E : Type*) [Field E] [Algebra K E] :
    ∃ L : IntermediateField K E, FiniteDimensional K L ∧ IsAbelianGalois K L ∧ normGroup K L = ⊤ :=
  ⟨⊥, inferInstance, inferInstance, normGroup_bot K E⟩

/-- The conclusion of `KroneckerWeber` for the trivial extension of $\mathbb{Q}$: it is contained in $\mathbb{Q}(\zeta_1) = \mathbb{Q}$. -/
theorem kroneckerWeber_bot :
    ∃ (n : ℕ) (ζ : AlgebraicClosure ℚ), 0 < n ∧ IsPrimitiveRoot ζ n ∧
      (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤ IntermediateField.adjoin ℚ {ζ} :=
  ⟨1, 1, one_pos, IsPrimitiveRoot.one, bot_le⟩

end Langlands.Fidelity
