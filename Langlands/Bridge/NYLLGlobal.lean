/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.All
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.KroneckerWeber
import Langlands.Statements.ClassField
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The bridge to the NYLL port of global class field theory

The port in `Langlands/Ported/NYLL` proves the main theorems of global class field theory for number fields: finite abelian global reciprocity, the existence theorem, the Artin map to the abelianized absolute Galois group, and the theorem of Kronecker and Weber. This file restates these theorems in the terms of `Langlands/Statements/ClassField.lean`.

* `Langlands.Bridge.kroneckerWeber`: the statement `Langlands.KroneckerWeber`, from the theorem `ClassFieldTheory.kroneckerWeber` of NYLL.

## Implementation notes

The theorem of NYLL gives an embedding of a finite abelian extension $L$ of $\mathbb{Q}$ into the cyclotomic field $\mathbb{Q}(\zeta_n)$ as an abstract field. The statement of the project is about a subfield $L$ of the fixed algebraic closure $\overline{\mathbb{Q}}$. An embedding $\psi$ of $\mathbb{Q}(\zeta_n)$ into $\overline{\mathbb{Q}}$ gives an embedding of $L$ into $\overline{\mathbb{Q}}$. Its image is $L$, because $L$ is normal over $\mathbb{Q}$. So $L$ is in the image of $\psi$, which is $\mathbb{Q}(\psi(\zeta_n))$.
-/

namespace Langlands.Bridge

/-- **The theorem of Kronecker and Weber** (NYLL). Each finite abelian extension of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ is in $\mathbb{Q}(\zeta)$ for a primitive root of unity $\zeta$. -/
theorem kroneckerWeber : KroneckerWeber := by
  intro L hfin hab
  have : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨n, hn, ⟨φ⟩⟩ := ClassFieldTheory.kroneckerWeber L
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ℚ) := ⟨by exact_mod_cast hn.ne'⟩
  have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let ψ : CyclotomicField n ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ζ := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  refine ⟨n, ψ ζ, hn, hζ.map_of_injective ψ.injective, ?_⟩
  have : Normal ℚ L := hab.toIsGalois.to_normal
  rw [← AlgHom.fieldRange_of_normal (ψ.comp φ)]
  rintro _ ⟨x, rfl⟩
  have hx : φ x ∈ Algebra.adjoin ℚ {ζ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    trivial
  have : ψ (φ x) ∈ Algebra.adjoin ℚ (ψ '' {ζ}) := by
    rw [← AlgHom.map_adjoin]
    exact ⟨φ x, hx, rfl⟩
  rw [Set.image_singleton] at this
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ _ this

end Langlands.Bridge
