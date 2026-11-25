/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocity
import Langlands.Statements.ClassField

/-!
# The bridge to the NYLL port of local class field theory

The port in `Langlands/Ported/NYLL` proves finite abelian local reciprocity: for a finite abelian extension $L/K$ of a nonarchimedean local field there is a continuous surjective homomorphism $K^\times \to \mathrm{Gal}(L/K)$ whose kernel is the norm group $N_{L/K}(L^\times)$. This file restates the theorem in the terms of `Langlands/Statements/ClassField.lean`.

* `Langlands.Bridge.isFieldNorm_iff_mem_normGroup`: the predicate `ClassFieldTheory.IsFieldNorm` of NYLL is membership in `Langlands.normGroup`. The two definitions are the same term.
* `Langlands.Bridge.finiteAbelianLocalReciprocity`: the theorem of NYLL for a finite abelian extension inside a fixed algebraic closure, with the kernel given by `Langlands.normGroup`.

This is step 1 of the plan of 05.5 of the spec for `LocalReciprocityGL1`. The next steps take the limit over the finite abelian extensions, prove the uniqueness and the normalization at a uniformizer, and pass from the Galois group to the Weil group.
-/

namespace Langlands.Bridge

universe u v

/-- The norm predicate of NYLL is membership in the norm group of the project. -/
theorem isFieldNorm_iff_mem_normGroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    ClassFieldTheory.IsFieldNorm K L x ↔ x ∈ normGroup K L :=
  Iff.rfl

/-- **Finite abelian local reciprocity** (NYLL). For a finite abelian extension $L$ of a nonarchimedean local field $K$ inside an algebraic closure, there is a continuous surjective homomorphism $K^\times \to \mathrm{Gal}(L/K)$ with kernel $N_{L/K}(L^\times)$. -/
theorem finiteAbelianLocalReciprocity (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L), Function.Surjective artin ∧ ∀ x : Kˣ, artin x = 1 ↔ x ∈ normGroup K L :=
  ClassFieldTheory.finiteAbelianLocalReciprocity K L

end Langlands.Bridge
