/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalExistence
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocity
import Langlands.Statements.ClassField

/-!
# The bridge to the NYLL port of local class field theory

The port in `Langlands/Ported/NYLL` proves finite abelian local reciprocity: for a finite abelian extension $L/K$ of a nonarchimedean local field there is a continuous surjective homomorphism $K^\times \to \mathrm{Gal}(L/K)$ whose kernel is the norm group $N_{L/K}(L^\times)$. This file restates the theorem in the terms of `Langlands/Statements/ClassField.lean`.

* `Langlands.Bridge.isFieldNorm_iff_mem_normGroup`: the predicate `ClassFieldTheory.IsFieldNorm` of NYLL is membership in `Langlands.normGroup`. The two definitions are the same term.
* `Langlands.Bridge.finiteAbelianLocalReciprocity`: the theorem of NYLL for a finite abelian extension inside a fixed algebraic closure, with the kernel given by `Langlands.normGroup`.
* `Langlands.Bridge.exists_intermediateField_of_finiteAbelianExtension`: a finite abelian extension inside the separable closure of NYLL gives an intermediate field of the algebraic closure with the same norm group.
* `Langlands.Bridge.localExistence`: the statement `Langlands.LocalExistence`, from the existence theorem `ClassFieldTheory.finiteAbelianLocalExistence` of NYLL.

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

/-- A finite abelian extension inside the separable closure of NYLL moves to an intermediate field of the algebraic closure of the project, with the same norm group. The map is the inclusion of the separable closure into the algebraic closure. -/
theorem exists_intermediateField_of_finiteAbelianExtension (K : Type u) [Field K]
    (E : ClassFieldTheory.FiniteAbelianExtension K) :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ IsAbelianGalois K L ∧
        normGroup K L = LocalFieldTheory.localNormSubgroup K E.1 := by
  let ι : SeparableClosure K →ₐ[K] AlgebraicClosure K := (separableClosure K (AlgebraicClosure K)).val
  let e : E.1 ≃ₐ[K] E.1.map ι := E.1.equivMap ι
  have : FiniteDimensional K E.1 := E.2.1
  have : IsAbelianGalois K E.1 := E.2.2
  refine ⟨E.1.map ι, LinearEquiv.finiteDimensional e.toLinearEquiv,
    IsAbelianGalois.of_algHom (e.symm : E.1.map ι →ₐ[K] E.1), ?_⟩
  ext x
  simp only [normGroup, LocalFieldTheory.localNormSubgroup, LocalFieldTheory.normUnits,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (e.symm : E.1.map ι →* E.1) y, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    exact Algebra.norm_eq_of_algEquiv e.symm (y : E.1.map ι)
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (e : E.1 →* E.1.map ι) y, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    exact Algebra.norm_eq_of_algEquiv e (y : E.1)

/-- **Local existence** (NYLL). For a nonarchimedean local field $K$, each open subgroup of finite index of $K^\times$ is the norm group of a finite abelian extension of $K$ inside an algebraic closure. -/
theorem localExistence : LocalExistence.{u} := by
  intro K _ _ _ _ U hU hfin
  obtain ⟨E, hE⟩ := ClassFieldTheory.finiteAbelianLocalExistence K ⟨⟨U, hU⟩, hfin⟩
  obtain ⟨L, hL, hab, hN⟩ := exists_intermediateField_of_finiteAbelianExtension K E
  exact ⟨L, hL, hab, hN.trans hE⟩

end Langlands.Bridge
