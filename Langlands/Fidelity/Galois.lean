/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Galois
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

/-!
# Fidelity checks for the statements of Galois representations and Artin L-functions

This file has the fidelity checks of spec 06.3 for the statements of `Langlands.Statements.Galois`.

* `Langlands.Fidelity.isUnramifiedAt_one`: the trivial representation is unramified at each prime.
* `Langlands.Fidelity.exists_isComplexConjugation`: a complex conjugation exists in $G_\mathbb{Q}$.
* `Langlands.Fidelity.exists_isFrobeniusAt`: an arithmetic Frobenius exists in $G_\mathbb{Q}$ at each prime.
* `Langlands.Fidelity.artinLFunction_one`: the Artin L-function of the trivial character is the Euler product of the Dedekind zeta function.
-/

namespace Langlands.Fidelity

open Langlands NumberField IsDedekindDomain ComplexConjugate

/-- The trivial representation is unramified at each prime. So the condition `IsUnramifiedAt` is not contradictory. -/
theorem isUnramifiedAt_one {H : Type*} [Group H] (p : ℕ) :
    IsUnramifiedAt (1 : Field.absoluteGaloisGroup ℚ →* H) p :=
  fun _ _ _ _ _ => rfl

/-- F2 for `IsOddRep`: a complex conjugation exists in $G_\mathbb{Q}$. It is the restriction of complex conjugation to the image of an embedding $\overline{\mathbb{Q}} \to \mathbb{C}$, which is a normal extension of $\mathbb{Q}$. So the condition to be odd is not empty. -/
theorem exists_isComplexConjugation :
    ∃ c : Field.absoluteGaloisGroup ℚ, IsComplexConjugation c := by
  let j : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure ℚ) ℂ := j.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let c : Field.absoluteGaloisGroup ℚ :=
    (Complex.conjAe.restrictScalars ℚ).restrictNormal (AlgebraicClosure ℚ)
  refine ⟨c, j.toRingHom, fun x => ?_⟩
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes (AlgebraicClosure ℚ) x


section Frobenius

attribute [local instance] Ideal.Quotient.field

/-- The absolute Galois group of $\mathbb{Q}$ is compact. -/
instance : CompactSpace (Field.absoluteGaloisGroup ℚ) :=
  inferInstanceAs (CompactSpace Gal(AlgebraicClosure ℚ/ℚ))

/-- The absolute Galois group of $\mathbb{Q}$ is totally disconnected. -/
instance : TotallyDisconnectedSpace (Field.absoluteGaloisGroup ℚ) :=
  inferInstanceAs (TotallyDisconnectedSpace Gal(AlgebraicClosure ℚ/ℚ))

/-- The elements of $\bar{\mathbb{Z}}$ that are fixed by $G_\mathbb{Q}$ are the integers. -/
theorem isInvariant_algebraicIntegers :
    Algebra.IsInvariant ℤ AlgebraicIntegers (Field.absoluteGaloisGroup ℚ) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ g : Gal(AlgebraicClosure ℚ/ℚ), g (b : AlgebraicClosure ℚ) = b := fun g =>
    congrArg Subtype.val (hb g)
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : AlgebraicClosure ℚ)).2 hfix
  have hint : IsIntegral ℤ q := by
    have : IsIntegral ℤ (b : AlgebraicClosure ℚ) := b.2
    rw [← hq] at this
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (AlgebraicClosure ℚ))
      (algebraMap ℚ _).injective).1 this
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨n, RingOfIntegers.ext (by simpa using hq)⟩

/-- F2 for `IsFrobeniusAt`: at each prime $p$ there is an arithmetic Frobenius in $G_\mathbb{Q}$. The proof lifts the Frobenius $x \mapsto x^p$ of the residue field of a maximal ideal of $\bar{\mathbb{Z}}$ over $p$ with the profinite form of the surjectivity of the decomposition group onto the automorphisms of the residue field. So the conditions at Frobenius in `EichlerShimuraDeligne` and `SerreModularityWeak` are not empty. -/
theorem exists_isFrobeniusAt (p : ℕ) (hp : p.Prime) :
    ∃ σ : Field.absoluteGaloisGroup ℚ, IsFrobeniusAt p σ := by
  let _ : TopologicalSpace AlgebraicIntegers := ⊥
  have : DiscreteTopology AlgebraicIntegers := ⟨rfl⟩
  have : ContinuousSMul (Field.absoluteGaloisGroup ℚ) AlgebraicIntegers := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have e : (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) x : Set (Field.absoluteGaloisGroup ℚ)) =
        (MulAction.stabilizer Gal(AlgebraicClosure ℚ/ℚ) (x : AlgebraicClosure ℚ) :
          Set Gal(AlgebraicClosure ℚ/ℚ)) := by
      ext g
      exact RingOfIntegers.ext_iff
    rw [e]
    exact stabilizer_isOpen_of_isIntegral (x : AlgebraicClosure ℚ)
  have := isInvariant_algebraicIntegers
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := AlgebraicIntegers) (Ideal.span {(p : ℤ)})
  have : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) := by
    have : Fact p.Prime := ⟨hp⟩
    exact .of_equiv _ (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  cases nonempty_fintype (ℤ ⧸ Ideal.span {(p : ℤ)})
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Field.absoluteGaloisGroup ℚ) (Ideal.span {(p : ℤ)}) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (AlgebraicIntegers ⧸ Q))
  refine ⟨σ, Q, hQ, hQP, fun x => ?_⟩
  rw [← Ideal.Quotient.eq, ← hQP.over, Nat.card_eq_fintype_card]
  exact congrArg (fun φ => φ (Ideal.Quotient.mk Q x)) hσ

end Frobenius

section Artin

variable {K : Type*} [Field K] (L : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K L]

/-- For the trivial representation the projector onto the inertia invariants is the identity. -/
theorem inertiaProjector_one {n : ℕ} (P : Ideal (𝓞 L)) :
    inertiaProjector (1 : Gal(L/K) →* GL (Fin n) ℂ) P = 1 := by
  classical
  have : Fintype (P.inertia Gal(L/K)) := Fintype.ofFinite _
  rw [inertiaProjector, finsum_eq_sum_of_fintype]
  simp only [MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),
    one_smul]

/-- The local factor of the trivial character at $v$ is $(1 - N(v)^{-s})^{-1}$, with no condition on the ramification of $v$. -/
theorem artinLocalFactor_one [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    artinLocalFactor (1 : Gal(L/K) →* GL (Fin 1) ℂ) v s =
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [artinLocalFactor, inertiaProjector_one]
  simp

/-- F2 for `artinLFunction`: the Artin L-function of the trivial character of $\mathrm{Gal}(L/K)$ is the Euler product of the Dedekind zeta function of $K$, with a factor at each prime. This shows that the ramified primes have the full factor on the invariants of inertia, and that the normalization of the local factors is correct. -/
theorem artinLFunction_one [NumberField K] (s : ℂ) :
    artinLFunction (1 : Gal(L/K) →* GL (Fin 1) ℂ) s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp only [artinLFunction, artinLocalFactor_one]

end Artin

end Langlands.Fidelity
