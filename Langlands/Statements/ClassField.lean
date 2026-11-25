/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Locus

/-!
# The statements of class field theory

This file states local and global class field theory in the form that the Langlands program uses. These are the statements of row 6.2.2 of the spec with the class "theorem". Each statement is a `def` of type `Prop`. The proofs are in other files, and the status of each statement on the site comes from the Lean index.

* `Langlands.LocalReciprocityGL1`: for a nonarchimedean local field $K$ there is a unique topological isomorphism $\mathrm{rec}_K : K^\times \to W_K^{ab}$ that sends each uniformizer to the class of a geometric Frobenius, and that is compatible with the norm groups of the finite abelian extensions. This is the local Langlands correspondence for $GL_1$.
* `Langlands.LocalExistence`: each open subgroup of finite index of $K^\times$ is the norm group of a finite abelian extension.
* `Langlands.GlobalReciprocity`: for a number field $K$ and a finite abelian extension $L$, there is a continuous surjective homomorphism from the idele class group of $K$ to $\mathrm{Gal}(L/K)$ that sends a uniformizer at an unramified prime to the inverse of the Frobenius.
* `Langlands.GlobalExistence`: each open subgroup of finite index of the idele class group is the kernel of such a map.
* `Langlands.KroneckerWeber`: each finite abelian extension of $\mathbb{Q}$ is contained in a cyclotomic field.

## Implementation notes

The finite extensions are intermediate fields of a fixed algebraic closure. Every finite extension of $K$ embeds in it, so this is not a restriction.

The normalization is geometric everywhere: a uniformizer maps to a geometric Frobenius. In the global statement this means that the inverse of the image of a uniformizer is an arithmetic Frobenius, which is the form of `IsArithFrobAt` in Mathlib.

The global statement asks only for the Frobenius at the unramified primes. This determines the map, because the principal ideles and the ideles that are trivial at a finite set of places generate a dense subgroup (weak approximation). The compatibility with `LocalReciprocityGL1` at every place needs the fact that the completions of a number field are local fields in the sense of `IsNonarchimedeanLocalField`. Mathlib does not have this instance yet, and the compatibility is a statement of milestone S2.

## References

* J.-P. Serre, Local class field theory, in Algebraic number theory (Cassels and Frohlich, eds.), 1967.
* J. Tate, Global class field theory, ibid.
* J. Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, part 2, 1979.
-/

namespace Langlands

open ValuativeRel NumberField IsDedekindDomain

universe u

/-- An element of a valued field is a uniformizer if it is an irreducible element of the ring of integers. -/
def IsUniformizer {K : Type*} [Field K] [ValuativeRel K] (x : K) : Prop :=
  ∃ π : 𝒪[K], Irreducible π ∧ (π : K) = x

/-- The norm group $N_{L/K}(L^\times)$ as a subgroup of $K^\times$. -/
noncomputable def normGroup (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range

section Local

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The properties of the local reciprocity map $\mathrm{rec}_K : K^\times \to W_K^{ab}$, in the geometric normalization. -/
structure IsLocalArtinMap (rec : Kˣ ≃ₜ* WeilGroup.Ab K) : Prop where
  /-- Each uniformizer maps to the class of a geometric Frobenius. -/
  uniformizer : ∀ ϖ : Kˣ, IsUniformizer (ϖ : K) →
    ∃ Φ : WeilGroup K, WeilGroup.IsGeometricFrobenius K Φ ∧ rec ϖ = (Φ : WeilGroup.Ab K)
  /-- For each finite abelian extension, the map to its Galois group is surjective. -/
  surjective : ∀ (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L], Function.Surjective (WeilGroup.Ab.restrict K L ∘ rec)
  /-- For each finite abelian extension, the kernel of the map to its Galois group is the norm group. -/
  ker : ∀ (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ), WeilGroup.Ab.restrict K L (rec x) = 1 ↔ x ∈ normGroup K L

end Local

/-- Local class field theory as the local Langlands correspondence for $GL_1$: for each nonarchimedean local field $K$ there is a unique topological isomorphism $K^\times \cong W_K^{ab}$ with the properties of `IsLocalArtinMap`. -/
def LocalReciprocityGL1 : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    ∃! rec : Kˣ ≃ₜ* WeilGroup.Ab K, IsLocalArtinMap K rec

/-- The local existence theorem: each open subgroup of finite index of $K^\times$ is the norm group of a finite abelian extension of $K$. -/
def LocalExistence : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (U : Subgroup Kˣ), IsOpen (U : Set Kˣ) → U.FiniteIndex →
      ∃ L : IntermediateField K (AlgebraicClosure K),
        FiniteDimensional K L ∧ IsAbelianGalois K L ∧ normGroup K L = U

section Global

variable (K : Type u) [Field K] [NumberField K]

/-- The Galois group of $L/K$ acts on the ring of integers of $L$, and the action is linear over the ring of integers of $K$. -/
instance (L : IntermediateField K (AlgebraicClosure K)) : SMulCommClass Gal(L/K) (𝓞 K) (𝓞 L) where
  smul_comm g r x := by
    apply RingOfIntegers.ext
    change g ((algebraMap (𝓞 K) (𝓞 L) r : L) * (x : L)) =
      (algebraMap (𝓞 K) (𝓞 L) r : L) * g (x : L)
    rw [map_mul]
    congr 1
    exact g.commutes (r : K)

/-- The properties of the Artin map $C_K \to \mathrm{Gal}(L/K)$ of a finite abelian extension $L$ of a number field $K$, in the geometric normalization. -/
structure IsArtinMap (L : IntermediateField K (AlgebraicClosure K))
    (art : IdeleClassGroup (𝓞 K) K →* Gal(L/K)) : Prop where
  /-- The map is continuous. -/
  continuous : Continuous art
  /-- The map is surjective. -/
  surjective : Function.Surjective art
  /-- At a prime $w$ of $L$ over a finite place $v$ of $K$ where $L$ is unramified, the inverse of the image of a uniformizer of $K_v$ is the arithmetic Frobenius at $w$. -/
  frobenius : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : Ideal (𝓞 L)) [w.IsMaximal],
    w.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 K) w →
      ∀ ϖ : (v.adicCompletion K)ˣ, IsUniformizer (ϖ : v.adicCompletion K) →
        IsArithFrobAt (𝓞 K) (art (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v ϖ))⁻¹ w

end Global

/-- Global reciprocity: for each finite abelian extension $L$ of a number field $K$ there is an Artin map from the idele class group of $K$ to $\mathrm{Gal}(L/K)$. -/
def GlobalReciprocity : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : IntermediateField K (AlgebraicClosure K)),
    FiniteDimensional K L → IsAbelianGalois K L →
      ∃ art : IdeleClassGroup (𝓞 K) K →* Gal(L/K), IsArtinMap K L art

/-- The global existence theorem: each open subgroup of finite index of the idele class group is the kernel of the Artin map of a finite abelian extension. -/
def GlobalExistence : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (U : Subgroup (IdeleClassGroup (𝓞 K) K)),
    IsOpen (U : Set (IdeleClassGroup (𝓞 K) K)) → U.FiniteIndex →
      ∃ (L : IntermediateField K (AlgebraicClosure K)) (art : IdeleClassGroup (𝓞 K) K →* Gal(L/K)),
        FiniteDimensional K L ∧ IsAbelianGalois K L ∧ IsArtinMap K L art ∧ art.ker = U

/-- The theorem of Kronecker and Weber: each finite abelian extension of $\mathbb{Q}$ is contained in a cyclotomic field. -/
def KroneckerWeber : Prop :=
  ∀ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L → IsAbelianGalois ℚ L →
    ∃ (n : ℕ) (ζ : AlgebraicClosure ℚ), 0 < n ∧ IsPrimitiveRoot ζ n ∧
      L ≤ IntermediateField.adjoin ℚ {ζ}

end Langlands
