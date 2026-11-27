/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.GlobalGL
import Langlands.Statements.Reciprocity
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Fidelity checks for the global statements for $GL_n$

This file has the checks F2 (positive instances), F3 (negative instances) and F4 (triviality attack) of spec 06.3 for the statements `Langlands.RamanujanGL`, `Langlands.FunctorialityGL` and `Langlands.ReciprocityGL`. The test objects are the constant function $1$ on $GL_n(\mathbb{A}_K)$ for $n \le 2$, the zero function, and the trivial character of $\mathrm{Gal}(\overline{K}/K)$.

## Main definitions

* `Langlands.Fidelity.constOne K n`: the constant function $1$ on $GL_n(\mathbb{A}_K)$.
* `Langlands.Fidelity.isobaricOne K m`: the isobaric sum of $m$ copies of the trivial character.
* `Langlands.Fidelity.RamanujanGLOfZero`, `Langlands.Fidelity.RamanujanGLWithoutCuspidal`, `Langlands.Fidelity.FunctorialityGLAnySet`, `Langlands.Fidelity.ReciprocityGLAllDim` and `Langlands.Fidelity.MatchesAnySet`: wrong variants of the statements, each without one condition.

## Main results

* `Langlands.Fidelity.ramanujanGL_one_constOne` (F2, F4): for $n = 1$ the hypotheses of `RamanujanGL` hold for the constant function $1$, with the Satake parameter $1$. The case $n = 1$ of the statement is `Langlands.ramanujanGL_one`.
* `Langlands.Fidelity.not_ramanujanGLOfZero_one` (F3): without $\varphi \ne 0$, `RamanujanGL 1 K` is false.
* `Langlands.Fidelity.not_ramanujanGLWithoutCuspidal_two` (F3): without the cuspidal condition, `RamanujanGL 2 K` is false. The constant function on $GL_2$ has the eigenvalues $\lambda_1 = q_v + 1$ and $\lambda_2 = 1$ and the Satake parameters $q_v^{\pm 1/2}$ of the trivial representation (`Langlands.Fidelity.sqrt_mem_satake_constOne_two`). This also checks the normalization of `satake`.
* `Langlands.Fidelity.exists_invariant_probabilityMeasure_of_ramanujanGL_two` (F4): `RamanujanGL 2 K` implies that $(\mathbb{A}_K / K)^{2 \times 2}$ has an invariant probability measure. Without such a measure the cuspidal condition is empty (`Langlands.Fidelity.hasVanishingConstantTerm_constOne_iff`).
* `Langlands.Fidelity.functorialityGL_one` (F2): `FunctorialityGL n 1 1` holds for the trivial representation $r = 1$. The case $r = \mathrm{id}$ is `Langlands.functorialityGL_id`.
* `Langlands.Fidelity.functorialityGLAnySet` (F3): without the finiteness of $S$, functoriality is trivially true for each $r$.
* `Langlands.Fidelity.functorialityGL_hypotheses` and `Langlands.Fidelity.not_isobaricOne_hasSatakeAt_two` (F4): the hypotheses of `FunctorialityGL` are satisfiable, and the condition `HasSatakeAt` of the conclusion is not always true.
* `Langlands.Fidelity.matches_cuspEigenformOne` and `Langlands.Fidelity.reciprocity_map_cuspEigenformOne` (F2): the constant function $1$ on $GL_1$ is algebraic and matches the trivial character, so each map $\Phi$ of `ReciprocityGL 1 K` sends it to the trivial character.
* `Langlands.Fidelity.not_reciprocityGLAllDim_zero` and `Langlands.Fidelity.matchesAnySet_trivial` (F3): without $0 < n$ the statement is false for $n = 0$, and without the finiteness of $S$ the matching condition holds for each pair.
* `Langlands.Fidelity.nonempty_padicAlgCl_ringEquiv_complex` and `Langlands.Fidelity.reciprocityGL_one_nonempty` (F4): an isomorphism $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ exists, so the quantifier over $\iota$ is not empty, and both sides of `ReciprocityGL 1 K` are not empty.

## Implementation notes

The cuspidal condition `HasVanishingConstantTerm` quantifies over the invariant probability measures on $(\mathbb{A}_K / K)^{n \times n}$. Such a measure exists because $\mathbb{A}_K / K$ is compact, but Mathlib does not have this fact. If there were no such measure, each function would be cuspidal, and `RamanujanGL n K` would be false for $n \ge 2$. So the statement is not trivially true, and its truth for $n \ge 2$ uses the compactness of $\mathbb{A}_K / K$.

These checks are still open.

* F2 for `ReciprocityGL 1 K`, the theorem of Weil and Serre. It needs the classification of the algebraic Hecke characters and global class field theory for the Galois characters.
* F4 for `Matches`: the existence of an arithmetic Frobenius `IsFrobAt v σ` at almost all places of $K$. Without it the matching condition would be empty. `Langlands.Fidelity.exists_isFrobeniusAt` proves the existence for the different form `Langlands.IsFrobeniusAt` over $\mathbb{Q}$.
* An F3 check that uses a cusp form on $GL_n$ for $n \ge 2$, for example a wrong normalization of the Satake parameters. The project has no such cusp form yet.
-/

namespace Langlands.Fidelity

open Langlands NumberField IsDedekindDomain NumberFieldGL Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

/-! ### Constant functions -/

/-- The constant function $1$ on $GL_n(\mathbb{A}_K)$. -/
abbrev constOne (K : Type u) [Field K] [NumberField K] (n : ℕ) : AdelicGL K n → ℂ :=
  fun _ ↦ 1

/-- The constant function $1$ is not zero. -/
theorem constOne_ne_zero (n : ℕ) : constOne K n ≠ 0 :=
  fun h ↦ one_ne_zero (congrFun h 1)

/-- For $n \le 1$ the constant function $1$ is a cusp form of level $1$. There is no proper parabolic subgroup, so the cuspidal condition is empty. -/
theorem isCuspForm_constOne {n : ℕ} (hn : n ≤ 1) : IsCuspForm (1 : 𝓞 K) (constOne K n) where
  continuous := continuous_const
  left_invariant _ _ := rfl
  level_ne_zero := one_ne_zero
  right_invariant _ _ _ := rfl
  central := ⟨1, fun _ _ ↦ by simp⟩
  growth := ⟨1, 0, fun _ ↦ by simp⟩
  cuspidal r h₁ h₂ := by omega

/-- The constant function $1$ is spherical at each finite place. -/
theorem isSphericalAt_constOne (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    IsSphericalAt (constOne K n) v :=
  fun _ _ _ ↦ rfl

/-- On $GL_1$ the constant function $1$ is a Hecke eigenvector at each finite place with the eigenvalue $1$. -/
theorem isHeckeEigenAt_constOne (v : HeightOneSpectrum (𝓞 K)) :
    IsHeckeEigenAt (constOne K 1) v (fun _ ↦ 1) := by
  refine ⟨isSphericalAt_constOne 1 v, fun i h₁ h₂ ↦ ?_⟩
  obtain rfl : i = 1 := by omega
  obtain ⟨t, ht⟩ := exists_adelicHeckeOperator_one_eq (K := K) v
  funext g
  simp [ht]

/-- The constant function $1$ on $GL_1$ is a Hecke eigenform. -/
theorem isHeckeEigenform_constOne : IsHeckeEigenform (constOne K 1) :=
  ⟨∅, Set.finite_empty, fun v _ ↦ ⟨_, isHeckeEigenAt_constOne v⟩⟩

/-- Each Hecke eigensystem of the constant function $1$ on $GL_1$ has $\lambda_1 = 1$. -/
theorem eq_one_of_isHeckeEigenAt_constOne {v : HeightOneSpectrum (𝓞 K)} {ev : ℕ → ℂ}
    (h : IsHeckeEigenAt (constOne K 1) v ev) : ev 1 = 1 :=
  heckeEigenvalue_unique (constOne_ne_zero 1) h (isHeckeEigenAt_constOne v) le_rfl le_rfl

/-- The ring of integers of a number field has a nonzero prime ideal, so there is a finite place. -/
theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨p, hp, hpr⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField K)
  exact ⟨⟨p, hpr, hp⟩⟩

/-! ### The Ramanujan conjecture -/

/-- **F2 and F4 for `RamanujanGL`.** For $n = 1$ the hypotheses of `RamanujanGL` hold for the constant function $1$ at each finite place, and its Satake parameter is $1$. So the hypotheses are satisfiable, and the conclusion holds in this case as `Langlands.ramanujanGL_one` says. -/
theorem ramanujanGL_one_constOne (v : HeightOneSpectrum (𝓞 K)) :
    IsCuspForm 1 (constOne K 1) ∧ constOne K 1 ≠ 0 ∧ (∃ C : ℝ, ∀ g, ‖constOne K 1 g‖ ≤ C) ∧
      IsHeckeEigenAt (constOne K 1) v (fun _ ↦ 1) ∧ satake 1 v (fun _ ↦ 1) = {1} :=
  ⟨isCuspForm_constOne le_rfl, constOne_ne_zero 1, ⟨1, fun _ ↦ by simp⟩,
    isHeckeEigenAt_constOne v, satake_one v _⟩

/-- The variant of `RamanujanGL` without the condition $\varphi \ne 0$. -/
def RamanujanGLOfZero (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (N : 𝓞 K) (φ : AdelicGL K n → ℂ), IsCuspForm N φ →
    (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (ev : ℕ → ℂ), IsHeckeEigenAt φ v ev →
      ∀ α ∈ satake n v ev, ‖α‖ = 1

/-- The zero function is a cusp form on $GL_n$ of level $1$. -/
theorem isCuspForm_zero (n : ℕ) : IsCuspForm (K := K) (n := n) 1 0 where
  continuous := continuous_const
  left_invariant _ _ := rfl
  level_ne_zero := one_ne_zero
  right_invariant _ _ _ := rfl
  central := ⟨1, fun _ _ ↦ by simp⟩
  growth := ⟨0, 0, fun _ ↦ by simp⟩
  cuspidal _ _ _ := by
    intro μ _ _ g
    simp

/-- The zero function is a Hecke eigenvector at each place, with each system of eigenvalues. -/
theorem isHeckeEigenAt_zero (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (ev : ℕ → ℂ) :
    IsHeckeEigenAt (0 : AdelicGL K n → ℂ) v ev :=
  ⟨fun _ _ _ ↦ rfl, fun i _ _ ↦ by funext g; simp [adelicHeckeOperator]⟩

/-- **F3 for `RamanujanGL`.** Without the condition $\varphi \ne 0$ the statement is false for $n = 1$: the zero function is a bounded cusp form and a Hecke eigenvector with the eigenvalue $2$, so its Satake parameter is $2$. So the condition $\varphi \ne 0$ is necessary. -/
theorem not_ramanujanGLOfZero_one : ¬ RamanujanGLOfZero 1 K := by
  intro h
  obtain ⟨v⟩ := nonempty_heightOneSpectrum (K := K)
  have := h 1 0 (isCuspForm_zero 1) ⟨0, fun _ ↦ by simp⟩ v (fun _ ↦ 2) (isHeckeEigenAt_zero 1 v _) 2
    (by simp [satake_one])
  norm_num at this

/-! ### Functoriality -/

/-- The isobaric sum of $m$ copies of the trivial character: $m$ copies of the constant function $1$ on $GL_1$. -/
def isobaricOne (K : Type u) [Field K] [NumberField K] (m : ℕ) : IsobaricCuspData K m where
  card := m
  size _ := 1
  level _ := 1
  form _ := constOne K 1
  isCuspForm _ := isCuspForm_constOne le_rfl
  ne_zero _ := constOne_ne_zero 1
  sum_size := by simp

/-- The isobaric sum of $m$ copies of the trivial character has the Satake parameters $\{1, \ldots, 1\}$ at each finite place. -/
theorem isobaricOne_hasSatakeAt (m : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (isobaricOne K m).HasSatakeAt v (Multiset.replicate m 1) := by
  refine ⟨fun _ _ ↦ 1, fun _ ↦ isHeckeEigenAt_constOne v, ?_⟩
  change ∑ _ : Fin m, satake 1 v (fun _ ↦ 1) = _
  simp [satake_one, Multiset.nsmul_singleton]

/-- **F4 for `FunctorialityGL`.** The condition `HasSatakeAt` of the conclusion is not empty: the trivial character does not have the Satake parameter $2$ at any place. -/
theorem not_isobaricOne_hasSatakeAt_two (v : HeightOneSpectrum (𝓞 K)) :
    ¬ (isobaricOne K 1).HasSatakeAt v {2} := by
  rintro ⟨μ, hμ, h⟩
  have h1 := eq_one_of_isHeckeEigenAt_constOne (hμ ⟨0, Nat.one_pos⟩)
  change ∑ j : Fin 1, satake 1 v (μ j) = {2} at h
  simp only [Fin.sum_univ_one, satake_one] at h
  have h2 : (2 : ℂ) = 1 := by
    rw [← h1]
    exact (Multiset.singleton_inj.1 h).symm
  norm_num at h2

/-- The trivial homomorphism $GL_n(\mathbb{C}) \to GL_1(\mathbb{C})$ is algebraic: its entry is the constant polynomial $1$. -/
theorem isAlgebraicRep_one (n : ℕ) : IsAlgebraicRep (1 : GL (Fin n) ℂ →* GL (Fin 1) ℂ) :=
  ⟨fun _ _ ↦ 1, fun g i j ↦ by simp [Subsingleton.elim i j]⟩

/-- **F2 for `FunctorialityGL`.** Functoriality holds for the trivial representation $r = 1 : GL_n(\mathbb{C}) \to GL_1(\mathbb{C})$: the lift of each form is the trivial character, with the Satake parameter $1$ at each place. Together with `Langlands.functorialityGL_id` this gives two known cases with different $m$. -/
theorem functorialityGL_one (n : ℕ) : FunctorialityGL.{u} n 1 1 := by
  intro _ K _ _ N φ _ _ _
  refine ⟨isobaricOne K 1, ∅, Set.finite_empty, fun v _ ev _ α _ ↦ ?_⟩
  have hr : ((1 : GL (Fin n) ℂ →* GL (Fin 1) ℂ) (diagonalGL α) : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    simp
  rw [hr, Matrix.charpoly_one, Fintype.card_fin, pow_one, ← C_1, roots_X_sub_C]
  exact isobaricOne_hasSatakeAt 1 v

/-- The variant of `FunctorialityGL` in which the set $S$ of excluded places need not be finite. -/
def FunctorialityGLAnySet (n m : ℕ) (r : GL (Fin n) ℂ →* GL (Fin m) ℂ) : Prop :=
  IsAlgebraicRep r →
  ∀ (K : Type u) [Field K] [NumberField K] (N : 𝓞 K) (φ : AdelicGL K n → ℂ),
    IsCuspForm N φ → φ ≠ 0 → IsHeckeEigenform φ →
    ∃ (D : IsobaricCuspData K m) (S : Set (HeightOneSpectrum (𝓞 K))),
      ∀ v ∉ S, ∀ ev : ℕ → ℂ, IsHeckeEigenAt φ v ev →
        ∀ α : Fin n → ℂˣ, Finset.univ.val.map (fun j ↦ (α j : ℂ)) = satake n v ev →
          D.HasSatakeAt v (r (diagonalGL α) : Matrix (Fin m) (Fin m) ℂ).charpoly.roots

/-- **F3 for `FunctorialityGL`.** Without the condition that $S$ is finite, the statement is trivially true for each $r$: take $S$ to be the set of all places. So the finiteness of $S$ is necessary. -/
theorem functorialityGLAnySet (n m : ℕ) (r : GL (Fin n) ℂ →* GL (Fin m) ℂ) :
    FunctorialityGLAnySet.{u} n m r :=
  fun _ K _ _ _ _ _ _ _ ↦ ⟨isobaricOne K m, Set.univ, fun _ hv ↦ (hv (Set.mem_univ _)).elim⟩

/-- **F4 for `FunctorialityGL`.** The hypotheses of `FunctorialityGL` are satisfiable: the identity is algebraic, and the constant function $1$ on $GL_1$ is a nonzero cusp form and a Hecke eigenform. -/
theorem functorialityGL_hypotheses :
    IsAlgebraicRep (MonoidHom.id (GL (Fin 1) ℂ)) ∧ IsCuspForm 1 (constOne K 1) ∧
      constOne K 1 ≠ 0 ∧ IsHeckeEigenform (constOne K 1) :=
  ⟨isAlgebraicRep_id 1, isCuspForm_constOne le_rfl, constOne_ne_zero 1, isHeckeEigenform_constOne⟩

/-! ### The constant function on $GL_2$ -/

/-- The residue field at a finite place is finite. -/
instance (v : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ v.asIdeal) := by
  have := v.isMaximal
  infer_instance

/-- The set of cosets of a Hecke operator is finite. -/
instance (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) : Finite (HeckeCoset K n v i) := by
  unfold HeckeCoset
  infer_instance

/-- The number of cosets in the Hecke operator $T_{v,i}$: a sum over the sets $s$ of $i$ indices of $q_v$ to the number of free positions. -/
theorem natCard_heckeCoset (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    Nat.card (HeckeCoset K n v i) = ∑ s ∈ (Finset.univ : Finset (Finset (Fin n))).filter (·.card = i),
      Ideal.absNorm v.asIdeal ^ Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ p.1 ∈ s ∧ p.2 ∉ s} := by
  rw [HeckeCoset, Nat.card_sigma, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) ↦ s.card = i) _ (fun s ↦ by simp) (fun s : Finset (Fin n) ↦
    Nat.card (𝓞 K ⧸ v.asIdeal) ^ Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ p.1 ∈ s ∧ p.2 ∉ s})]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Nat.card_fun]

/-- The operator $T_{v,1}$ on $GL_2$ has $q_v + 1$ cosets. -/
theorem natCard_heckeCoset_two_one (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (HeckeCoset K 2 v 1) = Ideal.absNorm v.asIdeal + 1 := by
  rw [natCard_heckeCoset]
  have hf : (Finset.univ : Finset (Finset (Fin 2))).filter (·.card = 1) = {{0}, {1}} := by decide
  have h0 : Nat.card {p : Fin 2 × Fin 2 // p.1 < p.2 ∧ p.1 ∈ ({0} : Finset (Fin 2)) ∧
      p.2 ∉ ({0} : Finset (Fin 2))} = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h1 : Nat.card {p : Fin 2 × Fin 2 // p.1 < p.2 ∧ p.1 ∈ ({1} : Finset (Fin 2)) ∧
      p.2 ∉ ({1} : Finset (Fin 2))} = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hf, Finset.sum_pair (by decide), h0, h1, pow_one, pow_zero]

/-- The operator $T_{v,2}$ on $GL_2$ has one coset. -/
theorem natCard_heckeCoset_two_two (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (HeckeCoset K 2 v 2) = 1 := by
  rw [natCard_heckeCoset]
  have hf : (Finset.univ : Finset (Finset (Fin 2))).filter (·.card = 2) = {Finset.univ} := by decide
  have h0 : Nat.card {p : Fin 2 × Fin 2 // p.1 < p.2 ∧ p.1 ∈ (Finset.univ : Finset (Fin 2)) ∧
      p.2 ∉ (Finset.univ : Finset (Fin 2))} = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hf, Finset.sum_singleton, h0, pow_zero]

/-- On a constant function, $T_{v,i}$ acts by the number of cosets. -/
theorem adelicHeckeOperator_constOne (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    adelicHeckeOperator v i (constOne K n) = (Nat.card (HeckeCoset K n v i) : ℂ) • constOne K n := by
  funext g
  have := Fintype.ofFinite (HeckeCoset K n v i)
  simp [adelicHeckeOperator, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]

/-- The Hecke eigenvalues of the constant function $1$ on $GL_2$: $\lambda_1 = q_v + 1$ and $\lambda_2 = 1$. These are the eigenvalues of the trivial representation. -/
def constTwoEigenvalues (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) : ℂ :=
  Nat.card (HeckeCoset K 2 v i)

/-- The constant function $1$ on $GL_2$ is a Hecke eigenvector at each finite place. -/
theorem isHeckeEigenAt_constOne_two (v : HeightOneSpectrum (𝓞 K)) :
    IsHeckeEigenAt (constOne K 2) v (constTwoEigenvalues v) :=
  ⟨isSphericalAt_constOne 2 v, fun i _ _ ↦ adelicHeckeOperator_constOne 2 v i⟩

/-- The norm $q_v$ of a finite place is at least $2$. -/
theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

/-- The Satake parameter $q_v^{1/2}$ of the trivial representation of $GL_2$: it is a root of the Satake polynomial of the constant function $1$. -/
theorem sqrt_mem_satake_constOne_two (v : HeightOneSpectrum (𝓞 K)) :
    ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ∈ satake 2 v (constTwoEigenvalues v) := by
  set q := Ideal.absNorm v.asIdeal with hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast two_le_absNorm v
  set s := Real.sqrt q with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : s * s = q := Real.mul_self_sqrt (by linarith)
  have hr : ((q : ℝ) ^ (-((1 * (2 - 1) : ℕ) : ℝ) / 2) : ℝ) = s⁻¹ := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
    norm_num
  have hpoly : satakePolynomial 2 q (constTwoEigenvalues v) =
      X ^ 2 - C (((s⁻¹ : ℝ) : ℂ) * ((q : ℂ) + 1)) * X + 1 := by
    rw [satakePolynomial]
    simp only [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2), Finset.Icc_self, Finset.sum_singleton]
    rw [hr]
    simp [constTwoEigenvalues, natCard_heckeCoset_two_one, natCard_heckeCoset_two_two, hq,
      sub_eq_add_neg]
    ring
  rw [satake, ← hq, hpoly, mem_roots]
  · have hsc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    have hssc : ((s : ℝ) : ℂ) * (s : ℂ) = (q : ℂ) := by exact_mod_cast hss
    simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
    push_cast
    field_simp
    linear_combination hssc
  · intro h
    have := congrArg (eval 0) h
    simp at this

/-- The Satake parameter $q_v^{1/2}$ of the trivial representation of $GL_2$ does not have absolute value $1$. -/
theorem norm_sqrt_absNorm_ne_one (v : HeightOneSpectrum (𝓞 K)) :
    ‖((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)‖ ≠ 1 := by
  have hq2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast two_le_absNorm v
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  intro h
  have := Real.sq_sqrt (show (0 : ℝ) ≤ Ideal.absNorm v.asIdeal by linarith)
  rw [h] at this
  linarith

variable (K) in
/-- The conditions of `IsCuspForm` without the cuspidal condition: an automorphic form of moderate growth with a central character. -/
structure IsAutomorphicFormGL (n : ℕ) (N : 𝓞 K) (φ : AdelicGL K n → ℂ) : Prop where
  continuous : Continuous φ
  left_invariant : ∀ (γ : GL (Fin n) K) (g : AdelicGL K n), φ (principalGL γ * g) = φ g
  level_ne_zero : N ≠ 0
  right_invariant : ∀ k : AdelicGL K n, IsInLevel N k → ∀ g, φ (g * k) = φ g
  central : ∃ ω : (AdeleRing (𝓞 K) K)ˣ → ℂ, ∀ z g, φ (g * adelicScalarGL z) = ω z * φ g
  growth : ∃ C s : ℝ, ∀ g : AdelicGL K n,
    ‖φ g‖ ≤ C * ‖(g : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)).det‖ ^ s

/-- The variant of `RamanujanGL` without the cuspidal condition. -/
def RamanujanGLWithoutCuspidal (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (N : 𝓞 K) (φ : AdelicGL K n → ℂ), IsAutomorphicFormGL K n N φ → φ ≠ 0 →
    (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (ev : ℕ → ℂ), IsHeckeEigenAt φ v ev →
      ∀ α ∈ satake n v ev, ‖α‖ = 1

/-- The constant function $1$ is an automorphic form on $GL_n$ of level $1$. -/
theorem isAutomorphicFormGL_constOne (n : ℕ) : IsAutomorphicFormGL K n 1 (constOne K n) where
  continuous := continuous_const
  left_invariant _ _ := rfl
  level_ne_zero := one_ne_zero
  right_invariant _ _ _ := rfl
  central := ⟨1, fun _ _ ↦ by simp⟩
  growth := ⟨1, 0, fun _ ↦ by simp⟩

/-- **F3 for `RamanujanGL`.** Without the cuspidal condition the statement is false for $n = 2$. The constant function $1$ on $GL_2$ is a bounded automorphic form and a Hecke eigenvector at each place, with $\lambda_1 = q_v + 1$ and $\lambda_2 = 1$. Its Satake parameters are $q_v^{1/2}$ and $q_v^{-1/2}$, the parameters of the trivial representation, which is not tempered. So the cuspidal condition is necessary, and the normalization of `satake` gives the expected parameters of the trivial representation. -/
theorem not_ramanujanGLWithoutCuspidal_two : ¬ RamanujanGLWithoutCuspidal 2 K := by
  intro h
  obtain ⟨v⟩ := nonempty_heightOneSpectrum (K := K)
  exact norm_sqrt_absNorm_ne_one v (h 1 _ (isAutomorphicFormGL_constOne 2) (constOne_ne_zero 2)
    ⟨1, fun _ ↦ by simp⟩ v _ (isHeckeEigenAt_constOne_two v) _ (sqrt_mem_satake_constOne_two v))

/-- The constant term of the constant function $1$ vanishes if and only if there is no invariant probability measure on $(\mathbb{A}_K / K)^{n \times n}$. -/
theorem hasVanishingConstantTerm_constOne_iff (n r : ℕ) :
    HasVanishingConstantTerm r (constOne K n) ↔
      letI : MeasurableSpace (AdeleQuotient K) := borel _
      ∀ μ : MeasureTheory.Measure (Fin n → Fin n → AdeleQuotient K),
        MeasureTheory.IsProbabilityMeasure μ → ¬ μ.IsAddLeftInvariant := by
  let _ : MeasurableSpace (AdeleQuotient K) := borel _
  refine ⟨fun h μ hμ hinv ↦ ?_, fun h μ hμ hinv ↦ (h μ hμ hinv).elim⟩
  have := h μ hμ hinv 1
  simp at this

/-- **F4 for `RamanujanGL`.** If `RamanujanGL 2 K` holds, then there is an invariant probability measure on $(\mathbb{A}_K / K)^{2 \times 2}$. If there were none, the cuspidal condition would be empty, and the constant function $1$ would be a counterexample by `not_ramanujanGLWithoutCuspidal_two`. Such a measure exists because $\mathbb{A}_K / K$ is compact, but Mathlib does not have this fact. So the statement for $n \ge 2$ is not trivially true, and its truth uses the compactness of $\mathbb{A}_K / K$. -/
theorem exists_invariant_probabilityMeasure_of_ramanujanGL_two (h : RamanujanGL 2 K) :
    letI : MeasurableSpace (AdeleQuotient K) := borel _
    ∃ μ : MeasureTheory.Measure (Fin 2 → Fin 2 → AdeleQuotient K),
      MeasureTheory.IsProbabilityMeasure μ ∧ μ.IsAddLeftInvariant := by
  let _ : MeasurableSpace (AdeleQuotient K) := borel _
  by_contra hne
  push Not at hne
  have hc : IsCuspForm (1 : 𝓞 K) (constOne K 2) :=
    { isAutomorphicFormGL_constOne (K := K) 2 with
      cuspidal := fun r _ _ ↦ (hasVanishingConstantTerm_constOne_iff 2 r).2 hne }
  obtain ⟨v⟩ := nonempty_heightOneSpectrum (K := K)
  exact norm_sqrt_absNorm_ne_one v (h 1 _ hc (constOne_ne_zero 2) ⟨1, fun _ ↦ by simp⟩ v _
    (isHeckeEigenAt_constOne_two v) _ (sqrt_mem_satake_constOne_two v))

/-! ### Reciprocity -/

/-- The field $\mathbb{Q}_p$ has the cardinality of the continuum. -/
theorem mk_padic (p : ℕ) [Fact p.Prime] : Cardinal.mk ℚ_[p] = Cardinal.continuum := by
  refine le_antisymm ?_ (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])
  have h₁ : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p)) :=
    Cardinal.mk_le_of_surjective (f := (Quotient.mk _ : CauSeq ℚ (padicNorm p) →
      CauSeq.Completion.Cauchy (padicNorm p))) Quotient.mk_surjective
  have h₂ : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_subtype_le _
  have h₃ : Cardinal.mk (ℕ → ℚ) = Cardinal.continuum := by
    rw [← Cardinal.power_def, Cardinal.mk_nat, Cardinal.mkRat, Cardinal.aleph0_power_aleph0]
  exact h₁.trans (h₂.trans h₃.le)

/-- The field $\overline{\mathbb{Q}}_p$ has the cardinality of the continuum. -/
theorem mk_padicAlgCl (p : ℕ) [Fact p.Prime] : Cardinal.mk (PadicAlgCl p) = Cardinal.continuum := by
  refine le_antisymm ?_ ?_
  · have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    rwa [mk_padic, max_eq_left Cardinal.aleph0_le_continuum] at this
  · rw [← mk_padic p]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

/-- **F4 for `ReciprocityGL`.** For each prime $\ell$ there is an isomorphism of fields $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$. Both are algebraically closed of characteristic $0$ and have the cardinality of the continuum. So the quantifier over $\iota$ in `ReciprocityGL` and `AutomorphicToGalois` is not empty, and the statements are not vacuous. -/
theorem nonempty_padicAlgCl_ringEquiv_complex (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (PadicAlgCl ℓ ≃+* ℂ) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [mk_padicAlgCl]
    exact Cardinal.aleph0_lt_continuum
  · exact Cardinal.eq.1 ((mk_padicAlgCl ℓ).trans Cardinal.mk_complex.symm)

/-- The derivatives at the infinite places of a constant function are zero. -/
theorem lieDerivative_const {n : ℕ} (w : InfinitePlace K) (X : Matrix (Fin n) (Fin n) w.Completion)
    (c : ℂ) : lieDerivative w X (fun _ : AdelicGL K n ↦ c) = 0 := by
  funext g
  simp [lieDerivative]

/-- A constant function on $GL_1$ has the Capelli root $0$ for each family of operators that kill the constants. -/
theorem hasCapelliRoots_constOne_one {D : Fin 1 → Fin 1 → (AdelicGL K 1 → ℂ) → AdelicGL K 1 → ℂ}
    (hD : D 0 0 (constOne K 1) = 0) : HasCapelliRoots D (constOne K 1) {0} := by
  refine ⟨rfl, fun u ↦ ?_⟩
  rw [capelliOperator_one, hD]
  simp

/-- On $GL_0$ each function has the empty multiset of Capelli roots. -/
theorem hasCapelliRoots_zero (D : Fin 0 → Fin 0 → (AdelicGL K 0 → ℂ) → AdelicGL K 0 → ℂ)
    (φ : AdelicGL K 0 → ℂ) : HasCapelliRoots D φ 0 :=
  ⟨rfl, fun u ↦ by simp [capelliOperator]⟩

/-- For $n \le 1$ the constant function $1$ is algebraic in the sense of Clozel. For $n = 1$ its Capelli root is $0$ at each infinite place: the trivial character is an algebraic Hecke character. -/
theorem isAlgebraicForm_constOne {n : ℕ} (hn : n ≤ 1) : IsAlgebraicForm (constOne K n) := by
  refine ⟨fun _ _ _ _ ↦ contDiffAt_const, fun w ↦ ?_⟩
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact ⟨fun _ ↦ ⟨0, trivial, hasCapelliRoots_zero _ _⟩,
      fun _ ↦ ⟨⟨0, trivial, hasCapelliRoots_zero _ _⟩, ⟨0, trivial, hasCapelliRoots_zero _ _⟩⟩⟩
  · refine ⟨fun _ ↦ ⟨{0}, trivial, hasCapelliRoots_constOne_one ?_⟩,
      fun _ ↦ ⟨⟨{0}, trivial, hasCapelliRoots_constOne_one ?_⟩,
        ⟨{0}, trivial, hasCapelliRoots_constOne_one ?_⟩⟩⟩
    · exact lieDerivative_const w _ 1
    · simp [holGenerator, lieDerivative_const]
    · simp [antiholGenerator, lieDerivative_const]

/-- For $n \le 1$ the constant function $1$ is a Hecke eigenform. -/
theorem isHeckeEigenform_constOne_of_le {n : ℕ} (hn : n ≤ 1) : IsHeckeEigenform (constOne K n) := by
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact ⟨∅, Set.finite_empty, fun v _ ↦
      ⟨fun _ ↦ 1, isSphericalAt_constOne 0 v, fun i h₁ h₂ ↦ by omega⟩⟩
  · exact isHeckeEigenform_constOne

/-- The constant function $1$ as a cuspidal eigenform on $GL_n$ for $n \le 1$. -/
def cuspEigenformOne {n : ℕ} (hn : n ≤ 1) : CuspEigenform K n :=
  ⟨constOne K n, ⟨1, isCuspForm_constOne hn⟩, constOne_ne_zero n, isHeckeEigenform_constOne_of_le hn⟩

/-- The class of the constant function $1$ is algebraic. -/
theorem isAlgebraicClass_cuspEigenformOne {n : ℕ} (hn : n ≤ 1) :
    IsAlgebraicClass (Quotient.mk _ (cuspEigenformOne (K := K) hn)) :=
  ⟨_, rfl, isAlgebraicForm_constOne hn⟩

/-- The trivial character of $\mathrm{Gal}(\overline{K}/K)$ as a representation of the Galois side. -/
def galoisRepOne (K : Type u) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] :
    GaloisRep K 1 ℓ :=
  ⟨1, (isGaloisRep_one K ℓ).1⟩

/-- **F2 for `ReciprocityGL`.** The constant function $1$ on $GL_1$ and the trivial character match at all places: the Hecke polynomial $X - \lambda_1$ is $X - 1$, the characteristic polynomial of the identity. So the matching condition holds for the pair of the trivial representations, which correspond under the theorem of Weil and Serre. -/
theorem matches_cuspEigenformOne {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) :
    Matches ι (cuspEigenformOne (K := K) le_rfl) (galoisRepOne K ℓ).1 := by
  refine ⟨∅, Set.finite_empty, fun v _ ev hev σ _ ↦ ?_⟩
  rw [heckePolynomial_one_eq_charpoly_map_iff, eq_one_of_isHeckeEigenAt_constOne hev]
  simp [galoisRepOne]

/-- **F2 for `ReciprocityGL`.** A map $\Phi$ with the matching property of `ReciprocityGL` for $n = 1$ sends the class of the constant function $1$ to the class of the trivial character, as the theorem of Weil and Serre does. -/
theorem reciprocity_map_cuspEigenformOne {ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (Φ : {c : AutomorphicClass K 1 // IsAlgebraicClass c} → GaloisClass K 1 ℓ)
    (h : ∀ (φ : CuspEigenform K 1) (hφ : IsAlgebraicClass (Quotient.mk _ φ)) (ρ : GaloisRep K 1 ℓ),
      Φ ⟨Quotient.mk _ φ, hφ⟩ = Quotient.mk _ ρ ↔ Matches ι φ ρ.1) :
    Φ ⟨Quotient.mk _ (cuspEigenformOne le_rfl), isAlgebraicClass_cuspEigenformOne le_rfl⟩ =
      Quotient.mk _ (galoisRepOne K ℓ) :=
  (h _ _ _).2 (matches_cuspEigenformOne ι)

/-- The variant of `ReciprocityGL` without the condition $0 < n$. -/
def ReciprocityGLAllDim (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
    ∃ Φ : {c : AutomorphicClass K n // IsAlgebraicClass c} → GaloisClass K n ℓ,
      Function.Injective Φ ∧
      (∀ (φ : CuspEigenform K n) (hφ : IsAlgebraicClass (Quotient.mk _ φ)) (ρ : GaloisRep K n ℓ),
        Φ ⟨Quotient.mk _ φ, hφ⟩ = Quotient.mk _ ρ ↔ Matches ι φ ρ.1) ∧
      ∀ ρ : GaloisRep K n ℓ, (Set.range ρ.1).Finite → ∃ c, Φ c = Quotient.mk _ ρ

/-- There is no representation of dimension $0$ on the Galois side, because an irreducible representation is nonzero. -/
theorem isEmpty_galoisClass_zero (ℓ : ℕ) [Fact ℓ.Prime] : IsEmpty (GaloisClass K 0 ℓ) :=
  ⟨fun c ↦ by
    obtain ⟨ρ, -⟩ := Quotient.exists_rep c
    exact lt_irrefl 0 ρ.2.irreducible.1⟩

/-- **F3 for `ReciprocityGL`.** Without the condition $0 < n$ the statement is false for $n = 0$. On the automorphic side the constant function on $GL_0$ gives an algebraic class, and on the Galois side there is no class. The proof uses an isomorphism $\overline{\mathbb{Q}}_2 \cong \mathbb{C}$ from `nonempty_padicAlgCl_ringEquiv_complex`. So the condition $0 < n$ is necessary. -/
theorem not_reciprocityGLAllDim_zero : ¬ ReciprocityGLAllDim 0 K := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨Φ, -⟩ := h 2 ι
  exact (isEmpty_galoisClass_zero (K := K) 2).elim
    (Φ ⟨Quotient.mk _ (cuspEigenformOne (Nat.zero_le 1)), isAlgebraicClass_cuspEigenformOne _⟩)

/-- **F4 for `ReciprocityGL`.** For $n = 1$ both sides of `ReciprocityGL` are not empty: there is an algebraic class, a representation with finite image, and an isomorphism $\iota$. So no part of the statement for $n = 1$ is vacuous. -/
theorem reciprocityGL_one_nonempty (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty {c : AutomorphicClass K 1 // IsAlgebraicClass c} ∧
      (∃ ρ : GaloisRep K 1 ℓ, (Set.range ρ.1).Finite) ∧ Nonempty (PadicAlgCl ℓ ≃+* ℂ) :=
  ⟨⟨⟨_, isAlgebraicClass_cuspEigenformOne le_rfl⟩⟩, ⟨galoisRepOne K ℓ, (isGaloisRep_one K ℓ).2⟩,
    nonempty_padicAlgCl_ringEquiv_complex ℓ⟩

/-- The matching condition of `Langlands.NumberFieldGL.Matches` without the condition that the set $S$ of excluded places is finite. -/
def MatchesAnySet {n ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) (φ : CuspEigenform K n)
    (ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ)) : Prop :=
  ∃ S : Set (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S, ∀ ev : ℕ → ℂ,
    IsHeckeEigenAt φ.1 v ev → ∀ σ, IsFrobAt v σ →
      heckePolynomial n (Ideal.absNorm v.asIdeal) ev =
        (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).charpoly.map (ι : PadicAlgCl ℓ →+* ℂ)

/-- **F3 for `ReciprocityGL`.** The matching condition at a set of places that need not be cofinite holds for each pair $(\varphi, \rho)$: take the set of all places. So the finiteness of $S$ in `Matches` is necessary, and with the weak condition the second property of `ReciprocityGL` would identify all the Galois classes. -/
theorem matchesAnySet_trivial {n ℓ : ℕ} [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ)
    (φ : CuspEigenform K n) (ρ : GlobalFunctionField.GaloisGroup K →* GL (Fin n) (PadicAlgCl ℓ)) :
    MatchesAnySet ι φ ρ :=
  ⟨Set.univ, fun _ hv ↦ (hv (Set.mem_univ _)).elim⟩

end

end Langlands.Fidelity
