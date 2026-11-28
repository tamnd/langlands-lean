/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2Reduction
import Langlands.Reciprocity.Unique
import Langlands.WeilGroup.Inertia
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The Galois side of the tame parametrization for $GL_2$

Let $K$ be a nonarchimedean local field with residue characteristic $p \ne 2$. This file reduces `Langlands.LocalGL2.GaloisTameParametrization` (Bushnell and Henniart, The local Langlands conjecture for GL(2), 34.1) to named facts about the Weil group $W_K$. Each fact is a published theorem of local class field theory or of ramification theory. None of them mentions Weil-Deligne representations or admissible pairs.

The proof has three parts.

1. Linear algebra in dimension $2$. A finite $p$-group of $GL_2(\mathbb{C})$ with $p$ odd has a common eigenvector.
2. Clifford theory in dimension $2$. Let $\rho$ be an irreducible representation of a group $W$ on $\mathbb{C}^2$ and let $N$ be a normal subgroup with a common eigenvector $v$. If some element of $N$ is not scalar, then the stabilizer of the line $\mathbb{C} v$ has index $2$, and $\rho$ is induced from a character of this stabilizer.
3. The Weil group. The wild inertia group $P_K$ is a pro-$p$ group, so it has a common eigenvector. If $P_K$ is not scalar, then part 2 applies to $N = P_K$. If $P_K$ is scalar, then the tame inertia group is procyclic, so the inertia group $I_K$ has a common eigenvector. If $I_K$ is not scalar, then part 2 applies to $N = I_K$. The inertia group cannot be scalar, since then a Frobenius element gives a stable line.

## Main definitions

* `Langlands.LocalGL2.IsScalarMat`: a $2 \times 2$ matrix is scalar.
* `Langlands.LocalGL2.lineStab`: the stabilizer of a line under a representation of dimension $2$.
* `Langlands.LocalGL2.lineChar`: the character of the stabilizer on the line.
* `Langlands.LocalGL2.wildInertia`: the wild inertia subgroup $P_K$ of $W_K$.
* `Langlands.LocalGL2.WildInertiaProP`, `Langlands.LocalGL2.TameInertiaProcyclic`, `Langlands.LocalGL2.OpenIndexTwoQuad`, `Langlands.LocalGL2.InertiaUnramified`, `Langlands.LocalGL2.UniqueUnramifiedQuad`, `Langlands.LocalGL2.WildArtinUnits`, `Langlands.LocalGL2.NormFactorU1`: the named published facts.
* `Langlands.LocalGL2.GaloisTameInputs`: the bundle of these facts with `Langlands.LocalGL2.ArtinConjCompat`.

## Main results

* `Langlands.LocalGL2.exists_common_eigen_of_isPGroup`: a finite $p$-subgroup of $GL_2(\mathbb{C})$ with $p$ odd has a common eigenvector.
* `Langlands.LocalGL2.index_lineStab`: Clifford theory in dimension $2$.
* `Langlands.LocalGL2.exists_tamePair_of_isIrreducible`: part 1 of the parametrization from the inputs.
* `Langlands.LocalGL2.eq_of_tameParam_iso`: part 2 of the parametrization from the inputs.
* `Langlands.LocalGL2.galoisTameParametrization_of_inputs`: the inputs imply `Langlands.LocalGL2.GaloisTameParametrization`.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), sections 18.2 and 34.1.
* J.-P. Serre, Local fields, Chapters III, IV and XV.
* J. Tate, Number theoretic background, section 1.4.
* K. Iwasawa, On Galois groups of local fields.

## Still open

The named facts in `Langlands.LocalGL2.GaloisTameInputs` are not proved here.
-/

open Matrix

namespace Langlands.LocalGL2

universe u

/-- The determinant $x_0 y_1 - x_1 y_0$ of two vectors $x, y$ of $\mathbb{C}^2$. -/
def gtpDet (x y : Fin 2 → ℂ) : ℂ := x 0 * y 1 - x 1 * y 0

/-- A matrix is a scalar matrix: it acts on $\mathbb{C}^2$ as multiplication by a scalar. -/
def IsScalarMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop := ∃ c : ℂ, ∀ x, M *ᵥ x = c • x

@[simp]
theorem gtpDet_smul_left (c : ℂ) (x y : Fin 2 → ℂ) : gtpDet (c • x) y = c * gtpDet x y := by
  simp [gtpDet]; ring

@[simp]
theorem gtpDet_smul_right (c : ℂ) (x y : Fin 2 → ℂ) : gtpDet x (c • y) = c * gtpDet x y := by
  simp [gtpDet]; ring

@[simp]
theorem gtpDet_self (x : Fin 2 → ℂ) : gtpDet x x = 0 := by
  simp [gtpDet]; ring

/-- If $x \ne 0$ and $\det(x, y) = 0$, then $y$ is a multiple of $x$. -/
theorem exists_eq_smul_of_gtpDet_eq_zero {x y : Fin 2 → ℂ} (hx : x ≠ 0) (h : gtpDet x y = 0) :
    ∃ c : ℂ, y = c • x := by
  unfold gtpDet at h
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := fun h1 => hx (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨y 1 / x 1, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_left h1
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨y 0 / x 0, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

/-- If $y = c x$, then $\det(x, y) = 0$. -/
theorem gtpDet_eq_zero_of_eq_smul {x y : Fin 2 → ℂ} {c : ℂ} (h : y = c • x) : gtpDet x y = 0 := by
  simp [h]

/-- Cramer's rule in dimension $2$: $\det(x, y) z = \det(z, y) x + \det(x, z) y$. -/
theorem gtpDet_smul_eq (x y z : Fin 2 → ℂ) :
    gtpDet x y • z = gtpDet z y • x + gtpDet x z • y := by
  ext i
  fin_cases i <;> simp [gtpDet] <;> ring

/-- The trace identity $\det(M x, y) + \det(x, M y) = \mathrm{tr}(M) \det(x, y)$. -/
theorem gtpDet_mulVec_add (M : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 2 → ℂ) :
    gtpDet (M *ᵥ x) y + gtpDet x (M *ᵥ y) = (M 0 0 + M 1 1) * gtpDet x y := by
  simp [gtpDet, mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- If two vectors $x, y$ with $\det(x, y) \ne 0$ are eigenvectors of $M$ with the same eigenvalue $a$, then $M$ is the scalar $a$. -/
theorem mulVec_eq_smul_of_gtpDet_ne_zero {M : Matrix (Fin 2) (Fin 2) ℂ} {x y : Fin 2 → ℂ} {a : ℂ}
    (hd : gtpDet x y ≠ 0) (hx : M *ᵥ x = a • x) (hy : M *ᵥ y = a • y) (z : Fin 2 → ℂ) :
    M *ᵥ z = a • z := by
  have h := congrArg (M *ᵥ ·) (gtpDet_smul_eq x y z)
  simp only [mulVec_smul, mulVec_add, hx, hy] at h
  have h2 : gtpDet x y • (M *ᵥ z) = gtpDet x y • (a • z) := by
    rw [h, smul_comm (gtpDet x y) a z, gtpDet_smul_eq x y z, smul_add, smul_comm a,
      smul_comm a (gtpDet x z)]
  exact smul_right_injective _ hd h2

/-- Let $x, y$ with $\det(x, y) \ne 0$ be eigenvectors of $M$ with distinct eigenvalues. Then each eigenvector $z$ of $M$ is a multiple of $x$ or of $y$. -/
theorem gtpDet_eq_zero_or_of_eigen {M : Matrix (Fin 2) (Fin 2) ℂ} {x y z : Fin 2 → ℂ}
    {a b c : ℂ} (hd : gtpDet x y ≠ 0) (hab : a ≠ b) (hx : M *ᵥ x = a • x) (hy : M *ᵥ y = b • y)
    (hz : M *ᵥ z = c • z) : gtpDet z y = 0 ∨ gtpDet x z = 0 := by
  have h1 := gtpDet_mulVec_add M x y
  have h2 := gtpDet_mulVec_add M z y
  have h3 := gtpDet_mulVec_add M x z
  rw [hx, hy, gtpDet_smul_left, gtpDet_smul_right] at h1
  rw [hz, hy, gtpDet_smul_left, gtpDet_smul_right] at h2
  rw [hx, hz, gtpDet_smul_left, gtpDet_smul_right] at h3
  have hT : M 0 0 + M 1 1 = a + b := by
    have : (a + b - (M 0 0 + M 1 1)) * gtpDet x y = 0 := by linear_combination h1
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)).symm
  by_contra hne
  push Not at hne
  have hc1 : c = a := by
    have : (c - a) * gtpDet z y = 0 := by rw [hT] at h2; linear_combination h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne.1)
  have hc2 : c = b := by
    have : (c - b) * gtpDet x z = 0 := by rw [hT] at h3; linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne.2)
  exact hab (hc1.symm.trans hc2)

/-- An eigenvalue $a$ of $M$ is a root of the characteristic polynomial $(M_{00} - t)(M_{11} - t) - M_{01} M_{10}$. -/
theorem charQ_eq_zero {M : Matrix (Fin 2) (Fin 2) ℂ} {x : Fin 2 → ℂ} {a : ℂ} (hx0 : x ≠ 0)
    (hx : M *ᵥ x = a • x) : (M 0 0 - a) * (M 1 1 - a) - M 0 1 * M 1 0 = 0 := by
  have e0 := congrFun hx 0
  have e1 := congrFun hx 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  by_contra hne
  apply hx0
  ext i
  fin_cases i
  · have : ((M 0 0 - a) * (M 1 1 - a) - M 0 1 * M 1 0) * x 0 = 0 := by
      linear_combination (M 1 1 - a) * e0 - M 0 1 * e1
    simpa using (mul_eq_zero.1 this).resolve_left hne
  · have : ((M 0 0 - a) * (M 1 1 - a) - M 0 1 * M 1 0) * x 1 = 0 := by
      linear_combination (M 0 0 - a) * e1 - M 1 0 * e0
    simpa using (mul_eq_zero.1 this).resolve_left hne

/-- A quadratic polynomial has at most two roots: if $a \ne b$ and $a, b, c$ are roots, then $c = a$ or $c = b$. -/
theorem eq_or_eq_of_charQ {m n k a b c : ℂ} (hab : a ≠ b) (ha : (m - a) * (n - a) - k = 0)
    (hb : (m - b) * (n - b) - k = 0) (hc : (m - c) * (n - c) - k = 0) : c = a ∨ c = b := by
  have h1 : (a - b) * (a + b - m - n) = 0 := by linear_combination ha - hb
  have h2 : a + b - m - n = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hab)
  have h3 : (c - a) * (c - b) = 0 := by linear_combination hc - ha - (c - a) * h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

/-- Each complex $2 \times 2$ matrix has an eigenvector. -/
theorem exists_eigen (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ x : Fin 2 → ℂ, x ≠ 0 ∧ ∃ a : ℂ, M *ᵥ x = a • x := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
  obtain ⟨x, hx⟩ := ha.exists_hasEigenvector
  exact ⟨x, hx.2, a, by simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hx.1⟩

/-- A scalar matrix commutes with each matrix. -/
theorem IsScalarMat.commute {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsScalarMat M)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : A * M = M * A := by
  obtain ⟨c, hc⟩ := hM
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, hc, hc, mulVec_smul]

/-- An element of the center of $\mathrm{GL}_2(\mathbb{C})$ is a scalar matrix. -/
theorem isScalarMat_of_mem_center {g : GL (Fin 2) ℂ} (hg : g ∈ Subgroup.center (GL (Fin 2) ℂ)) :
    IsScalarMat g := by
  obtain ⟨a, ha⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hg
  refine ⟨a, fun x => ?_⟩
  rw [← ha]
  simp [Matrix.scalar_apply]

/-- A scalar matrix in $\mathrm{GL}_2(\mathbb{C})$ lies in the center. -/
theorem mem_center_of_isScalarMat {g : GL (Fin 2) ℂ} (hg : IsScalarMat g) :
    g ∈ Subgroup.center (GL (Fin 2) ℂ) := by
  refine Subgroup.mem_center_iff.2 fun h => Units.ext ?_
  exact hg.commute _

/-- A scalar matrix $M = c$ satisfies $M A = c A$. -/
theorem IsScalarMat.mul_eq {M : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ} (hc : ∀ x, M *ᵥ x = c • x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : M * A = c • A := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, hc, smul_mulVec]

/-- An eigenvalue of an invertible matrix is not zero. -/
theorem eigen_ne_zero (g : GL (Fin 2) ℂ) {x : Fin 2 → ℂ} {a : ℂ} (hx0 : x ≠ 0)
    (hx : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x = a • x) : a ≠ 0 := by
  rintro rfl
  apply hx0
  have : ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) = x := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← this, hx, zero_smul, mulVec_zero]

/-- The image of a vector under an invertible matrix is not zero. -/
theorem mulVec_ne_zero (g : GL (Fin 2) ℂ) {x : Fin 2 → ℂ} (hx0 : x ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x ≠ 0 := by
  intro h
  apply hx0
  have : ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) = x := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← this, h, mulVec_zero]

/-- Let $p$ be an odd prime. A finite $p$-subgroup of $\mathrm{GL}_2(\mathbb{C})$ has a common eigenvector. -/
theorem exists_common_eigen_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (G : Subgroup (GL (Fin 2) ℂ)) [Finite G] (hG : IsPGroup p G) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∀ g ∈ G, ∃ c : ℂ, (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v := by
  by_cases hsc : G ≤ Subgroup.center (GL (Fin 2) ℂ)
  · refine ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0, fun g hg => ?_⟩
    obtain ⟨c, hc⟩ := isScalarMat_of_mem_center (hsc hg)
    exact ⟨c, hc _⟩
  obtain ⟨y, hyG, hyZ, hcomm⟩ : ∃ y ∈ G, y ∉ Subgroup.center (GL (Fin 2) ℂ) ∧
      ∀ h ∈ G, y * h * y⁻¹ * h⁻¹ ∈ Subgroup.center (GL (Fin 2) ℂ) := by
    set Z := (Subgroup.center (GL (Fin 2) ℂ)).subgroupOf G
    have hQ : IsPGroup p (G ⧸ Z) := hG.to_quotient Z
    have : Nontrivial (G ⧸ Z) := by
      obtain ⟨g, hg, hgZ⟩ := Set.not_subset.1 hsc
      refine ⟨⟨((⟨g, hg⟩ : G) : G ⧸ Z), 1, ?_⟩⟩
      rw [ne_eq, QuotientGroup.eq_one_iff]
      simpa [Z, Subgroup.mem_subgroupOf] using hgZ
    have := hQ.center_nontrivial
    obtain ⟨⟨q, hqc⟩, hq1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Z))
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y, y.2, fun hy => hq1 ?_, fun h hh => ?_⟩
    · ext
      exact (QuotientGroup.eq_one_iff y).2 (by simpa [Z, Subgroup.mem_subgroupOf] using hy)
    · have hc := Subgroup.mem_center_iff.1 hqc (⟨h, hh⟩ : G)
      have key : (((y * ⟨h, hh⟩ * y⁻¹ * (⟨h, hh⟩ : G)⁻¹ : G)) : G ⧸ Z) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, ← hc]
        group
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at key
      simpa using key
  have hyns : ¬ IsScalarMat (y : Matrix (Fin 2) (Fin 2) ℂ) := fun h => hyZ (mem_center_of_isScalarMat h)
  obtain ⟨v, hv0, a, hva⟩ := exists_eigen (y : Matrix (Fin 2) (Fin 2) ℂ)
  have ha0 : a ≠ 0 := eigen_ne_zero y hv0 hva
  refine ⟨v, hv0, fun h hh => ?_⟩
  obtain ⟨e, he⟩ := isScalarMat_of_mem_center (hcomm h hh)
  have hyh : (y : Matrix (Fin 2) (Fin 2) ℂ) * h = e • ((h : Matrix (Fin 2) (Fin 2) ℂ) * y) := by
    have h1 : y * h = (y * h * y⁻¹ * h⁻¹) * (h * y) := by group
    rw [← Units.val_mul, h1, Units.val_mul, IsScalarMat.mul_eq he, Units.val_mul]
  have hpow : ∀ m : ℕ, (y : Matrix (Fin 2) (Fin 2) ℂ) * ((h ^ m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      e ^ m • (((h ^ m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * y) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Units.val_mul, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hyh, mul_smul_comm,
        smul_smul, ← mul_assoc, pow_succ]
  have hev : ∀ m : ℕ, (y : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (((h ^ m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      (e ^ m * a) • (((h ^ m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := by
    intro m
    rw [mulVec_mulVec, hpow, smul_mulVec, ← mulVec_mulVec, hva, mulVec_smul, smul_smul]
  have hroot : ∀ m : ℕ, ((y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - e ^ m * a) *
      ((y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - e ^ m * a) -
      (y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 :=
    fun m => charQ_eq_zero (mulVec_ne_zero _ hv0) (hev m)
  have he0 : e ≠ 0 := by
    have := eigen_ne_zero y (mulVec_ne_zero _ hv0) (hev 1)
    rw [pow_one] at this
    exact left_ne_zero_of_mul this
  have he2 : e ^ 2 = 1 := by
    by_cases h1 : e ^ 1 * a = e ^ 0 * a
    · rw [pow_one, pow_zero, one_mul] at h1
      have : e = 1 := by
        have := mul_right_cancel₀ ha0 (h1.trans (one_mul a).symm)
        exact this
      simp [this]
    · rcases eq_or_eq_of_charQ h1 (hroot 1) (hroot 0) (hroot 2) with h2 | h2
      · exfalso
        apply h1
        have : e ^ 2 = e ^ 1 := mul_right_cancel₀ ha0 h2
        rw [pow_two, pow_one] at this
        have : e = 1 := by
          have := mul_left_cancel₀ he0 (this.trans (mul_one e).symm)
          exact this
        simp [this]
      · rw [pow_zero, one_mul] at h2
        exact mul_right_cancel₀ ha0 (h2.trans (one_mul a).symm)
  obtain ⟨k, hk⟩ := hG ⟨h, hh⟩
  have hk' : h ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hek : e ^ p ^ k = 1 := by
    have h1 := hev (p ^ k)
    rw [hk', Units.val_one, one_mulVec, hva] at h1
    have h2 : a = e ^ p ^ k * a := smul_left_injective ℂ hv0 h1
    exact (mul_right_cancel₀ ha0 ((one_mul a).trans h2)).symm
  have he1 : e = 1 := by
    obtain ⟨j, hj⟩ := (hp.out.odd_of_ne_two hp2).pow (n := k)
    rw [hj, pow_succ, pow_mul, he2, one_pow, one_mul] at hek
    exact hek
  rw [he1, one_smul] at hyh
  have hyv : (y : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      a • ((h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := by
    rw [mulVec_mulVec, hyh, ← mulVec_mulVec, hva, mulVec_smul]
  by_contra hne
  apply hyns
  refine ⟨a, mulVec_eq_smul_of_gtpDet_ne_zero (x := v) (y := (h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)
    (fun hd => hne (exists_eq_smul_of_gtpDet_eq_zero hv0 hd)) hva hyv⟩

/-- The determinant changes sign when the two vectors are swapped. -/
theorem gtpDet_swap (x y : Fin 2 → ℂ) : gtpDet x y = -gtpDet y x := by
  simp [gtpDet]; ring

/-- For $x \ne 0$ there is a vector $y$ with $\det(x, y) \ne 0$. -/
theorem exists_gtpDet_ne_zero {x : Fin 2 → ℂ} (hx : x ≠ 0) : ∃ y, gtpDet x y ≠ 0 := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := fun h1 => hx (by ext i; fin_cases i <;> simp [h0, h1])
    exact ⟨Pi.single 0 1, by simp [gtpDet, h1]⟩
  · exact ⟨Pi.single 1 1, by simp [gtpDet, h0]⟩

/-- If $u \ne 0$ and both $x$ and $y$ are multiples of $u$, then $\det(x, y) = 0$. -/
theorem gtpDet_eq_zero_of_gtpDet_eq_zero {u x y : Fin 2 → ℂ} (hu : u ≠ 0) (hx : gtpDet u x = 0)
    (hy : gtpDet u y = 0) : gtpDet x y = 0 := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_gtpDet_eq_zero hu hx
  obtain ⟨d, rfl⟩ := exists_eq_smul_of_gtpDet_eq_zero hu hy
  simp

section Clifford

variable {W : Type*} [Group W]

/-- The stabilizer in $W$ of the line $\mathbb{C} v$ under a representation $\rho$. -/
def lineStab (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) : Subgroup W where
  carrier := {g | ∃ c : ℂ, (ρ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [map_mul, Units.val_mul, ← mulVec_mulVec, hd, mulVec_smul, hc, smul_smul]⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    have hc0 : c ≠ 0 := eigen_ne_zero _ hv hc
    have h1 : (ρ a⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((ρ a : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        one_mulVec]
    rw [hc, mulVec_smul] at h1
    refine ⟨c⁻¹, ?_⟩
    calc (ρ a⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
        = c⁻¹ • (c • (ρ a⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • v := by rw [h1]

/-- An element $g$ stabilizes the line $\mathbb{C} v$ if and only if $\det(v, \rho(g) v) = 0$. -/
theorem mem_lineStab_iff (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) (g : W) :
    g ∈ lineStab ρ hv ↔ gtpDet v ((ρ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) = 0 :=
  ⟨fun ⟨_, hc⟩ => gtpDet_eq_zero_of_eq_smul hc, fun h => exists_eq_smul_of_gtpDet_eq_zero hv h⟩

/-- The value of the character of `lineStab` at $h$: the eigenvalue of $\rho(h)$ on $v$. -/
noncomputable def lineCharFun (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (h : lineStab ρ hv) : ℂ :=
  h.2.choose

theorem lineCharFun_spec (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (h : lineStab ρ hv) :
    (ρ h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = lineCharFun ρ hv h • v :=
  h.2.choose_spec

theorem lineCharFun_eq (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (h : lineStab ρ hv) {c : ℂ} (hc : (ρ h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v) :
    lineCharFun ρ hv h = c :=
  smul_left_injective ℂ hv ((lineCharFun_spec ρ hv h).symm.trans hc)

/-- The character of `lineStab` by which it acts on the line $\mathbb{C} v$. -/
noncomputable def lineChar (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    lineStab ρ hv →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := lineCharFun ρ hv
      map_one' := lineCharFun_eq ρ hv 1 (by simp)
      map_mul' := fun a b => lineCharFun_eq ρ hv (a * b) (by
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, ← mulVec_mulVec, lineCharFun_spec,
          mulVec_smul, lineCharFun_spec, smul_smul, mul_comm]) }

/-- The subgroup `lineStab` acts on $v$ by the character `lineChar`. -/
theorem lineChar_spec (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) (h : lineStab ρ hv) :
    (ρ h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (lineChar ρ hv h : ℂ) • v :=
  lineCharFun_spec ρ hv h

/-- The kernel of $\rho$ lies in `lineStab`. -/
theorem ker_le_lineStab (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ρ.ker ≤ lineStab ρ hv :=
  fun g hg => ⟨1, by rw [MonoidHom.mem_ker.1 hg]; simp⟩

/-- If $\rho$ is irreducible, then `lineStab` is not all of $W$. -/
theorem exists_notMem_lineStab {ρ : W →* GL (Fin 2) ℂ} (hρ : IsIrreducibleRep ρ)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) : ∃ s, s ∉ lineStab ρ hv := by
  by_contra hall
  push Not at hall
  set V : Submodule ℂ (Fin 2 → ℂ) := Submodule.span ℂ {v}
  have hst : ∀ w, V ≤ V.comap (Matrix.toLin' (ρ w : Matrix (Fin 2) (Fin 2) ℂ)) := by
    intro w x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨c, hc⟩ := hall w
    rw [Submodule.mem_comap, Matrix.toLin'_apply, mulVec_smul, hc, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨a * c, rfl⟩
  rcases hρ.2 V hst with h | h
  · exact hv (Submodule.span_singleton_eq_bot.1 h)
  · obtain ⟨y, hy⟩ := exists_gtpDet_ne_zero hv
    have : y ∈ V := h ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 this
    exact hy (by simp)

/-- The product rule $\rho(x) (\rho(y) z) = \rho(x y) z$. -/
theorem rho_mulVec_mulVec (ρ : W →* GL (Fin 2) ℂ) (x y : W) (z : Fin 2 → ℂ) :
    (ρ x : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((ρ y : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) =
      (ρ (x * y) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z := by
  rw [map_mul, Units.val_mul, mulVec_mulVec]

/-- If $v$ is an eigenvector of $\rho(s^{-1} n s)$, then $\rho(s) v$ is an eigenvector of $\rho(n)$ with the same eigenvalue. -/
theorem conj_eigen (ρ : W →* GL (Fin 2) ℂ) {n s : W} {c : ℂ} {v : Fin 2 → ℂ}
    (h : (ρ (s⁻¹ * n * s) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v) :
    (ρ n : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      c • ((ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := by
  rw [rho_mulVec_mulVec, show n * s = s * (s⁻¹ * n * s) by group, ← rho_mulVec_mulVec, h,
    mulVec_smul]

/-- If $\rho(n_0)$ is not scalar, $\rho(n_0) v = a v$, $s$ does not stabilize the line $\mathbb{C} v$, and $\rho(s^{-1} n_0 s) v = b v$, then $b \ne a$. -/
theorem eigen_conj_ne (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) {n₀ s : W}
    (hns : ¬ IsScalarMat (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ)) (hs : s ∉ lineStab ρ hv) {a b : ℂ}
    (ha : (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = a • v)
    (hb : (ρ (s⁻¹ * n₀ * s) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = b • v) : b ≠ a := by
  rintro rfl
  have h3 := conj_eigen ρ hb
  have hd : gtpDet v ((ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) ≠ 0 :=
    fun h => hs ((mem_lineStab_iff ρ hv s).2 h)
  exact hns ⟨_, mulVec_eq_smul_of_gtpDet_ne_zero hd ha h3⟩

/-- An element with scalar image stabilizes each line. -/
theorem mem_lineStab_of_isScalarMat (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) {g : W}
    (hg : IsScalarMat (ρ g : Matrix (Fin 2) (Fin 2) ℂ)) : g ∈ lineStab ρ hv := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, hc v⟩

/-- Let $\rho(n_0)$ be not scalar with eigenvector $v$. If $\rho(g)$ commutes with $\rho(n_0)$, then $g$ stabilizes the line $\mathbb{C} v$. -/
theorem mem_lineStab_of_commute (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) {n₀ g : W}
    (hns : ¬ IsScalarMat (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ)) {a : ℂ}
    (ha : (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = a • v)
    (hc : (ρ g : Matrix (Fin 2) (Fin 2) ℂ) * ρ n₀ = (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ) * ρ g) :
    g ∈ lineStab ρ hv := by
  rw [mem_lineStab_iff]
  by_contra hd
  apply hns
  refine ⟨a, mulVec_eq_smul_of_gtpDet_ne_zero hd ha ?_⟩
  rw [mulVec_mulVec, ← hc, ← mulVec_mulVec, ha, mulVec_smul]

/-- Let $H$ be a subgroup of index $2$ in the stabilizer of a line. If some element does not stabilize the line, then the stabilizer is $H$. -/
theorem lineStab_eq_of_le (ρ : W →* GL (Fin 2) ℂ) {v : Fin 2 → ℂ} (hv : v ≠ 0) {H : Subgroup W}
    (hH : H.index = 2) (hle : H ≤ lineStab ρ hv) {s : W} (hs : s ∉ lineStab ρ hv) :
    lineStab ρ hv = H := by
  refine le_antisymm (fun g hg => ?_) hle
  by_contra hgH
  have hsH : s ∉ H := fun h => hs (hle h)
  have hsg : s * g ∈ H := (mul_s_mem_iff hH hgH s).2 hsH
  apply hs
  simpa using (lineStab ρ hv).mul_mem (hle hsg) ((lineStab ρ hv).inv_mem hg)

/-- Multiplication by an invertible matrix is injective on $\mathbb{C}^2$. -/
theorem gl_mulVec_injective (g : GL (Fin 2) ℂ) :
    Function.Injective ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ·) := by
  intro x y h
  have h1 := congrArg (((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ·) h
  simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h1
  exact h1

/-- The conjugate $g h g^{-1}$ acts on $g x$ as $h$ acts on $x$. -/
theorem conj_mulVec (g h : GL (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    ((g * h * g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) := by
  rw [mulVec_mulVec, ← Units.val_mul, show g * h * g⁻¹ * g = g * h by group, Units.val_mul,
    mulVec_mulVec]

/-- The line stabilizers of isomorphic representations agree: if $\rho'(w) = g \rho(w) g^{-1}$, then the stabilizer of $\mathbb{C} g v$ under $\rho'$ is the stabilizer of $\mathbb{C} v$ under $\rho$. -/
theorem lineStab_conj {ρ ρ' : W →* GL (Fin 2) ℂ} (g : GL (Fin 2) ℂ) (hρ : ∀ w, ρ' w = g * ρ w * g⁻¹)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) (hgv : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v ≠ 0) :
    lineStab ρ' hgv = lineStab ρ hv := by
  ext w
  change (∃ c : ℂ, _ = _) ↔ ∃ c : ℂ, _ = _
  simp only [hρ, conj_mulVec, ← mulVec_smul]
  exact exists_congr fun c => (gl_mulVec_injective g).eq_iff

/-- A conjugate of a matrix is scalar exactly when the matrix is scalar. -/
theorem isScalarMat_conj_iff (g h : GL (Fin 2) ℂ) :
    IsScalarMat ((g * h * g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ↔
      IsScalarMat (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · intro H
    have := (Subgroup.center (GL (Fin 2) ℂ)).normal_of_characteristic
    refine isScalarMat_of_mem_center ?_
    simpa [mul_assoc] using this.conj_mem _ (mem_center_of_isScalarMat H) g⁻¹
  · intro H
    have := (Subgroup.center (GL (Fin 2) ℂ)).normal_of_characteristic
    exact isScalarMat_of_mem_center (this.conj_mem _ (mem_center_of_isScalarMat H) g)

/-- A diagonal matrix is scalar exactly when its two diagonal entries are equal. -/
theorem isScalarMat_diagonal_iff (a b : ℂ) : IsScalarMat (diagonal ![a, b]) ↔ b = a := by
  constructor
  · rintro ⟨c, hc⟩
    have h0 := congrFun (hc (Pi.single 0 1)) 0
    have h1 := congrFun (hc (Pi.single 1 1)) 1
    simp [mulVec_diagonal] at h0 h1
    rw [h0, h1]
  · rintro rfl
    refine ⟨b, fun x => ?_⟩
    ext i
    fin_cases i <;> simp [mulVec_diagonal]

section Induced

variable {H : Subgroup W} (hH : H.index = 2) {s : W} (hs : s ∉ H) {φ : H →* ℂˣ}

include hH in
/-- Let $\rho = \mathrm{Ind}_H^W \varphi$ be irreducible and let $n_0 \in H$ with $\varphi^s(n_0) \ne \varphi(n_0)$. Then the stabilizer of each eigenline of $\rho(n_0)$ is $H$. -/
theorem lineStab_ind_eq (hirr : IsIrreducibleRep (ind hH hs φ)) {n₀ : H}
    (hn₀ : conjChar hH s φ n₀ ≠ φ n₀) {u : Fin 2 → ℂ} (hu : u ≠ 0) {a : ℂ}
    (ha : (ind hH hs φ n₀ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u = a • u) :
    lineStab (ind hH hs φ) hu = H := by
  have hns : ¬ IsScalarMat (ind hH hs φ n₀ : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [ind_apply_of_mem, isScalarMat_diagonal_iff]
    exact fun h => hn₀ (Units.ext h)
  obtain ⟨t, ht⟩ := exists_notMem_lineStab hirr hu
  refine lineStab_eq_of_le _ hu hH (fun h hh => ?_) ht
  refine mem_lineStab_of_commute _ hu hns ha ?_
  change (ind hH hs φ (⟨h, hh⟩ : H) : Matrix (Fin 2) (Fin 2) ℂ) * _ = _
  rw [ind_apply_of_mem, ind_apply_of_mem, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Induced

variable {ρ : W →* GL (Fin 2) ℂ} {N : Subgroup W} [N.Normal] {v : Fin 2 → ℂ} (hv : v ≠ 0)
  (heig : ∀ n ∈ N, ∃ c : ℂ, (ρ n : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v)

include heig in
/-- Each translate $\rho(g) v$ is again an eigenvector of each element of the normal subgroup $N$. -/
theorem eigen_translate (g : W) {n : W} (hn : n ∈ N) :
    ∃ c : ℂ, (ρ n : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      c • ((ρ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := by
  obtain ⟨c, hc⟩ := heig (g⁻¹ * n * g) (by simpa using (inferInstance : N.Normal).conj_mem n hn g⁻¹)
  exact ⟨c, conj_eigen ρ hc⟩

omit [N.Normal] in
include heig in
/-- The normal subgroup $N$ lies in `lineStab`. -/
theorem le_lineStab : N ≤ lineStab ρ hv := fun n hn => heig n hn

include heig in
/-- **Clifford theory in dimension $2$.** Let $\rho$ be an irreducible $2$-dimensional representation of $W$ and let $N$ be a normal subgroup with a common eigenvector $v$. If some element of $N$ is not scalar, then the stabilizer of the line $\mathbb{C} v$ has index $2$. -/
theorem index_lineStab (hρ : IsIrreducibleRep ρ) {n₀ : W} (hn₀ : n₀ ∈ N)
    (hns : ¬ IsScalarMat (ρ n₀ : Matrix (Fin 2) (Fin 2) ℂ)) : (lineStab ρ hv).index = 2 := by
  obtain ⟨s, hs⟩ := exists_notMem_lineStab hρ hv
  set w := (ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
  have hw : w ≠ 0 := mulVec_ne_zero _ hv
  have hd : gtpDet v w ≠ 0 := fun h => hs ((mem_lineStab_iff ρ hv s).2 h)
  obtain ⟨a, ha⟩ := heig n₀ hn₀
  obtain ⟨b, hb⟩ := eigen_translate heig s hn₀
  have hab : a ≠ b := by
    rintro rfl
    exact hns ⟨a, mulVec_eq_smul_of_gtpDet_ne_zero hd ha hb⟩
  rw [Subgroup.index_eq_two_iff']
  refine ⟨s⁻¹, fun g => ?_⟩
  set u := (ρ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
  have hu : u ≠ 0 := mulVec_ne_zero _ hv
  have hsg : s⁻¹ * g ∈ lineStab ρ hv ↔ gtpDet w u = 0 := by
    constructor
    · rintro ⟨c, hc⟩
      have : u = c • w := by
        have h1 := congrArg ((ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ·) hc
        simp only [rho_mulVec_mulVec, mul_inv_cancel_left, mulVec_smul] at h1
        exact h1
      rw [this]
      simp
    · intro h
      obtain ⟨c, hc⟩ := exists_eq_smul_of_gtpDet_eq_zero hw h
      refine ⟨c, ?_⟩
      rw [← rho_mulVec_mulVec]
      change (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u = c • v
      rw [hc, mulVec_smul, rho_mulVec_mulVec, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  rw [hsg, mem_lineStab_iff]
  obtain ⟨c, hc⟩ := eigen_translate heig g hn₀
  have hor := gtpDet_eq_zero_or_of_eigen hd hab ha hb hc
  rw [gtpDet_swap u w, neg_eq_zero] at hor
  have hnot : ¬ (gtpDet w u = 0 ∧ gtpDet v u = 0) := by
    rintro ⟨h1, h2⟩
    apply hd
    rw [gtpDet_swap] at h1 h2
    exact gtpDet_eq_zero_of_gtpDet_eq_zero hu (neg_eq_zero.1 h2) (neg_eq_zero.1 h1)
  rcases hor with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

end Clifford

section Weil

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt Langlands.LocalField ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The wild inertia subgroup $P_K$ of $W_K$: the normal subgroup generated by the elements $w$ of $I_K$ with $w(x) / x \equiv 1 \bmod \bar{\mathfrak{m}}$ for each nonzero $x$ in the integral closure $\bar{\mathcal{O}}$ of $\mathcal{O}_K$ in $\bar K$. The condition is $w(x) - x \in \bar{\mathfrak{m}} x$ for each $x \in \bar{\mathcal{O}}$. These elements already form a normal subgroup, and each of them is in $I_K$ (Serre, Local fields, Chapter IV, Section 2, Proposition 7). -/
noncomputable def wildInertia : Subgroup (WeilGroup K) :=
  Subgroup.normalClosure
    {w | w ∈ inertia K ∧ ∀ x : integers K, ∃ m ∈ prime K,
      (toGalois K w : Field.absoluteGaloisGroup K) • (x : AlgebraicClosure K) - x = m * x}

/-- The wild inertia subgroup lies in the inertia subgroup. -/
theorem wildInertia_le_inertia : wildInertia K ≤ inertia K := by
  have : (inertia K).Normal := MonoidHom.normal_ker (toResidue K)
  exact Subgroup.normalClosure_le_normal fun w hw => hw.1

/-- **The wild inertia subgroup is a pro-$p$ group** (Serre, Local fields, Chapter IV, Section 2, Corollary 3 to Proposition 7, applied to each finite Galois extension). Let $p$ be the residue characteristic. For each open normal subgroup $U$ of $W_K$ and each $x \in P_K$, some power $x^{p^k}$ lies in $U$. -/
def WildInertiaProP : Prop :=
  ∀ U : Subgroup (WeilGroup K), IsOpen (U : Set (WeilGroup K)) → U.Normal →
    ∀ x ∈ wildInertia K, ∃ k : ℕ, x ^ ringChar 𝓀[K] ^ k ∈ U

/-- **The tame inertia group is procyclic** (Serre, Local fields, Chapter IV, Section 2, Corollary 1 to Proposition 7; Iwasawa, On Galois groups of local fields). The quotient $I_K / P_K$ is isomorphic to $\prod_{\ell \ne p} \mathbb{Z}_\ell(1)$, so it has a topological generator. In terms of $W_K$: there is $t \in I_K$ such that for each open subgroup $U$ and each $i \in I_K$, the element $i$ lies in $n t^k U$ for some $n \in P_K$ and $k \in \mathbb{Z}$. -/
def TameInertiaProcyclic : Prop :=
  ∃ t ∈ inertia K, ∀ U : Subgroup (WeilGroup K), IsOpen (U : Set (WeilGroup K)) →
    ∀ i ∈ inertia K, ∃ n ∈ wildInertia K, ∃ k : ℤ, (n * t ^ k)⁻¹ * i ∈ U

/-- **Open subgroups of index $2$** (Tate, Number theoretic background, Section 1.4; Weil, Sur la theorie du corps de classes). Each open subgroup of index $2$ of $W_K$ is the Weil group $W_L$ of a quadratic separable extension $L$ of $K$ inside $\bar K$. -/
def OpenIndexTwoQuad : Prop :=
  ∀ H : Subgroup (WeilGroup K), IsOpen (H : Set (WeilGroup K)) → H.index = 2 →
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L), restrictSubgroup K L = H

/-- **The inertia group and unramified extensions** (Serre, Local fields, Chapter IV, Section 1, and Chapter III, Section 5). If the Weil group $W_L$ of a quadratic separable extension $L$ contains the inertia group $I_K$, then $L / K$ is unramified. -/
def InertiaUnramified : Prop :=
  ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L], inertia K ≤ restrictSubgroup K L → IsUnramifiedExt K L

/-- **Uniqueness of the unramified quadratic extension** (Serre, Local fields, Chapter III, Section 5, Theorem 2 and its corollary). Two unramified quadratic separable extensions of $K$ inside $\bar K$ are equal. -/
def UniqueUnramifiedQuad : Prop :=
  ∀ (L L' : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] [Algebra.IsQuadraticExtension K L'] [Algebra.IsSeparable K L'],
    IsUnramifiedExt K L → IsUnramifiedExt K L' → L = L'

/-- **The Artin map on the principal units** (Serre, Local fields, Chapter XV, Section 2, Theorem 2, with the Hasse-Arf theorem of Chapter V, Section 7). Let $L$ be a quadratic separable extension of $K$ inside $\bar K$ and let $\mathrm{art}_L$ be a local Artin map. Then $\mathrm{art}_L(U^1_L)$ is the image in $W_L^{ab}$ of the wild inertia subgroup $W_L \cap P_K = P_L$. -/
def WildArtinUnits : Prop :=
  ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] (art : Lˣ ≃ₜ* WeilGroup.Ab L), IsLocalArtinMap L art →
    ∀ x : Lˣ, x ∈ unitFilt L 1 ↔ ∃ h : restrictSubgroup K L,
      (h : WeilGroup K) ∈ wildInertia K ∧ art.symm (toAbSub K L h) = x

/-- **Characters of $U^1_L$ invariant under conjugation** (a standard consequence of the structure of $U^1_L$). Let $p \ne 2$, let $L$ be a quadratic separable extension of $K$ with conjugation $\sigma$, and let $\xi$ be a character of $L^\times$ with $\xi(\sigma u) = \xi(u)$ for $u \in U^1_L$. Then $\xi$ on $U^1_L$ factors through the norm $N_{L/K}$. Proof: $U^1_L$ is a pro-$p$ group, so for $p \ne 2$ each $u \in U^1_L$ has a unique square root in $U^1_L$. Then $u = (u \sigma(u))^{1/2} (u / \sigma(u))^{1/2}$, the character $\xi$ is trivial on $(u / \sigma(u))^{1/2} = w / \sigma(w)$ with $w = u^{1/2}$, and $y \mapsto \xi(y^{1/2})$ on $U^1_K$ extends to $K^\times$ since $\mathbb{C}^\times$ is divisible. -/
def NormFactorU1 : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (L : IntermediateField K (AlgebraicClosure K))
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] (ξ : Lˣ →* ℂˣ),
    (∀ u ∈ unitFilt L 1, ξ (galConjUnits K L u) = ξ u) →
      ∃ φ : Kˣ →* ℂˣ, ∀ u ∈ unitFilt L 1, ξ u = φ (normUnits K L u)

/-- The published inputs for `Langlands.LocalGL2.GaloisTameParametrization`, for one field $K$. -/
structure GaloisTameInputs : Prop where
  /-- The local Artin maps of quadratic extensions are compatible with conjugation. -/
  conj : ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L], ArtinConjCompat K L
  /-- The wild inertia subgroup is a pro-$p$ group. -/
  wild : WildInertiaProP K
  /-- The tame inertia group is procyclic. -/
  tame : TameInertiaProcyclic K
  /-- Each open subgroup of index $2$ is the Weil group of a quadratic extension. -/
  indexTwo : OpenIndexTwoQuad K
  /-- A quadratic extension whose Weil group contains the inertia group is unramified. -/
  unram : InertiaUnramified K
  /-- There is at most one unramified quadratic extension. -/
  uniqueUnram : UniqueUnramifiedQuad K
  /-- The Artin map sends the principal units to the image of the wild inertia subgroup. -/
  wildArtin : WildArtinUnits K
  /-- A conjugation invariant character of $U^1_L$ factors through the norm. -/
  normFactor : NormFactorU1 K

variable {K}

/-- The residue characteristic is a prime number. -/
theorem ringChar_residue_prime : (ringChar 𝓀[K]).Prime :=
  CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])

/-- If $2 \ne 0$ in the residue field, then the residue characteristic is not $2$. -/
theorem ringChar_residue_ne_two (h2 : (2 : 𝓀[K]) ≠ 0) : ringChar 𝓀[K] ≠ 2 := by
  intro h
  apply h2
  have := (ringChar.spec 𝓀[K] 2).2 (by rw [h])
  exact_mod_cast this

/-- Let $H$ be a subgroup of index $2$ and $n$ an odd number. If $x^n \in H$, then $x \in H$. -/
theorem mem_of_pow_mem_of_index_two {W : Type*} [Group W] {H : Subgroup W} (hH : H.index = 2)
    {x : W} {n : ℕ} (hn : Odd n) (hx : x ^ n ∈ H) : x ∈ H := by
  obtain ⟨j, rfl⟩ := hn
  have h2 : x ^ 2 ∈ H := by
    by_cases hxH : x ∈ H
    · exact H.pow_mem hxH 2
    · rw [pow_two]
      exact (mul_s_mem_iff hH hxH x).2 hxH
  rw [pow_succ, pow_mul] at hx
  exact (H.mul_mem_cancel_left (H.pow_mem h2 j)).1 hx

/-- For $p \ne 2$, the wild inertia subgroup lies in the Weil group $W_L$ of each quadratic separable extension $L$. -/
theorem wildInertia_le_restrictSubgroup (hP : WildInertiaProP K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] : wildInertia K ≤ restrictSubgroup K L := by
  intro x hx
  have := Subgroup.normal_of_index_eq_two (index_restrictSubgroup_quad (F := K) (L := L))
  obtain ⟨k, hk⟩ := hP _ (isOpen_restrictSubgroup K L) inferInstance x hx
  exact mem_of_pow_mem_of_index_two index_restrictSubgroup_quad
    (((ringChar_residue_prime (K := K)).odd_of_ne_two (ringChar_residue_ne_two h2)).pow) hk

/-- A representation of $W_K$ with open kernel has finite image on the inertia group, since $I_K$ is compact. -/
theorem finite_map_inertia (ρ : WeilGroup K →* GL (Fin 2) ℂ) (hρ : IsOpen (ρ.ker : Set (WeilGroup K))) :
    Finite ((inertia K).map ρ) := by
  have : DiscreteTopology (WeilGroup K ⧸ ρ.ker) := QuotientGroup.discreteTopology hρ
  have hfin : ((QuotientGroup.mk : WeilGroup K → WeilGroup K ⧸ ρ.ker) ''
      (inertia K : Set (WeilGroup K))).Finite :=
    ((isCompact_inertia K).image QuotientGroup.continuous_mk).finite_of_discrete
  have heq : ((inertia K).map ρ : Set (GL (Fin 2) ℂ)) =
      QuotientGroup.kerLift ρ '' ((QuotientGroup.mk : WeilGroup K → WeilGroup K ⧸ ρ.ker) ''
        (inertia K : Set (WeilGroup K))) := by
    rw [Set.image_image, Subgroup.coe_map]
    rfl
  exact Set.Finite.to_subtype (heq ▸ hfin.image _)

/-- For $p \ne 2$, the wild inertia subgroup has a common eigenvector in each representation of $W_K$ of dimension $2$ with open kernel. -/
theorem exists_wildInertia_eigen (hP : WildInertiaProP K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (ρ : WeilGroup K →* GL (Fin 2) ℂ) (hρ : IsOpen (ρ.ker : Set (WeilGroup K))) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∀ n ∈ wildInertia K,
      ∃ c : ℂ, (ρ n : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨ringChar_residue_prime⟩
  have := finite_map_inertia ρ hρ
  have : Finite ((wildInertia K).map ρ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (Subgroup.map_mono (f := ρ) (wildInertia_le_inertia K)))
  have hG : IsPGroup (ringChar 𝓀[K]) ((wildInertia K).map ρ) := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨k, hk⟩ := hP ρ.ker hρ (MonoidHom.normal_ker ρ) x hx
    refine ⟨k, Subtype.ext ?_⟩
    simpa [← map_pow] using hk
  obtain ⟨v, hv, h⟩ := exists_common_eigen_of_isPGroup (ringChar_residue_ne_two h2) _ hG
  exact ⟨v, hv, fun n hn => h _ (Subgroup.mem_map_of_mem ρ hn)⟩

/-- An irreducible Weil-Deligne representation has monodromy $0$, and its representation part is irreducible. -/
theorem WeilDeligneRep.N_eq_zero_and_of_isIrreducible {m : ℕ} (ρ : WeilDeligneRep K m)
    (hρ : ρ.IsIrreducible) : ρ.N = 0 ∧ IsIrreducibleRep ρ.r := by
  set V : Submodule ℂ (Fin m → ℂ) := LinearMap.ker (Matrix.toLin' ρ.N) with hVdef
  have hst : ∀ w, V ≤ V.comap (Matrix.toLin' (ρ.r w : Matrix (Fin m) (Fin m) ℂ)) := by
    intro w v hv
    simp only [V, Submodule.mem_comap, LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    have h := ρ.conj w⁻¹
    have hinv : (((ρ.r w⁻¹)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = ρ.r w := by
      rw [← map_inv, inv_inv]
    rw [hinv] at h
    have h2 : ρ.N * (ρ.r w : Matrix (Fin m) (Fin m) ℂ) =
        (ρ.r w : Matrix (Fin m) (Fin m) ℂ) * (weilNorm K w⁻¹ • ρ.N) := by
      rw [← h, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
        Units.val_one, one_mul]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hv, smul_zero,
      Matrix.mulVec_zero]
  have hN : V ≤ V.comap (Matrix.toLin' ρ.N) := by
    intro v hv
    simp only [V, Submodule.mem_comap, LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [hv, Matrix.mulVec_zero]
  have hN0 : ρ.N = 0 := by
    rcases hρ.2 V hst hN with hV | hV
    · exfalso
      have : NeZero m := ⟨hρ.1.ne'⟩
      have hnil : IsNilpotent (Matrix.toLinAlgEquiv' ρ.N) := ρ.isNilpotent.map _
      exact hnil.not_isUnit ((LinearMap.isUnit_iff_ker_eq_bot _).2 hV)
    · exact Matrix.toLin'.injective ((LinearMap.ker_eq_top.1 hV).trans (map_zero _).symm)
  refine ⟨hN0, hρ.1, fun W hW => hρ.2 W hW ?_⟩
  intro x _
  simp [hN0]

/-- Each character $\varphi$ of $W_L$ with open kernel is $\xi_W$ for a smooth character $\xi$ of $L^\times$, with the Artin map `Langlands.LocalGL2.artOf`. -/
theorem exists_charW_eq (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    (φ : restrictSubgroup K L →* ℂˣ) (hφ : IsOpen (φ.ker : Set (restrictSubgroup K L))) :
    ∃ ξ : Lˣ →* ℂˣ, IsSmoothChar L ξ ∧ charW (F := K) (artOf L) ξ = φ := by
  set f : WeilGroup L →* ℂˣ := φ.comp (weilEquiv K L).toMulEquiv.toMonoidHom
  have hfo : IsOpen (f.ker : Set (WeilGroup L)) := hφ.preimage (weilEquiv K L).continuous
  have hfc : IsClosed (f.ker : Set (WeilGroup L)) := Subgroup.isClosed_of_isOpen _ hfo
  set ψ : WeilGroup.Ab L →* ℂˣ := QuotientGroup.lift _ f
    (Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker f) hfc)
  have hψ : IsOpen (ψ.ker : Set (WeilGroup.Ab L)) := by
    have : (ψ.ker : Set (WeilGroup.Ab L)) = QuotientGroup.mk '' (f.ker : Set (WeilGroup L)) := by
      ext y
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
      constructor
      · intro hy
        exact ⟨w, hy, rfl⟩
      · rintro ⟨w', hw', he⟩
        change ψ (QuotientGroup.mk w) = 1
        rw [← he]
        exact hw'
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ hfo
  refine ⟨ψ.comp (artOf L).toMulEquiv.toMonoidHom, hψ.preimage (artOf L).continuous, ?_⟩
  ext1 h
  obtain ⟨w, rfl⟩ := (weilEquiv K L).surjective h
  rw [charW_apply, toAbSub_weilEquiv]
  change ψ ((artOf L) ((artOf L).symm _)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

end Weil

section Main

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt Langlands.LocalField ValuativeRel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Two quadratic separable extensions of $K$ inside $\bar K$ with the same Weil group are equal. -/
theorem eq_of_restrictSubgroup_eq {L L' : IntermediateField K (AlgebraicClosure K)}
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
    [Algebra.IsQuadraticExtension K L'] [Algebra.IsSeparable K L']
    (h : restrictSubgroup K L = restrictSubgroup K L') : L = L' := by
  have key : ∀ (M M' : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K M]
      [Algebra.IsSeparable K M] [Algebra.IsQuadraticExtension K M'] [Algebra.IsSeparable K M'],
      restrictSubgroup K M = restrictSubgroup K M' → M' ≤ M := by
    intro M M' _ _ _ _ hM
    have hs : restrictSubgroup K (M ⊔ M') = restrictSubgroup K M := by
      have h1 : restrictSubgroup K (M ⊔ M') = restrictSubgroup K M ⊓ restrictSubgroup K M' := by
        change Subgroup.comap _ _ = Subgroup.comap _ _ ⊓ Subgroup.comap _ _
        rw [IntermediateField.fixingSubgroup_sup]
        ext w
        exact Iff.rfl
      rw [h1, ← hM, inf_idem]
    have hf : Module.finrank K M = Module.finrank K (M ⊔ M' : IntermediateField K _) := by
      rw [← index_restrictSubgroup, ← index_restrictSubgroup, hs]
    rw [IntermediateField.eq_of_le_of_finrank_eq (le_sup_left : M ≤ M ⊔ M') hf]
    exact le_sup_right
  exact le_antisymm (key L' L h.symm) (key L L' h)

/-- **Clifford theory for $W_K$.** Let $\rho$ be a Weil-Deligne representation of dimension $2$ whose representation part is irreducible. Let $N$ be a normal subgroup of $W_K$ with a common eigenvector $v$, and let $n_0 \in N$ have a non-scalar image. Then $\rho \cong \sigma(L, \xi)$ for a pair $(L, \xi)$ with $W_L$ the stabilizer of the line $\mathbb{C} v$. The hypothesis `hU` gives the last condition of admissibility. -/
theorem exists_tamePair_of_line (I : GaloisTameInputs K) (ρ : WeilDeligneRep K 2)
    (hirr : IsIrreducibleRep ρ.r) {N : Subgroup (WeilGroup K)} [N.Normal] {v : Fin 2 → ℂ}
    (hv : v ≠ 0) (heig : ∀ n ∈ N, ∃ c : ℂ, (ρ.r n : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v)
    {n₀ : WeilGroup K} (hn₀ : n₀ ∈ N) (hns : ¬ IsScalarMat (ρ.r n₀ : Matrix (Fin 2) (Fin 2) ℂ))
    (hU : ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
      [Algebra.IsSeparable K L], restrictSubgroup K L = lineStab ρ.r hv → ∀ ξ : Lˣ →* ℂˣ,
      (∀ h : restrictSubgroup K L,
        (ρ.r h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (charW (artOf L) ξ h : ℂ) • v) →
      (∃ φ : Kˣ →* ℂˣ, ∀ u ∈ unitFilt L 1, ξ u = φ (normUnits K L u)) → IsUnramifiedExt K L) :
    ∃ P : TamePair K, ∀ art : P.Lˣ ≃ₜ* WeilGroup.Ab P.L, IsLocalArtinMap P.L art →
      ρ.Iso (tameParam art P.ξ P.adm.smooth) := by
  have hidx := index_lineStab hv heig hirr hn₀ hns
  have hopen : IsOpen (lineStab ρ.r hv : Set (WeilGroup K)) :=
    Subgroup.isOpen_mono (ker_le_lineStab ρ.r hv) ρ.isOpen_ker
  obtain ⟨L, _, _, hL⟩ := I.indexTwo _ hopen hidx
  obtain ⟨φ', hφ'⟩ : ∃ φ' : restrictSubgroup K L →* ℂˣ, ∀ h : restrictSubgroup K L,
      (ρ.r h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (φ' h : ℂ) • v := by
    refine ⟨(lineChar ρ.r hv).comp (Subgroup.inclusion hL.le), fun h => ?_⟩
    have h1 := lineChar_spec ρ.r hv (Subgroup.inclusion hL.le h)
    exact h1
  have hφ'open : IsOpen (φ'.ker : Set (restrictSubgroup K L)) := by
    have hle : (ρ.r.comp (restrictSubgroup K L).subtype).ker ≤ φ'.ker := by
      intro h hh
      rw [MonoidHom.mem_ker] at hh ⊢
      have h1 := hφ' h
      rw [show ρ.r h = 1 from hh, Units.val_one, one_mulVec] at h1
      exact Units.ext (smul_left_injective ℂ hv ((one_smul ℂ v).trans h1)).symm
    exact Subgroup.isOpen_mono hle (ρ.isOpen_ker.preimage continuous_subtype_val)
  obtain ⟨ξ, hξ, hξφ⟩ := exists_charW_eq L φ' hφ'open
  have hξv : ∀ h : restrictSubgroup K L,
      (ρ.r h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (charW (artOf L) ξ h : ℂ) • v := by
    intro h
    rw [hξφ]
    exact hφ' h
  have hs := outElt_notMem (F := K) (L := L)
  have hsl : outElt K L ∉ lineStab ρ.r hv := by
    rw [← hL]
    exact hs
  have hn₀L : n₀ ∈ restrictSubgroup K L := by
    rw [hL]
    exact le_lineStab hv heig hn₀
  have hne : conjChar index_restrictSubgroup_quad (outElt K L) (charW (artOf L) ξ) ≠
      charW (artOf L) ξ := by
    intro h
    have h1 := congrArg (fun f => (f ⟨n₀, hn₀L⟩ : ℂ)) h
    simp only [conjChar_apply] at h1
    exact eigen_conj_ne ρ.r hv hns hsl (hξv ⟨n₀, hn₀L⟩)
      (hξv ⟨(outElt K L)⁻¹ * n₀ * outElt K L, conj_mem index_restrictSubgroup_quad _ hn₀L⟩) h1
  have adm : IsAdmissible K L ξ :=
    { smooth := hξ
      not_factor := by
        rintro ⟨χ, hχ⟩
        apply hne
        rw [conjChar_charW (I.conj L) (isLocalArtinMap_artOf L) hs]
        congr 1
        rw [hχ, MonoidHom.comp_assoc, normUnits_comp_galConjUnits]
      unramified_of_factor := hU L hL ξ hξv }
  refine ⟨⟨L, ξ, adm⟩, fun art hart => ?_⟩
  obtain rfl := isLocalArtinMap_unique L art (artOf L) hart (isLocalArtinMap_artOf L)
  have hiso : (tameParam (artOf L) ξ hξ).Iso ρ :=
    iso_indWD_of_eigenvector (Algebra.IsQuadraticExtension.finrank_eq_two K L) hs
      (isOpen_ker_charW (artOf L) hξ) hne ρ hv hξv
  exact (WeilDeligneRep.setoid (K := K) (m := 2)).symm hiso

/-- An irreducible representation of $W_K$ of dimension $2$ with open kernel is not scalar on the whole inertia group. If it were, the eigenline of a Frobenius element would be stable. -/
theorem not_forall_isScalarMat_inertia {ρ : WeilGroup K →* GL (Fin 2) ℂ} (hirr : IsIrreducibleRep ρ)
    (hsc : ∀ i ∈ inertia K, IsScalarMat (ρ i : Matrix (Fin 2) (Fin 2) ℂ)) : False := by
  obtain ⟨Φ, hΦ⟩ := degree_surjective K (Multiplicative.ofAdd 1)
  obtain ⟨v, hv, a, ha⟩ := exists_eigen (ρ Φ : Matrix (Fin 2) (Fin 2) ℂ)
  obtain ⟨s, hs⟩ := exists_notMem_lineStab hirr hv
  apply hs
  set k : ℤ := Multiplicative.toAdd (degree K s)
  have hi : s * Φ ^ (-k) ∈ inertia K := by
    rw [← ker_degree, MonoidHom.mem_ker, map_mul, map_zpow, hΦ]
    apply Multiplicative.toAdd.injective
    simp [k]
  have h1 := mem_lineStab_of_isScalarMat ρ hv (hsc _ hi)
  have h2 : Φ ^ k ∈ lineStab ρ hv := Subgroup.zpow_mem _ (show Φ ∈ lineStab ρ hv from ⟨a, ha⟩) k
  have h3 := Subgroup.mul_mem _ h1 h2
  rwa [_root_.zpow_neg, inv_mul_cancel_right] at h3

/-- **Part 1 of the parametrization.** For $p \ne 2$ and with the inputs, each irreducible Weil-Deligne representation of $W_K$ of dimension $2$ is $\sigma(L, \xi)$ for an admissible pair $(L, \xi)$. -/
theorem exists_tamePair_of_isIrreducible (I : GaloisTameInputs K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (ρ : WeilDeligneRep K 2) (hρ : ρ.IsIrreducible) :
    ∃ P : TamePair K, ∀ art : P.Lˣ ≃ₜ* WeilGroup.Ab P.L, IsLocalArtinMap P.L art →
      ρ.Iso (tameParam art P.ξ P.adm.smooth) := by
  have hirr := (WeilDeligneRep.N_eq_zero_and_of_isIrreducible ρ hρ).2
  by_cases hw : ∃ n₀ ∈ wildInertia K, ¬ IsScalarMat (ρ.r n₀ : Matrix (Fin 2) (Fin 2) ℂ)
  · obtain ⟨n₀, hn₀, hns⟩ := hw
    obtain ⟨v, hv, heig⟩ := exists_wildInertia_eigen I.wild h2 ρ.r ρ.isOpen_ker
    have : (wildInertia K).Normal := Subgroup.normalClosure_normal
    refine exists_tamePair_of_line I ρ hirr hv heig hn₀ hns ?_
    intro L _ _ hL ξ hξv ⟨φ, hφ⟩
    exfalso
    have hn₀L : n₀ ∈ restrictSubgroup K L := wildInertia_le_restrictSubgroup I.wild h2 L hn₀
    have hs : outElt K L ∉ lineStab ρ.r hv := by
      rw [← hL]
      exact outElt_notMem
    have hm := conj_mem index_restrictSubgroup_quad (outElt K L) hn₀L
    have hmw : (outElt K L)⁻¹ * n₀ * outElt K L ∈ wildInertia K := by
      simpa using this.conj_mem n₀ hn₀ (outElt K L)⁻¹
    have hval : ∀ h : restrictSubgroup K L, (h : WeilGroup K) ∈ wildInertia K →
        charW (artOf L) ξ h = charW (artOf L) (φ.comp (normUnits K L)) h := by
      intro h hw
      have hu := (I.wildArtin L (artOf L) (isLocalArtinMap_artOf L) _).2 ⟨h, hw, rfl⟩
      rw [charW_apply, charW_apply]
      exact hφ _ hu
    have hN : (φ.comp (normUnits K L)).comp (galConjUnits K L) = φ.comp (normUnits K L) := by
      rw [MonoidHom.comp_assoc, normUnits_comp_galConjUnits]
    have hconjN := congrArg (fun f => f ⟨n₀, hn₀L⟩)
      (conjChar_charW (I.conj L) (isLocalArtinMap_artOf L) outElt_notMem (φ.comp (normUnits K L)))
    simp only [conjChar_apply, hN] at hconjN
    have heq : charW (artOf L) ξ ⟨_, hm⟩ = charW (artOf L) ξ ⟨n₀, hn₀L⟩ := by
      rw [hval _ hmw, hval _ hn₀, hconjN]
    exact eigen_conj_ne ρ.r hv hns hs (hξv ⟨n₀, hn₀L⟩) (hξv ⟨_, hm⟩) (congrArg Units.val heq)
  push Not at hw
  obtain ⟨t, -, htU⟩ := I.tame
  obtain ⟨v, hv, a, ha⟩ := exists_eigen (ρ.r t : Matrix (Fin 2) (Fin 2) ℂ)
  have hI : inertia K ≤ lineStab ρ.r hv := by
    intro i hi
    obtain ⟨n, hn, k, hk⟩ := htU ρ.r.ker ρ.isOpen_ker i hi
    have h1 : n * t ^ k ∈ lineStab ρ.r hv :=
      Subgroup.mul_mem _ (mem_lineStab_of_isScalarMat _ hv (hw n hn))
        (Subgroup.zpow_mem _ (show t ∈ lineStab ρ.r hv from ⟨a, ha⟩) k)
    have h2 := Subgroup.mul_mem _ h1 (ker_le_lineStab ρ.r hv hk)
    rwa [mul_inv_cancel_left] at h2
  by_cases hi : ∃ i₀ ∈ inertia K, ¬ IsScalarMat (ρ.r i₀ : Matrix (Fin 2) (Fin 2) ℂ)
  · obtain ⟨i₀, hi₀, hns⟩ := hi
    have : (inertia K).Normal := MonoidHom.normal_ker _
    refine exists_tamePair_of_line I ρ hirr hv (fun n hn => hI hn) hi₀ hns ?_
    intro L _ _ hL _ _ _
    rw [← hL] at hI
    exact I.unram L hI
  push Not at hi
  exact (not_forall_isScalarMat_inertia hirr hi).elim

/-- With the inputs, if $p \ne 2$ and the image of the wild inertia group under $\sigma(L, \xi)$ is scalar, then $L / K$ is unramified. -/
theorem isUnramifiedExt_of_isScalarMat (I : GaloisTameInputs K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (P : TamePair K) (art : P.Lˣ ≃ₜ* WeilGroup.Ab P.L) (hart : IsLocalArtinMap P.L art)
    (hsc : ∀ n ∈ wildInertia K,
      IsScalarMat ((tameParam art P.ξ P.adm.smooth).r n : Matrix (Fin 2) (Fin 2) ℂ)) :
    IsUnramifiedExt K P.L := by
  refine P.adm.unramified_of_factor (I.normFactor h2 P.L P.ξ fun u hu => ?_)
  obtain ⟨h, hw, rfl⟩ := (I.wildArtin P.L art hart u).1 hu
  have h1 := hsc h hw
  rw [tameParam_r, ind_apply_of_mem, isScalarMat_diagonal_iff,
    conjChar_charW (I.conj P.L) hart outElt_notMem, charW_apply, charW_apply] at h1
  exact Units.ext h1

/-- **Part 2 of the parametrization.** For $p \ne 2$ and with the inputs, if $\sigma(P) \cong \sigma(Q)$ for two admissible pairs, then the two quadratic fields are equal. -/
theorem eq_of_tameParam_iso (I : GaloisTameInputs K) (h2 : (2 : 𝓀[K]) ≠ 0) (P Q : TamePair K)
    (artP : P.Lˣ ≃ₜ* WeilGroup.Ab P.L) (hartP : IsLocalArtinMap P.L artP)
    (artQ : Q.Lˣ ≃ₜ* WeilGroup.Ab Q.L) (hartQ : IsLocalArtinMap Q.L artQ)
    (hiso : (tameParam artP P.ξ P.adm.smooth).Iso (tameParam artQ Q.ξ Q.adm.smooth)) :
    P.L = Q.L := by
  obtain ⟨g, hg, -⟩ := hiso
  by_cases hsc : ∀ n ∈ wildInertia K,
      IsScalarMat ((tameParam artP P.ξ P.adm.smooth).r n : Matrix (Fin 2) (Fin 2) ℂ)
  · have hscQ : ∀ n ∈ wildInertia K,
        IsScalarMat ((tameParam artQ Q.ξ Q.adm.smooth).r n : Matrix (Fin 2) (Fin 2) ℂ) := by
      intro n hn
      rw [hg n, isScalarMat_conj_iff]
      exact hsc n hn
    exact I.uniqueUnram _ _ (isUnramifiedExt_of_isScalarMat I h2 P artP hartP hsc)
      (isUnramifiedExt_of_isScalarMat I h2 Q artQ hartQ hscQ)
  push Not at hsc
  obtain ⟨n₀, hn₀, hns⟩ := hsc
  have hnsQ : ¬ IsScalarMat ((tameParam artQ Q.ξ Q.adm.smooth).r n₀ : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hg n₀, isScalarMat_conj_iff]
    exact hns
  have hnP := wildInertia_le_restrictSubgroup I.wild h2 P.L hn₀
  have hnQ := wildInertia_le_restrictSubgroup I.wild h2 Q.L hn₀
  have hneP : conjChar index_restrictSubgroup_quad (outElt K P.L) (charW artP P.ξ) ⟨n₀, hnP⟩ ≠
      charW artP P.ξ ⟨n₀, hnP⟩ := by
    intro h
    apply hns
    rw [tameParam_r, ind_apply_of_mem _ _ _ ⟨n₀, hnP⟩, isScalarMat_diagonal_iff, h]
  have hneQ : conjChar index_restrictSubgroup_quad (outElt K Q.L) (charW artQ Q.ξ) ⟨n₀, hnQ⟩ ≠
      charW artQ Q.ξ ⟨n₀, hnQ⟩ := by
    intro h
    apply hnsQ
    rw [tameParam_r, ind_apply_of_mem _ _ _ ⟨n₀, hnQ⟩, isScalarMat_diagonal_iff, h]
  have hirrP : IsIrreducibleRep (ind index_restrictSubgroup_quad (outElt_notMem (F := K) (L := P.L))
      (charW artP P.ξ)) := by
    refine (isIrreducibleRep_ind_iff _ _ _).2 ?_
    rw [conjChar_charW (I.conj P.L) hartP outElt_notMem]
    exact fun h => P.adm.comp_galConjUnits_ne (charW_injective artP h)
  have hirrQ : IsIrreducibleRep (ind index_restrictSubgroup_quad (outElt_notMem (F := K) (L := Q.L))
      (charW artQ Q.ξ)) := by
    refine (isIrreducibleRep_ind_iff _ _ _).2 ?_
    rw [conjChar_charW (I.conj Q.L) hartQ outElt_notMem]
    exact fun h => Q.adm.comp_galConjUnits_ne (charW_injective artQ h)
  set e₀ : Fin 2 → ℂ := Pi.single 0 1
  have he₀ : e₀ ≠ 0 := by simp [e₀]
  have heP : (ind index_restrictSubgroup_quad (outElt_notMem (F := K) (L := P.L)) (charW artP P.ξ)
      (⟨n₀, hnP⟩ : restrictSubgroup K P.L) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e₀ =
      (charW artP P.ξ ⟨n₀, hnP⟩ : ℂ) • e₀ := by
    rw [ind_apply_of_mem]
    ext i
    fin_cases i <;> simp [e₀, mulVec_diagonal]
  have hSP := lineStab_ind_eq index_restrictSubgroup_quad _ hirrP hneP he₀ heP
  have hge₀ := mulVec_ne_zero g he₀
  have heQ : (ind index_restrictSubgroup_quad (outElt_notMem (F := K) (L := Q.L)) (charW artQ Q.ξ)
      (⟨n₀, hnQ⟩ : restrictSubgroup K Q.L) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e₀) =
      (charW artP P.ξ ⟨n₀, hnP⟩ : ℂ) • ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e₀) := by
    have h1 := hg n₀
    rw [tameParam_r, tameParam_r] at h1
    change (ind _ _ _ n₀ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ _ = _
    rw [h1, conj_mulVec]
    erw [heP]
    rw [mulVec_smul]
  have hSQ := lineStab_ind_eq index_restrictSubgroup_quad _ hirrQ hneQ hge₀ heQ
  have hc := lineStab_conj g hg he₀ hge₀
  exact eq_of_restrictSubgroup_eq (hSP.symm.trans (hc.symm.trans hSQ))

/-- **The Galois side of the tame parametrization from the inputs** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 34.1). The published inputs in `Langlands.LocalGL2.GaloisTameInputs` imply `Langlands.LocalGL2.GaloisTameParametrization`. -/
theorem galoisTameParametrization_of_inputs (I : GaloisTameInputs K) :
    GaloisTameParametrization K := fun h2 =>
  ⟨fun ρ hρ => exists_tamePair_of_isIrreducible I h2 ρ hρ,
    fun P Q artP hartP artQ hartQ hiso => eq_of_tameParam_iso I h2 P Q artP hartP artQ hartQ hiso⟩

end Main

end Langlands.LocalGL2
