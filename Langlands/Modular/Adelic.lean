/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Langlands.Modular.Hecke

/-!
# The adelic dictionary for `GL(2)` over `ℚ`

This file starts the dictionary between modular forms for $\Gamma_0(N)$ and functions on $GL_2(\mathbb{A})$, as in Volume 5, Chapter 1 of the handbook (sections 1.2 and 1.3). We model $GL_2(\mathbb{A})$ as the product $GL_2(\mathbb{R}) \times GL_2(\mathbb{A}_f)$, where $\mathbb{A}_f$ is the ring `FiniteAdeleRing ℤ ℚ` of Mathlib. The open compact subgroup $K_0(N)$ of $GL_2(\mathbb{A}_f)$ is the group of the matrices $g$ such that $g$ and $g^{-1}$ have integral entries and the lower left entry of $g$ is in $N\hat{\mathbb{Z}}$.

For a function $F$ on $\mathbb{H}$ the lift is $\phi_F(\gamma (h, 1)(1, \kappa)) = (F \|_k h)(i) = \det(h)^{1 - k/2} (F |_k h)(i)$ for $\gamma \in GL_2(\mathbb{Q})$, $\det h > 0$ and $\kappa \in K_0(N)$, and $\phi_F = 0$ at the elements without such a decomposition.

## Main definitions

* `Langlands.Modular.K0`: the subgroup $K_0(N)$ of $GL_2(\mathbb{A}_f)$.
* `Langlands.Modular.principalGL2`: the diagonal embedding of $GL_2(\mathbb{Q})$ in $GL_2(\mathbb{A})$.
* `Langlands.Modular.SL2StrongApprox`: strong approximation for $SL_2$ at level $K_0(N)$, as a `Prop`.
* `Langlands.Modular.adelicLift`: the lift $\phi_F$.
* `Langlands.Modular.adelicLiftLinear`: the lift as a linear map on $M_k(\Gamma_0(N))$.

## Main results

* `Langlands.Modular.toFinGL_mem_K0_iff`: $GL_2(\mathbb{Q}) \cap GL_2^+(\mathbb{R}) K_0(N) = \Gamma_0(N)$ (Lemma 1.2.6).
* `Langlands.Modular.exists_rat_mul_integralUnit`: class number one, $\mathbb{A}_f^\times = \mathbb{Q}_{>0} \hat{\mathbb{Z}}^\times$.
* `Langlands.Modular.exists_isDecomp`: $GL_2(\mathbb{A}) = GL_2(\mathbb{Q}) GL_2^+(\mathbb{R}) K_0(N)$, if `SL2StrongApprox N` holds (Theorem 1.2.5).
* `Langlands.Modular.principal_mul_mul_K0_iff`: two elements $h, h'$ of $GL_2^+(\mathbb{R})$ have the same double coset if and only if $h' \in \Gamma_0(N) h$ (Corollary 1.2.7).
* `Langlands.Modular.adelicLift_apply`: the lift of a modular form is well defined (Proposition 1.3.5).
* `Langlands.Modular.adelicLift_principal_mul`, `Langlands.Modular.adelicLift_mul_K0`: the lift is left invariant under $GL_2(\mathbb{Q})$ and right invariant under $K_0(N)$ (Proposition 1.3.6).
* `Langlands.Modular.adelicLift_injective`, `Langlands.Modular.adelicLiftLinear_injective`: the lift is linear and injective.

## Proof

Lemma 1.2.6 is a computation with the valuations: a rational number that is integral at all finite places is an integer. Class number one uses that each prime ideal of $\mathbb{Z}$ has a generator, so the valuations of a finite idele are those of a rational number. For Theorem 1.2.5 we write $\det g_f = q u$ with $q > 0$ rational and $u \in \hat{\mathbb{Z}}^\times$, divide by $\mathrm{diag}(q, 1)$ and $\mathrm{diag}(1, u)$, and use `SL2StrongApprox N` for the remaining element of $SL_2(\mathbb{A}_f)$. The matrix $\mathrm{diag}(-1, 1)$ makes the determinant at the infinite place positive. The lift is well defined because two decompositions differ by an element of $\Gamma_0(N)$ at the infinite place, by Lemma 1.2.6, and $f \|_k \sigma = f$ for $\sigma \in \Gamma_0(N)$. Injectivity follows from $\phi_f((h, 1)) = f(\tau)$ up to a nonzero factor for the element $h$ of $SL_2(\mathbb{R})$ with $h i = \tau$.

## What is left

* Strong approximation `SL2StrongApprox N` is a hypothesis in this file. `Langlands/Modular/StrongApprox.lean` proves it as `Langlands.Modular.sl2StrongApprox`, and gives the versions with no hypothesis `exists_isDecomp'` and `eq_adelicLift'`.
* The nebentypus character, the central character, the action of $K_\infty$, the growth conditions and the image of the lift (Sections 1.4 and 1.5) are not formalized.
* The Hecke operators $T_p$ as double coset operators and Theorem 1.6.8 are not formalized.

## References

* The langlands handbook, Volume 5, Chapter 1, sections 1.2, 1.3 and 1.6.
* S. Gelbart, Automorphic forms on adele groups, Section 3.
* D. Bump, Automorphic forms and representations, Section 3.6.
-/

namespace Langlands.Modular

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum UpperHalfPlane ModularForm
  CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The ring of finite adeles of `ℚ`. -/
abbrev FinAdele : Type := FiniteAdeleRing ℤ ℚ

local notation "𝔸f" => FinAdele

/-- A finite adele is integral if each of its components is in the ring of integers of its completion. -/
def IsIntegralAdele (x : 𝔸f) : Prop :=
  ∀ v : HeightOneSpectrum ℤ, x v ∈ v.adicCompletionIntegers ℚ

/-- The components of a product of finite adeles. -/
@[simp] lemma FinAdele.mul_apply (x y : 𝔸f) (v : HeightOneSpectrum ℤ) : (x * y) v = x v * y v := rfl
/-- The components of a sum of finite adeles. -/
@[simp] lemma FinAdele.add_apply (x y : 𝔸f) (v : HeightOneSpectrum ℤ) : (x + y) v = x v + y v := rfl
/-- The components of the negative of a finite adele. -/
@[simp] lemma FinAdele.neg_apply (x : 𝔸f) (v : HeightOneSpectrum ℤ) : (-x) v = -x v := rfl
/-- The components of a difference of finite adeles. -/
@[simp] lemma FinAdele.sub_apply (x y : 𝔸f) (v : HeightOneSpectrum ℤ) : (x - y) v = x v - y v := rfl
/-- The components of the finite adele `1`. -/
@[simp] lemma FinAdele.one_apply (v : HeightOneSpectrum ℤ) : (1 : 𝔸f) v = 1 := rfl
/-- The components of the finite adele `0`. -/
@[simp] lemma FinAdele.zero_apply (v : HeightOneSpectrum ℤ) : (0 : 𝔸f) v = 0 := rfl

/-- A product of integral adeles is integral. -/
lemma IsIntegralAdele.mul {x y : 𝔸f} (hx : IsIntegralAdele x) (hy : IsIntegralAdele y) :
    IsIntegralAdele (x * y) := fun v => by simpa using mul_mem (hx v) (hy v)

/-- A sum of integral adeles is integral. -/
lemma IsIntegralAdele.add {x y : 𝔸f} (hx : IsIntegralAdele x) (hy : IsIntegralAdele y) :
    IsIntegralAdele (x + y) := fun v => by simpa using add_mem (hx v) (hy v)

/-- The negative of an integral adele is integral. -/
lemma IsIntegralAdele.neg {x : 𝔸f} (hx : IsIntegralAdele x) : IsIntegralAdele (-x) :=
  fun v => by simpa using neg_mem (hx v)

/-- A rational number is an integral adele if and only if it is an integer. -/
lemma isIntegralAdele_algebraMap_iff (q : ℚ) :
    IsIntegralAdele (algebraMap ℚ 𝔸f q) ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_integers_of_valuation_le_one ℚ q fun v => by
      have := (mem_adicCompletionIntegers ℤ ℚ v).1 (h v)
      rwa [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation'] at this
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, rfl⟩ v
    rw [mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
      valuedAdicCompletion_eq_valuation']
    simpa using v.valuation_le_one (K := ℚ) n


/-- An integer is an integral adele. -/
lemma isIntegralAdele_intCast (n : ℤ) : IsIntegralAdele (n : 𝔸f) := by
  have := (isIntegralAdele_algebraMap_iff (n : ℚ)).2 ⟨n, rfl⟩
  simpa using this

/-- The adele `0` is integral. -/
lemma isIntegralAdele_zero : IsIntegralAdele 0 := fun _ => zero_mem _

/-- The adele `1` is integral. -/
lemma isIntegralAdele_one : IsIntegralAdele 1 := fun _ => one_mem _

/-- The entries of the identity matrix are integral adeles. -/
lemma isIntegralAdele_one_apply (i j : Fin 2) :
    IsIntegralAdele ((1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j) := by
  rw [Matrix.one_apply]
  split_ifs
  · exact isIntegralAdele_one
  · exact isIntegralAdele_zero

/-- The lower left entry of `g⁻¹` is `-g₁₀ det(g⁻¹)`. -/
lemma inv_apply_one_zero {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 =
      -((g : Matrix (Fin 2) (Fin 2) R) 1 0 * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det) := by
  set M := ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  have hM : M * (g : Matrix (Fin 2) (Fin 2) R) = 1 := by
    simp only [M]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h : M.adjugate = M.det • (g : Matrix (Fin 2) (Fin 2) R) := by
    calc M.adjugate = M.adjugate * (M * (g : Matrix (Fin 2) (Fin 2) R)) := by rw [hM, mul_one]
      _ = _ := by rw [← mul_assoc, Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  have := congrArg (fun A => A 1 0) h
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at this
  simp at this
  rw [mul_comm]; linear_combination -this

/-- The open compact subgroup `K₀(N)` of `GL(2, 𝔸f)`: the matrices `g` such that the entries of `g` and of `g⁻¹` are integral adeles, and the lower left entry of `g` is in `N Ẑ`. -/
def K0 (N : ℕ) : Subgroup (GL (Fin 2) 𝔸f) where
  carrier := {g | (∀ i j, IsIntegralAdele ((g : Matrix (Fin 2) (Fin 2) 𝔸f) i j)) ∧
    (∀ i j, IsIntegralAdele (((g⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) i j)) ∧
    ∃ c : 𝔸f, IsIntegralAdele c ∧ (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = (N : 𝔸f) * c}
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_, 0, isIntegralAdele_zero, ?_⟩
    · exact isIntegralAdele_one_apply i j
    · rw [inv_one]; exact isIntegralAdele_one_apply i j
    · rw [mul_zero, Units.val_one, Matrix.one_apply_ne (by decide)]
  mul_mem' := by
    rintro g h ⟨hg, hg', c, hc, hgc⟩ ⟨hh, hh', d, hd, hhd⟩
    have h1 : IsIntegralAdele (c * (h : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * d) := (hc.mul (hh 0 0)).add ((hg 1 1).mul hd)
    refine ⟨fun i j => ?_, fun i j => ?_, _, h1, ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact ((hg i 0).mul (hh 0 j)).add ((hg i 1).mul (hh 1 j))
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact ((hh' i 0).mul (hg' 0 j)).add ((hh' i 1).mul (hg' 1 j))
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hgc, hhd]
      ring
  inv_mem' := by
    rintro g ⟨hg, hg', c, hc, hgc⟩
    refine ⟨hg', by simpa using hg, -(c * ((g⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f).det), ?_, ?_⟩
    · rw [Matrix.det_fin_two, sub_eq_add_neg]
      exact (hc.mul (((hg' 0 0).mul (hg' 1 1)).add ((hg' 0 1).mul (hg' 1 0)).neg)).neg
    · rw [inv_apply_one_zero, hgc]
      ring


/-- The embedding of `GL(2, ℚ)` in `GL(2, 𝔸f)`. -/
noncomputable def toFinGL : GL (Fin 2) ℚ →* GL (Fin 2) 𝔸f :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ 𝔸f)

/-- The embedding of `GL(2, ℚ)` in `GL(2, ℝ)`. -/
noncomputable def toRealGL : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- The entries of the image of `γ` in `GL(2, 𝔸f)`. -/
lemma toFinGL_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (toFinGL γ : Matrix (Fin 2) (Fin 2) 𝔸f) i j = algebraMap ℚ 𝔸f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
  rfl

/-- The entries of the image of `γ` in `GL(2, ℝ)`. -/
lemma toRealGL_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (toRealGL γ : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) :=
  rfl

/-- The determinant of the image of `γ` in `GL(2, ℝ)`. -/
lemma toRealGL_det (γ : GL (Fin 2) ℚ) :
    (toRealGL γ).det.val = ((γ : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [toRealGL_apply]
  push_cast; ring

/-- The two maps from `SL(2, ℤ)` to `GL(2, ℝ)` agree. -/
lemma toRealGL_mapGL (σ : SL(2, ℤ)) : toRealGL (mapGL ℚ σ) = mapGL ℝ σ := by
  ext i j
  simp [toRealGL_apply]

/-- **Lemma 1.2.6.** An element `γ` of `GL(2, ℚ)` is in `GL(2, ℝ)⁺ K₀(N)`, that is, `det γ > 0` and the finite part of `γ` is in `K₀(N)`, if and only if `γ` is the image of an element of `Γ₀(N)`. -/
theorem toFinGL_mem_K0_iff (N : ℕ) [NeZero N] (γ : GL (Fin 2) ℚ) :
    (0 < (toRealGL γ).det.val ∧ toFinGL γ ∈ K0 N) ↔ ∃ σ ∈ Gamma0 N, mapGL ℚ σ = γ := by
  constructor
  · rintro ⟨hdet, hg, hg', c, hc, hgc⟩
    have hgi : ∀ i j, IsIntegralAdele (algebraMap ℚ 𝔸f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)) :=
      fun i j => hg i j
    have hgi' : ∀ i j,
        IsIntegralAdele (algebraMap ℚ 𝔸f (((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j)) :=
      fun i j => by simpa [← map_inv, toFinGL_apply] using hg' i j
    choose A hA using fun i j => (isIntegralAdele_algebraMap_iff _).1 (hgi i j)
    choose B hB using fun i j => (isIntegralAdele_algebraMap_iff _).1 (hgi' i j)
    have hAm : (Matrix.of A).map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j; simp [hA]
    have hBm : (Matrix.of B).map (Int.castRingHom ℚ) =
        ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j; simp [hB]
    have hAB : Matrix.of A * Matrix.of B = 1 := by
      apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
      dsimp only
      rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp
    have hdetAB := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hdetAB
    have hdetA : ((Matrix.of A).det : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ).det := by
      rw [← hAm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have hpos : 0 < (Matrix.of A).det := by
      rw [toRealGL_det, ← hdetA] at hdet
      exact_mod_cast hdet
    have hA1 : (Matrix.of A).det = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h | h
      · exact h
      · omega
    let σ : SL(2, ℤ) := ⟨Matrix.of A, hA1⟩
    have hσ : ∀ i j, σ i j = A i j := fun _ _ => rfl
    refine ⟨σ, ?_, ?_⟩
    · have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
      have hc' : c = algebraMap ℚ 𝔸f ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 / N) := by
        rw [div_eq_mul_inv, map_mul, ← toFinGL_apply, hgc, mul_comm (N : 𝔸f), mul_assoc,
          ← map_natCast (algebraMap ℚ 𝔸f), ← map_mul, mul_inv_cancel₀ hN, map_one, mul_one]
      obtain ⟨m, hm⟩ := (isIntegralAdele_algebraMap_iff _).1 (hc' ▸ hc)
      have h10 : A 1 0 = N * m := by
        have : (A 1 0 : ℚ) = N * m := by rw [hA, hm]; field_simp
        exact_mod_cast this
      rw [Gamma0_mem]
      rw [hσ, h10]; push_cast; simp
    · ext i j
      show algebraMap ℤ ℚ (σ i j) = _
      rw [hσ, eq_intCast, hA]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨by simp [toRealGL_mapGL], fun i j => ?_, fun i j => ?_, ?_⟩
    · rw [toFinGL_apply]
      exact (isIntegralAdele_algebraMap_iff _).2 ⟨σ i j, by simp⟩
    · rw [← map_inv, ← map_inv (mapGL ℚ) σ, toFinGL_apply]
      exact (isIntegralAdele_algebraMap_iff _).2
        ⟨(σ⁻¹ : SL(2, ℤ)) i j, by
          show _ = algebraMap ℤ ℚ _
          rw [eq_intCast]⟩
    · obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hσ)
      refine ⟨algebraMap ℚ 𝔸f m, (isIntegralAdele_algebraMap_iff _).2 ⟨m, rfl⟩, ?_⟩
      rw [toFinGL_apply, ← map_natCast (algebraMap ℚ 𝔸f), ← map_mul]
      congr 1
      simp [hm]


section ClassNumberOne

open WithZero

/-- A generator of the prime ideal `v` of `ℤ`. -/
noncomputable def primeGen (v : HeightOneSpectrum ℤ) : ℤ :=
  Submodule.IsPrincipal.generator v.asIdeal

/-- The prime ideal `v` is generated by `primeGen v`. -/
lemma primeGen_span (v : HeightOneSpectrum ℤ) : v.asIdeal = Ideal.span {primeGen v} :=
  (Submodule.IsPrincipal.span_singleton_generator _).symm

/-- The generator `primeGen v` is not zero. -/
lemma primeGen_ne_zero (v : HeightOneSpectrum ℤ) : primeGen v ≠ 0 := fun h =>
  v.ne_bot (by rw [primeGen_span, h, Ideal.span_singleton_eq_bot.2 rfl])

/-- The valuation of `primeGen v` at `v` is `exp (-1)`. -/
lemma valuation_primeGen_self (v : HeightOneSpectrum ℤ) :
    v.valuation ℚ (primeGen v : ℚ) = exp (-1 : ℤ) := by
  rw [show ((primeGen v : ℤ) : ℚ) = algebraMap ℤ ℚ (primeGen v) by simp, valuation_of_algebraMap,
    intValuation_singleton _ (primeGen_ne_zero v) (primeGen_span v)]

/-- The valuation of `primeGen v` at a place `w ≠ v` is `1`. -/
lemma valuation_primeGen_of_ne {v w : HeightOneSpectrum ℤ} (h : w ≠ v) :
    v.valuation ℚ (primeGen w : ℚ) = 1 := by
  rw [show ((primeGen w : ℤ) : ℚ) = algebraMap ℤ ℚ (primeGen w) by simp, valuation_of_algebraMap,
    intValuation_eq_one_iff]
  intro hmem
  have hle : w.asIdeal ≤ v.asIdeal := by
    rw [primeGen_span w, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle))

/-- The components of a finite idele have nonzero valuation. -/
lemma FinAdele.valued_unit_ne_zero (x : 𝔸fˣ) (v : HeightOneSpectrum ℤ) : Valued.v ((x : 𝔸f) v) ≠ 0 := by
  have h : ((x⁻¹ : 𝔸fˣ) : 𝔸f) v * (x : 𝔸f) v = 1 := by
    rw [← FinAdele.mul_apply, Units.inv_mul, FinAdele.one_apply]
  intro h0
  have := congrArg Valued.v h
  rw [Valuation.map_mul, h0, mul_zero, Valuation.map_one] at this
  exact zero_ne_one this

/-- The valuation of a component of `x⁻¹` is the inverse of the valuation of the component of `x`. -/
lemma FinAdele.valued_unit_inv (x : 𝔸fˣ) (v : HeightOneSpectrum ℤ) :
    Valued.v (((x⁻¹ : 𝔸fˣ) : 𝔸f) v) = (Valued.v ((x : 𝔸f) v))⁻¹ := by
  have h : ((x⁻¹ : 𝔸fˣ) : 𝔸f) v * (x : 𝔸f) v = 1 := by
    rw [← FinAdele.mul_apply, Units.inv_mul, FinAdele.one_apply]
  have := congrArg Valued.v h
  rw [Valuation.map_mul, Valuation.map_one] at this
  exact eq_inv_of_mul_eq_one_left this

/-- For each finite idele `x` there is a nonzero rational number with the same valuations as `x` at all finite places. -/
theorem exists_rat_valuation_eq (x : 𝔸fˣ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ q = Valued.v ((x : 𝔸f) v) := by
  classical
  have hfin : (Function.mulSupport fun v => Valued.v ((x : 𝔸f) v)).Finite :=
    FiniteAdeleRing.hasFiniteMulSupport_valued x
  refine ⟨∏ w ∈ hfin.toFinset, ((primeGen w : ℚ)) ^ (-(log (Valued.v ((x : 𝔸f) w)))), ?_,
    fun v => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun w _ => zpow_ne_zero _ (by exact_mod_cast primeGen_ne_zero w)
  · rw [map_prod]
    simp_rw [map_zpow₀]
    by_cases hv : v ∈ hfin.toFinset
    · rw [Finset.prod_eq_single v (fun w _ hw => by rw [valuation_primeGen_of_ne hw, one_zpow])
        (fun h => absurd hv h), valuation_primeGen_self, ← exp_zsmul,
        show ∀ L : ℤ, (-L) • (-1 : ℤ) = L from fun L => by simp, exp_log (FinAdele.valued_unit_ne_zero x v)]
    · rw [Finset.prod_eq_one fun w hw => by
        rw [valuation_primeGen_of_ne (fun h : w = v => hv (h ▸ hw)), one_zpow]]
      simp only [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      exact hv.symm

/-- **Class number one for `ℚ`.** Each finite idele `x` is `q u` with a positive rational number `q` and a unit `u` of the integral adeles `Ẑ`. -/
theorem exists_rat_mul_integralUnit (x : 𝔸fˣ) :
    ∃ q : ℚ, 0 < q ∧ ∃ u : 𝔸fˣ, IsIntegralAdele u ∧ IsIntegralAdele ↑u⁻¹ ∧
      (x : 𝔸f) = algebraMap ℚ 𝔸f q * u := by
  obtain ⟨q, hq0, hq⟩ := exists_rat_valuation_eq x
  have hq' : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ |q| = Valued.v ((x : 𝔸f) v) := by
    intro v
    rcases abs_choice q with h | h <;> rw [h]
    · exact hq v
    · rw [Valuation.map_neg]; exact hq v
  have ha : |q| ≠ 0 := abs_ne_zero.2 hq0
  let r : 𝔸fˣ := Units.map (algebraMap ℚ 𝔸f).toMonoidHom (Units.mk0 |q| ha)
  have hr : ∀ v, Valued.v ((r : 𝔸f) v) = Valued.v ((x : 𝔸f) v) := fun v => by
    have : (r : 𝔸f) = algebraMap ℚ 𝔸f |q| := rfl
    rw [this, FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation', hq']
  refine ⟨|q|, abs_pos.2 hq0, r⁻¹ * x, fun v => ?_, fun v => ?_, ?_⟩
  · rw [mem_adicCompletionIntegers, Units.val_mul, FinAdele.mul_apply, Valuation.map_mul,
      FinAdele.valued_unit_inv, hr, inv_mul_cancel₀ (FinAdele.valued_unit_ne_zero x v)]
  · rw [mem_adicCompletionIntegers, mul_inv_rev, inv_inv, Units.val_mul, FinAdele.mul_apply,
      Valuation.map_mul, FinAdele.valued_unit_inv, hr,
      inv_mul_cancel₀ (FinAdele.valued_unit_ne_zero x v)]
  · show (x : 𝔸f) = (r : 𝔸f) * ((r⁻¹ * x : 𝔸fˣ) : 𝔸f)
    rw [← Units.val_mul, mul_inv_cancel_left]

end ClassNumberOne


section Decomposition

/-- The group `GL(2, 𝔸) = GL(2, ℝ) × GL(2, 𝔸f)`. -/
abbrev AdelicGL2 : Type := GL (Fin 2) ℝ × GL (Fin 2) 𝔸f

/-- The diagonal embedding of `GL(2, ℚ)` in `GL(2, 𝔸)`. -/
noncomputable def principalGL2 : GL (Fin 2) ℚ →* AdelicGL2 :=
  toRealGL.prod toFinGL

/-- The components of the image of `γ` in `GL(2, 𝔸)`. -/
@[simp] lemma principalGL2_apply (γ : GL (Fin 2) ℚ) : principalGL2 γ = (toRealGL γ, toFinGL γ) :=
  rfl

/-- The statement that `g = γ (h, 1) (1, κ)` with `γ ∈ GL(2, ℚ)`, `h ∈ GL(2, ℝ)⁺` and `κ ∈ K₀(N)`. -/
def IsDecomp (N : ℕ) (g : AdelicGL2) (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) (κ : GL (Fin 2) 𝔸f) :
    Prop :=
  0 < h.det.val ∧ κ ∈ K0 N ∧ g = principalGL2 γ * (h, 1) * (1, κ)

/-- The componentwise form of `IsDecomp`. -/
lemma isDecomp_iff {N : ℕ} {g : AdelicGL2} {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) ℝ}
    {κ : GL (Fin 2) 𝔸f} :
    IsDecomp N g γ h κ ↔ 0 < h.det.val ∧ κ ∈ K0 N ∧ g.1 = toRealGL γ * h ∧ g.2 = toFinGL γ * κ := by
  unfold IsDecomp
  constructor
  · rintro ⟨h1, h2, rfl⟩; exact ⟨h1, h2, by simp, by simp⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, Prod.ext (by simp [h3]) (by simp [h4])⟩

/-- Two decompositions of the same element differ by an element of `Γ₀(N)` at the infinite place. This is the uniqueness part of Corollary 1.2.7. -/
theorem IsDecomp.exists_gamma0 {N : ℕ} [NeZero N] {g : AdelicGL2} {γ γ' : GL (Fin 2) ℚ}
    {h h' : GL (Fin 2) ℝ} {κ κ' : GL (Fin 2) 𝔸f} (H : IsDecomp N g γ h κ)
    (H' : IsDecomp N g γ' h' κ') : ∃ σ ∈ Gamma0 N, h' = mapGL ℝ σ * h := by
  rw [isDecomp_iff] at H H'
  obtain ⟨hh, hκ, h1, h2⟩ := H
  obtain ⟨hh', hκ', h1', h2'⟩ := H'
  have hR : toRealGL (γ'⁻¹ * γ) = h' * h⁻¹ := by
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1', h1, mul_inv_cancel_right]
  have hF : toFinGL (γ'⁻¹ * γ) = κ' * κ⁻¹ := by
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2', h2, mul_inv_cancel_right]
  have hdet : 0 < (toRealGL (γ'⁻¹ * γ)).det.val := by
    rw [hR, map_mul, map_inv, Units.val_mul]
    exact mul_pos hh' (by simpa using hh)
  obtain ⟨σ, hσ, hσγ⟩ := (toFinGL_mem_K0_iff N _).1
    ⟨hdet, hF ▸ mul_mem hκ' (inv_mem hκ)⟩
  refine ⟨σ, hσ, ?_⟩
  rw [← toRealGL_mapGL, hσγ, hR, inv_mul_cancel_right]

/-- The matrix `diag(q, 1)` in `GL(2, ℚ)`. -/
noncomputable def diagQ (q : ℚ) (hq : q ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![q, 0; 0, 1] (by simp [hq])

/-- The matrix `ε = diag(-1, 1)` in `GL(2, ℚ)`. -/
noncomputable def epsQ : GL (Fin 2) ℚ := diagQ (-1) (by norm_num)

/-- The matrix `ε` is its own inverse. -/
lemma epsQ_mul_self : epsQ * epsQ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsQ, diagQ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The determinant of `ε` is `-1`. -/
lemma toRealGL_epsQ_det : (toRealGL epsQ).det.val = -1 := by
  rw [toRealGL_det]; simp [epsQ, diagQ]

/-- The matrix `ε` is in `K₀(N)`. -/
lemma toFinGL_epsQ_mem_K0 (N : ℕ) : toFinGL epsQ ∈ K0 N := by
  have hinv : (toFinGL epsQ)⁻¹ = toFinGL epsQ := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right epsQ_mul_self]
  have hint : ∀ i j, IsIntegralAdele ((toFinGL epsQ : Matrix (Fin 2) (Fin 2) 𝔸f) i j) := by
    intro i j
    rw [toFinGL_apply]
    refine (isIntegralAdele_algebraMap_iff _).2 ?_
    fin_cases i <;> fin_cases j
    exacts [⟨-1, by simp [epsQ, diagQ]⟩, ⟨0, by simp [epsQ, diagQ]⟩, ⟨0, by simp [epsQ, diagQ]⟩,
      ⟨1, by simp [epsQ, diagQ]⟩]
  refine ⟨hint, hinv ▸ hint, 0, isIntegralAdele_zero, ?_⟩
  rw [mul_zero, toFinGL_apply]
  simp [epsQ, diagQ]

/-- The matrix `diag(1, u)` in `GL(2, 𝔸f)` for a finite idele `u`. -/
noncomputable def diagUnit (u : 𝔸fˣ) : GL (Fin 2) 𝔸f where
  val := !![1, 0; 0, (u : 𝔸f)]
  inv := !![1, 0; 0, ((u⁻¹ : 𝔸fˣ) : 𝔸f)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- If `u` is a unit of `Ẑ`, then `diag(1, u)` is in `K₀(N)`. -/
lemma diagUnit_mem_K0 (N : ℕ) {u : 𝔸fˣ} (hu : IsIntegralAdele u) (hu' : IsIntegralAdele ↑u⁻¹) :
    diagUnit u ∈ K0 N := by
  refine ⟨fun i j => ?_, fun i j => ?_, 0, isIntegralAdele_zero, ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [isIntegralAdele_one, isIntegralAdele_zero, isIntegralAdele_zero, hu]
  · fin_cases i <;> fin_cases j
    exacts [isIntegralAdele_one, isIntegralAdele_zero, isIntegralAdele_zero, hu']
  · rw [mul_zero]; rfl

/-- **Strong approximation for `SL(2)` at level `K₀(N)`.** Each `g ∈ SL(2, 𝔸f)` is `γ κ` with `γ ∈ SL(2, ℚ)` and `κ ∈ K₀(N)`. This is a true theorem: it follows from the density of `SL(2, ℚ)` in `SL(2, 𝔸f)` (Theorem 1.2.2 and Corollary 1.2.3 of the handbook), because `K₀(N) ∩ SL(2, 𝔸f)` is open. This file does not prove it, and it uses it only as a hypothesis. -/
def SL2StrongApprox (N : ℕ) : Prop :=
  ∀ g : GL (Fin 2) 𝔸f, Matrix.GeneralLinearGroup.det g = 1 →
    ∃ γ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det γ = 1 ∧ (toFinGL γ)⁻¹ * g ∈ K0 N

/-- **Theorem 1.2.5, finite part.** If `SL2StrongApprox N` holds, then `GL(2, 𝔸f) = GL(2, ℚ) K₀(N)`. The proof uses class number one for `ℚ` (`exists_rat_mul_integralUnit`). -/
theorem exists_toFinGL_inv_mul_mem_K0 {N : ℕ} (hSA : SL2StrongApprox N) (g : GL (Fin 2) 𝔸f) :
    ∃ γ : GL (Fin 2) ℚ, (toFinGL γ)⁻¹ * g ∈ K0 N := by
  obtain ⟨q, hq, u, hu, hu', hx⟩ :=
    exists_rat_mul_integralUnit (Matrix.GeneralLinearGroup.det g)
  set δ := diagQ q hq.ne'
  set k₁ := diagUnit u
  have hdet : Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det (toFinGL δ) * Matrix.GeneralLinearGroup.det k₁ := by
    ext
    rw [hx, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [toFinGL_apply]
    simp [δ, k₁, diagQ, diagUnit]
  obtain ⟨γ, -, hγ⟩ := hSA ((toFinGL δ)⁻¹ * g * k₁⁻¹) (by
    rw [map_mul, map_mul, map_inv, map_inv, hdet]; group)
  refine ⟨δ * γ, ?_⟩
  have := mul_mem hγ (diagUnit_mem_K0 N hu hu')
  convert this using 1
  rw [map_mul, mul_inv_rev]
  simp only [k₁, mul_assoc, inv_mul_cancel, mul_one]

/-- **Theorem 1.2.5.** If `SL2StrongApprox N` holds, then `GL(2, 𝔸) = GL(2, ℚ) GL(2, ℝ)⁺ K₀(N)`: each `g` is `γ (h, 1) (1, κ)` with `γ ∈ GL(2, ℚ)`, `det h > 0` and `κ ∈ K₀(N)`. -/
theorem exists_isDecomp {N : ℕ} (hSA : SL2StrongApprox N) (g : AdelicGL2) :
    ∃ γ h κ, IsDecomp N g γ h κ := by
  obtain ⟨γ₀, hγ₀⟩ := exists_toFinGL_inv_mul_mem_K0 hSA g.2
  set h₀ := (toRealGL γ₀)⁻¹ * g.1
  rcases lt_or_gt_of_ne h₀.det.ne_zero with hneg | hpos
  · refine ⟨γ₀ * epsQ, toRealGL epsQ * h₀, toFinGL epsQ * ((toFinGL γ₀)⁻¹ * g.2), ?_⟩
    rw [isDecomp_iff]
    refine ⟨?_, mul_mem (toFinGL_epsQ_mem_K0 N) hγ₀, ?_, ?_⟩
    · rw [map_mul, Units.val_mul, toRealGL_epsQ_det]; linarith
    · rw [map_mul, mul_assoc, ← mul_assoc (toRealGL epsQ), ← map_mul, epsQ_mul_self, map_one,
        one_mul, mul_inv_cancel_left]
    · rw [map_mul, mul_assoc, ← mul_assoc (toFinGL epsQ), ← map_mul, epsQ_mul_self, map_one,
        one_mul, mul_inv_cancel_left]
  · exact ⟨γ₀, h₀, _, isDecomp_iff.2 ⟨hpos, hγ₀, by simp [h₀], by simp⟩⟩

/-- **Corollary 1.2.7, injectivity.** For `h, h' ∈ GL(2, ℝ)⁺`, the elements `(h, 1)` and `(h', 1)` of `GL(2, 𝔸)` have the same class in `GL(2, ℚ) \ GL(2, 𝔸) / K₀(N)` if and only if `h' ∈ Γ₀(N) h`. -/
theorem principal_mul_mul_K0_iff (N : ℕ) [NeZero N] {h h' : GL (Fin 2) ℝ} (hh : 0 < h.det.val)
    (hh' : 0 < h'.det.val) :
    (∃ γ : GL (Fin 2) ℚ, ∃ κ ∈ K0 N, ((h', 1) : AdelicGL2) = principalGL2 γ * (h, 1) * (1, κ)) ↔
      ∃ σ ∈ Gamma0 N, h' = mapGL ℝ σ * h := by
  constructor
  · rintro ⟨γ, κ, hκ, he⟩
    exact IsDecomp.exists_gamma0 (g := (h', 1)) ⟨hh, hκ, he⟩
      ((isDecomp_iff (γ := 1) (κ := 1)).2 ⟨hh', (K0 N).one_mem, by simp, by simp⟩) |>.imp fun σ ⟨hσ, e⟩ =>
        ⟨hσ, by simpa using e⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hK : toFinGL (mapGL ℚ σ) ∈ K0 N := ((toFinGL_mem_K0_iff N _).2 ⟨σ, hσ, rfl⟩).2
    refine ⟨mapGL ℚ σ, (toFinGL (mapGL ℚ σ))⁻¹, inv_mem hK, ?_⟩
    ext1 <;> simp [toRealGL_mapGL]

end Decomposition


section Lift

variable {N : ℕ} {k : ℤ}

local notation "Γ₀" => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The value at `i` of the unitary slash operator, `(F ‖ₖ h)(i) = det(h)^{k/2} j(h, i)^{-k} F(h i)`. For `det h > 0` it is `det(h)^{1 - k/2} (F ∣ₖ h)(i)`, with the slash operator `∣ₖ` of Mathlib (Definition 1.3.4). -/
noncomputable def unitarySlashAtI (k : ℤ) (F : ℍ → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  ((h.det.val ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) * (F ∣[k] h) I

/-- The value `(f ‖ₖ h)(i)` does not change if `h` is replaced by `σ h` with `σ ∈ Γ₀(N)`. -/
lemma unitarySlashAtI_gamma0_mul (f : ModularForm Γ₀ k) {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N)
    (h : GL (Fin 2) ℝ) : unitarySlashAtI k f (mapGL ℝ σ * h) = unitarySlashAtI k f h := by
  unfold unitarySlashAtI
  rw [SlashAction.slash_mul, SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hσ), map_mul,
    Units.val_mul]
  simp

open scoped Classical in
/-- The adelic lift `φ_F` of a function `F` on `ℍ` of weight `k` and level `N`. At `g = γ (h, 1) (1, κ)` with `γ ∈ GL(2, ℚ)`, `det h > 0` and `κ ∈ K₀(N)`, it is `(F ‖ₖ h)(i)` for a chosen decomposition. At the other elements it is `0`. If `SL2StrongApprox N` holds, there are no other elements (`exists_isDecomp`). -/
noncomputable def adelicLift (N : ℕ) (k : ℤ) (F : ℍ → ℂ) (g : AdelicGL2) : ℂ :=
  if H : ∃ γ h κ, IsDecomp N g γ h κ then unitarySlashAtI k F H.choose_spec.choose else 0

/-- The lift does not depend on the decomposition: if `g = γ (h, 1) (1, κ)`, then `φ_f(g) = (f ‖ₖ h)(i)`. -/
theorem adelicLift_of_isDecomp [NeZero N] (f : ModularForm Γ₀ k) {g : AdelicGL2}
    {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) ℝ} {κ : GL (Fin 2) 𝔸f} (H : IsDecomp N g γ h κ) :
    adelicLift N k f g = unitarySlashAtI k f h := by
  have H₀ : ∃ γ h κ, IsDecomp N g γ h κ := ⟨γ, h, κ, H⟩
  rw [adelicLift, dite_eq_left H₀]
  obtain ⟨σ, hσ, e⟩ := H.exists_gamma0 H₀.choose_spec.choose_spec.choose_spec
  rw [e, unitarySlashAtI_gamma0_mul f hσ]

/-- **Proposition 1.3.5.** For a modular form `f` of weight `k` for `Γ₀(N)`, `φ_f(γ (h, 1) (1, κ)) = (f ‖ₖ h)(i)` for all `γ ∈ GL(2, ℚ)`, `h ∈ GL(2, ℝ)` with `det h > 0` and `κ ∈ K₀(N)`. -/
theorem adelicLift_apply [NeZero N] (f : ModularForm Γ₀ k) (γ : GL (Fin 2) ℚ)
    {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) {κ : GL (Fin 2) 𝔸f} (hκ : κ ∈ K0 N) :
    adelicLift N k f (principalGL2 γ * (h, 1) * (1, κ)) = unitarySlashAtI k f h :=
  adelicLift_of_isDecomp f ⟨hh, hκ, rfl⟩

/-- If `SL2StrongApprox N` holds, then `φ_f` is the only function on `GL(2, 𝔸)` with `φ(γ (h, 1) (1, κ)) = (f ‖ₖ h)(i)` for all `γ`, `h` with `det h > 0` and `κ ∈ K₀(N)`. -/
theorem eq_adelicLift [NeZero N] (hSA : SL2StrongApprox N) (f : ModularForm Γ₀ k)
    (φ : AdelicGL2 → ℂ) (hφ : ∀ (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) (κ : GL (Fin 2) 𝔸f),
      0 < h.det.val → κ ∈ K0 N → φ (principalGL2 γ * (h, 1) * (1, κ)) = unitarySlashAtI k f h) :
    φ = adelicLift N k f := by
  funext g
  obtain ⟨γ, h, κ, hh, hκ, rfl⟩ := exists_isDecomp hSA g
  rw [hφ γ h κ hh hκ, adelicLift_apply f γ hh hκ]

/-- A decomposition of `g` gives a decomposition of `γ' g`. -/
lemma isDecomp_principal_mul {g : AdelicGL2} {γ' γ : GL (Fin 2) ℚ} {h : GL (Fin 2) ℝ}
    {κ : GL (Fin 2) 𝔸f} (H : IsDecomp N g γ h κ) :
    IsDecomp N (principalGL2 γ' * g) (γ' * γ) h κ :=
  ⟨H.1, H.2.1, by rw [H.2.2, map_mul]; simp only [mul_assoc]⟩

/-- A decomposition of `g` gives a decomposition of `g κ'` for `κ' ∈ K₀(N)`. -/
lemma isDecomp_mul_K0 {g : AdelicGL2} {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) ℝ}
    {κ κ' : GL (Fin 2) 𝔸f} (H : IsDecomp N g γ h κ) (hκ' : κ' ∈ K0 N) :
    IsDecomp N (g * (1, κ')) γ h (κ * κ') := by
  obtain ⟨h1, h2, h3, h4⟩ := isDecomp_iff.1 H
  exact isDecomp_iff.2 ⟨h1, mul_mem h2 hκ', by simp [h3], by simp [h4, mul_assoc]⟩

/-- **Proposition 1.3.6, part 1.** The lift is left invariant under `GL(2, ℚ)`. -/
theorem adelicLift_principal_mul [NeZero N] (f : ModularForm Γ₀ k) (γ : GL (Fin 2) ℚ)
    (g : AdelicGL2) : adelicLift N k f (principalGL2 γ * g) = adelicLift N k f g := by
  by_cases H : ∃ γ' h κ, IsDecomp N g γ' h κ
  · obtain ⟨γ', h, κ, hd⟩ := H
    rw [adelicLift_of_isDecomp f (isDecomp_principal_mul (γ' := γ) hd), adelicLift_of_isDecomp f hd]
  · have H' : ¬ ∃ γ' h κ, IsDecomp N (principalGL2 γ * g) γ' h κ := by
      rintro ⟨γ', h, κ, hd⟩
      have := isDecomp_principal_mul (γ' := γ⁻¹) hd
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at this
      exact H ⟨_, h, κ, this⟩
    rw [adelicLift, adelicLift, dite_eq_right H, dite_eq_right H']

/-- **Proposition 1.3.6, part 2.** The lift is right invariant under `K₀(N)`. -/
theorem adelicLift_mul_K0 [NeZero N] (f : ModularForm Γ₀ k) (g : AdelicGL2)
    {κ' : GL (Fin 2) 𝔸f} (hκ' : κ' ∈ K0 N) :
    adelicLift N k f (g * (1, κ')) = adelicLift N k f g := by
  by_cases H : ∃ γ h κ, IsDecomp N g γ h κ
  · obtain ⟨γ, h, κ, hd⟩ := H
    rw [adelicLift_of_isDecomp f (isDecomp_mul_K0 hd hκ'), adelicLift_of_isDecomp f hd]
  · have H' : ¬ ∃ γ h κ, IsDecomp N (g * (1, κ')) γ h κ := by
      rintro ⟨γ, h, κ, hd⟩
      have := isDecomp_mul_K0 hd (inv_mem hκ')
      have e : g * (1, κ') * ((1 : GL (Fin 2) ℝ), κ'⁻¹) = g := by ext1 <;> simp
      rw [e] at this
      exact H ⟨γ, h, _, this⟩
    rw [adelicLift, adelicLift, dite_eq_right H, dite_eq_right H']

/-- The lift `f ↦ φ_f` as a `ℂ`-linear map from `M_k(Γ₀(N))` to the functions on `GL(2, 𝔸)`. -/
noncomputable def adelicLiftLinear (N : ℕ) [NeZero N] (k : ℤ) :
    ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (AdelicGL2 → ℂ) where
  toFun f := adelicLift N k f
  map_add' f f' := by
    funext g
    by_cases H : ∃ γ h κ, IsDecomp N g γ h κ
    · obtain ⟨γ, h, κ, hd⟩ := H
      simp only [Pi.add_apply]
      rw [adelicLift_of_isDecomp _ hd, adelicLift_of_isDecomp _ hd, adelicLift_of_isDecomp _ hd]
      simp [unitarySlashAtI, SlashAction.add_slash, mul_add]
    · simp [adelicLift, H]
  map_smul' c f := by
    funext g
    by_cases H : ∃ γ h κ, IsDecomp N g γ h κ
    · obtain ⟨γ, h, κ, hd⟩ := H
      simp only [Pi.smul_apply, RingHom.id_apply]
      rw [adelicLift_of_isDecomp _ hd, adelicLift_of_isDecomp _ hd]
      have hpos : 0 < (h : Matrix (Fin 2) (Fin 2) ℝ).det := by simpa using hd.1
      simp [unitarySlashAtI, smul_slash, σ, hpos]
      ring
    · simp [adelicLift, H]

/-- The linear map `adelicLiftLinear` is `adelicLift`. -/
@[simp] lemma adelicLiftLinear_apply [NeZero N] (f : ModularForm Γ₀ k) :
    adelicLiftLinear N k f = adelicLift N k f := rfl

/-- The value of `F ‖ₖ h` at `i` for the element `h` of `SL(2, ℝ)` with `h i = τ`. -/
lemma unitarySlashAtI_toSL2R (F : ℍ → ℂ) (τ : ℍ) :
    unitarySlashAtI k F (mapGL ℝ τ.toSL2R) = F τ * denom (mapGL ℝ τ.toSL2R) I ^ (-k) := by
  have hsmul : (mapGL ℝ τ.toSL2R : GL (Fin 2) ℝ) • I = τ := toSL2R_smul_I τ
  simp [unitarySlashAtI, slash_apply, hsmul, σ]

/-- **Injectivity of the lift.** If `φ_f = φ_{f'}`, then `f = f'`. -/
theorem adelicLift_injective [NeZero N] :
    Function.Injective (fun f : ModularForm Γ₀ k => adelicLift N k f) := by
  intro f f' he
  ext τ
  have hd : IsDecomp N (mapGL ℝ τ.toSL2R, 1) 1 (mapGL ℝ τ.toSL2R) 1 :=
    isDecomp_iff.2 ⟨by simp, (K0 N).one_mem, by simp, by simp⟩
  have := congrFun he (mapGL ℝ τ.toSL2R, 1)
  simp only at this
  rw [adelicLift_of_isDecomp f hd, adelicLift_of_isDecomp f' hd, unitarySlashAtI_toSL2R,
    unitarySlashAtI_toSL2R] at this
  exact mul_right_cancel₀ (zpow_ne_zero _ (denom_ne_zero _ _)) this

/-- **Injectivity of the lift**, for the linear map `adelicLiftLinear`. -/
theorem adelicLiftLinear_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (adelicLiftLinear N k) :=
  adelicLift_injective

end Lift

end Langlands.Modular
