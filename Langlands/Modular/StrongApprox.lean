/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Modular.Adelic

/-!
# Strong approximation for `SL(2)` over `ℚ`

This file proves strong approximation for $SL_2$ at level $K_0(N)$: each $g \in SL_2(\mathbb{A}_f)$ is $\gamma \kappa$ with $\gamma \in SL_2(\mathbb{Q})$ and $\kappa \in K_0(N)$. This is the statement `Langlands.Modular.SL2StrongApprox N` of `Langlands/Modular/Adelic.lean`. As a consequence, the decomposition $GL_2(\mathbb{A}) = GL_2(\mathbb{Q}) GL_2^+(\mathbb{R}) K_0(N)$ (Theorem 1.2.5 of the handbook) and the uniqueness of the adelic lift hold without a hypothesis.

## Main definitions

* `Langlands.Modular.FinAdele.ofIntegral`: the finite adele with given integral components.
* `Langlands.Modular.glOfDetOne`: the element of $GL_2(R)$ given by a matrix of determinant $1$.
* `Langlands.Modular.elemUpper`, `Langlands.Modular.elemLower`: the elementary matrices of $SL_2(\mathbb{Q})$.

## Main results

* `Langlands.Modular.exists_rat_sub_isIntegralAdele`: $\mathbb{A}_f = \mathbb{Q} + \hat{\mathbb{Z}}$.
* `Langlands.Modular.exists_int_sub_eq_mul`: $\hat{\mathbb{Z}} = \mathbb{Z} + N \hat{\mathbb{Z}}$.
* `Langlands.Modular.exists_toFinGL_inv_mul_mem_K0_one`: $SL_2(\mathbb{A}_f) = SL_2(\mathbb{Q}) SL_2(\hat{\mathbb{Z}})$.
* `Langlands.Modular.exists_toFinGL_inv_mul_mem_K0_of_mem_K0_one`: $SL_2(\hat{\mathbb{Z}}) = SL_2(\mathbb{Z}) (SL_2(\hat{\mathbb{Z}}) \cap K_0(N))$.
* `Langlands.Modular.sl2StrongApprox`: strong approximation `SL2StrongApprox N` for $N \geq 1$.
* `Langlands.Modular.exists_toFinGL_inv_mul_mem_K0'`: $GL_2(\mathbb{A}_f) = GL_2(\mathbb{Q}) K_0(N)$.
* `Langlands.Modular.exists_isDecomp'`: $GL_2(\mathbb{A}) = GL_2(\mathbb{Q}) GL_2^+(\mathbb{R}) K_0(N)$ (Theorem 1.2.5).
* `Langlands.Modular.eq_adelicLift'`: the adelic lift is the only function with the values of Proposition 1.3.5.

## Proof

The proof is elementary and works place by place. First, $\mathbb{Q}$ is dense in each completion $\mathbb{Q}_p$, so for $y \in \mathbb{Q}_p$ there is $a / p^n$ with $a \in \mathbb{Z}$ and $y - a / p^n \in \mathbb{Z}_p$. A finite adele is integral outside a finite set of places, and an induction on this set gives $\mathbb{A}_f = \mathbb{Q} + \hat{\mathbb{Z}}$. For an integral adele $x$, apply this to $x / N$ to get $\hat{\mathbb{Z}} = \mathbb{Z} + N \hat{\mathbb{Z}}$.

Let $g \in SL_2(\mathbb{A}_f)$ have lower row $(c, d)$. At each place, put $k_v = \begin{pmatrix} 1 & 0 \\ -c/d & 1 \end{pmatrix}$ if $|c|_v \leq |d|_v$ and $k_v = \begin{pmatrix} -d/c & -1 \\ 1 & 0 \end{pmatrix}$ if not. Then $k \in SL_2(\hat{\mathbb{Z}})$ and $g k$ is upper triangular. Class number one writes its upper left entry as $q u$ with $q \in \mathbb{Q}_{>0}$ and $u \in \hat{\mathbb{Z}}^\times$, and $\mathbb{A}_f = \mathbb{Q} + \hat{\mathbb{Z}}$ removes the upper right entry. This gives $g \in SL_2(\mathbb{Q}) SL_2(\hat{\mathbb{Z}})$.

Let $\kappa \in SL_2(\hat{\mathbb{Z}})$ have first column $(a, c)$. If $a$ is not a unit at $p$, then $c$ is a unit at $p$. Choose $s \in \mathbb{Z}$ with $s \equiv 0$ modulo $N \hat{\mathbb{Z}}$ at the places where $a$ is a unit and $s \equiv 1$ at the other places. Then $a + s c$ is a unit at all places that divide $N$. A right multiplication by a lower triangular element of $K_0(N)$ makes the upper left entry $w$ a unit at all places. Last, choose $r \in \mathbb{Z}$ with $r \equiv c w^{-1}$ modulo $N \hat{\mathbb{Z}}$. The row operation with $r$ puts the lower left entry in $N \hat{\mathbb{Z}}$. The two row operations are elements of $SL_2(\mathbb{Z})$.

## References

* The langlands handbook, Volume 5, Chapter 1, section 1.2.
* G. Shimura, Introduction to the arithmetic theory of automorphic functions, Lemma 6.15 and Theorem 6.17.
* D. Bump, Automorphic forms and representations, Section 3.3.
-/

namespace Langlands.Modular

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero ModularForm
  CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "𝔸f" => FinAdele

section Approximation

/-- The valuation of the component at `v` of a rational number is its `v`-adic valuation. -/
lemma valued_algebraMap_apply (q : ℚ) (v : HeightOneSpectrum ℤ) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  rw [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']

/-- For `y ∈ ℚ_v` there is a rational number `q` such that `y - q` is integral at `v` and `q` is integral at all other places. -/
lemma exists_rat_local (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ) :
    ∃ q : ℚ, Valued.v (y - (algebraMap ℚ 𝔸f q) v) ≤ 1 ∧ ∀ w ≠ v, w.valuation ℚ q ≤ 1 := by
  have hopen : IsOpen {z : v.adicCompletion ℚ | Valued.v (y - z) ≤ 1} :=
    (Valued.isOpen_integer (v.adicCompletion ℚ)).preimage (continuous_const.sub continuous_id)
  obtain ⟨r, hr⟩ := (denseRange_algebraMap ℚ v).exists_mem_open hopen
    ⟨y, by simp⟩
  change Valued.v (y - (algebraMap ℚ 𝔸f r) v) ≤ 1 at hr
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, hr, fun w _ => by simp⟩
  obtain ⟨π, hπv, hπw⟩ : ∃ π : ℚ, v.valuation ℚ π = exp (-1 : ℤ) ∧ ∀ w ≠ v, w.valuation ℚ π = 1 :=
    ⟨_, valuation_primeGen_self v, fun w hw => valuation_primeGen_of_ne hw.symm⟩
  have hπ0 : π ≠ 0 := fun h => exp_ne_zero (hπv.symm.trans (by simp [h]))
  set n : ℕ := (log (v.valuation ℚ r)).toNat
  have hvr : v.valuation ℚ r ≠ 0 := by simpa using hr0
  have hπn : v.valuation ℚ (π ^ n) = exp (-(n : ℤ)) := by
    rw [map_pow, hπv, ← exp_nsmul]; congr 1; simp
  have hx : v.valuation ℚ (π ^ n * r) ≤ 1 := by
    rw [map_mul, hπn]
    calc exp (-(n : ℤ)) * v.valuation ℚ r = exp (-(n : ℤ)) * exp (log (v.valuation ℚ r)) := by
          rw [exp_log hvr]
      _ = exp (log (v.valuation ℚ r) - n) := by rw [← exp_add]; congr 1; ring
      _ ≤ 1 := by
          rw [← exp_zero, exp_le_exp]
          have := Int.self_le_toNat (log (v.valuation ℚ r)); omega
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hx (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨a / π ^ n, ?_, fun w hw => ?_⟩
  · have hqr : v.valuation ℚ (a / π ^ n - r) < 1 := by
      have he : (a / π ^ n - r) * π ^ n = (algebraMap ℤ ℚ a - π ^ n * r) := by
        field_simp; simp
      have := congrArg (v.valuation ℚ) he
      rw [map_mul, hπn] at this
      have ha' : v.valuation ℚ (algebraMap ℤ ℚ a - π ^ n * r) < exp (-(n : ℤ)) := ha
      rw [← this] at ha'
      simpa using ha'
    have : y - (algebraMap ℚ 𝔸f (a / π ^ n)) v =
        (y - (algebraMap ℚ 𝔸f r) v) - (algebraMap ℚ 𝔸f (a / π ^ n - r)) v := by
      rw [map_sub, FinAdele.sub_apply]; ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le hr ?_)
    rw [valued_algebraMap_apply]; exact hqr.le
  · rw [map_div₀, map_pow, hπw w hw, one_pow, div_one]
    simpa using w.valuation_le_one (K := ℚ) a


/-- **Approximation.** Each finite adele is the sum of a rational number and an integral adele: `𝔸f = ℚ + Ẑ`. -/
theorem exists_rat_sub_isIntegralAdele (x : 𝔸f) :
    ∃ q : ℚ, IsIntegralAdele (x - algebraMap ℚ 𝔸f q) := by
  classical
  suffices H : ∀ s : Finset (HeightOneSpectrum ℤ), ∀ x : 𝔸f,
      (∀ v ∉ s, x v ∈ v.adicCompletionIntegers ℚ) →
        ∃ q : ℚ, IsIntegralAdele (x - algebraMap ℚ 𝔸f q) by
    refine H (FiniteAdeleRing.finite_valued_one_lt x).toFinset x fun v hv => ?_
    rw [mem_adicCompletionIntegers]; simpa using hv
  intro s
  induction s using Finset.induction_on with
  | empty => intro x hx; exact ⟨0, fun v => by simpa using hx v (Finset.notMem_empty v)⟩
  | insert v s hvs ih =>
    intro x hx
    obtain ⟨q, hq, hqw⟩ := exists_rat_local v (x v)
    have hx' : ∀ w ∉ s, (x - algebraMap ℚ 𝔸f q) w ∈ w.adicCompletionIntegers ℚ := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv; rw [mem_adicCompletionIntegers]; simpa using hq
      · rw [FinAdele.sub_apply]; refine sub_mem (hx w (by simp [hwv, hw])) ?_
        rw [mem_adicCompletionIntegers, valued_algebraMap_apply]; exact hqw w hwv
    obtain ⟨q', hq'⟩ := ih (x - algebraMap ℚ 𝔸f q) hx'
    exact ⟨q + q', by simpa [map_add, sub_add_eq_sub_sub] using hq'⟩

/-- **Approximation modulo `N`.** For each integral adele `x` there is an integer `m` with `x - m ∈ N Ẑ`: `Ẑ = ℤ + N Ẑ`. -/
theorem exists_int_sub_eq_mul (N : ℕ) [NeZero N] {x : 𝔸f} (hx : IsIntegralAdele x) :
    ∃ m : ℤ, ∃ c : 𝔸f, IsIntegralAdele c ∧ x - (m : 𝔸f) = (N : 𝔸f) * c := by
  obtain ⟨q, hq⟩ := exists_rat_sub_isIntegralAdele (algebraMap ℚ 𝔸f (N : ℚ)⁻¹ * x)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNc : (N : 𝔸f) * algebraMap ℚ 𝔸f (N : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ 𝔸f), ← map_mul, mul_inv_cancel₀ hN, map_one]
  set c := algebraMap ℚ 𝔸f (N : ℚ)⁻¹ * x - algebraMap ℚ 𝔸f q
  have hxc : x - algebraMap ℚ 𝔸f (N * q) = (N : 𝔸f) * c := by
    simp only [c, map_mul, map_natCast]; linear_combination (-x) * hNc
  have hNint : IsIntegralAdele (N : 𝔸f) := by exact_mod_cast isIntegralAdele_intCast N
  have hint : IsIntegralAdele (algebraMap ℚ 𝔸f (N * q)) := by
    have := hx.add (hNint.mul hq).neg
    rwa [← hxc, sub_eq_add_neg, neg_add, neg_neg, ← add_assoc, add_neg_cancel, zero_add] at this
  obtain ⟨m, hm⟩ := (isIntegralAdele_algebraMap_iff _).1 hint
  exact ⟨m, c, hq, by rw [← hxc, ← hm, map_intCast]⟩


end Approximation

section Matrices

/-- The integral finite adele with components `x v`. -/
def FinAdele.ofIntegral (x : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers ℚ) : 𝔸f :=
  ⟨x, Filter.Eventually.of_forall hx⟩

/-- The components of `FinAdele.ofIntegral x hx` are the `x v`. -/
@[simp] lemma FinAdele.ofIntegral_apply (x : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers ℚ) (v : HeightOneSpectrum ℤ) :
    FinAdele.ofIntegral x hx v = x v := rfl

/-- The adele `FinAdele.ofIntegral x hx` is integral. -/
lemma isIntegralAdele_ofIntegral (x : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers ℚ) : IsIntegralAdele (FinAdele.ofIntegral x hx) := hx

/-- The element of `GL(2, R)` given by a matrix of determinant `1`. -/
def glOfDetOne {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (h : M.det = 1) :
    GL (Fin 2) R where
  val := M
  inv := M.adjugate
  val_inv := by rw [Matrix.mul_adjugate, h, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, h, one_smul]

/-- The matrix of `glOfDetOne M h` is `M`. -/
@[simp] lemma coe_glOfDetOne {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.det = 1) : (glOfDetOne M h : Matrix (Fin 2) (Fin 2) R) = M := rfl

/-- The determinant of `glOfDetOne M h` is `1`. -/
lemma det_glOfDetOne {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (h : M.det = 1) :
    Matrix.GeneralLinearGroup.det (glOfDetOne M h) = 1 := by
  ext; rw [Matrix.GeneralLinearGroup.val_det_apply, coe_glOfDetOne, h, Units.val_one]

/-- The determinant of `g ∈ GL(2, R)` is `1` if and only if the determinant of its matrix is `1`. -/
lemma det_eq_one_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det g = 1 ↔ (g : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Units.val_eq_one]

/-- An element of `GL(2, 𝔸f)` of determinant `1` with integral entries and lower left entry in `N Ẑ` is in `K₀(N)`. -/
lemma mem_K0_of_det_eq_one {N : ℕ} {g : GL (Fin 2) 𝔸f} (hdet : Matrix.GeneralLinearGroup.det g = 1)
    (hg : ∀ i j, IsIntegralAdele ((g : Matrix (Fin 2) (Fin 2) 𝔸f) i j))
    (hc : ∃ c, IsIntegralAdele c ∧ (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = (N : 𝔸f) * c) :
    g ∈ K0 N := by
  have hinv : ((g⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      (g : Matrix (Fin 2) (Fin 2) 𝔸f).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, (det_eq_one_iff g).1 hdet]; simp
  refine ⟨hg, fun i j => ?_, hc⟩
  rw [hinv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  exacts [hg 1 1, (hg 0 1).neg, (hg 1 0).neg, hg 0 0]

/-- The group `K₀(N)` is a subgroup of `K₀(1) = GL(2, Ẑ)`. -/
lemma K0_le_K0_one (N : ℕ) : K0 N ≤ K0 1 := by
  rintro g ⟨h1, h2, c, hc, he⟩
  exact ⟨h1, h2, (N : 𝔸f) * c, (by exact_mod_cast isIntegralAdele_intCast N : IsIntegralAdele (N : 𝔸f)).mul hc,
    by rw [he, Nat.cast_one, one_mul]⟩


end Matrices

section Rational

/-- An upper triangular element `b` of `SL(2, 𝔸f)` is `γ κ` with `γ ∈ SL(2, ℚ)` and `κ ∈ GL(2, Ẑ)`. The proof uses class number one for the diagonal and `𝔸f = ℚ + Ẑ` for the upper right entry. -/
lemma exists_toFinGL_inv_mul_mem_K0_one_of_upper {b : GL (Fin 2) 𝔸f}
    (hdet : Matrix.GeneralLinearGroup.det b = 1) (hb : (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = 0) :
    ∃ γ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det γ = 1 ∧ (toFinGL γ)⁻¹ * b ∈ K0 1 := by
  have hB : (b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 * (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 = 1 := by
    have := (det_eq_one_iff b).1 hdet
    rw [Matrix.det_fin_two] at this; rw [← this]; simp only [hb, mul_zero, sub_zero]
  let t : 𝔸fˣ := ⟨(b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0, (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1, hB, by rw [mul_comm, hB]⟩
  obtain ⟨q, hq, u, hu, hu', ht⟩ := exists_rat_mul_integralUnit t
  obtain ⟨r, hr⟩ := exists_rat_sub_isIntegralAdele (u * algebraMap ℚ 𝔸f q⁻¹ * (b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1)
  set z := u * algebraMap ℚ 𝔸f q⁻¹ * (b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 - algebraMap ℚ 𝔸f r
  set ui : 𝔸f := ↑u⁻¹
  have huu : (u : 𝔸f) * ui = 1 := Units.mul_inv u
  have hqq : algebraMap ℚ 𝔸f q * algebraMap ℚ 𝔸f q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq.ne', map_one]
  have h00 : (b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 = algebraMap ℚ 𝔸f q * u := ht
  let γ := glOfDetOne !![q, q * r; 0, q⁻¹] (by simp [Matrix.det_fin_two, hq.ne'])
  let κ := glOfDetOne !![(u : 𝔸f), ui * z; 0, ui] (by simp [Matrix.det_fin_two, huu])
  have hbκ : b = toFinGL γ * κ := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, toFinGL_apply, toFinGL_apply]
    fin_cases i <;> fin_cases j
    · simp [γ, κ, h00]
    · simp [γ, κ, z]
      linear_combination -((b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 * (algebraMap ℚ 𝔸f q * algebraMap ℚ 𝔸f q⁻¹) * huu + (b : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 * hqq)
    · simp [γ, κ, hb]
    · simp [γ, κ]
      linear_combination algebraMap ℚ 𝔸f q⁻¹ * ui * hB -
        algebraMap ℚ 𝔸f q⁻¹ * ui * (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * h00 -
        (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * (algebraMap ℚ 𝔸f q * algebraMap ℚ 𝔸f q⁻¹) * huu -
        (b : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * hqq
  refine ⟨γ, det_glOfDetOne _ _, ?_⟩
  rw [hbκ, inv_mul_cancel_left]
  refine mem_K0_of_det_eq_one (det_glOfDetOne _ _) (fun i j => ?_) ⟨0, isIntegralAdele_zero, by simp [κ]⟩
  fin_cases i <;> fin_cases j
  exacts [hu, hu'.mul hr, isIntegralAdele_zero, hu']


/-- **Iwasawa decomposition.** For `g ∈ SL(2, 𝔸f)` there is `k ∈ SL(2, Ẑ)` such that `g k` is upper triangular. The element `k` is defined place by place. -/
lemma exists_mem_K0_one_mul_lower_eq_zero {g : GL (Fin 2) 𝔸f}
    (hdet : Matrix.GeneralLinearGroup.det g = 1) :
    ∃ k ∈ K0 1, Matrix.GeneralLinearGroup.det k = 1 ∧
      ((g * k : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 = d := ⟨_, rfl⟩
  have hcd : ∀ v, c v ≠ 0 ∨ d v ≠ 0 := by
    intro v; by_contra h; simp only [not_or, not_not] at h
    have h1 := (det_eq_one_iff g).1 hdet
    rw [Matrix.det_fin_two, hc, hd] at h1
    have h2 := congrArg (fun x : 𝔸f => x v) h1
    simp [h.1, h.2] at h2
  let P : HeightOneSpectrum ℤ → Prop := fun v => Valued.v (c v) ≤ Valued.v (d v)
  have hdP : ∀ v, P v → d v ≠ 0 := fun v hP h0 => by
    have : Valued.v (c v) = 0 := le_antisymm (by simpa [P, h0] using hP) zero_le
    exact ((hcd v).resolve_right (not_not.2 h0)) (by simpa using this)
  have hcP : ∀ v, ¬ P v → c v ≠ 0 := fun v hP h0 => hP (by simp [P, h0])
  let k00 := FinAdele.ofIntegral (fun v => if P v then 1 else -(d v / c v)) fun v => by
    split_ifs with hP
    · exact one_mem _
    · rw [mem_adicCompletionIntegers, Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ (not_le.1 hP).le zero_le
  let k01 := FinAdele.ofIntegral (fun v => if P v then 0 else -1) fun v => by
    split_ifs
    · exact zero_mem _
    · exact neg_mem (one_mem _)
  let k10 := FinAdele.ofIntegral (fun v => if P v then -(c v / d v) else 1) fun v => by
    split_ifs with hP
    · rw [mem_adicCompletionIntegers, Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ hP zero_le
    · exact one_mem _
  let k11 := FinAdele.ofIntegral (fun v => if P v then 1 else 0) fun v => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hk : !![k00, k01; k10, k11].det = 1 := by
    rw [Matrix.det_fin_two_of]
    refine FiniteAdeleRing.ext _ fun v => ?_
    simp only [FinAdele.sub_apply, FinAdele.mul_apply, FinAdele.one_apply, k00, k01, k10, k11,
      FinAdele.ofIntegral_apply]
    split_ifs <;> ring
  let k := glOfDetOne _ hk
  have hI : ∀ x : 𝔸f, x ∈ ({k00, k01, k10, k11} : Set 𝔸f) → IsIntegralAdele x := by
    rintro x (rfl | rfl | rfl | rfl) <;> exact isIntegralAdele_ofIntegral _ _
  refine ⟨k, mem_K0_of_det_eq_one (det_glOfDetOne _ _) (fun i j => ?_)
    ⟨k10, isIntegralAdele_ofIntegral _ _, by simp [k]⟩, det_glOfDetOne _ _, ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [hI k00 (by simp), hI k01 (by simp), hI k10 (by simp), hI k11 (by simp)]
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    refine FiniteAdeleRing.ext _ fun v => ?_
    simp only [k, coe_glOfDetOne, FinAdele.add_apply, FinAdele.mul_apply, FinAdele.zero_apply,
      k00, k10, FinAdele.ofIntegral_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    split_ifs with hP
    · field_simp [hdP v hP]; ring
    · field_simp [hcP v hP]; ring


/-- Each `g ∈ SL(2, 𝔸f)` is `γ κ` with `γ ∈ SL(2, ℚ)` and `κ ∈ GL(2, Ẑ)`. -/
theorem exists_toFinGL_inv_mul_mem_K0_one {g : GL (Fin 2) 𝔸f}
    (hdet : Matrix.GeneralLinearGroup.det g = 1) :
    ∃ γ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det γ = 1 ∧ (toFinGL γ)⁻¹ * g ∈ K0 1 := by
  obtain ⟨k, hk, hkdet, hgk⟩ := exists_mem_K0_one_mul_lower_eq_zero hdet
  obtain ⟨γ, hγ, hmem⟩ := exists_toFinGL_inv_mul_mem_K0_one_of_upper (b := g * k)
    (by rw [map_mul, hdet, hkdet, one_mul]) hgk
  refine ⟨γ, hγ, ?_⟩
  simpa [mul_assoc] using mul_mem hmem (inv_mem hk)

end Rational

section Integral

/-- The image in `GL(2, 𝔸f)` of an element of `SL(2, ℚ)` has determinant `1`. -/
lemma det_toFinGL_eq_one {γ : GL (Fin 2) ℚ} (h : Matrix.GeneralLinearGroup.det γ = 1) :
    Matrix.GeneralLinearGroup.det (toFinGL γ) = 1 := by
  rw [det_eq_one_iff] at h ⊢
  rw [Matrix.det_fin_two] at h ⊢
  simp only [toFinGL_apply]
  rw [← map_mul, ← map_mul, ← map_sub, h, map_one]

/-- The elementary matrix `!![1, x; 0, 1]` in `GL(2, ℚ)`. -/
noncomputable def elemUpper (x : ℚ) : GL (Fin 2) ℚ :=
  glOfDetOne !![1, x; 0, 1] (by simp [Matrix.det_fin_two])

/-- The elementary matrix `!![1, 0; x, 1]` in `GL(2, ℚ)`. -/
noncomputable def elemLower (x : ℚ) : GL (Fin 2) ℚ :=
  glOfDetOne !![1, 0; x, 1] (by simp [Matrix.det_fin_two])

/-- The determinant of `elemUpper x` is `1`. -/
lemma det_elemUpper (x : ℚ) : Matrix.GeneralLinearGroup.det (elemUpper x) = 1 :=
  det_glOfDetOne _ _

/-- The determinant of `elemLower x` is `1`. -/
lemma det_elemLower (x : ℚ) : Matrix.GeneralLinearGroup.det (elemLower x) = 1 :=
  det_glOfDetOne _ _

/-- Left multiplication by `elemUpper x` adds `x` times the second row to the first row. -/
lemma toFinGL_elemUpper_mul_apply (x : ℚ) (g : GL (Fin 2) 𝔸f) :
    ((toFinGL (elemUpper x) * g : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      !![(g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 + algebraMap ℚ 𝔸f x * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0,
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 + algebraMap ℚ 𝔸f x * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1;
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0, (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1] := by
  refine Matrix.ext fun i j => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, toFinGL_apply, toFinGL_apply]
  fin_cases i <;> fin_cases j <;> simp [elemUpper]

/-- Left multiplication by `elemLower x` adds `x` times the first row to the second row. -/
lemma toFinGL_elemLower_mul_apply (x : ℚ) (g : GL (Fin 2) 𝔸f) :
    ((toFinGL (elemLower x) * g : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      !![(g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0, (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1;
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 + algebraMap ℚ 𝔸f x * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0,
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 + algebraMap ℚ 𝔸f x * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1] := by
  refine Matrix.ext fun i j => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, toFinGL_apply, toFinGL_apply]
  fin_cases i <;> fin_cases j <;> simp [elemLower, add_comm]

/-- An element of `SL(2, ℚ)` with integer entries is in `GL(2, Ẑ)`. -/
lemma toFinGL_mem_K0_one_of_int {γ : GL (Fin 2) ℚ} (h : Matrix.GeneralLinearGroup.det γ = 1)
    (hγ : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j) : toFinGL γ ∈ K0 1 := by
  have hint : ∀ i j, IsIntegralAdele ((toFinGL γ : Matrix (Fin 2) (Fin 2) 𝔸f) i j) := fun i j => by
    rw [toFinGL_apply]; exact (isIntegralAdele_algebraMap_iff _).2 (hγ i j)
  exact mem_K0_of_det_eq_one (det_toFinGL_eq_one h) hint
    ⟨_, hint 1 0, by rw [Nat.cast_one, one_mul]⟩

/-- For an integer `n`, `elemUpper n` is in `GL(2, Ẑ)`. -/
lemma toFinGL_elemUpper_mem (n : ℤ) : toFinGL (elemUpper n) ∈ K0 1 :=
  toFinGL_mem_K0_one_of_int (det_elemUpper _) fun i j => by
    fin_cases i <;> fin_cases j
    exacts [⟨1, by simp [elemUpper]⟩, ⟨n, by simp [elemUpper]⟩, ⟨0, by simp [elemUpper]⟩,
      ⟨1, by simp [elemUpper]⟩]

/-- For an integer `n`, `elemLower n` is in `GL(2, Ẑ)`. -/
lemma toFinGL_elemLower_mem (n : ℤ) : toFinGL (elemLower n) ∈ K0 1 :=
  toFinGL_mem_K0_one_of_int (det_elemLower _) fun i j => by
    fin_cases i <;> fin_cases j
    exacts [⟨1, by simp [elemLower]⟩, ⟨0, by simp [elemLower]⟩, ⟨n, by simp [elemLower]⟩,
      ⟨1, by simp [elemLower]⟩]

/-- If `|x|_v = 1` and `|y|_v < 1`, then `|x + y|_v = 1`. -/
lemma valued_add_eq_one {v : HeightOneSpectrum ℤ} {x y : v.adicCompletion ℚ}
    (hx : Valued.v x = 1) (hy : Valued.v y < 1) : Valued.v (x + y) = 1 :=
  (Valuation.map_add_eq_of_lt_left _ (hx ▸ hy)).trans hx

/-- If `a, b, c, d` are integral at `v`, `a d - b c = 1` and `a` is not a unit at `v`, then `b` and `c` are units at `v`. -/
lemma valued_eq_one_of_det {v : HeightOneSpectrum ℤ} {a b c d : v.adicCompletion ℚ}
    (hb : Valued.v b ≤ 1) (hc : Valued.v c ≤ 1) (hd : Valued.v d ≤ 1)
    (hdet : a * d - b * c = 1) (ha : Valued.v a < 1) : Valued.v b = 1 ∧ Valued.v c = 1 := by
  have h1 : Valued.v b * Valued.v c = 1 := by
    have e : -(b * c) = 1 + -(a * d) := by linear_combination hdet
    rw [← map_mul, ← Valuation.map_neg, e]
    refine valued_add_eq_one (map_one _) ?_
    rw [Valuation.map_neg, map_mul]; exact mul_lt_of_lt_of_le_one ha hd
  constructor
  · refine le_antisymm hb (not_lt.1 fun h => ?_)
    exact (mul_lt_of_lt_of_le_one h hc).ne h1
  · refine le_antisymm hc (not_lt.1 fun h => ?_)
    exact (mul_lt_of_le_one_of_lt hb h).ne h1


/-- The determinant identity of `g ∈ SL(2, 𝔸f)` at the place `v`. -/
lemma det_apply_eq_one {g : GL (Fin 2) 𝔸f} (hdet : Matrix.GeneralLinearGroup.det g = 1)
    (v : HeightOneSpectrum ℤ) :
    (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 v * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v -
      (g : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 v * (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 v = 1 := by
  have h := (det_eq_one_iff g).1 hdet
  rw [Matrix.det_fin_two] at h
  simpa using congrArg (fun x : 𝔸f => x v) h

/-- A natural number is an integral adele. -/
lemma isIntegralAdele_natCast (N : ℕ) : IsIntegralAdele (N : 𝔸f) := by
  exact_mod_cast isIntegralAdele_intCast N

/-- The integral adele with component `0` at the places where `x` is a unit and `1` at the other places. -/
noncomputable def nonunitIndicator (x : 𝔸f) : 𝔸f := by
  classical
  exact FinAdele.ofIntegral (fun v => if Valued.v (x v) = 1 then 0 else 1) fun v => by
    split_ifs
    · exact zero_mem _
    · exact one_mem _

/-- The adele `nonunitIndicator x` is integral. -/
lemma isIntegralAdele_nonunitIndicator (x : 𝔸f) : IsIntegralAdele (nonunitIndicator x) :=
  isIntegralAdele_ofIntegral _ _

/-- At a place where `x` is a unit, `nonunitIndicator x` is `0`. -/
lemma nonunitIndicator_apply_of_eq_one {x : 𝔸f} {v : HeightOneSpectrum ℤ} (h : Valued.v (x v) = 1) :
    nonunitIndicator x v = 0 := by
  simp [nonunitIndicator, h]

/-- At a place where `x` is not a unit, `nonunitIndicator x` is `1`. -/
lemma nonunitIndicator_apply_of_ne_one {x : 𝔸f} {v : HeightOneSpectrum ℤ} (h : Valued.v (x v) ≠ 1) :
    nonunitIndicator x v = 1 := by
  simp [nonunitIndicator, h]

/-- For `κ ∈ SL(2, Ẑ)` there is an integer `s` such that the upper left entry of `elemUpper s * κ` is a unit at all places that divide `N`. -/
lemma exists_elemUpper_valued_eq_one (N : ℕ) [NeZero N] {κ : GL (Fin 2) 𝔸f} (hκ : κ ∈ K0 1)
    (hdet : Matrix.GeneralLinearGroup.det κ = 1) : ∃ s : ℤ, ∀ v, Valued.v ((N : 𝔸f) v) < 1 →
      Valued.v (((toFinGL (elemUpper s) * κ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 v) = 1 := by
  obtain ⟨hint, -, -⟩ := hκ
  set a := (κ : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0
  set c := (κ : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0
  obtain ⟨s, e, he, hse⟩ := exists_int_sub_eq_mul N (isIntegralAdele_nonunitIndicator a)
  refine ⟨s, fun v hv => ?_⟩
  rw [toFinGL_elemUpper_mul_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, map_intCast]
  have hsmall : Valued.v (((N : 𝔸f) * e * c) v) < 1 := by
    rw [FinAdele.mul_apply, FinAdele.mul_apply, map_mul, map_mul]
    exact mul_lt_of_lt_of_le_one (mul_lt_of_lt_of_le_one hv (he v)) (hint 1 0 v)
  have h1 : Valued.v ((a + nonunitIndicator a * c) v) = 1 := by
    rw [FinAdele.add_apply, FinAdele.mul_apply]
    by_cases hav : Valued.v (a v) = 1
    · rw [nonunitIndicator_apply_of_eq_one hav, zero_mul, add_zero, hav]
    · have hav' : Valued.v (a v) < 1 := lt_of_le_of_ne (hint 0 0 v) hav
      have hc1 := (valued_eq_one_of_det (hint 0 1 v) (hint 1 0 v) (hint 1 1 v)
        (det_apply_eq_one hdet v) hav').2
      rw [nonunitIndicator_apply_of_ne_one hav, one_mul, add_comm]
      exact valued_add_eq_one hc1 hav'
  have he' : a + (s : 𝔸f) * c = (a + nonunitIndicator a * c) + -((N : 𝔸f) * e * c) := by
    rw [← hse]; ring
  rw [he', FinAdele.add_apply]
  refine valued_add_eq_one h1 ?_
  rw [FinAdele.neg_apply, Valuation.map_neg]; exact hsmall


/-- Each `κ ∈ SL(2, Ẑ)` is `σ κ'` with `σ ∈ SL(2, ℤ)` and `κ' ∈ K₀(N)`. -/
lemma exists_toFinGL_inv_mul_mem_K0_of_mem_K0_one (N : ℕ) [NeZero N] {κ : GL (Fin 2) 𝔸f}
    (hκ : κ ∈ K0 1) (hdet : Matrix.GeneralLinearGroup.det κ = 1) :
    ∃ σ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det σ = 1 ∧ (toFinGL σ)⁻¹ * κ ∈ K0 N := by
  obtain ⟨s, hs⟩ := exists_elemUpper_valued_eq_one N hκ hdet
  set κ1 := toFinGL (elemUpper s) * κ with hκ1def
  have hκ1 : κ1 ∈ K0 1 := mul_mem (toFinGL_elemUpper_mem s) hκ
  have hdet1 : Matrix.GeneralLinearGroup.det κ1 = 1 := by
    rw [hκ1def, map_mul, det_toFinGL_eq_one (det_elemUpper _), hdet, one_mul]
  have hint1 := hκ1.1
  set a := (κ1 : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0
  set b := (κ1 : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1
  set e := nonunitIndicator a
  have he : IsIntegralAdele e := isIntegralAdele_nonunitIndicator a
  have hkdet : !![1, 0; (N : 𝔸f) * e, 1].det = 1 := by simp [Matrix.det_fin_two]
  set k := glOfDetOne _ hkdet
  have hk : k ∈ K0 N := by
    refine mem_K0_of_det_eq_one (det_glOfDetOne _ _) (fun i j => ?_) ⟨e, he, rfl⟩
    fin_cases i <;> fin_cases j
    exacts [isIntegralAdele_one, isIntegralAdele_zero, (isIntegralAdele_natCast N).mul he,
      isIntegralAdele_one]
  set κ2 := κ1 * k with hκ2def
  have hκ2 : κ2 ∈ K0 1 := mul_mem hκ1 (K0_le_K0_one N hk)
  have hdet2 : Matrix.GeneralLinearGroup.det κ2 = 1 := by
    rw [hκ2def, map_mul, hdet1, det_glOfDetOne, one_mul]
  have h00 : (κ2 : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 = a + b * ((N : 𝔸f) * e) := by
    simp [κ2, k, a, b, Matrix.mul_apply, Fin.sum_univ_two]
  set w := (κ2 : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0
  have hw : ∀ v, Valued.v (w v) = 1 := by
    intro v
    rw [h00, FinAdele.add_apply]
    by_cases hav : Valued.v (a v) = 1
    · simp [e, nonunitIndicator_apply_of_eq_one hav, hav]
    · have hav' : Valued.v (a v) < 1 := lt_of_le_of_ne (hint1 0 0 v) hav
      have hN : Valued.v ((N : 𝔸f) v) = 1 :=
        le_antisymm (isIntegralAdele_natCast N v) (not_lt.1 fun h => hav (hs v h))
      have hb1 := (valued_eq_one_of_det (hint1 0 1 v) (hint1 1 0 v) (hint1 1 1 v)
        (det_apply_eq_one hdet1 v) hav').1
      rw [add_comm]; refine valued_add_eq_one ?_ hav'
      simp only [FinAdele.mul_apply, map_mul, e, nonunitIndicator_apply_of_ne_one hav, hN, mul_one]
      exact hb1
  have hw0 : ∀ v, w v ≠ 0 := fun v h => by simpa [h] using hw v
  set winv := FinAdele.ofIntegral (fun v => (w v)⁻¹) fun v => by
    rw [mem_adicCompletionIntegers, map_inv₀, hw v, inv_one]
  have hwinv : w * winv = 1 := FiniteAdeleRing.ext _ fun v => by
    simp [winv, mul_inv_cancel₀ (hw0 v)]
  obtain ⟨r, f, hf, hrf⟩ := exists_int_sub_eq_mul N
    ((hκ2.1 1 0).mul (isIntegralAdele_ofIntegral _ _ : IsIntegralAdele winv))
  set κ3 := toFinGL (elemLower ((-r : ℤ) : ℚ)) * κ2 with hκ3def
  have hκ3 : κ3 ∈ K0 N := by
    refine mem_K0_of_det_eq_one ?_ (mul_mem (toFinGL_elemLower_mem (-r)) hκ2).1
      ⟨w * f, (hκ2.1 0 0).mul hf, ?_⟩
    · rw [hκ3def, map_mul, det_toFinGL_eq_one (det_elemLower _), hdet2, one_mul]
    · rw [hκ3def, toFinGL_elemLower_mul_apply]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_neg, map_neg, map_intCast]
      linear_combination w * hrf - (κ2 : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * hwinv
  refine ⟨(elemLower ((-r : ℤ) : ℚ) * elemUpper s)⁻¹, ?_, ?_⟩
  · rw [map_inv, map_mul, det_elemLower, det_elemUpper, one_mul, inv_one]
  · have : (toFinGL (elemLower ((-r : ℤ) : ℚ) * elemUpper s)⁻¹)⁻¹ * κ = κ3 * k⁻¹ := by
      rw [hκ3def, hκ2def, hκ1def, map_inv, inv_inv, map_mul]
      group
    rw [this]; exact mul_mem hκ3 (inv_mem hk)

end Integral

section StrongApproximation

/-- **Strong approximation for `SL(2)` at level `K₀(N)`.** For `N ≥ 1`, each `g ∈ SL(2, 𝔸f)` is `γ κ` with `γ ∈ SL(2, ℚ)` and `κ ∈ K₀(N)`. This is Theorem 1.2.2 and Corollary 1.2.3 of the handbook for `SL(2)`. -/
theorem sl2StrongApprox (N : ℕ) [NeZero N] : SL2StrongApprox N := by
  intro g hg
  obtain ⟨γ, hγ, hκ⟩ := exists_toFinGL_inv_mul_mem_K0_one hg
  have hdetκ : Matrix.GeneralLinearGroup.det ((toFinGL γ)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, det_toFinGL_eq_one hγ, hg, inv_one, one_mul]
  obtain ⟨σ, hσ, hmem⟩ := exists_toFinGL_inv_mul_mem_K0_of_mem_K0_one N hκ hdetκ
  exact ⟨γ * σ, by rw [map_mul, hγ, hσ, one_mul], by rwa [map_mul, mul_inv_rev, mul_assoc]⟩


/-- **Theorem 1.2.5, finite part.** For `N ≥ 1`, `GL(2, 𝔸f) = GL(2, ℚ) K₀(N)`. -/
theorem exists_toFinGL_inv_mul_mem_K0' (N : ℕ) [NeZero N] (g : GL (Fin 2) 𝔸f) :
    ∃ γ : GL (Fin 2) ℚ, (toFinGL γ)⁻¹ * g ∈ K0 N :=
  exists_toFinGL_inv_mul_mem_K0 (sl2StrongApprox N) g

/-- **Theorem 1.2.5.** For `N ≥ 1`, `GL(2, 𝔸) = GL(2, ℚ) GL(2, ℝ)⁺ K₀(N)`: each `g` is `γ (h, 1) (1, κ)` with `γ ∈ GL(2, ℚ)`, `det h > 0` and `κ ∈ K₀(N)`. -/
theorem exists_isDecomp' (N : ℕ) [NeZero N] (g : AdelicGL2) : ∃ γ h κ, IsDecomp N g γ h κ :=
  exists_isDecomp (sl2StrongApprox N) g

end StrongApproximation

section Lift

variable {N : ℕ} {k : ℤ}

local notation "Γ₀" => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The lift `φ_f` is the only function on `GL(2, 𝔸)` with `φ(γ (h, 1) (1, κ)) = (f ‖ₖ h)(i)` for all `γ ∈ GL(2, ℚ)`, `h` with `det h > 0` and `κ ∈ K₀(N)`. -/
theorem eq_adelicLift' [NeZero N] (f : ModularForm Γ₀ k) (φ : AdelicGL2 → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) (κ : GL (Fin 2) 𝔸f),
      0 < h.det.val → κ ∈ K0 N → φ (principalGL2 γ * (h, 1) * (1, κ)) = unitarySlashAtI k f h) :
    φ = adelicLift N k f :=
  eq_adelicLift (sl2StrongApprox N) f φ hφ

end Lift

end Langlands.Modular
