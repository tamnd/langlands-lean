/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.Induction

/-!
# The principal series of GL(2)

Let $K$ be a nonarchimedean local field, $G = GL_2(K)$, $B$ the Borel subgroup of the upper triangular matrices, $N$ its unipotent radical, $T$ the diagonal torus and $K_0 = GL_2(\mathcal{O}_K)$. This file continues `Langlands/Smooth/Induction.lean`. It gives the modulus character $\delta_B$ and the normalized principal series, the Iwasawa decomposition $G = B K_0$, the admissibility of the principal series, a quotient of dimension one of its Jacquet module, and the right exactness of the Jacquet functor.

## Main definitions

* `Langlands.unitGroup`: the subgroup $\mathcal{O}_K^\times$ of $K^\times$.
* `Langlands.absChar`, `Langlands.sqrtAbsChar`: the characters $|\cdot|$ and $|\cdot|^{1/2}$ of $K^\times$.
* `Langlands.GL2.modulus`, `Langlands.GL2.sqrtModulus`: the characters $\delta_B(b) = |a/d|$ and $\delta_B^{1/2}$ of $B$, for $b$ with diagonal $(a, d)$.
* `Langlands.normPrincipalSeries`: the normalized principal series $\mathrm{Ind}_B^G((\chi_1 \otimes \chi_2)\delta_B^{1/2})$.
* `Langlands.GL2.maxCompact`: the subgroup $K_0 = GL_2(\mathcal{O}_K)$.
* `Langlands.GL2.congruence`: the open subgroup of the $g$ such that the entries of $g - 1$ and $g^{-1} - 1$ have valuation less than $\gamma$.
* `Langlands.GL2.torusChar`: the character $\chi_1 \otimes \chi_2$ of $T$.
* `Langlands.principalSeriesEval`: evaluation at $1$, as an $N$-invariant map of representations of $T$.
* `Langlands.principalSeriesJacquetEval`: the map from the Jacquet module of the principal series to $\chi_1 \otimes \chi_2$ that evaluation at $1$ gives.

## Main results

* `Langlands.normAbs_mul`: the absolute value is multiplicative.
* `Langlands.GL2.modulus_apply`, `Langlands.GL2.sqrtModulus_sq`: $\delta_B(b) = |a/d|$ and $(\delta_B^{1/2})^2 = \delta_B$.
* `Langlands.GL2.conj_unipotent_val`: conjugation by $b$ multiplies the coordinate of $N \cong K$ by $a/d$.
* `Langlands.normPrincipalSeries_eq`: the normalized principal series of $(\chi_1, \chi_2)$ is `principalSeriesInd` of $(\chi_1|\cdot|^{1/2}, \chi_2|\cdot|^{-1/2})$.
* `Langlands.normPrincipalSeries_iso`: it is isomorphic to `Langlands.principalSeries K χ₁ χ₂` of `Langlands/Statements/Smooth.lean`.
* `Langlands.GL2.isCompact_maxCompact`: $K_0$ is compact.
* `Langlands.GL2.iwasawa`: the Iwasawa decomposition $G = B K_0$.
* `Langlands.SmoothRep.ind_borel_ext`: a vector of a representation induced from $B$ is determined by its restriction to $K_0$.
* `Langlands.SmoothRep.ind_isAdmissible`: if $G = HC$ with $C$ compact, then the induction from $H$ of a representation of finite dimension is admissible.
* `Langlands.principalSeriesInd_isAdmissible`, `Langlands.normPrincipalSeries_isAdmissible`, `Langlands.principalSeries_isAdmissible`: the principal series are admissible.
* `Langlands.principalSeriesInd_nontrivial`: the principal series is not zero.
* `Langlands.principalSeriesJacquetEval_surjective`: the Jacquet module of $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ maps onto $\chi_1 \otimes \chi_2$.
* `Langlands.SmoothRep.jacquetMap_exact`: the Jacquet functor is right exact.

## Implementation notes

The admissibility holds for each open subgroup $U$ of $G$, not only for the subgroups of $K_0$. The proof does not use the double cosets $B \backslash G / U$. It covers the compact set $K_0$ by finitely many cosets $xU$, and a vector of $V^U$ is then determined by its values at these points $x$.

The vector with $f(1) = 1$ has support $BU$ for a congruence subgroup $U$ on which $\chi_1 \otimes \chi_2$ is trivial. The subgroup $U$ comes from `Langlands.IsSmoothChar.exists_valuation_sub_one`.

The file does not prove that the Jacquet module has dimension two, with the semisimplification $\chi_1 \otimes \chi_2$ and its Weyl conjugate twisted by $\delta_B$. This needs the Bruhat decomposition $G = B \sqcup BwN$ and the computation of the Jacquet module of the functions with support in the open cell, which uses integration over $N$. The left exactness of the Jacquet functor needs the description of $V(N)$ by the vanishing of the integrals over the compact open subgroups of $N$ (Jacquet's lemma). The file does not prove these. It also does not identify $\delta_B$ with the modulus of a Haar measure of $B$. It only gives the scaling of the coordinate of $N$ under conjugation.

## References

* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapter 2.
* W. Casselman, Introduction to the theory of admissible representations of p-adic reductive groups, unpublished notes, 1995.
-/

namespace Langlands

universe u

open Representation Matrix ValuativeRel

section Admissible

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- If $G = H C$ for a subset $C$, then a vector of $\mathrm{Ind}_H^G \sigma$ is determined by its values on $C$. -/
theorem ind_ext_of_eqOn {H : Subgroup G} {σ : SmoothRep H} {C : Set G}
    (hC : ∀ g, ∃ h : H, ∃ c ∈ C, g = h * c) {f f' : (ind H σ).V}
    (hf : ∀ c ∈ C, ind.toFun f c = ind.toFun f' c) : f = f' := by
  refine ind.toFun_injective (funext fun g => ?_)
  obtain ⟨h, c, hc, rfl⟩ := hC g
  rw [ind.toFun_mul_left, ind.toFun_mul_left, hf c hc]

/-- If $G = H C$ for a compact subset $C$ and $\sigma$ has finite dimension, then $\mathrm{Ind}_H^G \sigma$ is admissible. The space $V^U$ embeds into $W^t$, where $t$ is a finite subset of $C$ with $C \subseteq t U$. -/
theorem ind_isAdmissible {H : Subgroup G} {σ : SmoothRep H} [FiniteDimensional ℂ σ.V]
    {C : Set G} (hCc : IsCompact C) (hC : ∀ g, ∃ h : H, ∃ c ∈ C, g = h * c) :
    (ind H σ).IsAdmissible := by
  intro U hU
  obtain ⟨t, -, ht⟩ := hCc.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (U : Set G))
    (fun x _ => ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds
      (by simp [U.one_mem]))
  let φ : fixedVectors (ind H σ).ρ U →ₗ[ℂ] (t → σ.V) :=
    { toFun := fun f x => ind.toFun f.1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective φ fun f f' hff' => Subtype.ext ?_
  refine ind_ext_of_eqOn hC fun c hc => ?_
  obtain ⟨x, hxt, hcx⟩ := Set.mem_iUnion₂.1 (ht hc)
  have hu : x⁻¹ * c ∈ U := hcx
  have key : ∀ F : fixedVectors (ind H σ).ρ U, ind.toFun F.1 c = ind.toFun F.1 x := by
    intro F
    have := congrArg (fun v => ind.toFun v x) (F.2 _ hu)
    simp only [ind.toFun_ρ, mul_inv_cancel_left] at this
    exact this
  rw [key f, key f']
  exact congrFun hff' ⟨x, hxt⟩

end SmoothRep

end Admissible

section Abs

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The residue field of $K$ has at least one element. -/
theorem residueCard_pos : 0 < residueCard K := by
  unfold residueCard
  exact Nat.card_pos

variable {K}

/-- For $x \neq 0$ the absolute value is $q^{-v(x)}$. -/
theorem normAbs_of_ne_zero {x : K} (hx : x ≠ 0) :
    normAbs K x = (residueCard K : ℝ) ^ WithZero.log
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x)) :=
  ite_eq_right hx

/-- The absolute value of a nonzero element is positive. -/
theorem normAbs_pos {x : K} (hx : x ≠ 0) : 0 < normAbs K x := by
  rw [normAbs_of_ne_zero hx]
  exact zpow_pos (by exact_mod_cast residueCard_pos K) _

/-- The absolute value is not negative. -/
theorem normAbs_nonneg (x : K) : 0 ≤ normAbs K x := by
  by_cases hx : x = 0
  · simp [normAbs, hx]
  · exact (normAbs_pos hx).le

/-- The absolute value is multiplicative: $|xy| = |x||y|$. -/
theorem normAbs_mul (x y : K) : normAbs K (x * y) = normAbs K x * normAbs K y := by
  by_cases hx : x = 0
  · simp [normAbs, hx]
  by_cases hy : y = 0
  · simp [normAbs, hy]
  rw [normAbs_of_ne_zero (mul_ne_zero hx hy), normAbs_of_ne_zero hx, normAbs_of_ne_zero hy,
    map_mul, map_mul, WithZero.log_mul, zpow_add₀]
  · exact_mod_cast (residueCard_pos K).ne'
  · simpa using hx
  · simpa using hy

/-- The absolute value of $1$ is $1$. -/
theorem normAbs_one : normAbs K 1 = 1 := by
  simp [normAbs]

/-- The absolute value of a quotient: $|x/y| = |x|/|y|$. -/
theorem normAbs_div (x y : K) : normAbs K (x / y) = normAbs K x / normAbs K y := by
  by_cases hy : y = 0
  · simp [normAbs, hy]
  rw [eq_div_iff (normAbs_pos hy).ne', ← normAbs_mul, div_mul_cancel₀ _ hy]

/-- An element with valuation $1$ has absolute value $1$. -/
theorem normAbs_eq_one {x : K} (hx : valuation K x = 1) : normAbs K x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rw [normAbs_of_ne_zero hx0, hx, map_one, WithZero.log_one, zpow_zero]

/-- The set $\{x : v(x - y) < \gamma\}$ is open for each $y$ and each $\gamma$. -/
theorem isOpen_valuation_sub_lt (y : K) (γ : ValueGroupWithZero K) :
    IsOpen {x : K | valuation K (x - y) < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hx)
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
  change valuation K (z - x) < γ at hz
  change valuation K (z - y) < γ
  rw [show z - y = (z - x) + (x - y) by ring]
  exact Valuation.map_add_lt _ hz hx

/-- The elements of valuation $1$ form an open subset of $K$. -/
theorem isOpen_valuation_eq_one : IsOpen {x : K | valuation K x = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation K x = 1 at hx
  have := (valuation K).locally_const (x := x) (by rw [hx]; exact one_ne_zero)
  rwa [hx] at this

variable (K)

/-- The character $x \mapsto |x|$ of $K^\times$. -/
noncomputable def absChar : Kˣ →* ℂˣ where
  toFun x := Units.mk0 ((normAbs K x : ℝ) : ℂ) (by exact_mod_cast (normAbs_pos x.ne_zero).ne')
  map_one' := Units.ext (by simp [normAbs_one])
  map_mul' x y := Units.ext (by simp [normAbs_mul])

/-- The character $x \mapsto |x|^{1/2}$ of $K^\times$. -/
noncomputable def sqrtAbsChar : Kˣ →* ℂˣ where
  toFun x := Units.mk0 ((Real.sqrt (normAbs K x) : ℝ) : ℂ)
    (by exact_mod_cast (Real.sqrt_pos.2 (normAbs_pos x.ne_zero)).ne')
  map_one' := Units.ext (by simp [normAbs_one])
  map_mul' x y := Units.ext (by simp [normAbs_mul, Real.sqrt_mul (normAbs_nonneg _)])

variable {K}

/-- The value of `absChar` is $|x|$. -/
theorem absChar_apply (x : Kˣ) : (absChar K x : ℂ) = (normAbs K x : ℂ) :=
  rfl

/-- The value of `sqrtAbsChar` is $|x|^{1/2}$. -/
theorem sqrtAbsChar_apply (x : Kˣ) : (sqrtAbsChar K x : ℂ) = (Real.sqrt (normAbs K x) : ℂ) :=
  rfl

/-- The square of $|\cdot|^{1/2}$ is $|\cdot|$. -/
theorem sqrtAbsChar_sq : sqrtAbsChar K ^ 2 = absChar K := by
  ext x
  simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, sqrtAbsChar_apply, absChar_apply]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (normAbs_nonneg _)]

variable (K) in
/-- The subgroup $\mathcal{O}_K^\times$ of $K^\times$: the units of valuation $1$. -/
def unitGroup : Subgroup Kˣ where
  carrier := {x | valuation K (x : K) = 1}
  mul_mem' {a b} ha hb := by
    change valuation K ((a * b : Kˣ) : K) = 1
    change valuation K (a : K) = 1 at ha
    change valuation K (b : K) = 1 at hb
    rw [Units.val_mul, map_mul, ha, hb, one_mul]
  one_mem' := by
    change valuation K ((1 : Kˣ) : K) = 1
    simp
  inv_mem' {a} ha := by
    change valuation K ((a⁻¹ : Kˣ) : K) = 1
    change valuation K (a : K) = 1 at ha
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

/-- The subgroup $\mathcal{O}_K^\times$ is open in $K^\times$. -/
theorem isOpen_unitGroup : IsOpen (unitGroup K : Set Kˣ) :=
  Units.continuous_val.isOpen_preimage _ isOpen_valuation_eq_one

/-- A character of $K^\times$ that is trivial on $\mathcal{O}_K^\times$ is smooth. -/
theorem isSmoothChar_of_unitGroup {χ : Kˣ →* ℂˣ} (h : ∀ x ∈ unitGroup K, χ x = 1) :
    IsSmoothChar K χ :=
  Subgroup.isOpen_mono (H₁ := unitGroup K) (fun x hx => h x hx) isOpen_unitGroup

/-- The character $|\cdot|$ is smooth. -/
theorem isSmoothChar_absChar : IsSmoothChar K (absChar K) :=
  isSmoothChar_of_unitGroup fun x hx => Units.ext (by
    change ((normAbs K x : ℝ) : ℂ) = 1
    rw [normAbs_eq_one hx, Complex.ofReal_one])

/-- The character $|\cdot|^{1/2}$ is smooth. -/
theorem isSmoothChar_sqrtAbsChar : IsSmoothChar K (sqrtAbsChar K) :=
  isSmoothChar_of_unitGroup fun x hx => Units.ext (by
    change ((Real.sqrt (normAbs K x) : ℝ) : ℂ) = 1
    rw [normAbs_eq_one hx, Real.sqrt_one, Complex.ofReal_one])

/-- The product of two smooth characters is smooth. -/
theorem IsSmoothChar.mul {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ') :
    IsSmoothChar K (χ * χ') := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ'.ker) ?_ (hχ.inter hχ')
  intro x hx
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, mul_one]

/-- The inverse of a smooth character is smooth. -/
theorem IsSmoothChar.inv {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) : IsSmoothChar K χ⁻¹ := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker) ?_ hχ
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, MonoidHom.inv_apply, hx, inv_one]

end Abs

section Iwasawa

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

/-- A $2 \times 2$ matrix is integral if each entry has valuation at most $1$. -/
def IsIntegralMatrix (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ i j, valuation K (M i j) ≤ 1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The product of two integral matrices is integral. -/
theorem IsIntegralMatrix.mul {M M' : Matrix (Fin 2) (Fin 2) K} (h : IsIntegralMatrix M)
    (h' : IsIntegralMatrix M') : IsIntegralMatrix (M * M') := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (h i k) (h' k j)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The identity matrix is integral. -/
theorem isIntegralMatrix_one : IsIntegralMatrix (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

variable (K) in
/-- The maximal compact subgroup $GL_2(\mathcal{O}_K)$ of $GL_2(K)$: the elements $g$ such that $g$ and $g^{-1}$ are integral. -/
def maxCompact : Subgroup (GL (Fin 2) K) where
  carrier := {g | IsIntegralMatrix g.1 ∧ IsIntegralMatrix (g⁻¹).1}
  mul_mem' {a b} ha hb :=
    ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
      by rw [_root_.mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  one_mem' := ⟨by simpa using isIntegralMatrix_one, by simpa using isIntegralMatrix_one⟩
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element is in $GL_2(\mathcal{O}_K)$ exactly when it and its inverse are integral. -/
theorem mem_maxCompact (g : GL (Fin 2) K) :
    g ∈ maxCompact K ↔ IsIntegralMatrix g.1 ∧ IsIntegralMatrix (g⁻¹).1 :=
  Iff.rfl

/-- The subgroup $GL_2(\mathcal{O}_K)$ is compact. Its image in $M_2(K) \times M_2(K)^{op}$ is the closed subset of the pairs $(A, B)$ with $AB = BA = 1$ in the compact set of the pairs of integral matrices. -/
theorem isCompact_maxCompact : IsCompact (maxCompact K : Set (GL (Fin 2) K)) := by
  let A : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => {x : K | valuation K x ≤ 1}
  have hA : IsCompact A := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hE : IsClosed {p : Matrix (Fin 2) (Fin 2) K × (Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ |
      p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    have h2 : Continuous fun p : Matrix (Fin 2) (Fin 2) K × (Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ =>
        p.2.unop := MulOpposite.continuous_unop.comp continuous_snd
    exact (isClosed_eq (continuous_fst.mul h2) continuous_const).inter
      (isClosed_eq (h2.mul continuous_fst) continuous_const)
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  convert (hA.prod (hA.image MulOpposite.continuous_op)).inter_right hE using 1
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨fun i _ j _ => hg.1 i j, ⟨(g⁻¹).1, fun i _ j _ => hg.2 i j, rfl⟩⟩, g.mul_inv, g.inv_mul⟩
  · rintro ⟨⟨h1, ⟨B, hB, hBp⟩⟩, e1, e2⟩
    refine ⟨⟨p.1, p.2.unop, e1, e2⟩, ⟨fun i j => h1 i trivial j trivial, ?_⟩, rfl⟩
    intro i j
    change valuation K (p.2.unop i j) ≤ 1
    rw [← hBp]
    exact hB i trivial j trivial

/-- The matrix $\begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$ of $GL_2(K)$. -/
def lowerUnip (c : K) : GL (Fin 2) K :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

/-- The matrix $\begin{pmatrix} 0 & -1 \\ 1 & c \end{pmatrix}$ of $GL_2(K)$. -/
def weylShear (c : K) : GL (Fin 2) K :=
  ⟨!![0, -1; 1, c], !![c, 1; -1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $v(c) \le 1$ the matrix $\begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$ is in $GL_2(\mathcal{O}_K)$. -/
theorem lowerUnip_mem {c : K} (hc : valuation K c ≤ 1) : lowerUnip c ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change valuation K (!![1, 0; c, 1] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hc]
  · change valuation K (!![1, 0; -c, 1] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hc]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $v(c) \le 1$ the matrix $\begin{pmatrix} 0 & -1 \\ 1 & c \end{pmatrix}$ is in $GL_2(\mathcal{O}_K)$. -/
theorem weylShear_mem {c : K} (hc : valuation K c ≤ 1) : weylShear c ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change valuation K (!![0, -1; 1, c] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hc]
  · change valuation K (!![c, 1; -1, 0] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hc]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Iwasawa decomposition $GL_2(K) = B(K) \, GL_2(\mathcal{O}_K)$: each $g$ is $bk$ with $b$ upper triangular and $k \in GL_2(\mathcal{O}_K)$. For the lower row $(r, s)$ of $g$, take $k = \begin{pmatrix} 1 & 0 \\ r/s & 1 \end{pmatrix}$ if $v(r) \le v(s)$, and $k = \begin{pmatrix} 0 & -1 \\ 1 & s/r \end{pmatrix}$ otherwise. -/
theorem iwasawa (g : GL (Fin 2) K) : ∃ b ∈ borel K, ∃ k ∈ maxCompact K, g = b * k := by
  suffices h : ∃ k ∈ maxCompact K, g * k⁻¹ ∈ borel K by
    obtain ⟨k, hk, hb⟩ := h
    exact ⟨_, hb, k, hk, by simp⟩
  have hdet := det_ne_zero g
  rw [Matrix.det_fin_two] at hdet
  rcases le_or_gt (valuation K (g.1 1 0)) (valuation K (g.1 1 1)) with h | h
  · have hs : g.1 1 1 ≠ 0 := by
      intro hs
      rw [hs, map_zero, le_zero_iff, map_eq_zero] at h
      apply hdet
      rw [h, hs]
      ring
    have hc : valuation K (g.1 1 0 / g.1 1 1) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    refine ⟨lowerUnip (g.1 1 0 / g.1 1 1), lowerUnip_mem hc, ?_⟩
    rw [mem_borel]
    change (g.1 * !![1, 0; -(g.1 1 0 / g.1 1 1), 1]) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · have hr : g.1 1 0 ≠ 0 := by
      intro hr
      rw [hr, map_zero] at h
      exact (not_lt.2 zero_le) h
    have hc : valuation K (g.1 1 1 / g.1 1 0) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h.le zero_le
    refine ⟨weylShear (g.1 1 1 / g.1 1 0), weylShear_mem hc, ?_⟩
    rw [mem_borel]
    change (g.1 * !![g.1 1 1 / g.1 1 0, 1; -1, 0]) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Iwasawa decomposition, in the form that `Langlands.SmoothRep.ind_isAdmissible` uses. -/
theorem exists_borel_mul_maxCompact (g : GL (Fin 2) K) :
    ∃ b : borel K, ∃ k ∈ (maxCompact K : Set (GL (Fin 2) K)), g = b * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := iwasawa g
  exact ⟨⟨b, hb⟩, k, hk, rfl⟩

end GL2

open GL2

namespace SmoothRep

/-- A vector of a representation induced from $B$ is determined by its restriction to $GL_2(\mathcal{O}_K)$. -/
theorem ind_borel_ext {σ : SmoothRep (borel K)} {f f' : (ind (borel K) σ).V}
    (h : ∀ k ∈ maxCompact K, ind.toFun f k = ind.toFun f' k) : f = f' :=
  ind_ext_of_eqOn exists_borel_mul_maxCompact h

/-- The induction from $B$ of a smooth representation of finite dimension is admissible. -/
theorem ind_borel_isAdmissible (σ : SmoothRep (borel K)) [FiniteDimensional ℂ σ.V] :
    (ind (borel K) σ).IsAdmissible :=
  ind_isAdmissible isCompact_maxCompact exists_borel_mul_maxCompact

/-- An isomorphism of smooth representations keeps admissibility. -/
theorem IsAdmissible.of_iso {G : Type u} [Group G] [TopologicalSpace G] {π π' : SmoothRep G}
    (hπ : π.IsAdmissible) (e : π.Iso π') : π'.IsAdmissible := by
  obtain ⟨e, he⟩ := e
  intro U hU
  have := hπ U hU
  let f : fixedVectors π'.ρ U →ₗ[ℂ] fixedVectors π.ρ U :=
    { toFun := fun w => ⟨e.symm w.1, fun g hg => e.injective (by
        rw [he, LinearEquiv.apply_symm_apply, w.2 g hg])⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  refine FiniteDimensional.of_injective f fun a b hab => Subtype.ext ?_
  exact e.symm.injective (congrArg Subtype.val hab)

end SmoothRep

/-- The principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ is admissible. -/
theorem principalSeriesInd_isAdmissible {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).IsAdmissible := by
  have : FiniteDimensional ℂ (SmoothRep.charRep (borelChar χ₁ χ₂)
      (isOpen_ker_borelChar hχ₁ hχ₂)).V := inferInstanceAs (FiniteDimensional ℂ (ULift.{u} ℂ))
  exact SmoothRep.ind_borel_isAdmissible _

end Iwasawa

section Normalized

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The product of two characters $\chi_1 \otimes \chi_2$ and $\chi'_1 \otimes \chi'_2$ of $B$ is $\chi_1\chi'_1 \otimes \chi_2\chi'_2$. -/
theorem borelChar_mul (χ₁ χ₂ χ₁' χ₂' : Kˣ →* ℂˣ) :
    borelChar χ₁ χ₂ * borelChar χ₁' χ₂' = borelChar (χ₁ * χ₁') (χ₂ * χ₂') := by
  ext b
  simp only [MonoidHom.mul_apply, borelChar_apply]
  push_cast
  ring

variable (K) in
/-- The modulus character $\delta_B$ of $B$: $\delta_B(b) = |a/d|$ for $b$ with diagonal $(a, d)$. It is the character $|\cdot| \otimes |\cdot|^{-1}$. -/
noncomputable def modulus : borel K →* ℂˣ :=
  borelChar (absChar K) (absChar K)⁻¹

variable (K) in
/-- The square root $\delta_B^{1/2}$ of the modulus character: $b \mapsto |a/d|^{1/2}$. -/
noncomputable def sqrtModulus : borel K →* ℂˣ :=
  borelChar (sqrtAbsChar K) (sqrtAbsChar K)⁻¹

/-- The value of the modulus character is $\delta_B(b) = |a/d|$. -/
theorem modulus_apply (b : borel K) :
    (modulus K b : ℂ) = (normAbs K (b.1.1 0 0 / b.1.1 1 1) : ℂ) := by
  rw [modulus, borelChar_apply, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    absChar_apply, absChar_apply, val_diagFst, val_diagSnd, normAbs_div, Complex.ofReal_div,
    div_eq_mul_inv]

/-- The value of $\delta_B^{1/2}$ is $|a/d|^{1/2}$. -/
theorem sqrtModulus_apply (b : borel K) :
    (sqrtModulus K b : ℂ) = (Real.sqrt (normAbs K (b.1.1 0 0 / b.1.1 1 1)) : ℂ) := by
  rw [sqrtModulus, borelChar_apply, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    sqrtAbsChar_apply, sqrtAbsChar_apply, val_diagFst, val_diagSnd, normAbs_div,
    Real.sqrt_div' _ (normAbs_nonneg _), Complex.ofReal_div, div_eq_mul_inv]

/-- The square of $\delta_B^{1/2}$ is $\delta_B$. -/
theorem sqrtModulus_sq : sqrtModulus K ^ 2 = modulus K := by
  ext b
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, sqrtModulus_apply, modulus_apply,
    ← Complex.ofReal_pow, Real.sq_sqrt (normAbs_nonneg _)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Conjugation by $b \in B$ multiplies the upper right entry of $n \in N$ by $a/d$: $b n(x) b^{-1} = n(ax/d)$. Thus $\delta_B(b) = |a/d|$ is the factor by which conjugation by $b$ scales a Haar measure of $N \cong K$. -/
theorem conj_unipotent_val (b : borel K) {n : GL (Fin 2) K} (hn : n ∈ unipotent K) :
    ((b : GL (Fin 2) K) * n * (b : GL (Fin 2) K)⁻¹).1 0 1 =
      b.1.1 0 0 / b.1.1 1 1 * n.1 0 1 := by
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have hb := b.2
  rw [mem_borel] at hb
  have ha := val_zero_zero_ne_zero b.2
  have hd := val_one_one_ne_zero b.2
  rw [Units.val_mul, Units.val_mul, val_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, hb, hn1, hn2, hn3]
  field_simp
  ring

/-- The character $\delta_B$ is smooth. -/
theorem isOpen_ker_modulus : IsOpen ((modulus K).ker : Set (borel K)) :=
  isOpen_ker_borelChar isSmoothChar_absChar isSmoothChar_absChar.inv

/-- The character $\delta_B^{1/2}$ is smooth. -/
theorem isOpen_ker_sqrtModulus : IsOpen ((sqrtModulus K).ker : Set (borel K)) :=
  isOpen_ker_borelChar isSmoothChar_sqrtAbsChar isSmoothChar_sqrtAbsChar.inv

/-- The character $(\chi_1 \otimes \chi_2) \delta_B^{1/2}$ is $\chi_1 |\cdot|^{1/2} \otimes \chi_2 |\cdot|^{-1/2}$. -/
theorem borelChar_mul_sqrtModulus (χ₁ χ₂ : Kˣ →* ℂˣ) :
    borelChar χ₁ χ₂ * sqrtModulus K =
      borelChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹) :=
  borelChar_mul _ _ _ _

/-- For smooth $\chi_1, \chi_2$ the character $(\chi_1 \otimes \chi_2) \delta_B^{1/2}$ is smooth. -/
theorem isOpen_ker_borelChar_mul_sqrtModulus {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    IsOpen ((borelChar χ₁ χ₂ * sqrtModulus K).ker : Set (borel K)) := by
  rw [borelChar_mul_sqrtModulus]
  exact isOpen_ker_borelChar (hχ₁.mul isSmoothChar_sqrtAbsChar)
    (hχ₂.mul isSmoothChar_sqrtAbsChar.inv)

end GL2

open GL2

/-- Two equal characters give the same representation of dimension one. -/
theorem SmoothRep.charRep_congr {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {θ θ' : G →* ℂˣ} (h : θ = θ') (hθ : IsOpen (θ.ker : Set G))
    (hθ' : IsOpen (θ'.ker : Set G)) : SmoothRep.charRep θ hθ = SmoothRep.charRep θ' hθ' := by
  subst h
  rfl

/-- The normalized principal series $\mathrm{Ind}_B^G((\chi_1 \otimes \chi_2)\delta_B^{1/2})$ of $GL_2(K)$: the functions $f$ with $f(bg) = \chi_1(a)\chi_2(d)|a/d|^{1/2} f(g)$ for each $b \in B$ with diagonal $(a, d)$, that are invariant on the right under an open subgroup. -/
noncomputable def normPrincipalSeries (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : SmoothRep (GL (Fin 2) K) :=
  SmoothRep.ind (borel K) (SmoothRep.charRep (borelChar χ₁ χ₂ * sqrtModulus K)
    (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂))

/-- The normalized principal series of $(\chi_1, \chi_2)$ is the unnormalized principal series of $(\chi_1 |\cdot|^{1/2}, \chi_2 |\cdot|^{-1/2})$. -/
theorem normPrincipalSeries_eq {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂ =
      principalSeriesInd (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹)
        (hχ₁.mul isSmoothChar_sqrtAbsChar) (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) := by
  unfold normPrincipalSeries principalSeriesInd
  rw [SmoothRep.charRep_congr (borelChar_mul_sqrtModulus χ₁ χ₂)]

/-- The functions of the normalized principal series satisfy $f(bg) = \chi_1(a)\chi_2(d)|a/d|^{1/2} f(g)$. -/
theorem normPrincipalSeries_mul_left {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁}
    {hχ₂ : IsSmoothChar K χ₂} (f : (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).V) (b : borel K)
    (g : GL (Fin 2) K) :
    SmoothRep.ind.toFun f (b * g) =
      ((χ₁ (diagFst b) : ℂ) * χ₂ (diagSnd b) *
        (Real.sqrt (normAbs K (b.1.1 0 0 / b.1.1 1 1)) : ℂ)) • SmoothRep.ind.toFun f g := by
  rw [SmoothRep.ind.toFun_mul_left (H := borel K) (σ := SmoothRep.charRep
    (borelChar χ₁ χ₂ * sqrtModulus K) (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂)) f b g]
  change (((borelChar χ₁ χ₂ * sqrtModulus K) b : ℂˣ) : ℂ) • (_ : ULift ℂ) = _
  rw [MonoidHom.mul_apply, Units.val_mul, borelChar_apply, Units.val_mul, sqrtModulus_apply]
  rfl

/-- The normalized principal series is isomorphic to the representation `Langlands.principalSeries K χ₁ χ₂` of `Langlands/Statements/Smooth.lean`. The isomorphism sends $f$ to $g \mapsto f(g)$, with the values in $\mathbb{C}$. -/
theorem normPrincipalSeries_iso {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).Iso (principalSeries K χ₁ χ₂) := by
  let π := normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂
  let e : π.V ≃ₗ[ℂ] principalSeriesSpace K χ₁ χ₂ :=
    { toFun := fun f => ⟨fun g => (SmoothRep.ind.toFun f g).down, fun b g a d h1 h2 h3 => by
          have := normPrincipalSeries_mul_left f ⟨b, h1⟩ g
          have ha : diagFst (⟨b, h1⟩ : borel K) = a := Units.ext h2
          have hd : diagSnd (⟨b, h1⟩ : borel K) = d := Units.ext h3
          rw [ha, hd] at this
          change (SmoothRep.ind.toFun f (b * g)).down = _
          rw [this]
          change _ * _ = _
          simp only [h2, h3],
        by
          obtain ⟨U, hU, hfU⟩ := (show indSpace _ _ from f).2.2
          exact ⟨U, hU, fun g u hu => by
            change (SmoothRep.ind.toFun f (g * u)).down = (SmoothRep.ind.toFun f g).down
            rw [show SmoothRep.ind.toFun f (g * u) = SmoothRep.ind.toFun f g from hfU g u hu]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun φ => show indSpace _ _ from
        ⟨fun g => ULift.up (φ.1 g), fun b g => by
            apply ULift.ext
            change φ.1 (b * g) = ((borelChar χ₁ χ₂ * sqrtModulus K) b : ℂ) * φ.1 g
            rw [φ.2.1 b g (diagFst b) (diagSnd b) b.2 rfl rfl, MonoidHom.mul_apply, Units.val_mul,
              borelChar_apply, Units.val_mul, sqrtModulus_apply, val_diagFst, val_diagSnd],
          by
            obtain ⟨U, hU, hφU⟩ := φ.2.2
            exact ⟨U, hU, fun g u hu => by
              change ULift.up (φ.1 (g * u)) = ULift.up (φ.1 g)
              rw [hφU g u hu]⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨e, fun _ _ => rfl⟩

/-- The normalized principal series is admissible. -/
theorem normPrincipalSeries_isAdmissible {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).IsAdmissible := by
  rw [normPrincipalSeries_eq]
  exact principalSeriesInd_isAdmissible _ _

/-- For smooth characters $\chi_1, \chi_2$, the principal series `Langlands.principalSeries K χ₁ χ₂` of `Langlands/Statements/Smooth.lean` is admissible. -/
theorem principalSeries_isAdmissible {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : (principalSeries K χ₁ χ₂).IsAdmissible :=
  (normPrincipalSeries_isAdmissible hχ₁ hχ₂).of_iso (normPrincipalSeries_iso hχ₁ hχ₂)

end Normalized

section JacquetExact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

omit [IsTopologicalGroup G] in
/-- The image of $V(N)$ under a surjective map of representations $V \to V'$ is $V'(N)$. -/
theorem jacquetKer_map {π π' : SmoothRep G} (N : Subgroup G) (f : IntertwiningMap π.ρ π'.ρ)
    (hf : Function.Surjective f) :
    (π.jacquetKer N).map f.toLinearMap = π'.jacquetKer N := by
  unfold jacquetKer Coinvariants.ker
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨⟨n, v⟩, rfl⟩, rfl⟩
    refine ⟨⟨n, f v⟩, ?_⟩
    change π'.ρ n (f v) - f v = f (π.ρ n v - v)
    rw [map_sub, IntertwiningMap.isIntertwining π.ρ π'.ρ f n v]
  · rintro ⟨⟨n, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    refine ⟨_, ⟨⟨n, v⟩, rfl⟩, ?_⟩
    change f (π.ρ n v - v) = π'.ρ n (f v) - f v
    rw [map_sub, IntertwiningMap.isIntertwining π.ρ π'.ρ f n v]

/-- The Jacquet functor is right exact: for an exact sequence $V' \to V \to V'' \to 0$ of smooth representations, the sequence $V'_N \to V_N \to V''_N \to 0$ is exact. The surjectivity is `Langlands.SmoothRep.jacquetMap_surjective`; this theorem gives the exactness at $V_N$. -/
theorem jacquetMap_exact {π' π π'' : SmoothRep G} {N M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (g : IntertwiningMap π'.ρ π.ρ)
    (f : IntertwiningMap π.ρ π''.ρ) (hfg : Function.Exact g f) (hf : Function.Surjective f) :
    Function.Exact (jacquetMap hMN g) (jacquetMap hMN f) := by
  intro y
  obtain ⟨v, rfl⟩ := π.jacquetMk_surjective N M hMN y
  rw [jacquetMap_mk, jacquetMk_eq_zero_iff]
  constructor
  · intro hv
    rw [← jacquetKer_map N f hf] at hv
    obtain ⟨k, hk, hkv⟩ := hv
    obtain ⟨x, hx⟩ := (hfg (v - k)).1 (by
      rw [map_sub, sub_eq_zero]
      exact hkv.symm)
    refine ⟨π'.jacquetMk N M hMN x, ?_⟩
    rw [jacquetMap_mk, hx]
    refine (Submodule.Quotient.eq _).2 ?_
    rwa [sub_sub_cancel_left, neg_mem_iff]
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := π'.jacquetMk_surjective N M hMN x
    rw [jacquetMap_mk] at hx
    have h0 : f (g x) = 0 := (hfg (g x)).2 ⟨x, rfl⟩
    have := (Submodule.Quotient.eq _).1 hx
    have h1 : f (g x - v) ∈ π''.jacquetKer N := by
      rw [← jacquetKer_map N f hf]
      exact ⟨_, this, rfl⟩
    rw [map_sub, h0, zero_sub, neg_mem_iff] at h1
    exact h1

end SmoothRep

end JacquetExact

section Congruence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

/-- A $2 \times 2$ matrix is $\gamma$-small if each entry has valuation less than $\gamma$. -/
def IsSmallMatrix (γ : ValueGroupWithZero K) (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ i j, valuation K (M i j) < γ

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The sum of two $\gamma$-small matrices is $\gamma$-small. -/
theorem IsSmallMatrix.add {γ : ValueGroupWithZero K} {M M' : Matrix (Fin 2) (Fin 2) K}
    (h : IsSmallMatrix γ M) (h' : IsSmallMatrix γ M') : IsSmallMatrix γ (M + M') :=
  fun i j => Valuation.map_add_lt _ (h i j) (h' i j)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $\gamma \le 1$ the product of two $\gamma$-small matrices is $\gamma$-small. -/
theorem IsSmallMatrix.mul {γ : ValueGroupWithZero K} (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1)
    {M M' : Matrix (Fin 2) (Fin 2) K}
    (h : IsSmallMatrix γ M) (h' : IsSmallMatrix γ M') : IsSmallMatrix γ (M * M') := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ hγ0 fun k _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' ((h' k j).le.trans hγ1)).trans_lt (h i k)

variable (K) in
/-- The congruence subgroup of the elements $g$ such that $g - 1$ and $g^{-1} - 1$ are $\gamma$-small, for $0 < \gamma \le 1$. -/
def congruence (γ : ValueGroupWithZero K) (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1) :
    Subgroup (GL (Fin 2) K) where
  carrier := {g | IsSmallMatrix γ (g.1 - 1) ∧ IsSmallMatrix γ ((g⁻¹).1 - 1)}
  mul_mem' {a b} ha hb := by
    have key : ∀ x y : Matrix (Fin 2) (Fin 2) K,
        x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := fun x y => by noncomm_ring
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, key]
      exact ((ha.1.mul hγ0 hγ1 hb.1).add ha.1).add hb.1
    · rw [_root_.mul_inv_rev, Units.val_mul, key]
      exact ((hb.2.mul hγ0 hγ1 ha.2).add hb.2).add ha.2
  one_mem' := by
    have : IsSmallMatrix γ (0 : Matrix (Fin 2) (Fin 2) K) := fun i j => by
      simpa using zero_lt_iff.2 hγ0
    exact ⟨by simpa using this, by simpa using this⟩
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

/-- The congruence subgroup is open. -/
theorem isOpen_congruence (γ : ValueGroupWithZero K) (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1) :
    IsOpen (congruence K γ hγ0 hγ1 : Set (GL (Fin 2) K)) := by
  have h1 : ∀ i j, Continuous fun g : GL (Fin 2) K => g.1 i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have h2 : ∀ i j, Continuous fun g : GL (Fin 2) K => (g⁻¹).1 i j := fun i j =>
    (Units.continuous_val.comp continuous_inv).matrix_elem i j
  have hs : ∀ (F : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K), (∀ i j, Continuous fun g => F g i j) →
      IsOpen {g | IsSmallMatrix γ (F g - 1)} := by
    intro F hF
    simp only [IsSmallMatrix, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hF i j).isOpen_preimage _ (isOpen_valuation_sub_lt _ γ)
  exact (hs _ h1).inter (hs _ h2)

/-- For a smooth character $\chi$ there is $\gamma \neq 0$ such that $\chi(x) = 1$ for each $x$ with $v(x - 1) < \gamma$. -/
theorem _root_.Langlands.IsSmoothChar.exists_valuation_sub_one {χ : Kˣ →* ℂˣ}
    (hχ : IsSmoothChar K χ) :
    ∃ γ : ValueGroupWithZero K, γ ≠ 0 ∧ ∀ x : Kˣ, valuation K ((x : K) - 1) < γ → χ x = 1 := by
  have h1 : (χ.ker : Set Kˣ) ∈ nhds (1 : Kˣ) := hχ.mem_nhds (Subgroup.one_mem _)
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨s, hs, hsub⟩ := h1
  rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at hs
  obtain ⟨γ, hγ⟩ := hs
  exact ⟨γ, γ.ne_zero, fun x hx => hsub (hγ hx)⟩

/-- For smooth characters $\chi_1, \chi_2$ there is a congruence subgroup $U$ such that $\chi_1 \otimes \chi_2$ is trivial on $B \cap U$. -/
theorem exists_congruence_borelChar {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    ∃ (γ : ValueGroupWithZero K) (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1),
      ∀ b : borel K, (b : GL (Fin 2) K) ∈ congruence K γ hγ0 hγ1 → borelChar χ₁ χ₂ b = 1 := by
  obtain ⟨γ₁, hγ₁, h₁⟩ := hχ₁.exists_valuation_sub_one
  obtain ⟨γ₂, hγ₂, h₂⟩ := hχ₂.exists_valuation_sub_one
  have hγ0 : min (min γ₁ γ₂) 1 ≠ 0 := by
    rw [← zero_lt_iff] at hγ₁ hγ₂ ⊢
    exact lt_min (lt_min hγ₁ hγ₂) zero_lt_one
  refine ⟨_, hγ0, min_le_right _ _, fun b hb => ?_⟩
  have e1 : valuation K ((diagFst b : K) - 1) < γ₁ := by
    have := hb.1 0 0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at this
    exact this.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : valuation K ((diagSnd b : K) - 1) < γ₂ := by
    have := hb.1 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at this
    exact this.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  rw [borelChar_apply, h₁ _ e1, h₂ _ e2, mul_one]

end GL2

end Congruence

section NonzeroVector

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- Let $\theta$ be a character of $H$ and let $U$ be an open subgroup of $G$ such that $\theta$ is trivial on $H \cap U$. Then $\mathrm{Ind}_H^G \theta$ has a vector $f$ with $f(1) = 1$: the function with support $HU$ and $f(hu) = \theta(h)$. -/
theorem exists_ind_charRep_eq_one {H : Subgroup G} (θ : H →* ℂˣ) (hθ : IsOpen (θ.ker : Set H))
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hθU : ∀ h : H, (h : G) ∈ U → θ h = 1) :
    ∃ f : (ind H (charRep θ hθ)).V, ind.toFun f 1 = ULift.up 1 := by
  classical
  let P : G → Prop := fun g => ∃ b : H, (b : G)⁻¹ * g ∈ U
  let F : G → ULift.{u} ℂ := fun g => if h : P g then ULift.up (θ h.choose : ℂ) else 0
  have key : ∀ (b : H) (g : G), (b : G)⁻¹ * g ∈ U → F g = ULift.up (θ b : ℂ) := by
    intro b g hb
    have h : P g := ⟨b, hb⟩
    simp only [F, dite_eq_left h]
    have hc := h.choose_spec
    have hm : ((b⁻¹ * h.choose : H) : G) = ((b : G)⁻¹ * g) * (((h.choose : H) : G)⁻¹ * g)⁻¹ := by
      simp [mul_assoc]
    have h1 : θ (b⁻¹ * h.choose) = 1 := hθU _ (by rw [hm]; exact U.mul_mem hb (U.inv_mem hc))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
  have zero : ∀ g, ¬ P g → F g = 0 := fun g h => dite_eq_right h
  have hF : F ∈ indSpace H (charRep θ hθ) := by
    refine ⟨fun h g => ?_, U, hU, fun g u hu => ?_⟩
    · change F (h * g) = (θ h : ℂ) • F g
      by_cases hg : P g
      · obtain ⟨b, hb⟩ := hg
        rw [key b g hb, key (h * b) (h * g) (by simpa [mul_assoc] using hb)]
        apply ULift.ext
        simp
      · have : ¬ P (h * g) := by
          rintro ⟨b, hb⟩
          exact hg ⟨h⁻¹ * b, by simpa [mul_assoc] using hb⟩
        rw [zero _ hg, zero _ this, smul_zero]
    · by_cases hg : P g
      · obtain ⟨b, hb⟩ := hg
        rw [key b g hb, key b (g * u) (by rw [← mul_assoc]; exact U.mul_mem hb hu)]
      · have : ¬ P (g * u) := by
          rintro ⟨b, hb⟩
          refine hg ⟨b, ?_⟩
          have := U.mul_mem hb (U.inv_mem hu)
          simpa [mul_assoc] using this
        rw [zero _ hg, zero _ this]
  refine ⟨show indSpace H (charRep θ hθ) from ⟨F, hF⟩, ?_⟩
  change F 1 = _
  rw [key 1 1 (by simp [U.one_mem]), map_one, Units.val_one]

end SmoothRep

end NonzeroVector

section PrincipalSeriesJacquet

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

namespace GL2

/-- The character $\chi_1 \otimes \chi_2$ of the torus $T$: $\mathrm{diag}(a, d) \mapsto \chi_1(a)\chi_2(d)$. -/
noncomputable def torusChar (χ₁ χ₂ : Kˣ →* ℂˣ) : torus K →* ℂˣ :=
  (borelChar χ₁ χ₂).comp (Subgroup.inclusion torus_le_borel)

/-- For smooth $\chi_1, \chi_2$ the character $\chi_1 \otimes \chi_2$ of $T$ is smooth. -/
theorem isOpen_ker_torusChar {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : IsOpen ((torusChar χ₁ χ₂).ker : Set (torus K)) := by
  have hc : Continuous (Subgroup.inclusion (torus_le_borel (K := K))) :=
    continuous_subtype_val.subtype_mk _
  exact hc.isOpen_preimage _ (isOpen_ker_borelChar hχ₁ hχ₂)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The character $\chi_1 \otimes \chi_2$ of $B$ is trivial on $N$. -/
theorem borelChar_unipotent (χ₁ χ₂ : Kˣ →* ℂˣ) (b : borel K) (hb : (b : GL (Fin 2) K) ∈ unipotent K) :
    borelChar χ₁ χ₂ b = 1 := by
  have h1 : diagFst b = 1 := Units.ext hb.2.1
  have h2 : diagSnd b = 1 := Units.ext hb.2.2
  rw [borelChar_apply, h1, h2, map_one, map_one, mul_one]

end GL2

/-- Evaluation at $1$, $f \mapsto f(1)$, as a map of representations of $T$ from the principal series to $\chi_1 \otimes \chi_2$ that is invariant under $N$. -/
noncomputable def principalSeriesEval (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).nInvariantHom (unipotent K) (torus K)
      (SmoothRep.charRep (torusChar χ₁ χ₂) (isOpen_ker_torusChar hχ₁ hχ₂)) :=
  ⟨{ toFun := fun f => SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f 1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     isIntertwining' := fun t => by
       ext f
       change SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f (1 * (t : GL (Fin 2) K)) =
         (torusChar χ₁ χ₂ t : ℂ) • SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f 1
       have := SmoothRep.ind.toFun_mul_left (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f ⟨t, torus_le_borel t.2⟩ 1
       rw [mul_one] at this
       rw [one_mul]
       exact this },
    fun n hn f => by
      change SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f (1 * n) = SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f 1
      have := SmoothRep.ind.toFun_mul_left (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f ⟨n, unipotent_le_borel hn⟩ 1
      rw [mul_one] at this
      rw [one_mul, this]
      change ((borelChar χ₁ χ₂ ⟨n, unipotent_le_borel hn⟩ : ℂˣ) : ℂ) • (_ : ULift ℂ) = _
      rw [borelChar_unipotent χ₁ χ₂ _ hn, Units.val_one]
      exact one_smul ℂ _⟩

/-- The value of `principalSeriesEval` at $f$ is $f(1)$. -/
theorem principalSeriesEval_apply {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) :
    (principalSeriesEval χ₁ χ₂ hχ₁ hχ₂).1 f = SmoothRep.ind.toFun (H := borel K) (σ := SmoothRep.charRep (borelChar χ₁ χ₂) (isOpen_ker_borelChar hχ₁ hχ₂)) f 1 :=
  rfl

/-- The map $(\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N \to \chi_1 \otimes \chi_2$ of representations of $T$ that evaluation at $1$ gives. -/
noncomputable def principalSeriesJacquetEval (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    IntertwiningMap (principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂).ρ
      (SmoothRep.charRep (torusChar χ₁ χ₂) (isOpen_ker_torusChar hχ₁ hχ₂)).ρ :=
  ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).jacquetEquiv (unipotent K) (torus K)
    (torus_le_borel.trans borel_le_normalizer_unipotent) _).symm
    (principalSeriesEval χ₁ χ₂ hχ₁ hχ₂)

/-- The principal series has a vector $f$ with $f(1) = 1$. -/
theorem principalSeriesInd_exists_eq_one {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    ∃ f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V, SmoothRep.ind.toFun f 1 = ULift.up 1 := by
  obtain ⟨γ, hγ0, hγ1, h⟩ := exists_congruence_borelChar hχ₁ hχ₂
  exact SmoothRep.exists_ind_charRep_eq_one _ _ _ (isOpen_congruence γ hγ0 hγ1) h

/-- The principal series is not zero. -/
theorem principalSeriesInd_nontrivial {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : Nontrivial (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V := by
  obtain ⟨f, hf⟩ := principalSeriesInd_exists_eq_one hχ₁ hχ₂
  refine ⟨⟨f, 0, fun h => ?_⟩⟩
  have : SmoothRep.ind.toFun f 1 = 0 := by rw [h]; rfl
  rw [hf] at this
  exact one_ne_zero (congrArg ULift.down this)

/-- The Jacquet module of the principal series maps onto $\chi_1 \otimes \chi_2$: the map that evaluation at $1$ gives is surjective. Thus $\chi_1 \otimes \chi_2$ is a quotient of $(\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N$ as a representation of $T$. -/
theorem principalSeriesJacquetEval_surjective {χ₁ χ₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    Function.Surjective (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂) := by
  intro y
  obtain ⟨f, hf⟩ := principalSeriesInd_exists_eq_one hχ₁ hχ₂
  refine ⟨(principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).jacquetMk _ _
    (torus_le_borel.trans borel_le_normalizer_unipotent) (y.down • f), ?_⟩
  show (principalSeriesEval χ₁ χ₂ hχ₁ hχ₂).1 (y.down • f) = y
  rw [principalSeriesEval_apply]
  apply ULift.ext
  change y.down * ULift.down (SmoothRep.ind.toFun f 1) = y.down
  rw [hf, mul_one]

end PrincipalSeriesJacquet

end Langlands
