/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.GodementJacquet
import Langlands.Smooth.Bruhat
import Langlands.Smooth.PrincipalSeries
import Langlands.Local.GL2Reduction

/-!
# The L-factor of a supercuspidal representation of GL(2)

Let $K$ be a nonarchimedean local field with residue field of $q$ elements and let $\pi$ be an irreducible admissible representation of $GL_2(K)$. This file proves that $L(s, \pi) = 1$ in the sense of `Langlands.IsGJLFactor` when $\pi$ is supercuspidal, from one named input on the zeta integrals.

`Langlands.IsGJLFactor π 1` has three clauses. Write $X = q^{-s}$.

1. $1 = P(X)^{-1}$ for a polynomial $P$ with $P(0) = 1$. This holds with $P = 1$.
2. Each zeta integral $Z(\Phi, s, f)$ is $A(X) X^{-k}$ for $\mathrm{Re}(s)$ large. This is the input `Langlands.LocalGL2.SupercuspidalZetaLaurent`.
3. The constant $1$ is a finite combination of zeta integrals with Laurent polynomial coefficients. The file proves this for each smooth representation of $GL_2(K)$ on a nonzero space.

## Main definitions

* `Langlands.LocalGL2.SupercuspidalZetaLaurent`: the zeta integrals of a supercuspidal representation are Laurent polynomials in $q^{-s}$ (Godement and Jacquet; Bushnell and Henniart, 24.2).
* `Langlands.LocalGL2.scBall`: the set of the matrices $x \in M_2(K)$ with $v((x - 1)_{ij}) < \gamma$ for each entry.

## Main results

* `Langlands.SmoothRep.exists_smoothDual_apply_ne_zero`: a nonzero vector fixed by a compact open subgroup $U$ has a smooth linear form $\lambda$ with $\lambda(v) \neq 0$.
* `Langlands.SmoothRep.isSupercuspidal_of_iso`: supercuspidality is invariant under isomorphism.
* `Langlands.LocalGL2.nonsingInvUnit_mem_nhds`: a neighbourhood of $1$ in $GL_2(K)$ contains the matrices near $1$ in $M_2(K)$.
* `Langlands.LocalGL2.gjZeta_indicator`: the zeta integral of the characteristic function of a small open set $S$ is $\mathrm{vol}(S) \lambda(v)$.
* `Langlands.LocalGL2.exists_gjZeta_eq_const`: for each smooth representation of $GL_2(K)$ and each vector $v$ there is a Schwartz-Bruhat function $\Phi$ with $Z(\Phi, s, f) = c \, \lambda(v)$ for each $s$ and each linear form $\lambda$, with a constant $c > 0$.
* `Langlands.LocalGL2.isGJLFactor_one_of_zeta`: if the zeta integrals of a smooth representation of $GL_2(K)$ on a nonzero space are Laurent polynomials in $q^{-s}$, then $L(s, \pi) = 1$.
* `Langlands.LocalGL2.isGJLFactor_one_of_isSupercuspidal`: the input gives $L(s, \pi) = 1$ for each irreducible supercuspidal $\pi$.
* `Langlands.LocalGL2.supercuspidalLFactor_of_zetaLaurent`: the input `Langlands.LocalGL2.SupercuspidalZetaLaurent` gives the input `Langlands.LocalGL2.SupercuspidalLFactor` of `Langlands.LocalGL2.GL2OddInputs`.

## Proof

For clause 3, let $v \neq 0$. Let $U$ be the compact open subgroup of the elements of $GL_2(\mathcal{O}_K)$ that fix $v$. The vector $v$ is not in the span $V(U)$ of the vectors $\pi(u) w - w$, because the average over $U$ kills $V(U)$ and fixes $v$ (`Langlands.SmoothRep.cosetSum_eq_zero_of_mem_jacquetKer`). A linear form $\lambda$ that is zero on $V(U)$ with $\lambda(v) \neq 0$ is fixed by $U$, so it is smooth. Let $S$ be a small neighbourhood of $1$ in $M_2(K)$ of the form `Langlands.LocalGL2.scBall`. Choose $S$ so small that each $x \in S$ is invertible, fixes $v$ and has $|\det x| = 1$. For $\Phi = 1_S$ the integrand of $Z(\Phi, s, f)$ is $\lambda(v)$ on $S$ and $0$ outside $S$. Thus $Z(\Phi, s, f) = \mathrm{vol}(S) \lambda(v)$, a nonzero constant, and $1 = (\mathrm{vol}(S) \lambda(v))^{-1} Z(\Phi, s, f)$.

## Implementation notes

The input `Langlands.LocalGL2.SupercuspidalZetaLaurent` is clause 2 of `Langlands.IsGJLFactor` for $L = 1$. Its proof needs analysis on $M_2(K)$ that the library does not have. Let $f$ be a matrix coefficient of $\pi$, with support in $C Z$ for a compact set $C$. If $\Phi$ is zero near $0$, then $\Phi f$ has compact support in $GL_2(K)$. Then $|\det g|$ takes finitely many values on the support, and the integral is a finite sum of terms $c_m X^m$. This needs the decomposition of the integral over the level sets of $|\det g|$. For $\Phi$ the characteristic function of a small ball around $0$, the terms with $m$ large are the integrals of $f$ over the sets $\{g \in C Z : |\det g| = q^{-m}\}$. They vanish because $\pi$ is cuspidal: the integral of $f$ over $\{|\det g| = q^{-m}\}$ is invariant under the subgroup $\{|\det g| = 1\}$, and a supercuspidal representation has no nonzero invariant linear form for this subgroup. This needs a Haar measure on $GL_2(K)$ and its comparison with $|\det x|^{-2} dx$. The library does not have these.

## References

* R. Godement, H. Jacquet, Zeta functions of simple algebras, LNM 260, Springer, 1972, theorem 3.3 and proposition 4.4.
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, section 24.2.
-/

namespace Langlands

universe u

open MeasureTheory ValuativeRel

section SmoothDual

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- Let $U$ be a compact open subgroup that fixes a vector $v \neq 0$. Then there is a smooth linear form $\lambda$ with $\lambda(v) \neq 0$. The vector $v$ is not in $V(U)$, and a linear form that is zero on $V(U)$ is fixed by $U$. -/
theorem exists_smoothDual_apply_ne_zero (π : SmoothRep G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) {v : π.V} (hv : v ≠ 0)
    (hfix : ∀ g ∈ U, π.ρ g v = v) :
    ∃ l : smoothVectors π.ρ.dual, (l : Module.Dual ℂ π.V) v ≠ 0 := by
  classical
  have hnot : v ∉ π.jacquetKer U := by
    intro hmem
    obtain ⟨s, hsU, hs⟩ := π.cosetSum_eq_zero_of_mem_jacquetKer hmem
    have h0 := hs U hUc hsU
    have := π.finiteIndex_stabIn hUc v
    have := Fintype.ofFinite (U ⧸ π.stabIn U v)
    rw [cosetSum_eq_sum] at h0
    have hterm : ∀ q : U ⧸ π.stabIn U v, π.ρ ((Quotient.out q : U) : G) v = v :=
      fun q => hfix _ (Quotient.out q).2
    simp only [hterm, Finset.sum_const, Finset.card_univ] at h0
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero, Nat.cast_eq_zero] at h0
    exact h0.elim (fun h => Fintype.card_ne_zero h) hv
  have hq : (π.jacquetKer U).mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hq
  let l : Module.Dual ℂ π.V := φ ∘ₗ (π.jacquetKer U).mkQ
  have hinv : ∀ g ∈ U, ∀ w, l (π.ρ g w) = l w := by
    intro g hg w
    have hsub := π.sub_mem_jacquetKer hg w
    have : (π.jacquetKer U).mkQ (π.ρ g w) = (π.jacquetKer U).mkQ w := by
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hsub
    change φ _ = φ _
    rw [this]
  have hsm : l ∈ smoothVectors π.ρ.dual := by
    refine Subgroup.isOpen_mono (H₁ := U) (fun g hg => ?_) hUo
    rw [mem_vecStabilizer]
    refine LinearMap.ext fun w => ?_
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    exact hinv _ (U.inv_mem hg) w
  exact ⟨⟨l, hsm⟩, hφ⟩

/-- Supercuspidality is invariant under isomorphism. A coefficient of $\pi'$ is a coefficient of $\pi$ for the transported vector and linear form. -/
theorem isSupercuspidal_of_iso {Z : Type*} [Group Z] {π π' : SmoothRep G} (hπ : π.Iso π')
    {ι : Z →* G} (h : π.IsSupercuspidal ι) : π'.IsSupercuspidal ι := by
  obtain ⟨e, he⟩ := hπ
  intro v l
  let l' : Module.Dual ℂ π.V := (l : Module.Dual ℂ π'.V) ∘ₗ (e : π.V →ₗ[ℂ] π'.V)
  have hl' : l' ∈ smoothVectors π.ρ.dual := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π'.ρ.dual l) (fun g hg => ?_) l.2
    rw [mem_vecStabilizer] at hg ⊢
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun hg (e w)
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] at this ⊢
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe, he]
    exact this
  have hcoeff : ∀ g, π.coeff (e.symm v) l' g = π'.coeff v l g := by
    intro g
    simp only [SmoothRep.coeff, l', LinearMap.comp_apply, LinearEquiv.coe_coe, he,
      LinearEquiv.apply_symm_apply]
  obtain ⟨C, hC, hsupp⟩ := h (e.symm v) ⟨l', hl'⟩
  exact ⟨C, hC, fun g hg => hsupp g (by rwa [hcoeff])⟩

end SmoothRep

end SmoothDual

namespace LocalGL2

section Ball

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [IsNonarchimedeanLocalField K] in
/-- The ball $\{x : v(x - y) < \gamma\}$ is closed. -/
theorem isClosed_valuation_sub_lt [IsValuativeTopology K] (y : K) (γ : ValueGroupWithZero K) :
    IsClosed {x : K | valuation K (x - y) < γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hx
  rcases eq_or_ne γ 0 with h0 | h0
  · refine Filter.Eventually.of_forall fun z => ?_
    simp [h0]
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ h0, fun z hz => ?_⟩
  change valuation K (z - x) < γ at hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have e : z - y = (x - y) + (z - x) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (hz.trans_le hx)]
  exact hx

variable (K) in
/-- The set of the matrices $x \in M_2(K)$ such that each entry of $x - 1$ has valuation less than $\gamma$. -/
def scBall (γ : ValueGroupWithZero K) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {x | ∀ i j, valuation K ((x - 1) i j) < γ}

/-- The set `scBall K γ` is open. -/
theorem isOpen_scBall (γ : ValueGroupWithZero K) : IsOpen (scBall K γ) := by
  have : scBall K γ = ⋂ i, ⋂ j, (fun x : Matrix (Fin 2) (Fin 2) K => x i j) ⁻¹'
      {y : K | valuation K (y - (1 : Matrix (Fin 2) (Fin 2) K) i j) < γ} := by
    ext x
    simp [scBall, Matrix.sub_apply]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (continuous_id.matrix_elem i j).isOpen_preimage _ (isOpen_valuation_sub_lt _ γ)

/-- The set `scBall K γ` is closed. -/
theorem isClosed_scBall (γ : ValueGroupWithZero K) : IsClosed (scBall K γ) := by
  have : scBall K γ = ⋂ i, ⋂ j, (fun x : Matrix (Fin 2) (Fin 2) K => x i j) ⁻¹'
      {y : K | valuation K (y - (1 : Matrix (Fin 2) (Fin 2) K) i j) < γ} := by
    ext x
    simp [scBall, Matrix.sub_apply]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_valuation_sub_lt _ γ).preimage (continuous_id.matrix_elem i j)

/-- The set `scBall K γ` is contained in a compact set. -/
theorem exists_isCompact_superset_scBall (γ : ValueGroupWithZero K) :
    ∃ C : Set (Matrix (Fin 2) (Fin 2) K), IsCompact C ∧ scBall K γ ⊆ C := by
  let P : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => {y : K | valuation K y ≤ γ}
  have hP : IsCompact P := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall K γ
  refine ⟨(fun y => y + 1) '' P, hP.image (continuous_id.add continuous_const), fun x hx => ?_⟩
  refine ⟨x - 1, fun i _ j _ => (hx i j).le, ?_⟩
  simp

/-- The set `scBall K γ` has compact closure. -/
theorem isCompact_scBall (γ : ValueGroupWithZero K) : IsCompact (scBall K γ) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_scBall γ
  exact hC.of_isClosed_subset (isClosed_scBall γ) hsub

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $\gamma \neq 0$ the identity matrix is in `scBall K γ`. -/
theorem one_mem_scBall {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    (1 : Matrix (Fin 2) (Fin 2) K) ∈ scBall K γ := by
  intro i j
  simpa using zero_lt_iff.2 hγ

/-- Each neighbourhood of $1$ in $M_2(K)$ contains `scBall K γ` for some $\gamma \neq 0$. -/
theorem exists_scBall_subset {N : Set (Matrix (Fin 2) (Fin 2) K)}
    (hN : N ∈ nhds (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ γ : ValueGroupWithZero K, γ ≠ 0 ∧ scBall K γ ⊆ N := by
  let N' : Set (Fin 2 → Fin 2 → K) := N
  have hN' : N' ∈ Filter.pi fun i => nhds (fun j => (1 : Matrix (Fin 2) (Fin 2) K) i j) := by
    rw [← nhds_pi]
    exact hN
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.1 hN'
  have ht' : ∀ i, ∃ t' : Fin 2 → Set K, (∀ j, t' j ∈ nhds ((1 : Matrix (Fin 2) (Fin 2) K) i j)) ∧
      Set.univ.pi t' ⊆ t i := by
    intro i
    have hti : t i ∈ Filter.pi fun j => nhds ((1 : Matrix (Fin 2) (Fin 2) K) i j) := by
      rw [← nhds_pi]
      exact ht i
    obtain ⟨I', -, t', ht', hsub'⟩ := Filter.mem_pi.1 hti
    exact ⟨t', ht', fun y hy => hsub' fun j _ => hy j trivial⟩
  choose t' ht' hsub' using ht'
  have hγ : ∀ i j, ∃ γ : (ValueGroupWithZero K)ˣ,
      {z | valuation K (z - (1 : Matrix (Fin 2) (Fin 2) K) i j) < γ} ⊆ t' i j :=
    fun i j => IsValuativeTopology.mem_nhds_iff'.1 (ht' i j)
  choose γ hγ using hγ
  let m : ValueGroupWithZero K :=
    min (min (γ 0 0 : ValueGroupWithZero K) (γ 0 1)) (min (γ 1 0 : ValueGroupWithZero K) (γ 1 1))
  have hm : ∀ i j, m ≤ γ i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [m]
  have hm0 : m ≠ 0 := by
    refine ne_of_gt ?_
    simp only [m, lt_min_iff, zero_lt_iff]
    exact ⟨⟨(γ 0 0).ne_zero, (γ 0 1).ne_zero⟩, ⟨(γ 1 0).ne_zero, (γ 1 1).ne_zero⟩⟩
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hx' : x ∈ Set.univ.pi t := by
    intro i _
    refine hsub' i fun j _ => hγ i j ?_
    have := (hx i j).trans_le (hm i j)
    simpa [Matrix.sub_apply] using this
  exact hsub fun i _ => hx' i trivial

end Ball

section Nhds

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A matrix in `scBall K 1` is integral. -/
theorem isIntegralMatrix_of_mem_scBall {x : Matrix (Fin 2) (Fin 2) K} (hx : x ∈ scBall K 1) :
    GL2.IsIntegralMatrix x := by
  intro i j
  have e : x i j = (x - 1) i j + (1 : Matrix (Fin 2) (Fin 2) K) i j := by simp
  rw [e]
  refine Valuation.map_add_le _ (hx i j).le ?_
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- The subgroup $GL_2(\mathcal{O}_K)$ is open. It contains the elements $g$ such that $g$ and $g^{-1}$ are in `scBall K 1`. -/
theorem isOpen_maxCompact_of_scBall : IsOpen (GL2.maxCompact K : Set (GL (Fin 2) K)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous (Units.embedProduct (Matrix (Fin 2) (Fin 2) K)) :=
    Units.isEmbedding_embedProduct.continuous
  have hS : scBall K 1 ×ˢ (MulOpposite.unop ⁻¹' scBall K 1) ∈
      nhds (Units.embedProduct (Matrix (Fin 2) (Fin 2) K) 1) := by
    refine prod_mem_nhds ((isOpen_scBall 1).mem_nhds ?_) ?_
    · simpa using one_mem_scBall (K := K) one_ne_zero
    · refine (MulOpposite.continuous_unop.isOpen_preimage _ (isOpen_scBall 1)).mem_nhds ?_
      simpa using one_mem_scBall (K := K) one_ne_zero
  filter_upwards [hc.continuousAt.preimage_mem_nhds hS] with g hg
  exact ⟨isIntegralMatrix_of_mem_scBall hg.1, isIntegralMatrix_of_mem_scBall hg.2⟩

/-- Let $W$ be a neighbourhood of $1$ in $GL_2(K)$. Then each matrix $x$ near $1$ is invertible and the element $x$ of $GL_2(K)$ is in $W$. -/
theorem nonsingInvUnit_mem_nhds {W : Set (GL (Fin 2) K)} (hW : W ∈ nhds 1) :
    {x : Matrix (Fin 2) (Fin 2) K | ∃ h : IsUnit x.det, Matrix.nonsingInvUnit x h ∈ W} ∈
      nhds 1 := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨s, hs, hsub⟩ := hW
  have hinv : ContinuousAt (fun x : Matrix (Fin 2) (Fin 2) K => x⁻¹) 1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Matrix.det_one]
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hF : ContinuousAt (fun x : Matrix (Fin 2) (Fin 2) K => (x, MulOpposite.op x⁻¹)) 1 :=
    continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hs' : s ∈ nhds ((fun x : Matrix (Fin 2) (Fin 2) K => (x, MulOpposite.op x⁻¹)) 1) := by
    convert hs using 2
    simp [Units.embedProduct_apply]
  have hdet : {x : Matrix (Fin 2) (Fin 2) K | x.det ≠ 0} ∈ nhds 1 :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  filter_upwards [hF.preimage_mem_nhds hs', hdet] with x hx hx0
  have h : IsUnit x.det := isUnit_iff_ne_zero.2 hx0
  refine ⟨h, hsub ?_⟩
  have hi : ((Matrix.nonsingInvUnit x h)⁻¹ : GL (Fin 2) K).1 = x⁻¹ :=
    (Matrix.inv_eq_right_inv (Units.mul_inv (Matrix.nonsingInvUnit x h))).symm
  change ((Matrix.nonsingInvUnit x h : Matrix (Fin 2) (Fin 2) K),
    MulOpposite.op ((Matrix.nonsingInvUnit x h)⁻¹ : GL (Fin 2) K).1) ∈ s
  rw [hi]
  exact hx

end Nhds

section Zeta

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- For $\gamma \neq 0$ the set `scBall K γ` has positive finite volume. -/
theorem matrixHaar_real_scBall_ne_zero {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    (matrixHaar K 2).real (scBall K γ) ≠ 0 := by
  let := matrixBorel K 2
  have : BorelSpace (Matrix (Fin 2) (Fin 2) K) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → K))
  have : (matrixHaar K 2).IsAddHaarMeasure := by unfold matrixHaar; infer_instance
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨(isOpen_scBall γ).measure_ne_zero _ ⟨1, one_mem_scBall hγ⟩,
    (isCompact_scBall γ).measure_lt_top.ne⟩

/-- Let $S \subseteq M_2(K)$ be open. Suppose that each $x \in S$ is invertible, fixes $v$ and has $|\det x| = 1$. Then $Z(1_S, s, f) = \mathrm{vol}(S) \lambda(v)$ for the coefficient $f(g) = \lambda(\pi(g) v)$. -/
theorem gjZeta_indicator (π : SmoothRep (GL (Fin 2) K)) {S : Set (Matrix (Fin 2) (Fin 2) K)}
    (hSo : IsOpen S) (v : π.V)
    (hS : ∀ x ∈ S, ∃ h : IsUnit x.det, π.ρ (Matrix.nonsingInvUnit x h) v = v ∧
      normAbs K x.det = 1)
    (l : Module.Dual ℂ π.V) (s : ℂ) :
    gjZeta K π (S.indicator fun _ => 1) v l s = (matrixHaar K 2).real S * l v := by
  classical
  let := matrixBorel K 2
  have : BorelSpace (Matrix (Fin 2) (Fin 2) K) := ⟨rfl⟩
  have hSm : MeasurableSet S := hSo.measurableSet
  have hfun : (fun x : Matrix (Fin 2) (Fin 2) K => if h : IsUnit x.det then
      S.indicator (fun _ => 1) x * π.coeff v l (Matrix.nonsingInvUnit x h) *
        ((normAbs K x.det : ℂ) ^ (s + (((2 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)))
      else 0) = S.indicator (fun _ => l v) := by
    funext x
    by_cases hx : x ∈ S
    · obtain ⟨h, hv, hn⟩ := hS x hx
      simp only [h, ↓reduceDIte]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, SmoothRep.coeff, hv, hn]
      simp
    · rw [Set.indicator_of_notMem hx]
      split_ifs <;> simp [Set.indicator_of_notMem hx]
  unfold gjZeta
  rw [hfun, integral_indicator_const _ hSm, Complex.real_smul]

/-- **The constant $1$ is a zeta integral up to a scalar.** For each smooth representation $\pi$ of $GL_2(K)$ and each vector $v$ there are a Schwartz-Bruhat function $\Phi$ and a constant $c > 0$ with $Z(\Phi, s, f) = c \, \lambda(v)$ for each linear form $\lambda$ and each $s$. Here $\Phi$ is the characteristic function of a small neighbourhood of $1$. -/
theorem exists_gjZeta_eq_const (π : SmoothRep (GL (Fin 2) K)) (v : π.V) :
    ∃ Φ : Matrix (Fin 2) (Fin 2) K → ℂ, IsSchwartzBruhat K Φ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (l : Module.Dual ℂ π.V) (s : ℂ), gjZeta K π Φ v l s = c * l v := by
  classical
  have hH : IsOpen (vecStabilizer π.ρ v : Set (GL (Fin 2) K)) := π.smooth v
  have hN1 := nonsingInvUnit_mem_nhds (hH.mem_nhds (vecStabilizer π.ρ v).one_mem)
  have hN2 : {x : Matrix (Fin 2) (Fin 2) K | valuation K (x.det - 1) < 1} ∈ nhds 1 :=
    ((isOpen_valuation_sub_lt 1 1).preimage continuous_id.matrix_det).mem_nhds (by simp)
  obtain ⟨γ, hγ, hsub⟩ := exists_scBall_subset (Filter.inter_mem hN1 hN2)
  refine ⟨(scBall K γ).indicator fun _ => 1, ⟨fun t => ?_, ?_⟩, (matrixHaar K 2).real (scBall K γ),
    lt_of_le_of_ne measureReal_nonneg (matrixHaar_real_scBall_ne_zero hγ).symm,
    fun l s => gjZeta_indicator π (isOpen_scBall γ) v (fun x hx => ?_) l s⟩
  · have hc : IsClopen (scBall K γ) := ⟨isClosed_scBall γ, isOpen_scBall γ⟩
    obtain h | h | h | h := Set.indicator_const_preimage (scBall K γ) t (1 : ℂ)
    · rw [h]
      exact isOpen_univ
    · rw [h]
      exact hc.2
    · rw [h]
      exact hc.1.isOpen_compl
    · rw [Set.mem_singleton_iff.1 h]
      exact isOpen_empty
  · exact HasCompactSupport.intro (isCompact_scBall γ) fun x hx => Set.indicator_of_notMem hx _
  · obtain ⟨⟨h, hv⟩, hd⟩ := hsub hx
    refine ⟨h, hv, normAbs_eq_one ?_⟩
    have := Valuation.map_eq_of_sub_lt (valuation K) (y := x.det) (x := 1) (by simpa using hd)
    simpa using this

end Zeta

section Reduction

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The zeta integrals of a supercuspidal representation are Laurent polynomials** (Godement and Jacquet, Zeta functions of simple algebras, LNM 260, theorem 3.3 and proposition 4.4; Bushnell and Henniart, The local Langlands conjecture for GL(2), 24.2). Let $\pi$ be an irreducible supercuspidal representation of $GL_2(K)$. For each Schwartz-Bruhat function $\Phi$, each vector $v$ and each smooth linear form $\lambda$ there are a polynomial $A$ and $k \in \mathbb{N}$ with $Z(\Phi, s, f) = A(q^{-s}) q^{ks}$ for $\mathrm{Re}(s)$ large. This is clause 2 of `Langlands.IsGJLFactor` for $L = 1$. The proof needs analysis that the library does not have; see the implementation notes. -/
def SupercuspidalZetaLaurent : Prop :=
  ∀ π : IrrRep (GL (Fin 2) K), π.1.IsSupercuspidal (scalarGL K 2) →
    ∀ (Φ : Matrix (Fin 2) (Fin 2) K → ℂ) (v : π.1.V) (l : smoothVectors π.1.ρ.dual),
      IsSchwartzBruhat K Φ → ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
        gjZeta K π.1 Φ v l s =
          A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k

variable {K}

/-- Let $\pi$ be a smooth representation of $GL_2(K)$ on a nonzero space. If the zeta integrals of $\pi$ are Laurent polynomials in $q^{-s}$, then $L(s, \pi) = 1$ in the sense of `Langlands.IsGJLFactor`. -/
theorem isGJLFactor_one_of_zeta (π : SmoothRep (GL (Fin 2) K)) [Nontrivial π.V]
    (h : ∀ (Φ : Matrix (Fin 2) (Fin 2) K → ℂ) (v : π.V) (l : smoothVectors π.ρ.dual),
      IsSchwartzBruhat K Φ → ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
        gjZeta K π Φ v l s =
          A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k) :
    IsGJLFactor K π (fun _ => 1) := by
  refine ⟨⟨1, by simp, fun s => by simp⟩, fun Φ v l hΦ => ?_, ?_⟩
  · obtain ⟨A, k, s₀, hA⟩ := h Φ v l hΦ
    exact ⟨A, k, s₀, fun s hs => by rw [hA s hs, mul_one]⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
    obtain ⟨Φ, hΦ, c, hc, hZ⟩ := exists_gjZeta_eq_const π v
    have hH : IsOpen (vecStabilizer π.ρ v : Set (GL (Fin 2) K)) := π.smooth v
    obtain ⟨l, hl⟩ := π.exists_smoothDual_apply_ne_zero
      (U := vecStabilizer π.ρ v ⊓ GL2.maxCompact K)
      (by
        rw [Subgroup.coe_inf]
        exact GL2.isCompact_maxCompact.inter_left (Subgroup.isClosed_of_isOpen _ hH))
      (by rw [Subgroup.coe_inf]; exact hH.inter isOpen_maxCompact_of_scBall) hv
      (fun g hg => hg.1)
    have hne : (c : ℂ) * (l : Module.Dual ℂ π.V) v ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hc.ne') hl
    refine ⟨1, fun _ => Φ, fun _ => v, fun _ => l,
      fun _ => Polynomial.C ((c : ℂ) * (l : Module.Dual ℂ π.V) v)⁻¹, 0, 0, fun _ => hΦ,
      fun s _ => ?_⟩
    rw [Fin.sum_univ_one, pow_zero, div_one, Polynomial.eval_C, hZ, inv_mul_cancel₀ hne]

/-- **The L-factor of a supercuspidal representation** from the input `Langlands.LocalGL2.SupercuspidalZetaLaurent`. Each irreducible supercuspidal representation $\pi$ of $GL_2(K)$ has $L(s, \pi) = 1$. -/
theorem isGJLFactor_one_of_isSupercuspidal (hZ : SupercuspidalZetaLaurent K)
    (π : IrrRep (GL (Fin 2) K)) (h : π.1.IsSupercuspidal (scalarGL K 2)) :
    IsGJLFactor K π.1 (fun _ => 1) := by
  have := π.2.1.1
  exact isGJLFactor_one_of_zeta π.1 (hZ π h)

/-- **The input `Langlands.LocalGL2.SupercuspidalLFactor`** of `Langlands.LocalGL2.GL2OddInputs` from the input `Langlands.LocalGL2.SupercuspidalZetaLaurent`. -/
theorem supercuspidalLFactor_of_zetaLaurent (hZ : SupercuspidalZetaLaurent K) :
    SupercuspidalLFactor K := by
  rintro π ⟨π', hπ', hsc⟩
  have hiso : π'.1.Iso π.1 := Quotient.exact hπ'
  exact isGJLFactor_one_of_isSupercuspidal hZ π (SmoothRep.isSupercuspidal_of_iso hiso hsc)

end Reduction

end LocalGL2

end Langlands
