/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GaloisTameParam
import Langlands.Local.AdaptedUnramified

/-!
# Facts on the Weil group for the tame parametrization

Let $K$ be a nonarchimedean local field. The file `Langlands/Local/GaloisTameParam.lean` reduces `Langlands.LocalGL2.GaloisTameParametrization` to named facts on $K$ and its Weil group $W_K$. This file proves three of these facts: `Langlands.LocalGL2.NormFactorU1`, `Langlands.LocalGL2.UniqueUnramifiedQuad` and `Langlands.LocalGL2.InertiaUnramified`.

The proof of `Langlands.LocalGL2.NormFactorU1` uses square roots in $U^1_L$. Let $u \in U^1_L$ have norm $1$ and let $w \in U^1_L$ be a square root of $u$. Then $(w \sigma(w))^2 = u \sigma(u) = 1$, and $1$ is the only square root of $1$ in $U^1_L$, so $u = w / \sigma(w)$. A character $\xi$ invariant under $\sigma$ on $U^1_L$ is then trivial on $u$, and the character of $N_{L/K}(U^1_L)$ extends to $K^\times$ because $\mathbb{C}^\times$ is divisible.

The proofs of the two other facts use the residue degree of a quadratic extension $L / K$. It is $2$ if $L / K$ is unramified and $1$ if $L / K$ is totally ramified. So $L / K$ is unramified exactly when the degree map sends $W_L$ onto $2 \mathbb{Z}$, that is when $W_L$ is the subgroup of the elements of even degree.

## Main definitions

* `Langlands.LocalGL2.wfEvenDegree`: the subgroup of the elements of even degree in $W_K$.
* `Langlands.LocalGL2.GaloisTameOpenInputs`: the inputs of `Langlands.LocalGL2.GaloisTameInputs` that are still open.

## Main results

* `Langlands.LocalGL2.normFactorU1_holds`: the fact `Langlands.LocalGL2.NormFactorU1`.
* `Langlands.LocalGL2.wf_residueDegree_eq_two_iff`: a quadratic extension has residue degree $2$ exactly when it is unramified.
* `Langlands.LocalGL2.uniqueUnramifiedQuad_holds`: the fact `Langlands.LocalGL2.UniqueUnramifiedQuad`.
* `Langlands.LocalGL2.inertiaUnramified_holds`: the fact `Langlands.LocalGL2.InertiaUnramified`.
* `Langlands.LocalGL2.galoisTameParametrization_of_openInputs`: the open inputs imply `Langlands.LocalGL2.GaloisTameParametrization`.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), sections 18.2 and 34.1.
* J.-P. Serre, Local fields, Chapters III and IV.

## Still open

The facts `Langlands.LocalGL2.ArtinConjCompat`, `Langlands.LocalGL2.WildInertiaProP`, `Langlands.LocalGL2.TameInertiaProcyclic`, `Langlands.LocalGL2.OpenIndexTwoQuad` and `Langlands.LocalGL2.WildArtinUnits` are not proved here. The first two of the Weil group facts need the ramification groups of finite Galois extensions. The fact `Langlands.LocalGL2.OpenIndexTwoQuad` needs the existence of unramified extensions of each degree inside $\bar K$ and the infinite Galois correspondence for the closure of a subgroup of $W_K$ in $G_K$.
-/

namespace Langlands.LocalGL2

universe u

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt Langlands.LocalField ValuativeRel LocalGL1

section Units

variable {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- If $2 \ne 0$ in the residue field, then $1$ is the only element of $U^1_E$ whose square is $1$. -/
theorem wf_eq_one_of_sq_eq_one (h2 : (2 : 𝓀[E]) ≠ 0) {a : Eˣ} (ha : a ∈ unitFilt E 1)
    (hsq : a ^ 2 = 1) : a = 1 := by
  have hall : ∀ n : ℕ, a ∈ unitFilt E (n + 1) := by
    intro n
    induction n with
    | zero => exact ha
    | succ n ih =>
      refine mem_unitFilt_succ_of_sq h2 (by omega) ih ?_
      rw [hsq]
      exact (unitFilt E (n + 1 + 1)).one_mem
  by_contra hne
  have hx0 : (a : E) - 1 ≠ 0 := fun h => hne (Units.ext (sub_eq_zero.1 h))
  have h := (mem_ordBall_of_ne_zero hx0).1 (hall (ord E ((a : E) - 1)).toNat).2
  omega

end Units

section Weil

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- If $2 \ne 0$ in the residue field of $K$, then $2 \ne 0$ in the residue field of each finite extension $L$ of $K$ inside $\bar K$. The reason is that $\mathfrak{p}_L$ lies over $\mathfrak{p}_K$. -/
theorem wf_two_ne_zero_residue (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    (h2 : (2 : 𝓀[K]) ≠ 0) : (2 : 𝓀[L]) ≠ 0 := by
  intro h
  apply h2
  have hm : (2 : 𝒪[L]) ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat]
    exact h
  have hK : (2 : 𝒪[K]) ∈ 𝓂[K] := by
    rw [Ideal.mem_of_liesOver 𝓂[L] 𝓂[K], map_ofNat]
    exact hm
  rw [← map_ofNat (IsLocalRing.residue 𝒪[K]) 2]
  exact (IsLocalRing.residue_eq_zero_iff _).2 hK

/-- **Elements of norm $1$ in $U^1_L$.** Let $2 \ne 0$ in the residue field of $K$ and let $L$ be a quadratic separable extension of $K$ with conjugation $\sigma$. If $u \in U^1_L$ has norm $1$, then $u = w / \sigma(w)$ with $w \in U^1_L$ and $w^2 = u$. -/
theorem wf_exists_sq_eq_div (L : IntermediateField K (AlgebraicClosure K))
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] (h2 : (2 : 𝓀[K]) ≠ 0)
    {u : Lˣ} (hu : u ∈ unitFilt L 1) (hn : normUnits K L u = 1) :
    ∃ w : Lˣ, w ∈ unitFilt L 1 ∧ galConjUnits K L w = w⁻¹ ∧ w ^ 2 = u := by
  have h2L := wf_two_ne_zero_residue L h2
  obtain ⟨w, hw, hw2⟩ := exists_sq_eq_of_mem_unitFilt h2L le_rfl hu
  have hσw : galConjUnits K L w ∈ unitFilt L 1 := (unitsMap_mem_unitFilt_iff _ w 1).2 hw
  have hus : u * galConjUnits K L u = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, val_unitsMap, ← algebraMap_norm_eq_mul, ← val_normUnits, hn, Units.val_one,
      map_one, Units.val_one]
  have hv : w * galConjUnits K L w = 1 := by
    refine wf_eq_one_of_sq_eq_one h2L (mul_mem hw hσw) ?_
    rw [mul_pow, ← map_pow, hw2, hus]
  exact ⟨w, hw, eq_inv_of_mul_eq_one_right hv, hw2⟩

/-- **A conjugation invariant character of $U^1_L$ factors through the norm** (`Langlands.LocalGL2.NormFactorU1`). Let $2 \ne 0$ in the residue field of $K$. For each quadratic separable extension $L$ of $K$ and each character $\xi$ of $L^\times$ with $\xi(\sigma u) = \xi(u)$ for $u \in U^1_L$, there is a character $\varphi$ of $K^\times$ with $\xi(u) = \varphi(N_{L/K}(u))$ for $u \in U^1_L$. The character $\xi$ does not have to be continuous. -/
theorem normFactorU1_holds : NormFactorU1 K := by
  intro h2 L _ _ ξ hξ
  refine (exists_factor_iff (unitFilt L 1) ξ).2 fun u hu hn => ?_
  obtain ⟨w, hw, hσw, rfl⟩ := wf_exists_sq_eq_div L h2 hu hn
  have h := hξ w hw
  rw [hσw, map_inv] at h
  rw [map_pow, sq]
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

end Weil

section Ramification

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
  [Algebra.IsSeparable K L]

/-- If the quadratic extension $L / K$ is unramified, then the residue degree $f(L|K)$ is not $1$. The residue class of `Langlands.LocalGL2.unramUnit` is not in $k_K$. -/
theorem wf_residueFinrank_ne_one (hu : IsUnramifiedExt K L) : residueFinrank K L ≠ 1 := by
  intro h1
  have hy : unramUnit K L hu ∈ 𝒪[L] := by
    rw [← SetLike.mem_coe, ← ordBall_zero_eq_integer]
    exact mem_ordBall_of_le (unramUnit_ne_zero hu) (ord_unramUnit hu).ge
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : residueField L) one_ne_zero).1 h1
    (Ideal.Quotient.mk 𝓂[L] ⟨_, hy⟩)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have ha : (a : K) ∈ ordBall K 0 := by
    rw [ordBall_zero_eq_integer]
    exact a.2
  apply unramUnit_sub_not_mem_ordBall_one hu ha
  have hm : (⟨_, hy⟩ : 𝒪[L]) - algebraMap 𝒪[K] 𝒪[L] a ∈ 𝓂[L] := by
    rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one]
    rfl
  exact (mem_ordBall_one_iff _).2 hm

omit [Algebra.IsSeparable K L] in
/-- If the quadratic extension $L / K$ is totally ramified, then the residue degree $f(L|K)$ is $1$. This is `Langlands.LocalGL2.exists_sub_mem_ordBall_one`. -/
theorem wf_residueFinrank_eq_one (hr : IsTotallyRamifiedExt K L) : residueFinrank K L = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' (1 : residueField L) one_ne_zero).2 fun w => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : (x : L) ∈ ordBall L 0 := by
    rw [ordBall_zero_eq_integer]
    exact x.2
  obtain ⟨c, hc0, hc1⟩ := exists_sub_mem_ordBall_one hr hx
  have hcO : c ∈ 𝒪[K] := by
    rw [← SetLike.mem_coe, ← ordBall_zero_eq_integer]
    exact hc0
  refine ⟨Ideal.Quotient.mk 𝓂[K] ⟨c, hcO⟩, ?_⟩
  rw [Algebra.smul_def, mul_one]
  change Ideal.Quotient.mk 𝓂[L] (algebraMap 𝒪[K] 𝒪[L] ⟨c, hcO⟩) = _
  rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
  exact (mem_ordBall_one_iff _).1 hc1

/-- **The residue degree of a quadratic extension.** The residue degree of $L / K$, defined with the degree map on $W_L$, is $2$ exactly when $L / K$ is unramified. -/
theorem wf_residueDegree_eq_two_iff : residueDegree K L = 2 ↔ IsUnramifiedExt K L := by
  rw [residueDegree_eq_residueFinrank]
  constructor
  · intro h
    by_contra hn
    have := wf_residueFinrank_eq_one L (isTotallyRamifiedExt_of_not_isUnramifiedExt hn)
    omega
  · intro hu
    have hd : residueFinrank K L ∣ 2 := by
      rw [← residueDegree_eq_residueFinrank, ← index_restrictSubgroup_eq_two
        (Algebra.IsQuadraticExtension.finrank_eq_two K L)]
      exact residueDegree_dvd_index K L
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h (wf_residueFinrank_ne_one L hu)
    · exact h

/-- The subgroup of the elements of even degree in $W_K$. It is the Weil group of the unramified quadratic extension. -/
noncomputable def wfEvenDegree (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Subgroup (WeilGroup K) :=
  (Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ))).comap (degree K)

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- The subgroup of the elements of even degree has index $2$. -/
theorem index_wfEvenDegree : (wfEvenDegree K).index = 2 := by
  rw [wfEvenDegree, Subgroup.index_comap_of_surjective _ (degree_surjective K),
    index_zpowers_ofAdd]
  rfl

/-- If $L / K$ is unramified, then $W_L$ is the subgroup of the elements of even degree. -/
theorem restrictSubgroup_eq_wfEvenDegree (hu : IsUnramifiedExt K L) :
    restrictSubgroup K L = wfEvenDegree K := by
  have hle : restrictSubgroup K L ≤ wfEvenDegree K := by
    intro w hw
    have h := map_degree_restrictSubgroup K L
    rw [(wf_residueDegree_eq_two_iff L).2 hu] at h
    have hm := Subgroup.mem_map_of_mem (degree K) hw
    rw [h] at hm
    exact hm
  have hi := Subgroup.relIndex_mul_index hle
  rw [index_wfEvenDegree, index_restrictSubgroup_eq_two
    (Algebra.IsQuadraticExtension.finrank_eq_two K L)] at hi
  have h1 : (restrictSubgroup K L).relIndex (wfEvenDegree K) = 1 := by omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h1)

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- **Uniqueness of the unramified quadratic extension** (`Langlands.LocalGL2.UniqueUnramifiedQuad`). Two unramified quadratic separable extensions of $K$ inside $\bar K$ are equal. Both Weil groups are the subgroup of the elements of even degree. -/
theorem uniqueUnramifiedQuad_holds : UniqueUnramifiedQuad K := by
  intro L L' _ _ _ _ hu hu'
  exact eq_of_restrictSubgroup_eq ((restrictSubgroup_eq_wfEvenDegree L hu).trans
    (restrictSubgroup_eq_wfEvenDegree L' hu').symm)

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- **The inertia group and unramified extensions** (`Langlands.LocalGL2.InertiaUnramified`). If the Weil group $W_L$ of a quadratic separable extension $L$ of $K$ contains $I_K$, then $L / K$ is unramified. The reason is that $W_L$ is then the inverse image of its image under the degree map, so its index $2$ is the residue degree. -/
theorem inertiaUnramified_holds : InertiaUnramified K := by
  intro L _ _ hI
  rw [← wf_residueDegree_eq_two_iff L]
  have hc : ((restrictSubgroup K L).map (degree K)).comap (degree K) = restrictSubgroup K L := by
    rw [Subgroup.comap_map_eq, ker_degree, sup_eq_left.2 hI]
  rw [residueDegree, ← Subgroup.index_comap_of_surjective _ (degree_surjective K), hc]
  exact index_restrictSubgroup_eq_two (Algebra.IsQuadraticExtension.finrank_eq_two K L)

end Ramification

section Main

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The inputs of `Langlands.LocalGL2.GaloisTameInputs` that are not proved in this file. The facts `Langlands.LocalGL2.InertiaUnramified`, `Langlands.LocalGL2.UniqueUnramifiedQuad` and `Langlands.LocalGL2.NormFactorU1` are not in this list, because this file proves them. -/
structure GaloisTameOpenInputs : Prop where
  /-- The local Artin maps of quadratic extensions are compatible with conjugation. -/
  conj : ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L], ArtinConjCompat K L
  /-- The wild inertia subgroup is a pro-$p$ group. -/
  wild : WildInertiaProP K
  /-- The tame inertia group is procyclic. -/
  tame : TameInertiaProcyclic K
  /-- Each open subgroup of index $2$ is the Weil group of a quadratic extension. -/
  indexTwo : OpenIndexTwoQuad K
  /-- The Artin map sends the principal units to the image of the wild inertia subgroup. -/
  wildArtin : WildArtinUnits K

variable {K}

/-- The open inputs and the facts proved in this file give `Langlands.LocalGL2.GaloisTameInputs`. -/
theorem GaloisTameOpenInputs.toGaloisTameInputs (I : GaloisTameOpenInputs K) :
    GaloisTameInputs K :=
  ⟨I.conj, I.wild, I.tame, I.indexTwo, inertiaUnramified_holds, uniqueUnramifiedQuad_holds,
    I.wildArtin, normFactorU1_holds⟩

/-- **The Galois side of the tame parametrization from the open inputs** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 34.1). The five facts in `Langlands.LocalGL2.GaloisTameOpenInputs` imply `Langlands.LocalGL2.GaloisTameParametrization`. -/
theorem galoisTameParametrization_of_openInputs (I : GaloisTameOpenInputs K) :
    GaloisTameParametrization K :=
  galoisTameParametrization_of_inputs I.toGaloisTameInputs

end Main

end Langlands.LocalGL2
