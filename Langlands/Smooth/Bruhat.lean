/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.Induction

/-!
# The Bruhat decomposition of GL(2) and Jacquet's lemma

Let $K$ be a field, $G = GL_2(K)$, $B$ the Borel subgroup of the upper triangular matrices, $N$ its unipotent radical and $w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. This file proves the Bruhat decomposition $G = B \sqcup BwN$, with the uniqueness of the decomposition $g = bwn$ on the big cell $BwN$.

It then proves Jacquet's lemma for a subgroup $N$ of a topological group $G$ that is the directed union of its compact open subgroups, as the unipotent radical $N \cong K$ of $GL_2(K)$ for a nonarchimedean local field $K$. A vector $v$ of a smooth representation is in $V(N)$ exactly when there is a compact open subgroup $N_0$ of $N$ such that the average of $\pi(n) v$ over $N_0$ is $0$. The average is the finite sum over $N_0 / (N_0 \cap \mathrm{Stab}(v))$, divided by the number of cosets. A consequence is that the Jacquet functor keeps injections, so it is exact.

At the end it gives the subspace $V_w$ of the principal series: the functions that vanish at $1$. These are the functions with support in the big cell, and $V_w$ is stable under $B$.

## Main definitions

* `Langlands.GL2.unip`: the matrix $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1 \end{pmatrix}$ of $N$.
* `Langlands.GL2.weyl`: the matrix $w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$.
* `Langlands.GL2.bigCell`: the big cell $BwN$.
* `Langlands.SmoothRep.cosetSum`: the sum of the vectors $\pi(n) v$ over a set of representatives $n$ of $N_0 / S$.
* `Langlands.SmoothRep.stabIn`: the subgroup $N_0 \cap \mathrm{Stab}(v)$ of $N_0$.
* `Langlands.SmoothRep.nAverage`: the average of $\pi(n) v$ over $N_0$, through the finite quotient $N_0 / (N_0 \cap \mathrm{Stab}(v))$.
* `Langlands.SmoothRep.IsCompactOpenSubgroupOf`: $N_0$ is a compact open subgroup of $N$.
* `Langlands.SmoothRep.HasCompactOpenExhaustion`: each finite subset of $N$ is in a compact open subgroup of $N$.
* `Langlands.GL2.unipBall`: the compact open subgroup of the $n(x)$ with $v(x) \le \gamma$.
* `Langlands.principalSeriesEvalOne`: the evaluation $f \mapsto f(1)$ on the principal series.
* `Langlands.principalSeriesBigCell`: the subspace $V_w$ of the functions that vanish at $1$.

## Main results

* `Langlands.GL2.bruhat`, `Langlands.GL2.disjoint_borel_bigCell`, `Langlands.GL2.bigCell_eq_compl`: the Bruhat decomposition $G = B \sqcup BwN$.
* `Langlands.GL2.mem_bigCell_iff`: $g \in BwN$ exactly when the lower left entry of $g$ is not $0$.
* `Langlands.GL2.bigCell_unique`: if $bwn = b'wn'$ with $b, b' \in B$ and $n, n' \in N$, then $b = b'$ and $n = n'$.
* `Langlands.SmoothRep.cosetSum_of_le`: for $S \le T$ and $v$ fixed by $T$, the sum over $N_0 / S$ is $[T : S]$ times the sum over $N_0 / T$.
* `Langlands.SmoothRep.mem_jacquetKer_iff`: Jacquet's lemma.
* `Langlands.SmoothRep.exists_forall_nAverage_eq_zero`: for $v \in V(N)$ the average vanishes on each compact open subgroup of $N$ that contains a given one.
* `Langlands.SmoothRep.jacquetMap_injective`: the Jacquet functor keeps injections.
* `Langlands.SmoothRep.jacquetMap_shortExact`: the Jacquet functor takes a short exact sequence to a short exact sequence.
* `Langlands.GL2.hasCompactOpenExhaustion_unipotent`: the unipotent radical $N$ of $GL_2(K)$ is the directed union of its compact open subgroups.
* `Langlands.SmoothRep.mem_jacquetKer_unipotent_iff`, `Langlands.SmoothRep.jacquetMap_unipotent_injective`, `Langlands.SmoothRep.jacquetMap_unipotent_shortExact`: these results for $N \subseteq GL_2(K)$.
* `Langlands.mem_principalSeriesBigCell_iff`: a function vanishes at $1$ exactly when its support is in the big cell.
* `Langlands.principalSeriesBigCell_stable`: the subspace $V_w$ is stable under $B$.

## Implementation notes

The average over $N_0$ uses no Haar measure. Since $v$ is smooth and $N_0$ is compact, $N_0 \cap \mathrm{Stab}(v)$ has finite index in $N_0$, and the average is a finite sum. For the proof that each vector of $V(N)$ has a vanishing average, the file uses the normal core of $N_1 \cap \mathrm{Stab}(w)$ in $N_1$: right translation by $n \in N_1$ permutes its cosets. Thus the proof does not use that $N$ is commutative.

The openness of $N_0$ in $N$ is part of the statement, but the proofs only use that $N_0$ is compact. The middle exactness in `Langlands.SmoothRep.jacquetMap_shortExact` repeats the proof of `Langlands.SmoothRep.jacquetMap_exact` of `Langlands/Smooth/PrincipalSeries.lean`, so that this file only imports `Langlands/Smooth/Induction.lean`.

The file does not compute the Jacquet module of $V_w$. This needs the identification of $V_w$ with the locally constant functions with compact support on $N \cong K$, through $f \mapsto (x \mapsto f(w n(x)))$, and integration over $N$. With the surjectivity of the evaluation at $1$ in `Langlands/Smooth/PrincipalSeries.lean`, it gives the exact sequence $0 \to V_w \to \mathrm{Ind}_B^G(\chi_1 \otimes \chi_2) \to \chi_1 \otimes \chi_2 \to 0$ of representations of $B$, and then that the Jacquet module of the principal series has dimension $2$.

## References

* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapter 2.
* W. Casselman, Introduction to the theory of admissible representations of p-adic reductive groups, unpublished notes, 1995, section 3.
* H. Jacquet, R. P. Langlands, Automorphic forms on GL(2), Lecture Notes in Mathematics 114, Springer, 1970.
-/

namespace Langlands

universe u

open Representation Matrix

section Bruhat

namespace GL2

variable {K : Type u} [Field K]

/-- The matrix $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1 \end{pmatrix}$ of $GL_2(K)$. -/
def unip (x : K) : GL (Fin 2) K :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

/-- The matrix of $n(x)$. -/
theorem unip_val (x : K) : (unip x).1 = !![1, x; 0, 1] :=
  rfl

/-- The matrix $n(x)$ is in $N$. -/
theorem unip_mem (x : K) : unip x ∈ unipotent K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [unip_val]

/-- Each element $n$ of $N$ is $n(x)$, with $x$ the upper right entry of $n$. -/
theorem eq_unip {n : GL (Fin 2) K} (hn : n ∈ unipotent K) : n = unip (n.1 0 1) := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine Units.ext ?_
  rw [unip_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

/-- The map $x \mapsto n(x)$ is a homomorphism: $n(x + y) = n(x) n(y)$. -/
theorem unip_add (x y : K) : unip (x + y) = unip x * unip y := by
  refine Units.ext ?_
  rw [Units.val_mul, unip_val, unip_val, unip_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The matrix $n(0)$ is $1$. -/
theorem unip_zero : unip (0 : K) = 1 := by
  refine Units.ext ?_
  rw [unip_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The inverse of $n(x)$ is $n(-x)$. -/
theorem unip_inv (x : K) : (unip x)⁻¹ = unip (-x) := by
  rw [inv_eq_iff_mul_eq_one, ← unip_add, add_neg_cancel, unip_zero]

/-- The map $x \mapsto n(x)$ is injective. -/
theorem unip_injective : Function.Injective (unip : K → GL (Fin 2) K) := by
  intro x y h
  have := congrArg (fun g : GL (Fin 2) K => g.1 0 1) h
  simpa [unip_val] using this

/-- The Weyl element $w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ of $GL_2(K)$. -/
def weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

/-- The matrix of $w$. -/
theorem weyl_val : (weyl : GL (Fin 2) K).1 = !![0, 1; 1, 0] :=
  rfl

/-- The Weyl element satisfies $w^2 = 1$. -/
theorem weyl_mul_weyl : (weyl : GL (Fin 2) K) * weyl = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, weyl_val]
  simp [Matrix.one_fin_two]

/-- The Weyl element is its own inverse. -/
theorem weyl_inv : (weyl : GL (Fin 2) K)⁻¹ = weyl := by
  rw [inv_eq_iff_mul_eq_one, weyl_mul_weyl]

/-- The Weyl element is not in $B$. -/
theorem weyl_not_mem_borel : (weyl : GL (Fin 2) K) ∉ borel K := by
  rw [mem_borel, weyl_val]
  simp

/-- The lower left entry of $w m w$ is the upper right entry of $m$. -/
theorem weyl_conj_val (m : GL (Fin 2) K) : (weyl * m * weyl).1 1 0 = m.1 0 1 := by
  rw [Units.val_mul, Units.val_mul, weyl_val, Matrix.eta_fin_two m.1]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- If $m \in N$ and $w m w \in B$, then $m = 1$. -/
theorem eq_one_of_weyl_conj_mem_borel {m : GL (Fin 2) K} (hm : m ∈ unipotent K)
    (h : weyl * m * weyl ∈ borel K) : m = 1 := by
  rw [mem_borel, weyl_conj_val] at h
  rw [eq_unip hm, h, unip_zero]

/-- For $b \in B$, the lower left entry of $b w n(x)$ is the lower right entry of $b$. -/
theorem mul_weyl_mul_unip_val (b : GL (Fin 2) K) (hb : b ∈ borel K) (x : K) :
    (b * weyl * unip x).1 1 0 = b.1 1 1 := by
  rw [mem_borel] at hb
  rw [Units.val_mul, Units.val_mul, weyl_val, unip_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb]

variable (K) in
/-- The big cell $BwN$: the elements $bwn$ with $b \in B$ and $n \in N$. -/
def bigCell : Set (GL (Fin 2) K) :=
  {g | ∃ b ∈ borel K, ∃ n ∈ unipotent K, g = b * weyl * n}

/-- An element $g$ is in the big cell $BwN$ exactly when its lower left entry $c$ is not $0$. For $g = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ with $c \neq 0$, take $n = n(d/c)$ and $b = g (w n)^{-1}$. -/
theorem mem_bigCell_iff (g : GL (Fin 2) K) : g ∈ bigCell K ↔ g.1 1 0 ≠ 0 := by
  constructor
  · rintro ⟨b, hb, n, hn, rfl⟩
    rw [eq_unip hn, mul_weyl_mul_unip_val b hb]
    exact val_one_one_ne_zero hb
  · intro hc
    let x := g.1 1 1 / g.1 1 0
    refine ⟨g * (weyl * unip x)⁻¹, ?_, unip x, unip_mem x, by group⟩
    rw [mem_borel, _root_.mul_inv_rev, unip_inv, weyl_inv, Units.val_mul, Units.val_mul,
      unip_val, weyl_val]
    simp [Matrix.mul_apply, Fin.sum_univ_two, x]
    field_simp
    ring

/-- The Bruhat decomposition: each element of $GL_2(K)$ is in $B$ or in the big cell $BwN$. -/
theorem bruhat (g : GL (Fin 2) K) : g ∈ borel K ∨ g ∈ bigCell K := by
  rw [mem_bigCell_iff, mem_borel]
  exact em _

/-- The Borel subgroup $B$ and the big cell $BwN$ are disjoint. -/
theorem disjoint_borel_bigCell : Disjoint (borel K : Set (GL (Fin 2) K)) (bigCell K) := by
  rw [Set.disjoint_left]
  intro g hg hg'
  rw [mem_bigCell_iff] at hg'
  exact hg' hg

/-- The big cell $BwN$ is the complement of $B$ in $GL_2(K)$. -/
theorem bigCell_eq_compl : bigCell K = (borel K : Set (GL (Fin 2) K))ᶜ := by
  ext g
  rw [mem_bigCell_iff, Set.mem_compl_iff, SetLike.mem_coe, mem_borel]

/-- The uniqueness of the Bruhat decomposition on the big cell: if $bwn = b'wn'$ with $b, b' \in B$ and $n, n' \in N$, then $b = b'$ and $n = n'$. The element $b'^{-1} b = w n' n^{-1} w$ is in $B$, so $n' n^{-1} = 1$. -/
theorem bigCell_unique {b b' n n' : GL (Fin 2) K} (hb : b ∈ borel K) (hb' : b' ∈ borel K)
    (hn : n ∈ unipotent K) (hn' : n' ∈ unipotent K) (h : b * weyl * n = b' * weyl * n') :
    b = b' ∧ n = n' := by
  have hm : n' * n⁻¹ ∈ unipotent K := (unipotent K).mul_mem hn' ((unipotent K).inv_mem hn)
  have key : weyl * (n' * n⁻¹) * weyl = b'⁻¹ * b := by
    have : b'⁻¹ * b = weyl * n' * n⁻¹ * weyl⁻¹ :=
      calc b'⁻¹ * b = b'⁻¹ * (b * weyl * n) * n⁻¹ * weyl⁻¹ := by group
        _ = b'⁻¹ * (b' * weyl * n') * n⁻¹ * weyl⁻¹ := by rw [h]
        _ = weyl * n' * n⁻¹ * weyl⁻¹ := by group
    rw [this, weyl_inv]
    group
  have h1 := eq_one_of_weyl_conj_mem_borel hm
    (key ▸ (borel K).mul_mem ((borel K).inv_mem hb') hb)
  have hnn : n' = n := by rwa [mul_inv_eq_one] at h1
  subst hnn
  refine ⟨?_, rfl⟩
  simpa using h

end GL2

end Bruhat

section JacquetLemma

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- The sum $\sum_{q \in N_0 / S} \pi(n_q) v$, where $n_q \in N_0$ is a chosen representative of the left coset $q$. If $S$ fixes $v$, then the sum does not depend on the choice. -/
noncomputable def cosetSum (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀) (v : π.V) :
    π.V :=
  ∑ᶠ q : N₀ ⧸ S, π.ρ ((Quotient.out q : N₀) : G) v

omit [IsTopologicalGroup G] in
/-- For a finite quotient $N_0 / S$, `cosetSum` is a sum over a finite set. -/
theorem cosetSum_eq_sum (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀)
    [Fintype (N₀ ⧸ S)] (v : π.V) :
    π.cosetSum N₀ S v = ∑ q : N₀ ⧸ S, π.ρ ((Quotient.out q : N₀) : G) v :=
  finsum_eq_sum_of_fintype _

omit [IsTopologicalGroup G] in
/-- The coset sum is additive in $v$. -/
theorem cosetSum_add (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀) [S.FiniteIndex]
    (v w : π.V) : π.cosetSum N₀ S (v + w) = π.cosetSum N₀ S v + π.cosetSum N₀ S w := by
  have := Fintype.ofFinite (N₀ ⧸ S)
  simp only [cosetSum_eq_sum, map_add, Finset.sum_add_distrib]

omit [IsTopologicalGroup G] in
/-- The coset sum commutes with subtraction. -/
theorem cosetSum_sub (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀) [S.FiniteIndex]
    (v w : π.V) : π.cosetSum N₀ S (v - w) = π.cosetSum N₀ S v - π.cosetSum N₀ S w := by
  have := Fintype.ofFinite (N₀ ⧸ S)
  simp only [cosetSum_eq_sum, map_sub, Finset.sum_sub_distrib]

omit [IsTopologicalGroup G] in
/-- The coset sum is linear in $v$. -/
theorem cosetSum_smul (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀) [S.FiniteIndex]
    (c : ℂ) (v : π.V) : π.cosetSum N₀ S (c • v) = c • π.cosetSum N₀ S v := by
  have := Fintype.ofFinite (N₀ ⧸ S)
  simp only [cosetSum_eq_sum, map_smul, Finset.smul_sum]

omit [IsTopologicalGroup G] in
/-- The coset sum of $0$ is $0$. -/
theorem cosetSum_zero (π : SmoothRep G) (N₀ : Subgroup G) (S : Subgroup N₀) :
    π.cosetSum N₀ S 0 = 0 := by
  simp [cosetSum]

omit [IsTopologicalGroup G] in
/-- If $T$ fixes $v$ and $g T = g' T$, then $\pi(g) v = \pi(g') v$. -/
theorem ρ_eq_of_mk_eq (π : SmoothRep G) {N₀ : Subgroup G} {T : Subgroup N₀} {v : π.V}
    (hv : ∀ t ∈ T, π.ρ ((t : N₀) : G) v = v) {g g' : N₀}
    (h : (g : N₀ ⧸ T) = (g' : N₀ ⧸ T)) : π.ρ (g : G) v = π.ρ (g' : G) v := by
  rw [QuotientGroup.eq] at h
  have e : (g' : G) = g * ((g⁻¹ * g' : N₀) : G) := by simp
  rw [e, map_mul, Module.End.mul_apply, hv _ h]

omit [IsTopologicalGroup G] in
/-- For subgroups $S \le T$ of $N_0$ with $S$ of finite index and $T$ fixing $v$, the sum over $N_0 / S$ is $[T : S]$ times the sum over $N_0 / T$. -/
theorem cosetSum_of_le (π : SmoothRep G) {N₀ : Subgroup G} {S T : Subgroup N₀} (hST : S ≤ T)
    [S.FiniteIndex] {v : π.V} (hv : ∀ t ∈ T, π.ρ ((t : N₀) : G) v = v) :
    π.cosetSum N₀ S v = S.relIndex T • π.cosetSum N₀ T v := by
  have : T.FiniteIndex := Subgroup.finiteIndex_of_le hST
  have := Fintype.ofFinite (N₀ ⧸ S)
  have := Fintype.ofFinite (N₀ ⧸ T)
  have := Fintype.ofFinite (T ⧸ S.subgroupOf T)
  let e := Subgroup.quotientEquivProdOfLE hST
  let F : N₀ ⧸ T → π.V := fun q => π.ρ ((Quotient.out q : N₀) : G) v
  have key : ∀ x : N₀ ⧸ S, π.ρ ((Quotient.out x : N₀) : G) v = F (e x).1 := by
    intro x
    refine π.ρ_eq_of_mk_eq hv ?_
    have : (e x).1 = ((Quotient.out x : N₀) : N₀ ⧸ T) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    rw [this, QuotientGroup.out_eq']
  rw [cosetSum_eq_sum, cosetSum_eq_sum, Finset.sum_congr rfl fun x _ => key x,
    Equiv.sum_comp e (fun p => F p.1), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Finset.smul_sum, Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

omit [IsTopologicalGroup G] in
/-- For subgroups $S \le T$ of $N_0$ with $S$ of finite index and $T$ fixing $v$, the sum over $N_0 / S$ vanishes exactly when the sum over $N_0 / T$ vanishes. -/
theorem cosetSum_eq_zero_iff_of_le (π : SmoothRep G) {N₀ : Subgroup G} {S T : Subgroup N₀}
    (hST : S ≤ T) [S.FiniteIndex] {v : π.V} (hv : ∀ t ∈ T, π.ρ ((t : N₀) : G) v = v) :
    π.cosetSum N₀ S v = 0 ↔ π.cosetSum N₀ T v = 0 := by
  rw [π.cosetSum_of_le hST hv, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero, Nat.cast_eq_zero,
    or_iff_right]
  exact Subgroup.FiniteIndex.index_ne_zero

omit [IsTopologicalGroup G] in
/-- For a normal subgroup $S$ of finite index of $N_0$ that fixes $w$ and for $n \in N_0$, the sums of $\pi(n) w$ and of $w$ over $N_0 / S$ are equal. Right translation by $n$ permutes the cosets of $S$. -/
theorem cosetSum_ρ_of_normal (π : SmoothRep G) {N₀ : Subgroup G} {S : Subgroup N₀} [S.Normal]
    [S.FiniteIndex] {w : π.V} (hw : ∀ s ∈ S, π.ρ ((s : N₀) : G) w = w) (n : N₀) :
    π.cosetSum N₀ S (π.ρ (n : G) w) = π.cosetSum N₀ S w := by
  have := Fintype.ofFinite (N₀ ⧸ S)
  rw [cosetSum_eq_sum, cosetSum_eq_sum, ← Equiv.sum_comp (Equiv.mulRight ((n : N₀ ⧸ S)))
    (fun q => π.ρ ((Quotient.out q : N₀) : G) w)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul]
  refine π.ρ_eq_of_mk_eq hw ?_
  rw [Equiv.coe_mulRight, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']

omit [IsTopologicalGroup G] in
/-- If $N_0 \le N$ and the sum of $\pi(n) v$ over the finite quotient $N_0 / S$ is $0$, then $v \in V(N)$. The vector $[N_0 : S] v$ is the sum of the vectors $v - \pi(n) v$. -/
theorem mem_jacquetKer_of_cosetSum_eq_zero (π : SmoothRep G) {N N₀ : Subgroup G} (hN₀ : N₀ ≤ N)
    {S : Subgroup N₀} [S.FiniteIndex] {v : π.V} (h : π.cosetSum N₀ S v = 0) :
    v ∈ π.jacquetKer N := by
  have := Fintype.ofFinite (N₀ ⧸ S)
  have hk : (Fintype.card (N₀ ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hmem : (Fintype.card (N₀ ⧸ S) : ℂ) • v ∈ π.jacquetKer N := by
    have : (Fintype.card (N₀ ⧸ S) : ℂ) • v =
        ∑ q : N₀ ⧸ S, (v - π.ρ ((Quotient.out q : N₀) : G) v) := by
      rw [Finset.sum_sub_distrib, ← cosetSum_eq_sum, h, sub_zero, Finset.sum_const,
        Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this]
    refine Submodule.sum_mem _ fun q _ => ?_
    rw [← neg_sub]
    exact neg_mem (π.sub_mem_jacquetKer (hN₀ (Quotient.out q).2) v)
  have := (π.jacquetKer N).smul_mem (Fintype.card (N₀ ⧸ S) : ℂ)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this

/-- The subgroup $N_0 \cap \mathrm{Stab}(v)$ of $N_0$. -/
def stabIn (π : SmoothRep G) (N₀ : Subgroup G) (v : π.V) : Subgroup N₀ :=
  (vecStabilizer π.ρ v).subgroupOf N₀

omit [IsTopologicalGroup G] in
/-- An element $s$ of $N_0$ is in $N_0 \cap \mathrm{Stab}(v)$ exactly when $\pi(s) v = v$. -/
theorem mem_stabIn (π : SmoothRep G) {N₀ : Subgroup G} {v : π.V} (s : N₀) :
    s ∈ π.stabIn N₀ v ↔ π.ρ (s : G) v = v := by
  rw [stabIn, Subgroup.mem_subgroupOf, mem_vecStabilizer]

/-- For a compact subgroup $N_0$, the subgroup $N_0 \cap \mathrm{Stab}(v)$ is open in $N_0$, so it has finite index. -/
theorem finiteIndex_stabIn (π : SmoothRep G) {N₀ : Subgroup G} (hN₀ : IsCompact (N₀ : Set G))
    (v : π.V) : (π.stabIn N₀ v).FiniteIndex := by
  have : CompactSpace N₀ := isCompact_iff_compactSpace.mp hN₀
  have := Subgroup.quotient_finite_of_isOpen (π.stabIn N₀ v)
    ((π.smooth v).preimage continuous_subtype_val)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The average of $\pi(n) v$ over $N_0$: the sum over the quotient $N_0 / (N_0 \cap \mathrm{Stab}(v))$ divided by the number of cosets. For a compact $N_0$ the quotient is finite. With a Haar measure $dn$ of total mass $1$ on $N_0$, it is $\int_{N_0} \pi(n) v \, dn$. -/
noncomputable def nAverage (π : SmoothRep G) (N₀ : Subgroup G) (v : π.V) : π.V :=
  (Nat.card (N₀ ⧸ π.stabIn N₀ v) : ℂ)⁻¹ • π.cosetSum N₀ (π.stabIn N₀ v) v

/-- For a compact subgroup $N_0$, the average over $N_0$ vanishes exactly when the coset sum vanishes. -/
theorem nAverage_eq_zero_iff (π : SmoothRep G) {N₀ : Subgroup G} (hN₀ : IsCompact (N₀ : Set G))
    (v : π.V) : π.nAverage N₀ v = 0 ↔ π.cosetSum N₀ (π.stabIn N₀ v) v = 0 := by
  have := π.finiteIndex_stabIn hN₀ v
  rw [nAverage, smul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, ← Subgroup.index_eq_card,
    or_iff_right Subgroup.FiniteIndex.index_ne_zero]

/-- The subgroup $N_0$ is a compact open subgroup of $N$: $N_0 \le N$, $N_0$ is compact, and $N_0$ is open in $N$. -/
def IsCompactOpenSubgroupOf (N₀ N : Subgroup G) : Prop :=
  N₀ ≤ N ∧ IsCompact (N₀ : Set G) ∧ IsOpen ((Subtype.val : N → G) ⁻¹' (N₀ : Set G))

/-- The subgroup $N$ is the directed union of its compact open subgroups: each finite subset of $N$ is contained in a compact open subgroup of $N$. The unipotent radical $N \cong K$ of $GL_2(K)$ has this property. -/
def HasCompactOpenExhaustion (N : Subgroup G) : Prop :=
  ∀ s : Finset G, (s : Set G) ⊆ N → ∃ N₀, IsCompactOpenSubgroupOf N₀ N ∧ (s : Set G) ⊆ N₀

/-- For $v \in V(N)$ there is a finite subset $s$ of $N$ such that for each compact subgroup $N_1$ that contains $s$, the sum of $\pi(n) v$ over $N_1 / (N_1 \cap \mathrm{Stab}(v))$ is $0$. -/
theorem cosetSum_eq_zero_of_mem_jacquetKer (π : SmoothRep G) {N : Subgroup G} {v : π.V}
    (hv : v ∈ π.jacquetKer N) :
    ∃ s : Finset G, (s : Set G) ⊆ N ∧ ∀ N₁ : Subgroup G, IsCompact (N₁ : Set G) →
      (s : Set G) ⊆ N₁ → π.cosetSum N₁ (π.stabIn N₁ v) v = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨n, w⟩, rfl⟩ := hx
    refine ⟨{(n : G)}, by simp, fun N₁ hN₁ hs => ?_⟩
    have hn : (n : G) ∈ N₁ := hs (by simp)
    have := π.finiteIndex_stabIn hN₁ w
    let S := (π.stabIn N₁ w).normalCore
    have hSw : ∀ s ∈ S, π.ρ ((s : N₁) : G) w = w := fun s hs =>
      (π.mem_stabIn s).1 (Subgroup.normalCore_le _ hs)
    have hSx : S ≤ π.stabIn N₁ (π.ρ (n : G) w - w) := by
      intro s hs
      rw [mem_stabIn, map_sub, hSw s hs]
      congr 1
      have hc : (⟨n, hn⟩ : N₁)⁻¹ * s * ⟨n, hn⟩ ∈ S := by
        simpa using (Subgroup.Normal.conj_mem s hs (⟨n, hn⟩ : N₁)⁻¹)
      have e : ((s : N₁) : G) * n = n * (((⟨n, hn⟩ : N₁)⁻¹ * s * ⟨n, hn⟩ : N₁) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hSw _ hc]
    have := π.finiteIndex_stabIn hN₁ (π.ρ (n : G) w - w)
    refine (π.cosetSum_eq_zero_iff_of_le hSx fun t ht => (π.mem_stabIn t).1 ht).1 ?_
    rw [cosetSum_sub, π.cosetSum_ρ_of_normal hSw ⟨n, hn⟩, sub_self]
  | zero =>
    refine ⟨∅, by simp, fun N₁ _ _ => π.cosetSum_zero _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨s', hs', hy⟩ := hy
    refine ⟨s ∪ s', by simpa using ⟨hs, hs'⟩, fun N₁ hN₁ h => ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at h
    have := π.finiteIndex_stabIn hN₁ x
    have := π.finiteIndex_stabIn hN₁ y
    let S := π.stabIn N₁ x ⊓ π.stabIn N₁ y
    have hS : S ≤ π.stabIn N₁ (x + y) := fun t ht => by
      rw [mem_stabIn, map_add, (π.mem_stabIn t).1 ht.1, (π.mem_stabIn t).1 ht.2]
    have := π.finiteIndex_stabIn hN₁ (x + y)
    refine (π.cosetSum_eq_zero_iff_of_le hS fun t ht => (π.mem_stabIn t).1 ht).1 ?_
    rw [cosetSum_add,
      (π.cosetSum_eq_zero_iff_of_le (inf_le_left : S ≤ _) fun t ht => (π.mem_stabIn t).1 ht).2
        (hx N₁ hN₁ h.1),
      (π.cosetSum_eq_zero_iff_of_le (inf_le_right : S ≤ _) fun t ht => (π.mem_stabIn t).1 ht).2
        (hy N₁ hN₁ h.2), add_zero]
  | smul c x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    refine ⟨s, hs, fun N₁ hN₁ h => ?_⟩
    have := π.finiteIndex_stabIn hN₁ x
    have hS : π.stabIn N₁ x ≤ π.stabIn N₁ (c • x) := fun t ht => by
      rw [mem_stabIn, map_smul, (π.mem_stabIn t).1 ht]
    refine (π.cosetSum_eq_zero_iff_of_le hS fun t ht => (π.mem_stabIn t).1 ht).1 ?_
    rw [cosetSum_smul, hx N₁ hN₁ h, smul_zero]

/-- For $v \in V(N)$ there is a compact open subgroup $N_0$ of $N$ such that the average of $\pi(n) v$ over each compact open subgroup $N_1 \supseteq N_0$ of $N$ is $0$. -/
theorem exists_forall_nAverage_eq_zero (π : SmoothRep G) {N : Subgroup G}
    (hN : HasCompactOpenExhaustion N) {v : π.V} (hv : v ∈ π.jacquetKer N) :
    ∃ N₀, IsCompactOpenSubgroupOf N₀ N ∧
      ∀ N₁, IsCompactOpenSubgroupOf N₁ N → N₀ ≤ N₁ → π.nAverage N₁ v = 0 := by
  obtain ⟨s, hsN, hs⟩ := π.cosetSum_eq_zero_of_mem_jacquetKer hv
  obtain ⟨N₀, hN₀, hsN₀⟩ := hN s hsN
  exact ⟨N₀, hN₀, fun N₁ hN₁ h01 =>
    (π.nAverage_eq_zero_iff hN₁.2.1 v).2 (hs N₁ hN₁.2.1 (hsN₀.trans h01))⟩

/-- Jacquet's lemma: if $N$ is the directed union of its compact open subgroups, then $v \in V(N)$ exactly when there is a compact open subgroup $N_0$ of $N$ such that the average of $\pi(n) v$ over $N_0$ is $0$. -/
theorem mem_jacquetKer_iff (π : SmoothRep G) {N : Subgroup G} (hN : HasCompactOpenExhaustion N)
    (v : π.V) :
    v ∈ π.jacquetKer N ↔ ∃ N₀, IsCompactOpenSubgroupOf N₀ N ∧ π.nAverage N₀ v = 0 := by
  constructor
  · intro hv
    obtain ⟨N₀, hN₀, h⟩ := π.exists_forall_nAverage_eq_zero hN hv
    exact ⟨N₀, hN₀, h N₀ hN₀ le_rfl⟩
  · rintro ⟨N₀, hN₀, h⟩
    have := π.finiteIndex_stabIn hN₀.2.1 v
    exact π.mem_jacquetKer_of_cosetSum_eq_zero hN₀.1 ((π.nAverage_eq_zero_iff hN₀.2.1 v).1 h)

omit [IsTopologicalGroup G] in
/-- An injective map of representations keeps the stabilizer of a vector. -/
theorem vecStabilizer_map {π π' : SmoothRep G} (f : IntertwiningMap π.ρ π'.ρ)
    (hf : Function.Injective f) (v : π.V) :
    vecStabilizer π'.ρ (f v) = vecStabilizer π.ρ v := by
  ext g
  rw [mem_vecStabilizer, mem_vecStabilizer, ← IntertwiningMap.isIntertwining π.ρ π'.ρ f g v,
    hf.eq_iff]

/-- An injective map of representations commutes with the average over a compact subgroup. -/
theorem nAverage_map {π π' : SmoothRep G} (f : IntertwiningMap π.ρ π'.ρ)
    (hf : Function.Injective f) (N₀ : Subgroup G) (hN₀ : IsCompact (N₀ : Set G)) (v : π.V) :
    π'.nAverage N₀ (f v) = f (π.nAverage N₀ v) := by
  have hS : π'.stabIn N₀ (f v) = π.stabIn N₀ v := by
    rw [stabIn, stabIn, vecStabilizer_map f hf]
  have := π.finiteIndex_stabIn hN₀ v
  have := Fintype.ofFinite (N₀ ⧸ π.stabIn N₀ v)
  rw [nAverage, nAverage, hS, cosetSum_eq_sum, cosetSum_eq_sum, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact (IntertwiningMap.isIntertwining π.ρ π'.ρ f _ v).symm

/-- The Jacquet functor keeps injections: if $N$ is the directed union of its compact open subgroups and $V \to V'$ is injective, then $V_N \to V'_N$ is injective. This follows from Jacquet's lemma. -/
theorem jacquetMap_injective {π π' : SmoothRep G} {N M : Subgroup G}
    (hN : HasCompactOpenExhaustion N) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (f : IntertwiningMap π.ρ π'.ρ) (hf : Function.Injective f) :
    Function.Injective (jacquetMap hMN f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v, rfl⟩ := π.jacquetMk_surjective N M hMN x
  rw [jacquetMap_mk, jacquetMk_eq_zero_iff, π'.mem_jacquetKer_iff hN] at hx
  obtain ⟨N₀, hN₀, h⟩ := hx
  rw [nAverage_map f hf N₀ hN₀.2.1, ← map_zero f] at h
  rw [jacquetMk_eq_zero_iff, π.mem_jacquetKer_iff hN]
  exact ⟨N₀, hN₀, hf h⟩

omit [IsTopologicalGroup G] in
/-- The image of $V(N)$ under a surjective map of representations $V \to V'$ is $V'(N)$. -/
theorem jacquetKer_map_of_surjective {π π' : SmoothRep G} (N : Subgroup G)
    (f : IntertwiningMap π.ρ π'.ρ) (hf : Function.Surjective f) :
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

/-- The Jacquet functor is exact: if $N$ is the directed union of its compact open subgroups, then for a short exact sequence $0 \to V' \to V \to V'' \to 0$ of smooth representations, the sequence $0 \to V'_N \to V_N \to V''_N \to 0$ is exact. -/
theorem jacquetMap_shortExact {π' π π'' : SmoothRep G} {N M : Subgroup G}
    (hN : HasCompactOpenExhaustion N) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (g : IntertwiningMap π'.ρ π.ρ) (f : IntertwiningMap π.ρ π''.ρ) (hg : Function.Injective g)
    (hfg : Function.Exact g f) (hf : Function.Surjective f) :
    Function.Injective (jacquetMap hMN g) ∧ Function.Exact (jacquetMap hMN g) (jacquetMap hMN f) ∧
      Function.Surjective (jacquetMap hMN f) := by
  refine ⟨jacquetMap_injective hN hMN g hg, fun y => ?_, jacquetMap_surjective hMN f hf⟩
  obtain ⟨v, rfl⟩ := π.jacquetMk_surjective N M hMN y
  rw [jacquetMap_mk, jacquetMk_eq_zero_iff]
  constructor
  · intro hv
    rw [← jacquetKer_map_of_surjective N f hf] at hv
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
      rw [← jacquetKer_map_of_surjective N f hf]
      exact ⟨_, this, rfl⟩
    rw [map_sub, h0, zero_sub, neg_mem_iff] at h1
    exact h1

end SmoothRep

end JacquetLemma

section UnipotentExhaustion

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open ValuativeRel

namespace GL2

variable (K) in
/-- The subgroup of the $n(x) \in N$ with $v(x) \le \gamma$. -/
def unipBall (γ : ValueGroupWithZero K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ unipotent K ∧ valuation K (g.1 0 1) ≤ γ}
  mul_mem' {a b} ha hb := by
    refine ⟨(unipotent K).mul_mem ha.1 hb.1, ?_⟩
    rw [eq_unip ha.1, eq_unip hb.1, ← unip_add, unip_val]
    simpa [unip_val] using Valuation.map_add_le _ ha.2 hb.2
  one_mem' := ⟨(unipotent K).one_mem, by simp⟩
  inv_mem' {a} ha := by
    refine ⟨(unipotent K).inv_mem ha.1, ?_⟩
    rw [eq_unip ha.1, unip_inv, unip_val]
    simpa [unip_val] using ha.2

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element is in `unipBall K γ` exactly when it is in $N$ and its upper right entry has valuation at most $\gamma$. -/
theorem mem_unipBall {γ : ValueGroupWithZero K} (g : GL (Fin 2) K) :
    g ∈ unipBall K γ ↔ g ∈ unipotent K ∧ valuation K (g.1 0 1) ≤ γ :=
  Iff.rfl

/-- The map $x \mapsto n(x)$ from $K$ to $GL_2(K)$ is continuous. -/
theorem continuous_unip : Continuous (unip : K → GL (Fin 2) K) := by
  have h : ∀ f : K → Matrix (Fin 2) (Fin 2) K, (∀ i j, Continuous fun x => f x i j) →
      Continuous f := fun f hf => continuous_pi fun i => continuous_pi fun j => hf i j
  refine Units.continuous_iff.mpr ⟨h _ fun i j => ?_, h _ fun i j => ?_⟩
  · change Continuous fun x : K => !![(1 : K), x; 0, 1] i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun x : K => !![(1 : K), -x; 0, 1] i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The subgroup `unipBall K γ` is the image of the ball $\{x : v(x) \le \gamma\}$ under $x \mapsto n(x)$. -/
theorem coe_unipBall (γ : ValueGroupWithZero K) :
    (unipBall K γ : Set (GL (Fin 2) K)) = unip '' {x | valuation K x ≤ γ} := by
  ext g
  constructor
  · rintro ⟨hg, hγ⟩
    exact ⟨g.1 0 1, hγ, (eq_unip hg).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨unip_mem x, by simpa [unip_val] using hx⟩

/-- The subgroup `unipBall K γ` is compact. -/
theorem isCompact_unipBall (γ : ValueGroupWithZero K) :
    IsCompact (unipBall K γ : Set (GL (Fin 2) K)) := by
  rw [coe_unipBall]
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K γ).image continuous_unip

/-- For $\gamma \neq 0$ the ball $\{x : v(x) \le \gamma\}$ is open in $K$. -/
theorem isOpen_valuation_le {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {x : K | valuation K x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
  change valuation K (z - x) < γ at hz
  change valuation K z ≤ γ
  rw [show z = (z - x) + x by ring]
  exact Valuation.map_add_le _ hz.le hx

/-- For $\gamma \neq 0$ the subgroup `unipBall K γ` is a compact open subgroup of $N$. -/
theorem isCompactOpenSubgroupOf_unipBall {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    SmoothRep.IsCompactOpenSubgroupOf (unipBall K γ) (unipotent K) := by
  refine ⟨fun g hg => hg.1, isCompact_unipBall γ, ?_⟩
  have hc : Continuous fun n : unipotent K => (n : GL (Fin 2) K).1 0 1 :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 1
  convert hc.isOpen_preimage _ (isOpen_valuation_le hγ) using 1
  ext n
  exact and_iff_right n.2

/-- The unipotent radical $N$ of $GL_2(K)$ is the directed union of its compact open subgroups: a finite subset of $N$ is in `unipBall K γ` for $\gamma$ the largest valuation of the upper right entries, or $1$. -/
theorem hasCompactOpenExhaustion_unipotent :
    SmoothRep.HasCompactOpenExhaustion (unipotent K) := by
  classical
  intro s hs
  have : ∃ γ : ValueGroupWithZero K, γ ≠ 0 ∧ ∀ g ∈ s, valuation K (g.1 0 1) ≤ γ := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨γ, hγ, h⟩ := ih
      refine ⟨max γ (valuation K (a.1 0 1)),
        ne_of_gt (lt_of_lt_of_le (zero_lt_iff.2 hγ) (le_max_left _ _)), ?_⟩
      intro g hg
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact le_max_right _ _
      · exact (h g hg).trans (le_max_left _ _)
  obtain ⟨γ, hγ, h⟩ := this
  exact ⟨unipBall K γ, isCompactOpenSubgroupOf_unipBall hγ, fun g hg => ⟨hs hg, h g hg⟩⟩

end GL2

open GL2

/-- Jacquet's lemma for $GL_2(K)$: for a smooth representation of $GL_2(K)$, $v \in V(N)$ exactly when there is a compact open subgroup $N_0$ of $N$ such that the average of $\pi(n) v$ over $N_0$ is $0$. -/
theorem SmoothRep.mem_jacquetKer_unipotent_iff (π : SmoothRep (GL (Fin 2) K)) (v : π.V) :
    v ∈ π.jacquetKer (unipotent K) ↔
      ∃ N₀, SmoothRep.IsCompactOpenSubgroupOf N₀ (unipotent K) ∧ π.nAverage N₀ v = 0 :=
  π.mem_jacquetKer_iff hasCompactOpenExhaustion_unipotent v

/-- The Jacquet functor of $GL_2(K)$ with respect to $N$ keeps injections. -/
theorem SmoothRep.jacquetMap_unipotent_injective {π π' : SmoothRep (GL (Fin 2) K)}
    {M : Subgroup (GL (Fin 2) K)} (hMN : M ≤ Subgroup.normalizer (unipotent K : Set _))
    (f : IntertwiningMap π.ρ π'.ρ) (hf : Function.Injective f) :
    Function.Injective (SmoothRep.jacquetMap hMN f) :=
  SmoothRep.jacquetMap_injective hasCompactOpenExhaustion_unipotent hMN f hf

/-- The Jacquet functor of $GL_2(K)$ with respect to $N$ is exact: it takes a short exact sequence of smooth representations to a short exact sequence. -/
theorem SmoothRep.jacquetMap_unipotent_shortExact {π' π π'' : SmoothRep (GL (Fin 2) K)}
    {M : Subgroup (GL (Fin 2) K)} (hMN : M ≤ Subgroup.normalizer (unipotent K : Set _))
    (g : IntertwiningMap π'.ρ π.ρ) (f : IntertwiningMap π.ρ π''.ρ) (hg : Function.Injective g)
    (hfg : Function.Exact g f) (hf : Function.Surjective f) :
    Function.Injective (SmoothRep.jacquetMap hMN g) ∧
      Function.Exact (SmoothRep.jacquetMap hMN g) (SmoothRep.jacquetMap hMN f) ∧
      Function.Surjective (SmoothRep.jacquetMap hMN f) :=
  SmoothRep.jacquetMap_shortExact hasCompactOpenExhaustion_unipotent hMN g f hg hfg hf

end UnipotentExhaustion

section BigCellSubspace

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

/-- The evaluation $f \mapsto f(1)$ on the principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$, as a linear map. -/
noncomputable def principalSeriesEvalOne (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V →ₗ[ℂ] ULift.{u} ℂ where
  toFun f := SmoothRep.ind.toFun f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The subspace $V_w$ of the principal series: the functions $f$ with $f(1) = 0$. By `Langlands.mem_principalSeriesBigCell_iff` these are the functions with support in the big cell $BwN$. -/
noncomputable def principalSeriesBigCell (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) : Submodule ℂ (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V :=
  LinearMap.ker (principalSeriesEvalOne χ₁ χ₂ hχ₁ hχ₂)

/-- A function of the principal series vanishes at $1$ exactly when it vanishes outside the big cell $BwN$. For $b \in B$ the value $f(b)$ is $\chi_1(a)\chi_2(d) f(1)$. -/
theorem mem_principalSeriesBigCell_iff {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁}
    {hχ₂ : IsSmoothChar K χ₂} (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) :
    f ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂ ↔ ∀ g ∉ bigCell K, SmoothRep.ind.toFun f g = 0 := by
  change SmoothRep.ind.toFun f 1 = 0 ↔ _
  constructor
  · intro h g hg
    rw [bigCell_eq_compl, Set.notMem_compl_iff] at hg
    rw [← mul_one g, show g = ((⟨g, hg⟩ : GL2.borel K) : GL (Fin 2) K) from rfl,
      principalSeriesInd_mul_left, h, smul_zero]
  · intro h
    refine h 1 ?_
    rw [bigCell_eq_compl, Set.notMem_compl_iff]
    exact (GL2.borel K).one_mem

/-- The subspace $V_w$ is stable under $B$, since $(b \cdot f)(1) = f(b) = \chi_1(a)\chi_2(d) f(1)$. -/
theorem principalSeriesBigCell_stable (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) :
    IsStableSubspace ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ.comp (GL2.borel K).subtype)
      (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) := by
  intro b f hf
  change SmoothRep.ind.toFun f 1 = 0 at hf
  change SmoothRep.ind.toFun f (1 * (b : GL (Fin 2) K)) = 0
  rw [one_mul, ← mul_one (b : GL (Fin 2) K), principalSeriesInd_mul_left, hf, smul_zero]

end BigCellSubspace

end Langlands
