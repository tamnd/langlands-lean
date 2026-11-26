/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.JacquetFinite

/-!
# Matrix coefficients of Jacquet cuspidal representations of $GL_2$

Let $K$ be a nonarchimedean local field, $G = GL_2(K)$, $K_0 = GL_2(\mathcal{O}_K)$, $N$ the upper unipotent subgroup, $T$ the diagonal torus and $Z \cong K^\times$ the centre. This file proves that a Jacquet cuspidal smooth representation $\pi$ of $G$ (the Jacquet module $\pi_N$ is $0$) is supercuspidal in the sense of `Langlands.SmoothRep.IsSupercuspidal`: each matrix coefficient $g \mapsto \lambda(\pi(g) v)$ with $\lambda$ a smooth vector of the dual has support in $C Z$ for a compact set $C$. The proof does not use admissibility.

## Main definitions

The file has no new definitions.

## Main results

* `Langlands.GL2.cartan`: the Cartan decomposition $G = K_0 T K_0$.
* `Langlands.SmoothRep.exists_coeff_diag_eq_zero_of_lt`: for $\pi$ Jacquet cuspidal there is $\varepsilon \neq 0$ with $\lambda(\pi(\mathrm{diag}(a, d)) v) = 0$ for $v(a/d) < \varepsilon$.
* `Langlands.SmoothRep.exists_coeff_diag_ne_zero`: for $\pi$ Jacquet cuspidal there is $\varepsilon \neq 0$ such that $\lambda(\pi(\mathrm{diag}(a, d)) v) \neq 0$ implies $\varepsilon \le v(a/d)$ and $\varepsilon \le v(d/a)$. Thus the coefficient on $T$ has support compact modulo $Z$.
* `Langlands.SmoothRep.isSupercuspidal_of_isJacquetCuspidal`: a Jacquet cuspidal smooth representation of $GL_2(K)$ is supercuspidal.

## Proof

Let $v \in V$. Since $\pi_N = 0$, Jacquet's lemma gives $\gamma \neq 0$ such that the average of $\pi(n) v$ over $N_\gamma = \{n(x) : v(x) \le \gamma\}$ is $0$. Let $\lambda$ be fixed by the $n(y)$ with $v(y) < \delta$. For $t = \mathrm{diag}(a, d)$ we have $t n(x) t^{-1} = n(a x / d)$. If $v(a/d) \gamma < \delta$, then $\lambda(\pi(t) \pi(n) v) = \lambda(\pi(t) v)$ for each $n \in N_\gamma$, so $\lambda(\pi(t) v)$ is $\lambda$ of $\pi(t)$ applied to the average, which is $0$. The Weyl element $w$ satisfies $w \, \mathrm{diag}(a, d) \, w = \mathrm{diag}(d, a)$, and the same argument for $\pi(w) v$ and $\lambda \circ \pi(w)$ gives the vanishing for $v(d/a)$ small.

For the whole group, the Cartan decomposition writes $g = k_1 t k_2$ with $k_1, k_2 \in K_0$. Then $\lambda(\pi(g) v) = (\pi^\vee(k_1^{-1}) \lambda)(\pi(t) \pi(k_2) v)$. The vectors $\pi(k_2) v$ and $\pi^\vee(k_1^{-1}) \lambda$ take finitely many values, because their stabilizers are open in the compact group $K_0$. The minimum of the finitely many bounds $\varepsilon$ gives an integer $m$ such that a nonzero coefficient at $g$ forces $t \in \mathrm{diag}(\varpi^k, 1) (T \cap K_0) Z$ with $|k| \le m$. The compact set is $C = \bigcup_{|k| \le m} K_0 \, \mathrm{diag}(\varpi^k, 1) \, K_0$.

The Cartan decomposition is proved by elimination. Move an entry of largest valuation to the upper left corner with the Weyl element. Then $g = \bar n(r/p) \, \mathrm{diag}(p, \det g / p) \, n(q/p)$ for $g = \begin{pmatrix} p & q \\ r & s \end{pmatrix}$, and the two unipotent matrices are in $K_0$.

## Open parts

* The file does not prove the converse: a supercuspidal representation in the sense of `Langlands.SmoothRep.IsSupercuspidal` is Jacquet cuspidal. This needs a nonzero matrix coefficient on $T$ with support that is not compact modulo $Z$ when $\pi_N \neq 0$, for example from the pairing of $\pi_N$ with the Jacquet module of the smooth dual (Casselman), and admissibility of $\pi$.
-/

universe u

open Representation Matrix ValuativeRel

namespace Langlands

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

namespace GL2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Conjugation by $t = \mathrm{diag}(a, d)$ scales the upper unipotent matrices: $t \, n(x) = n(a x / d) \, t$. -/
theorem diagTorusHom_mul_unip (a d : Kˣ) (x : K) :
    ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) * unip x =
      unip ((a : K) * x / d) * (diagTorusHom (a, d) : torus K) := by
  refine Units.ext ?_
  change !![(a : K), 0; 0, (d : K)] * !![1, x; 0, 1] =
    !![1, (a : K) * x / d; 0, 1] * !![(a : K), 0; 0, (d : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Weyl element exchanges the diagonal entries: $w \, \mathrm{diag}(a, d) \, w = \mathrm{diag}(d, a)$. -/
theorem weyl_mul_diagTorusHom_mul_weyl (a d : Kˣ) :
    (weyl : GL (Fin 2) K) * ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) * weyl =
      ((diagTorusHom (d, a) : torus K) : GL (Fin 2) K) := by
  refine Units.ext ?_
  change !![(0 : K), 1; 1, 0] * !![(a : K), 0; 0, (d : K)] * !![(0 : K), 1; 1, 0] =
    !![(d : K), 0; 0, (a : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $v(x) \le 1$ the matrix $n(x)$ is in $GL_2(\mathcal{O}_K)$. -/
theorem unip_mem_maxCompact {x : K} (hx : valuation K x ≤ 1) : unip x ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change valuation K (!![1, x; 0, 1] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hx]
  · change valuation K (!![1, -x; 0, 1] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hx]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Weyl element is in $GL_2(\mathcal{O}_K)$. -/
theorem weyl_mem_maxCompact : (weyl : GL (Fin 2) K) ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change valuation K (!![0, 1; 1, 0] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp
  · change valuation K (!![0, 1; 1, 0] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For units $a, d$ of $\mathcal{O}_K$ the matrix $\mathrm{diag}(a, d)$ is in $GL_2(\mathcal{O}_K)$. -/
theorem diagTorusHom_mem_maxCompact {a d : Kˣ} (ha : valuation K (a : K) = 1)
    (hd : valuation K (d : K) = 1) :
    ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change valuation K (!![(a : K), 0; 0, (d : K)] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [ha, hd]
  · change valuation K (!![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)] i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [ha, hd]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Cartan decomposition when the upper left entry $p$ has the largest valuation in its row and its column: $g = \bar n(r/p) \, \mathrm{diag}(p, \det g / p) \, n(q/p)$ with $k_1 = \bar n(r/p)$ and $k_2 = n(q/p)$ in $GL_2(\mathcal{O}_K)$. -/
theorem exists_cartan_of_le (g : GL (Fin 2) K) (h01 : valuation K (g.1 0 1) ≤ valuation K (g.1 0 0))
    (h10 : valuation K (g.1 1 0) ≤ valuation K (g.1 0 0)) :
    ∃ k₁ ∈ maxCompact K, ∃ k₂ ∈ maxCompact K, ∃ a d : Kˣ,
      g = k₁ * ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) * k₂ := by
  have hdet := det_ne_zero g
  rw [Matrix.det_fin_two] at hdet
  have hp : g.1 0 0 ≠ 0 := by
    intro h
    rw [h, map_zero, le_zero_iff, map_eq_zero] at h01 h10
    apply hdet
    rw [h, h01, h10]
    ring
  have hp' : 0 < valuation K (g.1 0 0) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact hp
  have he : g.1.det / g.1 0 0 ≠ 0 := div_ne_zero (det_ne_zero g) hp
  refine ⟨lowerUnip (g.1 1 0 / g.1 0 0), lowerUnip_mem ?_, unip (g.1 0 1 / g.1 0 0),
    unip_mem_maxCompact ?_, Units.mk0 _ hp, Units.mk0 _ he, ?_⟩
  · rw [map_div₀]
    exact div_le_one_of_le₀ h10 hp'.le
  · rw [map_div₀]
    exact div_le_one_of_le₀ h01 hp'.le
  · refine Units.ext ?_
    change g.1 = !![1, 0; g.1 1 0 / g.1 0 0, 1] * !![g.1 0 0, 0; 0, g.1.det / g.1 0 0] *
      !![1, g.1 0 1 / g.1 0 0; 0, 1]
    rw [Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
    ring

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **Cartan decomposition.** Each $g \in GL_2(K)$ is $k_1 \, \mathrm{diag}(a, d) \, k_2$ with $k_1, k_2 \in GL_2(\mathcal{O}_K)$. An entry of largest valuation is moved to the upper left corner with the Weyl element, and `Langlands.GL2.exists_cartan_of_le` is applied. -/
theorem cartan (g : GL (Fin 2) K) :
    ∃ k₁ ∈ maxCompact K, ∃ k₂ ∈ maxCompact K, ∃ a d : Kˣ,
      g = k₁ * ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) * k₂ := by
  obtain ⟨⟨i, j⟩, hij⟩ := Finite.exists_max fun ij : Fin 2 × Fin 2 => valuation K (g.1 ij.1 ij.2)
  have hw := weyl_mem_maxCompact (K := K)
  have e1 : ∀ h : GL (Fin 2) K, ∀ i j, (h * weyl).1 i j = h.1 i (Equiv.swap 0 1 j) := by
    intro h i j
    rw [Units.val_mul, weyl_val]
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : ∀ h : GL (Fin 2) K, ∀ i j, (weyl * h).1 i j = h.1 (Equiv.swap 0 1 i) j := by
    intro h i j
    rw [Units.val_mul, weyl_val]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · exact exists_cartan_of_le g (hij (0, 1)) (hij (1, 0))
  · obtain ⟨k₁, hk₁, k₂, hk₂, a, d, h⟩ := exists_cartan_of_le (g * weyl)
      (by simpa [e1] using hij (0, 0)) (by simpa [e1] using hij (1, 1))
    refine ⟨k₁, hk₁, k₂ * weyl, (maxCompact K).mul_mem hk₂ hw, a, d, ?_⟩
    rw [← mul_assoc, ← h, mul_assoc, weyl_mul_weyl, mul_one]
  · obtain ⟨k₁, hk₁, k₂, hk₂, a, d, h⟩ := exists_cartan_of_le (weyl * g)
      (by simpa [e2] using hij (1, 1)) (by simpa [e2] using hij (0, 0))
    refine ⟨weyl * k₁, (maxCompact K).mul_mem hw hk₁, k₂, hk₂, a, d, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc k₁, ← h, ← mul_assoc, weyl_mul_weyl, one_mul]
  · obtain ⟨k₁, hk₁, k₂, hk₂, a, d, h⟩ := exists_cartan_of_le (weyl * g * weyl)
      (by simpa [e1, e2] using hij (1, 0)) (by simpa [e1, e2] using hij (0, 1))
    refine ⟨weyl * k₁, (maxCompact K).mul_mem hw hk₁, k₂ * weyl,
      (maxCompact K).mul_mem hk₂ hw, a, d, ?_⟩
    have : g = weyl * (weyl * g * weyl) * weyl := by
      simp only [← mul_assoc, weyl_mul_weyl, one_mul]
      rw [mul_assoc, weyl_mul_weyl, mul_one]
    rw [this, h]
    group

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The matrix $\mathrm{diag}(d, d)$ is the scalar matrix of $d$. -/
theorem diagTorusHom_self (d : Kˣ) :
    ((diagTorusHom (d, d) : torus K) : GL (Fin 2) K) = scalarGL K 2 d := by
  refine Units.ext ?_
  change !![(d : K), 0; 0, (d : K)] = Matrix.scalar (Fin 2) (d : K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A scalar matrix commutes with each element of $GL_2(K)$. -/
theorem scalarGL_mul_comm (d : Kˣ) (g : GL (Fin 2) K) : scalarGL K 2 d * g = g * scalarGL K 2 d :=
  Units.ext (Matrix.scalar_commute (d : K) (fun _ => Commute.all _ _) g.1).eq

end GL2

namespace SmoothRep

omit [IsNonarchimedeanLocalField K] in
/-- If $h$ fixes the linear form $\lambda$ under the dual action, then $\lambda(\pi(h) w) = \lambda(w)$ for each $w$. -/
theorem apply_ρ_of_mem_vecStabilizer {G : Type u} [Group G] [TopologicalSpace G] (π : SmoothRep G)
    {l : Module.Dual ℂ π.V} {h : G} (hh : h ∈ vecStabilizer π.ρ.dual l) (w : π.V) :
    l (π.ρ h w) = l w := by
  have h' : π.ρ.dual h⁻¹ l = l := (vecStabilizer π.ρ.dual l).inv_mem hh
  conv_rhs => rw [← h']
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

/-- If $\pi$ is Jacquet cuspidal, then for each $v$ there is $\gamma \neq 0$ such that the average of $\pi(n) v$ over the compact subgroup $\{n(x) : v(x) \le \gamma\}$ of $N$ is $0$. -/
theorem exists_nAverage_unipBall_eq_zero (π : SmoothRep (GL (Fin 2) K))
    (hc : π.IsJacquetCuspidal) (v : π.V) :
    ∃ γ : ValueGroupWithZero K, γ ≠ 0 ∧ π.nAverage (unipBall K γ) v = 0 := by
  classical
  have hv : v ∈ π.jacquetKer (unipotent K) :=
    (π.jacquetMk_eq_zero_iff _ v).1 (@Subsingleton.elim _ hc _ _)
  obtain ⟨s, hs, h⟩ := π.cosetSum_eq_zero_of_mem_jacquetKer hv
  have : ∃ γ : ValueGroupWithZero K, γ ≠ 0 ∧ ∀ g ∈ s, valuation K (g.1 0 1) ≤ γ := by
    clear hs h
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
  obtain ⟨γ, hγ, hsγ⟩ := this
  refine ⟨γ, hγ, (π.nAverage_eq_zero_iff (isCompact_unipBall γ) v).2
    (h _ (isCompact_unipBall γ) fun g hg => ⟨hs hg, hsγ g hg⟩)⟩

/-- **Vanishing on the torus, first half.** Let $\pi$ be Jacquet cuspidal, $v \in V$, and $\lambda$ a linear form with open stabilizer. Then there is $\varepsilon \neq 0$ such that $\lambda(\pi(\mathrm{diag}(a, d)) v) = 0$ for each $a, d$ with $v(a/d) < \varepsilon$. -/
theorem exists_coeff_diag_eq_zero_of_lt (π : SmoothRep (GL (Fin 2) K)) (hc : π.IsJacquetCuspidal)
    (v : π.V) {l : Module.Dual ℂ π.V}
    (hl : IsOpen (vecStabilizer π.ρ.dual l : Set (GL (Fin 2) K))) :
    ∃ ε : ValueGroupWithZero K, ε ≠ 0 ∧ ∀ a d : Kˣ, valuation K ((a : K) / d) < ε →
      l (π.ρ ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) v) = 0 := by
  obtain ⟨γ, hγ, h0⟩ := exists_nAverage_unipBall_eq_zero π hc v
  have hO : IsOpen (unip ⁻¹' (vecStabilizer π.ρ.dual l : Set (GL (Fin 2) K))) :=
    continuous_unip.isOpen_preimage _ hl
  have hO0 : (0 : K) ∈ unip ⁻¹' (vecStabilizer π.ρ.dual l : Set (GL (Fin 2) K)) := by
    rw [Set.mem_preimage, unip_zero]
    exact (vecStabilizer _ _).one_mem
  obtain ⟨δ, hδ⟩ := IsValuativeTopology.mem_nhds_iff'.1 (hO.mem_nhds hO0)
  refine ⟨(δ : ValueGroupWithZero K) * γ⁻¹, mul_ne_zero δ.ne_zero (inv_ne_zero hγ),
    fun a d had => ?_⟩
  set t : GL (Fin 2) K := ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) with ht
  let f : π.V →ₗ[ℂ] ℂ := l ∘ₗ π.ρ t
  have key : f (π.nAverage (unipBall K γ) v) = f v := by
    refine π.map_nAverage (isCompact_unipBall γ) f fun g hg => ?_
    have hx : valuation K (g.1 0 1) ≤ γ := hg.2
    have hmem : unip ((a : K) * g.1 0 1 / d) ∈ vecStabilizer π.ρ.dual l := by
      refine hδ (show valuation K (_ - 0) < δ from ?_)
      rw [sub_zero, mul_div_right_comm, map_mul]
      exact (mul_le_mul_right hx _).trans_lt ((lt_mul_inv_iff₀ (zero_lt_iff.2 hγ)).1 had)
    change l (π.ρ t (π.ρ g v)) = l (π.ρ t v)
    rw [eq_unip hg.1, ← Module.End.mul_apply, ← map_mul, ht, diagTorusHom_mul_unip, map_mul,
      Module.End.mul_apply, apply_ρ_of_mem_vecStabilizer π hmem]
  rw [h0, map_zero] at key
  exact key.symm

/-- **Vanishing on the torus.** Let $\pi$ be Jacquet cuspidal, $v \in V$, and $\lambda$ a linear form with open stabilizer. Then there is $\varepsilon \neq 0$ such that $\lambda(\pi(\mathrm{diag}(a, d)) v) \neq 0$ implies $\varepsilon \le v(a/d)$ and $\varepsilon \le v(d/a)$. The second bound follows from the first for $\pi(w) v$ and $\lambda \circ \pi(w)$. -/
theorem exists_coeff_diag_ne_zero (π : SmoothRep (GL (Fin 2) K)) (hc : π.IsJacquetCuspidal)
    (v : π.V) {l : Module.Dual ℂ π.V}
    (hl : IsOpen (vecStabilizer π.ρ.dual l : Set (GL (Fin 2) K))) :
    ∃ ε : ValueGroupWithZero K, ε ≠ 0 ∧ ∀ a d : Kˣ,
      l (π.ρ ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) v) ≠ 0 →
        ε ≤ valuation K ((a : K) / d) ∧ ε ≤ valuation K ((d : K) / a) := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_coeff_diag_eq_zero_of_lt π hc v hl
  have hl' : IsOpen (vecStabilizer π.ρ.dual (π.ρ.dual weyl l) : Set (GL (Fin 2) K)) :=
    smoothVectors_stable π.ρ.dual weyl (show l ∈ smoothVectors π.ρ.dual from hl)
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_coeff_diag_eq_zero_of_lt π hc (π.ρ weyl v) hl'
  refine ⟨min ε₁ ε₂, ?_, fun a d had => ⟨?_, ?_⟩⟩
  · rcases min_choice ε₁ ε₂ with h | h <;> rw [h] <;> assumption
  · by_contra h
    exact had (h₁ a d ((not_le.1 h).trans_le (min_le_left _ _)))
  · by_contra h
    refine had ?_
    have := h₂ d a ((not_le.1 h).trans_le (min_le_right _ _))
    rw [← this]
    simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      weyl_inv]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      weyl_mul_diagTorusHom_mul_weyl]

/-- **Jacquet cuspidal representations are supercuspidal.** If the Jacquet module $\pi_N$ of a smooth representation $\pi$ of $GL_2(K)$ is $0$, then each matrix coefficient of $\pi$ has support in $C Z$ for a compact set $C$ and the centre $Z$. Admissibility is not used. -/
theorem isSupercuspidal_of_isJacquetCuspidal (π : SmoothRep (GL (Fin 2) K))
    (hc : π.IsJacquetCuspidal) : π.IsSupercuspidal (scalarGL K 2) := by
  classical
  intro v l
  have hKc := isCompact_maxCompact (K := K)
  have : CompactSpace (maxCompact K) := isCompact_iff_compactSpace.mp hKc
  let S : Subgroup (maxCompact K) := (vecStabilizer π.ρ.dual l).subgroupOf (maxCompact K)
  have : Finite (maxCompact K ⧸ S) :=
    Subgroup.quotient_finite_of_isOpen S
      ((show IsOpen (vecStabilizer π.ρ.dual l : Set (GL (Fin 2) K)) from l.2).preimage
        continuous_subtype_val)
  have : Finite (maxCompact K ⧸ π.stabIn (maxCompact K) v) :=
    Subgroup.quotient_finite_of_isOpen _ ((π.smooth v).preimage continuous_subtype_val)
  let L : maxCompact K ⧸ S → Module.Dual ℂ π.V := fun q =>
    π.ρ.dual ((Quotient.out q : maxCompact K) : GL (Fin 2) K) l
  let W : maxCompact K ⧸ π.stabIn (maxCompact K) v → π.V := fun q =>
    π.ρ ((Quotient.out q : maxCompact K) : GL (Fin 2) K) v
  have hL : ∀ q, IsOpen (vecStabilizer π.ρ.dual (L q) : Set (GL (Fin 2) K)) := fun q =>
    smoothVectors_stable π.ρ.dual _ l.2
  have hε := fun p : (maxCompact K ⧸ S) × (maxCompact K ⧸ π.stabIn (maxCompact K) v) =>
    exists_coeff_diag_ne_zero π hc (W p.2) (hL p.1)
  choose ε hε0 hε using hε
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min ε
  obtain ⟨e, he⟩ := valuation_surjective (ε p₀)
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hε0 p₀ (by simpa using he.symm)
  obtain ⟨n, hn⟩ := exists_valuation_eq_zpow he0
  rw [he] at hn
  obtain ⟨c, hcϖ⟩ := valuation_surjective (uniformizer K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (uniformizer_ne_zero (R := K)) (by simpa using hcϖ.symm)
  set ϖ : Kˣ := Units.mk0 c hc0
  let D : ℤ → GL (Fin 2) K := fun k => ((diagTorusHom (ϖ ^ k, 1) : torus K) : GL (Fin 2) K)
  refine ⟨⋃ k ∈ Finset.Icc (-n) n,
    (fun p : GL (Fin 2) K × GL (Fin 2) K => p.1 * D k * p.2) '' (maxCompact K ×ˢ maxCompact K),
    (Finset.Icc (-n) n).isCompact_biUnion fun k _ => (hKc.prod hKc).image
      ((continuous_fst.mul continuous_const).mul continuous_snd), fun g hg => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, a, d, rfl⟩ := cartan g
  let q₁ : maxCompact K ⧸ S := ((⟨k₁⁻¹, (maxCompact K).inv_mem hk₁⟩ : maxCompact K) : _)
  let q₂ : maxCompact K ⧸ π.stabIn (maxCompact K) v := ((⟨k₂, hk₂⟩ : maxCompact K) : _)
  have hq₂ : π.ρ k₂ v = W q₂ :=
    π.ρ_eq_of_mk_eq (fun s hs => (π.mem_stabIn s).1 hs) (g := ⟨k₂, hk₂⟩)
      (QuotientGroup.out_eq' q₂).symm
  have hq₁ : π.ρ.dual k₁⁻¹ l = L q₁ := by
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₁).symm
    rw [Subgroup.mem_subgroupOf, mem_vecStabilizer] at h
    change π.ρ.dual k₁⁻¹ l = π.ρ.dual ((Quotient.out q₁ : maxCompact K) : GL (Fin 2) K) l
    have e : ((Quotient.out q₁ : maxCompact K) : GL (Fin 2) K) =
        k₁⁻¹ * (((⟨k₁⁻¹, (maxCompact K).inv_mem hk₁⟩ : maxCompact K)⁻¹ * Quotient.out q₁ :
          maxCompact K) : GL (Fin 2) K) := by
      simp
    rw [e, map_mul, Module.End.mul_apply, h]
  have hcoeff : L q₁ (π.ρ ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) (W q₂)) ≠ 0 := by
    rw [← hq₁, ← hq₂]
    simpa [coeff, Representation.dual_apply, Module.Dual.transpose_apply, map_mul] using hg
  obtain ⟨h₁, h₂⟩ := hε (q₁, q₂) a d hcoeff
  have h₁' := (hp₀ (q₁, q₂)).trans h₁
  have h₂' := (hp₀ (q₁, q₂)).trans h₂
  rw [hn] at h₁' h₂'
  have had : (a : K) / d ≠ 0 := div_ne_zero a.ne_zero d.ne_zero
  obtain ⟨k, hk⟩ := exists_valuation_eq_zpow had
  rw [hk, uniformizer_zpow_le_iff] at h₁'
  rw [← inv_div, map_inv₀, hk, ← _root_.zpow_neg, uniformizer_zpow_le_iff] at h₂'
  have hϖ : valuation K (ϖ : K) = uniformizer K := hcϖ
  let u : Kˣ := a * d⁻¹ * (ϖ ^ k)⁻¹
  have hu : valuation K (u : K) = 1 := by
    have : (u : K) = (a : K) / d * ((ϖ : K) ^ k)⁻¹ := by
      simp [u, div_eq_mul_inv, Units.val_zpow_eq_zpow_val]
    rw [this, map_mul, map_inv₀, map_zpow₀, hk, hϖ,
      mul_inv_cancel₀ (zpow_ne_zero _ uniformizer_ne_zero)]
  have hdec : ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) =
      D k * ((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * scalarGL K 2 d := by
    rw [← diagTorusHom_self]
    simp only [D, ← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    congr 3
    refine Units.ext ?_
    simp only [u, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨k₁ * D k * (((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * k₂),
    Set.mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      ⟨(k₁, ((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * k₂),
        ⟨hk₁, (maxCompact K).mul_mem (diagTorusHom_mem_maxCompact hu (by simp)) hk₂⟩, rfl⟩⟩,
    d, ?_⟩
  rw [hdec]
  simp only [mul_assoc, scalarGL_mul_comm d k₂]

end SmoothRep

end Langlands
