/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Pseudo-characters of dimension 2

A pseudo-character of dimension 2 of a group $G$ with values in a commutative ring $A$ is a pair of functions $t, d : G \to A$ that has the algebraic properties of the trace and the determinant of a representation $G \to GL_2(A)$. This file uses the form of Chenevier: $d$ is multiplicative, $t(1) = 2$, $t(gh) = t(hg)$, and $d(g)\, t(g^{-1} h) - t(g)\, t(h) + t(gh) = 0$. The last identity is the trace of the Cayley-Hamilton identity $g + d(g) g^{-1} = t(g)$, multiplied by $h$.

The file proves that the trace and the determinant of a representation are a pseudo-character, that a limit of pseudo-characters is a pseudo-character, that a limit of approximate pseudo-characters in a normed ring is a pseudo-character, and that a continuous function is determined by its values on a dense set. It also proves the limit lemma that the congruence argument for the Galois representations of modular forms uses: a sequence of continuous functions that converges on a dense set, with a uniform rate, converges uniformly to a continuous function.

## Main definitions

* `Langlands.Galois.IsPseudoCharTwo`: the pair $(t, d)$ is a pseudo-character of dimension 2.

## Main results

* `Langlands.Galois.isPseudoCharTwo_trace_det`: the trace and the determinant of a representation $G \to GL_2(A)$ are a pseudo-character of dimension 2.
* `Langlands.Galois.IsPseudoCharTwo.d_mul_d_inv`: $d(g)\, d(g^{-1}) = 1$, so $d$ takes values in $A^\times$.
* `Langlands.Galois.IsPseudoCharTwo.of_tendsto`: a pointwise limit of pseudo-characters with values in a Hausdorff topological ring is a pseudo-character.
* `Langlands.Galois.IsPseudoCharTwo.of_approx`: a pointwise limit of approximate pseudo-characters with values in a normed ring, with defects that tend to 0, is a pseudo-character.
* `Langlands.Galois.IsPseudoCharTwo.eq_of_eqOn_dense`: two continuous pseudo-characters that agree on a dense set are equal.
* `Langlands.Galois.exists_continuous_limit_of_dense`: if continuous functions $f_n$ are within $\delta_n \to 0$ of the values $v(s) \in E$ on a dense set $S$, with $E$ complete, then $f_n$ converges uniformly to a continuous function with values in $E$.

## References

* R. Taylor, Galois representations associated to Siegel modular forms of low weight, Duke Math. J. 63 (1991), Section 1.
* G. Chenevier, The p-adic analytic space of pseudocharacters of a profinite group and pseudorepresentations over arbitrary rings, in Automorphic forms and Galois representations, LMS Lecture Note Series 414 (2014), Section 7.
-/

namespace Langlands.Galois

open Filter Topology

section Algebra

variable {G A : Type*} [Group G] [CommRing A]

/-- The pair $(t, d)$ of functions $G \to A$ is a pseudo-character of dimension 2 if $t(1) = 2$, $t(gh) = t(hg)$, $d(1) = 1$, $d(gh) = d(g) d(h)$ and $d(g)\, t(g^{-1} h) - t(g)\, t(h) + t(gh) = 0$ for all $g, h \in G$. For a ring in which 2 is not a zero divisor this is equivalent to a determinant of dimension 2 in the sense of Chenevier (Lemma 7.7 of the paper of Chenevier), and to a pseudo-representation of dimension 2 in the sense of Taylor. -/
structure IsPseudoCharTwo (t d : G → A) : Prop where
  /-- The value at $1$ is $2$. -/
  map_one : t 1 = 2
  /-- The function $t$ is central. -/
  comm : ∀ g h, t (g * h) = t (h * g)
  /-- The value of $d$ at $1$ is $1$. -/
  det_one : d 1 = 1
  /-- The function $d$ is multiplicative. -/
  det_mul : ∀ g h, d (g * h) = d g * d h
  /-- The trace of the Cayley-Hamilton identity. -/
  rel : ∀ g h, d g * t (g⁻¹ * h) - t g * t h + t (g * h) = 0

/-- The determinant part $d$ of a pseudo-character takes values in $A^\times$: $d(g)\, d(g^{-1}) = 1$. -/
theorem IsPseudoCharTwo.d_mul_d_inv {t d : G → A} (h : IsPseudoCharTwo t d) (g : G) :
    d g * d g⁻¹ = 1 := by
  rw [← h.det_mul, mul_inv_cancel, h.det_one]

/-- For a $2 \times 2$ matrix $M$ with a left inverse $M'$ and each matrix $X$, $\det(M) \operatorname{tr}(M' X) - \operatorname{tr}(M) \operatorname{tr}(X) + \operatorname{tr}(M X) = 0$. -/
theorem det_mul_trace_inv_mul {M M' : Matrix (Fin 2) (Fin 2) A} (h : M' * M = 1)
    (X : Matrix (Fin 2) (Fin 2) A) :
    M.det * (M' * X).trace - M.trace * X.trace + (M * X).trace = 0 := by
  have hadj : M.adjugate = M.det • M' := by
    have h1 : M * M' = 1 := mul_eq_one_comm.1 h
    calc M.adjugate = M.adjugate * (M * M') := by rw [h1, Matrix.mul_one]
      _ = (M.adjugate * M) * M' := by rw [Matrix.mul_assoc]
      _ = M.det • M' := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have h2 : M.det * (M' * X).trace = (M.adjugate * X).trace := by
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [h2, Matrix.adjugate_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

/-- **The trace and the determinant of a representation are a pseudo-character.** For a representation $\rho : G \to GL_2(A)$, the pair $(\operatorname{tr} \rho, \det \rho)$ is a pseudo-character of dimension 2. -/
theorem isPseudoCharTwo_trace_det (ρ : G →* GL (Fin 2) A) :
    IsPseudoCharTwo (fun g => (ρ g : Matrix (Fin 2) (Fin 2) A).trace)
      (fun g => (ρ g : Matrix (Fin 2) (Fin 2) A).det) where
  map_one := by simp
  comm g h := by
    simp only [map_mul, Units.val_mul]
    exact Matrix.trace_mul_comm _ _
  det_one := by simp
  det_mul g h := by simp [Matrix.det_mul]
  rel g h := by
    have hinv : ((ρ g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (ρ g : Matrix _ _ A) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have := det_mul_trace_inv_mul hinv (ρ h : Matrix (Fin 2) (Fin 2) A)
    simpa only [map_mul, Units.val_mul] using this

end Algebra

section Topology

variable {G A : Type*} [Group G]

/-- **A limit of pseudo-characters is a pseudo-character.** Let $A$ be a Hausdorff topological ring and let $(t_i, d_i)$ be pseudo-characters along a nontrivial filter, with $t_i \to t$ and $d_i \to d$ pointwise. Then $(t, d)$ is a pseudo-character. -/
theorem IsPseudoCharTwo.of_tendsto [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {ι : Type*} {F : Filter ι} [F.NeBot] {tn dn : ι → G → A} {t d : G → A}
    (h : ∀ᶠ i in F, IsPseudoCharTwo (tn i) (dn i))
    (ht : ∀ g, Tendsto (fun i => tn i g) F (𝓝 (t g)))
    (hd : ∀ g, Tendsto (fun i => dn i g) F (𝓝 (d g))) : IsPseudoCharTwo t d where
  map_one := tendsto_nhds_unique (ht 1)
    (tendsto_const_nhds.congr' (h.mono fun i hi => hi.map_one.symm))
  comm g h' := tendsto_nhds_unique (ht (g * h'))
    ((ht (h' * g)).congr' (h.mono fun i hi => (hi.comm g h').symm))
  det_one := tendsto_nhds_unique (hd 1)
    (tendsto_const_nhds.congr' (h.mono fun i hi => hi.det_one.symm))
  det_mul g h' := tendsto_nhds_unique (hd (g * h'))
    (((hd g).mul (hd h')).congr' (h.mono fun i hi => (hi.det_mul g h').symm))
  rel g h' := by
    have hl : Tendsto (fun i => dn i g * tn i (g⁻¹ * h') - tn i g * tn i h' + tn i (g * h')) F
        (𝓝 (d g * t (g⁻¹ * h') - t g * t h' + t (g * h'))) :=
      (((hd g).mul (ht _)).sub ((ht g).mul (ht h'))).add (ht _)
    exact tendsto_nhds_unique hl
      (tendsto_const_nhds.congr' (h.mono fun i hi => (hi.rel g h').symm))

/-- If $x_n \to a$ in a normed group and $\|x_n\| \le \varepsilon_n$ with $\varepsilon_n \to 0$, then $a = 0$. -/
theorem eq_zero_of_tendsto_of_norm_le {E : Type*} [NormedAddCommGroup E] {x : ℕ → E} {a : E}
    {ε : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 a)) (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ n, ‖x n‖ ≤ ε n) : a = 0 := by
  have h : ‖a‖ ≤ 0 := le_of_tendsto_of_tendsto' hx.norm hε hle
  exact norm_le_zero_iff.1 h

/-- **A limit of approximate pseudo-characters is a pseudo-character.** Let $A$ be a normed commutative ring, and let $t_n \to t$ and $d_n \to d$ pointwise. If each identity of a pseudo-character holds for $(t_n, d_n)$ up to an error of norm at most $\varepsilon_n$, with $\varepsilon_n \to 0$, then $(t, d)$ is a pseudo-character. -/
theorem IsPseudoCharTwo.of_approx [NormedCommRing A] {tn dn : ℕ → G → A} {t d : G → A}
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (ht : ∀ g, Tendsto (fun n => tn n g) atTop (𝓝 (t g)))
    (hd : ∀ g, Tendsto (fun n => dn n g) atTop (𝓝 (d g)))
    (h1 : ∀ n, ‖tn n 1 - 2‖ ≤ ε n)
    (hcomm : ∀ n g h, ‖tn n (g * h) - tn n (h * g)‖ ≤ ε n)
    (hd1 : ∀ n, ‖dn n 1 - 1‖ ≤ ε n)
    (hdmul : ∀ n g h, ‖dn n (g * h) - dn n g * dn n h‖ ≤ ε n)
    (hrel : ∀ n g h, ‖dn n g * tn n (g⁻¹ * h) - tn n g * tn n h + tn n (g * h)‖ ≤ ε n) :
    IsPseudoCharTwo t d where
  map_one := sub_eq_zero.1 (eq_zero_of_tendsto_of_norm_le ((ht 1).sub_const 2) hε h1)
  comm g h := sub_eq_zero.1
    (eq_zero_of_tendsto_of_norm_le ((ht _).sub (ht _)) hε fun n => hcomm n g h)
  det_one := sub_eq_zero.1 (eq_zero_of_tendsto_of_norm_le ((hd 1).sub_const 1) hε hd1)
  det_mul g h := sub_eq_zero.1
    (eq_zero_of_tendsto_of_norm_le ((hd _).sub ((hd g).mul (hd h))) hε fun n => hdmul n g h)
  rel g h := eq_zero_of_tendsto_of_norm_le
    ((((hd g).mul (ht _)).sub ((ht g).mul (ht h))).add (ht _)) hε fun n => hrel n g h

/-- **A continuous pseudo-character is determined on a dense set.** Two continuous pseudo-characters with values in a Hausdorff space that agree on a dense subset of $G$ are equal. With the theorem of Chebotarev, which gives that the Frobenius elements are dense in a Galois group, this is the statement that a continuous pseudo-character of a Galois group is determined by its values at the Frobenius elements. -/
theorem IsPseudoCharTwo.eq_of_eqOn_dense [CommRing A] [TopologicalSpace A] [T2Space A]
    [TopologicalSpace G] {t d t' d' : G → A} (_h : IsPseudoCharTwo t d)
    (_h' : IsPseudoCharTwo t' d') (ht : Continuous t) (hd : Continuous d) (ht' : Continuous t')
    (hd' : Continuous d') {S : Set G} (hS : Dense S) (htS : Set.EqOn t t' S)
    (hdS : Set.EqOn d d' S) : t = t' ∧ d = d' :=
  ⟨ht.ext_on hS ht' htS, hd.ext_on hS hd' hdS⟩

/-- If a continuous function $f$ to a normed group has $\|f(s)\| \le c$ on a dense set, then $\|f(x)\| \le c$ for each $x$. -/
theorem norm_le_of_dense {X E : Type*} [TopologicalSpace X] [SeminormedAddCommGroup E]
    {f : X → E} (hf : Continuous f) {S : Set X} (hS : Dense S) {c : ℝ}
    (h : ∀ s ∈ S, ‖f s‖ ≤ c) (x : X) : ‖f x‖ ≤ c := by
  have hc : IsClosed {x | ‖f x‖ ≤ c} := isClosed_le hf.norm continuous_const
  have : closure S ⊆ {x | ‖f x‖ ≤ c} := hc.closure_subset_iff.2 h
  exact this (hS.closure_eq ▸ Set.mem_univ x)

/-- **Uniform limits from a dense set.** Let $S$ be a dense subset of a topological space $X$, let $E$ be a complete subset of a metric space $Y$, let $v : X \to Y$ take values in $E$ on $S$, and let $f_n : X \to Y$ be continuous with $d(f_n(s), v(s)) \le \delta_n$ for $s \in S$, where $\delta_n > 0$ decreases to 0. Then there is a continuous $F : X \to E$ with $d(f_n(x), F(x)) \le \delta_n$ for each $x$. Moreover $F(x) = y$ for each $x$ and $y$ with $d(f_n(x), y) \le \delta_n$ for each $n$. -/
theorem exists_continuous_limit_of_dense {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {S : Set X} (hS : Dense S) {E : Set Y} (hE : IsComplete E) (v : X → Y)
    (hv : ∀ s ∈ S, v s ∈ E) (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (δ : ℕ → ℝ)
    (hδ0 : ∀ n, 0 < δ n) (hδ : Antitone δ) (hδt : Tendsto δ atTop (𝓝 0))
    (hfv : ∀ n, ∀ s ∈ S, dist (f n s) (v s) ≤ δ n) :
    ∃ F : X → Y, Continuous F ∧ (∀ x, F x ∈ E) ∧ (∀ n x, dist (f n x) (F x) ≤ δ n) ∧
      ∀ x y, (∀ n, dist (f n x) y ≤ δ n) → F x = y := by
  have hpair : ∀ n m x, dist (f n x) (f m x) ≤ δ n + δ m := by
    intro n m x
    have hc : IsClosed {x | dist (f n x) (f m x) ≤ δ n + δ m} :=
      isClosed_le ((hf n).dist (hf m)) continuous_const
    have : closure S ⊆ {x | dist (f n x) (f m x) ≤ δ n + δ m} :=
      hc.closure_subset_iff.2 fun s hs =>
        (dist_triangle_right _ _ (v s)).trans (add_le_add (hfv n s hs) (hfv m s hs))
    exact this (hS.closure_eq ▸ Set.mem_univ x)
  have hnear : ∀ n x, ∃ e ∈ E, dist (f n x) e < 2 * δ n := by
    intro n x
    have hc : IsClosed (f n ⁻¹' Metric.cthickening (δ n) E) :=
      Metric.isClosed_cthickening.preimage (hf n)
    have : closure S ⊆ f n ⁻¹' Metric.cthickening (δ n) E :=
      hc.closure_subset_iff.2 fun s hs =>
        Metric.mem_cthickening_of_dist_le _ _ _ _ (hv s hs) (hfv n s hs)
    have hx := this (hS.closure_eq ▸ Set.mem_univ x)
    have hx' := Metric.cthickening_subset_thickening' (δ₂ := 2 * δ n) (by linarith [hδ0 n])
      (by linarith [hδ0 n]) E hx
    exact Metric.mem_thickening_iff.1 hx'
  have hlim : ∀ x, ∃ y ∈ E, Tendsto (fun n => f n x) atTop (𝓝 y) := by
    intro x
    choose e heE he using fun n => hnear n x
    have hcau : CauchySeq e := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 6 * δ N) (fun n m N hn hm => ?_) ?_
      · calc dist (e n) (e m) ≤ dist (e n) (f n x) + dist (f n x) (f m x) + dist (f m x) (e m) :=
              dist_triangle4 _ _ _ _
          _ ≤ 2 * δ n + (δ n + δ m) + 2 * δ m := by
              rw [dist_comm (e n)]
              exact add_le_add (add_le_add (he n).le (hpair n m x)) (he m).le
          _ ≤ 6 * δ N := by linarith [hδ hn, hδ hm]
      · simpa using hδt.const_mul 6
    obtain ⟨y, hyE, hy⟩ := cauchySeq_tendsto_of_isComplete hE heE hcau
    refine ⟨y, hyE, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun n => 2 * δ n + dist (e n) y) atTop (𝓝 0) := by
      simpa using (hδt.const_mul 2).add (tendsto_iff_dist_tendsto_zero.1 hy)
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h2
    exact (dist_triangle _ (e n) _).trans (by linarith [(he n).le])
  choose F hFE hFt using hlim
  have hbound : ∀ n x, dist (f n x) (F x) ≤ δ n := by
    intro n x
    have h := le_of_tendsto_of_tendsto' (tendsto_const_nhds.dist (hFt x))
      (tendsto_const_nhds.add hδt) fun m => hpair n m x
    simpa using h
  have hunif : TendstoUniformly f F atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hδt.eventually (gt_mem_nhds hε)] with n hn x
    rw [dist_comm]
    exact (hbound n x).trans_lt hn
  refine ⟨F, hunif.continuous (Frequently.of_forall hf), hFE, hbound, fun x y hy => ?_⟩
  refine tendsto_nhds_unique (hFt x) ?_
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) hy hδt

end Topology

end Langlands.Galois
