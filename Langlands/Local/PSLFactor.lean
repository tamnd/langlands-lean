/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1EpsilonFull
import Langlands.Local.SupercuspidalLFactor
import Langlands.Local.PSInputPropsProof
import Langlands.Local.PSContragredient

/-!
# The L-factor of a character of the determinant of GL(2)

Let $K$ be a nonarchimedean local field with residue field of $q$ elements and let $\chi$ be a smooth character of $K^\times$. This file proves the input `Langlands.LocalGL2.PSLFactorDetChar` of `Langlands/Local/GL2PrincipalSeriesInputs.lean`: the Godement-Jacquet L-factor of the character $\chi |\cdot|^{1/2} \circ \det$ of $GL_2(K)$ is $L(s, \chi) L(s, \chi |\cdot|)$.

A matrix coefficient of the character $\theta = \chi |\cdot|^{1/2} \circ \det$ is $\theta(g) \lambda(v)$. Thus the zeta integral of $\Phi$ is $\lambda(v) \int_{M_2(K)} \Phi(x) \chi(\det x) |\det x|^{s - 1} \, dx$. The file writes $M_2(K)$ as $K^4$ with the entries $(a, b, c, d)$, and computes this integral.

## Main definitions

* `Langlands.LocalGL2.PlGood`: the function $f$ is $A(q^{-s}) q^{ks} L(s)$ for $\mathrm{Re}(s)$ large, with a polynomial $A$.
* `Langlands.LocalGL2.plRep`: the representation $\chi |\cdot|^{1/2} \circ \det$ of $GL_2(K)$.
* `Langlands.LocalGL2.plEntries`: the homeomorphism $M_2(K) \to K^4$.

## Main results

* `Langlands.LocalGL2.pl_good_det`: for a locally constant $F$ with compact support on $K^4$, the integral $\int F(x) \chi(\det x) |\det x|^{s - 1} \, dx$ is good for $L(s, \chi) L(s, \chi |\cdot|)$.
* `Langlands.LocalGL2.pl_integral_box`: for an unramified $\chi$, the integral for $F = \mathbf{1}_{\mathcal{O}_K^4}$ is a nonzero constant times $L(s, \chi) L(s, \chi |\cdot|)$.
* `Langlands.LocalGL2.psLFactorDetChar_holds`: the input `Langlands.LocalGL2.PSLFactorDetChar`.
* `Langlands.LocalGL2.nonSupercuspidalInputs_of_lFactor`: the structure `Langlands.LocalGL2.NonSupercuspidalInputs` from the two open inputs `Langlands.LocalGL2.PSLFactorIrreducible` and `Langlands.LocalGL2.PSLFactorSteinberg`.

## Proof

Each point of $K^4$ with $(a, c) \ne (0, 0)$ satisfies exactly one of $\mathrm{ord}(c/a) \ge 0$ and $\mathrm{ord}(a/c) \ge 1$. The exchange of the two rows keeps the Haar measure and changes $\det$ to $-\det$. Thus the integral is the integral over the region $\mathrm{ord}(c/a) \ge 0$ plus $\chi(-1)$ times a second integral of the same type. On the region, the change of variables $c = a t$, $d = d' + t b$ gives $\det = a d'$, and the integral becomes $\int G(a, b, t, d') \chi|\cdot|(a) |a|^{s - 1} \chi(d') |d'|^{s - 1}$ for a locally constant $G$ with compact support. The function $G$ is a finite sum of products of indicators of balls. So the integral is a finite sum of products of two zeta integrals on $K$, one for $\chi |\cdot|$ and one for $\chi$, and Tate's computation in `Langlands/Local/GL1LFactor.lean` gives the result. For a ramified $\chi$ both L-factors are $1$, and `Langlands.LocalGL2.isGJLFactor_one_of_zeta` gives the last clause. For an unramified $\chi$ the function $\mathbf{1}_{\mathcal{O}_K^4}$ gives the L-factor.

## References

* R. Godement, H. Jacquet, Zeta functions of simple algebras, LNM 260, Springer, 1972, theorem 3.3.
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapter 6, section 26.
-/

namespace Langlands

universe u

namespace LocalGL2

open LocalGL1 MeasureTheory Topology Filter
open scoped NNReal ENNReal

section Box

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The box $(\varpi^N \mathcal{O}_K)^4$ in $K^4$. -/
def plBox (N : ℤ) : Set (K × K × K × K) :=
  ordBall K N ×ˢ (ordBall K N ×ˢ (ordBall K N ×ˢ ordBall K N))

/-- A point is in the box $(\varpi^N \mathcal{O}_K)^4$ exactly when its four coordinates are in $\varpi^N \mathcal{O}_K$. -/
theorem pl_mem_box {N : ℤ} {p : K × K × K × K} :
    p ∈ plBox N ↔ p.1 ∈ ordBall K N ∧ p.2.1 ∈ ordBall K N ∧ p.2.2.1 ∈ ordBall K N ∧
      p.2.2.2 ∈ ordBall K N := by
  simp [plBox, Set.mem_prod]

/-- Each box is compact. -/
theorem pl_isCompact_box (N : ℤ) : IsCompact (plBox (K := K) N) :=
  (isCompact_ordBall N).prod ((isCompact_ordBall N).prod
    ((isCompact_ordBall N).prod (isCompact_ordBall N)))

/-- Each box is open. -/
theorem pl_isOpen_box (N : ℤ) : IsOpen (plBox (K := K) N) :=
  (isOpen_ordBall N).prod ((isOpen_ordBall N).prod ((isOpen_ordBall N).prod (isOpen_ordBall N)))

/-- The boxes decrease when $N$ increases. -/
theorem pl_box_anti {M N : ℤ} (h : M ≤ N) : plBox (K := K) N ⊆ plBox M := fun p hp => by
  rw [pl_mem_box] at hp ⊢
  exact ⟨ordBall_anti h hp.1, ordBall_anti h hp.2.1, ordBall_anti h hp.2.2.1,
    ordBall_anti h hp.2.2.2⟩

/-- Each box is closed under addition. -/
theorem pl_add_mem_box {N : ℤ} {p h : K × K × K × K} (hp : p ∈ plBox N) (hh : h ∈ plBox N) :
    p + h ∈ plBox N := by
  rw [pl_mem_box] at hp hh ⊢
  exact ⟨add_mem_ordBall hp.1 hh.1, add_mem_ordBall hp.2.1 hh.2.1,
    add_mem_ordBall hp.2.2.1 hh.2.2.1, add_mem_ordBall hp.2.2.2 hh.2.2.2⟩

/-- Each box is closed under negation. -/
theorem pl_neg_mem_box {N : ℤ} {h : K × K × K × K} (hh : h ∈ plBox N) : -h ∈ plBox N := by
  rw [pl_mem_box] at hh ⊢
  exact ⟨neg_mem_ordBall hh.1, neg_mem_ordBall hh.2.1, neg_mem_ordBall hh.2.2.1,
    neg_mem_ordBall hh.2.2.2⟩

/-- Each neighbourhood of $0$ in $K^4$ contains a box. -/
theorem pl_exists_box_subset {U : Set (K × K × K × K)} (hU : U ∈ 𝓝 0) :
    ∃ N : ℤ, plBox N ⊆ U := by
  rw [show (0 : K × K × K × K) = (0, 0, 0, 0) from rfl] at hU
  obtain ⟨u1, hu1, v1, hv1, h1⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨u2, hu2, v2, hv2, h2⟩ := mem_nhds_prod_iff.1 hv1
  obtain ⟨u3, hu3, u4, hu4, h3⟩ := mem_nhds_prod_iff.1 hv2
  obtain ⟨N1, hN1⟩ := exists_ordBall_subset hu1
  obtain ⟨N2, hN2⟩ := exists_ordBall_subset hu2
  obtain ⟨N3, hN3⟩ := exists_ordBall_subset hu3
  obtain ⟨N4, hN4⟩ := exists_ordBall_subset hu4
  refine ⟨max (max N1 N2) (max N3 N4), fun p hp => ?_⟩
  rw [pl_mem_box] at hp
  refine h1 ⟨hN1 (ordBall_anti (by omega) hp.1), h2 ⟨hN2 (ordBall_anti (by omega) hp.2.1),
    h3 ⟨hN3 (ordBall_anti (by omega) hp.2.2.1), hN4 (ordBall_anti (by omega) hp.2.2.2)⟩⟩⟩

/-- Each compact set in $K^4$ is in a box. -/
theorem pl_exists_box_superset {S : Set (K × K × K × K)} (hS : IsCompact S) :
    ∃ M : ℤ, S ⊆ plBox M := by
  obtain ⟨n, hn⟩ := hS.elim_directed_cover (fun n : ℕ => plBox (K := K) (-(n : ℤ)))
    (fun n => pl_isOpen_box _) (fun p _ => by
      obtain ⟨M1, h1⟩ := exists_mem_ordBall p.1
      obtain ⟨M2, h2⟩ := exists_mem_ordBall p.2.1
      obtain ⟨M3, h3⟩ := exists_mem_ordBall p.2.2.1
      obtain ⟨M4, h4⟩ := exists_mem_ordBall p.2.2.2
      refine Set.mem_iUnion.2 ⟨(-(min (min M1 M2) (min M3 M4))).toNat, ?_⟩
      rw [pl_mem_box]
      exact ⟨ordBall_anti (by omega) h1, ordBall_anti (by omega) h2, ordBall_anti (by omega) h3,
        ordBall_anti (by omega) h4⟩)
    (fun m n => ⟨max m n, pl_box_anti (by push_cast; omega), pl_box_anti (by push_cast; omega)⟩)
  exact ⟨_, hn⟩

/-- The point $0$ is in each box. -/
theorem pl_zero_mem_box (N : ℤ) : (0 : K × K × K × K) ∈ plBox N :=
  pl_mem_box.2 ⟨zero_mem_ordBall _, zero_mem_ordBall _, zero_mem_ordBall _, zero_mem_ordBall _⟩

/-- The point $x$ is in the translate $x + (\varpi^N \mathcal{O}_K)^4$. -/
theorem pl_zero_mem_box' {N : K × K × K × K → ℤ} (x : K × K × K × K) :
    x ∈ {y | y - x ∈ plBox (N x)} := by
  simpa using pl_zero_mem_box (N x)

/-- **Uniform local constancy on $K^4$.** -/
theorem pl_exists_forall_add_eq {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F)
    (hFs : HasCompactSupport F) :
    ∃ M N : ℤ, M ≤ N ∧ (∀ p ∉ plBox M, F p = 0) ∧ ∀ p, ∀ h ∈ plBox N, F (p + h) = F p := by
  obtain ⟨M, hM⟩ := pl_exists_box_superset hFs
  have hloc : ∀ x : K × K × K × K, ∃ N : ℤ, ∀ h ∈ plBox N, F (x + h) = F x := by
    intro x
    have h1 : ∀ᶠ y in 𝓝 x, F y = F x := (IsLocallyConstant.iff_eventually_eq F).1 hF x
    have h2 : {h | F (x + h) = F x} ∈ 𝓝 (0 : K × K × K × K) :=
      ((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)).eventually h1
    obtain ⟨N, hN⟩ := pl_exists_box_subset h2
    exact ⟨N, fun h hh => hN hh⟩
  choose Nx hNx using hloc
  obtain ⟨T, hT⟩ := (pl_isCompact_box (K := K) M).elim_finite_subcover
    (fun t => {x | x - t ∈ plBox (Nx t)}) (fun t => (pl_isOpen_box _).preimage
      (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, pl_zero_mem_box' x⟩)
  set N : ℤ := max M (∑ t ∈ T, ((Nx t).natAbs : ℤ)) with hNdef
  have hNt : ∀ t ∈ T, Nx t ≤ N := fun t ht => le_max_of_le_right
    ((Int.le_natAbs).trans (Finset.single_le_sum (f := fun t => ((Nx t).natAbs : ℤ))
      (fun t _ => by positivity) ht))
  have hzero : ∀ x ∉ plBox M, F x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hM h)
  refine ⟨M, N, le_max_left _ _, hzero, fun x h hh => ?_⟩
  by_cases hx : x ∈ plBox M
  · obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 (hT hx)
    have hxt' : x - t ∈ plBox (Nx t) := hxt
    have hh' : h ∈ plBox (Nx t) := pl_box_anti (hNt t ht) hh
    have e1 := hNx t (x - t) hxt'
    have e2 := hNx t (x - t + h) (pl_add_mem_box hxt' hh')
    rw [show t + (x - t) = x by abel] at e1
    rw [show t + (x - t + h) = x + h by abel] at e2
    rw [e1, e2]
  · have hxh : x + h ∉ plBox M := fun h' =>
      hx (by simpa using pl_add_mem_box h' (pl_neg_mem_box (pl_box_anti (le_max_left _ _) hh)))
    rw [hzero x hx, hzero _ hxh]

/-- **A partition of a ball into translates.** For $M \le N$ there is a finite set $T \subseteq \varpi^M \mathcal{O}_K$ such that the translates $b + \varpi^N \mathcal{O}_K$ for $b \in T$ partition $\varpi^M \mathcal{O}_K$. -/
theorem pl_exists_partition {M N : ℤ} (hMN : M ≤ N) :
    ∃ T : Finset K, (∀ b ∈ T, b ∈ ordBall K M) ∧
      ∀ x, ∑ b ∈ T, ballIndicator b N x = (ordBall K M).indicator 1 x := by
  classical
  set G : AddSubgroup K := ordBallAddSubgroup N
  have hG : ∀ x y : K, (QuotientAddGroup.mk x : K ⧸ G) = QuotientAddGroup.mk y ↔
      y - x ∈ ordBall K N := by
    intro x y
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    rfl
  set S : Set (K ⧸ G) := QuotientAddGroup.mk '' ordBall K M
  obtain ⟨T0, hT0⟩ := exists_finset_ordBall_subset (K := K) M N
  have hS : S.Finite := by
    refine ((T0.finite_toSet).image (QuotientAddGroup.mk : K → K ⧸ G)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.1 (hT0 hy)
    exact ⟨t, ht, (hG t y).2 hyt⟩
  have hmem : ∀ x y : K, y ∈ ordBall K M → x - y ∈ ordBall K N → x ∈ ordBall K M := by
    intro x y hy hxy
    simpa using add_mem_ordBall (ordBall_anti hMN hxy) hy
  have hout : ∀ q : K ⧸ G, (QuotientAddGroup.mk (Quotient.out q) : K ⧸ G) = q :=
    fun q => QuotientAddGroup.out_eq' q
  refine ⟨hS.toFinset.image Quotient.out, fun b hb => ?_, fun x => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨y, hy, hyq⟩ := (Set.Finite.mem_toFinset hS).1 hq
    refine hmem _ y hy ((hG y _).1 ?_)
    rw [hout, hyq]
  rw [Finset.sum_image fun q₁ _ q₂ _ h => by rw [← hout q₁, ← hout q₂]; exact congrArg _ h]
  have hb : ∀ q : K ⧸ G, ballIndicator (Quotient.out q) N x =
      if (QuotientAddGroup.mk x : K ⧸ G) = q then 1 else 0 := by
    intro q
    rw [ballIndicator]
    by_cases h : (QuotientAddGroup.mk x : K ⧸ G) = q
    · rw [ite_eq_left h, Set.indicator_of_mem, Pi.one_apply]
      exact (hG _ x).1 (by rw [hout, h])
    · rw [ite_eq_right h, Set.indicator_of_notMem]
      intro h'
      exact h ((hG _ x).2 h' ▸ hout q)
  simp_rw [hb]
  rw [Finset.sum_ite_eq]
  by_cases hx : x ∈ ordBall K M
  · rw [ite_eq_left ((Set.Finite.mem_toFinset hS).2 ⟨x, hx, rfl⟩), Set.indicator_of_mem hx,
      Pi.one_apply]
  · rw [Set.indicator_of_notMem hx, ite_eq_right]
    intro h
    obtain ⟨y, hy, hyx⟩ := (Set.Finite.mem_toFinset hS).1 h
    exact hx (hmem x y hy ((hG y x).1 hyx))

/-- The product of four ball indicators is the indicator of a translated box. -/
theorem pl_prod_ballIndicator (N : ℤ) (r p : K × K × K × K) :
    ballIndicator r.1 N p.1 * ballIndicator r.2.1 N p.2.1 * ballIndicator r.2.2.1 N p.2.2.1 *
      ballIndicator r.2.2.2 N p.2.2.2 = (plBox N).indicator 1 (p - r) := by
  classical
  simp only [ballIndicator]
  rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply, Set.indicator_apply,
    Set.indicator_apply, pl_mem_box]
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.one_apply]
  split_ifs <;> simp_all

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A sum over $T^4$ of a product of four functions is the product of the four sums. -/
theorem pl_sum_box_prod (T : Finset K) (f g h k : K → ℂ) :
    ∑ r ∈ T ×ˢ T ×ˢ T ×ˢ T, f r.1 * g r.2.1 * h r.2.2.1 * k r.2.2.2 =
      (∑ b ∈ T, f b) * (∑ b ∈ T, g b) * (∑ b ∈ T, h b) * (∑ b ∈ T, k b) := by
  simp only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Decomposition into boxes.** A locally constant function $F$ with compact support on $K^4$ is a finite linear combination of products of four ball indicators. -/
theorem pl_exists_eq_sum {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F)
    (hFs : HasCompactSupport F) :
    ∃ (N : ℤ) (T : Finset K), ∀ p, F p = ∑ r ∈ T ×ˢ T ×ˢ T ×ˢ T, F r *
      (ballIndicator r.1 N p.1 * ballIndicator r.2.1 N p.2.1 * ballIndicator r.2.2.1 N p.2.2.1 *
        ballIndicator r.2.2.2 N p.2.2.2) := by
  obtain ⟨M, N, hMN, hzero, hadd⟩ := pl_exists_forall_add_eq hF hFs
  obtain ⟨T, -, hT⟩ := pl_exists_partition (K := K) hMN
  refine ⟨N, T, fun p => ?_⟩
  have h1 : ∀ r ∈ T ×ˢ T ×ˢ T ×ˢ T, F r * (ballIndicator r.1 N p.1 * ballIndicator r.2.1 N p.2.1 *
      ballIndicator r.2.2.1 N p.2.2.1 * ballIndicator r.2.2.2 N p.2.2.2) =
      F p * (ballIndicator r.1 N p.1 * ballIndicator r.2.1 N p.2.1 *
      ballIndicator r.2.2.1 N p.2.2.1 * ballIndicator r.2.2.2 N p.2.2.2) := by
    intro r _
    rw [pl_prod_ballIndicator]
    by_cases h : p - r ∈ plBox N
    · rw [← hadd r _ h, add_sub_cancel]
    · rw [Set.indicator_of_notMem h, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, pl_sum_box_prod T (fun b => ballIndicator b N p.1)
    (fun b => ballIndicator b N p.2.1) (fun b => ballIndicator b N p.2.2.1)
    (fun b => ballIndicator b N p.2.2.2), hT, hT, hT, hT]
  by_cases hp : p ∈ plBox M
  · rw [pl_mem_box] at hp
    simp [Set.indicator_of_mem, hp]
  · rw [hzero p hp, zero_mul]

end Box

section Measure

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- The product measure $\mu^{\otimes 4}$ on $K^4$. -/
noncomputable def plProd : Measure (K × K × K × K) :=
  μ.prod (μ.prod (μ.prod μ))

/-- The determinant $a d - b c$ of the point $(a, b, c, d)$ of $K^4$. -/
def plDet (p : K × K × K × K) : K :=
  p.1 * p.2.2.2 - p.2.1 * p.2.2.1

omit [MeasurableSpace K] [BorelSpace K] in
/-- The function `plDet` is continuous. -/
theorem pl_continuous_det : Continuous (plDet (K := K)) :=
  (continuous_fst.mul continuous_snd.snd.snd).sub (continuous_snd.fst.mul continuous_snd.snd.fst)

omit [MeasurableSpace K] [BorelSpace K] in
/-- On the box $(\varpi^M \mathcal{O}_K)^4$, the value of `plDet` is in $\varpi^{2M} \mathcal{O}_K$. -/
theorem pl_det_mem_ordBall {M : ℤ} {p : K × K × K × K} (hp : p ∈ plBox M) :
    plDet p ∈ ordBall K (M + M) := by
  rw [pl_mem_box] at hp
  rw [plDet, sub_eq_add_neg]
  exact add_mem_ordBall (mul_mem_ordBall_add hp.1 hp.2.2.2)
    (neg_mem_ordBall (mul_mem_ordBall_add hp.2.1 hp.2.2.1))

/-- The measure $\mu^{\otimes 4}$ is an additive Haar measure. -/
instance pl_isAddHaarMeasure_prod : (plProd μ).IsAddHaarMeasure := by
  unfold plProd
  have : (μ.prod μ).IsAddHaarMeasure := inferInstance
  have : (μ.prod (μ.prod μ)).IsAddHaarMeasure := inferInstance
  exact Measure.prod.instIsAddHaarMeasure μ (μ.prod (μ.prod μ))

omit [BorelSpace K] in
/-- **Fubini on $K^4$.** -/
theorem pl_integral_four {f : K × K × K × K → ℂ} (hf : Integrable f (plProd μ)) :
    ∫ p, f p ∂(plProd μ) = ∫ a, ∫ b, ∫ c, ∫ d, f (a, b, c, d) ∂μ ∂μ ∂μ ∂μ := by
  rw [plProd, integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with a ha
  rw [integral_prod _ ha]
  refine integral_congr_ae ?_
  filter_upwards [ha.prod_right_ae] with b hb
  exact integral_prod _ hb

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- If $|\chi(\varpi) q^{1 - s}| \le 1$, then $\chi(y) |y|^{s - 1}$ is bounded on each ball. -/
theorem pl_exists_bound_zetaFn (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖zetaRatio χ s‖ ≤ 1) (N : ℤ) : ∃ C, ∀ y ∈ ordBall K N, ‖zetaFn χ s y‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_extChar χ hχ
  have hr : 0 < ‖zetaRatio χ s‖ := norm_pos_iff.2 (zetaRatio_ne_zero χ s)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 one_mem_ordShell_zero)
  refine ⟨‖zetaRatio χ s‖ ^ N * C, fun y hy => ?_⟩
  by_cases hy0 : y = 0
  · rw [hy0, zetaFn_zero, norm_zero]
    exact mul_nonneg (zpow_nonneg hr.le _) hC0
  rw [zetaFn_eq_zetaRatio χ hy0, norm_mul, norm_zpow]
  exact mul_le_mul (zpow_le_zpow_right_of_le_one₀ hr hs ((mem_ordBall_of_ne_zero hy0).1 hy))
    (hC _ (mem_ordShell_zero_div hy0)) (norm_nonneg _) (zpow_nonneg hr.le _)

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- The function $\chi(y) |y|^{s - 1}$ is measurable. -/
theorem pl_measurable_zetaFn [MeasurableSpace K] [BorelSpace K] (χ : Kˣ →* ℂˣ)
    (hχ : IsSmoothChar K χ) (s : ℂ) : Measurable (zetaFn χ s) :=
  measurable_of_continuousOn_compl_singleton 0 (continuousOn_zetaFn χ hχ s)

/-- A bounded measurable function $H$ that is zero outside a box, times $\chi(\det) |\det|^{s - 1}$, is integrable on $K^4$. -/
theorem pl_integrable_mul_zetaFn_det (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖zetaRatio χ s‖ ≤ 1) {H : K × K × K × K → ℂ} (hHm : Measurable H) {C : ℝ}
    (hHC : ∀ p, ‖H p‖ ≤ C) {M : ℤ} (hH0 : ∀ p ∉ plBox M, H p = 0) :
    Integrable (fun p => H p * zetaFn χ s (plDet p)) (plProd μ) := by
  obtain ⟨D, hD⟩ := pl_exists_bound_zetaFn χ hχ hs (M + M)
  have hsupp : Function.support (fun p => H p * zetaFn χ s (plDet p)) ⊆ plBox M := by
    intro p hp
    by_contra h
    exact hp (by simp [hH0 p h])
  refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
  refine Measure.integrableOn_of_bounded (M := C * D) (pl_isCompact_box M).measure_lt_top.ne
    ((hHm.mul ((pl_measurable_zetaFn χ hχ s).comp
      pl_continuous_det.measurable)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (pl_isOpen_box M).measurableSet).2 (Eventually.of_forall fun p hp => ?_)
  rw [norm_mul]
  exact mul_le_mul (hHC p) (hD _ (pl_det_mem_ordBall hp)) (norm_nonneg _)
    ((norm_nonneg _).trans (hHC p))

end Measure

section Region

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The extension of $\chi |\cdot|$ to $K$ is $y \mapsto \chi(y) |y|$. -/
theorem pl_extChar_mul_abs (χ : Kˣ →* ℂˣ) (y : K) :
    LocalGL1.extChar (χ * absChar K) y = LocalGL1.extChar χ y * (normAbs K y : ℂ) := by
  by_cases hy : y = 0
  · rw [hy, extChar_zero, extChar_zero, zero_mul]
  rw [extChar_of_ne_zero _ hy, extChar_of_ne_zero _ hy, MonoidHom.mul_apply, Units.val_mul,
    absChar_apply, Units.val_mk0]

/-- For $a \ne 0$, $|a| \chi(a y) |a y|^{s - 1} = \chi(a) |a|^s \cdot \chi(y) |y|^{s - 1}$, where the first factor is the function of `Langlands.LocalGL1.zetaFn` for $\chi |\cdot|$. -/
theorem pl_zetaFn_mul_abs (χ : Kˣ →* ℂˣ) {a : K} (ha : a ≠ 0) (s : ℂ) (y : K) :
    (((residueCard K : ℝ) ^ (-ord K a) : ℝ) : ℂ) * zetaFn χ s (a * y) =
      zetaFn (χ * absChar K) s a * zetaFn χ s y := by
  rw [zetaFn_mul χ ha, zetaFn_eq _ ha, pl_extChar_mul_abs, extChar_of_ne_zero χ ha]
  rw [LocalGL1.normAbs_eq_zpow ha]
  push_cast
  ring

/-- The region $a \ne 0$, $c / a \in \varpi^m \mathcal{O}_K$ of $K^4$. -/
def plRegion (m : ℤ) : Set (K × K × K × K) :=
  {p | p.1 ≠ 0 ∧ p.2.2.1 * p.1⁻¹ ∈ ordBall K m}

/-- The function $(a, b, t, d) \mapsto \mathbf{1}_{\varpi^m \mathcal{O}_K}(t) F(a, b, a t, d + t b)$. The substitution $c = a t$, $d \mapsto d + t b$ takes the region `plRegion m` to this function. -/
noncomputable def plSub (m : ℤ) (F : K × K × K × K → ℂ) (p : K × K × K × K) : ℂ :=
  (ordBall K m).indicator 1 p.2.2.1 * F (p.1, p.2.1, p.1 * p.2.2.1, p.2.2.2 + p.2.2.1 * p.2.1)

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/-- **The substitution on the region.** For fixed $a, b$, the substitution $c = a t$ and $d \mapsto d + t b$ gives $\int \int_{c / a \in \varpi^m \mathcal{O}} F \chi(\det) |\det|^{s - 1} = \int \int G(a, b, t, d) \chi(a) |a|^s \chi(d) |d|^{s - 1}$. -/
theorem pl_region_iter (χ : Kˣ →* ℂˣ) (m : ℤ) (F : K × K × K × K → ℂ) (s : ℂ) (a b : K) :
    ∫ c, ∫ d, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) (a, b, c, d) ∂μ ∂μ =
      ∫ t, ∫ d, plSub m F (a, b, t, d) * zetaFn (χ * absChar K) s a * zetaFn χ s d ∂μ ∂μ := by
  by_cases ha : a = 0
  · subst ha
    have h1 : ∀ c d : K, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p))
        ((0 : K), b, c, d) = 0 := fun c d => Set.indicator_of_notMem (fun h => h.1 rfl) _
    simp [h1, zetaFn_zero]
  have hreg : ∀ t d, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) (a, b, a * t, d) =
      (ordBall K m).indicator 1 t * F (a, b, a * t, d) * zetaFn χ s (a * (d - t * b)) := by
    intro t d
    have ht' : a * t * a⁻¹ = t := by field_simp
    by_cases ht : t ∈ ordBall K m
    · rw [Set.indicator_of_mem (show (a, b, a * t, d) ∈ plRegion m from ⟨ha, by simpa [ht'] using ht⟩),
        Set.indicator_of_mem ht, Pi.one_apply, one_mul, plDet]
      congr 2
      ring
    · rw [Set.indicator_of_notMem (fun h => ht (by simpa [ht'] using h.2)),
        Set.indicator_of_notMem ht]
      simp
  have h1 := integral_comp_mul_left μ ha
    (fun c => ∫ d, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) (a, b, c, d) ∂μ)
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast residueCard_pos'
  have h1' : ∫ c, ∫ d, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) (a, b, c, d) ∂μ ∂μ =
      ((residueCard K : ℝ) ^ (-ord K a)) • ∫ t, ∫ d, (plRegion m).indicator
        (fun p => F p * zetaFn χ s (plDet p)) (a, b, a * t, d) ∂μ ∂μ := by
    rw [h1, smul_smul, ← zpow_add₀ hq.ne', neg_add_cancel, zpow_zero, one_smul]
  have h2 : ∀ t, ∫ d, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) (a, b, a * t, d) ∂μ =
      ∫ d, (ordBall K m).indicator 1 t * F (a, b, a * t, d + t * b) * zetaFn χ s (a * d) ∂μ := by
    intro t
    simp_rw [hreg]
    rw [← integral_add_right_eq_self _ (t * b)]
    simp only [add_sub_cancel_right]
  rw [h1']
  simp_rw [h2]
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun d => ?_)
  have e := pl_zetaFn_mul_abs χ ha s d
  simp only [plSub, Complex.real_smul]
  linear_combination ((ordBall K m).indicator 1 t * F (a, b, a * t, d + t * b)) * e

end Region

section Product

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [BorelSpace K] in
/-- The integral of a product of four functions of the four coordinates. -/
theorem pl_integral_prod4 (f₁ f₂ f₃ f₄ : K → ℂ) :
    ∫ p, f₁ p.1 * (f₂ p.2.1 * (f₃ p.2.2.1 * f₄ p.2.2.2)) ∂(plProd μ) =
      (∫ x, f₁ x ∂μ) * ((∫ x, f₂ x ∂μ) * ((∫ x, f₃ x ∂μ) * ∫ x, f₄ x ∂μ)) := by
  rw [plProd, integral_prod_mul f₁ (fun q : K × K × K => f₂ q.1 * (f₃ q.2.1 * f₄ q.2.2)),
    integral_prod_mul f₂ (fun q : K × K => f₃ q.1 * f₄ q.2), integral_prod_mul f₃ f₄]

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]
  [μ.IsAddHaarMeasure] in
/-- A product of four integrable functions of the four coordinates is integrable. -/
theorem pl_integrable_prod4 {f₁ f₂ f₃ f₄ : K → ℂ} (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) :
    Integrable (fun p : K × K × K × K => f₁ p.1 * (f₂ p.2.1 * (f₃ p.2.2.1 * f₄ p.2.2.2)))
      (plProd μ) :=
  h₁.mul_prod (h₂.mul_prod (h₃.mul_prod h₄))

/-- A ball indicator is integrable. -/
theorem pl_integrable_ballIndicator (b : K) (N : ℤ) : Integrable (ballIndicator b N) μ := by
  have := (isBallBounded_of_isLocallyConstant μ (isLocallyConstant_ballIndicator b N)
    (hasCompactSupport_ballIndicator b N)).integrable_mul μ (g := fun _ => (1 : ℂ))
      (fun M => integrable_indicator_of_continuous μ continuous_const M)
  simpa using this

/-- A ball indicator times $\chi(y) |y|^{s - 1}$ is integrable if $|\chi(\varpi) q^{1 - s}| \le 1$. -/
theorem pl_integrable_ballIndicator_zetaFn (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖zetaRatio χ s‖ ≤ 1) (b : K) (N : ℤ) :
    Integrable (fun y => ballIndicator b N y * zetaFn χ s y) μ :=
  (isBallBounded_of_isLocallyConstant μ (isLocallyConstant_ballIndicator b N)
    (hasCompactSupport_ballIndicator b N)).integrable_mul μ fun M =>
      integrable_indicator_zetaFn χ μ hχ hs (isClosed_ordBall M).measurableSet subset_rfl

/-- **The integral after the substitution.** For a locally constant $G$ with compact support on $K^4$ there are $N$ and a finite set $T$ such that $\int G(a, b, t, d) \chi(a) |a|^s \chi(d) |d|^{s - 1}$ is a finite sum of products of one-variable zeta integrals of ball indicators and volumes of balls. -/
theorem pl_rhs (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {G : K × K × K × K → ℂ}
    (hG : IsLocallyConstant G) (hGs : HasCompactSupport G) :
    ∃ (N : ℤ) (T : Finset K), ∀ s : ℂ, ‖zetaRatio χ s‖ ≤ 1 → ‖zetaRatio (χ * absChar K) s‖ ≤ 1 →
      Integrable (fun p => G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2) (plProd μ) ∧
      ∫ p, G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2 ∂(plProd μ) =
        ∑ r ∈ T ×ˢ T ×ˢ T ×ˢ T, G r * (zeta (χ * absChar K) μ (ballIndicator r.1 N) s *
          ((∫ x, ballIndicator r.2.1 N x ∂μ) * ((∫ x, ballIndicator r.2.2.1 N x ∂μ) *
            zeta χ μ (ballIndicator r.2.2.2 N) s))) := by
  obtain ⟨N, T, hdec⟩ := pl_exists_eq_sum hG hGs
  refine ⟨N, T, fun s hs hs' => ?_⟩
  have hχ' : IsSmoothChar K (χ * absChar K) := hχ.mul isSmoothChar_absChar
  have hpt : (fun p => G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2) =
      fun p => ∑ r ∈ T ×ˢ T ×ˢ T ×ˢ T, G r *
        ((ballIndicator r.1 N p.1 * zetaFn (χ * absChar K) s p.1) *
          (ballIndicator r.2.1 N p.2.1 * (ballIndicator r.2.2.1 N p.2.2.1 *
            (ballIndicator r.2.2.2 N p.2.2.2 * zetaFn χ s p.2.2.2)))) := by
    funext p
    rw [hdec p, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hint : ∀ r : K × K × K × K, Integrable (fun p : K × K × K × K =>
      (ballIndicator r.1 N p.1 * zetaFn (χ * absChar K) s p.1) *
        (ballIndicator r.2.1 N p.2.1 * (ballIndicator r.2.2.1 N p.2.2.1 *
          (ballIndicator r.2.2.2 N p.2.2.2 * zetaFn χ s p.2.2.2)))) (plProd μ) := fun r =>
    pl_integrable_prod4 μ (f₁ := fun x => ballIndicator r.1 N x * zetaFn (χ * absChar K) s x)
      (f₂ := ballIndicator r.2.1 N) (f₃ := ballIndicator r.2.2.1 N)
      (f₄ := fun x => ballIndicator r.2.2.2 N x * zetaFn χ s x)
      (pl_integrable_ballIndicator_zetaFn μ _ hχ' hs' r.1 N)
      (pl_integrable_ballIndicator μ r.2.1 N) (pl_integrable_ballIndicator μ r.2.2.1 N)
      (pl_integrable_ballIndicator_zetaFn μ χ hχ hs r.2.2.2 N)
  rw [hpt]
  refine ⟨integrable_finsetSum _ fun r _ => (hint r).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun r _ => (hint r).const_mul _]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, pl_integral_prod4 μ (fun x => ballIndicator r.1 N x *
    zetaFn (χ * absChar K) s x) (ballIndicator r.2.1 N) (ballIndicator r.2.2.1 N)
    (fun x => ballIndicator r.2.2.2 N x * zetaFn χ s x)]
  rfl

end Product

section RegionIntegral

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A function on $K^4$ with compact support is zero outside a box $(\varpi^M \mathcal{O}_K)^4$ with $M \le 0$. -/
theorem pl_exists_zero_outside {F : K × K × K × K → ℂ} (hFs : HasCompactSupport F) :
    ∃ M : ℤ, M ≤ 0 ∧ ∀ p ∉ plBox M, F p = 0 := by
  obtain ⟨M, hM⟩ := pl_exists_box_superset hFs
  refine ⟨min M 0, min_le_right _ _, fun p hp => image_eq_zero_of_notMem_tsupport fun h =>
    hp (pl_box_anti (min_le_left _ _) (hM h))⟩

/-- The function `plSub m F` is locally constant. -/
theorem pl_isLocallyConstant_sub (m : ℤ) {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F) :
    IsLocallyConstant (plSub m F) := by
  have h1 : IsLocallyConstant fun p : K × K × K × K => (ordBall K m).indicator 1 p.2.2.1 :=
    (isLocallyConstant_indicator (isOpen_ordBall m) (isClosed_ordBall m)
      (fun _ _ => Eventually.of_forall fun _ => rfl)).comp_continuous continuous_snd.snd.fst
  have h2 : IsLocallyConstant fun p : K × K × K × K =>
      F (p.1, p.2.1, p.1 * p.2.2.1, p.2.2.2 + p.2.2.1 * p.2.1) :=
    hF.comp_continuous (continuous_fst.prodMk (continuous_snd.fst.prodMk
      ((continuous_fst.mul continuous_snd.snd.fst).prodMk
        (continuous_snd.snd.snd.add (continuous_snd.snd.fst.mul continuous_snd.fst)))))
  exact h1.mul h2

/-- For $m \ge 0$, the function `plSub m F` is zero outside each box outside which $F$ is zero, if the box has $M \le 0$. -/
theorem pl_sub_eq_zero {m M : ℤ} (hm : 0 ≤ m) (hM : M ≤ 0) {F : K × K × K × K → ℂ}
    (hF0 : ∀ p ∉ plBox M, F p = 0) : ∀ p ∉ plBox M, plSub m F p = 0 := by
  intro p hp
  unfold plSub
  by_cases ht : p.2.2.1 ∈ ordBall K m
  · rw [hF0, mul_zero]
    intro h
    rw [pl_mem_box] at h
    simp only at h
    refine hp (pl_mem_box.2 ⟨h.1, h.2.1, ordBall_anti (by omega) ht, ?_⟩)
    have h3 : p.2.2.1 * p.2.1 ∈ ordBall K M := by
      have := mul_mem_ordBall_add ht h.2.1
      exact ordBall_anti (by omega) this
    simpa using add_mem_ordBall h.2.2.2 (neg_mem_ordBall h3)
  · rw [Set.indicator_of_notMem ht, zero_mul]

/-- For $m \ge 0$, the function `plSub m F` has compact support. -/
theorem pl_hasCompactSupport_sub {m : ℤ} (hm : 0 ≤ m) {F : K × K × K × K → ℂ}
    (hFs : HasCompactSupport F) : HasCompactSupport (plSub m F) := by
  obtain ⟨M, hM, hF0⟩ := pl_exists_zero_outside hFs
  exact HasCompactSupport.intro (pl_isCompact_box M) (pl_sub_eq_zero hm hM hF0)

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

omit [μ.Regular] in
/-- The region `plRegion m` is measurable. -/
theorem pl_measurableSet_region (m : ℤ) : MeasurableSet (plRegion (K := K) m) :=
  (measurable_fst (measurableSet_singleton (0 : K)).compl).inter
    ((isClosed_ordBall m).measurableSet.preimage (measurable_snd.snd.fst.mul measurable_fst.inv))

omit [μ.Regular] in
/-- The function $\mathbf{1}_S F \chi(\det) |\det|^{s - 1}$ is integrable on $K^4$ for each measurable set $S$ and each locally constant $F$ with compact support. -/
theorem pl_integrable_indicator (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖zetaRatio χ s‖ ≤ 1) {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F)
    (hFs : HasCompactSupport F) {S : Set (K × K × K × K)} (hS : MeasurableSet S) :
    Integrable (fun p => S.indicator (fun p => F p * zetaFn χ s (plDet p)) p) (plProd μ) := by
  obtain ⟨M, -, hF0⟩ := pl_exists_zero_outside hFs
  obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hFs
  simp_rw [Set.indicator_mul_left]
  refine pl_integrable_mul_zetaFn_det μ χ hχ hs (hF.continuous.measurable.indicator hS) (C := C)
    (fun p => (norm_indicator_le_norm_self _ _).trans (hC p)) (M := M) (fun p hp => ?_)
  by_cases h : p ∈ S
  · rw [Set.indicator_of_mem h, hF0 p hp]
  · rw [Set.indicator_of_notMem h]

/-- **The region integral.** For $m \ge 0$ and $\mathrm{Re}(s)$ large, the integral of $F \chi(\det) |\det|^{s - 1}$ over the region `plRegion m` is the integral of `plSub m F` against $\chi(a) |a|^s \chi(d) |d|^{s - 1}$. -/
theorem pl_region_eq (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1)
    {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F) (hFs : HasCompactSupport F) (m : ℤ)
    (hR : Integrable (fun p => plSub m F p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2)
      (plProd μ)) :
    ∫ p, (plRegion m).indicator (fun p => F p * zetaFn χ s (plDet p)) p ∂(plProd μ) =
      ∫ p, plSub m F p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2 ∂(plProd μ) := by
  rw [pl_integral_four μ (pl_integrable_indicator μ χ hχ hs hF hFs (pl_measurableSet_region m)),
    pl_integral_four μ hR]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  exact pl_region_iter μ χ m F s a b

end RegionIntegral

section Swap

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The value of $\chi$ at $-1$, as a complex number. -/
noncomputable def plSign (χ : Kˣ →* ℂˣ) : ℂ :=
  (χ (-1) : ℂ)

/-- The function $\chi(y) |y|^{s - 1}$ satisfies $f(-y) = \chi(-1) f(y)$. -/
theorem pl_zetaFn_neg (χ : Kˣ →* ℂˣ) (s : ℂ) (y : K) :
    zetaFn χ s (-y) = plSign χ * zetaFn χ s y := by
  have h1 : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have h2 : ord K (-1 : K) = 0 := by
    have := ord_mul h1 h1
    rw [neg_one_mul, neg_neg, ord_one] at this
    omega
  have h3 : Units.mk0 (-1 : K) h1 = -1 := Units.ext (by simp)
  rw [show -y = (-1 : K) * y by ring, zetaFn_mul χ h1, h2, zpow_zero, mul_one, h3, plSign]

variable [MeasurableSpace K] [BorelSpace K]

/-- The exchange $(a, b, c, d) \mapsto (c, d, a, b)$ of the two rows, as a measurable equivalence of $K^4$. -/
def plSwap : (K × K × K × K) ≃ᵐ (K × K × K × K) :=
  (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm).trans MeasurableEquiv.prodAssoc

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K] in
/-- The formula for the exchange of the rows. -/
theorem pl_swap_apply (p : K × K × K × K) : plSwap p = (p.2.2.1, p.2.2.2, p.1, p.2.1) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K] in
/-- The exchange of the rows changes the sign of the determinant. -/
theorem pl_det_swap (p : K × K × K × K) : plDet (plSwap p) = -plDet p := by
  rw [pl_swap_apply, plDet, plDet]
  ring

omit [BorelSpace K] in
/-- **The two regions.** Each point of $K^4$ with $(a, c) \ne (0, 0)$ is in exactly one of the region `plRegion 0` and the image of `plRegion 1` under the exchange of the rows. -/
theorem pl_split_pt (χ : Kˣ →* ℂˣ) (s : ℂ) (F : K × K × K × K → ℂ) (p : K × K × K × K) :
    F p * zetaFn χ s (plDet p) = (plRegion 0).indicator (fun p => F p * zetaFn χ s (plDet p)) p +
      (plSwap ⁻¹' plRegion 1).indicator (fun p => F p * zetaFn χ s (plDet p)) p := by
  obtain ⟨a, b, c, d⟩ := p
  by_cases ha : a = 0
  · have h0 : (a, b, c, d) ∉ plRegion (K := K) 0 := fun h => h.1 ha
    rw [Set.indicator_of_notMem h0, zero_add]
    by_cases hc : c = 0
    · have h1 : (a, b, c, d) ∉ plSwap ⁻¹' plRegion (K := K) 1 := fun h => h.1 hc
      rw [Set.indicator_of_notMem h1, plDet, ha, hc]
      simp [zetaFn_zero]
    · have h1 : (a, b, c, d) ∈ plSwap ⁻¹' plRegion (K := K) 1 :=
        ⟨hc, by simpa [pl_swap_apply, ha] using zero_mem_ordBall (K := K) 1⟩
      rw [Set.indicator_of_mem h1]
  by_cases hc : c = 0
  · have h0 : (a, b, c, d) ∈ plRegion (K := K) 0 :=
      ⟨ha, by simpa [hc] using zero_mem_ordBall (K := K) 0⟩
    have h1 : (a, b, c, d) ∉ plSwap ⁻¹' plRegion (K := K) 1 := fun h => h.1 hc
    rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
  have hx : c * a⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hx' : a * c⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hc)
  have ho : ord K (a * c⁻¹) = -ord K (c * a⁻¹) := by
    rw [ord_mul ha (inv_ne_zero hc), ord_mul hc (inv_ne_zero ha), ord_inv ha, ord_inv hc]
    ring
  by_cases h : 0 ≤ ord K (c * a⁻¹)
  · have h0 : (a, b, c, d) ∈ plRegion (K := K) 0 := ⟨ha, (mem_ordBall_of_ne_zero hx).2 h⟩
    have h1 : (a, b, c, d) ∉ plSwap ⁻¹' plRegion (K := K) 1 := by
      intro h1
      have := (mem_ordBall_of_ne_zero hx').1 h1.2
      omega
    rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
  · have h0 : (a, b, c, d) ∉ plRegion (K := K) 0 := fun h0 =>
      h ((mem_ordBall_of_ne_zero hx).1 h0.2)
    have h1 : (a, b, c, d) ∈ plSwap ⁻¹' plRegion (K := K) 1 :=
      ⟨hc, (mem_ordBall_of_ne_zero hx').2 (by omega)⟩
    rw [Set.indicator_of_notMem h0, Set.indicator_of_mem h1, zero_add]

omit [Field K] [ValuativeRel K] [IsNonarchimedeanLocalField K] [BorelSpace K] in
/-- The exchange of the rows is continuous. -/
theorem pl_continuous_swap : Continuous (plSwap (K := K)) := by
  change Continuous fun p : K × K × K × K => (p.2.2.1, p.2.2.2, p.1, p.2.1)
  fun_prop

omit [BorelSpace K] in
/-- The exchange of the rows keeps each box. -/
theorem pl_swap_mem_box {N : ℤ} {p : K × K × K × K} : plSwap p ∈ plBox N ↔ p ∈ plBox N := by
  rw [pl_mem_box, pl_mem_box, pl_swap_apply]
  tauto

omit [BorelSpace K] in
/-- If $F$ has compact support, then $F$ with the rows exchanged has compact support. -/
theorem pl_hasCompactSupport_swap {F : K × K × K × K → ℂ} (hFs : HasCompactSupport F) :
    HasCompactSupport fun p => F (plSwap p) := by
  obtain ⟨M, -, hF0⟩ := pl_exists_zero_outside hFs
  exact HasCompactSupport.intro (pl_isCompact_box M) fun p hp =>
    hF0 _ fun h => hp (pl_swap_mem_box.1 h)

variable (μ : Measure K) [μ.IsAddHaarMeasure]

omit [BorelSpace K] in
/-- The exchange of the rows preserves the measure $\mu^{\otimes 4}$. -/
theorem pl_measurePreserving_swap : MeasurePreserving plSwap (plProd μ) (plProd μ) :=
  (measurePreserving_prodAssoc μ μ (μ.prod μ)).comp (Measure.measurePreserving_swap.comp
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc μ μ (μ.prod μ))))

/-- **The split of the integral.** For $\mathrm{Re}(s)$ large, $\int F \chi(\det) |\det|^{s - 1}$ is the integral over `plRegion 0` plus $\chi(-1)$ times the integral of $F$ with the rows exchanged over `plRegion 1`. -/
theorem pl_split (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1)
    {F : K × K × K × K → ℂ} (hF : IsLocallyConstant F) (hFs : HasCompactSupport F) :
    ∫ p, F p * zetaFn χ s (plDet p) ∂(plProd μ) =
      ∫ p, (plRegion 0).indicator (fun p => F p * zetaFn χ s (plDet p)) p ∂(plProd μ) +
        plSign χ * ∫ p, (plRegion 1).indicator (fun p => F (plSwap p) * zetaFn χ s (plDet p)) p
          ∂(plProd μ) := by
  rw [integral_congr_ae (μ := plProd μ) (Eventually.of_forall (pl_split_pt χ s F))]
  have hS : MeasurableSet (plSwap ⁻¹' plRegion (K := K) 1) :=
    plSwap.measurable (pl_measurableSet_region 1)
  rw [integral_add (pl_integrable_indicator μ χ hχ hs hF hFs (pl_measurableSet_region 0))
    (pl_integrable_indicator μ χ hχ hs hF hFs hS)]
  congr 1
  rw [← (pl_measurePreserving_swap μ).integral_comp' (fun p =>
    (plSwap ⁻¹' plRegion 1).indicator (fun p => F p * zetaFn χ s (plDet p)) p), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  have hq : plSwap (plSwap q) = q := rfl
  by_cases h : q ∈ plRegion (K := K) 1
  · have h' : plSwap q ∈ plSwap ⁻¹' plRegion (K := K) 1 := by rw [Set.mem_preimage, hq]; exact h
    beta_reduce
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h, pl_det_swap, pl_zetaFn_neg]
    ring
  · have h' : plSwap q ∉ plSwap ⁻¹' plRegion (K := K) 1 := by rw [Set.mem_preimage, hq]; exact h
    beta_reduce
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h, mul_zero]

end Swap

section Good

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The function $f$ is $A(X) X^{-k} L(s)$ for $\mathrm{Re}(s)$ large, where $X = q^{-s}$ and $A$ is a polynomial. This is the form of clause 2 of `Langlands.IsGJLFactor`. -/
def PlGood (L f : ℂ → ℂ) : Prop :=
  ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
    f s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k * L s

/-- The number $q^{-s}$ is not zero. -/
theorem pl_cpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 :=
  Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne'))

/-- A function that is equal to a good function for $\mathrm{Re}(s)$ large is good. -/
theorem pl_good_of_eq {L f g : ℂ → ℂ} (hf : PlGood K L f) (s₁ : ℝ)
    (h : ∀ s : ℂ, s₁ < s.re → g s = f s) : PlGood K L g := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  exact ⟨A, k, max s₀ s₁, fun s hs => by
    rw [h s (lt_of_le_of_lt (le_max_right _ _) hs), hA s (lt_of_le_of_lt (le_max_left _ _) hs)]⟩

/-- A good function stays good if $L$ is replaced by an equal function. -/
theorem pl_good_congr {L L' f : ℂ → ℂ} (hf : PlGood K L f) (h : ∀ s, L s = L' s) :
    PlGood K L' f := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  exact ⟨A, k, s₀, fun s hs => by rw [hA s hs, h]⟩

/-- The zero function is good. -/
theorem pl_good_zero (L : ℂ → ℂ) : PlGood K L fun _ => 0 :=
  ⟨0, 0, 0, fun s _ => by simp⟩

/-- A sum of two good functions is good. -/
theorem pl_good_add {L f g : ℂ → ℂ} (hf : PlGood K L f) (hg : PlGood K L g) :
    PlGood K L fun s => f s + g s := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  obtain ⟨B, m, s₁, hB⟩ := hg
  refine ⟨A * Polynomial.X ^ m + B * Polynomial.X ^ k, k + m, max s₀ s₁, fun s hs => ?_⟩
  beta_reduce
  rw [hA s (lt_of_le_of_lt (le_max_left _ _) hs), hB s (lt_of_le_of_lt (le_max_right _ _) hs)]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have hX := pl_cpow_ne_zero (K := K) s
  generalize (residueCard K : ℂ) ^ (-s) = X at hX ⊢
  field_simp
  ring

/-- A constant times a good function is good. -/
theorem pl_good_const_mul {L f : ℂ → ℂ} (c : ℂ) (hf : PlGood K L f) :
    PlGood K L fun s => c * f s := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  refine ⟨Polynomial.C c * A, k, s₀, fun s hs => ?_⟩
  beta_reduce
  rw [hA s hs, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- A finite sum of good functions is good. -/
theorem pl_good_sum {ι : Type*} (T : Finset ι) {L : ℂ → ℂ} {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ T, PlGood K L (f i)) : PlGood K L fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using pl_good_zero (K := K) L
  | insert a T ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact pl_good_add (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A product of a function good for $L_1$ and a function good for $L_2$ is good for $L_1 L_2$. -/
theorem pl_good_mul {L₁ L₂ f g : ℂ → ℂ} (hf : PlGood K L₁ f) (hg : PlGood K L₂ g) :
    PlGood K (fun s => L₁ s * L₂ s) fun s => f s * g s := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  obtain ⟨B, m, s₁, hB⟩ := hg
  refine ⟨A * B, k + m, max s₀ s₁, fun s hs => ?_⟩
  beta_reduce
  rw [hA s (lt_of_le_of_lt (le_max_left _ _) hs), hB s (lt_of_le_of_lt (le_max_right _ _) hs),
    Polynomial.eval_mul, pow_add]
  ring

/-- If $L = 1$, then a good function is a Laurent polynomial in $X = q^{-s}$ for $\mathrm{Re}(s)$ large. -/
theorem pl_good_one {L f : ℂ → ℂ} (hf : PlGood K L f) (hL : ∀ s, L s = 1) :
    ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
      f s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k := by
  obtain ⟨A, k, s₀, hA⟩ := hf
  exact ⟨A, k, s₀, fun s hs => by rw [hA s hs, hL, mul_one]⟩

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/-- **Tate's computation in the good form.** For a locally constant $\varphi$ with compact support on $K$, the zeta integral $Z(\varphi, \chi, s)$ is good for $L(s, \chi)$. -/
theorem pl_good_zeta (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {φ : K → ℂ}
    (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    PlGood K (charLFactor K (unif K) χ) (zeta χ μ φ) := by
  classical
  obtain ⟨A, M, N, hA⟩ := exists_zeta_eq χ μ hχ hφ hφs
  by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
  · refine ⟨A * (1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X) +
      Polynomial.C (φ 0 * (μ.real (ordShell K 0) : ℂ) * (χ (unif K) : ℂ) ^ N) *
        Polynomial.X ^ (N + M), M, zetaBound χ, fun s hs => ?_⟩
    have hs' := norm_zetaRatio_le χ hs
    have h0 := ballZeta_one_zero χ μ hχ hs'
    rw [shellCoeff_one_of_unramified χ μ hunr] at h0
    have h1 := one_sub_ne_zero χ hs'
    have hT : ballZeta χ μ (fun _ => 1) s 0 =
        (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
      rw [← h0, mul_div_cancel_right₀ _ h1]
    rw [hA s hs', hT, charLFactor, ite_eq_left hunr]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
    have hXs := pl_cpow_ne_zero (K := K) s
    generalize (residueCard K : ℂ) ^ (-s) = X at hXs h1 ⊢
    generalize (χ (unif K) : ℂ) = c at h1 ⊢
    have h1' : 1 - X * c ≠ 0 := by rwa [mul_comm]
    field_simp
    ring
  · simp only [not_forall] at hunr
    obtain ⟨u, hu, hχu⟩ := hunr
    refine ⟨A, M, zetaBound χ, fun s hs => ?_⟩
    have hs' := norm_zetaRatio_le χ hs
    have h0 := ballZeta_one_zero χ μ hχ hs'
    rw [shellCoeff_one_of_ramified χ μ hu hχu] at h0
    have hT : ballZeta χ μ (fun _ => 1) s 0 = 0 :=
      (mul_eq_zero.1 h0).resolve_right (one_sub_ne_zero χ hs')
    have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
    rw [hA s hs', hT, charLFactor, ite_eq_right hn]
    ring

/-- The bound $\max(s_0(\chi), s_0(\chi |\cdot|))$ for the two zeta integrals on $K^4$. -/
noncomputable def plBound (χ : Kˣ →* ℂˣ) : ℝ :=
  max (zetaBound χ) (zetaBound (χ * absChar K))

omit [MeasurableSpace K] [BorelSpace K] in
/-- For $\mathrm{Re}(s) > $ `plBound χ`, both numbers $|\chi(\varpi) q^{1 - s}|$ and $|\chi|\cdot|(\varpi) q^{1 - s}|$ are at most $1$. -/
theorem pl_norm_le_of_bound (χ : Kˣ →* ℂˣ) {s : ℂ} (hs : plBound χ < s.re) :
    ‖zetaRatio χ s‖ ≤ 1 ∧ ‖zetaRatio (χ * absChar K) s‖ ≤ 1 :=
  ⟨norm_zetaRatio_le χ (lt_of_le_of_lt (le_max_left _ _) hs),
    norm_zetaRatio_le _ (lt_of_le_of_lt (le_max_right _ _) hs)⟩

/-- For a locally constant $G$ with compact support on $K^4$, the integral of $G(a, b, c, d) \chi|\cdot|(a) |a|^{s - 1} \chi(d) |d|^{s - 1}$ is good for $L(s, \chi) L(s, \chi |\cdot|)$. -/
theorem pl_good_rhs (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {G : K × K × K × K → ℂ}
    (hG : IsLocallyConstant G) (hGs : HasCompactSupport G) :
    PlGood K (fun s => charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s)
      fun s => ∫ p, G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2 ∂(plProd μ) := by
  obtain ⟨N, T, h⟩ := pl_rhs μ χ hχ hG hGs
  have hχ' : IsSmoothChar K (χ * absChar K) := hχ.mul isSmoothChar_absChar
  have hb : ∀ b : K, IsLocallyConstant (ballIndicator b N) ∧ HasCompactSupport (ballIndicator b N) :=
    fun b => ⟨isLocallyConstant_ballIndicator b N, hasCompactSupport_ballIndicator b N⟩
  refine pl_good_of_eq (pl_good_congr (pl_good_sum (T ×ˢ T ×ˢ T ×ˢ T) fun r _ =>
    pl_good_const_mul (G r) (pl_good_mul (pl_good_zeta μ _ hχ' (hb r.1).1 (hb r.1).2)
      (pl_good_const_mul (∫ x, ballIndicator r.2.1 N x ∂μ)
        (pl_good_const_mul (∫ x, ballIndicator r.2.2.1 N x ∂μ) (pl_good_zeta μ χ hχ (hb r.2.2.2).1
        (hb r.2.2.2).2))))) (fun s => mul_comm _ _)) (plBound χ) fun s hs => ?_
  obtain ⟨h1, h2⟩ := pl_norm_le_of_bound χ hs
  exact (h s h1 h2).2

end Good

section Det

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/-- **The zeta integral on $K^4$.** For a locally constant $F$ with compact support on $K^4$, the integral $\int F(x) \chi(\det x) |\det x|^{s - 1} \, dx$ is good for $L(s, \chi) L(s, \chi |\cdot|)$. -/
theorem pl_good_det (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {F : K × K × K × K → ℂ}
    (hF : IsLocallyConstant F) (hFs : HasCompactSupport F) :
    PlGood K (fun s => charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s)
      fun s => ∫ p, F p * zetaFn χ s (plDet p) ∂(plProd μ) := by
  have hFσ : IsLocallyConstant fun p => F (plSwap p) := hF.comp_continuous pl_continuous_swap
  have hFσs := pl_hasCompactSupport_swap hFs
  have hG0 := pl_isLocallyConstant_sub 0 hF
  have hG0s := pl_hasCompactSupport_sub le_rfl hFs
  have hG1 := pl_isLocallyConstant_sub 1 hFσ
  have hG1s := pl_hasCompactSupport_sub zero_le_one hFσs
  obtain ⟨N0, T0, h0⟩ := pl_rhs μ χ hχ hG0 hG0s
  obtain ⟨N1, T1, h1⟩ := pl_rhs μ χ hχ hG1 hG1s
  refine pl_good_of_eq (pl_good_add (pl_good_rhs μ χ hχ hG0 hG0s)
    (pl_good_const_mul (plSign χ) (pl_good_rhs μ χ hχ hG1 hG1s))) (plBound χ) fun s hs => ?_
  obtain ⟨hs1, hs2⟩ := pl_norm_le_of_bound χ hs
  rw [pl_split μ χ hχ hs1 hF hFs, pl_region_eq μ χ hχ hs1 hF hFs 0 (h0 s hs1 hs2).1,
    pl_region_eq μ χ hχ hs1 hFσ hFσs 1 (h1 s hs1 hs2).1]

end Det

section Matrix

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The homeomorphism $M_2(K) \to K^4$ that sends a matrix to its four entries $(x_{00}, x_{01}, x_{10}, x_{11})$. -/
def plEntries : Matrix (Fin 2) (Fin 2) K ≃ₜ K × K × K × K where
  toFun x := (x 0 0, x 0 1, x 1 0, x 1 1)
  invFun p := Matrix.of ![![p.1, p.2.1], ![p.2.2.1, p.2.2.2]]
  left_inv x := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    change Continuous fun p : K × K × K × K => fun i j => ![![p.1, p.2.1], ![p.2.2.1, p.2.2.2]] i j
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

variable (K) in
/-- The map `plEntries` as an additive isomorphism. -/
def plEntriesAdd : Matrix (Fin 2) (Fin 2) K ≃+ K × K × K × K :=
  { (plEntries K).toEquiv with map_add' := fun _ _ => rfl }

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The determinant of a matrix is `plDet` of its entries. -/
theorem pl_det_symm (p : K × K × K × K) : ((plEntries K).symm p).det = plDet p := by
  rw [Matrix.det_fin_two]
  rfl

/-- The representation $\chi |\cdot|^{1/2} \circ \det$ of $GL_2(K)$ on $\mathbb{C}$. -/
noncomputable abbrev plRep (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) : SmoothRep (GL (Fin 2) K) :=
  SmoothRep.charRep (detChar K 2 (χ * sqrtAbsChar K)) (isOpen_ker_detChar K 2 _ (hχ.mul isSmoothChar_sqrtAbsChar))

/-- The group element $g$ acts on the space of `plRep χ hχ` by the scalar $\chi(\det g) |\det g|^{1/2}$. -/
theorem pl_rep_apply (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (g : GL (Fin 2) K) (v : (plRep χ hχ).V) :
    (plRep χ hχ).ρ g v = (detChar K 2 (χ * sqrtAbsChar K) g : ℂ) • v :=
  rfl

/-- For $r > 0$, the equation $r^{1/2} r^{s + 1/2 - 2} = r^{s - 1}$ holds. -/
theorem pl_sqrt_mul_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((Real.sqrt r : ℝ) : ℂ) * (r : ℂ) ^ (s + (((2 : ℕ) : ℂ) - 1) / 2 - ((2 : ℕ) : ℂ)) =
      (r : ℂ) ^ (s - 1) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hr.ne')]
  congr 1
  push_cast
  ring

/-- **The zeta integral of $\chi |\cdot|^{1/2} \circ \det$.** The Godement-Jacquet zeta integral of the representation `plRep χ hχ` is $\lambda(v) \int_{M_2(K)} \Phi(x) \chi(\det x) |\det x|^{s - 1} \, dx$. -/
theorem pl_gjZeta_eq (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (Φ : Matrix (Fin 2) (Fin 2) K → ℂ)
    (v : (plRep χ hχ).V) (l : Module.Dual ℂ (plRep χ hχ).V) (s : ℂ) :
    gjZeta K (plRep χ hχ) Φ v l s = l v * (letI := matrixBorel K 2
      ∫ x, Φ x * zetaFn χ s x.det ∂(matrixHaar K 2)) := by
  unfold gjZeta
  rw [← integral_const_mul]
  congr 1
  funext x
  split_ifs with h
  · have h0 : x.det ≠ 0 := h.ne_zero
    have hd : Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) = Units.mk0 x.det h0 := by
      ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mk0]
      rfl
    have hr : 0 < normAbs K x.det := normAbs_pos h0
    rw [SmoothRep.coeff, pl_rep_apply, map_smul, smul_eq_mul, zetaFn, extChar_of_ne_zero χ h0,
      detChar, MonoidHom.comp_apply, hd, MonoidHom.mul_apply, Units.val_mul]
    have hs : ((sqrtAbsChar K (Units.mk0 x.det h0) : ℂˣ) : ℂ) = ((Real.sqrt (normAbs K x.det) : ℝ) : ℂ) :=
      rfl
    rw [hs, ← pl_sqrt_mul_cpow hr s]
    ring
  · have h0 : x.det = 0 := by
      by_contra h0
      exact h (Ne.isUnit h0)
    rw [h0, zetaFn_zero, mul_zero, mul_zero]

variable [MeasurableSpace K] [BorelSpace K]

/-- **The Haar measure of $M_2(K)$ on $K^4$.** There is $c > 0$ with $\int_{M_2(K)} f \, dx = c \int_{K^4} f \circ e^{-1} \, d\mu^{\otimes 4}$, where $e$ is `plEntries`. -/
theorem pl_exists_scalar (μ : Measure K) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin 2) (Fin 2) K → ℂ,
      (letI := matrixBorel K 2; ∫ x, f x ∂(matrixHaar K 2)) =
        (c : ℂ) * ∫ p, f ((plEntries K).symm p) ∂(plProd μ) := by
  let := matrixBorel K 2
  have : BorelSpace (Matrix (Fin 2) (Fin 2) K) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → K))
  have : (matrixHaar K 2).IsAddHaarMeasure := by
    unfold matrixHaar
    infer_instance
  set ν := Measure.map (plEntries K) (matrixHaar K 2)
  have : ν.IsAddHaarMeasure := (plEntriesAdd K).isAddHaarMeasure_map (matrixHaar K 2)
    (plEntries K).continuous (plEntries K).symm.continuous
  have hν := Measure.isAddLeftInvariant_eq_smul ν (plProd μ)
  refine ⟨(ν.addHaarScalarFactor (plProd μ) : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun f => ?_⟩
  have h1 : ∫ x, f x ∂(matrixHaar K 2) = ∫ p, f ((plEntries K).symm p) ∂ν := by
    rw [(plEntries K).measurableEmbedding.integral_map]
    simp
  have h2 := congrArg (fun m : Measure (K × K × K × K) => ∫ p, f ((plEntries K).symm p) ∂m) hν
  rw [h1, h2, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Matrix

section Unramified

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The character $\chi |\cdot|$ is unramified exactly when $\chi$ is unramified. -/
theorem pl_unr_abs_iff (χ : Kˣ →* ℂˣ) :
    (∀ x : Kˣ, normAbs K x = 1 → (χ * absChar K) x = 1) ↔ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := by
  have h : ∀ x : Kˣ, normAbs K x = 1 → (χ * absChar K) x = χ x := fun x hx => by
    rw [MonoidHom.mul_apply]
    refine (mul_eq_left).2 (Units.ext ?_)
    rw [absChar_apply, hx, Complex.ofReal_one, Units.val_one]
  exact forall_congr' fun x => imp_congr_right fun hx => by rw [h x hx]

/-- The order of $-1$ is $0$. -/
theorem pl_ord_neg_one : ord K (-1 : K) = 0 := by
  have h1 : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have := ord_mul h1 h1
  rw [neg_one_mul, neg_neg, ord_one] at this
  omega

/-- For an unramified character, $\chi(-1) = 1$. -/
theorem pl_sign_unr {χ : Kˣ →* ℂˣ} (hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) :
    plSign χ = 1 := by
  have h1 : ((-1 : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have h : normAbs K ((-1 : Kˣ) : K) = 1 :=
    (normAbs_eq_one_iff h1).2 (by rw [Units.val_neg, Units.val_one]; exact pl_ord_neg_one)
  rw [plSign, hunr _ h, Units.val_one]

/-- The indicator of the box $\mathcal{O}_K^4$ is locally constant. -/
theorem pl_isLocallyConstant_box :
    IsLocallyConstant ((plBox (K := K) 0).indicator (1 : K × K × K × K → ℂ)) :=
  isLocallyConstant_indicator (pl_isOpen_box 0) (pl_isCompact_box 0).isClosed
    fun _ _ => Eventually.of_forall fun _ => rfl

/-- The indicator of the box $\mathcal{O}_K^4$ has compact support. -/
theorem pl_hasCompactSupport_box :
    HasCompactSupport ((plBox (K := K) 0).indicator (1 : K × K × K × K → ℂ)) :=
  HasCompactSupport.intro (pl_isCompact_box 0) fun _ hp => Set.indicator_of_notMem hp _

/-- For $m \ge 0$ and $F = \mathbf{1}_{\mathcal{O}_K^4}$, the function `plSub m F` is the indicator of $\mathcal{O}_K \times \mathcal{O}_K \times \varpi^m \mathcal{O}_K \times \mathcal{O}_K$. -/
theorem pl_sub_box {m : ℤ} (hm : 0 ≤ m) {G : K × K × K × K → ℂ}
    (hG : ∀ p, G p = (plBox 0).indicator 1 p) (p : K × K × K × K) :
    plSub m G p = (ordBall K 0).indicator (fun _ => 1) p.1 * ((ordBall K 0).indicator (fun _ => 1)
      p.2.1 * ((ordBall K m).indicator (fun _ => 1) p.2.2.1 *
        (ordBall K 0).indicator (fun _ => 1) p.2.2.2)) := by
  classical
  obtain ⟨a, b, c, d⟩ := p
  rw [plSub, hG]
  by_cases hc : c ∈ ordBall K m
  · have hc0 : c ∈ ordBall K 0 := ordBall_anti hm hc
    have key : (a, b, a * c, d + c * b) ∈ plBox (K := K) 0 ↔
        a ∈ ordBall K 0 ∧ b ∈ ordBall K 0 ∧ d ∈ ordBall K 0 := by
      rw [pl_mem_box]
      constructor
      · rintro ⟨ha, hb, -, hd⟩
        have hcb : c * b ∈ ordBall K 0 := by simpa using mul_mem_ordBall_add hc0 hb
        exact ⟨ha, hb, (add_mem_ordBall_iff hcb d).1 hd⟩
      · rintro ⟨ha, hb, hd⟩
        have hcb : c * b ∈ ordBall K 0 := by simpa using mul_mem_ordBall_add hc0 hb
        exact ⟨ha, hb, by simpa using mul_mem_ordBall_add ha hc0, (add_mem_ordBall_iff hcb d).2 hd⟩
    simp only [Set.indicator_apply, Pi.one_apply, key, hc, ite_true]
    split_ifs <;> simp_all
  · simp only [Set.indicator_apply, Pi.one_apply, hc, ite_false]
    simp

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/-- For an unramified $\chi$ and $|\chi(\varpi) q^{1 - s}| \le 1$, the integral $T_0$ is $\mu(\mathcal{O}_K^\times) L(s, \chi)$. -/
theorem pl_ballZeta_unr {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {s : ℂ} (hs : ‖zetaRatio χ s‖ ≤ 1) :
    ballZeta χ μ (fun _ => 1) s 0 = (μ.real (ordShell K 0) : ℂ) * charLFactor K (unif K) χ s := by
  classical
  have h0 := ballZeta_one_zero χ μ hχ hs
  rw [shellCoeff_one_of_unramified χ μ hunr] at h0
  have h1 := one_sub_ne_zero χ hs
  rw [charLFactor, ite_eq_left hunr, ← h0]
  field_simp

omit [μ.Regular] [μ.IsAddHaarMeasure] in
/-- The integral of the indicator of $\varpi^m \mathcal{O}_K$ is its volume. -/
theorem pl_integral_indicator_ordBall (m : ℤ) :
    ∫ y, (ordBall K m).indicator (fun _ => (1 : ℂ)) y ∂μ = (μ.real (ordBall K m) : ℂ) := by
  rw [integral_indicator_const _ (isClosed_ordBall m).measurableSet, Complex.real_smul, mul_one]

omit [μ.Regular] in
/-- The integral of `plSub m F` against the two zeta functions for $F = \mathbf{1}_{\mathcal{O}_K^4}$ and $m \ge 0$. -/
theorem pl_integral_sub_box (χ : Kˣ →* ℂˣ) {m : ℤ} (hm : 0 ≤ m) {G : K × K × K × K → ℂ}
    (hG : ∀ p, G p = (plBox 0).indicator 1 p) (s : ℂ) :
    ∫ p, plSub m G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2 ∂(plProd μ) =
      zeta (χ * absChar K) μ ((ordBall K 0).indicator fun _ => 1) s *
        ((μ.real (ordBall K 0) : ℂ) * ((μ.real (ordBall K m) : ℂ) *
          zeta χ μ ((ordBall K 0).indicator fun _ => 1) s)) := by
  have h : ∀ p : K × K × K × K, plSub m G p * zetaFn (χ * absChar K) s p.1 * zetaFn χ s p.2.2.2 =
      ((ordBall K 0).indicator (fun _ => 1) p.1 * zetaFn (χ * absChar K) s p.1) *
        ((ordBall K 0).indicator (fun _ => 1) p.2.1 * ((ordBall K m).indicator (fun _ => 1) p.2.2.1 *
          ((ordBall K 0).indicator (fun _ => 1) p.2.2.2 * zetaFn χ s p.2.2.2))) := fun p => by
    rw [pl_sub_box hm hG]
    ring
  rw [integral_congr_ae (Eventually.of_forall h), pl_integral_prod4 μ
    (fun y => (ordBall K 0).indicator (fun _ => 1) y * zetaFn (χ * absChar K) s y)
    ((ordBall K 0).indicator fun _ => 1) ((ordBall K m).indicator fun _ => 1)
    (fun y => (ordBall K 0).indicator (fun _ => 1) y * zetaFn χ s y),
    pl_integral_indicator_ordBall, pl_integral_indicator_ordBall]
  rfl

/-- The constant $\mu(\mathcal{O}_K^\times)^2 \mu(\mathcal{O}_K) (\mu(\mathcal{O}_K) + \mu(\varpi \mathcal{O}_K))$. -/
noncomputable def plConst : ℂ :=
  ((μ.real (ordShell K 0) ^ 2 * μ.real (ordBall K 0) *
    (μ.real (ordBall K 0) + μ.real (ordBall K 1)) : ℝ) : ℂ)

omit [BorelSpace K] [μ.Regular] in
/-- The constant `plConst μ` is not zero. -/
theorem pl_const_ne_zero : plConst μ ≠ 0 := by
  have h0 : 0 < μ.real (ordBall K 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ordBall_ne_zero μ 0) (measure_ordBall_ne_top μ 0)
  have h1 : 0 ≤ μ.real (ordBall K 1) := measureReal_nonneg
  refine Complex.ofReal_ne_zero.2 (mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (measureReal_ordShell_ne_zero μ)) h0.ne') (by linarith))

/-- **The zeta integral of the unit box.** For an unramified $\chi$ and $\mathrm{Re}(s)$ large, the integral of $\mathbf{1}_{\mathcal{O}_K^4}(x) \chi(\det x) |\det x|^{s - 1}$ is `plConst μ` times $L(s, \chi) L(s, \chi |\cdot|)$. -/
theorem pl_integral_box (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1) {s : ℂ} (hs : plBound χ < s.re) :
    ∫ p, (plBox 0).indicator 1 p * zetaFn χ s (plDet p) ∂(plProd μ) =
      plConst μ * (charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s) := by
  obtain ⟨hs1, hs2⟩ := pl_norm_le_of_bound χ hs
  have hF := pl_isLocallyConstant_box (K := K)
  have hFs := pl_hasCompactSupport_box (K := K)
  have hFσ : IsLocallyConstant fun p => (plBox (K := K) 0).indicator (1 : K × K × K × K → ℂ)
    (plSwap p) := hF.comp_continuous pl_continuous_swap
  have hFσs := pl_hasCompactSupport_swap hFs
  have hG : ∀ p, (fun p => (plBox (K := K) 0).indicator (1 : K × K × K × K → ℂ) (plSwap p)) p =
      (plBox 0).indicator 1 p := fun p => by
    beta_reduce
    by_cases h : p ∈ plBox (K := K) 0
    · rw [Set.indicator_of_mem (pl_swap_mem_box.2 h), Set.indicator_of_mem h, Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem (fun h' => h (pl_swap_mem_box.1 h')), Set.indicator_of_notMem h]
  obtain ⟨N0, T0, h0⟩ := pl_rhs μ χ hχ (pl_isLocallyConstant_sub 0 hF)
    (pl_hasCompactSupport_sub le_rfl hFs)
  obtain ⟨N1, T1, h1⟩ := pl_rhs μ χ hχ (pl_isLocallyConstant_sub 1 hFσ)
    (pl_hasCompactSupport_sub zero_le_one hFσs)
  rw [pl_split μ χ hχ hs1 hF hFs, pl_region_eq μ χ hχ hs1 hF hFs 0 (h0 s hs1 hs2).1,
    pl_region_eq μ χ hχ hs1 hFσ hFσs 1 (h1 s hs1 hs2).1,
    pl_integral_sub_box μ χ le_rfl (fun p => rfl), pl_integral_sub_box μ χ zero_le_one hG,
    zeta_indicator_ordBall, zeta_indicator_ordBall, pl_ballZeta_unr μ hχ hunr hs1,
    pl_ballZeta_unr μ (hχ.mul isSmoothChar_absChar) ((pl_unr_abs_iff χ).2 hunr) hs2,
    pl_sign_unr hunr, plConst]
  push_cast
  ring

end Unramified

section Main

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The linear form $\lambda(z) = z$ on the space $\mathbb{C}$ of `plRep χ hχ`. -/
noncomputable def plForm (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) : Module.Dual ℂ (plRep χ hχ).V :=
  (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).toLinearMap

/-- The linear form `plForm χ hχ` is smooth. -/
theorem pl_form_mem (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    plForm χ hχ ∈ smoothVectors (plRep χ hχ).ρ.dual := by
  refine Subgroup.isOpen_mono (H₁ := (detChar K 2 (χ * sqrtAbsChar K)).ker) ?_
    (isOpen_ker_detChar K 2 _ (hχ.mul isSmoothChar_sqrtAbsChar))
  intro g hg
  have hg' : (detChar K 2 (χ * sqrtAbsChar K) g : ℂ) = 1 := by
    rw [MonoidHom.mem_ker.1 hg, Units.val_one]
  rw [mem_vecStabilizer, Representation.dual_apply]
  ext w
  simp [Module.Dual.transpose_apply, pl_rep_apply, hg']

/-- **The L-factor of $\chi |\cdot|^{1/2} \circ \det$.** This is `Langlands.LocalGL2.PSLFactorDetChar`: for each smooth character $\chi$ of $K^\times$, the Godement-Jacquet L-factor of the character $\chi |\cdot|^{1/2} \circ \det$ of $GL_2(K)$ is $L(s, \chi) L(s, \chi |\cdot|)$. -/
theorem psLFactorDetChar_holds : PSLFactorDetChar K := by
  intro χ hχ
  classical
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨c, hc, hcJ⟩ := pl_exists_scalar (K := K) (Measure.addHaar : Measure K)
  change IsGJLFactor K (plRep χ hχ) _
  have hZ : ∀ Φ v (l : Module.Dual ℂ (plRep χ hχ).V) s, gjZeta K (plRep χ hχ) Φ v l s =
      l v * ((c : ℂ) * ∫ p, Φ ((plEntries K).symm p) * zetaFn χ s (plDet p)
        ∂(plProd (Measure.addHaar : Measure K))) := by
    intro Φ v l s
    rw [pl_gjZeta_eq, hcJ]
    simp only [pl_det_symm]
  have hgood : ∀ Φ v (l : Module.Dual ℂ (plRep χ hχ).V), IsSchwartzBruhat K Φ →
      PlGood K (fun s => charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s)
        fun s => gjZeta K (plRep χ hχ) Φ v l s := by
    intro Φ v l hΦ
    refine pl_good_of_eq (pl_good_const_mul (l v * c) (pl_good_det Measure.addHaar χ hχ
      (hΦ.1.comp_continuous (plEntries K).symm.continuous)
      (hΦ.2.comp_homeomorph (plEntries K).symm))) 0 fun s _ => ?_
    rw [hZ]
    simp only [Function.comp_apply]
    ring
  by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
  · have hunr' := (pl_unr_abs_iff χ).2 hunr
    refine ⟨?_, fun Φ v l hΦ => hgood Φ v l hΦ, ?_⟩
    · refine ⟨(1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X) *
        (1 - Polynomial.C ((χ * absChar K) (unif K) : ℂ) * Polynomial.X), by simp, fun s => ?_⟩
      beta_reduce
      unfold charLFactor
      rw [ite_eq_left hunr, ite_eq_left hunr']
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
        Polynomial.eval_X, mul_inv]
    · have hΦ0 : IsSchwartzBruhat K fun x => (plBox (K := K) 0).indicator 1 (plEntries K x) :=
        ⟨pl_isLocallyConstant_box.comp_continuous (plEntries K).continuous,
          pl_hasCompactSupport_box.comp_homeomorph (plEntries K)⟩
      have hC := pl_const_ne_zero (Measure.addHaar : Measure K)
      have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      refine ⟨1, fun _ x => (plBox (K := K) 0).indicator 1 (plEntries K x), fun _ => (ULift.up 1 : (plRep χ hχ).V),
        fun _ => ⟨plForm χ hχ, pl_form_mem χ hχ⟩,
        fun _ => Polynomial.C (((c : ℂ) * plConst (Measure.addHaar : Measure K))⁻¹), 0,
        plBound χ, fun _ => hΦ0, fun s hs => ?_⟩
      rw [Fin.sum_univ_one, pow_zero, div_one, Polynomial.eval_C]
      beta_reduce
      erw [hZ]
      simp only [Homeomorph.apply_symm_apply]
      rw [pl_integral_box _ χ hχ hunr hs]
      have h1 : (plForm χ hχ) (ULift.up 1) = 1 := rfl
      change _ = _ * (plForm χ hχ (ULift.up 1) * _)
      rw [h1]
      field_simp
  · have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → (χ * absChar K) x = 1 :=
      fun h => hunr ((pl_unr_abs_iff χ).1 h)
    have hL : ∀ s, charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s = 1 :=
      fun s => by
        unfold charLFactor
        rw [ite_eq_right hunr, ite_eq_right hn, mul_one]
    have hfun : (fun s => charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s) =
        fun _ => 1 := funext hL
    rw [hfun]
    have : Nontrivial (plRep χ hχ).V := inferInstanceAs (Nontrivial (ULift.{u} ℂ))
    exact isGJLFactor_one_of_zeta _ fun Φ v l hΦ => pl_good_one (hgood Φ v l hΦ) hL

variable (K) in
/-- **The eight inputs on the principal series** from the two open inputs on the L-factors of the irreducible principal series and of the twisted Steinberg representation. -/
theorem nonSupercuspidalInputs_of_lFactor (h1 : PSLFactorIrreducible K)
    (h3 : PSLFactorSteinberg K) : NonSupercuspidalInputs K :=
  nonSupercuspidalInputs_of_contragredient_lFactor K (psContragredientIso_holds (K := K)) h1
    (psLFactorDetChar_holds (K := K)) h3

end Main

end LocalGL2

end Langlands
