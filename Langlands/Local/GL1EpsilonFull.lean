/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL1Epsilon

/-!
# Toward the local functional equation for $GL_1$ on all Schwartz-Bruhat functions

The module `Langlands.Local.GL1Epsilon` proves Tate's local functional equation for the two test functions $\mathbf{1}_{\mathcal{O}}$ and $\mathbf{1}_{1 + \mathfrak{p}^a}$. This module proves the facts that reduce the general case to translates of balls.

## Main results

* `secondCountableTopology`: a nonarchimedean local field is second countable. A consequence is `measurable_addChar_mul`, the product measurability of $(x, \xi) \mapsto \psi(x \xi)$.
* `IsConductor.continuous`: an additive character with a conductor exponent is locally constant, and thus continuous.
* `exists_forall_add_eq`: a locally constant function with compact support is zero outside a ball and invariant under translation by a smaller ball.
* `exists_eq_sum_ballIndicator`: such a function is a finite linear combination of the indicator functions $\mathbf{1}_{b + \varpi^N \mathcal{O}}$.
* `fourier_sum` and `zeta_sum`: the Fourier transform and the zeta integral are linear on finite combinations of such functions.

## The general case

The module `Langlands.Local.GL1EpsilonRamified` uses these results to prove the local functional equation for a ramified character on each locally constant function with compact support, and the nonvanishing of the Gauss integral.
-/

namespace Langlands.LocalGL1

universe u

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise

section Countable

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The translate $b + \varpi^N \mathcal{O}_K$ is open. -/
theorem isOpen_setOf_sub_mem_ordBall (b : K) (N : ℤ) : IsOpen {x : K | x - b ∈ ordBall K N} :=
  (isOpen_ordBall N).preimage (continuous_sub_right b)

/-- The translate $b + \varpi^N \mathcal{O}_K$ is closed. -/
theorem isClosed_setOf_sub_mem_ordBall (b : K) (N : ℤ) :
    IsClosed {x : K | x - b ∈ ordBall K N} :=
  (isClosed_ordBall N).preimage (continuous_sub_right b)

/-- Two translates of $\varpi^N \mathcal{O}_K$ that meet are equal: if $y - x \in \varpi^N \mathcal{O}_K$, then $y + \varpi^N \mathcal{O}_K = x + \varpi^N \mathcal{O}_K$. -/
theorem setOf_sub_mem_ordBall_eq {N : ℤ} {x y : K} (h : y - x ∈ ordBall K N) :
    {z : K | z - y ∈ ordBall K N} = {z | z - x ∈ ordBall K N} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hz
    simpa only [sub_add_sub_cancel] using add_mem_ordBall hz h
  · intro hz
    simpa only [neg_sub, sub_add_sub_cancel] using add_mem_ordBall hz (neg_mem_ordBall h)

/-- The translate $b + \varpi^N \mathcal{O}_K$ is in the ball $\varpi^M \mathcal{O}_K$ with $M = \min(N, \mathrm{ord}(b))$. -/
theorem setOf_sub_mem_ordBall_subset (b : K) (N : ℤ) :
    {x : K | x - b ∈ ordBall K N} ⊆ ordBall K (min N (ord K b)) := by
  intro x hx
  have hb : b ∈ ordBall K (min N (ord K b)) := by
    by_cases hb0 : b = 0
    · exact hb0 ▸ zero_mem_ordBall _
    · exact (mem_ordBall_of_ne_zero hb0).2 (min_le_right _ _)
  simpa using add_mem_ordBall (ordBall_anti (min_le_left _ _) hx) hb

/-- Each ball $\varpi^M \mathcal{O}_K$ is covered by finitely many translates of $\varpi^N \mathcal{O}_K$. -/
theorem exists_finset_ordBall_subset (M N : ℤ) :
    ∃ T : Finset K, ordBall K M ⊆ ⋃ t ∈ T, {x : K | x - t ∈ ordBall K N} :=
  (isCompact_ordBall M).elim_finite_subcover (fun t : K => {x : K | x - t ∈ ordBall K N})
    (fun t => isOpen_setOf_sub_mem_ordBall t N)
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [zero_mem_ordBall]⟩)

/-- Each element of $K$ is in some ball $\varpi^M \mathcal{O}_K$. -/
theorem exists_mem_ordBall (x : K) : ∃ M : ℤ, x ∈ ordBall K M := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ zero_mem_ordBall _⟩
  · exact ⟨ord K x, (mem_ordBall_of_ne_zero hx).2 le_rfl⟩

/-- **Second countability.** A nonarchimedean local field has a countable basis of open sets: the translates $t + \varpi^N \mathcal{O}_K$, with $N \in \mathbb{Z}$ and $t$ in a countable set that meets each coset of each $\varpi^N \mathcal{O}_K$. -/
instance secondCountableTopology : SecondCountableTopology K := by
  choose T hT using fun p : ℤ × ℤ => exists_finset_ordBall_subset (K := K) p.1 p.2
  set D : Set K := ⋃ p : ℤ × ℤ, (T p : Set K)
  have hD : D.Countable := Set.countable_iUnion fun p => (T p).countable_toSet
  set B : Set (Set K) := ⋃ t ∈ D, ⋃ N : ℤ, {{x : K | x - t ∈ ordBall K N}}
  have hB : B.Countable :=
    hD.biUnion fun t _ => Set.countable_iUnion fun N => Set.countable_singleton _
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (s := B) ?_ ?_).secondCountableTopology hB
  · intro v hv
    simp only [B, Set.mem_iUnion, Set.mem_singleton_iff] at hv
    obtain ⟨t, -, N, rfl⟩ := hv
    exact isOpen_setOf_sub_mem_ordBall t N
  · intro x v hx hv
    have h : {h : K | x + h ∈ v} ∈ 𝓝 (0 : K) :=
      ((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)).eventually (hv.mem_nhds hx)
    obtain ⟨N, hN⟩ := exists_ordBall_subset h
    obtain ⟨M, hM⟩ := exists_mem_ordBall x
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 (hT (M, N) hM)
    refine ⟨{z : K | z - t ∈ ordBall K N}, ?_, hxt, ?_⟩
    · simp only [B, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨t, Set.mem_iUnion.2 ⟨(M, N), ht⟩, N, rfl⟩
    · rw [← setOf_sub_mem_ordBall_eq hxt]
      intro z hz
      simpa using hN hz

/-- **Product measurability.** For a continuous additive character $\psi$, the function $(x, \xi) \mapsto \psi(x \xi)$ on $K \times K$ is measurable for the product $\sigma$-algebra. This uses the second countability of $K$. -/
theorem measurable_addChar_mul [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K ℂ}
    (hψ : Continuous ψ) : Measurable fun p : K × K => ψ (p.1 * p.2) :=
  (hψ.comp continuous_mul).measurable

end Countable

section SchwartzBruhat

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- An additive character with a conductor exponent is locally constant: it is constant on each translate of $\varpi^{-n} \mathcal{O}_K$. -/
theorem IsConductor.isLocallyConstant {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) :
    IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : {y : K | y - x ∈ ordBall K (-n)} ∈ 𝓝 x :=
    (isOpen_setOf_sub_mem_ordBall x (-n)).mem_nhds (by simp [zero_mem_ordBall])
  filter_upwards [h] with y hy
  rw [show y = x + (y - x) by ring, AddChar.map_add_eq_mul, hψ.trivial _ hy, mul_one]

/-- An additive character with a conductor exponent is continuous. -/
theorem IsConductor.continuous {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) : Continuous ψ :=
  hψ.isLocallyConstant.continuous

/-- The function $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ is the indicator function of the set $\{x : x - b \in \varpi^N \mathcal{O}_K\}$. -/
theorem ballIndicator_eq_indicator (b : K) (N : ℤ) :
    ballIndicator b N = {x : K | x - b ∈ ordBall K N}.indicator 1 := by
  funext x
  unfold ballIndicator
  by_cases h : x - b ∈ ordBall K N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ {x : K | x - b ∈ ordBall K N} from h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show x ∉ {x : K | x - b ∈ ordBall K N} from h)]

/-- The function $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ is locally constant. -/
theorem isLocallyConstant_ballIndicator (b : K) (N : ℤ) : IsLocallyConstant (ballIndicator b N) := by
  rw [ballIndicator_eq_indicator]
  exact isLocallyConstant_indicator (isOpen_setOf_sub_mem_ordBall b N)
    (isClosed_setOf_sub_mem_ordBall b N) fun _ _ => Eventually.of_forall fun _ => rfl

/-- The function $\mathbf{1}_{b + \varpi^N \mathcal{O}_K}$ has compact support. -/
theorem hasCompactSupport_ballIndicator (b : K) (N : ℤ) : HasCompactSupport (ballIndicator b N) := by
  refine HasCompactSupport.intro (isCompact_ordBall (min N (ord K b))) fun x hx => ?_
  rw [ballIndicator_eq_indicator]
  exact Set.indicator_of_notMem (fun h => hx (setOf_sub_mem_ordBall_subset b N h)) _

/-- The function $\varphi$ is a.e. strongly measurable, bounded, and zero outside some ball $\varpi^M \mathcal{O}_K$. Schwartz-Bruhat functions and their Fourier transforms have this property. -/
structure IsBallBounded [MeasurableSpace K] (μ : Measure K) (φ : K → ℂ) : Prop where
  /-- The function is a.e. strongly measurable. -/
  aestronglyMeasurable : AEStronglyMeasurable φ μ
  /-- The function is bounded. -/
  bounded : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C
  /-- The function is zero outside some ball. -/
  vanish : ∃ M : ℤ, ∀ x ∉ ordBall K M, φ x = 0

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K)

/-- A locally constant function with compact support is a.e. strongly measurable, bounded, and zero outside some ball. -/
theorem isBallBounded_of_isLocallyConstant {φ : K → ℂ} (hφ : IsLocallyConstant φ)
    (hφs : HasCompactSupport φ) : IsBallBounded μ φ := by
  obtain ⟨M, hM⟩ := exists_nat_tsupport_subset hφs
  exact ⟨hφ.continuous.aestronglyMeasurable, hφ.continuous.bounded_above_of_compact_support hφs,
    -(M : ℤ), fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hM h)⟩

/-- For a continuous function $g$, the function $\mathbf{1}_{\varpi^M \mathcal{O}_K} g$ is a.e. strongly measurable, bounded, and zero outside a ball. -/
theorem isBallBounded_indicator {g : K → ℂ} (hg : Continuous g) (M : ℤ) :
    IsBallBounded μ ((ordBall K M).indicator g) := by
  obtain ⟨C, hC⟩ := (isCompact_ordBall (K := K) M).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨hg.aestronglyMeasurable.indicator (isClosed_ordBall M).measurableSet, ⟨max C 0, ?_⟩,
    M, fun x hx => Set.indicator_of_notMem hx _⟩
  intro x
  by_cases hx : x ∈ ordBall K M
  · rw [Set.indicator_of_mem hx]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-- If $\varphi$ is bounded and zero outside a ball, and $g$ is integrable on each ball, then $\varphi g$ is integrable. -/
theorem IsBallBounded.integrable_mul {φ g : K → ℂ} (hφ : IsBallBounded μ φ)
    (hg : ∀ M : ℤ, Integrable ((ordBall K M).indicator g) μ) : Integrable (fun x => φ x * g x) μ := by
  obtain ⟨C, hC⟩ := hφ.bounded
  obtain ⟨M, hM⟩ := hφ.vanish
  have : (fun x => φ x * g x) = fun x => φ x * (ordBall K M).indicator g x := by
    funext x
    by_cases hx : x ∈ ordBall K M
    · rw [Set.indicator_of_mem hx]
    · rw [hM x hx, zero_mul, zero_mul]
  rw [this]
  exact (hg M).bdd_mul hφ.aestronglyMeasurable (Eventually.of_forall hC)

/-- A continuous function is integrable on each ball for a Haar measure. -/
theorem integrable_indicator_of_continuous [μ.IsAddHaarMeasure] {g : K → ℂ} (hg : Continuous g)
    (M : ℤ) : Integrable ((ordBall K M).indicator g) μ :=
  (integrable_indicator_iff (isClosed_ordBall M).measurableSet).2
    (hg.continuousOn.integrableOn_compact (isCompact_ordBall M))

/-- The integral of a finite linear combination: $\int (\sum_i c_i f_i) g = \sum_i c_i \int f_i g$ when each $f_i g$ is integrable. -/
theorem integral_sum_mul {ι : Type*} (T : Finset ι) (c : ι → ℂ) (f : ι → K → ℂ) (g : K → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x => f i x * g x) μ) :
    ∫ x, (∑ i ∈ T, c i * f i x) * g x ∂μ = ∑ i ∈ T, c i * ∫ x, f i x * g x ∂μ := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum T fun i hi => (hf i hi).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

variable [μ.IsAddHaarMeasure]

/-- **Linearity of the Fourier transform** on functions that are bounded, measurable and zero outside a ball. -/
theorem fourier_sum {ψ : AddChar K ℂ} (hψ : Continuous ψ) {ι : Type*} (T : Finset ι) (c : ι → ℂ)
    (f : ι → K → ℂ) (hf : ∀ i ∈ T, IsBallBounded μ (f i)) :
    fourier μ ψ (fun x => ∑ i ∈ T, c i * f i x) = fun ξ => ∑ i ∈ T, c i * fourier μ ψ (f i) ξ := by
  funext ξ
  exact integral_sum_mul μ T c f _ fun i hi => (hf i hi).integrable_mul μ
    fun M => integrable_indicator_of_continuous μ (hψ.comp (continuous_id.mul continuous_const)) M

variable (χ : Kˣ →* ℂˣ) [μ.Regular]

/-- **Linearity of the zeta integral** on functions that are bounded, measurable and zero outside a ball, for $|\chi(\varpi) q^{-s}| < 1$. -/
theorem zeta_sum (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) {ι : Type*} (T : Finset ι)
    (c : ι → ℂ) (f : ι → K → ℂ) (hf : ∀ i ∈ T, IsBallBounded μ (f i)) :
    zeta χ μ (fun x => ∑ i ∈ T, c i * f i x) s = ∑ i ∈ T, c i * zeta χ μ (f i) s :=
  integral_sum_mul μ T c f _ fun i hi => (hf i hi).integrable_mul μ fun M =>
    integrable_indicator_zetaFn_of_lt χ μ hχ hs (isClosed_ordBall M).measurableSet subset_rfl

end SchwartzBruhat

section Decomposition

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Uniform local constancy.** A locally constant function $\varphi$ with compact support is invariant under translation by a ball: there are $M \le N$ such that $\varphi$ is zero outside $\varpi^M \mathcal{O}_K$ and $\varphi(x + h) = \varphi(x)$ for each $x$ and each $h \in \varpi^N \mathcal{O}_K$. -/
theorem exists_forall_add_eq {φ : K → ℂ} (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    ∃ M N : ℤ, M ≤ N ∧ (∀ x ∉ ordBall K M, φ x = 0) ∧
      ∀ x, ∀ h ∈ ordBall K N, φ (x + h) = φ x := by
  obtain ⟨M, hM⟩ := exists_nat_tsupport_subset hφs
  have hloc : ∀ x : K, ∃ N : ℤ, ∀ h ∈ ordBall K N, φ (x + h) = φ x := by
    intro x
    have h1 : ∀ᶠ y in 𝓝 x, φ y = φ x := (IsLocallyConstant.iff_eventually_eq φ).1 hφ x
    have h2 : {h : K | φ (x + h) = φ x} ∈ 𝓝 (0 : K) :=
      ((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)).eventually h1
    obtain ⟨N, hN⟩ := exists_ordBall_subset h2
    exact ⟨N, fun h hh => hN hh⟩
  choose Nx hNx using hloc
  obtain ⟨T, hT⟩ := (isCompact_ordBall (K := K) (-(M : ℤ))).elim_finite_subcover
    (fun t : K => {x : K | x - t ∈ ordBall K (Nx t)}) (fun t => isOpen_setOf_sub_mem_ordBall t _)
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [zero_mem_ordBall]⟩)
  set N : ℤ := ∑ t ∈ T, ((Nx t).natAbs : ℤ) with hNdef
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun t _ => by positivity
  have hNt : ∀ t ∈ T, Nx t ≤ N := fun t ht =>
    (Int.le_natAbs).trans (Finset.single_le_sum (f := fun t => ((Nx t).natAbs : ℤ))
      (fun t _ => by positivity) ht)
  have hzero : ∀ x ∉ ordBall K (-(M : ℤ)), φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hM h)
  refine ⟨-(M : ℤ), N, by omega, hzero, fun x h hh => ?_⟩
  by_cases hx : x ∈ ordBall K (-(M : ℤ))
  · obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 (hT hx)
    have hxt' : x - t ∈ ordBall K (Nx t) := hxt
    have hh' : h ∈ ordBall K (Nx t) := ordBall_anti (hNt t ht) hh
    have e1 := hNx t (x - t) hxt'
    have e2 := hNx t (x - t + h) (add_mem_ordBall hxt' hh')
    rw [show t + (x - t) = x by ring] at e1
    rw [show t + (x - t + h) = x + h by ring] at e2
    rw [e1, e2]
  · have hxh : x + h ∉ ordBall K (-(M : ℤ)) := fun h' =>
      hx (by simpa using add_mem_ordBall h' (neg_mem_ordBall (ordBall_anti (by omega) hh)))
    rw [hzero x hx, hzero _ hxh]

/-- The ball $\varpi^N \mathcal{O}_K$ as an additive subgroup of $K$. -/
def ordBallAddSubgroup (N : ℤ) : AddSubgroup K where
  carrier := ordBall K N
  add_mem' := add_mem_ordBall
  zero_mem' := zero_mem_ordBall N
  neg_mem' := neg_mem_ordBall

/-- **Decomposition into balls.** Each locally constant function $\varphi$ with compact support is a finite linear combination of indicator functions of translated balls: there are $N$ and a finite set $T$ with $\varphi = \sum_{b \in T} \varphi(b) \mathbf{1}_{b + \varpi^N \mathcal{O}_K}$. -/
theorem exists_eq_sum_ballIndicator {φ : K → ℂ} (hφ : IsLocallyConstant φ)
    (hφs : HasCompactSupport φ) :
    ∃ (N : ℤ) (T : Finset K), ∀ x, φ x = ∑ b ∈ T, φ b * ballIndicator b N x := by
  classical
  obtain ⟨M, N, hMN, hzero, hadd⟩ := exists_forall_add_eq hφ hφs
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
  set F := hS.toFinset
  have hval : ∀ x : K, φ (Quotient.out (QuotientAddGroup.mk x : K ⧸ G)) *
      ballIndicator (Quotient.out (QuotientAddGroup.mk x : K ⧸ G)) N x = φ x := by
    intro x
    set b := Quotient.out (QuotientAddGroup.mk x : K ⧸ G)
    have hb : (QuotientAddGroup.mk b : K ⧸ G) = QuotientAddGroup.mk x := QuotientAddGroup.out_eq' _
    have hxb : x - b ∈ ordBall K N := (hG b x).1 hb
    rw [ballIndicator, Set.indicator_of_mem hxb, Pi.one_apply, mul_one,
      ← hadd b (x - b) hxb, add_sub_cancel]
  refine ⟨N, F.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image fun q₁ _ q₂ _ h => by
    rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂]
    exact congrArg _ h]
  rw [eq_comm]
  refine (Finset.sum_eq_single (QuotientAddGroup.mk x : K ⧸ G) ?_ ?_).trans (hval x)
  · intro q _ hq
    rw [ballIndicator, Set.indicator_of_notMem, mul_zero]
    intro h
    refine hq ?_
    rw [← QuotientAddGroup.out_eq' q]
    exact (hG _ x).2 h
  · intro hx
    rw [hval]
    refine hzero x fun hxM => hx ?_
    rw [Set.Finite.mem_toFinset]
    exact ⟨x, hxM, rfl⟩

end Decomposition

end Langlands.LocalGL1
