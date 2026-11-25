/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Hecke
import Mathlib

/-!
# Hecke's theorem for `ℚ`

This file proves `Langlands.HeckeFunctionalEquationAt ℚ`. A Hecke character $\chi$ of $\mathbb{Q}$ is the product of a primitive Dirichlet character $\psi$ and a power $\|\cdot\|^{t}$ of the idele norm. The completed L-function of $\chi$ is the completed Dirichlet L-function of $\psi$ at $s + t$. The functional equation and the poles then come from Mathlib.

* `Langlands.HeckeRat.Top.exists_trivial_on_units`: a Hecke character is trivial on an open subgroup of ideles of the form $1 \times \prod_{v \in S} (1 + \mathfrak{p}_v^k) \times \prod_{v \notin S} \mathcal{O}_v^\times$.
* `Langlands.HeckeRat.Analytic.norm_rootNumber`: the root number of a primitive Dirichlet character has absolute value $1$.
* `Langlands.HeckeRat.psi`: the Dirichlet character of $\chi$, of level `Langlands.HeckeRat.level χ`.
* `Langlands.HeckeRat.psi_isPrimitive`: this Dirichlet character is primitive.
* `Langlands.HeckeRat.absNorm_conductor`: the norm of the conductor of $\chi$ is the level.
* `Langlands.HeckeRat.norm_chi`: $|\chi| = \|\cdot\|^{\mathrm{Re}\, t}$.
* `Langlands.HeckeRat.completed_eq`: the completed L-function of $\chi$ is the completed L-function of $\psi$ at $s + t$, on the half plane of convergence.
* `Langlands.heckeFunctionalEquationAt_rat`: the statement `HeckeFunctionalEquationAt ℚ`.
-/

namespace Langlands.HeckeRat.Top

open NumberField IsDedekindDomain Filter Topology
open scoped WithZero


theorem eq_one_of_forall_pow_two_pow {z : ℂ} (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      set a := z ^ (2 ^ k) with ha
      have h1 : z ^ (2 ^ (k + 1)) - 1 = (a - 1) * (a + 1) := by
        rw [ha, pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖a + 1‖ := by
        have : a + 1 = 2 - (1 - a) := by ring
        have h3 := norm_sub_norm_le (2 : ℂ) (1 - a)
        rw [← this, norm_sub_rev] at h3
        have := h k
        rw [← ha] at this
        simp at h3
        linarith
      rw [h1, norm_mul, pow_succ]
      calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
        _ ≤ ‖a - 1‖ * ‖a + 1‖ := by gcongr
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have := (key n).trans_lt (h n)
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith

theorem valued_nhds {R : Type*} [Ring R] [Valued R ℤᵐ⁰] {u : Set R} {x : R} (hu : u ∈ 𝓝 x) :
    ∃ k : ℕ, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(k : ℤ)) → y ∈ u := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hu
  set g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have g0 : g ≠ 0 := by
    exact (γ.isUnit.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := ((Valued.v : Valuation R ℤᵐ⁰) : R →*₀ ℤᵐ⁰)))).ne_zero
  refine ⟨(-WithZero.log g).toNat + 1, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  rw [← hg]
  have : WithZero.exp (-(((-WithZero.log g).toNat + 1 : ℕ) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.mpr (by omega)
  rwa [WithZero.exp_log g0] at this

open RestrictedProduct in
theorem finite_nhds_one (K : Type*) [Field K] [NumberField K]
    {B : Set (FiniteAdeleRing (𝓞 K) K)} (hB : B ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ), ∀ y : FiniteAdeleRing (𝓞 K) K,
      (∀ v, Valued.v (y v) ≤ 1) →
      (∀ v ∈ S, Valued.v (y v - 1) ≤ WithZero.exp (-(k : ℤ))) → y ∈ B := by
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let one : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K := fun _ => 1
  have h1 : structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite one =
      (1 : FiniteAdeleRing (𝓞 K) K) := rfl
  have hB' : B ∈ 𝓝 (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite one) := by
    rw [h1]; exact hB
  rw [nhds_eq_map_structureMap hAopen] at hB'
  have hB'' : Set.preimage (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) B ∈
      𝓝 one := hB'
  rw [nhds_pi, Filter.mem_pi'] at hB''
  obtain ⟨I, t, ht, hIt⟩ := hB''
  have : ∀ v : HeightOneSpectrum (𝓞 K), ∃ k : ℕ, ∀ y : v.adicCompletion K,
      Valued.v (y - 1) ≤ WithZero.exp (-(k : ℤ)) → (hy : y ∈ v.adicCompletionIntegers K) →
        (⟨y, hy⟩ : v.adicCompletionIntegers K) ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
    obtain ⟨k, hk⟩ := valued_nhds hu
    exact ⟨k, fun y hy hy' => hut (hk y (by simpa [one] using hy))⟩
  choose k hk using this
  refine ⟨I, I.sup k, fun y hy1 hyS => ?_⟩
  have hyI : ∀ v, y v ∈ v.adicCompletionIntegers K := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hy1 v)
  have : y = structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
      (fun v => ⟨y v, hyI v⟩) := rfl
  rw [this]
  apply hIt
  intro v hv
  apply hk v (y v) _ (hyI v)
  refine (hyS v hv).trans ?_
  rw [WithZero.exp_le_exp]
  have := Finset.le_sup (f := k) hv
  omega

/-- The set of ideles in the statement of `exists_trivial_on_units`. -/
def Good (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ)
    (x : IdeleGroup (𝓞 K) K) : Prop :=
  (x : AdeleRing (𝓞 K) K).1 = 1 ∧ (∀ v, Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1) ∧
    (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 K) K).2 v - 1) ≤ WithZero.exp (-(k : ℤ)))

theorem good_one (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : ℕ) : Good K S k 1 := by
  refine ⟨rfl, fun v => ?_, fun v _ => ?_⟩
  · show Valued.v (1 : v.adicCompletion K) = 1
    exact map_one _
  · show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    simp

theorem good_mul (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : ℕ) {x y : IdeleGroup (𝓞 K) K} (hx : Good K S k x) (hy : Good K S k y) :
    Good K S k (x * y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, fun v => ?_, fun v hv => ?_⟩
  · show (x : AdeleRing (𝓞 K) K).1 * (y : AdeleRing (𝓞 K) K).1 = 1
    rw [hx1, hy1, one_mul]
  · show Valued.v ((x : AdeleRing (𝓞 K) K).2 v * (y : AdeleRing (𝓞 K) K).2 v) = 1
    rw [map_mul, hx2, hy2, one_mul]
  · show Valued.v ((x : AdeleRing (𝓞 K) K).2 v * (y : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    set a := (x : AdeleRing (𝓞 K) K).2 v
    set b := (y : AdeleRing (𝓞 K) K).2 v
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine Valuation.map_add_le _ ?_ (hx3 v hv)
    rw [map_mul, hx2, one_mul]
    exact hy3 v hv

theorem good_pow (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : ℕ) {x : IdeleGroup (𝓞 K) K} (hx : Good K S k x) (n : ℕ) : Good K S k (x ^ n) := by
  induction n with
  | zero => simpa using good_one K S k
  | succ n ih => rw [pow_succ]; exact good_mul K S k ih hx

theorem good_inv (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : ℕ) {x : IdeleGroup (𝓞 K) K} (hx : Good K S k x) : Good K S k x⁻¹ := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have h := Units.mul_inv x
  refine ⟨?_, fun v => ?_, fun v hv => ?_⟩
  · have h' := congrArg Prod.fst h
    change (x : AdeleRing (𝓞 K) K).1 * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 = 1
      at h'
    rwa [hx1, one_mul] at h'
  all_goals
    have h' := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) h
    change (x : AdeleRing (𝓞 K) K).2 v *
      ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v = 1 at h'
    set a := (x : AdeleRing (𝓞 K) K).2 v
    set b := ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v
    have hb : Valued.v b = 1 := by
      have := congrArg Valued.v h'
      rwa [map_mul, map_one, hx2, one_mul] at this
  · exact hb
  · have : b - 1 = -(b * (a - 1)) := by linear_combination h'
    rw [this, Valuation.map_neg, map_mul, hb, one_mul]
    exact hx3 v hv

theorem idele_nhds_one (K : Type*) [Field K] [NumberField K] {U : Set (IdeleGroup (𝓞 K) K)}
    (hU : U ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ), ∀ x, Good K S k x → x ∈ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨t1, ht1, t2, ht2, ht12⟩ := ht
  have ht2' : MulOpposite.op ⁻¹' t2 ∈ 𝓝 (1 : AdeleRing (𝓞 K) K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using ht2)
  have ht1' : t1 ∈ 𝓝 (1 : AdeleRing (𝓞 K) K) := by simpa using ht1
  change t1 ∈ 𝓝 ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)) at ht1'
  change MulOpposite.op ⁻¹' t2 ∈ 𝓝 ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))
    at ht2'
  rw [nhds_prod_eq, Filter.mem_prod_iff] at ht1' ht2'
  obtain ⟨A1, hA1, B1, hB1, h1⟩ := ht1'
  obtain ⟨A2, hA2, B2, hB2, h2⟩ := ht2'
  obtain ⟨S, k, hSk⟩ := finite_nhds_one K (Filter.inter_mem hB1 hB2)
  refine ⟨S, k, fun x hx => htU (ht12 ⟨h1 ⟨?_, ?_⟩, h2 ⟨?_, ?_⟩⟩)⟩
  · show (x : AdeleRing (𝓞 K) K).1 ∈ A1
    rw [hx.1]; exact mem_of_mem_nhds hA1
  · exact (hSk _ (fun v => (hx.2.1 v).le) hx.2.2).1
  · show ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 ∈ A2
    rw [(good_inv K S k hx).1]; exact mem_of_mem_nhds hA2
  · have hx' := good_inv K S k hx
    exact (hSk _ (fun v => (hx'.2.1 v).le) hx'.2.2).2

theorem exists_trivial_on_units (K : Type*) [Field K] [NumberField K]
    (χ : Langlands.HeckeCharacter K) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ),
      ∀ x : IdeleGroup (𝓞 K) K, (x : AdeleRing (𝓞 K) K).1 = 1 →
        (∀ v, Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1) →
        (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 K) K).2 v - 1) ≤ WithZero.exp (-(k : ℤ))) →
        χ (x : IdeleClassGroup (𝓞 K) K) = 1 := by
  let f : IdeleGroup (𝓞 K) K → ℂ := fun x => ((χ (x : IdeleClassGroup (𝓞 K) K) : ℂˣ) : ℂ)
  have hf : Continuous f :=
    Units.continuous_val.comp ((map_continuous χ).comp continuous_quot_mk)
  have hU : {x | ‖f x - 1‖ < 1 / 2} ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) := by
    refine (isOpen_lt (continuous_norm.comp (hf.sub continuous_const)) continuous_const).mem_nhds ?_
    simp [f]
  obtain ⟨S, k, hSk⟩ := idele_nhds_one K hU
  refine ⟨S, k, fun x h1 h2 h3 => ?_⟩
  have hx : Good K S k x := ⟨h1, h2, h3⟩
  apply Units.ext
  apply eq_one_of_forall_pow_two_pow
  intro m
  have := hSk _ (good_pow K S k hx (2 ^ m))
  simpa [f, QuotientGroup.mk_pow, map_pow, Units.val_pow_eq_pow_val] using this

end Langlands.HeckeRat.Top

namespace Langlands.HeckeRat.Analytic

open Complex DirichletCharacter


theorem isPrimitive_inv {N : ℕ} {ψ : DirichletCharacter ℂ N} (hψ : ψ.IsPrimitive) :
    ψ⁻¹.IsPrimitive :=
  (isPrimitive_def _).mpr ((conductor_inv ψ).trans hψ)

lemma conj_stdAddChar {N : ℕ} [NeZero N] (a : ZMod N) :
    starRingEnd ℂ (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_neZero N),
    AddChar.inv_apply]

lemma conj_gaussSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) = χ⁻¹ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  simp only [gaussSum, map_sum, map_mul, conj_stdAddChar]
  have h1 : ∀ a, (starRingEnd ℂ) (χ a) = χ⁻¹ a := fun a => MulChar.star_apply' χ a
  simp only [h1, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun a => ?_)
  simp only [Equiv.neg_apply]
  rw [← mul_assoc, ← map_mul, neg_one_mul, neg_neg]

lemma gaussSum_mul_gaussSum_inv {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = N := by
  have h1 : ZMod.dft (fun k => (χ : ZMod N → ℂ) k) =
      fun k => (χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar) * χ⁻¹ k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul k, map_mul]
    ring
  have h2 := congrFun (ZMod.dft_dft (fun k => (χ : ZMod N → ℂ) k)) (-1)
  rw [h1, ZMod.dft_const_mul] at h2
  simp only at h2
  rw [(isPrimitive_inv hχ).fourierTransform_eq_inv_mul_gaussSum, inv_inv, neg_neg,
    map_one, one_mul, smul_eq_mul, mul_one] at h2
  exact h2

theorem norm_rootNumber {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ.IsPrimitive) :
    ‖rootNumber ψ‖ = 1 := by
  have hg : ‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 = N := by
    have h := gaussSum_mul_gaussSum_inv hψ
    have hc : gaussSum ψ ZMod.stdAddChar * starRingEnd ℂ (gaussSum ψ ZMod.stdAddChar) = N := by
      rw [conj_gaussSum, ← h]; ring
    have : ((‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 : ℝ) : ℂ) = (N : ℂ) := by
      rw [← hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  have hN : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = ‖gaussSum ψ ZMod.stdAddChar‖ := by
    rw [norm_natCast_cpow_of_pos (Nat.pos_of_neZero N),
      show (1 / 2 : ℂ).re = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow, ← hg,
      Real.sqrt_sq (norm_nonneg _)]
  have hg0 : ‖gaussSum ψ ZMod.stdAddChar‖ ≠ 0 := by
    intro h0
    rw [h0] at hg
    have h1 : (N : ℝ) = 0 := by rw [← hg]; norm_num
    exact NeZero.ne N (by exact_mod_cast h1)
  rw [rootNumber, norm_div, norm_div, norm_pow, norm_I, one_pow, div_one, hN, div_self hg0]

theorem meromorphicOn_completedLFunction_shift {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (t : ℂ) : MeromorphicOn (fun s => completedLFunction ψ (s + t)) Set.univ := by
  intro x _
  have hpow : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ (-(s + t))) := fun s =>
    ((differentiableAt_id.add_const t).neg).const_cpow (Or.inl (by exact_mod_cast NeZero.ne N))
  have h0 : Differentiable ℂ (fun s => ZMod.completedLFunction₀ (ψ : ZMod N → ℂ) (s + t)) :=
    (ZMod.differentiable_completedLFunction₀ _).comp (differentiable_id.add_const t)
  have : (fun s => completedLFunction ψ (s + t)) = fun s =>
      ZMod.completedLFunction₀ (ψ : ZMod N → ℂ) (s + t) - (N : ℂ) ^ (-(s + t)) * ψ 0 / (s + t)
        - (N : ℂ) ^ (-(s + t)) * (∑ j, ψ j) / (1 - (s + t)) := by
    funext s
    exact ZMod.completedLFunction_eq _ _
  rw [this]
  have a0 := (h0.analyticAt x).meromorphicAt
  have a1 := (hpow.analyticAt x).meromorphicAt
  fun_prop

theorem analyticAt_completedLFunction_shift {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) (t s : ℂ) : AnalyticAt ℂ (fun s => completedLFunction ψ (s + t)) s :=
  ((differentiable_completedLFunction hψ).comp (differentiable_id.add_const t)).analyticAt s

lemma completedRiemannZeta_shift_eq (t : ℂ) : (fun s => completedRiemannZeta (s + t)) =
    fun s => completedRiemannZeta₀ (s + t) - 1 / (s + t) - 1 / (1 - (s + t)) :=
  funext fun _ => completedRiemannZeta_eq _

lemma analyticAt_completedZeta₀_shift (t s : ℂ) :
    AnalyticAt ℂ (fun s => completedRiemannZeta₀ (s + t)) s :=
  (differentiable_completedZeta₀.comp (differentiable_id.add_const t)).analyticAt s

theorem analyticAt_completedRiemannZeta_shift (t s : ℂ) (h0 : s ≠ -t) (h1 : s ≠ 1 - t) :
    AnalyticAt ℂ (fun s => completedRiemannZeta (s + t)) s := by
  rw [completedRiemannZeta_shift_eq]
  have ha : s + t ≠ 0 := fun h => h0 (eq_neg_of_add_eq_zero_left h)
  have hb : 1 - (s + t) ≠ 0 := fun h => h1 (by linear_combination -h)
  have := analyticAt_completedZeta₀_shift t s
  fun_prop (disch := assumption)

lemma meromorphicAt_completedRiemannZeta_shift (t x : ℂ) :
    MeromorphicAt (fun s => completedRiemannZeta (s + t)) x := by
  rw [completedRiemannZeta_shift_eq]
  have := (analyticAt_completedZeta₀_shift t x).meromorphicAt
  fun_prop

theorem meromorphicOrderAt_completedRiemannZeta_shift_zero (t : ℂ) :
    meromorphicOrderAt (fun s => completedRiemannZeta (s + t)) (-t) = -1 := by
  suffices key : meromorphicOrderAt (fun s => completedRiemannZeta (s + t)) _ = ((-1 : ℤ) : WithTop ℤ) by
    rw [key]; rfl
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_completedRiemannZeta_shift t _)]
  refine ⟨fun s => (s + t) * completedRiemannZeta₀ (s + t) - 1 - (s + t) / (1 - (s + t)),
    ?_, ?_, ?_⟩
  · have := analyticAt_completedZeta₀_shift t (-t)
    have hb : 1 - (-t + t) ≠ 0 := by simp
    fun_prop (disch := assumption)
  · simp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z + t ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
    rw [completedRiemannZeta_eq, sub_neg_eq_add, zpow_neg_one, smul_eq_mul, mul_sub, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hz', one_mul, mul_one, div_eq_mul_inv (z + t),
      inv_mul_cancel_left₀ hz', one_div, one_div]

theorem meromorphicOrderAt_completedRiemannZeta_shift_one (t : ℂ) :
    meromorphicOrderAt (fun s => completedRiemannZeta (s + t)) (1 - t) = -1 := by
  suffices key : meromorphicOrderAt (fun s => completedRiemannZeta (s + t)) _ = ((-1 : ℤ) : WithTop ℤ) by
    rw [key]; rfl
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_completedRiemannZeta_shift t _)]
  refine ⟨fun s => (s + t - 1) * completedRiemannZeta₀ (s + t) - (s + t - 1) / (s + t) + 1,
    ?_, ?_, ?_⟩
  · have := analyticAt_completedZeta₀_shift t (1 - t)
    have hb : 1 - t + t ≠ 0 := by simp
    fun_prop (disch := assumption)
  · simp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z + t - 1 ≠ 0 := fun h => hz (by rw [Set.mem_singleton_iff]; linear_combination h)
    have e : z - (1 - t) = z + t - 1 := by ring
    have e2 : 1 - (z + t) = -(z + t - 1) := by ring
    rw [completedRiemannZeta_eq, e, e2, zpow_neg_one, smul_eq_mul, mul_add, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hz', one_mul, div_eq_mul_inv (z + t - 1),
      inv_mul_cancel_left₀ hz', mul_one, one_div, one_div, inv_neg]
    ring

theorem completedLFunction_eq_mul_LSeries {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    completedLFunction ψ s = DirichletCharacter.gammaFactor ψ s * LSeries (fun n => ψ n) s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hγ : DirichletCharacter.gammaFactor ψ s ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [← LFunction_eq_LSeries ψ hs, LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0),
    mul_div_cancel₀ _ hγ]

end Langlands.HeckeRat.Analytic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Langlands.HeckeRat

local notation "HS" => HeightOneSpectrum (𝓞 ℚ)
local notation "𝕀" => IdeleGroup (𝓞 ℚ) ℚ
local notation "v₀" => Rat.infinitePlace

/-- The component of an idele at the infinite place of `ℚ`. -/
noncomputable def compInf : 𝕀 →* (v₀).Completionˣ :=
  Units.map ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) v₀).comp
    (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))).toMonoidHom

/-- The component of an idele at a finite place of `ℚ`. -/
noncomputable def compFin (v : HS) : 𝕀 →* (v.adicCompletion ℚ)ˣ :=
  Units.map ((RestrictedProduct.evalRingHom _ v).comp
    (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))).toMonoidHom

@[simp] theorem coe_compInf (x : 𝕀) :
    (compInf x : (v₀).Completion) = (x : AdeleRing (𝓞 ℚ) ℚ).1 v₀ := rfl

@[simp] theorem coe_compFin (v : HS) (x : 𝕀) :
    (compFin v x : v.adicCompletion ℚ) = (x : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl

theorem compFin_ofAdicCompletion_self (v : HS) (y : (v.adicCompletion ℚ)ˣ) :
    compFin v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v y) = y := by
  classical
  refine Units.ext ?_
  change RestrictedProduct.mulSingle (fun w => adicCompletionIntegers ℚ w) v (y : v.adicCompletion ℚ) v = y
  convert RestrictedProduct.mulSingle_eq_same (fun w => adicCompletionIntegers ℚ w) v
    (y : v.adicCompletion ℚ)

theorem compFin_ofAdicCompletion_of_ne {v w : HS} (h : w ≠ v) (y : (w.adicCompletion ℚ)ˣ) :
    compFin v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w y) = 1 := by
  classical
  refine Units.ext ?_
  change RestrictedProduct.mulSingle (fun w => adicCompletionIntegers ℚ w) w (y : w.adicCompletion ℚ) v = 1
  convert RestrictedProduct.mulSingle_eq_of_ne' (fun w => adicCompletionIntegers ℚ w)
    (y : w.adicCompletion ℚ) h

theorem compInf_ofAdicCompletion (w : HS) (y : (w.adicCompletion ℚ)ˣ) :
    compInf (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w y) = 1 := rfl

theorem compInf_ofCompletion (y : (v₀).Completionˣ) :
    compInf (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ v₀ y) = y := by
  classical
  refine Units.ext ?_
  change InfiniteAdeleRing.ofCompletion v₀ (y : (v₀).Completion) v₀ = y
  rw [InfiniteAdeleRing.ofCompletion_apply]
  convert Pi.mulSingle_eq_same (M := fun v : InfinitePlace ℚ => v.Completion) v₀ (y : (v₀).Completion)

theorem compFin_ofCompletion (v : HS) (y : (v₀).Completionˣ) :
    compFin v (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ v₀ y) = 1 := rfl

theorem coe_compInf_unitEmbedding (q : ℚˣ) :
    (compInf (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q) : (v₀).Completion) = algebraMap ℚ _ q := rfl

theorem coe_compFin_unitEmbedding (v : HS) (q : ℚˣ) :
    (compFin v (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q) : v.adicCompletion ℚ) =
      algebraMap ℚ _ q := rfl

theorem ext_idele {x y : 𝕀} (hinf : compInf x = compInf y) (hfin : ∀ v, compFin v x = compFin v y) :
    x = y := by
  ext1
  refine Prod.ext ?_ ?_
  · funext w
    obtain rfl := Subsingleton.elim w v₀
    exact congrArg Units.val hinf
  · exact FiniteAdeleRing.ext _ fun v =>
      congrArg (fun u : (v.adicCompletion ℚ)ˣ => (u : v.adicCompletion ℚ)) (hfin v)

/-! ### Valuations of rational numbers -/

/-- The prime number of a finite place of `ℚ`. -/
noncomputable def pr (v : HS) : ℕ := Rat.HeightOneSpectrum.natGenerator v

theorem pr_prime (v : HS) : (pr v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v

theorem pr_injective : Function.Injective pr := by
  intro v w h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem intCast_intEquiv (b : 𝓞 ℚ) :
    ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) b : ℤ) : 𝓞 ℚ) = b := by
  rw [← map_intCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm, Int.cast_id]
  exact (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply b

theorem intCast_mem_asIdeal_pow (v : HS) (z : ℤ) (k : ℕ) :
    (z : 𝓞 ℚ) ∈ v.asIdeal ^ k ↔ (pr v : ℤ) ^ k ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), Ideal.map_pow,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    map_intCast]
  exact Iff.rfl

theorem valuation_intCast (v : HS) (z : ℤ) :
    v.valuation ℚ (z : ℚ) = v.intValuation (z : 𝓞 ℚ) := by
  rw [← valuation_of_algebraMap (K := ℚ)]
  congr 1

theorem valuation_intCast_le_iff (v : HS) (z : ℤ) (k : ℕ) :
    v.valuation ℚ (z : ℚ) ≤ WithZero.exp (-(k : ℤ)) ↔ (pr v : ℤ) ^ k ∣ z := by
  rw [valuation_intCast, intValuation_le_pow_iff_mem, intCast_mem_asIdeal_pow]

theorem valuation_intCast_eq_one_iff (v : HS) (z : ℤ) :
    v.valuation ℚ (z : ℚ) = 1 ↔ ¬ (pr v : ℤ) ∣ z := by
  have h := intCast_mem_asIdeal_pow v z 1
  rw [pow_one, pow_one] at h
  rw [valuation_intCast, ← h, intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff]

theorem valuation_pr_self (v : HS) : v.valuation ℚ (pr v : ℚ) = WithZero.exp (-1) := by
  have hp := (pr_prime v).two_le
  have e : (pr v : ℚ) = ((pr v : ℤ) : ℚ) := by norm_cast
  have h1 := (valuation_intCast_le_iff v (pr v) 1).mpr (by simp)
  have h2 : ¬ v.valuation ℚ ((pr v : ℤ) : ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [valuation_intCast_le_iff]
    intro h
    have := Int.le_of_dvd (by positivity) h
    have : ((pr v : ℕ) : ℤ) ≥ 2 := by exact_mod_cast hp
    nlinarith
  rw [← e] at h1 h2
  have h0 : v.valuation ℚ (pr v : ℚ) ≠ 0 := by
    simp only [ne_eq, map_eq_zero, Nat.cast_eq_zero]
    exact (pr_prime v).ne_zero
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  rw [WithZero.exp_inj]
  push_cast at h1 h2
  omega

theorem valuation_pr_of_ne {v w : HS} (h : w ≠ v) : v.valuation ℚ (pr w : ℚ) = 1 := by
  have e : (pr w : ℚ) = ((pr w : ℤ) : ℚ) := by norm_cast
  rw [e, valuation_intCast_eq_one_iff, Int.natCast_dvd_natCast]
  intro hd
  exact h (pr_injective ((Nat.prime_dvd_prime_iff_eq (pr_prime v) (pr_prime w)).mp hd).symm)

theorem val_coe (v : HS) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' v q

theorem val_intCast_le_iff (v : HS) (z : ℤ) (k : ℕ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ)) ≤ WithZero.exp (-(k : ℤ)) ↔
      (pr v : ℤ) ^ k ∣ z := by
  rw [val_coe, valuation_intCast_le_iff]

theorem val_intCast_eq_one_iff (v : HS) (z : ℤ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ)) = 1 ↔ ¬ (pr v : ℤ) ∣ z := by
  rw [val_coe, valuation_intCast_eq_one_iff]

theorem val_le_one_of_eq_one {v : HS} {x : v.adicCompletion ℚ} (h : Valued.v x = 1) :
    Valued.v x ≤ 1 := h.le

theorem val_sub_one_le_one {v : HS} {x : v.adicCompletion ℚ} (h : Valued.v x ≤ 1) :
    Valued.v (x - 1) ≤ 1 :=
  (Valuation.map_sub _ _ _).trans (max_le h (by simp))

theorem exp_neg_nat_le_one (k : ℕ) : WithZero.exp (-(k : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simp

/-! ### Approximation by integers -/

theorem exists_approx (v : HS) (u : v.adicCompletion ℚ) (hu : Valued.v u ≤ 1) (k : ℕ) :
    ∃ b : 𝓞 ℚ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ b) - u) ≤
      WithZero.exp (-(k : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer ℚ
  set c : v.adicCompletion ℚ := algebraMap ℚ _ (π ^ (-(k : ℤ)))
  have hc : Valued.v c = WithZero.exp (k : ℤ) := by
    rw [val_coe, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hcont : Continuous (fun y : v.adicCompletion ℚ => (y - u) * c) :=
    (continuous_sub_right u).mul continuous_const
  have hopen := (Valued.isOpen_integer (v.adicCompletion ℚ)).preimage hcont
  obtain ⟨r, hr⟩ := (denseRange_algebraMap (R := 𝓞 ℚ) (K := ℚ) (v := v)).exists_mem_open hopen
    ⟨u, by simp only [Set.mem_preimage, sub_self, zero_mul]; exact zero_mem _⟩
  have hru : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r - u) ≤ WithZero.exp (-(k : ℤ)) := by
    have h1 : Valued.v ((algebraMap ℚ (v.adicCompletion ℚ) r - u) * c) ≤ 1 := hr
    rw [map_mul, hc] at h1
    calc Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r - u)
        = Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r - u) * WithZero.exp (k : ℤ) *
            WithZero.exp (-(k : ℤ)) := by
          rw [mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (-(k : ℤ)) := by gcongr
      _ = _ := one_mul _
  have hr1 : v.valuation ℚ r ≤ 1 := by
    rw [← val_coe]
    have : algebraMap ℚ (v.adicCompletion ℚ) r = (algebraMap ℚ _ r - u) + u := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hru.trans (exp_neg_nat_le_one k)) hu)
  have hden : ((r.den : 𝓞 ℚ)) ∉ v.asIdeal := Rat.valuation_le_one_iff_den.mp hr1
  obtain ⟨c', a, ha, hca⟩ := Ideal.IsMaximal.exists_inv_pow v.asIdeal hden k
  refine ⟨(r.num : 𝓞 ℚ) * c', ?_⟩
  set A := algebraMap (𝓞 ℚ) ℚ
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hAca : A c' * r.den + A a = 1 := by
    have := congrArg A hca
    simpa [map_add, map_mul, map_natCast] using this
  have key : r - A ((r.num : 𝓞 ℚ) * c') = A ((r.num : 𝓞 ℚ) * a) / A (r.den : 𝓞 ℚ) := by
    rw [map_natCast, eq_div_iff hden0, map_mul, map_mul, map_intCast]
    have hA : A a = 1 - A c' * r.den := by linear_combination hAca
    rw [hA]
    have hr : r = r.num / r.den := (Rat.num_div_den r).symm
    rw [sub_mul]
    nth_rewrite 1 [hr]
    field_simp
  have hval : v.valuation ℚ (r - A ((r.num : 𝓞 ℚ) * c')) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [key, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
      (intValuation_eq_one_iff_mem_primeCompl _ _).mpr hden, div_one, map_mul]
    calc v.intValuation (r.num : 𝓞 ℚ) * v.intValuation a ≤ 1 * v.intValuation a := by
          gcongr; exact v.intValuation_le_one _
      _ = v.intValuation a := one_mul _
      _ ≤ _ := (intValuation_le_pow_iff_mem _ _ _).mpr ha
  have : algebraMap ℚ (v.adicCompletion ℚ) (A ((r.num : 𝓞 ℚ) * c')) - u =
      -(algebraMap ℚ (v.adicCompletion ℚ) (r - A ((r.num : 𝓞 ℚ) * c'))) +
        (algebraMap ℚ (v.adicCompletion ℚ) r - u) := by
    rw [map_sub]; ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ hru)
  rw [Valuation.map_neg, val_coe]
  exact hval

theorem algebraMap_intEquiv (y : 𝓞 ℚ) :
    ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) y : ℤ) : ℚ) = algebraMap (𝓞 ℚ) ℚ y := by
  rw [← map_intCast (algebraMap (𝓞 ℚ) ℚ), intCast_intEquiv]

/-- Simultaneous approximation of local integers by one integer. -/
theorem exists_approx_crt (S : Finset HS) (u : ∀ v : HS, v.adicCompletion ℚ)
    (hu : ∀ v ∈ S, Valued.v (u v) ≤ 1) (k : HS → ℕ) :
    ∃ b : ℤ, ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) - u v) ≤
      WithZero.exp (-(k v : ℤ)) := by
  classical
  choose a ha using fun v : S => exists_approx v.1 (u v.1) (hu v.1 v.2) (k v.1)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HS => v.asIdeal) k (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) a
  refine ⟨Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) y, fun v hv => ?_⟩
  have h1 := ha ⟨v, hv⟩
  have h2 := hy v hv
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := ℚ), ← val_coe] at h2
  rw [algebraMap_intEquiv]
  have : algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ y) - u v =
      algebraMap ℚ _ (algebraMap (𝓞 ℚ) ℚ (y - a ⟨v, hv⟩)) +
        (algebraMap ℚ _ (algebraMap (𝓞 ℚ) ℚ (a ⟨v, hv⟩)) - u v) := by
    simp only [map_sub]; ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le h2 h1)

/-! ### Local units from elements -/

open Classical in
/-- A unit of `ℚ_v` from an element, with the value `1` at zero. -/
noncomputable def loc (v : HS) (x : v.adicCompletion ℚ) : (v.adicCompletion ℚ)ˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

open Classical in
theorem coe_loc {v : HS} {x : v.adicCompletion ℚ} (h : x ≠ 0) :
    (loc v x : v.adicCompletion ℚ) = x := by
  simp [loc, h]

theorem loc_mul {v : HS} {x y : v.adicCompletion ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    loc v (x * y) = loc v x * loc v y :=
  Units.ext (by rw [Units.val_mul, coe_loc hx, coe_loc hy, coe_loc (mul_ne_zero hx hy)])

theorem ne_zero_of_val_eq_one {v : HS} {x : v.adicCompletion ℚ} (h : Valued.v x = 1) : x ≠ 0 := by
  rintro rfl; simp at h

/-! ### The norm of an idele -/

theorem ideleNorm_mul (a b : 𝕀) : ideleNorm ℚ (a * b) = ideleNorm ℚ a * ideleNorm ℚ b := by
  have hfa : Function.HasFiniteMulSupport (fun v => ‖(a : AdeleRing (𝓞 ℚ) ℚ).2 v‖) :=
    FiniteAdeleRing.hasFiniteMulSupport_norm
      (Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom a)
  have hfb : Function.HasFiniteMulSupport (fun v => ‖(b : AdeleRing (𝓞 ℚ) ℚ).2 v‖) :=
    FiniteAdeleRing.hasFiniteMulSupport_norm
      (Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom b)
  rw [ideleNorm, ideleNorm, ideleNorm, AdeleRing.norm_apply_of_isUnit (a * b).isUnit,
    AdeleRing.norm_apply_of_isUnit a.isUnit, AdeleRing.norm_apply_of_isUnit b.isUnit]
  have h1 : (∏ x, ‖((a * b : 𝕀) : AdeleRing (𝓞 ℚ) ℚ).1 x‖ ^ x.mult) =
      (∏ x, ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 x‖ ^ x.mult) *
        ∏ x, ‖(b : AdeleRing (𝓞 ℚ) ℚ).1 x‖ ^ x.mult := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => by rw [← mul_pow, ← norm_mul]; rfl
  have h2 : (∏ᶠ v, ‖((a * b : 𝕀) : AdeleRing (𝓞 ℚ) ℚ).2 v‖) =
      (∏ᶠ v, ‖(a : AdeleRing (𝓞 ℚ) ℚ).2 v‖) * ∏ᶠ v, ‖(b : AdeleRing (𝓞 ℚ) ℚ).2 v‖ := by
    rw [← finprod_mul_distrib hfa hfb]
    exact finprod_congr fun v => by rw [← norm_mul]; rfl
  rw [h1, h2]
  ring

theorem ideleNorm_unitEmbedding (q : ℚˣ) : ideleNorm ℚ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q) = 1 :=
  AdeleRing.norm_algebraMap_eq_one_of_ne_zero q.ne_zero

theorem ideleNorm_of_units (y : 𝕀) (hy : ∀ v, Valued.v (compFin v y : v.adicCompletion ℚ) = 1) :
    ideleNorm ℚ y = ‖(compInf y : (v₀).Completion)‖ := by
  rw [ideleNorm, AdeleRing.norm_apply_of_isUnit y.isUnit, Fintype.prod_subsingleton _ v₀,
    InfinitePlace.mult, ite_eq_left Rat.isReal_infinitePlace, pow_one]
  rw [show (∏ᶠ v, ‖(y : AdeleRing (𝓞 ℚ) ℚ).2 v‖) = ∏ᶠ _ : HS, (1 : ℝ) from
      finprod_congr fun v => (Valued.toNormedField.norm_eq_one_iff).mpr (hy v),
    finprod_one, mul_one]
  rfl

theorem norm_extensionEmbedding (z : (v₀).Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding v₀ z‖ = ‖z‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v₀).norm_map_of_map_zero (map_zero _) z


/-! ### The character on ideles -/

variable (χ : HeckeCharacter ℚ)

/-- The character `χ` as a function on ideles. -/
noncomputable def chiI : 𝕀 →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 ℚ) ℚ →* ℂˣ).comp (QuotientGroup.mk' _)

theorem chiI_apply (x : 𝕀) : chiI χ x = χ (x : IdeleClassGroup (𝓞 ℚ) ℚ) := rfl

theorem chiI_ofCompletion (y : (v₀).Completionˣ) :
    chiI χ (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ v₀ y) = χ.infiniteComponent v₀ y := rfl

theorem chiI_ofAdicCompletion (v : HS) (y : (v.adicCompletion ℚ)ˣ) :
    chiI χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v y) = χ.finiteComponent v y := rfl

theorem chiI_unitEmbedding (q : ℚˣ) : chiI χ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q) = 1 := by
  rw [chiI_apply, (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) _).mpr
    (MonoidHom.mem_range.mpr ⟨q, rfl⟩), map_one]

theorem chiI_inv (x : 𝕀) : chiI χ⁻¹ x = (chiI χ x)⁻¹ := rfl

/-- The character is trivial on the ideles with trivial infinite component, unit finite components, and finite components in `1 + p_v^{m_v}`. -/
def TrivOn (m : HS → ℕ) : Prop :=
  ∀ x : 𝕀, compInf x = 1 → (∀ v, Valued.v (compFin v x : v.adicCompletion ℚ) = 1) →
    (∀ v, Valued.v ((compFin v x : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m v : ℤ))) →
      chiI χ x = 1

theorem key {m : HS → ℕ} (hm : TrivOn χ m) (S : Finset HS) (hS : ∀ v ∉ S, m v = 0) (x : 𝕀)
    (hx : ∀ v, Valued.v (compFin v x : v.adicCompletion ℚ) = 1) :
    chiI χ x = χ.infiniteComponent v₀ (compInf x) *
      ∏ v ∈ S, χ.finiteComponent v (compFin v x) := by
  classical
  set A : 𝕀 := IdeleGroup.ofCompletion (𝓞 ℚ) ℚ v₀ (compInf x) with hA
  set P : 𝕀 := ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (compFin v x) with hP
  have hPinf : compInf P = 1 := by
    rw [hP, map_prod]
    exact Finset.prod_eq_one fun w _ => compInf_ofAdicCompletion w _
  have hPfin : ∀ v, compFin v P = if v ∈ S then compFin v x else 1 := by
    intro v
    rw [hP, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single v (fun w _ hw => compFin_ofAdicCompletion_of_ne hw _)
        (fun h => absurd hv h), compFin_ofAdicCompletion_self]
    · exact Finset.prod_eq_one fun w hw =>
        compFin_ofAdicCompletion_of_ne (ne_of_mem_of_not_mem hw hv) _
  set z : 𝕀 := x * A⁻¹ * P⁻¹ with hz
  have hz1 : compInf z = 1 := by
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, compInf_ofCompletion, hPinf]
    simp
  have hzfin : ∀ v, compFin v z = if v ∈ S then 1 else compFin v x := by
    intro v
    rw [hz, map_mul, map_mul, map_inv, map_inv, hA, compFin_ofCompletion, hPfin]
    split_ifs <;> simp
  have hz' : chiI χ z = 1 := by
    refine hm z hz1 (fun v => ?_) (fun v => ?_)
    · rw [hzfin]
      split_ifs
      · simp
      · exact hx v
    · rw [hzfin]
      split_ifs with hv
      · simp
      · rw [hS v hv, Nat.cast_zero, neg_zero, WithZero.exp_zero]
        exact val_sub_one_le_one (hx v).le
  have hxz : x = z * A * P := by
    rw [hz, mul_right_comm _ P⁻¹, inv_mul_cancel_right, inv_mul_cancel_right]
  conv_lhs => rw [hxz]
  rw [map_mul, map_mul, hz', one_mul, hA, chiI_ofCompletion, hP, map_prod]
  rfl

theorem trivOn_ofAdic {m : HS → ℕ} (hm : TrivOn χ m) (v : HS) :
    χ.IsTrivialOnHigherUnits v (m v) := by
  intro u hu hu1
  rw [← chiI_ofAdicCompletion]
  refine hm _ (compInf_ofAdicCompletion v u) (fun w => ?_) (fun w => ?_)
  · by_cases h : w = v
    · subst h; rw [compFin_ofAdicCompletion_self]; exact hu
    · rw [compFin_ofAdicCompletion_of_ne (Ne.symm h)]; simp
  · by_cases h : w = v
    · subst h; rw [compFin_ofAdicCompletion_self]; exact hu1
    · rw [compFin_ofAdicCompletion_of_ne (Ne.symm h)]; simp

theorem exists_trivOn : ∃ (m : HS → ℕ) (S : Finset HS), TrivOn χ m ∧ ∀ v ∉ S, m v = 0 := by
  classical
  obtain ⟨S, k, h⟩ := Langlands.HeckeRat.Top.exists_trivial_on_units ℚ χ
  refine ⟨fun v => if v ∈ S then k else 0, S, fun x hinf hfin hsub => ?_, fun v hv => ite_eq_right hv⟩
  refine h x ?_ hfin fun v hv => ?_
  · funext w
    obtain rfl := Subsingleton.elim w v₀
    exact congrArg Units.val hinf
  · simpa [hv] using hsub v

theorem isTrivial_mono {v : HS} {a b : ℕ} (hab : a ≤ b) (h : χ.IsTrivialOnHigherUnits v a) :
    χ.IsTrivialOnHigherUnits v b :=
  fun x hx hx1 => h x hx (hx1.trans (by rw [WithZero.exp_le_exp]; omega))

theorem isTrivial_cond (v : HS) : χ.IsTrivialOnHigherUnits v (χ.conductorExponent v) := by
  obtain ⟨m, S, hm, -⟩ := exists_trivOn χ
  exact Nat.sInf_mem (s := {a | χ.IsTrivialOnHigherUnits v a}) ⟨m v, trivOn_ofAdic χ hm v⟩

theorem cond_le_of_isTrivial {v : HS} {a : ℕ} (h : χ.IsTrivialOnHigherUnits v a) :
    χ.conductorExponent v ≤ a :=
  Nat.sInf_le h

theorem finite_ramified : {v : HS | χ.conductorExponent v ≠ 0}.Finite := by
  obtain ⟨m, S, hm, hS⟩ := exists_trivOn χ
  refine S.finite_toSet.subset fun v hv => ?_
  by_contra h
  exact hv (Nat.le_zero.mp ((cond_le_of_isTrivial χ (trivOn_ofAdic χ hm v)).trans (hS v h).le))

/-- The finite places where `χ` is ramified. -/
noncomputable def ram : Finset HS := (finite_ramified χ).toFinset

theorem mem_ram {v : HS} : v ∈ ram χ ↔ χ.conductorExponent v ≠ 0 := by
  simp [ram]

theorem isUnramifiedAt_iff (v : HS) : χ.IsUnramifiedAt v ↔ v ∉ ram χ := by
  rw [mem_ram, not_not]
  constructor
  · intro h; exact Nat.le_zero.mp (cond_le_of_isTrivial χ h)
  · intro h; have := isTrivial_cond χ v; rwa [h] at this

theorem trivOn_cond : TrivOn χ χ.conductorExponent := by
  obtain ⟨m, S, hm, hS⟩ := exists_trivOn χ
  intro x hinf hfin hsub
  rw [key χ hm S hS x hfin, hinf, map_one, one_mul]
  exact Finset.prod_eq_one fun v _ => isTrivial_cond χ v _ (hfin v) (hsub v)

theorem key_ram (x : 𝕀) (hx : ∀ v, Valued.v (compFin v x : v.adicCompletion ℚ) = 1) :
    chiI χ x = χ.infiniteComponent v₀ (compInf x) *
      ∏ v ∈ ram χ, χ.finiteComponent v (compFin v x) :=
  key χ (trivOn_cond χ) (ram χ) (fun v hv => by simpa [mem_ram] using hv) x hx

theorem ram_inv : ram χ⁻¹ = ram χ := by
  have h : ∀ v, (χ⁻¹).conductorExponent v = χ.conductorExponent v := by
    intro v
    have e : ∀ a, (χ⁻¹).IsTrivialOnHigherUnits v a ↔ χ.IsTrivialOnHigherUnits v a := by
      intro a
      refine forall_congr' fun x => imp_congr_right fun _ => imp_congr_right fun _ => ?_
      change (χ.finiteComponent v x)⁻¹ = 1 ↔ _
      exact inv_eq_one
    simp only [HeckeCharacter.conductorExponent, e]
  ext v
  simp [mem_ram, h]

theorem cond_inv (v : HS) : (χ⁻¹).conductorExponent v = χ.conductorExponent v := by
  have e : ∀ a, (χ⁻¹).IsTrivialOnHigherUnits v a ↔ χ.IsTrivialOnHigherUnits v a := by
    intro a
    refine forall_congr' fun x => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    change (χ.finiteComponent v x)⁻¹ = 1 ↔ _
    exact inv_eq_one
  simp only [HeckeCharacter.conductorExponent, e]

/-! ### Local components at integers -/

theorem finiteComponent_loc_congr {w : HS} {x y : w.adicCompletion ℚ} (hx : Valued.v x = 1)
    (hy : Valued.v y = 1)
    (hxy : Valued.v (y - x) ≤ WithZero.exp (-(χ.conductorExponent w : ℤ))) :
    χ.finiteComponent w (loc w y) = χ.finiteComponent w (loc w x) := by
  have hx0 := ne_zero_of_val_eq_one hx
  have hy0 := ne_zero_of_val_eq_one hy
  have hq0 : y / x ≠ 0 := div_ne_zero hy0 hx0
  have hyx : y = x * (y / x) := by field_simp
  rw [hyx, loc_mul hx0 hq0, map_mul]
  suffices h : χ.finiteComponent w (loc w (y / x)) = 1 by rw [h, mul_one]
  refine isTrivial_cond χ w _ ?_ ?_
  · rw [coe_loc hq0, map_div₀, hx, hy, div_one]
  · rw [coe_loc hq0, show y / x - 1 = (y - x) / x by field_simp, map_div₀, hx, div_one]
    exact hxy

/-- The product of the ramified local components at an element of `ℚ`. -/
noncomputable def H (q : ℚ) : ℂˣ :=
  ∏ v ∈ ram χ, χ.finiteComponent v (loc v (algebraMap ℚ (v.adicCompletion ℚ) q))

/-- The level of the Dirichlet character of `χ`. -/
noncomputable def level : ℕ := ∏ v ∈ ram χ, pr v ^ χ.conductorExponent v

theorem level_pos : 0 < level χ := Finset.prod_pos fun v _ => pow_pos (pr_prime v).pos _

theorem pow_dvd_level {v : HS} (hv : v ∈ ram χ) : pr v ^ χ.conductorExponent v ∣ level χ :=
  Finset.dvd_prod_of_mem _ hv

theorem pr_dvd_level {v : HS} (hv : v ∈ ram χ) : pr v ∣ level χ :=
  (dvd_pow_self _ ((mem_ram χ).mp hv)).trans (pow_dvd_level χ hv)

theorem level_inv : level χ⁻¹ = level χ := by
  simp only [level, ram_inv, cond_inv]

/-- An integer is prime to the level. -/
def Good (b : ℤ) : Prop := ∀ v ∈ ram χ, ¬ (pr v : ℤ) ∣ b

theorem val_of_good {b : ℤ} (hb : Good χ b) {v : HS} (hv : v ∈ ram χ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ)) = 1 :=
  (val_intCast_eq_one_iff v b).mpr (hb v hv)

theorem H_mul {b c : ℤ} (hb : Good χ b) (hc : Good χ c) :
    H χ ((b * c : ℤ) : ℚ) = H χ b * H χ c := by
  rw [H, H, H, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Int.cast_mul, map_mul, loc_mul (ne_zero_of_val_eq_one (val_of_good χ hb hv))
    (ne_zero_of_val_eq_one (val_of_good χ hc hv)), map_mul]

theorem H_congr {b b' : ℤ} (hb : Good χ b) (h : (level χ : ℤ) ∣ b' - b) :
    H χ b' = H χ b := by
  refine Finset.prod_congr rfl fun v hv => ?_
  have hd : ((pr v ^ χ.conductorExponent v : ℕ) : ℤ) ∣ b' - b :=
    (Int.natCast_dvd_natCast.mpr (pow_dvd_level χ hv)).trans h
  push_cast at hd
  have hb' : Good χ b' := by
    intro w hw hdw
    apply hb w hw
    have h2 : (pr w : ℤ) ∣ b' - b := (Int.natCast_dvd_natCast.mpr (pr_dvd_level χ hw)).trans h
    simpa using dvd_sub hdw h2
  exact finiteComponent_loc_congr χ (val_of_good χ hb hv) (val_of_good χ hb' hv)
    (by rw [← map_sub, ← Int.cast_sub]; exact (val_intCast_le_iff v _ _).mpr hd)

/-! ### The Dirichlet character of `χ` -/

instance : NeZero (level χ) := ⟨(level_pos χ).ne'⟩

theorem prime_dvd_level {p : ℕ} (hp : p.Prime) (h : p ∣ level χ) : ∃ v ∈ ram χ, p = pr v := by
  obtain ⟨v, hv, hpv⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  exact ⟨v, hv, (Nat.prime_dvd_prime_iff_eq hp (pr_prime v)).mp (hp.dvd_of_dvd_pow hpv)⟩

theorem good_iff_coprime (n : ℕ) : Good χ (n : ℤ) ↔ Nat.Coprime n (level χ) := by
  constructor
  · intro h
    refine Nat.coprime_of_dvd fun k hk hkn hkN => ?_
    obtain ⟨v, hv, rfl⟩ := prime_dvd_level χ hk hkN
    exact h v hv (Int.natCast_dvd_natCast.mpr hkn)
  · intro h v hv hd
    have h1 : pr v ∣ n := Int.natCast_dvd_natCast.mp hd
    have h2 : pr v ∣ Nat.gcd n (level χ) := Nat.dvd_gcd h1 (pr_dvd_level χ hv)
    rw [Nat.Coprime.gcd_eq_one h] at h2
    exact (pr_prime v).not_dvd_one h2

theorem good_congr {b b' : ℤ} (hb : Good χ b) (h : (level χ : ℤ) ∣ b' - b) : Good χ b' := by
  intro w hw hdw
  apply hb w hw
  have h2 : (pr w : ℤ) ∣ b' - b := (Int.natCast_dvd_natCast.mpr (pr_dvd_level χ hw)).trans h
  simpa using dvd_sub hdw h2

theorem good_one : Good χ 1 := fun v _ hd =>
  (pr_prime v).not_dvd_one (Int.natCast_dvd_natCast.mp (by exact_mod_cast hd))

theorem good_neg_one : Good χ (-1) := fun v hv hd => good_one χ v hv (by simpa using hd)

theorem good_mul {b c : ℤ} (hb : Good χ b) (hc : Good χ c) : Good χ (b * c) := fun v hv hd =>
  ((Nat.prime_iff_prime_int.mp (pr_prime v)).dvd_or_dvd hd).elim (hb v hv) (hc v hv)

theorem cast_val (x : ZMod (level χ)) : (((x.val : ℤ)) : ZMod (level χ)) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem dvd_val_sub (b : ℤ) : (level χ : ℤ) ∣ (((b : ZMod (level χ)).val : ℕ) : ℤ) - b :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (cast_val χ _).symm

theorem H_zmod (x : ZMod (level χ)) {b : ℤ} (hx : (b : ZMod (level χ)) = x) (hb : Good χ b) :
    H χ ((x.val : ℤ) : ℚ) = H χ b := by
  subst hx
  exact H_congr χ hb (dvd_val_sub χ b)

theorem good_zmod_val (x : ZMod (level χ)) {b : ℤ} (hx : (b : ZMod (level χ)) = x)
    (hb : Good χ b) : Good χ (x.val : ℤ) := by
  subst hx
  exact good_congr χ hb (dvd_val_sub χ b)

theorem good_unit (a : (ZMod (level χ))ˣ) : Good χ ((a : ZMod (level χ)).val : ℤ) :=
  (good_iff_coprime χ _).mpr (ZMod.val_coe_unit_coprime a)

theorem loc_one (v : HS) : loc v 1 = 1 := Units.ext (coe_loc one_ne_zero)

theorem H_one : H χ 1 = 1 := by
  refine Finset.prod_eq_one fun v _ => ?_
  rw [map_one, loc_one, map_one]

theorem H_inv (q : ℚ) : H χ⁻¹ q = (H χ q)⁻¹ := by
  rw [H, H, ram_inv, ← Finset.prod_inv_distrib]
  rfl

/-- The Dirichlet character of `χ`, as a map on units. The level `N` is a parameter, to compare the characters of `χ` and of `χ⁻¹`. -/
noncomputable def psiHom (N : ℕ) (hN : level χ = N) : (ZMod N)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun a => (H χ (((a : ZMod N).val : ℤ) : ℚ))⁻¹) (by
    subst hN
    intro a b
    show (H χ _)⁻¹ = (H χ _)⁻¹ * (H χ _)⁻¹
    rw [Units.val_mul, ← mul_inv, ← H_mul χ (good_unit χ a) (good_unit χ b)]
    congr 1
    exact H_zmod χ _ (by rw [Int.cast_mul, cast_val, cast_val])
      (good_mul χ (good_unit χ a) (good_unit χ b)))

/-- The Dirichlet character of `χ`. -/
noncomputable def psi (N : ℕ) (hN : level χ = N) : DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (psiHom χ N hN)

theorem psi_apply_unit (a : (ZMod (level χ))ˣ) :
    psi χ _ rfl (a : ZMod (level χ)) = (((H χ (((a : ZMod (level χ)).val : ℤ) : ℚ))⁻¹ : ℂˣ) : ℂ) := by
  rw [psi, MulChar.ofUnitHom_coe]
  rfl

theorem isUnit_of_good {b : ℤ} (hb : Good χ b) : IsUnit (b : ZMod (level χ)) := by
  rw [← cast_val χ (b : ZMod (level χ)), Int.cast_natCast, ZMod.isUnit_iff_coprime]
  exact (good_iff_coprime χ _).mp (good_zmod_val χ _ rfl hb)

theorem psi_apply_int {b : ℤ} (hb : Good χ b) :
    psi χ _ rfl (b : ZMod (level χ)) = (((H χ b)⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨u, hu⟩ := isUnit_of_good χ hb
  rw [← hu, psi_apply_unit, H_zmod χ _ hu.symm hb]

theorem psi_apply_nat {n : ℕ} (hn : Good χ (n : ℤ)) :
    psi χ _ rfl (n : ZMod (level χ)) = (((H χ n)⁻¹ : ℂˣ) : ℂ) := by
  have h := psi_apply_int χ hn
  rwa [Int.cast_natCast, Int.cast_natCast] at h

theorem psi_apply_nat_of_not_good {n : ℕ} (hn : ¬ Good χ (n : ℤ)) :
    psi χ _ rfl (n : ZMod (level χ)) = 0 :=
  MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime, ← good_iff_coprime])

theorem psi_inv (N : ℕ) (hN : level χ = N) (hN' : level χ⁻¹ = N) :
    psi χ⁻¹ N hN' = (psi χ N hN)⁻¹ := by
  ext a
  rw [MulChar.inv_apply_eq_inv', psi, psi, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
  simp only [psiHom, MonoidHom.mk'_apply, H_inv, inv_inv, Units.val_inv_eq_inv_val]

/-! ### The infinite component -/

theorem extensionEmbedding_algebraMap (q : ℚ) :
    InfinitePlace.Completion.extensionEmbedding v₀ (algebraMap ℚ (v₀).Completion q) = (q : ℂ) := by
  rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  exact eq_ratCast _ q

theorem infiniteComponent_rat {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) (q : ℚˣ) :
    (χ.infiniteComponent v₀ (compInf (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q)) : ℂ) =
      ((q : ℂ) / ((|(q : ℝ)| : ℝ) : ℂ)) ^ n * ((|(q : ℝ)| : ℝ) : ℂ) ^ t := by
  rw [h.eq, coe_compInf_unitEmbedding, extensionEmbedding_algebraMap, Complex.norm_ratCast,
    InfinitePlace.mult, ite_eq_left Rat.isReal_infinitePlace, Nat.cast_one, one_mul]

theorem compFin_unitEmbedding (v : HS) (q : ℚˣ) :
    compFin v (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q) = loc v (algebraMap ℚ (v.adicCompletion ℚ) q) :=
  Units.ext (by rw [coe_compFin_unitEmbedding, coe_loc ((map_ne_zero _).mpr q.ne_zero)])

theorem val_neg_one (v : HS) : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (-1 : ℚ)) = 1 := by
  rw [map_neg, map_one, Valuation.map_neg, Valuation.map_one]

theorem H_neg_one {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) :
    ((H χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ n := by
  have key := key_ram χ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (-1)) fun v => by
    rw [coe_compFin_unitEmbedding, Units.val_neg, Units.val_one]
    exact val_neg_one v
  rw [chiI_unitEmbedding] at key
  have hinf := infiniteComponent_rat χ h (-1)
  simp only [Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one, abs_neg, abs_one,
    Complex.ofReal_one, div_one, Complex.one_cpow, mul_one] at hinf
  have hH : ∏ v ∈ ram χ, χ.finiteComponent v (compFin v (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (-1))) =
      H χ (-1) := by
    rw [H]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [compFin_unitEmbedding, Units.val_neg, Units.val_one]
  rw [hH] at key
  have key' := congrArg (fun u : ℂˣ => (u : ℂ)) key
  simp only [Units.val_one, Units.val_mul, hinf] at key'
  have hsq : ((-1 : ℂ) ^ n) * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  calc ((H χ (-1) : ℂˣ) : ℂ) = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (H χ (-1) : ℂ) := by
        rw [hsq, one_mul]
    _ = (-1 : ℂ) ^ n := by rw [mul_assoc, ← key', mul_one]

theorem psi_neg_one {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) :
    psi χ _ rfl (-1) = (-1 : ℂ) ^ n := by
  have e := psi_apply_int χ (good_neg_one χ)
  simp only [Int.cast_neg, Int.cast_one] at e
  rw [e, Units.val_inv_eq_inv_val, H_neg_one χ h, ← inv_zpow, inv_neg, inv_one]

/-! ### The local factors and the Euler product -/

theorem asIdeal_eq_span (v : HS) : v.asIdeal = Ideal.span {((pr v : ℕ) : 𝓞 ℚ)} := by
  ext b
  rw [Ideal.mem_span_singleton]
  have h := intCast_mem_asIdeal_pow v (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) b) 1
  rw [pow_one, pow_one, intCast_intEquiv] at h
  rw [h, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]

theorem absNorm_asIdeal (v : HS) : Ideal.absNorm v.asIdeal = pr v := by
  rw [asIdeal_eq_span, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self,
    pow_one]

theorem good_pr {w : HS} (hw : w ∉ ram χ) : Good χ (pr w : ℤ) := by
  intro v hv hd
  have h := Int.natCast_dvd_natCast.mp hd
  rw [Nat.prime_dvd_prime_iff_eq (pr_prime v) (pr_prime w)] at h
  exact hw (by rw [← pr_injective h]; exact hv)

theorem not_good_pr {w : HS} (hw : w ∈ ram χ) : ¬ Good χ (pr w : ℤ) := fun h => h w hw dvd_rfl

theorem pr_ne_zero (w : HS) : (pr w : ℚ) ≠ 0 := by exact_mod_cast (pr_prime w).ne_zero

theorem finiteComponent_uniformizer {w : HS} (hw : w ∉ ram χ) :
    χ.finiteComponent w (localUniformizer ℚ w) =
      χ.finiteComponent w (loc w (algebraMap ℚ (w.adicCompletion ℚ) (pr w : ℚ))) := by
  set a := uniformizer ℚ w
  have ha : w.valuation ℚ a = WithZero.exp (-1) := (w.valuation_exists_uniformizer ℚ).choose_spec
  have hp0 := pr_ne_zero w
  have hA0 : algebraMap ℚ (w.adicCompletion ℚ) (pr w : ℚ) ≠ 0 := (map_ne_zero _).mpr hp0
  have hq0 : algebraMap ℚ (w.adicCompletion ℚ) (a / pr w) ≠ 0 :=
    (map_ne_zero _).mpr (div_ne_zero (uniformizer_ne_zero ℚ w) hp0)
  have hsplit : localUniformizer ℚ w = loc w (algebraMap ℚ (w.adicCompletion ℚ) (pr w : ℚ)) *
      loc w (algebraMap ℚ (w.adicCompletion ℚ) (a / pr w)) := by
    have hmul : (pr w : ℚ) * (a / pr w) = a := by field_simp
    rw [← loc_mul hA0 hq0, ← map_mul, hmul]
    exact Units.ext (coe_loc ((map_ne_zero (algebraMap ℚ (w.adicCompletion ℚ))).mpr
      (uniformizer_ne_zero ℚ w))).symm
  have hval : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (a / pr w)) = 1 := by
    rw [val_coe, map_div₀, ha, valuation_pr_self, div_self (by simp)]
  have h1 : χ.finiteComponent w (loc w (algebraMap ℚ (w.adicCompletion ℚ) (a / pr w))) = 1 := by
    refine (isUnramifiedAt_iff χ w).mpr hw _ ?_ ?_
    · rw [coe_loc hq0]; exact hval
    · rw [coe_loc hq0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact val_sub_one_le_one hval.le
  rw [hsplit, map_mul, h1, mul_one]

theorem finiteComponent_pr_mul {w : HS} (hw : w ∉ ram χ) :
    χ.finiteComponent w (loc w (algebraMap ℚ (w.adicCompletion ℚ) (pr w : ℚ))) *
      (χ.infiniteComponent v₀ (compInf (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
        (Units.mk0 (pr w : ℚ) (pr_ne_zero w)))) * H χ (pr w : ℚ)) = 1 := by
  obtain ⟨p, hp⟩ : ∃ p : ℚˣ, p = Units.mk0 (pr w : ℚ) (pr_ne_zero w) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = loc w (algebraMap ℚ (w.adicCompletion ℚ) (pr w : ℚ)) := ⟨_, rfl⟩
  have hpv : ∀ v, compFin v (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ p) =
      loc v (algebraMap ℚ (v.adicCompletion ℚ) (pr w : ℚ)) := fun v => by
    rw [compFin_unitEmbedding, hp, Units.val_mk0]
  have hpy : compFin w (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ p) = y := by rw [hpv, hy]
  rw [← hp, ← hy]
  set x : 𝕀 := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ p * (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w y)⁻¹
    with hx_def
  have hfin : ∀ v ≠ w, compFin v x = loc v (algebraMap ℚ (v.adicCompletion ℚ) (pr w : ℚ)) := by
    intro v hv
    rw [hx_def, map_mul, map_inv, compFin_ofAdicCompletion_of_ne (Ne.symm hv), inv_one, mul_one,
      hpv]
  have hx : ∀ v, Valued.v (compFin v x : v.adicCompletion ℚ) = 1 := by
    intro v
    by_cases hv : v = w
    · rw [hv, hx_def, map_mul, map_inv, compFin_ofAdicCompletion_self, hpy, mul_inv_cancel,
        Units.val_one, Valuation.map_one]
    · rw [hfin v hv, coe_loc ((map_ne_zero _).mpr (pr_ne_zero w)), val_coe,
        valuation_pr_of_ne (Ne.symm hv)]
  have key := key_ram χ x hx
  have hinf : compInf x = compInf (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ p) := by
    rw [hx_def, map_mul, map_inv, compInf_ofAdicCompletion, inv_one, mul_one]
  have hprod : ∏ v ∈ ram χ, χ.finiteComponent v (compFin v x) = H χ (pr w : ℚ) := by
    rw [H]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hfin v (ne_of_mem_of_not_mem hv hw)]
  have hl : chiI χ x = (χ.finiteComponent w y)⁻¹ := by
    rw [hx_def, map_mul, chiI_unitEmbedding, one_mul, map_inv, chiI_ofAdicCompletion]
  rw [hinf, hprod, hl] at key
  rw [← key, mul_inv_cancel]

theorem finiteComponent_localUniformizer {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t)
    {w : HS} (hw : w ∉ ram χ) :
    (χ.finiteComponent w (localUniformizer ℚ w) : ℂ) =
      psi χ _ rfl ((pr w : ℕ) : ZMod (level χ)) * ((pr w : ℕ) : ℂ) ^ (-t) := by
  have e := finiteComponent_pr_mul χ hw
  rw [← finiteComponent_uniformizer χ hw] at e
  have e' := congrArg (fun u : ℂˣ => (u : ℂ)) e
  simp only [Units.val_mul, Units.val_one] at e'
  rw [infiniteComponent_rat χ h] at e'
  have hp0 : ((pr w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pr_prime w).ne_zero
  simp only [Units.val_mk0, Rat.cast_natCast, Nat.abs_cast, Complex.ofReal_natCast,
    div_self hp0, one_zpow, one_mul] at e'
  rw [psi_apply_nat χ (good_pr χ hw), Units.val_inv_eq_inv_val, Complex.cpow_neg]
  have hH : ((H χ ((pr w : ℕ) : ℚ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have ht : ((pr w : ℕ) : ℂ) ^ t ≠ 0 := fun h0 => hp0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  field_simp
  linear_combination e'

variable {χ} in
theorem localFactor_eq {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) (w : HS) (s : ℂ) :
    χ.localFactor w s =
      (1 - psi χ _ rfl ((pr w : ℕ) : ZMod (level χ)) * ((pr w : ℕ) : ℂ) ^ (-(s + t)))⁻¹ := by
  by_cases hw : w ∈ ram χ
  · rw [HeckeCharacter.localFactor, ite_eq_right (fun h' => (isUnramifiedAt_iff χ w).mp h' hw),
      psi_apply_nat_of_not_good χ (not_good_pr χ hw), zero_mul, sub_zero, inv_one]
  · have hp0 : ((pr w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pr_prime w).ne_zero
    rw [HeckeCharacter.localFactor, ite_eq_left ((isUnramifiedAt_iff χ w).mpr hw),
      finiteComponent_localUniformizer χ h hw, absNorm_asIdeal, mul_assoc,
      ← Complex.cpow_add _ _ hp0, show -t + -s = -(s + t) by ring]

variable {χ} in
theorem finiteLFunction_eq {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) {s : ℂ}
    (hs : 1 < (s + t).re) :
    χ.finiteLFunction s = LSeries (fun k => psi χ _ rfl (k : ZMod (level χ))) (s + t) := by
  rw [HeckeCharacter.finiteLFunction,
    ← DirichletCharacter.LSeries_eulerProduct_tprod (psi χ _ rfl) hs,
    ← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tprod_eq]
  exact tprod_congr fun w => localFactor_eq h w s

variable {χ} in
theorem gammaFactor_eq {n : InfinitePlace ℚ → ℤ} {t : InfinitePlace ℚ → ℂ}
    (h : χ.IsArchimedeanParameter v₀ (n v₀) (t v₀)) (s : ℂ) :
    Langlands.gammaFactor ℚ n t s = DirichletCharacter.gammaFactor (psi χ _ rfl) (s + t v₀) := by
  rw [Langlands.gammaFactor, Fintype.prod_subsingleton _ v₀, ite_eq_left Rat.isReal_infinitePlace]
  have hpar := psi_neg_one χ h
  rcases h.isReal Rat.isReal_infinitePlace with h0 | h1
  · rw [h0, zpow_zero] at hpar
    rw [DirichletCharacter.gammaFactor, ite_eq_left (show (psi χ _ rfl).Even from hpar), h0, Int.cast_zero,
      add_zero]
  · rw [h1, zpow_one] at hpar
    have hne : ¬ (psi χ _ rfl).Even := by
      intro he
      have := he.symm.trans hpar
      norm_num at this
    rw [DirichletCharacter.gammaFactor, ite_eq_right hne, h1, Int.cast_one]


/-! ### The norm of `χ` -/

theorem exp_neg_lt_one {c : ℕ} (hc : c ≠ 0) : WithZero.exp (-(c : ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exists_good_H {w : HS} (hw : w ∈ ram χ) (u : (w.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : w.adicCompletion ℚ) = 1) :
    ∃ b : ℤ, Good χ b ∧ H χ b = χ.finiteComponent w u ∧
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (b : ℚ) - u) ≤
        WithZero.exp (-(χ.conductorExponent w : ℤ)) ∧
      ∀ v ∈ ram χ, v ≠ w → Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) - 1) ≤
        WithZero.exp (-(χ.conductorExponent v : ℤ)) := by
  classical
  let U : ∀ v : HS, v.adicCompletion ℚ :=
    Function.update (fun v => (1 : v.adicCompletion ℚ)) w (u : w.adicCompletion ℚ)
  have hUw : U w = u := Function.update_self _ _ _
  have hUv : ∀ v, v ≠ w → U v = 1 := fun v h => Function.update_of_ne h _ _
  have hU1 : ∀ v, Valued.v (U v) = 1 := by
    intro v
    by_cases h : v = w
    · rw [h, hUw]; exact hu
    · rw [hUv v h, Valuation.map_one]
  obtain ⟨b, hb⟩ := exists_approx_crt (ram χ) U (fun v _ => (hU1 v).le) χ.conductorExponent
  have hbv : ∀ v ∈ ram χ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ)) = 1 := by
    intro v hv
    refine (Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt (hb v hv) ?_)).trans (hU1 v)
    rw [hU1 v]
    exact exp_neg_lt_one ((mem_ram χ).mp hv)
  have hgood : Good χ b := fun v hv => (val_intCast_eq_one_iff v b).mp (hbv v hv)
  have hbw := hb w hw
  rw [hUw] at hbw
  refine ⟨b, hgood, ?_, hbw, fun v hv hvw => ?_⟩
  · rw [H, Finset.prod_eq_single_of_mem w hw (fun v hv hvw => ?_)]
    · rw [finiteComponent_loc_congr χ hu (hbv w hw) hbw]
      congr 1
      exact Units.ext (coe_loc (Units.ne_zero u))
    · have h1 := hb v hv
      rw [hUv v hvw] at h1
      rw [finiteComponent_loc_congr χ (Valuation.map_one _) (hbv v hv) h1, loc_one, map_one]
  · have h1 := hb v hv
    rwa [hUv v hvw] at h1

theorem norm_finiteComponent_unit (w : HS) (u : (w.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : w.adicCompletion ℚ) = 1) : ‖(χ.finiteComponent w u : ℂ)‖ = 1 := by
  by_cases hw : w ∈ ram χ
  · obtain ⟨b, hb, hH, -, -⟩ := exists_good_H χ hw u hu
    obtain ⟨a, ha⟩ := isUnit_of_good χ hb
    have h1 := DirichletCharacter.unit_norm_eq_one (psi χ _ rfl) a
    rw [ha, psi_apply_int χ hb, hH, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at h1
    exact h1
  · rw [(isUnramifiedAt_iff χ w).mpr hw u hu (by
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact val_sub_one_le_one hu.le),
      Units.val_one, norm_one]

theorem norm_infiniteComponent {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t)
    (z : (v₀).Completionˣ) :
    ‖(χ.infiniteComponent v₀ z : ℂ)‖ = ‖(z : (v₀).Completion)‖ ^ t.re := by
  have hz : InfinitePlace.Completion.extensionEmbedding v₀ (z : (v₀).Completion) ≠ 0 :=
    (map_ne_zero (InfinitePlace.Completion.extensionEmbedding v₀)).mpr z.ne_zero
  have hpos := norm_pos_iff.mpr hz
  rw [h.eq, InfinitePlace.mult, ite_eq_left Rat.isReal_infinitePlace, Nat.cast_one, one_mul, norm_mul,
    norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self hpos.ne', one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos, norm_extensionEmbedding]

open Classical in
theorem val_prod_pr_zpow (T : Finset HS) (e : HS → ℤ) (v : HS) :
    v.valuation ℚ (∏ w ∈ T, (pr w : ℚ) ^ (-(e w))) = if v ∈ T then WithZero.exp (e v) else 1 := by
  rw [map_prod]
  split_ifs with hv
  · rw [Finset.prod_eq_single_of_mem v hv (fun w _ hw => by
      rw [map_zpow₀, valuation_pr_of_ne hw, one_zpow]), map_zpow₀, valuation_pr_self,
      ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  · exact Finset.prod_eq_one fun w hw => by
      rw [map_zpow₀, valuation_pr_of_ne (ne_of_mem_of_not_mem hw hv), one_zpow]

theorem exists_rat_val (x : 𝕀) : ∃ q : ℚˣ, ∀ v : HS,
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ)) =
      Valued.v (compFin v x : v.adicCompletion ℚ) := by
  classical
  have hfin : Function.HasFiniteMulSupport (fun v => ‖(x : AdeleRing (𝓞 ℚ) ℚ).2 v‖) :=
    FiniteAdeleRing.hasFiniteMulSupport_norm
      (Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom x)
  have hT : (Function.mulSupport (fun v => ‖(x : AdeleRing (𝓞 ℚ) ℚ).2 v‖)).Finite := hfin
  let e : HS → ℤ := fun v => WithZero.log (Valued.v (compFin v x : v.adicCompletion ℚ))
  have hq0 : ∏ w ∈ hT.toFinset, (pr w : ℚ) ^ (-(e w)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => zpow_ne_zero _ (pr_ne_zero w)
  refine ⟨Units.mk0 _ hq0, fun v => ?_⟩
  rw [Units.val_mk0, val_coe, val_prod_pr_zpow]
  have hne : Valued.v (compFin v x : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  split_ifs with hv
  · exact WithZero.exp_log hne
  · have h1 : ‖(x : AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1 := by
      by_contra h
      exact hv (hT.mem_toFinset.mpr h)
    exact ((Valued.toNormedField.norm_eq_one_iff).mp h1).symm

theorem exists_unit_decomp (x : 𝕀) : ∃ q : ℚˣ, ∀ v : HS,
    Valued.v (compFin v ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q)⁻¹ * x) : v.adicCompletion ℚ) = 1 := by
  obtain ⟨q, hq⟩ := exists_rat_val x
  refine ⟨q, fun v => ?_⟩
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, coe_compFin_unitEmbedding,
    Valuation.map_mul, map_inv₀, hq]
  exact inv_mul_cancel₀ ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))

theorem chiI_decomp (q : ℚˣ) (x : 𝕀) :
    chiI χ ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q)⁻¹ * x) = chiI χ x := by
  rw [map_mul, map_inv, chiI_unitEmbedding, inv_one, one_mul]

theorem ideleNorm_decomp (q : ℚˣ) (x : 𝕀) :
    ideleNorm ℚ ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q)⁻¹ * x) = ideleNorm ℚ x := by
  rw [ideleNorm_mul, ← map_inv, ideleNorm_unitEmbedding, one_mul]

theorem norm_chi {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) (x : 𝕀) :
    ‖((χ (x : IdeleClassGroup (𝓞 ℚ) ℚ) : ℂˣ) : ℂ)‖ = ideleNorm ℚ x ^ t.re := by
  obtain ⟨q, hq⟩ := exists_unit_decomp x
  set y := (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q)⁻¹ * x
  have hprod : ∏ v ∈ ram χ, ‖((χ.finiteComponent v (compFin v y) : ℂˣ) : ℂ)‖ = 1 :=
    Finset.prod_eq_one fun v _ => norm_finiteComponent_unit χ v _ (hq v)
  rw [← chiI_apply, ← chiI_decomp χ q x, ← ideleNorm_decomp q x, ideleNorm_of_units _ hq,
    key_ram χ _ hq, Units.val_mul, Units.coe_prod, norm_mul, norm_prod, hprod, mul_one,
    norm_infiniteComponent χ h]

/-! ### The Dirichlet character is primitive -/

theorem level_dvd {z : ℤ} (h : ∀ v ∈ ram χ, (pr v : ℤ) ^ χ.conductorExponent v ∣ z) :
    (level χ : ℤ) ∣ z := by
  rw [level, Nat.cast_prod]
  simp only [Nat.cast_pow]
  refine Finset.prod_dvd_of_coprime (fun v _ w _ hvw => ?_) h
  exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (pr_prime v) (pr_prime w)).mpr
    fun e => hvw (pr_injective e))).pow

theorem isCoprime_of_good {b : ℤ} (hb : Good χ b) : IsCoprime b (level χ : ℤ) := by
  have h : Nat.Coprime b.natAbs (level χ) := Nat.coprime_of_dvd fun k hk hkb hkN => by
    obtain ⟨v, hv, rfl⟩ := prime_dvd_level χ hk hkN
    exact hb v hv (Int.natCast_dvd.mpr hkb)
  exact Int.isCoprime_iff_nat_coprime.mpr (by rwa [Int.natAbs_natCast])

theorem val_sub_one_iff (v : HS) (b : ℤ) (k : ℕ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) ↔
      (pr v : ℤ) ^ k ∣ b - 1 := by
  have e : algebraMap ℚ (v.adicCompletion ℚ) ((b - 1 : ℤ) : ℚ) =
      algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) - 1 := by
    rw [Int.cast_sub, Int.cast_one, map_sub, map_one]
  rw [← e, val_intCast_le_iff]

theorem psi_isPrimitive_rfl : (psi χ _ rfl).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  obtain ⟨m, hm⟩ := (psi χ _ rfl).conductor_dvd_level
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hne hm.symm
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hpN : p ∣ level χ := (dvd_mul_of_dvd_right hpm _).trans (dvd_of_eq hm.symm)
  have hdp : (psi χ _ rfl).conductor * p ∣ level χ :=
    (mul_dvd_mul_left _ hpm).trans (dvd_of_eq hm.symm)
  obtain ⟨w, hw, rfl⟩ := prime_dvd_level χ hp hpN
  have hc : χ.conductorExponent w ≠ 0 := (mem_ram χ).mp hw
  have hnt : ¬ χ.IsTrivialOnHigherUnits w (χ.conductorExponent w - 1) := fun h' => by
    have := cond_le_of_isTrivial χ h'
    omega
  unfold HeckeCharacter.IsTrivialOnHigherUnits at hnt
  push Not at hnt
  obtain ⟨u, hu, hu1, hχu⟩ := hnt
  obtain ⟨b, hb, hH, hbw, hbv⟩ := exists_good_H χ hw u hu
  have hdiv : (level χ : ℤ) ∣ (pr w : ℤ) * (b - 1) := by
    refine level_dvd χ fun v hv => ?_
    by_cases hvw : v = w
    · rw [hvw]
      have h1 : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (b : ℚ) - 1) ≤
          WithZero.exp (-((χ.conductorExponent w - 1 : ℕ) : ℤ)) := by
        have e : algebraMap ℚ (w.adicCompletion ℚ) (b : ℚ) - 1 =
            (algebraMap ℚ (w.adicCompletion ℚ) (b : ℚ) - u) + ((u : w.adicCompletion ℚ) - 1) := by
          ring
        rw [e]
        refine (Valuation.map_add _ _ _).trans (max_le (hbw.trans ?_) hu1)
        rw [WithZero.exp_le_exp]
        omega
      have h2 := (val_sub_one_iff w b _).mp h1
      obtain ⟨k, hk⟩ : ∃ k, χ.conductorExponent w = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_ne_zero hc).symm⟩
      rw [hk, Nat.add_sub_cancel] at h2
      rw [hk, pow_succ']
      exact mul_dvd_mul_left _ h2
    · exact Dvd.dvd.mul_left ((val_sub_one_iff v b _).mp (hbv v hv hvw)) _
  have hd : ((psi χ _ rfl).conductor : ℤ) ∣ b - 1 := by
    have h1 : (((psi χ _ rfl).conductor * pr w : ℕ) : ℤ) ∣ (level χ : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdp
    have h2 := h1.trans hdiv
    push_cast at h2
    rw [mul_comm ((psi χ _ rfl).conductor : ℤ)] at h2
    exact (mul_dvd_mul_iff_left (by exact_mod_cast (pr_prime w).ne_zero)).mp h2
  have hψb : psi χ _ rfl (b : ZMod (level χ)) = 1 := by
    rw [← DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := psi χ _ rfl)
      (isCoprime_of_good χ hb)]
    have h1 := ((ZMod.intCast_eq_intCast_iff_dvd_sub 1 b _).mpr hd).symm
    rw [Int.cast_one] at h1
    rw [h1, map_one]
  rw [psi_apply_int χ hb, hH] at hψb
  exact hχu (inv_eq_one.mp (Units.val_eq_one.mp hψb))

theorem psi_isPrimitive (N : ℕ) (hN : level χ = N) : (psi χ N hN).IsPrimitive := by
  subst hN
  exact psi_isPrimitive_rfl χ

/-! ### The conductor -/

theorem absNorm_conductor : Ideal.absNorm χ.conductor = level χ := by
  rw [HeckeCharacter.conductor, finprod_eq_prod_of_mulSupport_subset _ (s := ram χ) ?_, map_prod]
  · exact Finset.prod_congr rfl fun v _ => by rw [map_pow, absNorm_asIdeal]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, mem_ram]
    intro h0
    apply hv
    rw [h0, pow_zero]

/-! ### The case of level one -/

theorem ram_eq_empty (h1 : level χ = 1) : ram χ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv =>
    (pr_prime v).not_dvd_one (h1 ▸ pr_dvd_level χ hv)

theorem n_eq_zero_of_level_one {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t)
    (h1 : level χ = 1) : n = 0 := by
  have hsub : Subsingleton (ZMod (level χ)) := ZMod.subsingleton_iff.mpr h1
  have e := psi_neg_one χ h
  rw [Subsingleton.elim (-1 : ZMod (level χ)) 1, map_one] at e
  rcases h.isReal Rat.isReal_infinitePlace with h0 | h0
  · exact h0
  · rw [h0, zpow_one] at e
    norm_num at e

theorem chi_eq_norm_cpow {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t)
    (h1 : level χ = 1) (x : 𝕀) :
    ((χ (x : IdeleClassGroup (𝓞 ℚ) ℚ) : ℂˣ) : ℂ) = (ideleNorm ℚ x : ℂ) ^ t := by
  obtain ⟨q, hq⟩ := exists_unit_decomp x
  have hn := n_eq_zero_of_level_one χ h h1
  rw [← chiI_apply, ← chiI_decomp χ q x, ← ideleNorm_decomp q x, ideleNorm_of_units _ hq,
    key_ram χ _ hq, ram_eq_empty χ h1, Finset.prod_empty, mul_one, h.eq, hn, zpow_zero, one_mul,
    InfinitePlace.mult, ite_eq_left Rat.isReal_infinitePlace, Nat.cast_one, one_mul,
    norm_extensionEmbedding]

/-! ### The parameter of `χ⁻¹` -/

theorem exists_completion_exp (a : ℝ) : ∃ z : (v₀).Completionˣ,
    InfinitePlace.Completion.extensionEmbedding v₀ (z : (v₀).Completion) = (Real.exp a : ℂ) := by
  obtain ⟨z0, hz0⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace (Real.exp a)
  have h1 : InfinitePlace.Completion.extensionEmbedding v₀ z0 = (Real.exp a : ℂ) := by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply Rat.isReal_infinitePlace, hz0]
  have h0 : z0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at h1
    exact (Real.exp_pos a).ne' (by exact_mod_cast h1.symm)
  exact ⟨Units.mk0 z0 h0, h1⟩

theorem infiniteComponent_of_exp {n : ℤ} {t : ℂ} (h : χ.IsArchimedeanParameter v₀ n t) (a : ℝ)
    (z : (v₀).Completionˣ)
    (hz : InfinitePlace.Completion.extensionEmbedding v₀ (z : (v₀).Completion) = (Real.exp a : ℂ)) :
    (χ.infiniteComponent v₀ z : ℂ) = Complex.exp (a * t) := by
  have he : ((Real.exp a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos a).ne'
  rw [h.eq, hz, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos a).le, div_self he, one_zpow,
    one_mul, InfinitePlace.mult, ite_eq_left Rat.isReal_infinitePlace, Nat.cast_one, one_mul,
    Complex.cpow_def_of_ne_zero he, ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp]

variable {χ} in
theorem t_inv {n n' : ℤ} {t t' : ℂ} (h : χ.IsArchimedeanParameter v₀ n t)
    (h' : χ⁻¹.IsArchimedeanParameter v₀ n' t') : t' = -t := by
  have hexp : ∀ a : ℝ, Complex.exp (a * (t + t')) = 1 := by
    intro a
    obtain ⟨z, hz⟩ := exists_completion_exp a
    have e1 := infiniteComponent_of_exp χ h a z hz
    have e2 := infiniteComponent_of_exp χ⁻¹ h' a z hz
    have e3 : (χ⁻¹.infiniteComponent v₀ z : ℂ) = (χ.infiniteComponent v₀ z : ℂ)⁻¹ := by
      rw [← Units.val_inv_eq_inv_val]
      rfl
    rw [mul_add, Complex.exp_add, ← e1, ← e2, e3, mul_inv_cancel₀ (Units.ne_zero _)]
  suffices hu : t + t' = 0 by linear_combination hu
  by_contra hu
  have ha : (0 : ℝ) < 1 / (‖t + t'‖ + 1) := by positivity
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (hexp (1 / (‖t + t'‖ + 1)))
  have hnorm : ‖((1 / (‖t + t'‖ + 1) : ℝ) : ℂ) * (t + t')‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le, div_mul_eq_mul_div, one_mul,
      div_lt_one (by positivity)]
    linarith
  by_cases hk0 : k = 0
  · rw [hk0, Int.cast_zero, zero_mul] at hk
    rcases mul_eq_zero.mp hk with h0 | h0
    · exact ha.ne' (by exact_mod_cast h0)
    · exact hu h0
  · have h2 : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat, mul_one]
    have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [hk, h2] at hnorm
    nlinarith [Real.pi_gt_three]

/-! ### The completed L-function -/

theorem completed_eq {n : InfinitePlace ℚ → ℤ} {t : InfinitePlace ℚ → ℂ}
    (h : χ.IsArchimedeanParameter v₀ (n v₀) (t v₀)) (N : ℕ) (hN : level χ = N) [NeZero N]
    {s : ℂ} (hs : 1 < (s + t v₀).re) :
    χ.completedLFunction n t s =
      DirichletCharacter.completedLFunction (psi χ N hN) (s + t v₀) := by
  subst hN
  rw [HeckeCharacter.completedLFunction, gammaFactor_eq h, finiteLFunction_eq h hs,
    Langlands.HeckeRat.Analytic.completedLFunction_eq_mul_LSeries _ hs]

end Langlands.HeckeRat

namespace Langlands

/-- Hecke's theorem for the field `ℚ`. -/
theorem heckeFunctionalEquationAt_rat : HeckeFunctionalEquationAt ℚ := by
  intro χ n n' t t' h h'
  have h0 := h Rat.infinitePlace
  have h0' := h' Rat.infinitePlace
  have ht : t' Rat.infinitePlace = -t Rat.infinitePlace := HeckeRat.t_inv h0 h0'
  obtain ⟨N, hN⟩ : ∃ N, HeckeRat.level χ = N := ⟨_, rfl⟩
  have hN' : HeckeRat.level χ⁻¹ = N := (HeckeRat.level_inv χ).trans hN
  have : NeZero N := ⟨by rw [← hN]; exact (HeckeRat.level_pos χ).ne'⟩
  have hprim := HeckeRat.psi_isPrimitive χ N hN
  have hinv : HeckeRat.psi χ⁻¹ N hN' = (HeckeRat.psi χ N hN)⁻¹ := HeckeRat.psi_inv χ N hN hN'
  refine ⟨(t Rat.infinitePlace).re, fun x => HeckeRat.norm_chi χ h0 x,
    fun s => DirichletCharacter.completedLFunction (HeckeRat.psi χ N hN) (s + t Rat.infinitePlace),
    fun s => DirichletCharacter.completedLFunction (HeckeRat.psi χ N hN)⁻¹
      (s + t' Rat.infinitePlace),
    DirichletCharacter.rootNumber (HeckeRat.psi χ N hN) *
      (N : ℂ) ^ (((t Rat.infinitePlace).re : ℂ) - t Rat.infinitePlace),
    Langlands.HeckeRat.Analytic.meromorphicOn_completedLFunction_shift _ _,
    Langlands.HeckeRat.Analytic.meromorphicOn_completedLFunction_shift _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    beta_reduce
    rw [HeckeRat.completed_eq χ h0 N hN (by rw [Complex.add_re]; linarith)]
  · intro s hs
    beta_reduce
    rw [HeckeRat.completed_eq χ⁻¹ h0' N hN'
      (by rw [Complex.add_re, ht, Complex.neg_re]; linarith), hinv]
  · rw [norm_mul, Langlands.HeckeRat.Analytic.norm_rootNumber hprim, one_mul,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_neZero N)]
    simp
  · intro s
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have e := hprim.completedLFunction_one_sub (1 - (s + t Rat.infinitePlace))
    rw [sub_sub_cancel] at e
    beta_reduce
    rw [discr_rat, HeckeRat.absNorm_conductor, hN, e, ht,
      show 1 - (s + t Rat.infinitePlace) - 1 / 2 = (1 / 2 - s - ((t Rat.infinitePlace).re : ℂ)) +
        (((t Rat.infinitePlace).re : ℂ) - t Rat.infinitePlace) by ring,
      Complex.cpow_add _ _ hN0,
      show 1 - s + -t Rat.infinitePlace = 1 - (s + t Rat.infinitePlace) by ring]
    simp only [abs_one, Int.cast_one, one_mul]
    ring
  · by_cases hN1 : N = 1
    · subst hN1
      right
      refine ⟨t Rat.infinitePlace, fun x => HeckeRat.chi_eq_norm_cpow χ h0 hN x, ?_, ?_, ?_⟩
      · intro s hs0 hs1
        rw [DirichletCharacter.completedLFunction_modOne_eq]
        exact Langlands.HeckeRat.Analytic.analyticAt_completedRiemannZeta_shift _ _ hs0 hs1
      · rw [DirichletCharacter.completedLFunction_modOne_eq]
        exact Langlands.HeckeRat.Analytic.meromorphicOrderAt_completedRiemannZeta_shift_zero _
      · rw [DirichletCharacter.completedLFunction_modOne_eq]
        exact Langlands.HeckeRat.Analytic.meromorphicOrderAt_completedRiemannZeta_shift_one _
    · left
      have hψ1 : HeckeRat.psi χ N hN ≠ 1 := by
        intro e
        have := (DirichletCharacter.isPrimitive_def _).mp hprim
        rw [e, DirichletCharacter.conductor_one] at this
        exact hN1 this.symm
      exact fun s => Langlands.HeckeRat.Analytic.analyticAt_completedLFunction_shift hψ1 _ s

end Langlands
