/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.DedekindFE
import Langlands.Tate.HeckeOne
import Langlands.Tate.QuadraticDedekind
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Euler product of the Dedekind zeta function

Let $K$ be a number field. This file proves the Euler product $$\zeta_K(s) = \prod_{\mathfrak{p}} (1 - N(\mathfrak{p})^{-s})^{-1}$$ for $\mathrm{Re}\, s > 1$, where the product is over the nonzero prime ideals of $\mathcal{O}_K$ and $\zeta_K$ is Mathlib's `NumberField.dedekindZeta`. Thus the finite $L$-function of the trivial Hecke character is the Dedekind zeta function.

The proof follows the proof for $\zeta(s)$. For a finite set $S$ of primes, the nonzero ideals with all prime factors in $S$ are the products $\prod_{\mathfrak{p} \in S} \mathfrak{p}^{e_\mathfrak{p}}$, with unique exponents. Thus the sum of $N(I)^{-s}$ over these ideals is the finite product of the geometric series $\sum_e N(\mathfrak{p})^{-es}$. The proof adds one prime at a time. When $S$ becomes large, each ideal has its prime factors in $S$, and the dominated convergence theorem for series (Tannery's theorem) gives the limit.

## Main results

* `Langlands.Tate.summable_absNorm_rpow`: the series $\sum_{I \neq 0} N(I)^{-\sigma}$ converges for $\sigma > 1$.
* `Langlands.Tate.hasSum_supportedIn`: the sum over the ideals with prime factors in a finite set $S$.
* `Langlands.Tate.hasProd_dedekindZeta`: the Euler product of $\zeta_K$.
* `Langlands.Tate.finiteLFunction_one`: the finite $L$-function of the trivial Hecke character is $\zeta_K$.
-/

namespace Langlands.Tate

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units IsDedekindDomain

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

section Summable

variable (K) in
/-- For $\sigma > 1$, the series $\sum_{I \neq 0} N(I)^{-\sigma}$ converges. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ)) := by
  have hu : 1 < (σ : ℂ).re := by simpa using hσ
  have hs : HasSum (fun I : (Ideal (𝓞 K))⁰ => xiTerm (σ : ℂ) I)
      (∑ C : ClassGroup (𝓞 K), classXi (classRepUnit K C) σ) := by
    have h := hasSum_sum (s := Finset.univ) fun C _ => hasSum_classXi (classRepUnit K C) hu
    convert h using 1
    funext I
    rw [Finset.sum_eq_single (ClassGroup.mk0 I)⁻¹ (fun C _ hC => ite_eq_right (fun h =>
      hC (by rw [mk_classRepUnit] at h; rw [h, inv_inv]))) (fun h => absurd (Finset.mem_univ _) h),
      mk_classRepUnit, inv_inv, ite_eq_left rfl]
  have hw : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (σ : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  have hΓ : gammaK K σ ≠ 0 := gammaK_ne_zero (by simp; linarith)
  have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
  have hc : (torsionOrder K : ℂ) * (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ (σ : ℂ) * gammaK K σ) /
      ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero hw (mul_ne_zero hA hΓ)) hC
  have h2 : Summable (fun I : (Ideal (𝓞 K))⁰ =>
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-(σ : ℂ))) := by
    refine (summable_mul_left_iff hc).1 (hs.summable.congr fun I => ?_)
    rw [xiTerm]
    ring
  refine Complex.summable_ofReal.1 (h2.congr fun I => ?_)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg]

/-- The norm of $N(I)^{-s}$ is $N(I)^{-\mathrm{Re}\, s}$. -/
theorem norm_absNorm_cpow (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖ =
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I), Complex.neg_re]

variable (K) in
/-- For $\mathrm{Re}\, s > 1$, the series $\sum_{I \neq 0} N(I)^{-s}$ converges absolutely. -/
theorem summable_norm_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖) :=
  (summable_absNorm_rpow K hs).congr fun I => (norm_absNorm_cpow I s).symm

end Summable

open scoped Classical

section Finite

variable (K) in
/-- The map $I \mapsto N(I)^{-s}$, as a homomorphism of monoids. -/
noncomputable def normCpow (s : ℂ) : Ideal (𝓞 K) →* ℂ where
  toFun I := (Ideal.absNorm I : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

@[simp]
theorem normCpow_apply (s : ℂ) (I : Ideal (𝓞 K)) :
    normCpow K s I = (Ideal.absNorm I : ℂ) ^ (-s) :=
  rfl

/-- For a prime $\mathfrak{p}$ and $\mathrm{Re}\, s > 0$, $|N(\mathfrak{p})^{-s}| < 1$. -/
theorem norm_normCpow_lt_one (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    ‖normCpow K s v.asIdeal‖ < 1 := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  rw [normCpow_apply, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h0), Complex.neg_re]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
  exact_mod_cast lt_of_le_of_ne (Nat.one_le_iff_ne_zero.2 h0) (Ne.symm h1)

variable (K) in
/-- The nonzero ideals with all prime factors in a finite set $S$ of primes. -/
def supportedIn (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Ideal (𝓞 K))⁰ :=
  {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (I : Ideal (𝓞 K)) → v ∈ S}

/-- If a prime $\mathfrak{q}$ divides a prime $\mathfrak{p}$, then $\mathfrak{q} = \mathfrak{p}$. -/
theorem eq_of_asIdeal_dvd {v w : HeightOneSpectrum (𝓞 K)} (h : w.asIdeal ∣ v.asIdeal) : w = v :=
  HeightOneSpectrum.asIdeal_injective
    (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.dvd_iff_le.1 h)).symm

/-- The only nonzero ideal with no prime factor is $(1)$. -/
theorem supportedIn_empty : supportedIn K ∅ = {1} := by
  ext I
  simp only [supportedIn, Finset.notMem_empty, imp_false, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hI
    have hI' : (I : Ideal (𝓞 K)) ≠ ⊤ := fun h' => hI (Subtype.ext (by simpa using h'))
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI'
    have hM0 : M ≠ ⊥ := fun h0 => nonZeroDivisors.coe_ne_zero I (le_bot_iff.1 (h0 ▸ hIM))
    exact h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hIM)
  · rintro rfl v hv
    exact v.prime.not_dvd_one (by simpa using hv)

/-- A prime $\mathfrak{p}$ as a nonzero ideal. -/
noncomputable def primeNZ (v : HeightOneSpectrum (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

omit [NumberField K] in
@[simp]
theorem coe_primeNZ (v : HeightOneSpectrum (𝓞 K)) : (primeNZ v : Ideal (𝓞 K)) = v.asIdeal :=
  rfl

/-- The product $\mathfrak{p}^n J$ has its prime factors in $S \cup \{\mathfrak{p}\}$. -/
theorem pow_mul_mem_supportedIn {S : Finset (HeightOneSpectrum (𝓞 K))}
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (J : supportedIn K S) :
    primeNZ v ^ n * (J : (Ideal (𝓞 K))⁰) ∈ supportedIn K (insert v S) := by
  intro w hw
  rw [Submonoid.coe_mul, SubmonoidClass.coe_pow, coe_primeNZ] at hw
  rcases w.prime.dvd_or_dvd hw with h | h
  · exact Finset.mem_insert.2 (Or.inl (eq_of_asIdeal_dvd (w.prime.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (J.2 w h)

/-- If $\mathfrak{p} \notin S$ and $\mathfrak{p}^n J = \mathfrak{p}^m J'$ with $J, J'$ supported in $S$ and $n \le m$, then $n = m$. -/
theorem eq_of_pow_mul_eq {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ S) {n m : ℕ} {J J' : supportedIn K S}
    (h : v.asIdeal ^ n * ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      v.asIdeal ^ m * ((J' : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) (hnm : n ≤ m) : n = m := by
  by_contra hne
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_le_of_ne hnm hne)
  rw [pow_add, pow_add, pow_one, mul_assoc, mul_assoc] at h
  have h' := mul_left_cancel₀ (pow_ne_zero n v.ne_bot) h
  have hdvd : v.asIdeal ∣ ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :=
    ⟨v.asIdeal ^ k * ((J' : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), by rw [h']; ring⟩
  exact hv (J.2 v hdvd)

/-- The map $(n, J) \mapsto \mathfrak{p}^n J$, from $\mathbb{N}$ times the ideals supported in $S$ to the ideals supported in $S \cup \{\mathfrak{p}\}$. -/
noncomputable def insertMap (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    ℕ × supportedIn K S → supportedIn K (insert v S) :=
  fun p => ⟨primeNZ v ^ p.1 * p.2, pow_mul_mem_supportedIn v p.1 p.2⟩

/-- For $\mathfrak{p} \notin S$, the map $(n, J) \mapsto \mathfrak{p}^n J$ is a bijection. -/
theorem bijective_insertMap {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ S) : Function.Bijective (insertMap S v) := by
  constructor
  · rintro ⟨n, J⟩ ⟨m, J'⟩ h
    have h' : v.asIdeal ^ n * ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
        v.asIdeal ^ m * ((J' : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
      have := congrArg (fun I : supportedIn K (insert v S) => ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
      simpa [insertMap] using this
    have hnm : n = m := by
      rcases le_total n m with hle | hle
      · exact eq_of_pow_mul_eq hv h' hle
      · exact (eq_of_pow_mul_eq hv h'.symm hle).symm
    subst hnm
    have hJ := mul_left_cancel₀ (pow_ne_zero n v.ne_bot) h'
    exact Prod.ext rfl (Subtype.ext (Subtype.ext hJ))
  · rintro ⟨I, hI⟩
    obtain ⟨n, J, hvJ, hIJ⟩ := WfDvdMonoid.max_power_factor'
      (nonZeroDivisors.coe_ne_zero I) v.prime.not_isUnit
    have hJ0 : J ≠ 0 := right_ne_zero_of_mul (hIJ ▸ nonZeroDivisors.coe_ne_zero I)
    have hJS : (⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩ : (Ideal (𝓞 K))⁰) ∈ supportedIn K S := by
      intro w hw
      have hwI : w.asIdeal ∣ (I : Ideal (𝓞 K)) := hIJ ▸ dvd_mul_of_dvd_right hw _
      rcases Finset.mem_insert.1 (hI w hwI) with rfl | hwS
      · exact absurd hw hvJ
      · exact hwS
    refine ⟨⟨n, ⟨_, hJS⟩⟩, Subtype.ext (Subtype.ext ?_)⟩
    simp [insertMap, hIJ]

/-- For $\mathrm{Re}\, s > 1$ and a finite set $S$ of primes, $\sum N(I)^{-s}$ over the ideals with prime factors in $S$ is $\prod_{\mathfrak{p} \in S} (1 - N(\mathfrak{p})^{-s})^{-1}$. -/
theorem hasSum_supportedIn {s : ℂ} (hs : 1 < s.re) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasSum (fun I : supportedIn K S => normCpow K s ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
      (∏ v ∈ S, (1 - normCpow K s v.asIdeal)⁻¹) := by
  have hsum := summable_norm_absNorm_cpow K hs
  induction S using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, supportedIn_empty]
    convert hasSum_singleton (1 : (Ideal (𝓞 K))⁰)
      (fun I : (Ideal (𝓞 K))⁰ => normCpow K s (I : Ideal (𝓞 K)))
    all_goals simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv]
    have hg := hasSum_geometric_of_norm_lt_one (norm_normCpow_lt_one v (s := s) (by linarith))
    have hgn : Summable (fun n : ℕ => ‖normCpow K s v.asIdeal ^ n‖) :=
      (summable_geometric_of_lt_one (norm_nonneg _)
        (norm_normCpow_lt_one v (s := s) (by linarith))).congr fun n => (norm_pow _ _).symm
    have hJn : Summable (fun J : supportedIn K S =>
        ‖normCpow K s ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))‖) :=
      hsum.comp_injective Subtype.coe_injective
    have hfg : Summable (fun p : ℕ × supportedIn K S => normCpow K s v.asIdeal ^ p.1 *
        normCpow K s ((p.2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) :=
      summable_mul_of_summable_norm (f := fun n : ℕ => normCpow K s v.asIdeal ^ n)
        (g := fun J : supportedIn K S => normCpow K s ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) hgn hJn
    have hm := hg.mul ih hfg
    rw [← (Equiv.ofBijective _ (bijective_insertMap hv)).hasSum_iff]
    convert hm using 1
    funext p
    change normCpow K s ((primeNZ v ^ p.1 * p.2 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = _
    rw [Submonoid.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, coe_primeNZ]

end Finite

section Euler

variable (K) in
/-- **The Euler product of the Dedekind zeta function.** For $\mathrm{Re}\, s > 1$, $\zeta_K(s) = \prod_{\mathfrak{p}} (1 - N(\mathfrak{p})^{-s})^{-1}$. -/
theorem hasProd_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) := by
  have hsum := summable_norm_absNorm_cpow K hs
  rw [dedekindZeta_eq_of_hasSum K hsum.of_norm.hasSum]
  have h1 : ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ v ∈ T, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ =
        ∑' I : (Ideal (𝓞 K))⁰, (supportedIn K T).indicator
          (fun I : (Ideal (𝓞 K))⁰ => (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) I := by
    intro T
    rw [← tsum_subtype]
    exact (hasSum_supportedIn hs T).tsum_eq.symm
  change Tendsto _ atTop _
  simp_rw [h1]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I => ?_)
    (Eventually.of_forall fun T I => norm_indicator_le_norm_self _ _)
  have hfin := Ideal.finite_factors (nonZeroDivisors.coe_ne_zero I)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT
  rw [Set.indicator_of_mem]
  exact fun v hv => hT (hfin.mem_toFinset.2 hv)

variable (K) in
/-- The finite $L$-function of the trivial Hecke character is the Dedekind zeta function. -/
theorem finiteLFunction_one {s : ℂ} (hs : 1 < s.re) :
    (1 : HeckeCharacter K).finiteLFunction s = dedekindZeta K s := by
  rw [HeckeCharacter.finiteLFunction]
  simp_rw [localFactor_one]
  exact (hasProd_dedekindZeta K hs).tprod_eq

end Euler

end Langlands.Tate
