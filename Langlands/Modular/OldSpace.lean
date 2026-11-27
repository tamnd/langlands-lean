/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Modular.HeckeTn

/-!
# The oldspace is stable under the Hecke operators $T_n$ with $\gcd(n, N) = 1$, and the newspace

Let $N \ge 1$, let $k$ be an integer and let $n$ be coprime to $N$. This file proves that the Hecke operator $T_n$ of `Langlands/Modular/HeckeTn.lean` commutes with the inclusion of the cusp forms of level $L$ in the cusp forms of level $N$ for $L \mid N$, and with the level raising map $B_d$ from level $M$ to level $dM$ for $dM \mid N$. It follows that the oldspace of level $N$ is stable under $T_n$. The file also defines the newspace of level $N$ as the joint kernel of the trace maps to the levels $N/p$ for the primes $p \mid N$, and of these trace maps composed with the slash action of $\mathrm{diag}(p, 1)^{-1}$.

## Main definitions

* `Langlands.Modular.raiseSeq`: the map $a \mapsto (m \mapsto a_{m/d})$ on coefficient sequences, with the value $0$ for $d \nmid m$. It is the action of $B_d$ on $q$-expansion coefficients.
* `Langlands.Modular.cuspTrace`: the trace `CuspForm.trace` of Mathlib, from `CuspForm 𝒢 k` to `CuspForm ℋ k`, as a linear map.
* `Langlands.Modular.cuspTranslate`: the map $f \mapsto f \mid_k g$ for $\det g > 0$, as a linear map.
* `Langlands.Modular.traceDown`: the trace from level $N$ to level $M$.
* `Langlands.Modular.traceDownRaise`: the map $f \mapsto \mathrm{Tr}(f \mid_k \mathrm{diag}(d, 1)^{-1})$ from level $N$ to level $M$.
* `Langlands.Modular.newSpace`: the cusp forms $f$ of level $N$ with $\mathrm{Tr}(f) = 0$ and $\mathrm{Tr}(f \mid_k \mathrm{diag}(p, 1)^{-1}) = 0$ for each prime $p \mid N$, where $\mathrm{Tr}$ is the trace to level $N/p$.

## Main results

* `Langlands.Modular.heckeSeq_congr_level`: for $n$ coprime to $N$ and to $L$, the operators $T_n$ on coefficient sequences of level $N$ and of level $L$ are equal.
* `Langlands.Modular.heckeSeq_raiseSeq`: for $n$ coprime to $d$, the operator $T_n$ on coefficient sequences commutes with `raiseSeq d`.
* `Langlands.Modular.heckeTn_zero`: $T_0 = 1$.
* `Langlands.Modular.heckeTn_cuspRestrict` and `Langlands.Modular.heckeTn_comp_cuspRestrict`: for $L \mid N$ and $n$ coprime to $N$, $T_n$ of level $N$ on the restriction of $f$ is the restriction of $T_n f$ of level $L$.
* `Langlands.Modular.heckeTn_levelRaise` and `Langlands.Modular.heckeTn_comp_levelRaise`: for $n$ coprime to $dM$, $T_n B_d = B_d T_n$.
* `Langlands.Modular.cuspHeckeT_cuspRestrict` and `Langlands.Modular.cuspHeckeT_levelRaise`: the same results for $T_p$ with a prime $p$ that does not divide the level.
* `Langlands.Modular.heckeTn_mem_oldSpace` and `Langlands.Modular.oldSpace_le_comap_heckeTn`: for $n$ coprime to $N$, the operator $T_n$ maps the oldspace of level $N$ into itself.
* `Langlands.Modular.cuspHeckeT_mem_oldSpace`: for a prime $p \nmid N$, the operator $T_p$ maps the oldspace of level $N$ into itself.
* `Langlands.Modular.mem_newSpace_iff`: the explicit condition for a form to be in the newspace.

## Proof

A cusp form on $\Gamma_0(N)$ is determined by its $q$-expansion coefficients (`Langlands.Modular.cuspForm_ext_qCoeff`). For $n \ge 1$, the coefficients of $T_n f$ are $a_m(T_n f) = \sum_{e} e^{k-1} a_{mn/e^2}(f)$, where $e$ runs over the common divisors of $m$ and $n$ that are coprime to the level (`Langlands.Modular.qCoeff_heckeTn`). For $n$ coprime to the level, each divisor $e$ of $n$ is coprime to the level, so the formula does not depend on the level. The restriction does not change the function, so it does not change the coefficients. This gives the commutation with the restriction. The map $B_d$ acts on the coefficients by `raiseSeq d` (`Langlands.Modular.qCoeff_levelRaise`). For $e \mid n$ with $n$ coprime to $d$, the number $e$ is coprime to $d$. Thus $e \mid dt$ if and only if $e \mid t$, and $d \mid mn/e^2$ if and only if $d \mid m$. This gives the commutation of the coefficient maps, and thus the commutation with $B_d$. The oldspace is the span of the images of the maps $f \mapsto B_d f$ from level $M$, restricted to level $N$, over the pairs $(M, d)$ with $dM \mid N$ and $M < N$. Each $n$ coprime to $N$ is coprime to $dM$, so $T_n$ maps each of these images into the image of the same map. For the newspace, the trace and the translate are linear, because the slash action of a matrix of positive determinant is linear. The groups $\Gamma_0(N)$, $\Gamma_0(M)$ and $\alpha \Gamma_0(N) \alpha^{-1}$ with $\alpha = \mathrm{diag}(d, 1)$ are arithmetic (`Subgroup.IsArithmetic.conj`), so they are commensurable and the traces are defined.

## What is left

The file does not prove that the newspace is the orthogonal complement of the oldspace for the Petersson inner product. The two trace maps of the definition are, up to nonzero constants, the adjoints of the inclusion and of the map $B_p$ from level $N/p$ to level $N$, but the file does not prove this, and it does not prove that the oldspace is the span of the images of these two maps over the primes $p \mid N$. The file does not prove that the newspace is stable under the $T_n$, and it does not prove the decomposition of the cusp forms into the oldspace and the newspace. The file does not treat the operators $U_p$ with $p \mid N$ on the oldspace.

## References

* F. Diamond and J. Shurman, A first course in modular forms, chapter 5, sections 5.6 and 5.7.
* A. O. L. Atkin and J. Lehner, Hecke operators on $\Gamma_0(m)$, Math. Ann. 185 (1970), 134 to 160.
-/

namespace Langlands.Modular

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "Γ₀" N => (Gamma0 N : Subgroup (GL (Fin 2) ℝ))

section Sequence

/-- The map `a ↦ (m ↦ a_{m / d})` on coefficient sequences, with the value `0` for `d ∤ m`. It is the action of the level raising map `B_d` on `q`-expansion coefficients. -/
def raiseSeq (d : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if d ∣ m then a (m / d) else 0

variable {k : ℤ}

/-- For `n` coprime to `N` and to `L`, the operator `T_n` on coefficient sequences does not depend on the choice of the level `N` or `L`. -/
theorem heckeSeq_congr_level {N L n : ℕ} (hN : n.Coprime N) (hL : n.Coprime L) :
    heckeSeq N k n = heckeSeq L k n := by
  funext a m
  unfold heckeSeq
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := Nat.dvd_of_mem_divisors he
  simp only [eq_true (Nat.Coprime.coprime_dvd_left he' hN),
    eq_true (Nat.Coprime.coprime_dvd_left he' hL), true_and]

/-- For `n` coprime to `d`, the operator `T_n` on coefficient sequences commutes with `raiseSeq d`. -/
theorem heckeSeq_raiseSeq {N d n : ℕ} (hd : n.Coprime d) (a : ℕ → ℂ) :
    heckeSeq N k n (raiseSeq d a) = raiseSeq d (heckeSeq N k n a) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rw [Nat.coprime_zero_right] at hd
    subst hd
    rw [heckeSeq_one, heckeSeq_one]
  funext m
  unfold heckeSeq
  by_cases hdm : d ∣ m
  · obtain ⟨t, rfl⟩ := hdm
    simp only [raiseSeq, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hd0]
    refine Finset.sum_congr rfl fun e he => ?_
    have hen := Nat.dvd_of_mem_divisors he
    have hed : e.Coprime d := Nat.Coprime.coprime_dvd_left hen hd
    simp only [hed.dvd_mul_left]
    by_cases het : e.Coprime N ∧ e ∣ t
    · obtain ⟨-, s, rfl⟩ := het
      obtain ⟨u, rfl⟩ := hen
      have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
      have h1 : d * (e * s) * (e * u) / (e * e) = d * (s * u) :=
        Nat.div_eq_of_eq_mul_left (Nat.mul_pos he0 he0) (by ring)
      have h2 : e * s * (e * u) / (e * e) = s * u :=
        Nat.div_eq_of_eq_mul_left (Nat.mul_pos he0 he0) (by ring)
      simp only [h1, h2, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hd0]
    · simp only [het, ↓reduceIte]
  · simp only [raiseSeq, hdm, ↓reduceIte]
    refine Finset.sum_eq_zero fun e he => ?_
    have hen := Nat.dvd_of_mem_divisors he
    by_cases hem : e.Coprime N ∧ e ∣ m
    · obtain ⟨-, s, rfl⟩ := hem
      obtain ⟨u, rfl⟩ := hen
      have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
      have h1 : e * s * (e * u) / (e * e) = s * u :=
        Nat.div_eq_of_eq_mul_left (Nat.mul_pos he0 he0) (by ring)
      have hdu : d.Coprime u := (Nat.Coprime.coprime_dvd_left (dvd_mul_left u e) hd).symm
      have hds : ¬ d ∣ s * u := fun h => hdm ((hdu.dvd_of_dvd_mul_right h).mul_left e)
      simp [h1, hds]
    · simp only [hem, ↓reduceIte]

end Sequence

section Operator

variable {k : ℤ}

/-- The coefficients of the restriction of `f` from level `L` to level `N` are the coefficients of `f`. -/
lemma qCoeff_cuspRestrict {L N : ℕ} (h : L ∣ N) (f : CuspForm (Γ₀ L) k) :
    qCoeff (cuspRestrict h f) = qCoeff f :=
  rfl

/-- The coefficients of `B_d f` are `raiseSeq d` of the coefficients of `f`. -/
lemma qCoeff_levelRaise_eq (d M : ℕ) [NeZero d] [NeZero M] (f : CuspForm (Γ₀ M) k) :
    qCoeff (levelRaise d M f) = raiseSeq d (qCoeff f) :=
  funext fun m => qCoeff_levelRaise d M f m

/-- The relation `T_0 = 1`, from the convention that `T_0` is the empty product. -/
@[simp]
theorem heckeTn_zero (N : ℕ) [NeZero N] : heckeTn N k 0 = 1 := by
  rw [heckeTn, Finset.noncommProd_congr Nat.primeFactors_zero (fun _ _ => rfl)]
  exact Finset.noncommProd_empty _ _

/-- **Commutation of `T_n` with the restriction**: for `L ∣ N` and `n` coprime to `N`, the operator `T_n` of level `N` on the restriction of a cusp form `f` of level `L` is the restriction of the form `T_n f` of level `L`. -/
theorem heckeTn_cuspRestrict {L N : ℕ} [NeZero L] [NeZero N] (h : L ∣ N) {n : ℕ}
    (hn : n.Coprime N) (f : CuspForm (Γ₀ L) k) :
    heckeTn N k n (cuspRestrict h f) = cuspRestrict h (heckeTn L k n f) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  refine cuspForm_ext_qCoeff N k fun m => ?_
  rw [qCoeff_heckeTn hn0, qCoeff_cuspRestrict, qCoeff_cuspRestrict, qCoeff_heckeTn hn0,
    heckeSeq_congr_level hn (hn.coprime_dvd_right h)]

/-- **Commutation of `T_n` with the restriction**, as an equality of linear maps: for `L ∣ N` and `n` coprime to `N`, `T_n ∘ ι = ι ∘ T_n`, where `ι` is the restriction from level `L` to level `N`. -/
theorem heckeTn_comp_cuspRestrict {L N : ℕ} [NeZero L] [NeZero N] (h : L ∣ N) {n : ℕ}
    (hn : n.Coprime N) :
    (heckeTn N k n).comp (cuspRestrict h) = (cuspRestrict h).comp (heckeTn L k n) :=
  LinearMap.ext fun f => heckeTn_cuspRestrict h hn f

/-- **Commutation of `T_n` with `B_d`**: for `n` coprime to `d M`, `T_n (B_d f) = B_d (T_n f)` for each cusp form `f` of level `M`, where the first `T_n` has level `d M` and the second `T_n` has level `M`. -/
theorem heckeTn_levelRaise (d M : ℕ) [NeZero d] [NeZero M] {n : ℕ} (hn : n.Coprime (d * M))
    (f : CuspForm (Γ₀ M) k) :
    heckeTn (d * M) k n (levelRaise d M f) = levelRaise d M (heckeTn M k n f) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  refine cuspForm_ext_qCoeff (d * M) k fun m => ?_
  rw [qCoeff_heckeTn hn0, qCoeff_levelRaise_eq, qCoeff_levelRaise_eq, qCoeff_heckeTn hn0,
    heckeSeq_raiseSeq (Nat.Coprime.coprime_mul_right_right hn),
    heckeSeq_congr_level hn (Nat.Coprime.coprime_mul_left_right hn)]

/-- **Commutation of `T_n` with `B_d`**, as an equality of linear maps: for `n` coprime to `d M`, `T_n ∘ B_d = B_d ∘ T_n`. -/
theorem heckeTn_comp_levelRaise (d M : ℕ) [NeZero d] [NeZero M] {n : ℕ}
    (hn : n.Coprime (d * M)) :
    (heckeTn (d * M) k n).comp (levelRaise d M) = (levelRaise d M).comp (heckeTn M k n) :=
  LinearMap.ext fun f => heckeTn_levelRaise d M hn f

/-- **Commutation of `T_p` with the restriction**: for a prime `p ∤ N` and `L ∣ N`, the operator `T_p` of `Langlands/Modular/Hecke.lean` of level `N` on the restriction of `f` is the restriction of `T_p f` of level `L`. -/
theorem cuspHeckeT_cuspRestrict (p : ℕ) [Fact p.Prime] {L N : ℕ} [NeZero L] [NeZero N]
    (h : L ∣ N) (hpN : ¬ p ∣ N) (f : CuspForm (Γ₀ L) k) :
    cuspHeckeT p N (cuspRestrict h f) = cuspRestrict h (cuspHeckeT p L f) := by
  rw [← heckeTn_prime, ← heckeTn_prime,
    heckeTn_cuspRestrict h (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hpN)]

/-- **Commutation of `T_p` with `B_d`**: for a prime `p ∤ d M`, `T_p (B_d f) = B_d (T_p f)`, where the first `T_p` has level `d M` and the second `T_p` has level `M`. -/
theorem cuspHeckeT_levelRaise (p : ℕ) [Fact p.Prime] (d M : ℕ) [NeZero d] [NeZero M]
    (hp : ¬ p ∣ d * M) (f : CuspForm (Γ₀ M) k) :
    cuspHeckeT p (d * M) (levelRaise d M f) = levelRaise d M (cuspHeckeT p M f) := by
  rw [← heckeTn_prime, ← heckeTn_prime,
    heckeTn_levelRaise d M (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hp)]

end Operator

section OldSpace

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Stability of the oldspace**: for `n` coprime to `N`, the operator `T_n` maps the oldspace of level `N` into itself. -/
theorem oldSpace_le_comap_heckeTn {n : ℕ} (hn : n.Coprime N) :
    oldSpace N k ≤ (oldSpace N k).comap (heckeTn N k n) := by
  refine iSup_le fun M => iSup_le fun d => iSup_le fun _ => iSup_le fun h => iSup_le fun hM => ?_
  rintro _ ⟨f, rfl⟩
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using h))
  have : NeZero M := ⟨hM0⟩
  rw [Submodule.mem_comap, LinearMap.comp_apply, heckeTn_cuspRestrict h hn,
    heckeTn_levelRaise d M (hn.coprime_dvd_right h)]
  exact levelRaise_mem_oldSpace h hM _

/-- **Stability of the oldspace**: for `n` coprime to `N` and `f` in the oldspace of level `N`, the form `T_n f` is in the oldspace of level `N`. -/
theorem heckeTn_mem_oldSpace {n : ℕ} (hn : n.Coprime N) {f : CuspForm (Γ₀ N) k}
    (hf : f ∈ oldSpace N k) : heckeTn N k n f ∈ oldSpace N k :=
  oldSpace_le_comap_heckeTn hn hf

/-- **Stability of the oldspace under `T_p`**: for a prime `p ∤ N` and `f` in the oldspace of level `N`, the form `T_p f` is in the oldspace of level `N`. -/
theorem cuspHeckeT_mem_oldSpace (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {f : CuspForm (Γ₀ N) k} (hf : f ∈ oldSpace N k) : cuspHeckeT p N f ∈ oldSpace N k := by
  rw [← heckeTn_prime]
  exact heckeTn_mem_oldSpace (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hpN) hf

end OldSpace

section NewSpace

open ConjAct Pointwise

variable {k : ℤ}

/-- The term `f ∣[k] h⁻¹` of the trace of `f + g` is the sum of the terms of the traces of `f` and `g`. -/
lemma quotientFunc_add {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} (f g : CuspForm 𝒢 k)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    SlashInvariantForm.quotientFunc (f + g) q =
      SlashInvariantForm.quotientFunc f q + SlashInvariantForm.quotientFunc g q := by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.add_slash]

/-- The slash action of a matrix `g` with `det g > 0` commutes with scalar multiplication by a complex number. -/
lemma smul_slash_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] g = c • (f ∣[k] g) := by
  rw [ModularForm.smul_slash, σ, ite_eq_left_of_eq_true _ _ (eq_true hg)]
  rfl

/-- A conjugate of a subgroup of determinant one has determinant one. -/
instance hasDetOne_conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.HasDetOne] (g : GL (Fin 2) ℝ) :
    (toConjAct g • 𝒢).HasDetOne where
  det_eq {x} hx := by
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
    simp [toConjAct_smul, Subgroup.HasDetOne.det_eq hy]

/-- The term `f ∣[k] h⁻¹` of the trace of `c f` is `c` times the term of the trace of `f`. -/
lemma quotientFunc_smul' {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [ℋ.HasDetOne] (c : ℂ)
    (f : CuspForm 𝒢 k) (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    SlashInvariantForm.quotientFunc (c • f) q = c • SlashInvariantForm.quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hr : 0 < ((r : GL (Fin 2) ℝ)⁻¹).det.val := by
      rw [Subgroup.HasDetOne.det_eq (inv_mem r.2)]
      exact one_pos
    simp only [SlashInvariantForm.quotientFunc_mk, FunLike.coe_smul]
    exact smul_slash_of_det_pos hr c f

/-- The trace `f ↦ ∑ f ∣[k] h⁻¹` from `CuspForm 𝒢 k` to `CuspForm ℋ k`, as a linear map. The sum is over the cosets `h (𝒢 ∩ ℋ)` of `ℋ`. -/
noncomputable def cuspTrace (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.HasDetOne] [ℋ.HasDetOne]
    [𝒢.IsFiniteRelIndex ℋ] : CuspForm 𝒢 k →ₗ[ℂ] CuspForm ℋ k where
  toFun f := CuspForm.trace ℋ f
  map_add' f g := by
    ext τ
    simp [quotientFunc_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext τ
    simp [quotientFunc_smul', Finset.mul_sum]

/-- The translate `f ↦ f ∣[k] g` from `CuspForm 𝒢 k` to `CuspForm (g⁻¹ 𝒢 g) k`, as a linear map, for `det g > 0`. -/
noncomputable def cuspTranslate (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.HasDetOne] (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) : CuspForm 𝒢 k →ₗ[ℂ] CuspForm (toConjAct g⁻¹ • 𝒢) k where
  toFun f := CuspForm.translate f g
  map_add' f f' := by
    ext τ
    simp only [FunLike.coe_add, CuspForm.coe_translate, SlashAction.add_slash, Pi.add_apply]
  map_smul' c f := by
    ext τ
    simp only [FunLike.coe_smul, CuspForm.coe_translate, smul_slash_of_det_pos hg, Pi.smul_apply,
      RingHom.id_apply]

/-- The matrix `diag(d, 1)` in `GL(2, ℚ)`. -/
noncomputable def raiseMatQ (d : ℕ) [NeZero d] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by simp [Matrix.det_fin_two_of, NeZero.ne d])

/-- The image of `raiseMatQ d` in `GL(2, ℝ)` is `raiseMat d`. -/
lemma raiseMatQ_map (d : ℕ) [NeZero d] : (raiseMatQ d).map (Rat.castHom ℝ) = raiseMat d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raiseMatQ, raiseMat]

/-- The conjugate `α Γ₀(N) α⁻¹` is an arithmetic subgroup, with `α = diag(d, 1)`. -/
instance (d N : ℕ) [NeZero d] [NeZero N] :
    (toConjAct (raiseMat d)⁻¹⁻¹ • (Γ₀ N)).IsArithmetic := by
  have := Subgroup.IsArithmetic.conj (Γ₀ N) (raiseMatQ d)
  simpa [raiseMatQ_map] using this

/-- The group `Γ₀(N)` is commensurable with `Γ₀(M)`. -/
instance (M N : ℕ) [NeZero M] [NeZero N] : (Γ₀ N).IsFiniteRelIndex (Γ₀ M) :=
  (Subgroup.IsArithmetic.is_commensurable.trans Subgroup.IsArithmetic.is_commensurable.symm).1

/-- The group `α Γ₀(N) α⁻¹` is commensurable with `Γ₀(M)`, with `α = diag(d, 1)`. -/
instance (d M N : ℕ) [NeZero d] [NeZero M] [NeZero N] :
    (toConjAct (raiseMat d)⁻¹⁻¹ • (Γ₀ N)).IsFiniteRelIndex (Γ₀ M) :=
  (Subgroup.IsArithmetic.is_commensurable.trans Subgroup.IsArithmetic.is_commensurable.symm).1

/-- The trace map from cusp forms of level `N` to cusp forms of level `M`. -/
noncomputable def traceDown (N M : ℕ) [NeZero M] [NeZero N] :
    CuspForm (Γ₀ N) k →ₗ[ℂ] CuspForm (Γ₀ M) k :=
  cuspTrace (k := k) (Γ₀ N) (Γ₀ M)

/-- The map `f ↦ Tr(f ∣[k] diag(d, 1)⁻¹)` from cusp forms of level `N` to cusp forms of level `M`. For `N = d M` it is, up to a nonzero constant, the adjoint of the level raising map `B_d` for the Petersson inner product. -/
noncomputable def traceDownRaise (d N M : ℕ) [NeZero d] [NeZero M] [NeZero N] :
    CuspForm (Γ₀ N) k →ₗ[ℂ] CuspForm (Γ₀ M) k :=
  (cuspTrace _ (Γ₀ M)).comp (cuspTranslate (Γ₀ N) (raiseMat d)⁻¹ (by
    rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, raiseMat_coe,
      Matrix.det_fin_two_of]
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
    simpa using this))

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- **The newspace** of level `N`: the cusp forms `f` of level `N` with `Tr(f) = 0` and `Tr(f ∣[k] diag(p, 1)⁻¹) = 0` for each prime `p ∣ N`, where `Tr` is the trace to level `N / p`. These two maps are, up to nonzero constants, the adjoints of the inclusion and of the map `B_p` from level `N / p` to level `N` for the Petersson inner product. -/
noncomputable def newSpace : Submodule ℂ (CuspForm (Γ₀ N) k) :=
  ⨅ (p : ℕ) (_ : NeZero p) (_ : p.Prime) (M : ℕ) (_ : NeZero M) (_ : p * M = N),
    LinearMap.ker (traceDown (k := k) N M) ⊓ LinearMap.ker (traceDownRaise (k := k) p N M)

variable {N k}

/-- A cusp form `f` of level `N` is in the newspace if and only if, for each prime `p` and each `M` with `p M = N`, the trace of `f` to level `M` is zero and the trace of `f ∣[k] diag(p, 1)⁻¹` to level `M` is zero. -/
theorem mem_newSpace_iff (f : CuspForm (Γ₀ N) k) :
    f ∈ newSpace N k ↔ ∀ (p : ℕ) [NeZero p], p.Prime → ∀ (M : ℕ) [NeZero M], p * M = N →
      traceDown N M f = 0 ∧ traceDownRaise p N M f = 0 := by
  simp only [newSpace, Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker]

end NewSpace

end Langlands.Modular
