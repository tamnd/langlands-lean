/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.AdmissiblePairs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Henselian

/-!
# Minimal pairs

Let $F$ be a nonarchimedean local field and $E/F$ a quadratic extension. This file proves the facts on $E/F$ that BH §18 uses: the ramification index is $e(E|F) \in \{1, 2\}$, so $E/F$ is unramified or totally ramified, and in the totally ramified case $k_E = k_F$ and each class of $U^{2m}_E / U^{2m+1}_E$ has a representative in $U^m_F$. It also proves that the elements of a small enough $U^M_F$ are norms of elements of $U^k_E$, with Hensel's lemma. Then it defines minimal pairs (BH §18), proves that each admissible pair is a twist of a minimal pair, and proves that a minimal pair $(E/F, \xi)$ with $E/F$ ramified has odd level. The last part computes the level of a twist $\xi \otimes \chi_E$ when the two levels are different.

## Main definitions

* `Langlands.LocalGL2.ramIdx`: the ramification index $e(E|F) = \mathrm{ord}_E(\varpi_F)$.
* `Langlands.LocalGL2.inclUnits`: the inclusion $F^\times \to E^\times$.
* `Langlands.LocalGL2.IsMinimal`: the admissible character $\xi$ is minimal: $\xi$ on $U^n_E$, $n = \ell(\xi)$, does not factor through $N_{E/F}$ (BH §18).
* `Langlands.LocalGL2.AdmissiblePair.IsMinimal`: the admissible pair is minimal.

## Main results

* `Langlands.LocalGL2.ramIdx_eq_one_or_two`: $e(E|F) \in \{1, 2\}$ for a quadratic extension.
* `Langlands.LocalGL2.isUnramifiedExt_or_isTotallyRamifiedExt`: $E/F$ is unramified or totally ramified.
* `Langlands.LocalGL2.isTotallyRamifiedExt_iff_not_isUnramifiedExt`: $E/F$ is totally ramified exactly when it is not unramified.
* `Langlands.LocalGL2.exists_sub_mem_ordBall_one`: if $E/F$ is totally ramified, then $k_E = k_F$.
* `Langlands.LocalGL2.exists_inclUnits_mul`: if $E/F$ is totally ramified and $m \ge 1$, then $U^{2m}_E = U^m_F U^{2m+1}_E$.
* `Langlands.LocalGL2.normUnits_mem_unitFilt_of_lt`: $N_{E/F}(U^k_E) \subseteq U^m_F$ when $e m < k + e$.
* `Langlands.LocalGL2.exists_normUnits_eq`: each element of a small enough $U^M_F$ is the norm of an element of $U^k_E$.
* `Langlands.LocalGL2.exists_factor_iff`: $\xi$ on a subgroup $U$ factors through $N_{E/F}$ exactly when $\xi$ is trivial on the elements of $U$ of norm $1$.
* `Langlands.LocalGL2.IsAdmissible.exists_isMinimal_twistChar`, `Langlands.LocalGL2.AdmissiblePair.exists_isMinimal_iso_twist`: each admissible pair is $F$-isomorphic to $(E/F, \xi' \otimes \chi_E)$ for a minimal pair $(E/F, \xi')$ and a smooth character $\chi$ of $F^\times$ (BH §18).
* `Langlands.LocalGL2.IsMinimal.odd_level`, `Langlands.LocalGL2.AdmissiblePair.IsMinimal.odd_level`: if $E/F$ is ramified and $(E/F, \xi)$ is minimal, then the level of $\xi$ is odd (BH §18).
* `Langlands.LocalGL2.isLevel_twistChar_of_ne`: if $\ell(\xi) \ne \ell(\chi_E)$, then $\ell(\xi \otimes \chi_E) = \max(\ell(\xi), \ell(\chi_E))$.
* `Langlands.LocalGL2.isLevel_comp_normUnits_of_ramified`: if $E/F$ is tamely and totally ramified and $\ell(\chi) \ge 1$, then $\ell(\chi_E) = 2 \ell(\chi)$.
* `Langlands.LocalGL2.isLevel_twistChar_of_ramified`: in the same case, $\ell(\xi \otimes \chi_E) = \max(\ell(\xi), e(E|F) \ell(\chi))$ when the two numbers are different.

## Implementation notes

The ramification index is the integer $\mathrm{ord}_E(\varpi_F)$. The bound $e(E|F) \le 2$ uses the basis $1, \varpi_E$ of $E/F$, which exists when $e(E|F) \ge 2$, and the strict ultrametric property `Langlands.LocalGL2.ord_add_of_lt`. The residue degree is not defined here. The norm statement `exists_normUnits_eq` uses an element $\beta$ with $\beta + \sigma(\beta) = 1$, so it is true also when $p = 2$. It gives the smoothness of the character $\varphi$ in the proof that each admissible pair is a twist of a minimal pair. Hensel's lemma comes from `HenselianRing.is_henselian` for $\mathcal{O}_F$, which is $\mathfrak{p}_F$-adically complete. This needs the uniform structure of the topological group $F$, which the proofs give locally.

## What is still open

* The residue degree $f(E|F)$ and the identity $e f = 2$. Here only $f = 1$ in the totally ramified case is proved, in the form $k_E = k_F$. The fact $f = 2$ in the unramified case is open.
* The level of $\chi_E$ when $E/F$ is unramified ($\ell(\chi_E) = \ell(\chi)$), and when $E/F$ is ramified and $\ell(\chi) = 0$. The first needs the surjectivity of the norm on the quotients $U^n_E / U^{n+1}_E$.
* The other statements of BH §18 on minimal pairs, for example the uniqueness of the minimal pair up to twist.
* The separability of $E/F$ is not proved from the other hypotheses. It is still a field of `Langlands.LocalGL2.TameQuadExt`, which this file does not change.

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, §18.
-/

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel

section Ord

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The strict ultrametric property.** If $x, y \ne 0$ and $\mathrm{ord}(x) < \mathrm{ord}(y)$, then $x + y \ne 0$ and $\mathrm{ord}(x + y) = \mathrm{ord}(x)$. -/
theorem ord_add_of_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : ord K x < ord K y) :
    x + y ≠ 0 ∧ ord K (x + y) = ord K x := by
  have hx' : x ∈ ordBall K (ord K x) := mem_ordBall_of_le hx le_rfl
  have hy' : y ∈ ordBall K (ord K x + 1) := mem_ordBall_of_le hy (by omega)
  have hs : x + y ∈ ordBall K (ord K x) := add_mem_ordBall hx' (ordBall_anti (by omega) hy')
  have hn : x + y ∉ ordBall K (ord K x + 1) := by
    intro hxy
    have h1 := add_mem_ordBall hxy (neg_mem_ordBall hy')
    rw [add_neg_cancel_right] at h1
    have := (mem_ordBall_of_ne_zero hx).1 h1
    omega
  have h0 : x + y ≠ 0 := fun h0 => hn (h0 ▸ zero_mem_ordBall _)
  refine ⟨h0, le_antisymm ?_ ((mem_ordBall_of_ne_zero h0).1 hs)⟩
  by_contra hc
  exact hn (mem_ordBall_of_le h0 (by omega))

/-- If $n \ge 1$ and $y \in \mathfrak{p}_K^n$, then $1 + y$ is a unit in $U^n_K$. -/
theorem exists_unitFilt_one_add {n : ℕ} (hn : 1 ≤ n) {y : K} (hy : y ∈ ordBall K n) :
    ∃ x : Kˣ, x ∈ unitFilt K n ∧ (x : K) = 1 + y := by
  have key : 1 + y ≠ 0 ∧ ord K (1 + y) = 0 := by
    by_cases hy0 : y = 0
    · simp [hy0, ord_one]
    · have h1 := (mem_ordBall_of_ne_zero hy0).1 hy
      have := ord_add_of_lt one_ne_zero hy0 (by rw [ord_one]; omega)
      rwa [ord_one] at this
  refine ⟨Units.mk0 _ key.1, ⟨key.2, ?_⟩, rfl⟩
  rwa [Units.val_mk0, add_sub_cancel_left]

/-- An element of order $0$ is in $\mathcal{O}_K$, so $x - 1 \in \mathfrak{p}_K^0$. -/
theorem sub_one_mem_ordBall_zero {x : K} (hx : x ≠ 0) (h0 : ord K x = 0) : x - 1 ∈ ordBall K 0 :=
  sub_eq_add_neg x 1 ▸ add_mem_ordBall (mem_ordBall_of_le hx h0.ge)
    (neg_mem_ordBall (mem_ordBall_of_le one_ne_zero (by rw [ord_one])))

/-- If $2 \ne 0$ in the residue field of $K$, then $\mathrm{ord}(2) = 0$. -/
theorem ord_two_eq_zero (h2 : (2 : 𝓀[K]) ≠ 0) : ord K (2 : K) = 0 := by
  have h20 : (2 : K) ≠ 0 := two_ne_zero_of_residue h2
  have hO : ((2 : 𝒪[K]) : K) = 2 := by
    change 𝒪[K].subtype 2 = 2
    exact map_ofNat _ 2
  have hmem : (2 : K) ∈ ordBall K 0 := by
    rw [ordBall_zero_eq_integer, ← hO]
    exact (2 : 𝒪[K]).2
  have hnot : (2 : K) ∉ ordBall K 1 := by
    rw [← hO, mem_ordBall_one_iff]
    intro hm
    apply h2
    rw [← map_ofNat (IsLocalRing.residue 𝒪[K]) 2]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hm
  have h1 := (mem_ordBall_of_ne_zero h20).1 hmem
  by_contra hc
  exact hnot (mem_ordBall_of_le h20 (by omega))

/-- **Square roots in the filtration.** Let $2 \ne 0$ in the residue field of $K$, $m \ge 1$ and $a \in U^m_K$. If $a^2 \in U^{m+1}_K$, then $a \in U^{m+1}_K$. The reason is $a^2 - 1 = x (2 + x)$ with $x = a - 1$ and $\mathrm{ord}(2 + x) = 0$. -/
theorem mem_unitFilt_succ_of_sq (h2 : (2 : 𝓀[K]) ≠ 0) {m : ℕ} (hm : 1 ≤ m) {a : Kˣ}
    (ha : a ∈ unitFilt K m) (ha2 : a ^ 2 ∈ unitFilt K (m + 1)) : a ∈ unitFilt K (m + 1) := by
  refine ⟨ha.1, ?_⟩
  set x : K := (a : K) - 1 with hx
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem_ordBall _
  have hxm := (mem_ordBall_of_ne_zero hx0).1 ha.2
  have h20 : (2 : K) ≠ 0 := two_ne_zero_of_residue h2
  have hord2 := ord_two_eq_zero h2
  obtain ⟨h2x, h2xo⟩ := ord_add_of_lt h20 hx0 (by rw [hord2]; omega)
  have he : ((a ^ 2 : Kˣ) : K) - 1 = x * (2 + x) := by
    rw [hx, Units.val_pow_eq_pow_val]
    ring
  have hprod : x * (2 + x) ≠ 0 := mul_ne_zero hx0 h2x
  have h3 := (mem_ordBall_of_ne_zero hprod).1 (he ▸ ha2.2)
  rw [ord_mul hx0 h2x, h2xo, hord2, add_zero] at h3
  exact mem_ordBall_of_le hx0 h3

end Ord

section Ramification

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]

/-- The ramification index $e(E|F) = \mathrm{ord}_E(\varpi_F)$, where $\varpi_F$ is the chosen uniformizer of $F$. -/
noncomputable def ramIdx : ℤ :=
  ord E (algebraMap F E (unif F : F))

variable {F E}

/-- The ramification index is positive. -/
theorem ramIdx_pos : 0 < ramIdx F E :=
  ord_algebraMap_unif_pos

/-- For $a \in F$, $\mathrm{ord}_E(a) = e(E|F) \, \mathrm{ord}_F(a)$. -/
theorem ord_algebraMap_eq (a : F) : ord E (algebraMap F E a) = ramIdx F E * ord F a :=
  ord_algebraMap a

/-- The extension $E/F$ is unramified exactly when $e(E|F) = 1$. -/
theorem isUnramifiedExt_iff_ramIdx : IsUnramifiedExt F E ↔ ramIdx F E = 1 := by
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · rw [ramIdx, h, ord_unif]
  · rw [ord_algebraMap_eq, h, one_mul]

/-- The extension $E/F$ is totally ramified exactly when $e(E|F) = 2$. -/
theorem isTotallyRamifiedExt_iff_ramIdx : IsTotallyRamifiedExt F E ↔ ramIdx F E = 2 := by
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · rw [ramIdx, h, ord_unif, mul_one]
  · rw [ord_algebraMap_eq, h]

/-- If $e(E|F) \ge 2$, then $1$ and a uniformizer $\varpi_E$ of $E$ are linearly independent over $F$, because the elements of $F$ have orders in $e(E|F) \mathbb{Z}$. -/
theorem linearIndependent_one_unif (he : 2 ≤ ramIdx F E) :
    LinearIndependent F ![(1 : E), (unif E : E)] := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  rw [Algebra.smul_def, mul_one] at ha
  have h := congrArg (ord E) ha
  rw [ord_algebraMap_eq, ord_unif] at h
  have := Int.le_of_dvd one_pos ⟨ord F a, h.symm⟩
  omega

variable [Algebra.IsQuadraticExtension F E]

/-- If $e(E|F) \ge 2$, then each $w \in E$ is $w = s + t \varpi_E$ with $s, t \in F$. -/
theorem exists_eq_add_mul_unif (he : 2 ≤ ramIdx F E) (w : E) :
    ∃ s t : F, algebraMap F E s + algebraMap F E t * (unif E : E) = w := by
  have hspan := (linearIndependent_one_unif he).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  have hw : w ∈ Submodule.span F (Set.range ![(1 : E), (unif E : E)]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hw
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

omit [Algebra.IsQuadraticExtension F E] in
/-- The order of $w = s + t \varpi_E$ with $s, t \in F$ and $w \ne 0$, if $e(E|F) \ge 2$: it is the order of $s$ or the order of $t \varpi_E$, and it is at most the order of each of the two terms that are not zero. -/
theorem ord_add_mul_unif (he : 2 ≤ ramIdx F E) {s t : F}
    (hw : algebraMap F E s + algebraMap F E t * (unif E : E) ≠ 0) :
    (s ≠ 0 → ord E (algebraMap F E s + algebraMap F E t * (unif E : E)) ≤ ramIdx F E * ord F s) ∧
    (t ≠ 0 → ord E (algebraMap F E s + algebraMap F E t * (unif E : E)) ≤
      ramIdx F E * ord F t + 1) ∧
    (ord E (algebraMap F E s + algebraMap F E t * (unif E : E)) = ramIdx F E * ord F s ∨
      ord E (algebraMap F E s + algebraMap F E t * (unif E : E)) = ramIdx F E * ord F t + 1) := by
  have hπ : (unif E : E) ≠ 0 := (unif E).ne_zero
  by_cases hs : s = 0
  · have ht : t ≠ 0 := by
      rintro rfl
      simp [hs] at hw
    have ho : ord E (algebraMap F E t * (unif E : E)) = ramIdx F E * ord F t + 1 := by
      rw [ord_mul ((map_ne_zero _).2 ht) hπ, ord_algebraMap_eq, ord_unif]
    simp only [hs, map_zero, zero_add, ho]
    exact ⟨fun h => absurd rfl h, fun _ => le_rfl, by simp⟩
  by_cases ht : t = 0
  · simp only [ht, map_zero, zero_mul, add_zero, ord_algebraMap_eq]
    exact ⟨fun _ => le_rfl, fun h => absurd rfl h, by simp⟩
  have hs' : algebraMap F E s ≠ 0 := (map_ne_zero _).2 hs
  have ht' : algebraMap F E t * (unif E : E) ≠ 0 := mul_ne_zero ((map_ne_zero _).2 ht) hπ
  have h1 : ord E (algebraMap F E s) = ramIdx F E * ord F s := ord_algebraMap_eq s
  have h2 : ord E (algebraMap F E t * (unif E : E)) = ramIdx F E * ord F t + 1 := by
    rw [ord_mul ((map_ne_zero _).2 ht) hπ, ord_algebraMap_eq, ord_unif]
  have hne : ramIdx F E * ord F s ≠ ramIdx F E * ord F t + 1 := by
    intro h
    have := Int.le_of_dvd one_pos
      (show ramIdx F E ∣ 1 from ⟨ord F s - ord F t, by rw [mul_sub]; omega⟩)
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := (ord_add_of_lt hs' ht' (by rw [h1, h2]; exact hlt)).2
    rw [this, h1]
    exact ⟨fun _ => le_rfl, fun _ => hlt.le, Or.inl rfl⟩
  · have := (ord_add_of_lt ht' hs' (by rw [h1, h2]; exact hlt)).2
    rw [add_comm, this, h2]
    exact ⟨fun _ => hlt.le, fun _ => le_rfl, Or.inr rfl⟩

variable (F E) in
/-- **The ramification index of a quadratic extension** (BH §18). For a quadratic extension $E/F$ of nonarchimedean local fields, $e(E|F) \in \{1, 2\}$. The proof writes $\varpi_E^2 = s + t \varpi_E$ with $s, t \in F$: if $e(E|F) \ge 3$, then the order $2$ of $\varpi_E^2$ is not in $e \mathbb{Z} \cup (e \mathbb{Z} + 1)$. -/
theorem ramIdx_eq_one_or_two : ramIdx F E = 1 ∨ ramIdx F E = 2 := by
  have he0 : 0 < ramIdx F E := ramIdx_pos
  by_contra hc
  push Not at hc
  have he3 : 3 ≤ ramIdx F E := by omega
  obtain ⟨s, t, hst⟩ := exists_eq_add_mul_unif (F := F) (by omega) ((unif E : E) ^ 2)
  have hπ2 : ord E ((unif E : E) ^ 2) = 2 := by
    rw [← zpow_natCast, ord_zpow, ord_unif]
    norm_num
  have hw : algebraMap F E s + algebraMap F E t * (unif E : E) ≠ 0 := by
    rw [hst]
    exact pow_ne_zero 2 (unif E).ne_zero
  have h := (ord_add_mul_unif (by omega) hw).2.2
  rw [hst, hπ2] at h
  rcases h with h | h
  · have := Int.le_of_dvd two_pos ⟨ord F s, h⟩
    omega
  · have := Int.le_of_dvd one_pos (show ramIdx F E ∣ 1 from ⟨ord F t, by omega⟩)
    omega

variable (F E) in
/-- **Unramified or totally ramified** (BH §18). A quadratic extension $E/F$ of nonarchimedean local fields is unramified or totally ramified. -/
theorem isUnramifiedExt_or_isTotallyRamifiedExt :
    IsUnramifiedExt F E ∨ IsTotallyRamifiedExt F E := by
  rw [isUnramifiedExt_iff_ramIdx, isTotallyRamifiedExt_iff_ramIdx]
  exact ramIdx_eq_one_or_two F E

/-- A quadratic extension that is not unramified is totally ramified. -/
theorem isTotallyRamifiedExt_of_not_isUnramifiedExt (h : ¬ IsUnramifiedExt F E) :
    IsTotallyRamifiedExt F E :=
  (isUnramifiedExt_or_isTotallyRamifiedExt F E).resolve_left h

/-- A quadratic extension is totally ramified exactly when it is not unramified. -/
theorem isTotallyRamifiedExt_iff_not_isUnramifiedExt :
    IsTotallyRamifiedExt F E ↔ ¬ IsUnramifiedExt F E :=
  ⟨IsTotallyRamifiedExt.not_isUnramifiedExt, isTotallyRamifiedExt_of_not_isUnramifiedExt⟩

/-- **The residue fields in the ramified case** (BH §18). If $E/F$ is totally ramified, then $k_E = k_F$: for each $w \in \mathcal{O}_E$ there is $c \in \mathcal{O}_F$ with $w - c \in \mathfrak{p}_E$. The proof writes $w = s + t \varpi_E$ with $s, t \in F$; the two terms have orders of different parity, so both are in $\mathcal{O}_E$, and then $s \in \mathcal{O}_F$ and $t \varpi_E \in \mathfrak{p}_E$. -/
theorem exists_sub_mem_ordBall_one (hr : IsTotallyRamifiedExt F E) {w : E}
    (hw : w ∈ ordBall E 0) : ∃ c : F, c ∈ ordBall F 0 ∧ w - algebraMap F E c ∈ ordBall E 1 := by
  have he : ramIdx F E = 2 := isTotallyRamifiedExt_iff_ramIdx.1 hr
  obtain ⟨s, t, hst⟩ := exists_eq_add_mul_unif (F := F) (by omega) w
  by_cases hw0 : w = 0
  · exact ⟨0, zero_mem_ordBall _, by rw [hw0, map_zero, sub_zero]; exact zero_mem_ordBall _⟩
  have hw' : algebraMap F E s + algebraMap F E t * (unif E : E) ≠ 0 := by rwa [hst]
  have ho := (mem_ordBall_of_ne_zero hw0).1 hw
  obtain ⟨hs, ht, -⟩ := ord_add_mul_unif (by omega) hw'
  rw [hst, he] at hs ht
  refine ⟨s, ?_, ?_⟩
  · by_cases hs0 : s = 0
    · rw [hs0]
      exact zero_mem_ordBall _
    · exact mem_ordBall_of_le hs0 (by have := hs hs0; omega)
  · rw [← hst, add_sub_cancel_left]
    by_cases ht0 : t = 0
    · rw [ht0, map_zero, zero_mul]
      exact zero_mem_ordBall _
    · refine mem_ordBall_of_le (mul_ne_zero ((map_ne_zero _).2 ht0) (unif E).ne_zero) ?_
      rw [ord_mul ((map_ne_zero _).2 ht0) (unif E).ne_zero, ord_algebraMap_eq, ord_unif, he]
      have := ht ht0
      omega

end Ramification

section Norm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]

variable (F E) in
/-- The inclusion $F^\times \to E^\times$. -/
noncomputable def inclUnits : Fˣ →* Eˣ :=
  Units.map (algebraMap F E : F →* E)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The value of the inclusion $F^\times \to E^\times$. -/
@[simp]
theorem val_inclUnits (a : Fˣ) : ((inclUnits F E a : Eˣ) : E) = algebraMap F E (a : F) := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- For $a \in F^\times$, $N_{E/F}(a) = a^2$. -/
theorem normUnits_inclUnits [Algebra.IsQuadraticExtension F E] (a : Fˣ) :
    normUnits F E (inclUnits F E a) = a ^ 2 := by
  ext
  rw [val_normUnits, val_inclUnits, Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, Units.val_pow_eq_pow_val]

omit [Valuation.HasExtension (valuation F) (valuation E)] in
/-- If $E/F$ is totally ramified, then the inclusion maps $U^m_F$ into $U^{2m}_E$. -/
theorem inclUnits_mem_unitFilt (hr : IsTotallyRamifiedExt F E) {m : ℕ} {a : Fˣ}
    (ha : a ∈ unitFilt F m) : inclUnits F E a ∈ unitFilt E (2 * m) := by
  refine ⟨?_, ?_⟩
  · rw [val_inclUnits, hr, ha.1, mul_zero]
  · rw [val_inclUnits, ← map_one (algebraMap F E), ← map_sub]
    by_cases h0 : (a : F) - 1 = 0
    · rw [h0, map_zero]
      exact zero_mem_ordBall _
    · refine mem_ordBall_of_le ((map_ne_zero _).2 h0) ?_
      rw [hr]
      have := (mem_ordBall_of_ne_zero h0).1 ha.2
      push_cast
      omega

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- **The norm on the filtration.** If $x \in U^k_E$ and $e(E|F) \, m < k + e(E|F)$, then $N_{E/F}(x) \in U^m_F$. In particular $N_{E/F}(U^k_E) \subseteq U^m_F$ with $m = \lceil k / e(E|F) \rceil$. The proof writes $x = 1 + z$; then $N_{E/F}(x) - 1 = z + \sigma(z) + z \sigma(z)$ is in $F$ and has order at least $k$ in $E$. -/
theorem normUnits_mem_unitFilt_of_lt {k m : ℕ} {x : Eˣ} (hx : x ∈ unitFilt E k)
    (hkm : ramIdx F E * m < k + ramIdx F E) : normUnits F E x ∈ unitFilt F m := by
  have he0 : 0 < ramIdx F E := ramIdx_pos
  obtain ⟨hx0, hx1⟩ := hx
  set z : E := (x : E) - 1 with hz
  have hσz : galConj F E z ∈ ordBall E k := (map_mem_ordBall_iff (galConj F E) z _).2 hx1
  have hzz : z * galConj F E z ∈ ordBall E k :=
    ordBall_anti (by omega) (mul_mem_ordBall_add hx1 hσz)
  have hw : algebraMap F E ((normUnits F E x : F) - 1) = z + galConj F E z + z * galConj F E z := by
    rw [map_sub, map_one, val_normUnits, algebraMap_norm_eq_mul, hz, map_sub, map_one]
    ring
  have hwmem : algebraMap F E ((normUnits F E x : F) - 1) ∈ ordBall E k := by
    rw [hw]
    exact add_mem_ordBall (add_mem_ordBall hx1 hσz) hzz
  refine ⟨?_, ?_⟩
  · have h1 := ord_algebraMap_eq (E := E) (normUnits F E x : F)
    rw [val_normUnits, algebraMap_norm_eq_mul, ord_mul x.ne_zero (by simp), ord_map, hx0,
      add_zero] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · omega
    · exact h
  · by_cases h0 : (normUnits F E x : F) - 1 = 0
    · rw [h0]
      exact zero_mem_ordBall _
    · refine (mem_ordBall_of_ne_zero h0).2 ?_
      have h1 := (mem_ordBall_of_ne_zero ((map_ne_zero _).2 h0)).1 hwmem
      rw [ord_algebraMap_eq] at h1
      have h2 : ramIdx F E * (m : ℤ) < ramIdx F E * (ord F ((normUnits F E x : F) - 1) + 1) := by
        rw [mul_add, mul_one]
        omega
      have := lt_of_mul_lt_mul_left h2 he0.le
      omega

omit [Algebra.IsSeparable F E] in
/-- **Representatives in the ramified case** (BH §18). Let $E/F$ be totally ramified and $m \ge 1$. Each $u \in U^{2m}_E$ is $u = a v$ with $a \in U^m_F$ and $v \in U^{2m+1}_E$: each class of $U^{2m}_E / U^{2m+1}_E$ has a representative in $U^m_F = F \cap U^{2m}_E$. The proof uses $k_E = k_F$. -/
theorem exists_inclUnits_mul (hr : IsTotallyRamifiedExt F E) {m : ℕ} (hm : 1 ≤ m) {u : Eˣ}
    (hu : u ∈ unitFilt E (2 * m)) :
    ∃ a : Fˣ, a ∈ unitFilt F m ∧
      ∃ v : Eˣ, v ∈ unitFilt E (2 * m + 1) ∧ u = inclUnits F E a * v := by
  have he : ramIdx F E = 2 := isTotallyRamifiedExt_iff_ramIdx.1 hr
  set ϖ : F := (unif F : F) ^ (m : ℤ) with hϖ
  have hϖ0 : ϖ ≠ 0 := zpow_ne_zero _ (unif F).ne_zero
  have hϖE0 : algebraMap F E ϖ ≠ 0 := (map_ne_zero _).2 hϖ0
  have hϖF : ord F ϖ = m := by rw [hϖ, ord_zpow, ord_unif, mul_one]
  have hϖE : ord E (algebraMap F E ϖ) = 2 * m := by rw [ord_algebraMap_eq, he, hϖF]
  set z : E := (u : E) - 1 with hz
  set w : E := z * (algebraMap F E ϖ)⁻¹ with hw
  have hwO : w ∈ ordBall E 0 := by
    have h1 : (algebraMap F E ϖ)⁻¹ ∈ ordBall E (-(2 * m)) :=
      mem_ordBall_of_le (inv_ne_zero hϖE0) (by rw [ord_inv hϖE0, hϖE])
    have h2 := mul_mem_ordBall_add hu.2 h1
    have h3 : ((2 * m : ℕ) : ℤ) + -(2 * (m : ℤ)) = 0 := by push_cast; ring
    rwa [h3] at h2
  obtain ⟨c, hcO, hc⟩ := exists_sub_mem_ordBall_one hr hwO
  have hcϖ : c * ϖ ∈ ordBall F m := by
    have := mul_mem_ordBall_add hcO (mem_ordBall_of_le hϖ0 hϖF.ge)
    rwa [zero_add] at this
  obtain ⟨a, ha, hav⟩ := exists_unitFilt_one_add hm hcϖ
  have haE : inclUnits F E a ∈ unitFilt E (2 * m) := inclUnits_mem_unitFilt hr ha
  refine ⟨a, ha, (inclUnits F E a)⁻¹ * u, ⟨?_, ?_⟩, by group⟩
  · rw [Units.val_mul, ord_mul (Units.ne_zero _) u.ne_zero, Units.val_inv_eq_inv_val,
      ord_inv (Units.ne_zero _), haE.1, hu.1, neg_zero, add_zero]
  · have hdiff : (u : E) - (inclUnits F E a : E) = algebraMap F E ϖ * (w - algebraMap F E c) := by
      rw [val_inclUnits, hav, mul_sub, hw, map_add, map_one, map_mul, hz]
      field_simp
      ring
    have hd : (u : E) - (inclUnits F E a : E) ∈ ordBall E (2 * m + 1) := by
      rw [hdiff]
      have := mul_mem_ordBall_add (mem_ordBall_of_le hϖE0 hϖE.ge) hc
      exact this
    have hinv : (((inclUnits F E a)⁻¹ : Eˣ) : E) ∈ ordBall E 0 :=
      mem_ordBall_of_le (Units.ne_zero _) (by
        rw [Units.val_inv_eq_inv_val, ord_inv (Units.ne_zero _), haE.1, neg_zero])
    have h1 := mul_mem_ordBall_add hinv hd
    have h2 : (((inclUnits F E a)⁻¹ : Eˣ) : E) * ((u : E) - (inclUnits F E a : E)) =
        (((inclUnits F E a)⁻¹ * u : Eˣ) : E) - 1 := by
      rw [Units.val_mul, mul_sub, Units.inv_mul]
    rw [h2, zero_add] at h1
    exact_mod_cast h1

end Norm

section Surjective

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [Algebra F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **Characters that factor through the norm on a subgroup.** Let $U$ be a subgroup of $E^\times$ and $\xi$ a character of $E^\times$. There is a character $\varphi$ of $F^\times$ with $\xi(u) = \varphi(N_{E/F}(u))$ for $u \in U$ exactly when $\xi$ is trivial on the elements of $U$ of norm $1$. The proof extends a character of $N_{E/F}(U)$ to $F^\times$. -/
theorem exists_factor_iff (U : Subgroup Eˣ) (ξ : Eˣ →* ℂˣ) :
    (∃ φ : Fˣ →* ℂˣ, ∀ u ∈ U, ξ u = φ (normUnits F E u)) ↔
      ∀ u ∈ U, normUnits F E u = 1 → ξ u = 1 := by
  constructor
  · rintro ⟨φ, hφ⟩ u hu h1
    rw [hφ u hu, h1, map_one]
  · intro h
    set N : U →* Fˣ := (normUnits F E).comp U.subtype with hN
    set ξU : U →* ℂˣ := ξ.comp U.subtype with hξU
    have hker : N.ker ≤ ξU.ker := fun x hx => h x x.2 hx
    let f : N.range →* ℂˣ :=
      (QuotientGroup.lift _ ξU hker).comp (QuotientGroup.quotientKerEquivRange N).symm.toMonoidHom
    obtain ⟨φ, hφ⟩ := exists_extend_char _ f
    refine ⟨φ, fun u hu => ?_⟩
    have h1 := hφ ⟨N ⟨u, hu⟩, ⟨u, hu⟩, rfl⟩
    change φ (N ⟨u, hu⟩) = _ at h1
    change ξ u = φ (N ⟨u, hu⟩)
    rw [h1]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    have he : (QuotientGroup.quotientKerEquivRange N).symm ⟨N ⟨u, hu⟩, ⟨u, hu⟩, rfl⟩ =
        ((⟨u, hu⟩ : U) : U ⧸ N.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]
    rfl

/-- **A quadratic equation over $\mathcal{O}_F$.** If $c \in \mathfrak{p}_F$, then $z^2 + z = c$ for some $z \in \mathfrak{p}_F$. This is Hensel's lemma for $X^2 + X - c$ at $X = 0$, since $\mathcal{O}_F$ is complete. -/
theorem exists_sq_add_self_eq {c : F} (hc : c ∈ ordBall F 1) :
    ∃ z : F, z ∈ ordBall F 1 ∧ z ^ 2 + z = c := by
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have _ := isUniformAddGroup_of_addCommGroup (G := F)
  have hcO : c ∈ 𝒪[F] := by
    rw [← SetLike.mem_coe, ← ordBall_zero_eq_integer]
    exact ordBall_anti (by norm_num) hc
  set c' : 𝒪[F] := ⟨c, hcO⟩ with hc'def
  have hc' : c' ∈ 𝓂[F] := (mem_ordBall_one_iff c').1 hc
  obtain ⟨a, ha, ha0⟩ := HenselianRing.is_henselian (I := 𝓂[F])
    (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c' : Polynomial 𝒪[F]) (by monicity!) 0
    (by simpa using neg_mem hc') (by simp)
  refine ⟨a, (mem_ordBall_one_iff a).2 (by simpa using ha0), ?_⟩
  have h1 : a ^ 2 + a - c' = 0 := by simpa using ha
  have h2 := congrArg (fun x : 𝒪[F] => (x : F)) h1
  simp only [ZeroMemClass.coe_zero] at h2
  push_cast at h2
  rw [hc'def] at h2
  linear_combination h2

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- There is $\beta \in E$ with $\beta + \sigma(\beta) = 1$. If $2 \ne 0$, then $\beta = 1/2$. If $2 = 0$, then $\beta = z / (z + \sigma(z))$ for an element $z$ with $\sigma(z) \ne z$. -/
theorem exists_add_galConj_eq_one : ∃ β : E, β + galConj F E β = 1 := by
  by_cases h2 : (2 : E) = 0
  · obtain ⟨z, hz⟩ : ∃ z : E, galConj F E z ≠ z := by
      by_contra hc
      push Not at hc
      exact galConj_ne_one F E (AlgEquiv.ext hc)
    have hd : z + galConj F E z ≠ 0 := by
      intro h
      apply hz
      linear_combination h - z * h2
    refine ⟨z / (z + galConj F E z), ?_⟩
    rw [map_div₀, map_add, galConj_galConj, add_comm (galConj F E z) z, ← add_div,
      div_self hd]
  · refine ⟨2⁻¹, ?_⟩
    rw [map_inv₀, map_ofNat]
    field_simp
    norm_num

/-- **Deep units are norms.** For each $k$ there is $M$ such that each $u \in U^M_F$ is the norm $N_{E/F}(x)$ of some $x \in U^k_E$. The proof chooses $\beta$ with $\beta + \sigma(\beta) = 1$ and solves $N_{E/F}(1 + b \beta) = 1 + b + b^2 N_{E/F}(\beta) = u$ for $b \in F$ with Hensel's lemma. -/
theorem exists_normUnits_eq (k : ℕ) :
    ∃ M : ℕ, ∀ u : Fˣ, u ∈ unitFilt F M → ∃ x : Eˣ, x ∈ unitFilt E k ∧ normUnits F E x = u := by
  obtain ⟨β, hβ⟩ := exists_add_galConj_eq_one (F := F) (E := E)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβ
  set c : F := Algebra.norm F β with hcdef
  have hc : algebraMap F E c = β * galConj F E β := algebraMap_norm_eq_mul β
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact mul_ne_zero hβ0 ((map_ne_zero _).2 hβ0) hc.symm
  have he0 : 0 < ramIdx F E := ramIdx_pos
  set K : ℕ := max k 1 with hK
  set r : ℤ := ord E β
  set s : ℤ := ord F c
  refine ⟨(|s| + |r| + K + 1).toNat, fun u hu => ?_⟩
  set M : ℕ := (|s| + |r| + K + 1).toNat with hMdef
  have hM : (M : ℤ) = |s| + |r| + K + 1 := by
    rw [hMdef, Int.toNat_of_nonneg (by positivity)]
  set t : F := (u : F) - 1 with ht
  have htM : t ∈ ordBall F M := hu.2
  have hct : c * t ∈ ordBall F 1 := by
    have h1 := mul_mem_ordBall_add (mem_ordBall_of_le hc0 (le_refl s)) htM
    have h2 := neg_abs_le s
    have h3 := abs_nonneg r
    exact ordBall_anti (by omega) h1
  obtain ⟨z, hz1, hz⟩ := exists_sq_add_self_eq hct
  obtain ⟨v, hv, hvz⟩ := exists_unitFilt_one_add le_rfl hz1
  set b : F := t * (v⁻¹ : Fˣ) with hb
  have hbM : b ∈ ordBall F M := by
    have hvi : ((v⁻¹ : Fˣ) : F) ∈ ordBall F 0 :=
      mem_ordBall_of_le (Units.ne_zero _) (by
        rw [Units.val_inv_eq_inv_val, ord_inv v.ne_zero, hv.1, neg_zero])
    have := mul_mem_ordBall_add htM hvi
    rwa [add_zero] at this
  have hbt : c * b ^ 2 + b = t := by
    have hv0 : (1 + z) ≠ 0 := by rw [← hvz]; exact v.ne_zero
    rw [hb, Units.val_inv_eq_inv_val, hvz]
    field_simp
    linear_combination (-t) * hz
  clear_value b
  have hy : algebraMap F E b * β ∈ ordBall E K := by
    have h1 : algebraMap F E b ∈ ordBall E (ramIdx F E * M) := by
      by_cases hb0 : b = 0
      · rw [hb0, map_zero]
        exact zero_mem_ordBall _
      · refine mem_ordBall_of_le ((map_ne_zero _).2 hb0) ?_
        rw [ord_algebraMap_eq]
        exact mul_le_mul_of_nonneg_left ((mem_ordBall_of_ne_zero hb0).1 hbM) he0.le
    have h2 := mul_mem_ordBall_add h1 (mem_ordBall_of_le hβ0 (le_refl r))
    refine ordBall_anti ?_ h2
    have h3 : (M : ℤ) ≤ ramIdx F E * M := le_mul_of_one_le_left (by omega) he0
    have := neg_abs_le r
    have := abs_nonneg s
    omega
  obtain ⟨x, hx, hxy⟩ := exists_unitFilt_one_add (le_max_right k 1) hy
  refine ⟨x, unitFilt_anti (le_max_left k 1) hx, ?_⟩
  ext
  apply (algebraMap F E).injective
  rw [val_normUnits, algebraMap_norm_eq_mul, hxy, map_add, map_one, map_mul, AlgEquiv.commutes]
  have hu' : (u : F) = 1 + (c * b ^ 2 + b) := by rw [hbt, ht]; ring
  rw [hu', map_add, map_one, map_add, map_mul, map_pow]
  linear_combination (algebraMap F E b) * hβ - (algebraMap F E b) ^ 2 * hc

/-- **A criterion for smoothness.** If $\varphi$ is a character of $F^\times$ and $\varphi \circ N_{E/F}$ is trivial on some $U^k_E$, then $\varphi$ is smooth. -/
theorem isSmoothChar_of_comp_normUnits {φ : Fˣ →* ℂˣ} {k : ℕ}
    (h : ∀ x ∈ unitFilt E k, φ (normUnits F E x) = 1) : IsSmoothChar F φ := by
  obtain ⟨M, hM⟩ := exists_normUnits_eq (F := F) (E := E) k
  refine (isSmoothChar_iff_exists_unitFilt_le φ).2 ⟨M, fun u hu => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hM u hu
  exact h x hx

end Surjective

section Minimal

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E]

/-- **Minimal pairs** (BH §18). Let $(E/F, \xi)$ be admissible and let $n = \ell(\xi)$ be the level of $\xi$. The pair is minimal when the restriction of $\xi$ to $U^n_E$ does not factor through $N_{E/F}$: there is no character $\varphi$ of $F^\times$ with $\xi(u) = \varphi(N_{E/F}(u))$ for each $u \in U^n_E$. -/
structure IsMinimal (ξ : Eˣ →* ℂˣ) : Prop where
  /-- The character $\xi$ is admissible. -/
  admissible : IsAdmissible F E ξ
  /-- The restriction of $\xi$ to $U^n_E$, with $n = \ell(\xi)$, does not factor through $N_{E/F}$. -/
  not_factor_level : ¬ ∃ φ : Fˣ →* ℂˣ, ∀ u ∈ unitFilt E (level ξ), ξ u = φ (normUnits F E u)

variable {F E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The twist by the trivial character is $\xi$. -/
@[simp]
theorem twistChar_one (ξ : Eˣ →* ℂˣ) : twistChar F E ξ 1 = ξ :=
  MonoidHom.ext fun x => by simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- Two twists are one twist: $(\xi \otimes \chi_E) \otimes \chi'_E = \xi \otimes (\chi \chi')_E$. -/
theorem twistChar_twistChar (ξ : Eˣ →* ℂˣ) (χ χ' : Fˣ →* ℂˣ) :
    twistChar F E (twistChar F E ξ χ) χ' = twistChar F E ξ (χ * χ') :=
  MonoidHom.ext fun x => by simp [mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The twist by $\chi^{-1}$ and then by $\chi$ is $\xi$. -/
theorem twistChar_inv_twistChar (ξ : Eˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) :
    twistChar F E (twistChar F E ξ χ⁻¹) χ = ξ :=
  MonoidHom.ext fun x => by simp

/-- The trivial character is smooth. -/
theorem isSmoothChar_one' : IsSmoothChar F (1 : Fˣ →* ℂˣ) :=
  (isSmoothChar_iff_exists_unitFilt_le 1).2 ⟨0, fun _ _ => rfl⟩

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)]

/-- **Admissible characters are ramified somewhere.** If $(E/F, \xi)$ is admissible, then $\xi$ is not trivial on $U^0_E$. Otherwise $\xi \circ \sigma = \xi$, because $\sigma(x) / x \in U^0_E$ for each $x \in E^\times$, and then $\xi$ factors through $N_{E/F}$. -/
theorem IsAdmissible.not_unitFilt_zero_le_ker {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ) :
    ¬ unitFilt E 0 ≤ ξ.ker := by
  intro h0
  apply h.comp_galConjUnits_ne
  refine MonoidHom.ext fun x => ?_
  have ho : ord E ((x⁻¹ * galConjUnits F E x : Eˣ) : E) = 0 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ord_mul (inv_ne_zero x.ne_zero) (Units.ne_zero _),
      ord_inv x.ne_zero, val_unitsMap, ord_map]
    ring
  have h1 := h0 ⟨ho, sub_one_mem_ordBall_zero (Units.ne_zero _) ho⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
  rw [MonoidHom.comp_apply, ← h1]

/-- An admissible character $\xi$ has level $\ell(\xi)$. -/
theorem IsAdmissible.isLevel_level {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ) :
    IsLevel ξ (level ξ) :=
  LocalGL2.isLevel_level h.smooth h.not_unitFilt_zero_le_ker

/-- **Each admissible pair is a twist of a minimal pair** (BH §18). If $(E/F, \xi)$ is admissible, then $\xi = \xi' \otimes \chi_E$ for a minimal pair $(E/F, \xi')$ and a smooth character $\chi$ of $F^\times$. The proof is by induction on the level $n$ of $\xi$. If $\xi = \varphi \circ N_{E/F}$ on $U^n_E$, then $\varphi$ is smooth, because the elements of a small $U^M_F$ are norms of elements of $U^{n+1}_E$, and $\xi \otimes \varphi^{-1}_E$ has a level less than $n$. -/
theorem IsAdmissible.exists_isMinimal_twistChar {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ) :
    ∃ ξ' : Eˣ →* ℂˣ, IsMinimal F E ξ' ∧
      ∃ χ : Fˣ →* ℂˣ, IsSmoothChar F χ ∧ ξ = twistChar F E ξ' χ := by
  obtain ⟨n, hn⟩ : ∃ n, level ξ = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing ξ with
  | _ n ih =>
  by_cases hmin : IsMinimal F E ξ
  · exact ⟨ξ, hmin, 1, isSmoothChar_one', (twistChar_one ξ).symm⟩
  have hnf : ∃ φ : Fˣ →* ℂˣ, ∀ u ∈ unitFilt E (level ξ), ξ u = φ (normUnits F E u) := by
    by_contra hc
    exact hmin ⟨h, hc⟩
  obtain ⟨φ, hφ⟩ := hnf
  have hl := h.isLevel_level
  have hφs : IsSmoothChar F φ := isSmoothChar_of_comp_normUnits (E := E) (k := level ξ + 1)
    fun x hx => by
      rw [← hφ x (unitFilt_anti (Nat.le_succ _) hx)]
      exact hl.1 hx
  have h₁ : IsAdmissible F E (twistChar F E ξ φ⁻¹) := h.twist (isSmoothChar_inv φ hφs)
  have htriv : unitFilt E (level ξ) ≤ (twistChar F E ξ φ⁻¹).ker := fun u hu => by
    rw [MonoidHom.mem_ker, twistChar_apply, MonoidHom.inv_apply, ← hφ u hu, mul_inv_cancel]
  have hlt : level (twistChar F E ξ φ⁻¹) < n := by
    have hl1 := h₁.isLevel_level
    by_contra hc
    push Not at hc
    exact hl1.2 ((unitFilt_anti (by omega)).trans htriv)
  obtain ⟨ξ', hξ', χ', hχ', he⟩ := ih _ hlt h₁ rfl
  refine ⟨ξ', hξ', χ' * φ, isSmoothChar_mul hχ' hφs, ?_⟩
  rw [← twistChar_twistChar, ← he, twistChar_inv_twistChar]

/-- **Minimal pairs in the ramified case have odd level** (BH §18). Let $E/F$ be tamely and totally ramified and let $(E/F, \xi)$ be minimal. Then the level $n$ of $\xi$ is odd. Suppose $n = 2m$. Each $u \in U^{2m}_E$ is $u = a v$ with $a \in U^m_F$ and $v \in U^{2m+1}_E$. If $N_{E/F}(u) = 1$, then $a^2 = N_{E/F}(v)^{-1} \in U^{m+1}_F$, so $a \in U^{m+1}_F$ since $p \ne 2$, and $u \in U^{2m+1}_E$. Thus $\xi$ is trivial on the elements of $U^n_E$ of norm $1$, and $\xi$ on $U^n_E$ factors through $N_{E/F}$. -/
theorem IsMinimal.odd_level {ξ : Eˣ →* ℂˣ} (hξ : IsMinimal F E ξ) (ht : IsTameQuadratic F E)
    (hr : IsTotallyRamifiedExt F E) : Odd (level ξ) := by
  have h2 : (2 : 𝓀[F]) ≠ 0 := ht.resolve_right hr.not_isUnramifiedExt
  obtain ⟨hl, hl1⟩ := hξ.admissible.isLevel_level_of_ramified hr
  by_contra hodd
  obtain ⟨m, hm⟩ : ∃ m, level ξ = 2 * m := by
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    exact ⟨m, by omega⟩
  have hm1 : 1 ≤ m := by omega
  apply hξ.not_factor_level
  rw [exists_factor_iff]
  intro u hu hNu
  rw [hm] at hu
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_inclUnits_mul hr hm1 hu
  have hNv : normUnits F E v ∈ unitFilt F (m + 1) :=
    normUnits_mem_unitFilt_of_lt hv (by rw [isTotallyRamifiedExt_iff_ramIdx.1 hr]; push_cast; omega)
  have ha2 : a ^ 2 ∈ unitFilt F (m + 1) := by
    rw [map_mul, normUnits_inclUnits] at hNu
    rw [eq_inv_of_mul_eq_one_left hNu]
    exact inv_mem hNv
  have haE := inclUnits_mem_unitFilt (E := E) hr (mem_unitFilt_succ_of_sq h2 hm1 ha ha2)
  have hmem : inclUnits F E a * v ∈ unitFilt E (level ξ + 1) := by
    rw [hm]
    exact mul_mem (unitFilt_anti (by omega) haE) hv
  exact hl.1 hmem

end Minimal

section Bundled

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

namespace AdmissiblePair

/-- **Minimal pairs** (BH §18): the admissible pair $(E/F, \xi)$ is minimal in the sense of `Langlands.LocalGL2.IsMinimal`. -/
def IsMinimal (P : AdmissiblePair F) : Prop :=
  LocalGL2.IsMinimal F P.ext.E P.ξ

/-- **Each admissible pair is a twist of a minimal pair** (BH §18). For each admissible pair $(E/F, \xi)$ there are a minimal pair $(E/F, \xi')$ and a smooth character $\chi$ of $F^\times$ with $(E/F, \xi) \cong (E/F, \xi' \otimes \chi_E)$. -/
theorem exists_isMinimal_iso_twist (P : AdmissiblePair F) :
    ∃ Q : AdmissiblePair F, Q.IsMinimal ∧
      ∃ (χ : Fˣ →* ℂˣ) (hχ : IsSmoothChar F χ), P.Iso (Q.twist χ hχ) := by
  obtain ⟨ξ', hξ', χ, hχ, he⟩ := P.admissible.exists_isMinimal_twistChar
  refine ⟨⟨P.ext, ξ', hξ'.admissible⟩, hξ', χ, hχ, AlgEquiv.refl, MonoidHom.ext fun x => ?_⟩
  rw [MonoidHom.comp_apply, he]
  exact congrArg (twistChar F P.ext.E ξ' χ) (Units.ext rfl)

/-- **Minimal pairs in the ramified case have odd level** (BH §18). If $(E/F, \xi)$ is a minimal pair and $E/F$ is not unramified, then the level of $\xi$ is odd. -/
theorem IsMinimal.odd_level {P : AdmissiblePair F} (hP : P.IsMinimal)
    (hr : ¬ IsUnramifiedExt F P.ext.E) : Odd (level P.ξ) :=
  LocalGL2.IsMinimal.odd_level hP P.ext.tame (isTotallyRamifiedExt_of_not_isUnramifiedExt hr)

end AdmissiblePair

end Bundled

section Level

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- If $\chi$ has level $n$, then $\ell(\chi) = n$. -/
theorem IsLevel.level_eq {χ : Kˣ →* ℂˣ} {n : ℕ} (h : IsLevel χ n) : level χ = n := by
  classical
  have hP : ∃ n, unitFilt K (n + 1) ≤ χ.ker := ⟨n, h.1⟩
  rw [show level χ = Nat.find hP from dite_eq_left hP]
  refine le_antisymm (Nat.find_min' hP h.1) ?_
  by_contra hlt
  push Not at hlt
  exact h.2 ((unitFilt_anti (by omega)).trans (Nat.find_spec hP))

/-- If $\xi$ has level $n$ and $\psi$ is trivial on $U^n_K$, then $\xi \psi$ has level $n$. -/
theorem IsLevel.mul_of_le_ker {ξ ψ : Kˣ →* ℂˣ} {n : ℕ} (hξ : IsLevel ξ n)
    (hψ : unitFilt K n ≤ ψ.ker) : IsLevel (ξ * ψ) n := by
  refine ⟨fun x hx => ?_, fun hle => hξ.2 fun x hx => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hξ.1 hx,
      hψ (unitFilt_anti (Nat.le_succ n) hx), mul_one]
  · have h1 := hle hx
    rwa [MonoidHom.mem_ker, MonoidHom.mul_apply, hψ hx, mul_one] at h1

/-- **The level of a product.** If $\xi$ has level $m$, $\psi$ has level $n$ and $m \ne n$, then $\xi \psi$ has level $\max(m, n)$. -/
theorem IsLevel.mul_of_ne {ξ ψ : Kˣ →* ℂˣ} {m n : ℕ} (hξ : IsLevel ξ m) (hψ : IsLevel ψ n)
    (h : m ≠ n) : IsLevel (ξ * ψ) (max m n) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [max_eq_right h.le, show ξ * ψ = ψ * ξ from MonoidHom.ext fun x => mul_comm _ _]
    exact hψ.mul_of_le_ker ((unitFilt_anti h).trans hξ.1)
  · rw [max_eq_left h.le]
    exact hξ.mul_of_le_ker ((unitFilt_anti h).trans hψ.1)

/-- **Square roots of units** (BH §18). Let $2 \ne 0$ in the residue field of $K$ and $n \ge 1$. Each $a \in U^n_K$ is $a = b^2$ with $b \in U^n_K$. The proof uses Hensel's lemma for $X^2 - a$ at $X = 1$. -/
theorem exists_sq_eq_of_mem_unitFilt (h2 : (2 : 𝓀[K]) ≠ 0) {n : ℕ} (hn : 1 ≤ n) {a : Kˣ}
    (ha : a ∈ unitFilt K n) : ∃ b : Kˣ, b ∈ unitFilt K n ∧ b ^ 2 = a := by
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  have _ := isUniformAddGroup_of_addCommGroup (G := K)
  have haO : (a : K) ∈ 𝒪[K] := by
    rw [← SetLike.mem_coe, ← ordBall_zero_eq_integer]
    exact mem_ordBall_of_le a.ne_zero ha.1.ge
  set a' : 𝒪[K] := ⟨a, haO⟩ with ha'def
  have ha1 : (1 : 𝒪[K]) - a' ∈ 𝓂[K] := by
    rw [← mem_ordBall_one_iff]
    have h1 := neg_mem_ordBall (ordBall_anti (show (1 : ℤ) ≤ n by exact_mod_cast hn) ha.2)
    rw [neg_sub] at h1
    simpa [ha'def] using h1
  have hunit : IsUnit (Ideal.Quotient.mk 𝓂[K] (2 : 𝒪[K])) := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [map_ofNat]
    exact h2
  obtain ⟨b, hb, hb1⟩ := HenselianRing.is_henselian (I := 𝓂[K])
    (Polynomial.X ^ 2 - Polynomial.C a' : Polynomial 𝒪[K]) (by monicity!) 1
    (by simpa using ha1) (by convert hunit using 2; simp [one_add_one_eq_two])
  have hb2 : (b : K) ^ 2 = a := by
    have h1 : b ^ 2 - a' = 0 := by simpa using hb
    have h2 := congrArg (fun x : 𝒪[K] => (x : K)) h1
    simp only [ZeroMemClass.coe_zero] at h2
    push_cast at h2
    rw [ha'def] at h2
    linear_combination h2
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hb2
    exact a.ne_zero hb2.symm
  set c : Kˣ := Units.mk0 _ hb0 with hc
  have hc2 : c ^ 2 = a := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_mk0, hb2])
  have hc1 : c ∈ unitFilt K 1 := by
    have h1 := (mem_ordBall_one_iff (b - 1)).2 hb1
    push_cast at h1
    have hord : ord K (c : K) = 0 := by
      have := ord_mul hb0 hb0
      rw [← pow_two, hb2, ha.1] at this
      rw [hc, Units.val_mk0]
      omega
    exact ⟨hord, by rwa [hc, Units.val_mk0]⟩
  refine ⟨c, ?_, hc2⟩
  induction n, hn using Nat.le_induction with
  | base => exact hc1
  | succ j hj ih =>
    exact mem_unitFilt_succ_of_sq h2 hj (ih (unitFilt_anti (Nat.le_succ j) ha)) (hc2 ▸ ha)

end Level

section TwistLevel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E] in
/-- **The level of a twist** (BH §18). If $\xi$ has level $m$, $\chi_E = \chi \circ N_{E/F}$ has level $n$ and $m \ne n$, then $\xi \otimes \chi_E$ has level $\max(m, n)$. -/
theorem isLevel_twistChar_of_ne {ξ : Eˣ →* ℂˣ} {χ : Fˣ →* ℂˣ} {m n : ℕ} (hξ : IsLevel ξ m)
    (hχ : IsLevel (χ.comp (normUnits F E)) n) (h : m ≠ n) :
    IsLevel (twistChar F E ξ χ) (max m n) :=
  hξ.mul_of_ne hχ h

/-- **An upper bound for the level of $\chi_E$.** If $\chi$ is trivial on $U^{\ell + 1}_F$, then $\chi_E = \chi \circ N_{E/F}$ is trivial on $U^{e \ell + 1}_E$, with $e = e(E|F)$. -/
theorem unitFilt_le_ker_comp_normUnits {χ : Fˣ →* ℂˣ} {l : ℕ}
    (hχ : unitFilt F (l + 1) ≤ χ.ker) :
    unitFilt E ((ramIdx F E).toNat * l + 1) ≤ (χ.comp (normUnits F E)).ker := by
  intro x hx
  have he0 : 0 < ramIdx F E := ramIdx_pos
  refine hχ (normUnits_mem_unitFilt_of_lt hx ?_)
  have hc : (((ramIdx F E).toNat * l + 1 : ℕ) : ℤ) = ramIdx F E * l + 1 := by
    push_cast [Int.toNat_of_nonneg he0.le]
    ring
  rw [hc]
  push_cast
  linarith

/-- **The level of $\chi_E$ in the ramified case** (BH §18). Let $E/F$ be totally ramified, $2 \ne 0$ in the residue field of $F$, and let $\chi$ have level $\ell \ge 1$. Then $\chi_E = \chi \circ N_{E/F}$ has level $2 \ell$. For $a \in U^\ell_F$ with $\chi(a) \ne 1$, write $a = b^2$ with $b \in U^\ell_F$; then $b \in U^{2\ell}_E$ and $\chi(N_{E/F}(b)) = \chi(a) \ne 1$. -/
theorem isLevel_comp_normUnits_of_ramified (h2 : (2 : 𝓀[F]) ≠ 0)
    (hr : IsTotallyRamifiedExt F E) {χ : Fˣ →* ℂˣ} {l : ℕ} (hχ : IsLevel χ l) (hl : 1 ≤ l) :
    IsLevel (χ.comp (normUnits F E)) (2 * l) := by
  have he : ramIdx F E = 2 := isTotallyRamifiedExt_iff_ramIdx.1 hr
  refine ⟨?_, fun hle => hχ.2 fun a ha => ?_⟩
  · have := unitFilt_le_ker_comp_normUnits (E := E) hχ.1
    rwa [he] at this
  · obtain ⟨b, hb, rfl⟩ := exists_sq_eq_of_mem_unitFilt h2 hl ha
    have h1 := hle (inclUnits_mem_unitFilt hr hb)
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, normUnits_inclUnits] at h1

/-- **The level of a twist in the ramified case** (BH §18). Let $E/F$ be tamely and totally ramified, let $\xi$ have level $m$ and let $\chi$ have level $\ell \ge 1$. If $m \ne 2 \ell$, then $\xi \otimes \chi_E$ has level $\max(m, 2 \ell) = \max(\ell(\xi), e(E|F) \ell(\chi))$. -/
theorem isLevel_twistChar_of_ramified (ht : IsTameQuadratic F E) (hr : IsTotallyRamifiedExt F E)
    {ξ : Eˣ →* ℂˣ} {χ : Fˣ →* ℂˣ} {m l : ℕ} (hξ : IsLevel ξ m) (hχ : IsLevel χ l) (hl : 1 ≤ l)
    (h : m ≠ 2 * l) : IsLevel (twistChar F E ξ χ) (max m (2 * l)) :=
  isLevel_twistChar_of_ne hξ
    (isLevel_comp_normUnits_of_ramified (ht.resolve_right hr.not_isUnramifiedExt) hr hχ hl) h

end TwistLevel

end Langlands.LocalGL2
