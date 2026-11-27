/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.ChainOrders
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Adapted bases for unramified extensions and the element of a minimal pair

Let $F$ be a nonarchimedean local field and $E/F$ a quadratic extension. This file completes two parts of `Langlands/Local/ChainOrders.lean` (BH Chapter 4, §§12 to 13 and §19). First, for unramified $E/F$ it constructs a unit $u \in \mathcal{O}_E^\times$ whose residue class is not in $k_F$, and proves that the basis $(1, u)$ of $E$ over $F$ is adapted to the maximal order $\mathfrak{M}$. So $\mathfrak{A}_E = \mathfrak{M}$, and each $\alpha \in E \setminus F$ with $\mathrm{ord}_E(\alpha) = -n$, $n \ge 1$, gives a simple stratum $(\mathfrak{M}, n, \alpha)$. Second, it proves the duality of the pairing $(x, y) \mapsto \psi(\mathrm{tr}_{E/F}(xy))$ between $\mathfrak{p}^{1-N}_E / \mathfrak{p}^{1-m}_E$ and $\mathfrak{p}^m_E / \mathfrak{p}^N_E$ when $p \ne 2$. From this it gives, for a character $\xi$ of $E^\times$ of level $n \ge 1$, an element $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ on $\mathfrak{p}^{[n/2]+1}_E$. For a minimal pair it proves that the stratum of $\alpha$ is simple.

## Main definitions

* `Langlands.LocalGL2.unramUnit`: for unramified $E/F$, a unit $u$ of $\mathcal{O}_E$ with $\mathrm{ord}_E(u - a) \le 0$ for each $a \in F$.
* `Langlands.LocalGL2.unramBasis`: the basis $(1, u)$ of $E$ over $F$.
* `Langlands.LocalGL2.quotChar`: a character of $G$ that is trivial on $H$, as a character of $G / H$.
* `Langlands.LocalGL2.traceChar`: the character $y \mapsto \psi(\mathrm{tr}_{E/F}(\alpha y))$ of $\mathfrak{p}^m_E$.
* `Langlands.LocalGL2.psiUnit`: the value $\psi(x)$ as a unit of $\mathbb{C}$.

## Main results

* `Langlands.LocalGL2.ord_sub_le_ord_sub_galConj`, `Langlands.LocalGL2.exists_ord_sub_greatest`: for $x \in E \setminus F$, $\mathrm{ord}_E(x - a) \le \mathrm{ord}_E(x - \sigma(x))$ for each $a \in F$, so $x$ has a best approximation in $F$.
* `Langlands.LocalGL2.exists_unit_ord_sub_nonpos`, `Langlands.LocalGL2.unramUnit_sub_not_mem_ordBall_one`: for unramified $E/F$ there is a unit $u$ with $u - a \notin \mathfrak{p}_E$ for each $a \in \mathcal{O}_F$, that is $f(E|F) = 2$ in an elementwise form.
* `Langlands.LocalGL2.isAdapted_unramBasis`: for unramified $E/F$, the basis $(1, u)$ is adapted to $\mathfrak{M}$.
* `Langlands.LocalGL2.isSimpleStratum_unramBasis`, `Langlands.LocalGL2.exists_isSimpleStratum_unramBasis`: for unramified $E/F$, $n \ge 1$ and $\alpha \in E \setminus F$ with $\mathrm{ord}_E(\alpha) = -n$, the stratum $(\mathfrak{M}, n, \alpha)$ is simple, and such $\alpha$ exist for each $n \ge 1$.
* `Langlands.LocalGL2.trace_mem_ordBall_one`: $\mathrm{tr}_{E/F}(\mathfrak{p}_E) \subseteq \mathfrak{p}_F$.
* `Langlands.LocalGL2.mem_ordBall_of_forall_psi_trace`: the injectivity half of trace duality, for $p \ne 2$.
* `Langlands.LocalGL2.exists_eq_psi_trace`: trace duality, for $p \ne 2$: each character of $\mathfrak{p}^m_E$ that is trivial on $\mathfrak{p}^N_E$ is $\psi(\mathrm{tr}_{E/F}(\alpha \, \cdot))$ for some $\alpha \in \mathfrak{p}^{1-N}_E$.
* `Langlands.LocalGL2.map_mul_eq_of_unitFilt_le_ker`: $y \mapsto \xi(1 + y)$ is additive on $\mathfrak{p}^m_K$ when $\xi$ is trivial on $U^{n+1}_K$ and $n + 1 \le 2m$.
* `Langlands.LocalGL2.exists_alpha_of_unitFilt_le_ker`, `Langlands.LocalGL2.IsLevel.exists_alpha`, `Langlands.LocalGL2.IsAdmissible.exists_alpha`: for $p \ne 2$ and $\xi$ of level $n \ge 1$, there is $\alpha$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for $y \in \mathfrak{p}^{[n/2]+1}_E$.
* `Langlands.LocalGL2.IsMinimal.alpha_not_mem`: for an unramified minimal pair of level $n \ge 1$, each such $\alpha$ is not in $F$.
* `Langlands.LocalGL2.IsMinimal.exists_isSimpleStratum_unram`, `Langlands.LocalGL2.IsMinimal.exists_isSimpleStratum_ram`: a minimal pair of level $n \ge 1$ gives a simple stratum $(\mathfrak{M}, n, \alpha)$ or $(\mathfrak{J}, n, \alpha)$, for $p \ne 2$.

## Implementation notes

The residue degree is not used. For $x \in E \setminus F$ and $a \in F$, the identity $x - \sigma(x) = (x - a) - \sigma(x - a)$ bounds $\mathrm{ord}_E(x - a)$. A best approximation $a_0$ then gives the unit $u = (x - a_0) \varpi_F^{-k}$, and $\mathrm{ord}_E(u - a) \le 0$ for each $a \in F$ is the orthogonality of $(1, u)$. This part needs that $E/F$ is separable, as a hypothesis. Trace duality uses a counting argument: multiplication by $\varpi_E^{1-N-m}$ and the pairing give an injective map from the finite group $\mathfrak{p}^m_E / \mathfrak{p}^N_E$ to its group of characters, and `AddChar.card_eq` says that the two groups have the same number of elements. The injectivity uses the element $1/2 \in \mathcal{O}_F$ with $\mathrm{tr}_{E/F}(1/2) = 1$, so it needs $p \ne 2$. The finiteness of the quotient comes from the compactness of $\mathfrak{p}^m_E$ and the openness of $\mathfrak{p}^N_E$.

## What is still open

* Trace duality for $p = 2$. For unramified $E/F$ it needs an element of $\mathcal{O}_E$ with trace $1$. For wildly ramified $E/F$ the level of $\psi \circ \mathrm{tr}_{E/F}$ is not one, and the statement must use the different.
* The adapted basis for unramified $E/F$ uses the hypothesis `Algebra.IsSeparable F E`. It is automatic for $p \ne 2$, and in general it follows from the fact that inseparable quadratic extensions are ramified, which is not proved here.
* The residue degree $f(E|F)$ as a number, and the identity $e f = 2$.
* The uniqueness of $\alpha$ modulo $\mathfrak{p}^{-[n/2]}_E$ is only proved in the form `mem_ordBall_of_forall_psi_trace`. The facts that the class of $\alpha$ determines the minimal pair up to the rest of the data (BH §19) are open.
* For unramified minimal pairs, the stronger condition $\alpha \notin F + \mathfrak{p}^{1-n}_E$ is not proved. Here only $\alpha \notin F$ is proved, which is the condition of `Langlands.LocalGL2.IsSimpleStratum`.
* The uniqueness and conjugacy of chain orders, and the intertwining and induction of simple strata (BH Chapter 4, §§14 to 16).

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, Chapter 4 (§§12 to 13) and §§18 to 19.
-/

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel ChainOrder

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- An element $x \in E$ is in $F$ exactly when $\sigma(x) = x$. -/
theorem galConj_ne_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    galConj F E x ≠ x := by
  intro h
  apply hx
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  rcases eq_one_or_eq_galConj F E τ with rfl | rfl
  · rfl
  · exact h

/-- **The distance to $F$ is bounded.** If $x \in E \setminus F$ and $a \in F$, then $x - a \ne 0$ and $\mathrm{ord}_E(x - a) \le \mathrm{ord}_E(x - \sigma(x))$, because $x - \sigma(x) = (x - a) - \sigma(x - a)$. -/
theorem ord_sub_le_ord_sub_galConj {x : E} (hx : x ∉ Set.range (algebraMap F E)) (a : F) :
    x - algebraMap F E a ≠ 0 ∧ ord E (x - algebraMap F E a) ≤ ord E (x - galConj F E x) := by
  have hw : x - algebraMap F E a ≠ 0 := by
    intro h
    exact hx ⟨a, (sub_eq_zero.1 h).symm⟩
  refine ⟨hw, ?_⟩
  have hd : x - galConj F E x ≠ 0 := sub_ne_zero.2 (galConj_ne_of_not_mem hx).symm
  have h1 : x - algebraMap F E a ∈ ordBall E (ord E (x - algebraMap F E a)) :=
    mem_ordBall_of_le hw le_rfl
  have h2 : galConj F E (x - algebraMap F E a) ∈ ordBall E (ord E (x - algebraMap F E a)) :=
    (map_mem_ordBall_iff _ _ _).2 h1
  have he : x - galConj F E x =
      (x - algebraMap F E a) + -(galConj F E (x - algebraMap F E a)) := by
    rw [map_sub, AlgEquiv.commutes]
    ring
  have h3 : x - galConj F E x ∈ ordBall E (ord E (x - algebraMap F E a)) := by
    rw [he]
    exact add_mem_ordBall h1 (neg_mem_ordBall h2)
  exact (mem_ordBall_of_ne_zero hd).1 h3

/-- For $x \in E \setminus F$ there is a best approximation $a_0 \in F$: $\mathrm{ord}_E(x - a) \le \mathrm{ord}_E(x - a_0)$ for each $a \in F$. -/
theorem exists_ord_sub_greatest {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    ∃ a₀ : F, ∀ a : F, ord E (x - algebraMap F E a) ≤ ord E (x - algebraMap F E a₀) := by
  classical
  obtain ⟨k, ⟨a₀, ha₀⟩, hk⟩ := Int.exists_greatest_of_bdd
    (P := fun k => ∃ a : F, ord E (x - algebraMap F E a) = k)
    ⟨ord E (x - galConj F E x), fun k ⟨a, ha⟩ => ha ▸ (ord_sub_le_ord_sub_galConj hx a).2⟩
    ⟨_, 0, rfl⟩
  exact ⟨a₀, fun a => ha₀ ▸ hk _ ⟨a, rfl⟩⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- A quadratic extension has an element that is not in $F$, for example an element $z$ with $\sigma(z) \ne z$. -/
theorem exists_not_mem_range : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  obtain ⟨z, hz⟩ : ∃ z : E, galConj F E z ≠ z := by
    by_contra hc
    push Not at hc
    exact galConj_ne_one F E (AlgEquiv.ext hc)
  refine ⟨z, ?_⟩
  rintro ⟨a, rfl⟩
  exact hz (AlgEquiv.commutes _ a)

/-- **A unit of $E$ far from $F$.** If $E/F$ is unramified, there is $y \in E$ with $\mathrm{ord}_E(y) = 0$ such that $y - a \ne 0$ and $\mathrm{ord}_E(y - a) \le 0$ for each $a \in F$. So the residue class of $y$ is not in $k_F$. The element is $y = (x - a_0) \varpi_F^{-k}$, where $a_0$ is a best approximation of some $x \in E \setminus F$ and $k = \mathrm{ord}_E(x - a_0)$. -/
theorem exists_unit_ord_sub_nonpos (hu : IsUnramifiedExt F E) :
    ∃ y : E, y ≠ 0 ∧ ord E y = 0 ∧
      ∀ a : F, y - algebraMap F E a ≠ 0 ∧ ord E (y - algebraMap F E a) ≤ 0 := by
  obtain ⟨x, hx⟩ := exists_not_mem_range (F := F) (E := E)
  obtain ⟨a₀, ha₀⟩ := exists_ord_sub_greatest hx
  set k := ord E (x - algebraMap F E a₀) with hk
  have hw := (ord_sub_le_ord_sub_galConj hx a₀).1
  set π : E := algebraMap F E (unif F : F) with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero _).2 (unif F).ne_zero
  have hπo : ord E π = 1 := by rw [hπ, hu, ord_unif]
  have hzk : ord E (π ^ (-k)) = -k := by rw [ord_zpow, hπo, mul_one]
  have hz0 : π ^ (-k) ≠ 0 := zpow_ne_zero _ hπ0
  refine ⟨(x - algebraMap F E a₀) * π ^ (-k), mul_ne_zero hw hz0, ?_, fun b => ?_⟩
  · rw [ord_mul hw hz0, hzk, ← hk, add_neg_cancel]
  · have he : (x - algebraMap F E a₀) * π ^ (-k) - algebraMap F E b =
        (x - algebraMap F E (a₀ + b * (unif F : F) ^ k)) * π ^ (-k) := by
      rw [map_add, map_mul, map_zpow₀, ← hπ]
      have : π ^ k * π ^ (-k) = 1 := by rw [← zpow_add₀ hπ0, add_neg_cancel, zpow_zero]
      linear_combination (algebraMap F E b) * this
    obtain ⟨h1, h2⟩ := ord_sub_le_ord_sub_galConj hx (a₀ + b * (unif F : F) ^ k)
    rw [he]
    refine ⟨mul_ne_zero h1 hz0, ?_⟩
    rw [ord_mul h1 hz0, hzk]
    have := ha₀ (a₀ + b * (unif F : F) ^ k)
    omega

variable (F E) in
/-- For unramified $E/F$, a chosen unit $u \in \mathcal{O}_E^\times$ with $\mathrm{ord}_E(u - a) \le 0$ for each $a \in F$. Its residue class generates $k_E$ over $k_F$. -/
noncomputable def unramUnit (hu : IsUnramifiedExt F E) : E :=
  (exists_unit_ord_sub_nonpos hu).choose

/-- The unit $u$ is not $0$. -/
theorem unramUnit_ne_zero (hu : IsUnramifiedExt F E) : unramUnit F E hu ≠ 0 :=
  (exists_unit_ord_sub_nonpos hu).choose_spec.1

/-- The unit $u$ has order $0$. -/
theorem ord_unramUnit (hu : IsUnramifiedExt F E) : ord E (unramUnit F E hu) = 0 :=
  (exists_unit_ord_sub_nonpos hu).choose_spec.2.1

/-- For each $a \in F$, $u - a \ne 0$ and $\mathrm{ord}_E(u - a) \le 0$. -/
theorem ord_unramUnit_sub (hu : IsUnramifiedExt F E) (a : F) :
    unramUnit F E hu - algebraMap F E a ≠ 0 ∧ ord E (unramUnit F E hu - algebraMap F E a) ≤ 0 :=
  (exists_unit_ord_sub_nonpos hu).choose_spec.2.2 a

/-- The unit $u$ is not in $F$. -/
theorem unramUnit_not_mem (hu : IsUnramifiedExt F E) :
    unramUnit F E hu ∉ Set.range (algebraMap F E) := by
  rintro ⟨a, ha⟩
  exact (ord_unramUnit_sub hu a).1 (by rw [ha, sub_self])

/-- **The residue degree is $2$.** For unramified $E/F$, the residue class of $u$ is not in $k_F$: for each $a \in \mathcal{O}_F$, $u - a \notin \mathfrak{p}_E$. -/
theorem unramUnit_sub_not_mem_ordBall_one (hu : IsUnramifiedExt F E) {a : F}
    (_ha : a ∈ ordBall F 0) : unramUnit F E hu - algebraMap F E a ∉ ordBall E 1 := by
  obtain ⟨h0, hle⟩ := ord_unramUnit_sub hu a
  rw [mem_ordBall_of_ne_zero h0]
  omega

/-- The elements $1$ and $u$ are linearly independent over $F$. -/
theorem linearIndependent_one_unramUnit (hu : IsUnramifiedExt F E) :
    LinearIndependent F ![(1 : E), unramUnit F E hu] := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  apply unramUnit_not_mem hu
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩

variable (F E) in
/-- For unramified $E/F$, the basis $(1, u)$ of $E$ over $F$. -/
noncomputable def unramBasis (hu : IsUnramifiedExt F E) : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank' ![(1 : E), unramUnit F E hu]
    (linearIndependent_one_unramUnit hu)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])

/-- The vectors of the basis $(1, u)$. -/
theorem unramBasis_apply (hu : IsUnramifiedExt F E) (i : Fin 2) :
    unramBasis F E hu i = ![(1 : E), unramUnit F E hu] i := by
  simp only [unramBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- **Orthogonality of $(1, u)$.** If $c_1 \ne 0$, then $c_0 + c_1 u \ne 0$ and $\mathrm{ord}_E(c_0 + c_1 u) \le \mathrm{ord}_E(c_1)$. The reason is $c_0 + c_1 u = c_1 (u + c_0 / c_1)$. -/
theorem ord_add_smul_unramUnit_le (hu : IsUnramifiedExt F E) (c₀ : F) {c₁ : F} (h₁ : c₁ ≠ 0) :
    c₀ • (1 : E) + c₁ • unramUnit F E hu ≠ 0 ∧
      ord E (c₀ • (1 : E) + c₁ • unramUnit F E hu) ≤ ord E (algebraMap F E c₁) := by
  have hc : algebraMap F E c₁ ≠ 0 := (map_ne_zero _).2 h₁
  obtain ⟨h0, hle⟩ := ord_unramUnit_sub hu (-(c₀ / c₁))
  have he : c₀ • (1 : E) + c₁ • unramUnit F E hu =
      algebraMap F E c₁ * (unramUnit F E hu - algebraMap F E (-(c₀ / c₁))) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_neg, map_div₀]
    field_simp
    ring
  rw [he]
  refine ⟨mul_ne_zero hc h0, ?_⟩
  rw [ord_mul hc h0]
  omega

/-- **The adapted basis for unramified $E/F$.** For unramified $E/F$, the basis $(1, u)$ is adapted to the maximal order. So $\mathfrak{A}_E = \mathfrak{M}$ in this basis. -/
theorem isAdapted_unramBasis (hu : IsUnramifiedExt F E) :
    IsAdapted maximal (unramBasis F E hu) where
  ramIdx_eq := by rw [isUnramifiedExt_iff_ramIdx.1 hu]; rfl
  ord_basis := ⟨0, fun i => by
    fin_cases i <;> simp [unramBasis_apply, wt, ord_one, ord_unramUnit]⟩
  orth := by
    intro c N
    simp only [unramBasis_apply, Fin.sum_univ_two, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · intro h
      by_cases h₁ : c 1 = 0
      · rw [h₁, zero_smul, add_zero] at h
        rw [h₁, zero_smul]
        exact ⟨h, zero_mem_ordBall _⟩
      obtain ⟨h0, hle⟩ := ord_add_smul_unramUnit_le hu (c 0) h₁
      have hN := (mem_ordBall_of_ne_zero h0).1 h
      have hcu : c 1 • unramUnit F E hu ∈ ordBall E N := by
        have hc : algebraMap F E (c 1) ≠ 0 := (map_ne_zero _).2 h₁
        rw [Algebra.smul_def]
        apply mem_ordBall_of_le (mul_ne_zero hc (unramUnit_ne_zero hu))
        rw [ord_mul hc (unramUnit_ne_zero hu), ord_unramUnit]
        omega
      refine ⟨?_, hcu⟩
      have := add_mem_ordBall h (neg_mem_ordBall hcu)
      rwa [add_neg_cancel_right] at this
    · rintro ⟨h0, h1⟩
      exact add_mem_ordBall h0 h1

/-- **Unramified simple strata.** For unramified $E/F$, $n \ge 1$ and $\alpha \in E \setminus F$ with $\mathrm{ord}_E(\alpha) = -n$, the stratum $(\mathfrak{M}, n, \alpha)$ given by the basis $(1, u)$ is simple. -/
theorem isSimpleStratum_unramBasis (hu : IsUnramifiedExt F E) {n : ℕ} (hn : 1 ≤ n) {α : E}
    (hord : ord E α = -n) (hα : α ∉ Set.range (algebraMap F E)) :
    IsSimpleStratum maximal n (Algebra.leftMulMatrix (unramBasis F E hu) α) :=
  (isAdapted_unramBasis hu).isSimpleStratum hn (by simpa [e] using isCoprime_one_right) hord hα

/-- For unramified $E/F$ and each $n \ge 1$, the element $\alpha = u \varpi_F^{-n}$ has $\mathrm{ord}_E(\alpha) = -n$ and gives a simple stratum $(\mathfrak{M}, n, \alpha)$. -/
theorem exists_isSimpleStratum_unramBasis (hu : IsUnramifiedExt F E) {n : ℕ} (hn : 1 ≤ n) :
    ∃ α : E, ord E α = -n ∧
      IsSimpleStratum maximal n (Algebra.leftMulMatrix (unramBasis F E hu) α) := by
  set π : F := (unif F : F) ^ (-(n : ℤ)) with hπ
  have hπ0 : π ≠ 0 := zpow_ne_zero _ (unif F).ne_zero
  have hπ0' : algebraMap F E π ≠ 0 := (map_ne_zero _).2 hπ0
  have hord : ord E (unramUnit F E hu * algebraMap F E π) = -n := by
    rw [ord_mul (unramUnit_ne_zero hu) hπ0', ord_unramUnit, hu, hπ, ord_zpow, ord_unif]
    ring
  refine ⟨_, hord, isSimpleStratum_unramBasis hu hn hord ?_⟩
  rintro ⟨a, ha⟩
  apply unramUnit_not_mem hu
  refine ⟨a / π, ?_⟩
  rw [map_div₀, ha, mul_div_cancel_right₀ _ hπ0']

end Unramified

section Trace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The trace is $\mathrm{tr}_{E/F}(z) = z + \sigma(z)$. -/
theorem algebraMap_trace_eq_add [Algebra.IsSeparable F E] (z : E) :
    algebraMap F E (Algebra.trace F E z) = z + galConj F E z := by
  classical
  rw [trace_eq_sum_automorphisms]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, galConj F E} := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact eq_one_or_eq_galConj F E τ
  rw [huniv, Finset.sum_pair (galConj_ne_one F E).symm]
  rfl

/-- The trace maps $\mathfrak{p}_E$ into $\mathfrak{p}_F$. -/
theorem trace_mem_ordBall_one [Algebra.IsSeparable F E] {z : E} (hz : z ∈ ordBall E 1) :
    Algebra.trace F E z ∈ ordBall F 1 := by
  by_cases ht : Algebra.trace F E z = 0
  · rw [ht]
    exact zero_mem_ordBall _
  have h1 : algebraMap F E (Algebra.trace F E z) ∈ ordBall E 1 := by
    rw [algebraMap_trace_eq_add]
    exact add_mem_ordBall hz ((map_mem_ordBall_iff _ _ _).2 hz)
  rw [mem_ordBall_of_ne_zero ((map_ne_zero _).2 ht), ord_algebraMap_eq] at h1
  apply mem_ordBall_of_le ht
  have := ramIdx_pos (F := F) (E := E)
  by_contra hc
  push Not at hc
  nlinarith

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- For $a \in F$, $\mathrm{tr}_{E/F}(a) = 2a$. -/
theorem trace_algebraMap_eq_two_mul (a : F) : Algebra.trace F E (algebraMap F E a) = 2 * a := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num

/-- A value of a character with values in $\mathbb{C}$ is not $0$. -/
theorem addChar_ne_zero {A : Type*} [AddGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := by
  have h : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact left_ne_zero_of_mul_eq_one h

/-- **The injectivity half of trace duality.** Let $2 \ne 0$ in $k_F$ and let $\psi$ have level one. If $\psi(\mathrm{tr}_{E/F}(\delta y)) = 1$ for each $y \in \mathfrak{p}^m_E$, then $\delta \in \mathfrak{p}^{1-m}_E$. The proof takes $c \in \mathcal{O}_F$ with $\psi(c) \ne 1$ and $y = (c/2) \delta^{-1}$. -/
theorem mem_ordBall_of_forall_psi_trace (h2 : (2 : 𝓀[F]) ≠ 0) {ψ : AddChar F ℂ}
    (hψ : IsConductor ψ (-1)) {δ : E} {m : ℤ}
    (h : ∀ y ∈ ordBall E m, ψ (Algebra.trace F E (δ * y)) = 1) : δ ∈ ordBall E (1 - m) := by
  by_contra hδ
  have hδ0 : δ ≠ 0 := fun h0 => hδ (h0 ▸ zero_mem_ordBall _)
  have hδo : ord E δ ≤ -m := by
    by_contra hc
    exact hδ (mem_ordBall_of_le hδ0 (by omega))
  obtain ⟨c, hc, hψc⟩ := hψ.nontrivial
  have hc0 : c ∈ ordBall F 0 := by simpa using hc
  have h20 : (2 : F) ≠ 0 := two_ne_zero_of_residue h2
  have hy : algebraMap F E (c / 2) * δ⁻¹ ∈ ordBall E m := by
    by_cases hc' : c = 0
    · simp [hc', zero_mem_ordBall]
    have hc2 : c / 2 ≠ 0 := div_ne_zero hc' h20
    apply mem_ordBall_of_le (mul_ne_zero ((map_ne_zero _).2 hc2) (inv_ne_zero hδ0))
    rw [ord_mul ((map_ne_zero _).2 hc2) (inv_ne_zero hδ0), ord_inv hδ0, ord_algebraMap_eq,
      div_eq_mul_inv, ord_mul hc' (inv_ne_zero h20), ord_inv h20, ord_two_eq_zero h2]
    have h3 := (mem_ordBall_of_ne_zero hc').1 hc0
    have h4 := ramIdx_pos (F := F) (E := E)
    nlinarith
  apply hψc
  have := h _ hy
  rwa [mul_comm, mul_assoc, inv_mul_cancel₀ hδ0, mul_one, trace_algebraMap_eq_two_mul,
    mul_div_cancel₀ _ h20] at this

/-- A character $f$ of $G$ that is trivial on $H$, as a character of $G / H$. -/
def quotChar {G : Type*} [AddCommGroup G] {H : AddSubgroup G} (f : AddChar G ℂ)
    (hf : ∀ h ∈ H, f h = 1) : AddChar (G ⧸ H) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift H (AddChar.toAddMonoidHomEquiv f)
    (fun h hh => by rw [AddMonoidHom.mem_ker, AddChar.toAddMonoidHomEquiv_apply, hf h hh]; rfl))

/-- The value of `quotChar` on a class is the value of $f$. -/
@[simp]
theorem quotChar_mk {G : Type*} [AddCommGroup G] {H : AddSubgroup G} (f : AddChar G ℂ)
    (hf : ∀ h ∈ H, f h = 1) (a : G) : quotChar f hf (QuotientAddGroup.mk a) = f a :=
  rfl

variable (F) in
/-- The character $y \mapsto \psi(\mathrm{tr}_{E/F}(\alpha y))$ of the group $\mathfrak{p}^m_E$. -/
noncomputable def traceChar (ψ : AddChar F ℂ) (m : ℤ) (α : E) :
    AddChar (ordBallAddSubgroup (K := E) m) ℂ where
  toFun y := ψ (Algebra.trace F E (α * y))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [AddSubgroup.coe_add, mul_add, map_add, AddChar.map_add_eq_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E] in
/-- The value of `traceChar`. -/
@[simp]
theorem traceChar_apply (ψ : AddChar F ℂ) (m : ℤ) (α : E) (y : ordBallAddSubgroup (K := E) m) :
    traceChar F ψ m α y = ψ (Algebra.trace F E (α * y)) :=
  rfl

/-- **Trace duality** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one, and let $\chi$ be a character of $\mathfrak{p}^m_E$ that is trivial on $\mathfrak{p}^N_E$. Then there is $\alpha \in \mathfrak{p}^{1-N}_E$ with $\chi(y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^m_E$. The proof shows that $z \mapsto \psi(\mathrm{tr}_{E/F}(\varpi_E^{1-N-m} z \, \cdot))$ is an injective map from the finite group $\mathfrak{p}^m_E / \mathfrak{p}^N_E$ to its group of characters, which has the same number of elements. -/
theorem exists_eq_psi_trace (h2 : (2 : 𝓀[F]) ≠ 0) {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1))
    (m N : ℤ) (χ : AddChar (ordBallAddSubgroup (K := E) m) ℂ)
    (hχ : ∀ y : ordBallAddSubgroup (K := E) m, (y : E) ∈ ordBall E N → χ y = 1) :
    ∃ α ∈ ordBall E (1 - N), ∀ y : ordBallAddSubgroup (K := E) m,
      χ y = ψ (Algebra.trace F E (α * y)) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  let G := ordBallAddSubgroup (K := E) m
  let H : AddSubgroup G := (ordBallAddSubgroup (K := E) N).addSubgroupOf G
  have hH : ∀ y : G, y ∈ H ↔ (y : E) ∈ ordBall E N := fun y => AddSubgroup.mem_addSubgroupOf
  set γ : E := (unif E : E) ^ (1 - N - m) with hγ
  have hγ0 : γ ≠ 0 := zpow_ne_zero _ (unif E).ne_zero
  have hγo : ord E γ = 1 - N - m := by rw [hγ, ord_zpow, ord_unif, mul_one]
  have hγb : γ ∈ ordBall E (1 - N - m) := mem_ordBall_of_le hγ0 hγo.ge
  have hpair : ∀ z y : E, z ∈ ordBall E N → y ∈ ordBall E m →
      ψ (Algebra.trace F E (γ * z * y)) = 1 := by
    intro z y hz hy
    refine hψ.trivial _ ?_
    simp only [neg_neg]
    refine trace_mem_ordBall_one (mem_ordBall_congr ?_ (mul_mem_ordBall_add
      (mul_mem_ordBall_add hγb hz) hy))
    ring
  have hwell : ∀ z : G, ∀ h ∈ H, traceChar F ψ m (γ * z) h = 1 := by
    intro z h hh
    rw [traceChar_apply, show γ * (z : E) * h = γ * h * z by ring]
    exact hpair _ _ ((hH h).1 hh) z.2
  let Ψ : G ⧸ H → AddChar (G ⧸ H) ℂ := fun q => Quotient.liftOn' q
    (fun z => quotChar (traceChar F ψ m (γ * z)) (hwell z)) (by
      intro a b hab
      rw [QuotientAddGroup.leftRel_apply] at hab
      refine DFunLike.ext _ _ fun q => ?_
      induction q using QuotientAddGroup.induction_on with | H y => ?_
      show ψ (Algebra.trace F E (γ * a * y)) = ψ (Algebra.trace F E (γ * b * y))
      have hb : γ * (b : E) * y = γ * a * y + γ * ((-a + b : G) : E) * y := by
        push_cast
        ring
      rw [hb, map_add, AddChar.map_add_eq_mul, hpair _ _ ((hH _).1 hab) y.2, mul_one])
  have hΨ : ∀ z y : G, Ψ (QuotientAddGroup.mk z) (QuotientAddGroup.mk y) =
      ψ (Algebra.trace F E (γ * z * y)) := fun z y => rfl
  have hinj : Function.Injective Ψ := by
    intro q₁ q₂ hq
    induction q₁ using QuotientAddGroup.induction_on with | H a => ?_
    induction q₂ using QuotientAddGroup.induction_on with | H b => ?_
    have hall : ∀ y ∈ ordBall E m, ψ (Algebra.trace F E (γ * ((b : E) - a) * y)) = 1 := by
      intro y hy
      have h1 := congrArg (fun f : AddChar (G ⧸ H) ℂ => f (QuotientAddGroup.mk ⟨y, hy⟩)) hq
      simp only [hΨ] at h1
      have hb : γ * (b : E) * y = γ * a * y + γ * ((b : E) - a) * y := by ring
      rw [hb, map_add, AddChar.map_add_eq_mul] at h1
      exact (mul_eq_left₀ (addChar_ne_zero ψ _)).1 h1.symm
    have h1 := mem_ordBall_of_forall_psi_trace h2 hψ hall
    rw [mul_mem_ordBall_iff hγ0, hγo] at h1
    rw [QuotientAddGroup.eq, hH]
    have h3 : ((-a + b : G) : E) = (b : E) - a := by
      push_cast
      ring
    rw [h3]
    exact mem_ordBall_congr (by ring) h1
  have : CompactSpace G := isCompact_iff_compactSpace.mp (isCompact_ordBall m)
  have hopen : IsOpen (H : Set G) := by
    rw [AddSubgroup.coe_addSubgroupOf]
    exact (isOpen_ordBall N).preimage continuous_subtype_val
  have : Finite (G ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hopen
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hbij : Function.Bijective Ψ :=
    (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨q, hq⟩ := hbij.2 (quotChar χ (fun h hh => hχ h ((hH h).1 hh)))
  induction q using QuotientAddGroup.induction_on with | H z => ?_
  refine ⟨γ * z, ?_, fun y => ?_⟩
  · exact mem_ordBall_congr (by ring) (mul_mem_ordBall_add hγb z.2)
  · have h1 := congrArg (fun f : AddChar (G ⧸ H) ℂ => f (QuotientAddGroup.mk y)) hq
    simp only [hΨ, quotChar_mk] at h1
    exact h1.symm

end Trace

section Characters

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- If $n \ge 1$, $y \in \mathfrak{p}^n_K$ and $u = 1 + y$, then $u \in U^n_K$. -/
theorem mem_unitFilt_of_eq_one_add {n : ℕ} (hn : 1 ≤ n) {y : K} (hy : y ∈ ordBall K n) {u : Kˣ}
    (hu : (u : K) = 1 + y) : u ∈ unitFilt K n := by
  obtain ⟨x, hx, hxe⟩ := exists_unitFilt_one_add hn hy
  have : x = u := Units.ext (hxe.trans hu.symm)
  exact this ▸ hx

/-- **The character $\xi(1 + y)$ is additive.** Let $\xi$ be trivial on $U^{n+1}_K$, let $m \ge 1$ with $n + 1 \le 2m$, and let $y, z \in \mathfrak{p}^m_K$. Then $\xi(1 + y) \xi(1 + z) = \xi(1 + y + z)$, because $(1 + y)(1 + z)(1 + y + z)^{-1} = 1 + yz (1 + y + z)^{-1} \in U^{n+1}_K$. -/
theorem map_mul_eq_of_unitFilt_le_ker {ξ : Kˣ →* ℂˣ} {n m : ℕ} (hm : 1 ≤ m) (hmn : n + 1 ≤ 2 * m)
    (hξ : unitFilt K (n + 1) ≤ ξ.ker) {y z : K} (hy : y ∈ ordBall K m) (hz : z ∈ ordBall K m)
    {u v w : Kˣ} (hu : (u : K) = 1 + y) (hv : (v : K) = 1 + z) (hw : (w : K) = 1 + (y + z)) :
    ξ u * ξ v = ξ w := by
  have hu' := mem_unitFilt_of_eq_one_add hm hy hu
  have hv' := mem_unitFilt_of_eq_one_add hm hz hv
  have hw' := mem_unitFilt_of_eq_one_add hm (add_mem_ordBall hy hz) hw
  have hw0 : (w : K) ≠ 0 := w.ne_zero
  have hmem : u * v * w⁻¹ ∈ unitFilt K (n + 1) := by
    rw [mem_unitFilt]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        ord_mul (mul_ne_zero u.ne_zero v.ne_zero) (inv_ne_zero hw0), ord_mul u.ne_zero v.ne_zero,
        ord_inv hw0, hu'.1, hv'.1, hw'.1]
      simp
    · have he : ((u * v * w⁻¹ : Kˣ) : K) - 1 = y * z * (w : K)⁻¹ := by
        rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
        have : (u : K) * v - w = y * z := by rw [hu, hv, hw]; ring
        field_simp
        linear_combination this
      rw [he]
      have hwi : (w : K)⁻¹ ∈ ordBall K 0 :=
        mem_ordBall_of_le (inv_ne_zero hw0) (by rw [ord_inv hw0, hw'.1, neg_zero])
      refine ordBall_anti ?_ (mul_mem_ordBall_add (mul_mem_ordBall_add hy hz) hwi)
      push_cast
      omega
  have h1 := hξ hmem
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Characters

section Alpha

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]

/-- **The element $\alpha$ of a character** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one and let $\xi$ be a character of $E^\times$ that is trivial on $U^{n+1}_E$. Then there is $\alpha \in \mathfrak{p}^{-n}_E$ with $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$. -/
theorem exists_alpha_of_unitFilt_le_ker (h2 : (2 : 𝓀[F]) ≠ 0) {ψ : AddChar F ℂ}
    (hψ : IsConductor ψ (-1)) {ξ : Eˣ →* ℂˣ} {n : ℕ} (hξ : unitFilt E (n + 1) ≤ ξ.ker) :
    ∃ α ∈ ordBall E (-n), ∀ y ∈ ordBall E ((n / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ, (u : E) = 1 + y →
      (ξ u : ℂ) = ψ (Algebra.trace F E (α * y)) := by
  have hm1 : 1 ≤ n / 2 + 1 := by omega
  have hmn : n + 1 ≤ 2 * (n / 2 + 1) := by omega
  let G := ordBallAddSubgroup (K := E) ((n / 2 + 1 : ℕ) : ℤ)
  let U : G → Eˣ := fun y => (exists_unitFilt_one_add hm1 y.2).choose
  have hU : ∀ y : G, (U y : E) = 1 + y := fun y => (exists_unitFilt_one_add hm1 y.2).choose_spec.2
  let χ : AddChar G ℂ :=
    { toFun := fun y => (ξ (U y) : ℂ)
      map_zero_eq_one' := by
        have : U 0 = 1 := Units.ext (by rw [hU]; simp)
        simp only [this, map_one, Units.val_one]
      map_add_eq_mul' := fun a b => by
        rw [← Units.val_mul, map_mul_eq_of_unitFilt_le_ker (w := U (a + b)) hm1 hmn hξ a.2 b.2
          (hU a) (hU b) (by rw [hU (a + b)]; push_cast; ring)] }
  obtain ⟨α, hα, hαχ⟩ := exists_eq_psi_trace h2 hψ _ ((n : ℤ) + 1) χ (fun y hy => by
    have hmem := mem_unitFilt_of_eq_one_add (n := n + 1) (by omega) (by exact_mod_cast hy) (hU y)
    have h1 := hξ hmem
    rw [MonoidHom.mem_ker] at h1
    change (ξ (U y) : ℂ) = 1
    rw [h1, Units.val_one])
  refine ⟨α, mem_ordBall_congr (by ring) hα, fun y hy u hu => ?_⟩
  have : u = U ⟨y, hy⟩ := Units.ext (hu.trans (hU ⟨y, hy⟩).symm)
  rw [this]
  exact hαχ ⟨y, hy⟩

/-- **The element $\alpha$ of a character of level $n$** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one and let $\xi$ be a character of $E^\times$ of level $n \ge 1$. Then there is $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$. -/
theorem IsLevel.exists_alpha (h2 : (2 : 𝓀[F]) ≠ 0) {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1))
    {ξ : Eˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n) (hξ : IsLevel ξ n) :
    ∃ α : E, α ≠ 0 ∧ ord E α = -n ∧ ∀ y ∈ ordBall E ((n / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ,
      (u : E) = 1 + y → (ξ u : ℂ) = ψ (Algebra.trace F E (α * y)) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  obtain ⟨α, hα, hαξ⟩ := exists_alpha_of_unitFilt_le_ker h2 hψ hξ.1
  by_cases hα1 : α ∈ ordBall E (1 - n)
  · exfalso
    apply hξ.2
    intro u hu
    rw [MonoidHom.mem_ker]
    have hy : (u : E) - 1 ∈ ordBall E ((n / 2 + 1 : ℕ) : ℤ) :=
      ordBall_anti (by push_cast; omega) hu.2
    have h1 := hαξ _ hy u (by ring)
    have h3 : ψ (Algebra.trace F E (α * ((u : E) - 1))) = 1 := by
      refine hψ.trivial _ ?_
      simp only [neg_neg]
      exact trace_mem_ordBall_one (mem_ordBall_congr (by ring) (mul_mem_ordBall_add hα1 hu.2))
    exact Units.ext (by rw [h1, h3, Units.val_one])
  have hα0 : α ≠ 0 := fun h0 => hα1 (h0 ▸ zero_mem_ordBall _)
  refine ⟨α, hα0, ?_, hαξ⟩
  have h1 := (mem_ordBall_of_ne_zero hα0).1 hα
  have h2 : ¬ 1 - (n : ℤ) ≤ ord E α := fun h => hα1 (mem_ordBall_of_le hα0 h)
  omega

/-- **The element $\alpha$ of an admissible character** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one and let $\xi$ be an admissible character of $E^\times$ of level $n \ge 1$. Then there is $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$. -/
theorem IsAdmissible.exists_alpha (h2 : (2 : 𝓀[F]) ≠ 0) {ψ : AddChar F ℂ}
    (hψ : IsConductor ψ (-1)) {ξ : Eˣ →* ℂˣ} (hξ : IsAdmissible F E ξ) (hn : 1 ≤ level ξ) :
    ∃ α : E, α ≠ 0 ∧ ord E α = -(level ξ : ℤ) ∧
      ∀ y ∈ ordBall E ((level ξ / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ,
        (u : E) = 1 + y → (ξ u : ℂ) = ψ (Algebra.trace F E (α * y)) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  exact hξ.isLevel_level.exists_alpha h2 hψ hn

end Alpha

section MinimalAlpha

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]

omit [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E] in
/-- For unramified $E/F$ and $t \in F$, $t \in \mathfrak{p}^k_E$ exactly when $t \in \mathfrak{p}^k_F$. -/
theorem algebraMap_mem_ordBall_iff (hu : IsUnramifiedExt F E) (t : F) (k : ℤ) :
    algebraMap F E t ∈ ordBall E k ↔ t ∈ ordBall F k := by
  by_cases ht : t = 0
  · simp [ht, zero_mem_ordBall]
  rw [mem_ordBall_of_ne_zero ((map_ne_zero _).2 ht), mem_ordBall_of_ne_zero ht, hu]

/-- The unit $\psi(x)$ of $\mathbb{C}$. -/
noncomputable def psiUnit (ψ : AddChar F ℂ) (x : F) : ℂˣ :=
  Units.mk0 (ψ x) (addChar_ne_zero ψ x)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E]
  [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E] in
/-- **The character $\psi_a$ of $U^n_F$.** Let $\psi$ have level one, $n \ge 1$ and $a \in \mathfrak{p}^{-n}_F$. Then $v \mapsto \psi(a (v - 1))$ is a character of $U^n_F$. -/
theorem exists_psiChar_unitFilt {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1)) {n : ℕ} (hn : 1 ≤ n)
    {a : F} (ha : a ∈ ordBall F (-n)) :
    ∃ φ : unitFilt F n →* ℂˣ, ∀ v : unitFilt F n, φ v = psiUnit ψ (a * (((v : Fˣ) : F) - 1)) := by
  refine ⟨{ toFun := fun v => psiUnit ψ (a * (((v : Fˣ) : F) - 1))
            map_one' := by ext; simp [psiUnit]
            map_mul' := fun v w => ?_ }, fun v => rfl⟩
  ext
  simp only [psiUnit, Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
  have he : a * (((v : Fˣ) : F) * ((w : Fˣ) : F) - 1) = a * (((v : Fˣ) : F) - 1) +
      a * (((w : Fˣ) : F) - 1) + a * (((v : Fˣ) : F) - 1) * (((w : Fˣ) : F) - 1) := by ring
  have h1 : ψ (a * (((v : Fˣ) : F) - 1) * (((w : Fˣ) : F) - 1)) = 1 := by
    refine hψ.trivial _ ?_
    simp only [neg_neg]
    refine ordBall_anti ?_ (mul_mem_ordBall_add (mul_mem_ordBall_add ha v.2.2) w.2.2)
    omega
  rw [he, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, mul_one]

/-- **The element $\alpha$ of a minimal pair is not in $F$.** Let $E/F$ be unramified, let $2 \ne 0$ in $k_F$, let $\psi$ have level one, and let $(E/F, \xi)$ be a minimal pair of level $n \ge 1$. If $\alpha \in \mathfrak{p}^{-n}_E$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$, then $\alpha \notin F$. If $\alpha = a \in F$, then $\xi(u) = \psi(a (N_{E/F}(u) - 1))$ on $U^n_E$, so $\xi$ on $U^n_E$ factors through $N_{E/F}$. -/
theorem IsMinimal.alpha_not_mem (h2 : (2 : 𝓀[F]) ≠ 0) (hu : IsUnramifiedExt F E)
    {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1)) {ξ : Eˣ →* ℂˣ} (hξ : IsMinimal F E ξ)
    (hn : 1 ≤ level ξ) {α : E} (hα : α ∈ ordBall E (-(level ξ : ℤ)))
    (hαξ : ∀ y ∈ ordBall E ((level ξ / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ, (u : E) = 1 + y →
      (ξ u : ℂ) = ψ (Algebra.trace F E (α * y))) :
    α ∉ Set.range (algebraMap F E) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  set n := level ξ with hndef
  rintro ⟨a, rfl⟩
  have ha : a ∈ ordBall F (-n) := (algebraMap_mem_ordBall_iff hu a _).1 hα
  obtain ⟨φ₀, hφ₀⟩ := exists_psiChar_unitFilt hψ hn ha
  obtain ⟨φ, hφ⟩ := exists_extend_char _ φ₀
  apply hξ.not_factor_level
  refine ⟨φ, fun u hu' => ?_⟩
  have he : ramIdx F E = 1 := isUnramifiedExt_iff_ramIdx.1 hu
  have hN : normUnits F E u ∈ unitFilt F n :=
    normUnits_mem_unitFilt_of_lt hu' (by rw [he]; omega)
  have h1 := hφ ⟨_, hN⟩
  rw [hφ₀] at h1
  simp only at h1
  rw [h1]
  set y : E := (u : E) - 1 with hy
  have hyb : y ∈ ordBall E ((n / 2 + 1 : ℕ) : ℤ) := ordBall_anti (by push_cast; omega) hu'.2
  have h3 := hαξ y hyb u (by rw [hy]; ring)
  apply Units.ext
  rw [h3, psiUnit, Units.val_mk0]
  have hnorm : algebraMap F E (Algebra.norm F (u : E) - 1) =
      algebraMap F E (Algebra.trace F E y + Algebra.norm F y) := by
    rw [map_sub, map_one, map_add, algebraMap_norm_eq_mul, algebraMap_trace_eq_add,
      algebraMap_norm_eq_mul, show (u : E) = 1 + y by rw [hy]; ring, map_add, map_one]
    ring
  have hnorm' := (algebraMap F E).injective hnorm
  rw [val_normUnits, hnorm', mul_add, AddChar.map_add_eq_mul]
  have h4 : ψ (a * Algebra.norm F y) = 1 := by
    refine hψ.trivial _ ?_
    simp only [neg_neg]
    rw [← algebraMap_mem_ordBall_iff hu, map_mul, algebraMap_norm_eq_mul]
    have hσ : galConj F E y ∈ ordBall E n := (map_mem_ordBall_iff _ _ _).2 hu'.2
    refine ordBall_anti ?_ (mul_mem_ordBall_add hα (mul_mem_ordBall_add hu'.2 hσ))
    omega
  rw [h4, mul_one, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/-- **Minimal pairs give simple strata** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one, and let $(E/F, \xi)$ be a minimal pair with unramified $E/F$ and level $n \ge 1$. Then there is $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$, and $(\mathfrak{M}, n, \alpha)$ is a simple stratum in the basis $(1, u)$. -/
theorem IsMinimal.exists_isSimpleStratum_unram (h2 : (2 : 𝓀[F]) ≠ 0) (hu : IsUnramifiedExt F E)
    {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1)) {ξ : Eˣ →* ℂˣ} (hξ : IsMinimal F E ξ)
    (hn : 1 ≤ level ξ) :
    ∃ α : E, ord E α = -(level ξ : ℤ) ∧
      (∀ y ∈ ordBall E ((level ξ / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ, (u : E) = 1 + y →
        (ξ u : ℂ) = ψ (Algebra.trace F E (α * y))) ∧
      haveI := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
      IsSimpleStratum maximal (level ξ) (Algebra.leftMulMatrix (unramBasis F E hu) α) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  obtain ⟨α, hα0, hord, hαξ⟩ := hξ.admissible.exists_alpha h2 hψ hn
  refine ⟨α, hord, hαξ, isSimpleStratum_unramBasis hu hn hord ?_⟩
  exact hξ.alpha_not_mem h2 hu hψ hn (mem_ordBall_of_le hα0 hord.ge) hαξ

/-- **Ramified minimal pairs give simple strata** (BH Chapter 4, §19). Let $2 \ne 0$ in $k_F$, let $\psi$ have level one, and let $(E/F, \xi)$ be a minimal pair with totally ramified $E/F$. Then the level $n$ is odd, there is $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$, and $(\mathfrak{J}, n, \alpha)$ is a simple stratum in the basis $(\varpi_E, 1)$. -/
theorem IsMinimal.exists_isSimpleStratum_ram (h2 : (2 : 𝓀[F]) ≠ 0)
    (hr : IsTotallyRamifiedExt F E) {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1))
    {ξ : Eˣ →* ℂˣ} (hξ : IsMinimal F E ξ) :
    ∃ α : E, ord E α = -(level ξ : ℤ) ∧
      (∀ y ∈ ordBall E ((level ξ / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ, (u : E) = 1 + y →
        (ξ u : ℂ) = ψ (Algebra.trace F E (α * y))) ∧
      IsSimpleStratum iwahori (level ξ) (Algebra.leftMulMatrix (ramBasis F E hr) α) := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  have hodd := hξ.odd_level (Or.inl h2) hr
  have hn : 1 ≤ level ξ := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨α, -, hord, hαξ⟩ := hξ.admissible.exists_alpha h2 hψ hn
  exact ⟨α, hord, hαξ, isSimpleStratum_ramBasis hr hn hodd hord⟩

end MinimalAlpha

end Langlands.LocalGL2
