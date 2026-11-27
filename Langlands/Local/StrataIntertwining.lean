/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.CuspidalTypes

/-!
# The adjoint map and the intertwining of a simple stratum

Let $F$ be a nonarchimedean local field, $\mathfrak{A}$ a chain order of $M_2(F)$, and $E/F$ a quadratic extension embedded in $M_2(F)$ by a basis adapted to $\mathfrak{A}$. This file proves the properties of the adjoint map $a_\alpha(X) = \alpha X - X \alpha$ of BH §13, and it computes the intertwining of the character $\psi_\alpha$ of a simple stratum and of a cuspidal type inside the normalizer $\mathfrak{K}_{\mathfrak{A}}$ (BH §15.1).

For $\alpha \in E \setminus F$ the kernel of $a_\alpha$ is $F[\alpha]$, the image of $E$. An element $\alpha \in E$ is minimal of level $n$ if $\alpha \in \mathfrak{p}^{-n}_E$ and $\alpha \notin F + \mathfrak{p}^{1-n}_E$. For ramified $E/F$ and odd $n$ each $\alpha$ with $\mathrm{ord}_E(\alpha) = -n$ is minimal. For a minimal $\alpha$ the file proves the exactness of BH §13.4 in the form $a_\alpha^{-1}(\mathfrak{P}^j_{\mathfrak{A}}) = F[\alpha] + \mathfrak{P}^{j+n}_{\mathfrak{A}}$ for each $j \in \mathbb{Z}$.

Then it proves trace duality for $M_2(F)$: if $\psi(\mathrm{tr}(Y X)) = 1$ for each $X \in \mathfrak{P}^k_{\mathfrak{A}}$, then $Y \in \mathfrak{P}^{1-k}_{\mathfrak{A}}$. With the exactness this gives the conjugation criterion: for $g \in \mathfrak{K}_{\mathfrak{A}}$ and $r \ge 1$, $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{r-n}_{\mathfrak{A}}$ exactly when $g \in E^\times U^r_{\mathfrak{A}}$. So an element $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\psi_\alpha$ exactly when $g \in J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$, and the same holds for each cuspidal type $\Lambda$ of `Langlands.LocalGL2.cuspTypes`.

## Main definitions

* `Langlands.LocalGL2.adjointMap`: the adjoint map $a_\alpha(X) = \alpha X - X \alpha$, as an $F$-linear map of $M_2(F)$.
* `Langlands.LocalGL2.IsMinimalElt`: $\alpha \in E$ is minimal of level $n$, that is $\alpha \in \mathfrak{p}^{-n}_E$ and $\alpha \notin F + \mathfrak{p}^{1-n}_E$.

## Main results

* `Langlands.LocalGL2.adjointMap_eq_zero_iff`, `Langlands.LocalGL2.eq_leftMulMatrix_of_adjointMap_eq_zero`: for $\alpha \in E \setminus F$, the kernel of $a_\alpha$ is $F[\alpha]$, so the centralizer of $\alpha$ in $M_2(F)$ is $E$.
* `Langlands.LocalGL2.isMinimalElt_of_ramified`: for ramified $E/F$ and odd $n$, each $\alpha$ with $\mathrm{ord}_E(\alpha) = -n$ is minimal.
* `Langlands.LocalGL2.IsMinimalElt.smul_mem_ordBall`: for minimal $\alpha$, the basis $(1, \alpha)$ of $E$ is orthogonal.
* `Langlands.LocalGL2.IsAdapted.sub_leftMulMatrix_mem_radPow`, `Langlands.LocalGL2.IsAdapted.adjointMap_mem_radPow_iff`: $a_\alpha(X) \in \mathfrak{P}^j_{\mathfrak{A}}$ exactly when $X \in F[\alpha] + \mathfrak{P}^{j+n}_{\mathfrak{A}}$ (BH §13.4).
* `Langlands.LocalGL2.IsAdapted.exists_sub_mem_radPow_succ`: if $X \in \mathfrak{P}^k_{\mathfrak{A}}$ and $a_\alpha(X) \in \mathfrak{P}^{k-n+1}_{\mathfrak{A}}$, then $X \in \mathfrak{p}^k_E + \mathfrak{P}^{k+1}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.mem_radPow_of_forall_psi_trace`: trace duality, the dual of $\mathfrak{P}^k_{\mathfrak{A}}$ lies in $\mathfrak{P}^{1-k}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.IsAdapted.mem_jGroup_iff_conj_sub_mem`: $E^\times U^r_{\mathfrak{A}}$ is the set of $g \in \mathfrak{K}_{\mathfrak{A}}$ with $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{r-n}_{\mathfrak{A}}$, for $r \ge 1$.
* `Langlands.LocalGL2.intertwines_psiAlpha_iff`, `Langlands.LocalGL2.intertwines_psiAlpha_of_mem_jGroup`: an element of $\mathfrak{K}_{\mathfrak{A}}$ intertwines $\psi_\alpha$ exactly when it lies in $J_\alpha$.
* `Langlands.LocalGL2.intertwines_psiAlpha_of_mem_cuspTypes`, `Langlands.LocalGL2.intertwines_cuspType_iff`: the intertwining of a cuspidal type lies in the intertwining of $\psi_\alpha$, and its part in $\mathfrak{K}_{\mathfrak{A}}$ is $J_\alpha$.
* `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType`: if the intertwining of $\psi_\alpha$ lies in $\mathfrak{K}_{\mathfrak{A}}$, then the intertwining of each cuspidal type is $J_\alpha$, in the form of the hypothesis of `Langlands.eq_smul_cIndBasic_of_isotypic`.

## Implementation notes

The proof of the exactness does not use the Galois conjugation of $E$. For $y = X(1)$ the matrix $X' = X - y$ kills $1$, and $X'(\alpha) = -a_\alpha(X)(1)$. Since $(1, \alpha)$ is an orthogonal basis of $E$, an element $t = a + b \alpha$ of $\mathfrak{p}^N_E$ has $b \in \mathfrak{p}^{N+n}_E$, so $X'(t) = b X'(\alpha) \in \mathfrak{p}^{N+j+n}_E$. The orthogonality is the minimality of $\alpha$. For $g \in \mathfrak{K}_{\mathfrak{A}} = \Pi^{\mathbb{Z}} \mathfrak{A}^\times$ one has $g \in \mathfrak{P}^l_{\mathfrak{A}}$ and $g^{-1} \in \mathfrak{P}^{-l}_{\mathfrak{A}}$ for some $l$, and $a_\alpha(g) = g (g^{-1} \alpha g - \alpha)$. The exactness gives $y \in E$ with $g - y \in \mathfrak{P}^{l+r}_{\mathfrak{A}}$, and then $\mathrm{ord}_E(y) = l$ and $y^{-1} g \in U^r_{\mathfrak{A}}$. Because $\mathfrak{K}_{\mathfrak{A}}$ normalizes $U^{[n/2]+1}_{\mathfrak{A}}$, the intertwining condition for $g \in \mathfrak{K}_{\mathfrak{A}}$ is $\psi(\mathrm{tr}((g^{-1} \alpha g - \alpha) X)) = 1$ for each $X \in \mathfrak{P}^{[n/2]+1}_{\mathfrak{A}}$, and trace duality applies. The intertwining is `Langlands.Intertwines` of `Langlands/Local/CuspidalTypes.lean`.

## Still open

* The part of BH §15.1 outside $\mathfrak{K}_{\mathfrak{A}}$: each $g \in GL_2(F)$ that intertwines $\psi_\alpha$ lies in $\mathfrak{K}_{\mathfrak{A}}$. This is the hypothesis `hK` of `mem_jGroup_of_intertwines_cuspType`. For $g \notin \mathfrak{K}_{\mathfrak{A}}$ the group $U^{[n/2]+1}_{\mathfrak{A}} \cap g^{-1} U^{[n/2]+1}_{\mathfrak{A}} g$ is smaller, and the proof needs the duality of an intersection of two lattices, $(L \cap L')^\perp = L^\perp + L'^\perp$, which gives $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{-[n/2]}_{\mathfrak{A}} + g^{-1} \mathfrak{P}^{-[n/2]}_{\mathfrak{A}} g$. Then it needs the statement that a simple stratum determines its chain order: if $g$ intertwines $(\mathfrak{A}, n, \alpha)$, then $g$ normalizes $\mathfrak{A}$ (BH §14 and §15.1, with the double cosets $\mathfrak{A}^\times \backslash GL_2(F) / \mathfrak{A}^\times$). Without this the intertwining of a cuspidal type is only proved to be $J_\alpha$ inside $\mathfrak{K}_{\mathfrak{A}}$.
* For unramified $E/F$, the minimality $\alpha \notin F + \mathfrak{p}^{1-n}_E$ of the element of a minimal pair (see `Langlands/Local/AdaptedUnramified.lean`). The ramified case with odd $n$ is `isMinimalElt_of_ramified`.
* The case of even $n$ of the cuspidal types, where $J_\alpha$ is larger than the group of `typeChar` (see `Langlands/Local/CuspidalTypes.lean`). The results on $\psi_\alpha$ here hold for each $n \ge 1$.

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, Chapter 3 and 4, §§12 to 15.
-/

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel Matrix

section Adjoint

variable {F : Type u} [Field F]

variable (F) in
/-- The adjoint map $a_\alpha(X) = \alpha X - X \alpha$ of $\alpha \in M_2(F)$, as an $F$-linear map of $M_2(F)$ (BH §13.1). -/
def adjointMap (α : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F where
  toFun X := α * X - X * α
  map_add' X Y := by noncomm_ring
  map_smul' c X := by simp [smul_sub]

/-- The value of the adjoint map. -/
theorem adjointMap_apply (α X : Matrix (Fin 2) (Fin 2) F) :
    adjointMap F α X = α * X - X * α := rfl

variable {E : Type v} [Field E] [Algebra F E] (v : Module.Basis (Fin 2) F E)

/-- The action of a matrix is additive. -/
theorem act_add (Y : Matrix (Fin 2) (Fin 2) F) (x y : E) :
    act v Y (x + y) = act v Y x + act v Y y := by
  simp only [act, map_add, Matrix.mulVec_add]

/-- The action of a matrix is $F$-linear. -/
theorem act_smul (Y : Matrix (Fin 2) (Fin 2) F) (c : F) (y : E) :
    act v Y (c • y) = c • act v Y y := by
  simp only [act, map_smul, Matrix.mulVec_smul]

/-- The action is additive in the matrix. -/
theorem act_sub_left (X Y : Matrix (Fin 2) (Fin 2) F) (y : E) :
    act v (X - Y) y = act v X y - act v Y y := by
  simp only [act, Matrix.sub_mulVec, map_sub]

/-- A matrix is determined by its action on $E$. -/
theorem act_injective {X Y : Matrix (Fin 2) (Fin 2) F} (h : ∀ y, act v X y = act v Y y) : X = Y := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  have hw := h (v.equivFun.symm w)
  simp only [act, LinearEquiv.apply_symm_apply] at hw
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact v.equivFun.symm.injective hw

/-- For $y = X(1)$, the matrix $X - y$ kills $1$. -/
theorem act_sub_leftMulMatrix_one (X : Matrix (Fin 2) (Fin 2) F) :
    act v (X - Algebra.leftMulMatrix v (act v X 1)) 1 = 0 := by
  rw [act_sub_left, act_leftMulMatrix, mul_one, sub_self]

/-- For $y = X(1)$, the value of $X - y$ at $\alpha$ is $-a_\alpha(X)(1)$. -/
theorem act_sub_leftMulMatrix_alpha (X : Matrix (Fin 2) (Fin 2) F) (α : E) :
    act v (X - Algebra.leftMulMatrix v (act v X 1)) α =
      -act v (adjointMap F (Algebra.leftMulMatrix v α) X) 1 := by
  rw [act_sub_left, act_leftMulMatrix, adjointMap_apply, act_sub_left, act_mul, act_mul,
    act_leftMulMatrix, act_leftMulMatrix, mul_one]
  ring

/-- The matrix of an element of $E$ is in the kernel of $a_\alpha$ for $\alpha \in E$. -/
theorem adjointMap_leftMulMatrix (α y : E) :
    adjointMap F (Algebra.leftMulMatrix v α) (Algebra.leftMulMatrix v y) = 0 := by
  rw [adjointMap_apply, ← map_mul, ← map_mul, mul_comm, sub_self]

variable [Algebra.IsQuadraticExtension F E]

/-- For $\alpha \in E \setminus F$, each element of $E$ is $a + b \alpha$ with $a, b \in F$. -/
theorem exists_eq_smul_one_add_smul {α : E} (hα : α ∉ Set.range (algebraMap F E)) (t : E) :
    ∃ a b : F, t = a • (1 : E) + b • α := by
  have hli : LinearIndependent F ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    apply hα
    exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  rw [Matrix.range_cons_cons_empty] at hspan
  have ht : t ∈ Submodule.span F ({1, α} : Set E) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.1 ht
  exact ⟨a, b, h.symm⟩

/-- For $\alpha \in E \setminus F$, the algebra $F[\alpha] \subseteq M_2(F)$ is the image of $E$. -/
theorem adjoin_leftMulMatrix_eq_range {α : E} (hα : α ∉ Set.range (algebraMap F E)) :
    Algebra.adjoin F {Algebra.leftMulMatrix v α} = (Algebra.leftMulMatrix v).range := by
  rw [← AlgHom.map_adjoin_singleton, adjoin_eq_top_of_not_mem hα, Algebra.map_top]

/-- The centralizer of $\alpha \in E \setminus F$ in $M_2(F)$ is $E$: if $X$ commutes with $\alpha$, then $X$ is the matrix of $X(1) \in E$. -/
theorem eq_leftMulMatrix_of_adjointMap_eq_zero {α : E} (hα : α ∉ Set.range (algebraMap F E))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : adjointMap F (Algebra.leftMulMatrix v α) X = 0) :
    X = Algebra.leftMulMatrix v (act v X 1) := by
  have h0 : X - Algebra.leftMulMatrix v (act v X 1) = 0 := by
    refine act_injective v fun t => ?_
    obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul hα t
    rw [act_add, act_smul, act_smul, act_sub_leftMulMatrix_one, act_sub_leftMulMatrix_alpha, hX]
    simp [act]
  exact sub_eq_zero.1 h0

/-- The kernel of $a_\alpha$ is $F[\alpha]$ for $\alpha \in E \setminus F$ (BH §13.1). -/
theorem adjointMap_eq_zero_iff {α : E} (hα : α ∉ Set.range (algebraMap F E))
    (X : Matrix (Fin 2) (Fin 2) F) :
    adjointMap F (Algebra.leftMulMatrix v α) X = 0 ↔ X ∈ Algebra.adjoin F {Algebra.leftMulMatrix v α} := by
  rw [adjoin_leftMulMatrix_eq_range v hα]
  constructor
  · intro hX
    exact ⟨_, (eq_leftMulMatrix_of_adjointMap_eq_zero v hα hX).symm⟩
  · rintro ⟨y, rfl⟩
    exact adjointMap_leftMulMatrix v α y

end Adjoint

section Minimal

/-- The order of $-x$ is the order of $x$. -/
theorem ord_neg {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) : ord K (-x) = ord K x := by
  simp only [ord, Valuation.map_neg]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]

variable (F) in
/-- The element $\alpha \in E$ is minimal of level $n$ over $F$ (BH §13.4): $\alpha \in \mathfrak{p}^{-n}_E$ and $\alpha \notin F + \mathfrak{p}^{1-n}_E$. For ramified $E/F$ and odd $n$ this is $\mathrm{ord}_E(\alpha) = -n$. For unramified $E/F$ it says that $\varpi_F^n \alpha$ is a unit whose residue class is not in $k_F$. -/
def IsMinimalElt (n : ℕ) (α : E) : Prop :=
  α ∈ ordBall E (-n) ∧ ∀ a : F, α - algebraMap F E a ∉ ordBall E (1 - n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- For a minimal element, $\alpha - a \ne 0$ and $\mathrm{ord}_E(\alpha - a) \le -n$ for each $a \in F$. -/
theorem IsMinimalElt.sub_ne_zero_and {n : ℕ} {α : E} (hα : IsMinimalElt F n α) (a : F) :
    α - algebraMap F E a ≠ 0 ∧ ord E (α - algebraMap F E a) ≤ -n := by
  have h := hα.2 a
  have h0 : α - algebraMap F E a ≠ 0 := fun h0 => h (h0 ▸ zero_mem_ordBall _)
  rw [mem_ordBall_of_ne_zero h0] at h
  exact ⟨h0, by omega⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- A minimal element of level $n$ has $\mathrm{ord}_E(\alpha) = -n$. -/
theorem IsMinimalElt.ne_zero_and_ord {n : ℕ} {α : E} (hα : IsMinimalElt F n α) :
    α ≠ 0 ∧ ord E α = -n := by
  have h := hα.sub_ne_zero_and 0
  rw [map_zero, sub_zero] at h
  exact ⟨h.1, le_antisymm h.2 ((mem_ordBall_of_ne_zero h.1).1 hα.1)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- A minimal element is not in $F$. -/
theorem IsMinimalElt.not_mem_range {n : ℕ} {α : E} (hα : IsMinimalElt F n α) :
    α ∉ Set.range (algebraMap F E) := by
  rintro ⟨a, rfl⟩
  exact (hα.sub_ne_zero_and a).1 (sub_self _)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- For a minimal element $\alpha$, the basis $(1, \alpha)$ is orthogonal: if $a + b \alpha \in \mathfrak{p}^N_E$ with $a, b \in F$, then $b \alpha \in \mathfrak{p}^N_E$. -/
theorem IsMinimalElt.smul_mem_ordBall {n : ℕ} {α : E} (hα : IsMinimalElt F n α) (a b : F) {N : ℤ}
    (h : a • (1 : E) + b • α ∈ ordBall E N) : b • α ∈ ordBall E N := by
  by_cases hb : b = 0
  · rw [hb, zero_smul]
    exact zero_mem_ordBall _
  obtain ⟨hα0, hord⟩ := hα.ne_zero_and_ord
  have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
  have e1 : a • (1 : E) + b • α = algebraMap F E b * (α - algebraMap F E (-(a / b))) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_sub, map_neg, map_div₀]
    field_simp
    ring
  obtain ⟨h0, hle⟩ := hα.sub_ne_zero_and (-(a / b))
  rw [e1, mem_ordBall_of_ne_zero (mul_ne_zero hb' h0), ord_mul hb' h0] at h
  rw [Algebra.smul_def]
  exact mem_ordBall_of_le (mul_ne_zero hb' hα0) (by rw [ord_mul hb' hα0, hord]; omega)

/-- For ramified $E/F$ and odd $n$, each $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$ is minimal. -/
theorem isMinimalElt_of_ramified (hr : IsTotallyRamifiedExt F E) {n : ℕ} (hodd : Odd n) {α : E}
    (hα0 : α ≠ 0) (hord : ord E α = -n) : IsMinimalElt F n α := by
  have he := isTotallyRamifiedExt_iff_ramIdx.1 hr
  refine ⟨mem_ordBall_of_le hα0 (by rw [hord]), fun a h => ?_⟩
  obtain ⟨k, hk⟩ := hodd
  by_cases ha : a = 0
  · rw [ha, map_zero, sub_zero, mem_ordBall_of_ne_zero hα0, hord] at h
    omega
  have ha' : algebraMap F E a ≠ 0 := (map_ne_zero _).2 ha
  have hna : -algebraMap F E a ≠ 0 := neg_ne_zero.2 ha'
  have hordn : ord E (-algebraMap F E a) = 2 * ord F a := by
    rw [ord_neg, ord_algebraMap_eq, he]
  rcases lt_or_gt_of_ne (show ord E α ≠ ord E (-algebraMap F E a) by rw [hord, hordn]; omega)
    with hlt | hlt
  · obtain ⟨h0, he'⟩ := ord_add_of_lt hα0 hna hlt
    rw [← sub_eq_add_neg] at h0 he'
    rw [mem_ordBall_of_ne_zero h0, he', hord] at h
    omega
  · obtain ⟨h0, he'⟩ := ord_add_of_lt hna hα0 hlt
    rw [neg_add_eq_sub] at h0 he'
    rw [mem_ordBall_of_ne_zero h0, he'] at h
    omega

end Minimal

section Exactness

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

/-- The exactness of $a_\alpha$ (BH §13.4). Let $v$ be adapted to $\mathfrak{A}$ and $\alpha \in E$ minimal of level $n$. If $a_\alpha(X) \in \mathfrak{P}^j_{\mathfrak{A}}$, then $X - y \in \mathfrak{P}^{j+n}_{\mathfrak{A}}$ for $y = X(1) \in E$. -/
theorem IsAdapted.sub_leftMulMatrix_mem_radPow (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : IsMinimalElt F n α) {j : ℤ} {X : Matrix (Fin 2) (Fin 2) F}
    (hX : adjointMap F (Algebra.leftMulMatrix v α) X ∈ radPow F A j) :
    X - Algebra.leftMulMatrix v (act v X 1) ∈ radPow F A (j + n) := by
  obtain ⟨hα0, hord⟩ := hα.ne_zero_and_ord
  rw [hv.mem_radPow_iff]
  intro N t ht
  obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul hα.not_mem_range t
  have hb := hα.smul_mem_ordBall a b ht
  rw [Algebra.smul_def, mul_comm, mul_mem_ordBall_iff hα0, hord] at hb
  have hD := (hv.mem_radPow_iff j _).1 hX 0 1 (one_mem_ordBall le_rfl)
  rw [act_add, act_smul, act_smul, act_sub_leftMulMatrix_one, act_sub_leftMulMatrix_alpha, smul_zero,
    zero_add, smul_neg, Algebra.smul_def]
  exact neg_mem_ordBall (mem_ordBall_congr (by ring) (mul_mem_ordBall_add hb hD))

omit [Algebra.IsQuadraticExtension F E] in
/-- For $\alpha \in E$ of order $\ge -n$ and $Z \in \mathfrak{P}^{j+n}_{\mathfrak{A}}$, $a_\alpha(Z) \in \mathfrak{P}^j_{\mathfrak{A}}$. -/
theorem IsAdapted.adjointMap_mem_radPow (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : α ∈ ordBall E (-n)) {j : ℤ} {Z : Matrix (Fin 2) (Fin 2) F} (hZ : Z ∈ radPow F A (j + n)) :
    adjointMap F (Algebra.leftMulMatrix v α) Z ∈ radPow F A j := by
  have hαA := (hv.leftMulMatrix_mem_radPow_iff (-n) α).2 hα
  have h1 := mul_mem_radPow hαA hZ
  have h2 := mul_mem_radPow hZ hαA
  rw [show -(n : ℤ) + (j + n) = j by ring] at h1
  rw [show j + n + -(n : ℤ) = j by ring] at h2
  exact sub_mem h1 h2

/-- The exact sequence of BH §13.4 in the form $a_\alpha^{-1}(\mathfrak{P}^j_{\mathfrak{A}}) = F[\alpha] + \mathfrak{P}^{j+n}_{\mathfrak{A}}$, for $\alpha \in E$ minimal of level $n$ and $v$ adapted to $\mathfrak{A}$. -/
theorem IsAdapted.adjointMap_mem_radPow_iff (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : IsMinimalElt F n α) (j : ℤ) (X : Matrix (Fin 2) (Fin 2) F) :
    adjointMap F (Algebra.leftMulMatrix v α) X ∈ radPow F A j ↔
      ∃ y : E, X - Algebra.leftMulMatrix v y ∈ radPow F A (j + n) := by
  constructor
  · intro hX
    exact ⟨_, hv.sub_leftMulMatrix_mem_radPow hα hX⟩
  · rintro ⟨y, hy⟩
    have h := hv.adjointMap_mem_radPow hα.1 hy
    rwa [map_sub, adjointMap_leftMulMatrix, sub_zero] at h

/-- The exactness of $a_\alpha$ on $\mathfrak{P}^k_{\mathfrak{A}}$ (BH §13.4): if $X \in \mathfrak{P}^k_{\mathfrak{A}}$ and $a_\alpha(X) \in \mathfrak{P}^{k-n+1}_{\mathfrak{A}}$, then $X \in (\mathfrak{p}^k_E) + \mathfrak{P}^{k+1}_{\mathfrak{A}}$, where $\mathfrak{p}^k_E = F[\alpha] \cap \mathfrak{P}^k_{\mathfrak{A}}$. -/
theorem IsAdapted.exists_sub_mem_radPow_succ (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : IsMinimalElt F n α) {k : ℤ} {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ radPow F A k)
    (hXa : adjointMap F (Algebra.leftMulMatrix v α) X ∈ radPow F A (k - n + 1)) :
    ∃ y ∈ ordBall E k, X - Algebra.leftMulMatrix v y ∈ radPow F A (k + 1) := by
  refine ⟨act v X 1, ?_, ?_⟩
  · have := (hv.mem_radPow_iff k X).1 hX 0 1 (one_mem_ordBall le_rfl)
    rwa [zero_add] at this
  · have := hv.sub_leftMulMatrix_mem_radPow hα hXa
    rwa [show k - n + 1 + n = k + 1 by ring] at this

end Exactness

section Normalizer

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {A : ChainOrder}

/-- The arithmetic of the dual bound: $b(1 - k, i, j) \le 1 - b(k, j, i)$. -/
theorem ChainOrder.bd_one_sub_le (A : ChainOrder) (k : ℤ) (i j : Fin 2) :
    A.bd (1 - k) i j ≤ 1 - A.bd k j i := by
  rw [A.le_bd_iff]
  have h2 : ¬ (A.bd k j i ≤ A.bd k j i - 1) := by omega
  rw [A.le_bd_iff, not_le] at h2
  have e : A.e * (1 - A.bd k j i) = -(A.e * (A.bd k j i - 1)) := by ring
  rw [e]
  linarith

/-- Trace duality for $M_2(F)$: if $\psi$ has level one and $\psi(\mathrm{tr}(Y X)) = 1$ for each $X \in \mathfrak{P}^k_{\mathfrak{A}}$, then $Y \in \mathfrak{P}^{1-k}_{\mathfrak{A}}$ (BH §12.8). -/
theorem mem_radPow_of_forall_psi_trace {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1)) {k : ℤ}
    {Y : Matrix (Fin 2) (Fin 2) F} (h : ∀ X ∈ radPow F A k, ψ (Y * X).trace = 1) :
    Y ∈ radPow F A (1 - k) := by
  intro i j
  have key : Y i j ∈ ordBall F (-(-1) - A.bd k j i) := by
    refine (hψ.forall_mul_iff (A.bd k j i) (Y i j)).1 fun c hc => ?_
    have hX : Matrix.single j i c ∈ radPow F A k := by
      intro a b
      by_cases hab : j = a ∧ i = b
      · obtain ⟨rfl, rfl⟩ := hab
        rwa [Matrix.single_apply_same]
      · rw [Matrix.single_apply_of_ne (h := hab)]
        exact zero_mem_ordBall _
    have := h _ hX
    rwa [Matrix.trace_mul_single, op_smul_eq_mul, mul_comm] at this
  rw [show -(-1 : ℤ) - A.bd k j i = 1 - A.bd k j i by ring] at key
  exact ordBall_anti (A.bd_one_sub_le k i j) key

/-- The identity matrix does not lie in $\mathfrak{P}_{\mathfrak{A}}$. -/
theorem one_not_mem_radPow_one (A : ChainOrder) : (1 : Matrix (Fin 2) (Fin 2) F) ∉ radPow F A 1 := by
  intro h
  have h00 := h 0 0
  rw [Matrix.one_apply_eq, mem_ordBall_of_ne_zero one_ne_zero, ord_one] at h00
  have := A.one_le_bd_self le_rfl 0
  omega

/-- An element $g$ of $\mathfrak{K}_{\mathfrak{A}}$ lies in $\mathfrak{P}^l_{\mathfrak{A}}$ with $g^{-1} \in \mathfrak{P}^{-l}_{\mathfrak{A}}$ for some $l \in \mathbb{Z}$. -/
theorem exists_mem_radPow_of_mem_normalizer {g : GL (Fin 2) F} (hg : g ∈ normalizer F A) :
    ∃ l : ℤ, (g : Matrix (Fin 2) (Fin 2) F) ∈ radPow F A l ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ radPow F A (-l) := by
  obtain ⟨k, u, hu, rfl⟩ := (mem_normalizer_iff A g).1 hg
  refine ⟨k, ?_, ?_⟩
  · have := (zpow_mul_mem_iff A k 0 _).1 (mem_order.1 hu.1)
    rwa [zero_add, ← Units.val_mul] at this
  · have := (mul_zpow_mem_iff A (-k) 0 _).1 (mem_order.1 hu.2.1)
    rwa [zero_add, ← Units.val_mul, zpow_neg, ← _root_.mul_inv_rev] at this

/-- Conjugation by an element of $\mathfrak{K}_{\mathfrak{A}}$ preserves $\mathfrak{P}^k_{\mathfrak{A}}$. -/
theorem conj_mem_radPow_of_mem_normalizer {g : GL (Fin 2) F} (hg : g ∈ normalizer F A) {k : ℤ}
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ radPow F A k) :
    (g : Matrix (Fin 2) (Fin 2) F) * X * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈
      radPow F A k := by
  obtain ⟨l, h1, h2⟩ := exists_mem_radPow_of_mem_normalizer hg
  have := mul_mem_radPow (mul_mem_radPow h1 hX) h2
  rwa [show l + k + -l = k by ring] at this

/-- Conjugation by an element of $\mathfrak{K}_{\mathfrak{A}}$ preserves $U^k_{\mathfrak{A}}$ for $k \ge 1$. -/
theorem conj_mem_unitsFilt_of_mem_normalizer {g : GL (Fin 2) F} (hg : g ∈ normalizer F A) {k : ℕ}
    (hk : 1 ≤ k) {x : GL (Fin 2) F} (hx : x ∈ unitsFilt F A k) : g * x * g⁻¹ ∈ unitsFilt F A k := by
  rw [mem_unitsFilt_iff hk] at hx ⊢
  have e : ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
      (g : Matrix (Fin 2) (Fin 2) F) * ((x : Matrix (Fin 2) (Fin 2) F) - 1) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [e]
  exact conj_mem_radPow_of_mem_normalizer hg hx

/-- For $k \ge 1$ and $X \in \mathfrak{P}^k_{\mathfrak{A}}$, the matrix $1 + X$ is an element of $U^k_{\mathfrak{A}}$. -/
theorem exists_unitsFilt_eq_one_add {k : ℕ} (hk : 1 ≤ k) {X : Matrix (Fin 2) (Fin 2) F}
    (hX : X ∈ radPow F A k) :
    ∃ x : GL (Fin 2) F, x ∈ unitsFilt F A k ∧ (x : Matrix (Fin 2) (Fin 2) F) = 1 + X := by
  have h1 : (1 + X) - 1 ∈ radPow F A 1 := by
    rw [add_sub_cancel_left]
    exact radPow_anti (by exact_mod_cast hk) hX
  have hd := (sub_one_mem_ordBall_one (det_sub_one_mem h1)).1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + X) hd, ?_, rfl⟩
  rw [mem_unitsFilt_iff hk]
  change (1 + X) - 1 ∈ _
  rw [add_sub_cancel_left]
  exact hX

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The value $\psi_\alpha(g x g^{-1}) = \psi_\alpha(x) \, \psi(\mathrm{tr}((g^{-1} \alpha g - \alpha)(x - 1)))$. -/
theorem psiAlphaFun_conj_eq (ψ : AddChar F ℂ) (α : Matrix (Fin 2) (Fin 2) F) (g x : GL (Fin 2) F) :
    psiAlphaFun F ψ α (g * x * g⁻¹) = psiAlphaFun F ψ α x *
      ψ ((((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * α * (g : Matrix (Fin 2) (Fin 2) F) - α) *
        ((x : Matrix (Fin 2) (Fin 2) F) - 1)).trace := by
  unfold psiAlphaFun
  rw [← AddChar.map_add_eq_mul]
  congr 1
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  set Gi : Matrix (Fin 2) (Fin 2) F := ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F)
  have e1 : ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 = G * (X - 1) * Gi := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  have e2 : (α * (G * (X - 1) * Gi)).trace = (Gi * α * G * (X - 1)).trace := by
    rw [show α * (G * (X - 1) * Gi) = (α * G * (X - 1)) * Gi by simp only [mul_assoc],
      Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [e1, e2, sub_mul, Matrix.trace_sub]
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The values of an additive character are not zero. -/
theorem addChar_apply_ne_zero (ψ : AddChar F ℂ) (x : F) : ψ x ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel x, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

end Normalizer

section Intertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

/-- If $g \in E^\times U^r_{\mathfrak{A}}$ and $\alpha \in \mathfrak{p}^{-n}_E$, then $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{r-n}_{\mathfrak{A}}$. -/
theorem IsAdapted.conj_sub_mem_of_mem_jGroup (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : α ∈ ordBall E (-n)) {r : ℕ} {g : GL (Fin 2) F} (hg : g ∈ jGroup v hv r) :
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
      (g : Matrix (Fin 2) (Fin 2) F) - Algebra.leftMulMatrix v α ∈ radPow F A (r - n) := by
  obtain ⟨y, u, hu, rfl⟩ := (mem_jGroup_iff_exists_mul hv r g).1 hg
  set Y : Matrix (Fin 2) (Fin 2) F := ((embGL v y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set Yi : Matrix (Fin 2) (Fin 2) F := (((embGL v y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set U : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F)
  set Ui : Matrix (Fin 2) (Fin 2) F := ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set L : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v α
  have hYiY : Yi * Y = 1 := Units.inv_mul _
  have hUiU : Ui * U = 1 := Units.inv_mul _
  have hc : Yi * L * Y = L := by
    rw [mul_assoc, leftMulMatrix_mul_embGL α y, ← mul_assoc, hYiY, one_mul]
  have e : (((embGL v y * u)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * L *
      ((embGL v y * u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - L =
      Ui * adjointMap F L (U - 1) := by
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, adjointMap_apply]
    calc Ui * Yi * L * (Y * U) - L = Ui * (Yi * L * Y) * U - L := by simp only [mul_assoc]
      _ = Ui * (L * (U - 1) - (U - 1) * L) := by
        rw [hc]
        simp only [mul_sub, sub_mul, mul_one, ← mul_assoc, hUiU, one_mul]
        abel
  rw [e]
  have hU : U - 1 ∈ radPow F A ((r - n : ℤ) + n) := by
    rw [sub_add_cancel]
    exact hu.2.2
  have := mul_mem_radPow (mem_order.1 hu.2.1) (hv.adjointMap_mem_radPow hα hU)
  rwa [zero_add] at this

variable [Algebra.IsQuadraticExtension F E]

/-- The conjugation criterion (BH §15.1, the part in $\mathfrak{K}_{\mathfrak{A}}$). Let $v$ be adapted to $\mathfrak{A}$, $\alpha \in E$ minimal of level $n$ and $r \ge 1$. If $g \in \mathfrak{K}_{\mathfrak{A}}$ and $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{r-n}_{\mathfrak{A}}$, then $g \in E^\times U^r_{\mathfrak{A}}$. -/
theorem IsAdapted.mem_jGroup_of_conj_sub_mem (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : IsMinimalElt F n α) {r : ℕ} (hr : 1 ≤ r) {g : GL (Fin 2) F} (hg : g ∈ normalizer F A)
    (h : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
      (g : Matrix (Fin 2) (Fin 2) F) - Algebra.leftMulMatrix v α ∈ radPow F A (r - n)) :
    g ∈ jGroup v hv r := by
  obtain ⟨l, hG, hGi⟩ := exists_mem_radPow_of_mem_normalizer hg
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  set Gi : Matrix (Fin 2) (Fin 2) F := ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set L : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v α
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hGiG : Gi * G = 1 := Units.inv_mul g
  have ha : adjointMap F L G ∈ radPow F A (l + (r - n)) := by
    have e : adjointMap F L G = G * (Gi * L * G - L) := by
      rw [adjointMap_apply, mul_sub, ← mul_assoc, ← mul_assoc, hGGi, one_mul]
    rw [e]
    exact mul_mem_radPow hG h
  have hZ := hv.sub_leftMulMatrix_mem_radPow hα ha
  rw [show l + (r - n) + n = l + r by ring] at hZ
  set y : E := act v G 1
  set Z : Matrix (Fin 2) (Fin 2) F := G - Algebra.leftMulMatrix v y with hZdef
  have hGiZ : Gi * Z ∈ radPow F A r := by
    have := mul_mem_radPow hGi hZ
    rwa [show -l + (l + r) = r by ring] at this
  have hLy : Algebra.leftMulMatrix v y = G - Z := by rw [hZdef, sub_sub_cancel]
  have hy1 : y ∉ ordBall E (l + 1) := by
    intro hy
    have h1 := mul_mem_radPow hGi ((hv.leftMulMatrix_mem_radPow_iff (l + 1) y).2 hy)
    rw [show -l + (l + 1) = 1 by ring] at h1
    have e : (1 : Matrix (Fin 2) (Fin 2) F) = Gi * Algebra.leftMulMatrix v y + Gi * Z := by
      rw [← mul_add, hLy, sub_add_cancel, hGiG]
    exact one_not_mem_radPow_one A (e ▸ add_mem h1 (radPow_anti (by exact_mod_cast hr) hGiZ))
  have hyl : y ∈ ordBall E l := by
    rw [← hv.leftMulMatrix_mem_radPow_iff, hLy]
    exact sub_mem hG (radPow_anti (by omega) hZ)
  have hy0 : y ≠ 0 := fun h0 => hy1 (h0 ▸ zero_mem_ordBall _)
  rw [mem_ordBall_of_ne_zero hy0] at hyl hy1
  have hyi : y⁻¹ ∈ ordBall E (-l) :=
    mem_ordBall_of_le (inv_ne_zero hy0) (by rw [ord_inv hy0]; omega)
  refine ⟨Units.mk0 y hy0, ?_⟩
  rw [mem_unitsFilt_iff hr, Units.val_mul, val_embGL_inv, Units.val_inv_eq_inv_val, Units.val_mk0]
  have e : Algebra.leftMulMatrix v y⁻¹ * G - 1 = Algebra.leftMulMatrix v y⁻¹ * Z := by
    rw [hZdef, mul_sub, ← map_mul, inv_mul_cancel₀ hy0, map_one]
  rw [e]
  have := mul_mem_radPow ((hv.leftMulMatrix_mem_radPow_iff (-l) _).2 hyi) hZ
  rwa [show -l + (l + r) = r by ring] at this

/-- The group $E^\times U^r_{\mathfrak{A}}$ for $r \ge 1$ is the set of $g \in \mathfrak{K}_{\mathfrak{A}}$ with $g^{-1} \alpha g \in \alpha + \mathfrak{P}^{r-n}_{\mathfrak{A}}$, for $\alpha \in E$ minimal of level $n$. -/
theorem IsAdapted.mem_jGroup_iff_conj_sub_mem (hv : IsAdapted A v) {n : ℕ} {α : E}
    (hα : IsMinimalElt F n α) {r : ℕ} (hr : 1 ≤ r) (g : GL (Fin 2) F) :
    g ∈ jGroup v hv r ↔ g ∈ normalizer F A ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
        (g : Matrix (Fin 2) (Fin 2) F) - Algebra.leftMulMatrix v α ∈ radPow F A (r - n) :=
  ⟨fun hg => ⟨jGroup_le_normalizer hv r hg, hv.conj_sub_mem_of_mem_jGroup hα.1 hg⟩,
    fun h => hv.mem_jGroup_of_conj_sub_mem hα hr h.1 h.2⟩

variable (hv : IsAdapted A v) (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) {n : ℕ} {α : E}
  (hαA : Algebra.leftMulMatrix v α ∈ radPow F A (-n))

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E] in
/-- If $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$, then $g^{-1} \alpha g - \alpha \in \mathfrak{P}^{-[n/2]}_{\mathfrak{A}}$. -/
theorem conj_sub_mem_of_intertwines_psiAlpha {g : GL (Fin 2) F} (hg : g ∈ normalizer F A)
    (hI : Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g) :
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
      (g : Matrix (Fin 2) (Fin 2) F) - Algebra.leftMulMatrix v α ∈
        radPow F A (1 - ((n / 2 + 1 : ℕ) : ℤ)) := by
  refine mem_radPow_of_forall_psi_trace hψ fun X hX => ?_
  obtain ⟨x, hx, hxX⟩ := exists_unitsFilt_eq_one_add (by omega) hX
  have hgx := conj_mem_unitsFilt_of_mem_normalizer hg (by omega) hx
  have h1 := congrArg Units.val (hI ⟨x, hx⟩ hgx)
  rw [coe_psiAlphaUnits, coe_psiAlphaUnits] at h1
  change psiAlphaFun F ψ _ (g * x * g⁻¹) = psiAlphaFun F ψ _ x at h1
  rw [psiAlphaFun_conj_eq, hxX, add_sub_cancel_left] at h1
  have h2 := h1.trans (mul_one _).symm
  exact mul_left_cancel₀ (addChar_apply_ne_zero ψ _) h2

/-- The intertwining of $\psi_\alpha$ in $\mathfrak{K}_{\mathfrak{A}}$ (BH §15.1, the part in $\mathfrak{K}_{\mathfrak{A}}$). Let $v$ be adapted to $\mathfrak{A}$ and $\alpha \in E$ minimal of level $n \ge 1$. An element $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines the character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ exactly when $g \in J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$. -/
theorem intertwines_psiAlpha_iff (hα : IsMinimalElt F n α) (hn : 1 ≤ n) {g : GL (Fin 2) F}
    (hg : g ∈ normalizer F A) :
    Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g ↔
      g ∈ jGroup v hv ((n + 1) / 2) := by
  have hlev : (1 : ℤ) - ((n / 2 + 1 : ℕ) : ℤ) = (((n + 1) / 2 : ℕ) : ℤ) - n := by omega
  constructor
  · intro hI
    have h := conj_sub_mem_of_intertwines_psiAlpha ψ hψ hαA hg hI
    rw [hlev] at h
    exact hv.mem_jGroup_of_conj_sub_mem hα (by omega) hg h
  · intro hJ x hx
    have hD := hv.conj_sub_mem_of_mem_jGroup hα.1 hJ
    rw [← hlev] at hD
    have hX := (mem_unitsFilt_iff (by omega)).1 x.2
    have ht := trace_mul_mem_ordBall_one (by push_cast; omega) hD hX
    apply Units.ext
    rw [coe_psiAlphaUnits, coe_psiAlphaUnits]
    change psiAlphaFun F ψ _ (g * x * g⁻¹) = psiAlphaFun F ψ _ x
    rw [psiAlphaFun_conj_eq, hψ.trivial _ (by rw [neg_neg]; exact ht), mul_one]

/-- Each element of $J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$ intertwines $\psi_\alpha$. -/
theorem intertwines_psiAlpha_of_mem_jGroup (hα : IsMinimalElt F n α) (hn : 1 ≤ n) {g : GL (Fin 2) F}
    (hg : g ∈ jGroup v hv ((n + 1) / 2)) :
    Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g :=
  (intertwines_psiAlpha_iff hv ψ hψ hαA hα hn (jGroup_le_normalizer hv _ hg)).2 hg

variable (ξ : Eˣ →* ℂˣ)

omit [Algebra.IsQuadraticExtension F E] in
/-- An element that intertwines a cuspidal type $\Lambda$ also intertwines $\psi_\alpha$, because $\Lambda$ restricts to $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem intertwines_psiAlpha_of_mem_cuspTypes {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ}
    (hΛ : Λ ∈ cuspTypes hv ψ hψ n α hαA ξ) {g : GL (Fin 2) F}
    (hI : Intertwines (jGroup v hv ((n + 1) / 2)) Λ g) :
    Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g := by
  intro x h
  have hm : (n + 1) / 2 ≤ n / 2 + 1 := by omega
  have e := hI ⟨x, unitsFilt_le_jGroup hv _ (unitsFilt_anti hm x.2)⟩
    (unitsFilt_le_jGroup hv _ (unitsFilt_anti hm h))
  apply Units.ext
  rw [coe_psiAlphaUnits, coe_psiAlphaUnits, ← hΛ.1 x, ← hΛ.1 ⟨_, h⟩]
  exact congrArg Units.val e

/-- The intertwining of a cuspidal type in $\mathfrak{K}_{\mathfrak{A}}$ (BH §15.1 and §15.6, the part in $\mathfrak{K}_{\mathfrak{A}}$). Let $\alpha \in E$ be minimal of level $n \ge 1$ and $\Lambda$ a cuspidal type of $J_\alpha$. An element $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\Lambda$ exactly when $g \in J_\alpha$. -/
theorem intertwines_cuspType_iff (hα : IsMinimalElt F n α) (hn : 1 ≤ n)
    {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ} (hΛ : Λ ∈ cuspTypes hv ψ hψ n α hαA ξ) {g : GL (Fin 2) F}
    (hg : g ∈ normalizer F A) :
    Intertwines (jGroup v hv ((n + 1) / 2)) Λ g ↔ g ∈ jGroup v hv ((n + 1) / 2) :=
  ⟨fun hI => (intertwines_psiAlpha_iff hv ψ hψ hαA hα hn hg).1
      (intertwines_psiAlpha_of_mem_cuspTypes hv ψ hψ hαA ξ hΛ hI),
    fun hJ => intertwines_of_mem _ Λ hJ⟩

/-- The intertwining of a cuspidal type is $J_\alpha$, under the hypothesis that each element that intertwines $\psi_\alpha$ lies in $\mathfrak{K}_{\mathfrak{A}}$ (the part of BH §15.1 outside $\mathfrak{K}_{\mathfrak{A}}$, which is not proved here). This is the form that the irreducibility criterion `Langlands.eq_smul_cIndBasic_of_isotypic` uses. -/
theorem mem_jGroup_of_intertwines_cuspType (hα : IsMinimalElt F n α) (hn : 1 ≤ n)
    (hK : ∀ g : GL (Fin 2) F,
      Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g → g ∈ normalizer F A)
    {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ} (hΛ : Λ ∈ cuspTypes hv ψ hψ n α hαA ξ) :
    ∀ g, Intertwines (jGroup v hv ((n + 1) / 2)) Λ g → g ∈ jGroup v hv ((n + 1) / 2) := by
  intro g hI
  have h := intertwines_psiAlpha_of_mem_cuspTypes hv ψ hψ hαA ξ hΛ hI
  exact (intertwines_psiAlpha_iff hv ψ hψ hαA hα hn (hK g h)).1 h

end Intertwining

end Langlands.LocalGL2
