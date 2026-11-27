/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.CIndIrreducible

/-!
# The group J is compact modulo the centre

Let $G$ be a topological group, $J$ a subgroup of $G$ and $Z$ a subgroup of the centre of $G$. The file `Langlands/Local/CIndIrreducible.lean` uses the condition `IsCompactModCenter J Z`: for each open subgroup $U$ of $J$, the subgroup $(Z \cap J) U$ has finite index in $J$. This file gives a general sufficient condition and applies it to the group $J = E^\times U^m_{\mathfrak{A}}$ of `Langlands/Local/CuspidalTypes.lean`.

The general condition is as follows. Let $K$ be a compact subgroup of $J$ such that $(Z \cap J) K$ has finite index in $J$. Then $J$ is compact modulo $Z$. The proof is a count of cosets. The subgroup $U \cap K$ is open in the compact group $K$, so it has finite index in $K$. Because $Z$ is central, each coset of $(Z \cap J) U$ in $J$ has the form $r k (Z \cap J) U$, where $r$ is a representative of a coset of $(Z \cap J) K$ and $k$ is a representative of a coset of $U \cap K$ in $K$.

For $J = E^\times U^m_{\mathfrak{A}}$ the file takes $K = U^0_{\mathfrak{A}} \cap J$, which is compact because $U^0_{\mathfrak{A}}$ is compact. Let $\varpi_E$ be a uniformizer of $E$ and $e = e(E|F)$. Each $y \in E^\times$ is $\varpi_E^k w$ with $w \in U^0_E \subseteq U^0_{\mathfrak{A}}$, and $\varpi_E^e = \varpi_F w'$ with $w' \in U^0_E$. So each coset of $F^\times K$ in $J$ is $\varpi_E^r F^\times K$ with $0 \le r < e$, and $F^\times K$ has index at most $e$ in $J$.

## Main definitions

This file has no new definitions. It uses `Langlands.IsCompactModCenter` of `Langlands/Local/CIndIrreducible.lean`.

## Main results

* `Langlands.IsCompactModCenter.mono`: the condition `IsCompactModCenter` passes to a larger group $Z$.
* `Langlands.isCompactModCenter_of_isCompact`: if $K$ is a compact subgroup of $J$ and $(Z \cap J) K$ has finite index in $J$, then $J$ is compact modulo $Z$.
* `Langlands.isCompactModCenter_of_le`: the same statement for a compact subgroup $K$ of $G$ with $K \le J$.
* `Langlands.LocalGL2.scalarGL_mem_center`, `Langlands.LocalGL2.range_scalarGL_le_center`: the scalar matrices lie in the centre of $GL_2(F)$.
* `Langlands.LocalGL2.isCompact_unitsFilt_subgroupOf`: $U^k_{\mathfrak{A}} \cap J$ is compact.
* `Langlands.LocalGL2.exists_zpow_inv_mul_mem_unitsFilt`: each $g \in J$ is $\varpi_E^k u$ with $u \in U^0_{\mathfrak{A}}$.
* `Langlands.LocalGL2.finiteIndex_jGroup`: $F^\times (U^0_{\mathfrak{A}} \cap J)$ has finite index in $J$.
* `Langlands.LocalGL2.isCompactModCenter_jGroup`, `Langlands.LocalGL2.isCompactModCenter_jGroup_center`: $J = E^\times U^m_{\mathfrak{A}}$ is compact modulo $F^\times$, and so modulo the centre of $GL_2(F)$.
* `Langlands.LocalGL2.isIrreducible_cuspInd`: for a cuspidal type $\Lambda$, if each $g$ that intertwines $\Lambda$ lies in $J_\alpha$, then $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ is irreducible.

## Implementation notes

The group $F^\times$ is the range of `Langlands.scalarGL`. The compactness of $K$ is stated for the topology of a subspace of $J$. The general result does not use that $K$ is open. The corollary `isIrreducible_cuspInd` holds for each $n$, not only for odd $n$. Its hypothesis on the intertwining has the form that `Langlands.isIrreducible_cInd` uses.

## Still open

* The computation of the intertwining $I_G(\Lambda) = J_\alpha$ of a cuspidal type (BH §15.1 and §19). With it, the hypothesis `hI` of `isIrreducible_cuspInd` goes away.
* The exact index $[J : F^\times (U^0_{\mathfrak{A}} \cap J)]$. The file proves only that it is at most $e(E|F)$.
-/

namespace Langlands

universe w

section General

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {J : Subgroup G}

omit [IsTopologicalGroup G] in
/-- If $J$ is compact modulo $Z_1$ and $Z_1 \le Z_2$, then $J$ is compact modulo $Z_2$. -/
theorem IsCompactModCenter.mono {Z₁ Z₂ : Subgroup G} (h : Z₁ ≤ Z₂)
    (hc : IsCompactModCenter J Z₁) : IsCompactModCenter J Z₂ := fun U hU => by
  have := hc U hU
  exact Subgroup.finiteIndex_of_le (sup_le_sup_right (Subgroup.subgroupOf_mono J h) U)

/-- Let $Z$ be a subgroup of the centre of $G$ and $K$ a compact subgroup of $J$ such that $(Z \cap J) K$ has finite index in $J$. Then $J$ is compact modulo $Z$: for each open subgroup $U$ of $J$, the subgroup $(Z \cap J) U$ has finite index in $J$. -/
theorem isCompactModCenter_of_isCompact {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    {K : Subgroup J} (hK : IsCompact (K : Set J)) (hKZ : (Z.subgroupOf J ⊔ K).FiniteIndex) :
    IsCompactModCenter J Z := by
  intro U hU
  set Z' := Z.subgroupOf J with hZ'def
  have hZ' : Z' ≤ Subgroup.center J := fun z hz => Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hZc hz) g)
  have : Z'.Normal := Subgroup.normal_of_le_center hZ'
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hL : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hL
  let f : (J ⧸ (Z' ⊔ K)) × (K ⧸ U.subgroupOf K) → J ⧸ (Z' ⊔ U) :=
    fun q => ((q.1.out * (q.2.out : J) : J) : J ⧸ (Z' ⊔ U))
  have hf : Function.Surjective f := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul (Z' ⊔ K) g
      obtain ⟨z, hz, k, hk, hzk⟩ := Subgroup.mem_sup_of_normal_left.1 ((Z' ⊔ K).inv_mem b.2)
      obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
      refine ⟨((g : J ⧸ (Z' ⊔ K)), ((⟨k, hk⟩ : K) : K ⧸ U.subgroupOf K)), ?_⟩
      change ((_ * _ : J) : J ⧸ (Z' ⊔ U)) = _
      rw [hb, hl, QuotientGroup.eq, Subgroup.coe_mul]
      have hc : z * k = k * z := (Subgroup.mem_center_iff.1 (hZ' hz) k).symm
      have e : (g * (b : J) * (k * ((l : K) : J)))⁻¹ * g = ((l : K) : J)⁻¹ * z := by
        have e1 : (g * (b : J) * (k * ((l : K) : J)))⁻¹ * g =
            ((l : K) : J)⁻¹ * k⁻¹ * (b : J)⁻¹ := by group
        rw [e1, ← hzk, hc]
        group
      rw [e]
      exact (Z' ⊔ U).mul_mem (Subgroup.mem_sup_right ((U.inv_mem l.2)))
        (Subgroup.mem_sup_left hz)
  have : Finite (J ⧸ (Z' ⊔ U)) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Let $Z$ be a subgroup of the centre of $G$ and $K \le J$ a compact subgroup of $G$ such that $(Z \cap J) (K \cap J)$ has finite index in $J$. Then $J$ is compact modulo $Z$. -/
theorem isCompactModCenter_of_le {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G) {K : Subgroup G}
    (hKJ : K ≤ J) (hK : IsCompact (K : Set G))
    (hKZ : (Z.subgroupOf J ⊔ K.subgroupOf J).FiniteIndex) : IsCompactModCenter J Z := by
  refine isCompactModCenter_of_isCompact hZc ?_ hKZ
  rw [Subgroup.coe_subgroupOf]
  refine Topology.IsInducing.subtypeVal.isCompact_preimage' hK ?_
  intro x hx
  exact ⟨⟨x, hKJ hx⟩, rfl⟩

end General

end Langlands

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel Matrix

section JGroupCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A scalar matrix $c \cdot 1$ lies in the centre of $GL_2(F)$. -/
theorem scalarGL_mem_center (c : Fˣ) :
    Langlands.scalarGL F 2 c ∈ Subgroup.center (GL (Fin 2) F) :=
  Subgroup.mem_center_iff.2 fun g =>
    Units.ext (Matrix.scalar_commute (c : F) (fun _ => Commute.all _ _) g.1).eq.symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The group $F^\times$ of scalar matrices lies in the centre of $GL_2(F)$. -/
theorem range_scalarGL_le_center :
    (Langlands.scalarGL F 2).range ≤ Subgroup.center (GL (Fin 2) F) := by
  rintro _ ⟨c, rfl⟩
  exact scalarGL_mem_center c

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The image of $c \in F^\times$ under $E^\times \to GL_2(F)$ is the scalar matrix $c \cdot 1$. -/
theorem embGL_algebraMap (c : Fˣ) :
    embGL v (Units.map (algebraMap F E).toMonoidHom c) = Langlands.scalarGL F 2 c := by
  ext : 1
  rw [val_embGL]
  simp [Langlands.scalarGL, Matrix.algebraMap_eq_diagonal]

/-- The group $U^k_{\mathfrak{A}} \cap J$ is compact, for the topology of a subspace of $J = E^\times U^m_{\mathfrak{A}}$. -/
theorem isCompact_unitsFilt_subgroupOf (hv : IsAdapted A v) (m k : ℕ) :
    IsCompact (((unitsFilt F A k).subgroupOf (jGroup v hv m) : Subgroup (jGroup v hv m)) :
      Set (jGroup v hv m)) := by
  rw [Subgroup.coe_subgroupOf]
  exact Topology.IsClosedEmbedding.isCompact_preimage
    (Subgroup.isClosed_of_isOpen _ (isOpen_jGroup hv m)).isClosedEmbedding_subtypeVal
    (isCompact_unitsFilt A k)

omit [Valuation.HasExtension (valuation F) (valuation E)] in
/-- A unit $w$ of $E$ with $\mathrm{ord}_E(w) = 0$ lies in $U^0_E$. -/
theorem mem_unitFilt_zero_of_ord {w : Eˣ} (h : ord E (w : E) = 0) : w ∈ unitFilt E 0 :=
  ⟨h, by exact_mod_cast sub_one_mem_ordBall_zero w.ne_zero h⟩

/-- Each $g \in J = E^\times U^m_{\mathfrak{A}}$ is $\varpi_E^k u$ with $u \in U^0_{\mathfrak{A}}$, where $\varpi_E$ is the chosen uniformizer of $E$. -/
theorem exists_zpow_inv_mul_mem_unitsFilt (hv : IsAdapted A v) (m : ℕ) {g : GL (Fin 2) F}
    (hg : g ∈ jGroup v hv m) : ∃ k : ℤ, (embGL v (unif E ^ k))⁻¹ * g ∈ unitsFilt F A 0 := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨ord E (y : E), ?_⟩
  set w : Eˣ := y * unif E ^ (-ord E (y : E)) with hw
  have hw0 : embGL v w ∈ unitsFilt F A 0 :=
    (hv.embGL_mem_unitsFilt_iff 0 w).2 (mem_unitFilt_zero_of_ord (ord_mul_unif_zpow y))
  have e : (embGL v (unif E ^ ord E (y : E)))⁻¹ * g = embGL v w * ((embGL v y)⁻¹ * g) := by
    rw [hw, mul_comm y, map_mul, map_zpow, map_zpow, zpow_neg]
    group
  rw [e]
  exact (unitsFilt F A 0).mul_mem hw0 (unitsFilt_anti (Nat.zero_le m) hy)

/-- The power $\varpi_E^e$, with $e = e(E|F)$, is $\varpi_F w$ for a unit $w$ of $E$ with $\mathrm{ord}_E(w) = 0$. In $GL_2(F)$ it is the scalar matrix $\varpi_F \cdot 1$ times an element of $U^0_{\mathfrak{A}}$. -/
theorem exists_embGL_unif_zpow_ramIdx (hv : IsAdapted A v) :
    ∃ w : Eˣ, embGL v w ∈ unitsFilt F A 0 ∧
      embGL v (unif E ^ ramIdx F E) = Langlands.scalarGL F 2 (unif F) * embGL v w := by
  set a : Eˣ := Units.map (algebraMap F E).toMonoidHom (unif F) with ha
  have ha0 : ord E (a : E) = ramIdx F E := rfl
  set w : Eˣ := unif E ^ ramIdx F E * a⁻¹ with hw
  have hw0 : ord E (w : E) = 0 := by
    rw [hw, Units.val_mul, Units.val_zpow_eq_zpow_val,
      ord_mul (zpow_ne_zero _ (unif E).ne_zero) (a⁻¹).ne_zero, ord_zpow, ord_unif,
      Units.val_inv_eq_inv_val, ord_inv a.ne_zero, ha0]
    ring
  refine ⟨w, (hv.embGL_mem_unitsFilt_iff 0 w).2 (mem_unitFilt_zero_of_ord hw0), ?_⟩
  rw [← embGL_algebraMap (E := E) (v := v), ← ha, ← map_mul]
  congr 1
  rw [hw, mul_comm, inv_mul_cancel_right]

/-- The subgroup $F^\times (U^0_{\mathfrak{A}} \cap J)$ has finite index in $J = E^\times U^m_{\mathfrak{A}}$. Each of its cosets is $\varpi_E^r F^\times (U^0_{\mathfrak{A}} \cap J)$ with $0 \le r < e(E|F)$. -/
theorem finiteIndex_jGroup (hv : IsAdapted A v) (m : ℕ) :
    ((Langlands.scalarGL F 2).range.subgroupOf (jGroup v hv m) ⊔
      (unitsFilt F A 0).subgroupOf (jGroup v hv m)).FiniteIndex := by
  set J := jGroup v hv m
  set H : Subgroup J := (Langlands.scalarGL F 2).range.subgroupOf J ⊔
    (unitsFilt F A 0).subgroupOf J with hH
  set e := ramIdx F E with he
  have he0 : 0 < e := ramIdx_pos
  let ϖ : J := ⟨embGL v (unif E), embGL_mem_jGroup hv m _⟩
  have hϖ : ∀ k : ℤ, ((ϖ ^ k : J) : GL (Fin 2) F) = embGL v (unif E ^ k) := by
    intro k
    rw [map_zpow, SubgroupClass.coe_zpow]
  have h1 : ∀ g : J, ∃ k : ℤ, (ϖ ^ k)⁻¹ * g ∈ H := by
    intro g
    obtain ⟨k, hk⟩ := exists_zpow_inv_mul_mem_unitsFilt hv m g.2
    refine ⟨k, Subgroup.mem_sup_right ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, hϖ]
    exact hk
  have h2 : ϖ ^ e ∈ H := by
    obtain ⟨w, hw, hwe⟩ := exists_embGL_unif_zpow_ramIdx (E := E) hv
    have e1 : ϖ ^ e = (⟨Langlands.scalarGL F 2 (unif F), scalarGL_mem_jGroup hv m _⟩ : J) *
        ⟨embGL v w, embGL_mem_jGroup hv m _⟩ := by
      apply Subtype.ext
      rw [hϖ, Subgroup.coe_mul]
      exact hwe
    rw [e1]
    refine H.mul_mem (Subgroup.mem_sup_left ⟨unif F, rfl⟩) (Subgroup.mem_sup_right ?_)
    exact hw
  have h3 : ∀ k : ℤ, (ϖ ^ (k % e))⁻¹ * ϖ ^ k ∈ H := by
    intro k
    have e2 : ϖ ^ k = ϖ ^ (k % e) * (ϖ ^ e) ^ (k / e) := by
      rw [← zpow_mul, ← zpow_add, Int.emod_add_mul_ediv]
    rw [e2, inv_mul_cancel_left]
    exact H.zpow_mem h2 _
  let f : Fin e.toNat → J ⧸ H := fun r => ((ϖ ^ ((r : ℕ) : ℤ) : J) : J ⧸ H)
  have hf : Function.Surjective f := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := h1 g
      have hnn : 0 ≤ k % e := Int.emod_nonneg k he0.ne'
      have hlt : k % e < e := Int.emod_lt_of_pos k he0
      refine ⟨⟨(k % e).toNat, by omega⟩, ?_⟩
      change ((ϖ ^ (((k % e).toNat : ℕ) : ℤ) : J) : J ⧸ H) = (g : J ⧸ H)
      rw [Int.toNat_of_nonneg hnn, QuotientGroup.eq]
      have := H.mul_mem (h3 k) hk
      rwa [mul_assoc, mul_inv_cancel_left] at this
  have : Finite (J ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The group $J = E^\times U^m_{\mathfrak{A}}$ is compact modulo the group $F^\times$ of scalar matrices: for each open subgroup $U$ of $J$, the subgroup $F^\times U$ has finite index in $J$. -/
theorem isCompactModCenter_jGroup (hv : IsAdapted A v) (m : ℕ) :
    IsCompactModCenter (jGroup v hv m) (Langlands.scalarGL F 2).range :=
  isCompactModCenter_of_isCompact range_scalarGL_le_center
    (isCompact_unitsFilt_subgroupOf hv m 0) (finiteIndex_jGroup hv m)

/-- The group $J = E^\times U^m_{\mathfrak{A}}$ is compact modulo the centre of $GL_2(F)$. -/
theorem isCompactModCenter_jGroup_center (hv : IsAdapted A v) (m : ℕ) :
    IsCompactModCenter (jGroup v hv m) (Subgroup.center (GL (Fin 2) F)) :=
  (isCompactModCenter_jGroup hv m).mono range_scalarGL_le_center

variable (hv : IsAdapted A v) (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) (n : ℕ) (α : E)
  (hα : Algebra.leftMulMatrix v α ∈ radPow F A (-n)) (ξ : Eˣ →* ℂˣ)

/-- Let $\Lambda$ be a cuspidal type for the simple stratum $(\mathfrak{A}, n, \alpha)$ and the character $\xi$. If each $g \in GL_2(F)$ that intertwines $\Lambda$ lies in $J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$, then $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ is irreducible (BH 11.4 and §15). -/
theorem isIrreducible_cuspInd {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ}
    (h : Λ ∈ cuspTypes hv ψ hψ n α hα ξ)
    (hI : ∀ g, Intertwines (jGroup v hv ((n + 1) / 2)) Λ g → g ∈ jGroup v hv ((n + 1) / 2)) :
    (cuspInd hv n Λ).IsIrreducible :=
  isIrreducible_cInd _ Λ (isOpen_jGroup hv _)
    (IsTypeChar.isOpen_ker hv ψ hψ n α hα ξ (hm := by omega) h) range_scalarGL_le_center
    (isCompactModCenter_jGroup hv _) hI

end JGroupCompact

end Langlands.LocalGL2
