/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2TameTypes

/-!
# Independence of the type representation

This file works toward `Langlands.LocalGL2.TypeRepIndependent K` (Bushnell and Henniart, 15.6 and §19). The claim is that for $K$-isomorphic tame admissible pairs, the representations $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ of any two data are isomorphic. The choices in a datum are the character $\psi$, the element $\alpha$, the adapted basis, the chain order and the factorization $\xi = \xi_0 \otimes \chi_L$. The file reduces the claim to one precise statement, `Langlands.LocalGL2.TypeCharUnitsAgree`, about the values of $\Lambda$ on the group $U^m_{\mathfrak{A}}$. It also proves this statement, and so the full independence, for data with the same $\psi$ and the same $\chi$.

## Main definitions

* `Langlands.LocalGL2.cIndConjMap`: the map $f \mapsto (x \mapsto f(g^{-1} x))$ from $c\text{-}\mathrm{Ind}_J^G \Lambda$ to $c\text{-}\mathrm{Ind}_{gJg^{-1}}^G \Lambda^g$.
* `Langlands.LocalGL2.basisChangeGL`: the matrix of a change of basis of $L$ over $K$, as an element of $GL_2(K)$.
* `Langlands.LocalGL2.TameDatum.transport`: the datum for $(L/K, \xi' \circ j)$ made from a datum for $(L'/K, \xi')$ and a $K$-isomorphism $j : L \cong L'$.
* `Langlands.LocalGL2.TameDatum.rebase`: the datum made from a datum by a change to a second adapted basis.
* `Langlands.LocalGL2.TypeCharUnitsAgree`: for two data of one pair with the same chain order and basis, the characters $\Lambda$ and $\Lambda'$ agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$.

## Main results

* `Langlands.LocalGL2.cInd_conj_iso`: $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{gJg^{-1}}^G \Lambda^g$.
* `Langlands.LocalGL2.cInd_congr_iso`: compact induction respects equal groups and equal characters.
* `Langlands.LocalGL2.level_comp_unitsMap` and `Langlands.LocalGL2.IsMinimal.comp_unitsMap`: the level and minimality do not change under a $K$-isomorphism of fields.
* `Langlands.LocalGL2.level_le_of_twistChar_eq`: if $\xi_0 \otimes \chi_L = \xi_0' \otimes \chi'_L$ with $\xi_0'$ minimal, then the level of $\xi_0'$ is at most the level of $\xi_0$.
* `Langlands.LocalGL2.TameDatum.transport_rep_iso`: the transported datum has an isomorphic representation.
* `Langlands.LocalGL2.TameDatum.A_eq` and `Langlands.LocalGL2.TameDatum.level_eq`: two data of one pair have the same chain order and the same level.
* `Langlands.LocalGL2.TameDatum.rebase_rep_iso`: the change of basis gives an isomorphic representation.
* `Langlands.LocalGL2.TameDatum.rep_iso_of_eq_basis`: two data with the same chain order and basis, whose characters agree on $U^m_{\mathfrak{A}}$, give isomorphic representations.
* `Langlands.LocalGL2.TameDatum.Λ_unitsFilt_eq` and `Langlands.LocalGL2.TameDatum.rep_iso_of_ψ_eq_of_χ_eq`: for $p \ne 2$, two data of one pair with the same $\psi$ and $\chi$ give isomorphic representations.
* `Langlands.LocalGL2.typeRepIndependent_of_typeCharUnitsAgree`: `Langlands.LocalGL2.TypeCharUnitsAgree K` implies `Langlands.LocalGL2.TypeRepIndependent K`.

## Proof

A $K$-isomorphism $j : L \cong L'$ with $\xi = \xi' \circ j$ moves a datum for $(L', \xi')$ to a datum for $(L, \xi)$ with the basis $j^{-1} v$. The matrices of multiplication do not change, so the groups $J_\alpha$ and the characters $\Lambda$ are the same, and the representations are equal. For two data of one pair, the chain orders are equal, because $e(\mathfrak{A}) = e(L/K)$. The levels are equal, because each $\xi_0$ is minimal and $\xi_0' = \xi_0 \otimes (\chi \chi'^{-1})_L$. A change of basis by $g \in GL_2(K)$ conjugates $\mathfrak{A}$, $J_\alpha$ and $\Lambda$, so `Langlands.LocalGL2.cInd_conj_iso` moves both data to one basis. Then $J_\alpha = L^\times U^m_{\mathfrak{A}}$ is the same group for both data. On $L^\times$ both characters equal $\xi$, since $\det \circ \iota = N_{L/K}$. So the characters are equal if they agree on $U^m_{\mathfrak{A}}$. If $\psi$ and $\chi$ are the same, then $\xi_0 = \xi_0'$, and the compatibility of $\alpha$ and $\alpha'$ with $\xi_0$ on $U^{[n/2]+1}_L$ gives $\psi(\mathrm{tr}((\alpha' - \alpha) y)) = 1$ for $y \in \mathfrak{p}^{[n/2]+1}_L$. Trace duality, for $p \ne 2$, gives $\alpha' - \alpha \in \mathfrak{p}^{-[n/2]}_L$, and then $\psi_{\alpha'} = \psi_\alpha$ on $U^m_{\mathfrak{A}}$, because $n$ is odd.

## The general case

The statement `Langlands.LocalGL2.TypeCharUnitsAgree K` in general is proved in `Langlands.Local.TypeCharAgree`, so `TypeRepIndependent` holds with no input.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§15 and 19.
-/

namespace Langlands.LocalGL2

universe w

open SmoothRep

section Conjugation

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The map $f \mapsto (x \mapsto f(g^{-1} x))$ from $c\text{-}\mathrm{Ind}_J^G \Lambda$ to $c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$, when $J' = g J g^{-1}$ and $\Lambda'(x) = \Lambda(g^{-1} x g)$. -/
noncomputable def cIndConjMap {J J' : Subgroup G} (g : G) (hJ : ∀ x, x ∈ J' ↔ g⁻¹ * x * g ∈ J)
    {Λ : J →* ℂˣ} {Λ' : J' →* ℂˣ} (hΛ : ∀ x : J', Λ' x = Λ ⟨g⁻¹ * x * g, (hJ x).1 x.2⟩) :
    (cInd J Λ).V →ₗ[ℂ] (cInd J' Λ').V where
  toFun f := ⟨fun x => cInd.toFun f (g⁻¹ * x), by
    classical
    obtain ⟨h1, ⟨U, hU, hfU⟩, S, hS⟩ := (show cIndSpace J Λ from f).2
    refine ⟨fun j x => ?_, ⟨U, hU, fun x u hu => ?_⟩, S.image (g * ·), fun x hx => ?_⟩
    · have e : g⁻¹ * (j * x) = (⟨g⁻¹ * j * g, (hJ j).1 j.2⟩ : J) * (g⁻¹ * x) := by
        simp [mul_assoc]
      change (show cIndSpace J Λ from f).1 (g⁻¹ * (j * x)) =
        Λ' j * (show cIndSpace J Λ from f).1 (g⁻¹ * x)
      rw [e, h1, hΛ]
    · change (show cIndSpace J Λ from f).1 (g⁻¹ * (x * u)) =
        (show cIndSpace J Λ from f).1 (g⁻¹ * x)
      rw [← mul_assoc, hfU _ u hu]
    · obtain ⟨s, hs, hsJ⟩ := hS (g⁻¹ * x) hx
      refine ⟨g * s, Finset.mem_image_of_mem _ hs, ?_⟩
      have e : g⁻¹ * x * s⁻¹ = g⁻¹ * (x * (g * s)⁻¹) * g := by group
      exact (hJ _).2 (e ▸ hsJ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The value of `cIndConjMap` at $x$ is $f(g^{-1} x)$. -/
theorem cInd.toFun_cIndConjMap {J J' : Subgroup G} (g : G) (hJ : ∀ x, x ∈ J' ↔ g⁻¹ * x * g ∈ J)
    {Λ : J →* ℂˣ} {Λ' : J' →* ℂˣ} (hΛ : ∀ x : J', Λ' x = Λ ⟨g⁻¹ * x * g, (hJ x).1 x.2⟩)
    (f : (cInd J Λ).V) (x : G) :
    cInd.toFun (cIndConjMap g hJ hΛ f) x = cInd.toFun f (g⁻¹ * x) :=
  rfl

/-- **Compact induction of a conjugate character.** Let $J' = g J g^{-1}$ and $\Lambda'(x) = \Lambda(g^{-1} x g)$ for $x \in J'$. Then $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$, by $f \mapsto (x \mapsto f(g^{-1} x))$. -/
theorem cInd_conj_iso {J J' : Subgroup G} (g : G) (hJ : ∀ x, x ∈ J' ↔ g⁻¹ * x * g ∈ J)
    {Λ : J →* ℂˣ} {Λ' : J' →* ℂˣ} (hΛ : ∀ x : J', Λ' x = Λ ⟨g⁻¹ * x * g, (hJ x).1 x.2⟩) :
    (cInd J Λ).Iso (cInd J' Λ') := by
  have hJ' : ∀ y, y ∈ J ↔ g⁻¹⁻¹ * y * g⁻¹ ∈ J' := fun y => by
    rw [hJ, inv_inv]
    simp [mul_assoc]
  have hΛ' : ∀ y : J, Λ y = Λ' ⟨g⁻¹⁻¹ * y * g⁻¹, (hJ' y).1 y.2⟩ := fun y => by
    rw [hΛ]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])
  refine ⟨{ cIndConjMap g hJ hΛ with
    invFun := cIndConjMap g⁻¹ hJ' hΛ'
    left_inv := fun f => cInd.ext fun x => ?_
    right_inv := fun f => cInd.ext fun x => ?_ }, fun h f => cInd.ext fun x => ?_⟩
  · change cInd.toFun (cIndConjMap g⁻¹ hJ' hΛ' (cIndConjMap g hJ hΛ f)) x = cInd.toFun f x
    rw [cInd.toFun_cIndConjMap, cInd.toFun_cIndConjMap, inv_inv, inv_mul_cancel_left]
  · change cInd.toFun (cIndConjMap g hJ hΛ (cIndConjMap g⁻¹ hJ' hΛ' f)) x = cInd.toFun f x
    rw [cInd.toFun_cIndConjMap, cInd.toFun_cIndConjMap, inv_inv, mul_inv_cancel_left]
  · change cInd.toFun (cIndConjMap g hJ hΛ ((cInd J Λ).ρ h f)) x =
      cInd.toFun ((cInd J' Λ').ρ h (cIndConjMap g hJ hΛ f)) x
    rw [cInd.toFun_cIndConjMap, cInd.toFun_ρ, cInd.toFun_ρ, cInd.toFun_cIndConjMap, mul_assoc]

/-- **Compact induction from equal subgroups.** If $J = J'$ as sets and $\Lambda$ and $\Lambda'$ agree, then $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$. -/
theorem cInd_congr_iso {J J' : Subgroup G} (hJ : ∀ x, x ∈ J' ↔ x ∈ J) {Λ : J →* ℂˣ}
    {Λ' : J' →* ℂˣ} (hΛ : ∀ x : J', Λ' x = Λ ⟨x, (hJ x).1 x.2⟩) :
    (cInd J Λ).Iso (cInd J' Λ') :=
  cInd_conj_iso 1 (fun x => by simp [hJ]) fun x => by
    rw [hΛ]
    congr 1
    exact Subtype.ext (by simp)

end Conjugation

universe u v

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)]
variable {E' : Type*} [Field E'] [ValuativeRel E'] [TopologicalSpace E']
  [IsNonarchimedeanLocalField E'] [Algebra F E'] [FiniteDimensional F E'] [Algebra.IsSeparable F E']
  [Valuation.HasExtension (valuation F) (valuation E')]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Valuation.HasExtension (valuation F) (valuation E)] [ValuativeRel E']
  [TopologicalSpace E'] [IsNonarchimedeanLocalField E'] [FiniteDimensional F E']
  [Algebra.IsSeparable F E'] [Valuation.HasExtension (valuation F) (valuation E')] in
/-- For an $F$-isomorphism $j : E \to E'$ and a basis $v$ of $E'$, the matrix of $x \in E$ in the basis $j^{-1}(v)$ is the matrix of $j(x)$ in the basis $v$. -/
theorem leftMulMatrix_basis_map (v : Module.Basis (Fin 2) F E') (j : E ≃ₐ[F] E') (x : E) :
    Algebra.leftMulMatrix (v.map j.symm.toLinearEquiv) x = Algebra.leftMulMatrix v (j x) := by
  ext a b
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.map_repr,
    Module.Basis.map_apply]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Valuation.HasExtension (valuation F) (valuation E)] [ValuativeRel E']
  [TopologicalSpace E'] [IsNonarchimedeanLocalField E'] [FiniteDimensional F E']
  [Algebra.IsSeparable F E'] [Valuation.HasExtension (valuation F) (valuation E')] in
/-- The embedding of $E^\times$ given by the basis $j^{-1}(v)$ is the embedding of $E'^\times$ given by $v$, composed with $j$. -/
theorem embGL_basis_map (v : Module.Basis (Fin 2) F E') (j : E ≃ₐ[F] E') (y : Eˣ) :
    embGL (v.map j.symm.toLinearEquiv) y = embGL v (unitsMap j y) :=
  Units.ext (by rw [val_embGL, val_embGL, val_unitsMap, leftMulMatrix_basis_map])

/-- **Transport of an adapted basis.** If $v$ is a basis of $E'$ adapted to $\mathfrak{A}$ and $j : E \to E'$ is an $F$-isomorphism, then $j^{-1}(v)$ is a basis of $E$ adapted to $\mathfrak{A}$. -/
theorem IsAdapted.basis_map {A : ChainOrder} {v : Module.Basis (Fin 2) F E'} (hv : IsAdapted A v)
    (j : E ≃ₐ[F] E') : IsAdapted A (v.map j.symm.toLinearEquiv) where
  ramIdx_eq := by
    rw [← hv.ramIdx_eq, ramIdx, ramIdx, ← ord_map j, AlgEquiv.commutes]
  ord_basis := by
    obtain ⟨s, hs⟩ := hv.ord_basis
    refine ⟨s, fun i => ?_⟩
    rw [Module.Basis.map_apply, ← ord_map j, ← hs i]
    simp
  orth c N := by
    have e : ∀ i, c i • (v.map j.symm.toLinearEquiv) i = j.symm (c i • v i) := fun i => by
      simp
    simp only [e, ← map_sum, map_mem_ordBall_iff]
    exact hv.orth c N

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Valuation.HasExtension (valuation F) (valuation E)] [ValuativeRel E']
  [TopologicalSpace E'] [IsNonarchimedeanLocalField E'] [FiniteDimensional F E']
  [Algebra.IsSeparable F E'] [Valuation.HasExtension (valuation F) (valuation E')] in
/-- The map $j$ on units composed with the map $j^{-1}$ on units is the identity. -/
theorem unitsMap_unitsMap_symm (j : E ≃ₐ[F] E') (y : E'ˣ) : unitsMap j (unitsMap j.symm y) = y :=
  Units.ext (by simp)

/-- **Transport of the group $J$.** The group $E^\times U^m_{\mathfrak{A}}$ for the basis $j^{-1}(v)$ of $E$ is the group $E'^\times U^m_{\mathfrak{A}}$ for the basis $v$ of $E'$. -/
theorem mem_jGroup_basis_map_iff {A : ChainOrder} {v : Module.Basis (Fin 2) F E'}
    (hv : IsAdapted A v) (j : E ≃ₐ[F] E') (m : ℕ) (g : GL (Fin 2) F) :
    g ∈ jGroup (v.map j.symm.toLinearEquiv) (hv.basis_map j) m ↔ g ∈ jGroup v hv m := by
  rw [mem_jGroup, mem_jGroup]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨unitsMap j y, by rwa [← embGL_basis_map]⟩
  · rintro ⟨y, hy⟩
    exact ⟨unitsMap j.symm y, by rwa [embGL_basis_map, unitsMap_unitsMap_symm]⟩

/-- For an $F$-isomorphism $j : E \to E'$, a character $\xi$ of $E'^\times$ is trivial on $U^n_{E'}$ exactly when $\xi \circ j$ is trivial on $U^n_E$. -/
theorem unitFilt_le_ker_comp_iff (ξ : E'ˣ →* ℂˣ) (j : E ≃ₐ[F] E') (n : ℕ) :
    unitFilt E n ≤ (ξ.comp (unitsMap j)).ker ↔ unitFilt E' n ≤ ξ.ker := by
  constructor
  · intro h y hy
    have hy' : unitsMap j.symm y ∈ unitFilt E n := by
      rwa [← unitsMap_mem_unitFilt_iff j, unitsMap_unitsMap_symm]
    have := h hy'
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, unitsMap_unitsMap_symm] at this
  · intro h x hx
    exact h ((unitsMap_mem_unitFilt_iff j x n).2 hx)

/-- **Transport of the level.** For an admissible character $\xi$ of $E'^\times$ and an $F$-isomorphism $j : E \to E'$, the level of $\xi \circ j$ is the level of $\xi$. -/
theorem level_comp_unitsMap [Algebra.IsQuadraticExtension F E'] {ξ : E'ˣ →* ℂˣ} (h : IsAdmissible F E' ξ) (j : E ≃ₐ[F] E') :
    level (ξ.comp (unitsMap j)) = level ξ := by
  have hl := h.isLevel_level
  refine IsLevel.level_eq ⟨?_, ?_⟩
  · exact (unitFilt_le_ker_comp_iff ξ j _).2 hl.1
  · rw [unitFilt_le_ker_comp_iff]
    exact hl.2

/-- **Transport of minimality.** If $(E'/F, \xi)$ is minimal and $j : E \to E'$ is an $F$-isomorphism, then $(E/F, \xi \circ j)$ is minimal. -/
theorem IsMinimal.comp_unitsMap [Algebra.IsQuadraticExtension F E'] {ξ : E'ˣ →* ℂˣ} (h : IsMinimal F E' ξ) (j : E ≃ₐ[F] E') :
    IsMinimal F E (ξ.comp (unitsMap j)) where
  admissible := h.admissible.comp_unitsMap j
  not_factor_level := by
    rintro ⟨φ, hφ⟩
    refine h.not_factor_level ⟨φ, fun u hu => ?_⟩
    rw [level_comp_unitsMap h.admissible] at hφ
    have hu' : unitsMap j.symm u ∈ unitFilt E (level ξ) := by
      rwa [← unitsMap_mem_unitFilt_iff j, unitsMap_unitsMap_symm]
    have h1 := hφ _ hu'
    have h3 : normUnits F E (unitsMap j.symm u) = normUnits F E' u :=
      DFunLike.congr_fun (normUnits_comp_unitsMap j.symm) u
    rwa [MonoidHom.comp_apply, unitsMap_unitsMap_symm, h3] at h1

/-- **Transport of a minimal element.** If $\alpha \in E'$ is minimal of level $n$ over $F$, then so is $j^{-1}(\alpha) \in E$. -/
theorem IsMinimalElt.algEquiv_symm {n : ℕ} {α : E'} (h : IsMinimalElt F n α) (j : E ≃ₐ[F] E') :
    IsMinimalElt F n (j.symm α) := by
  refine ⟨(map_mem_ordBall_iff j.symm α _).2 h.1, fun a ha => h.2 a ?_⟩
  rwa [← map_mem_ordBall_iff j.symm, map_sub, AlgEquiv.commutes]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Valuation.HasExtension (valuation F) (valuation E)] [ValuativeRel E']
  [TopologicalSpace E'] [IsNonarchimedeanLocalField E'] [FiniteDimensional F E']
  [Algebra.IsSeparable F E'] [Valuation.HasExtension (valuation F) (valuation E')] in
/-- **Transport of a twist.** $(\xi \otimes \chi_{E'}) \circ j = (\xi \circ j) \otimes \chi_E$. -/
theorem twistChar_comp_unitsMap (ξ : E'ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (j : E ≃ₐ[F] E') :
    (twistChar F E' ξ χ).comp (unitsMap j) = twistChar F E (ξ.comp (unitsMap j)) χ := by
  ext x
  have h : normUnits F E' (unitsMap j x) = normUnits F E x :=
    DFunLike.congr_fun (normUnits_comp_unitsMap j) x
  simp only [MonoidHom.comp_apply, twistChar_apply, h]

omit [FiniteDimensional F E] in
/-- **Two minimal factorizations have the same level.** Let $\xi_0$ be admissible and $\xi_0'$ minimal, with $\xi_0 \otimes \chi_E = \xi_0' \otimes \chi'_E$. Then $\ell(\xi_0') \le \ell(\xi_0)$. Otherwise $\xi_0$ is trivial on $U^{\ell(\xi_0')}_E$, and there $\xi_0' = (\chi \chi'^{-1}) \circ N_{E/F}$, which minimality forbids. -/
theorem level_le_of_twistChar_eq [Algebra.IsQuadraticExtension F E] {ξ₀ ξ₀' : Eˣ →* ℂˣ}
    {χ χ' : Fˣ →* ℂˣ} (h0 : IsAdmissible F E ξ₀) (h0' : IsMinimal F E ξ₀')
    (h : twistChar F E ξ₀ χ = twistChar F E ξ₀' χ') : level ξ₀' ≤ level ξ₀ := by
  by_contra hlt
  push Not at hlt
  refine h0'.not_factor_level ⟨χ * χ'⁻¹, fun u hu => ?_⟩
  have h1 : ξ₀ u = 1 := h0.isLevel_level.1 (unitFilt_anti hlt hu)
  have h2 := DFunLike.congr_fun h u
  rw [twistChar_apply, twistChar_apply, h1, one_mul] at h2
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h2, mul_inv_cancel_right]

end Transport

section Rebase

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]

/-- The change of basis matrix from $v$ to $v'$, as an element of $GL_2(F)$. Its columns are the coordinates of the vectors $v'_j$ in the basis $v$. -/
noncomputable def basisChangeGL (v v' : Module.Basis (Fin 2) F E) : GL (Fin 2) F :=
  ⟨v.toMatrix v', v'.toMatrix v, v.toMatrix_mul_toMatrix_flip v', v'.toMatrix_mul_toMatrix_flip v⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The matrix of the change of basis. -/
theorem val_basisChangeGL (v v' : Module.Basis (Fin 2) F E) :
    ((basisChangeGL v v' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = v.toMatrix v' :=
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The matrix of the inverse of the change of basis. -/
theorem val_basisChangeGL_inv (v v' : Module.Basis (Fin 2) F E) :
    (((basisChangeGL v v')⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = v'.toMatrix v :=
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- **Change of basis for the matrix of $x$.** With $g$ the change of basis from $v$ to $v'$, the matrix of $x$ in the basis $v'$ is $g^{-1} M_v(x) g$. -/
theorem leftMulMatrix_basisChange (v v' : Module.Basis (Fin 2) F E) (x : E) :
    Algebra.leftMulMatrix v' x = v'.toMatrix v * Algebra.leftMulMatrix v x * v.toMatrix v' := by
  rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The embedding of $E^\times$ for the basis $v'$ is the conjugate $g^{-1} (\cdot) g$ of the embedding for $v$, with $g$ the change of basis. -/
theorem embGL_basisChange (v v' : Module.Basis (Fin 2) F E) (y : Eˣ) :
    embGL v' y = (basisChangeGL v v')⁻¹ * embGL v y * basisChangeGL v v' :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, val_embGL, val_embGL, leftMulMatrix_basisChange,
    val_basisChangeGL, val_basisChangeGL_inv])

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The action of $Y$ through the basis $v'$ is the action of $g Y g^{-1}$ through the basis $v$, with $g$ the change of basis. -/
theorem act_basisChange (v v' : Module.Basis (Fin 2) F E) (Y : Matrix (Fin 2) (Fin 2) F) (y : E) :
    act v' Y y = act v (v.toMatrix v' * Y * v'.toMatrix v) y := by
  have h1 : ∀ z, v.equivFun (v'.equivFun.symm z) = v.toMatrix v' *ᵥ z := fun z => by
    rw [Module.Basis.equivFun_apply, ← Module.Basis.toMatrix_mulVec_repr (b := v') (b' := v),
      ← Module.Basis.equivFun_apply v', LinearEquiv.apply_symm_apply]
  have h2 : v'.repr y = v'.toMatrix v *ᵥ v.repr y :=
    (Module.Basis.toMatrix_mulVec_repr (b := v) (b' := v') y).symm
  apply v.equivFun.injective
  simp only [act, LinearEquiv.apply_symm_apply, h1, Module.Basis.equivFun_apply, h2,
    Matrix.mulVec_mulVec, mul_assoc]

/-- **Change of basis for $\mathfrak{P}^n_{\mathfrak{A}}$.** Let $v$ and $v'$ be two bases of $E$ adapted to $\mathfrak{A}$, and $g$ the change of basis. Then $Y \in \mathfrak{P}^n_{\mathfrak{A}}$ exactly when $g Y g^{-1} \in \mathfrak{P}^n_{\mathfrak{A}}$. -/
theorem mem_radPow_basisChange_iff {A : ChainOrder} {v v' : Module.Basis (Fin 2) F E}
    (hv : IsAdapted A v) (hv' : IsAdapted A v') (n : ℤ) (Y : Matrix (Fin 2) (Fin 2) F) :
    v.toMatrix v' * Y * v'.toMatrix v ∈ radPow F A n ↔ Y ∈ radPow F A n := by
  rw [hv.mem_radPow_iff n, hv'.mem_radPow_iff n Y]
  simp only [act_basisChange v v']

/-- **Change of basis for $U^m_{\mathfrak{A}}$.** Let $v$ and $v'$ be two bases of $E$ adapted to $\mathfrak{A}$, and $g$ the change of basis. Then $g u g^{-1} \in U^m_{\mathfrak{A}}$ exactly when $u \in U^m_{\mathfrak{A}}$. -/
theorem mem_unitsFilt_basisChange_iff {A : ChainOrder} {v v' : Module.Basis (Fin 2) F E}
    (hv : IsAdapted A v) (hv' : IsAdapted A v') (m : ℕ) (u : GL (Fin 2) F) :
    basisChangeGL v v' * u * (basisChangeGL v v')⁻¹ ∈ unitsFilt F A m ↔ u ∈ unitsFilt F A m := by
  set g := basisChangeGL v v'
  have e1 : ((g * u * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      v.toMatrix v' * (u : Matrix (Fin 2) (Fin 2) F) * v'.toMatrix v := by
    rw [Units.val_mul, Units.val_mul, val_basisChangeGL, val_basisChangeGL_inv]
  have e2 : (((g * u * g⁻¹)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      v.toMatrix v' * ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * v'.toMatrix v := by
    rw [show (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ by group, Units.val_mul, Units.val_mul,
      val_basisChangeGL, val_basisChangeGL_inv]
  have e3 : ((g * u * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
      v.toMatrix v' * ((u : Matrix (Fin 2) (Fin 2) F) - 1) * v'.toMatrix v := by
    rw [e1, mul_sub, sub_mul, mul_one, v.toMatrix_mul_toMatrix_flip v']
  change (_ ∈ order F A ∧ _ ∈ order F A ∧ _ ∈ radPow F A m) ↔
    (_ ∈ order F A ∧ _ ∈ order F A ∧ _ ∈ radPow F A m)
  rw [e3, e2, e1, mem_order, mem_order, mem_order, mem_order,
    mem_radPow_basisChange_iff hv hv', mem_radPow_basisChange_iff hv hv',
    mem_radPow_basisChange_iff hv hv']

/-- **Change of basis for $J$.** Let $v$ and $v'$ be two bases of $E$ adapted to $\mathfrak{A}$, and $g$ the change of basis. Then $x \in E^\times U^m_{\mathfrak{A}}$ for $v$ exactly when $g^{-1} x g \in E^\times U^m_{\mathfrak{A}}$ for $v'$. -/
theorem mem_jGroup_basisChange_iff {A : ChainOrder} {v v' : Module.Basis (Fin 2) F E}
    (hv : IsAdapted A v) (hv' : IsAdapted A v') (m : ℕ) (x : GL (Fin 2) F) :
    x ∈ jGroup v hv m ↔ (basisChangeGL v v')⁻¹ * x * basisChangeGL v v' ∈ jGroup v' hv' m := by
  have key : ∀ y : Eˣ, (embGL v' y)⁻¹ * ((basisChangeGL v v')⁻¹ * x * basisChangeGL v v') ∈
      unitsFilt F A m ↔
      (embGL v y)⁻¹ * x ∈ unitsFilt F A m := fun y => by
    rw [← mem_unitsFilt_basisChange_iff hv hv' m, embGL_basisChange v v']
    congr! 1
    group
  rw [mem_jGroup, mem_jGroup]
  simp only [key]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The trace of $g^{-1} X g$ is the trace of $X$, for the change of basis $g$. -/
theorem trace_basisChange (v v' : Module.Basis (Fin 2) F E) (X : Matrix (Fin 2) (Fin 2) F) :
    (v'.toMatrix v * X * v.toMatrix v').trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, v.toMatrix_mul_toMatrix_flip v', one_mul]

/-- Conjugation by the change of basis, as a homomorphism from $E^\times U^m_{\mathfrak{A}}$ for $v$ to $E^\times U^m_{\mathfrak{A}}$ for $v'$. -/
noncomputable def jGroupBasisChange {A : ChainOrder} {v v' : Module.Basis (Fin 2) F E}
    (hv : IsAdapted A v) (hv' : IsAdapted A v') (m : ℕ) : jGroup v hv m →* jGroup v' hv' m where
  toFun x := ⟨(basisChangeGL v v')⁻¹ * x * basisChangeGL v v',
    (mem_jGroup_basisChange_iff hv hv' m x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

end Rebase

section Datum

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]

/-- The same datum, seen as a datum for an equal character $\xi'$. -/
noncomputable def congrChar {ξ ξ' : Lˣ →* ℂˣ} (D : TameDatum K L ξ) (h : ξ = ξ') :
    TameDatum K L ξ' :=
  { D with eq := h ▸ D.eq }

/-- The representation of `TameDatum.congrChar` is the representation of the datum. -/
theorem congrChar_rep {ξ ξ' : Lˣ →* ℂˣ} (D : TameDatum K L ξ) (h : ξ = ξ') :
    (D.congrChar h).rep = D.rep :=
  rfl

variable [Algebra.IsSeparable K L] {L' : IntermediateField K (AlgebraicClosure K)}
  [Algebra.IsQuadraticExtension K L'] [Algebra.IsSeparable K L'] {ξ' : L'ˣ →* ℂˣ}

/-- The group $J_\alpha$ of the transported datum lies in the group $J_\alpha$ of the datum. -/
theorem transport_jGroup_le (D : TameDatum K L' ξ') (j : L ≃ₐ[K] L') :
    jGroup (D.v.map j.symm.toLinearEquiv) (D.hv.basis_map j)
      ((level (D.ξ₀.comp (unitsMap j)) + 1) / 2) ≤ D.J := fun g hg => by
  rw [level_comp_unitsMap D.minimal.admissible] at hg
  exact (mem_jGroup_basis_map_iff D.hv j _ g).1 hg

/-- **Transport of a datum** along a $K$-isomorphism $j : L \to L'$. A datum for $(L'/K, \xi')$ gives a datum for $(L/K, \xi' \circ j)$, with the basis $j^{-1}(v)$, the character $\xi_0 \circ j$ and the element $j^{-1}(\alpha)$. The group $J_\alpha$ and the character $\Lambda$ do not change. -/
noncomputable def transport (D : TameDatum K L' ξ') (j : L ≃ₐ[K] L') :
    TameDatum K L (ξ'.comp (unitsMap j)) where
  ψ := D.ψ
  hψ := D.hψ
  A := D.A
  v := D.v.map j.symm.toLinearEquiv
  hv := D.hv.basis_map j
  ξ₀ := D.ξ₀.comp (unitsMap j)
  α := j.symm D.α
  hα := by
    rw [leftMulMatrix_basis_map, AlgEquiv.apply_symm_apply,
      level_comp_unitsMap D.minimal.admissible]
    exact D.hα
  Λ₀ := D.Λ₀.comp (Subgroup.inclusion (D.transport_jGroup_le j))
  χ := D.χ
  Λ := D.Λ.comp (Subgroup.inclusion (D.transport_jGroup_le j))
  minimal := D.minimal.comp_unitsMap j
  odd := by
    rw [level_comp_unitsMap D.minimal.admissible]
    exact D.odd
  minElt := by
    rw [level_comp_unitsMap D.minimal.admissible]
    exact D.minElt.algEquiv_symm j
  mem := by
    have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega)
        D.Λ₀ := D.mem
    have hl := level_comp_unitsMap D.minimal.admissible j
    refine ⟨fun ⟨g, hg0⟩ => ?_, fun y => ?_⟩
    · have hg : g ∈ unitsFilt K D.A (level D.ξ₀ / 2 + 1) := by
        rwa [hl] at hg0
      have h1 := hmem.1 ⟨g, hg⟩
      rw [psiAlpha_apply] at h1
      rw [psiAlpha_apply, leftMulMatrix_basis_map, AlgEquiv.apply_symm_apply, ← h1]
      rfl
    · change D.Λ₀ _ = D.ξ₀ (unitsMap j y)
      rw [← hmem.2 (unitsMap j y)]
      exact congrArg D.Λ₀ (Subtype.ext (embGL_basis_map D.v j y))
  smooth := D.smooth
  eq := (congrArg (·.comp (unitsMap j)) D.eq).trans (twistChar_comp_unitsMap _ _ _)
  mul x := D.mul _

/-- **The representation of a transported datum** is the representation of the datum. -/
theorem transport_rep_iso (D : TameDatum K L' ξ') (j : L ≃ₐ[K] L') :
    D.rep.Iso (D.transport j).rep := by
  refine cInd_congr_iso (fun g => ⟨fun hg => D.transport_jGroup_le j hg, fun hg => ?_⟩)
    fun _ => rfl
  rw [level_comp_unitsMap D.minimal.admissible, mem_jGroup_basis_map_iff]
  exact hg

end TameDatum

/-- A chain order is determined by its period $e_{\mathfrak{A}}$. -/
theorem ChainOrder.eq_of_e_eq {A A' : ChainOrder} (h : A.e = A'.e) : A = A' := by
  cases A <;> cases A' <;> simp_all [ChainOrder.e]

namespace TameDatum

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  {ξ : Lˣ →* ℂˣ}

/-- **The chain order of a datum** is determined by $L$: it is $\mathfrak{M}$ for $L/K$ unramified and $\mathfrak{J}$ for $L/K$ ramified, because its period is $e(L|K)$. -/
theorem A_eq (D D' : TameDatum K L ξ) : D'.A = D.A :=
  ChainOrder.eq_of_e_eq (D'.hv.ramIdx_eq.symm.trans D.hv.ramIdx_eq)

/-- **The level of a datum** does not depend on the factorization: two data for $(L/K, \xi)$ have minimal characters of the same level. -/
theorem level_eq [Algebra.IsSeparable K L] (D D' : TameDatum K L ξ) : level D'.ξ₀ = level D.ξ₀ :=
  le_antisymm (level_le_of_twistChar_eq D.minimal.admissible D'.minimal (D.eq.symm.trans D'.eq))
    (level_le_of_twistChar_eq D'.minimal.admissible D.minimal (D'.eq.symm.trans D.eq))

/-- **Rebasing a datum.** For a basis $v$ of $L$ adapted to the chain order of a datum $D$, the datum with the basis $v$, the same $\psi$, $\xi_0$, $\alpha$ and $\chi$, and the characters $\Lambda_0$ and $\Lambda$ composed with the conjugation by the change of basis $g$ from $v$ to the basis of $D$. -/
noncomputable def rebase (D : TameDatum K L ξ) (v : Module.Basis (Fin 2) K L) (hv : IsAdapted D.A v) :
    TameDatum K L ξ where
  ψ := D.ψ
  hψ := D.hψ
  A := D.A
  v := v
  hv := hv
  ξ₀ := D.ξ₀
  α := D.α
  hα := by
    rw [leftMulMatrix_basisChange D.v v]
    exact (mem_radPow_basisChange_iff hv D.hv _ _).2 D.hα
  Λ₀ := D.Λ₀.comp (jGroupBasisChange hv D.hv _)
  χ := D.χ
  Λ := D.Λ.comp (jGroupBasisChange hv D.hv _)
  minimal := D.minimal
  odd := D.odd
  minElt := D.minElt
  mem := by
    have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega)
        D.Λ₀ := D.mem
    have hPQ := v.toMatrix_mul_toMatrix_flip D.v
    refine ⟨fun u => ?_, fun y => ?_⟩
    · have hu : (basisChangeGL v D.v)⁻¹ * u * basisChangeGL v D.v ∈
          unitsFilt K D.A (level D.ξ₀ / 2 + 1) := by
        rw [← mem_unitsFilt_basisChange_iff hv D.hv]
        convert u.2 using 1
        group
      have h1 := hmem.1 ⟨_, hu⟩
      rw [psiAlpha_apply] at h1
      rw [psiAlpha_apply]
      change (D.Λ₀ ⟨(basisChangeGL v D.v)⁻¹ * u * basisChangeGL v D.v, _⟩ : ℂ) = _
      rw [h1, Units.val_mul, Units.val_mul, val_basisChangeGL, val_basisChangeGL_inv,
        leftMulMatrix_basisChange v D.v]
      congr 1
      rw [← trace_basisChange v D.v (Algebra.leftMulMatrix v D.α *
        (((u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1))]
      congr 1
      calc D.v.toMatrix v * Algebra.leftMulMatrix v D.α * v.toMatrix D.v *
            (D.v.toMatrix v * ((u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * v.toMatrix D.v - 1)
          = D.v.toMatrix v * Algebra.leftMulMatrix v D.α * (v.toMatrix D.v * D.v.toMatrix v) *
              ((u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * v.toMatrix D.v -
            D.v.toMatrix v * Algebra.leftMulMatrix v D.α * v.toMatrix D.v := by noncomm_ring
        _ = _ := by rw [hPQ, mul_one]; noncomm_ring
    · change D.Λ₀ ⟨(basisChangeGL v D.v)⁻¹ * embGL v y * basisChangeGL v D.v, _⟩ = D.ξ₀ y
      rw [← hmem.2 y]
      exact congrArg D.Λ₀ (Subtype.ext (embGL_basisChange v D.v y).symm)
  smooth := D.smooth
  eq := D.eq
  mul x := by
    change D.Λ (jGroupBasisChange hv D.hv _ x) =
      D.Λ₀ (jGroupBasisChange hv D.hv _ x) * detChar K 2 D.χ (x : GL (Fin 2) K)
    rw [D.mul]
    congr 1
    change detChar K 2 D.χ ((basisChangeGL v D.v)⁻¹ * x * basisChangeGL v D.v) = _
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]

/-- **The representation of a rebased datum** is isomorphic to the representation of the datum, because the two characters are conjugate by the change of basis. -/
theorem rebase_rep_iso (D : TameDatum K L ξ) (v : Module.Basis (Fin 2) K L)
    (hv : IsAdapted D.A v) : D.rep.Iso (D.rebase v hv).rep :=
  cInd_conj_iso (basisChangeGL v D.v) (fun x => mem_jGroup_basisChange_iff hv D.hv _ x)
    fun _ => rfl

/-- The character $\Lambda$ of a datum restricts to $\xi$ on $L^\times$, because $\det \circ \iota = N_{L/K}$ for the embedding $\iota$ of $L^\times$. -/
theorem Λ_embGL (D : TameDatum K L ξ) (y : Lˣ) :
    D.Λ ⟨embGL D.v y, embGL_mem_jGroup D.hv _ y⟩ = ξ y := by
  have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega)
      D.Λ₀ := D.mem
  have hdet : Matrix.GeneralLinearGroup.det (embGL D.v y) = normUnits K L y := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_normUnits, val_embGL,
      Algebra.norm_eq_matrix_det D.v]
  rw [D.mul, hmem.2 y, DFunLike.congr_fun D.eq y, twistChar_apply]
  simp only [detChar, MonoidHom.comp_apply, hdet]

/-- **Data with the same basis.** Let $D$ and $D'$ be two data for $(L/K, \xi)$ with the same chain order and the same basis, and with characters $\Lambda$ and $\Lambda'$ that agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$. Then the two groups $J_\alpha$ are equal, the two characters are equal, and $\pi_D \cong \pi_{D'}$. -/
theorem rep_iso_of_eq_basis [Algebra.IsSeparable K L] (D D' : TameDatum K L ξ) (hA : D'.A = D.A) (hv : D'.v = D.v)
    (hU : ∀ (u : GL (Fin 2) K) (hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2))
      (hu' : u ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2)),
      D'.Λ ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ = D.Λ ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩) :
    D.rep.Iso D'.rep := by
  have hl := D.level_eq D'
  have hJ : ∀ x, x ∈ D'.J ↔ x ∈ D.J := fun x => by
    rw [mem_jGroup, mem_jGroup, hA, hv, hl]
  refine cInd_congr_iso hJ fun x => ?_
  obtain ⟨y, u, hu', hx⟩ := (mem_jGroup_iff_exists_mul D'.hv _ x).1 x.2
  have hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2) := by
    rwa [hA, hl] at hu'
  have e' : x = ⟨embGL D'.v y, embGL_mem_jGroup D'.hv _ y⟩ * ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ :=
    Subtype.ext hx
  have e : (⟨x, (hJ x).1 x.2⟩ : D.J) =
      ⟨embGL D.v y, embGL_mem_jGroup D.hv _ y⟩ * ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩ :=
    Subtype.ext (by rw [hx, hv]; rfl)
  rw [e, e', map_mul, map_mul, Λ_embGL, Λ_embGL, hU u hu hu']

/-- **Data with the same $\psi$ and $\chi$** (Bushnell and Henniart, §15). Let $p \ne 2$, and let $D$ and $D'$ be two data for $(L/K, \xi)$ with the same basis, character $\psi$ and character $\chi$. Then $\Lambda$ and $\Lambda'$ agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$. Here $\xi_0 = \xi_0'$, so $\psi(\mathrm{tr}((\alpha' - \alpha) y)) = 1$ for $y \in \mathfrak{p}^m_L$, and trace duality gives $\alpha' - \alpha \in \mathfrak{p}^{1-m}_L$. -/
theorem Λ_unitsFilt_eq (h2 : (2 : 𝓀[K]) ≠ 0) [Algebra.IsSeparable K L] (D D' : TameDatum K L ξ)
    (hv : D'.v = D.v) (hψ : D'.ψ = D.ψ) (hχ : D'.χ = D.χ) (u : GL (Fin 2) K)
    (hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2))
    (hu' : u ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2)) :
    D'.Λ ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ = D.Λ ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩ := by
  have hl := D.level_eq D'
  have hξ₀ : D'.ξ₀ = D.ξ₀ := by
    ext1 y
    have h := (DFunLike.congr_fun D'.eq.symm y).trans (DFunLike.congr_fun D.eq y)
    rw [twistChar_apply, twistChar_apply, hχ] at h
    exact mul_right_cancel h
  obtain ⟨k, hk⟩ := D.odd
  have hc := isCompatible_of_mem_cuspTypes (h := D.mem)
  have hc' := isCompatible_of_mem_cuspTypes (h := D'.mem)
  have hδ : D'.α - D.α ∈ ordBall L (-((level D.ξ₀ / 2 : ℕ) : ℤ)) := by
    have key : ∀ y ∈ ordBall L ((level D.ξ₀ / 2 + 1 : ℕ) : ℤ),
        D.ψ (Algebra.trace K L ((D'.α - D.α) * y)) = 1 := fun y hy => by
      obtain ⟨x, hx, hxe⟩ := exists_unitFilt_one_add (by omega) hy
      have e1 := hc x hx
      have e2 := hc' x (by rwa [hl])
      rw [hxe, add_sub_cancel_left] at e1 e2
      rw [hξ₀, hψ] at e2
      rw [sub_mul, map_sub, AddChar.map_sub_eq_div, ← e1, ← e2, div_self (Units.ne_zero _)]
    have := mem_ordBall_of_forall_psi_trace h2 D.hψ key
    convert this using 2
    push_cast
    ring
  have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega)
      D.Λ₀ := D.mem
  have hmem' : IsTypeChar D'.hv D'.ψ D'.hψ _ D'.α D'.hα D'.ξ₀ ((level D'.ξ₀ + 1) / 2) (by omega)
      D'.Λ₀ := D'.mem
  have hu2 : u ∈ unitsFilt K D.A (level D.ξ₀ / 2 + 1) := unitsFilt_anti (by omega) hu
  have hu2' : u ∈ unitsFilt K D'.A (level D'.ξ₀ / 2 + 1) := unitsFilt_anti (by omega) hu'
  have h1 := hmem.1 ⟨u, hu2⟩
  have h1' := hmem'.1 ⟨u, hu2'⟩
  rw [psiAlpha_apply] at h1 h1'
  rw [D'.mul, D.mul, hχ]
  congr 1
  refine Units.ext ?_
  rw [h1, h1', hψ, hv]
  have e : Algebra.leftMulMatrix D.v D'.α =
      Algebra.leftMulMatrix D.v D.α + Algebra.leftMulMatrix D.v (D'.α - D.α) := by
    rw [map_sub]
    abel
  have ht := trace_mul_mem_ordBall_one (by push_cast; omega)
    ((D.hv.leftMulMatrix_mem_radPow_iff _ _).2 hδ) ((mem_unitsFilt_iff (by omega)).1 hu2)
  have h0 : D.ψ ((Algebra.leftMulMatrix D.v (D'.α - D.α) * ((u : Matrix (Fin 2) (Fin 2) K) - 1)).trace) =
      1 := D.hψ.trivial _ (by rw [neg_neg]; exact ht)
  rw [e, add_mul, Matrix.trace_add, AddChar.map_add_eq_mul]
  change _ * D.ψ ((Algebra.leftMulMatrix D.v (D'.α - D.α) *
    ((u : Matrix (Fin 2) (Fin 2) K) - 1)).trace) = _
  rw [h0, mul_one]

/-- **Independence of $\alpha$, the basis and the chain of lattices** (Bushnell and Henniart, §15). Let $p \ne 2$. Two data for $(L/K, \xi)$ with the same character $\psi$ and the same character $\chi$ give isomorphic representations. -/
theorem rep_iso_of_ψ_eq_of_χ_eq (h2 : (2 : 𝓀[K]) ≠ 0) [Algebra.IsSeparable K L]
    (D D' : TameDatum K L ξ) (hψ : D'.ψ = D.ψ) (hχ : D'.χ = D.χ) : D.rep.Iso D'.rep := by
  have hA := D.A_eq D'
  have hv' : IsAdapted D'.A D.v := hA ▸ D.hv
  exact (rep_iso_of_eq_basis D (D'.rebase D.v hv') hA rfl
    (Λ_unitsFilt_eq h2 D (D'.rebase D.v hv') rfl hψ hχ)).trans (D'.rebase_rep_iso D.v hv').symm

end TameDatum

variable (K) in
/-- **The type characters agree on $U^m_{\mathfrak{A}}$** (Bushnell and Henniart, §15 and §19). Let $p \ne 2$. Let $D$ and $D'$ be two data for one pair $(L/K, \xi)$, with the same chain order $\mathfrak{A}$ and the same basis. Then the characters $\Lambda = \psi_\alpha \cdot (\chi \circ \det)$ and $\Lambda' = \psi'_{\alpha'} \cdot (\chi' \circ \det)$ agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$. -/
def TypeCharUnitsAgree : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P : TamePair K) (D D' : TameDatum K P.L P.ξ), D'.A = D.A → D'.v = D.v →
    ∀ (u : GL (Fin 2) K) (hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2))
      (hu' : u ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2)),
      D'.Λ ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ = D.Λ ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩

/-- **Two data for one pair** give isomorphic representations, if `Langlands.LocalGL2.TypeCharUnitsAgree` holds. The second datum is first rebased to the basis of the first datum. -/
theorem rep_iso_of_typeCharUnitsAgree (h : TypeCharUnitsAgree K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (P : TamePair K) (D D' : TameDatum K P.L P.ξ) : D.rep.Iso D'.rep := by
  have hA := D.A_eq D'
  have hv' : IsAdapted D'.A D.v := hA ▸ D.hv
  exact (TameDatum.rep_iso_of_eq_basis D (D'.rebase D.v hv') hA rfl
    (h h2 P D (D'.rebase D.v hv') hA rfl)).trans (D'.rebase_rep_iso D.v hv').symm

/-- **The type representation does not depend on the choices**, if `Langlands.LocalGL2.TypeCharUnitsAgree` holds. A $K$-isomorphism of pairs moves a datum to a datum for the first pair, with the same representation. -/
theorem typeRepIndependent_of_typeCharUnitsAgree (h : TypeCharUnitsAgree K) :
    TypeRepIndependent K := by
  rintro h2 P Q D D' ⟨j, hj⟩
  exact (rep_iso_of_typeCharUnitsAgree h h2 P D ((D'.transport j).congrChar hj.symm)).trans
    (D'.transport_rep_iso j).symm

end Datum

end Langlands.LocalGL2
