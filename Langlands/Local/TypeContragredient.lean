/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2TameTypes
import Langlands.Local.CIndAdmissible

/-!
# The contragredient of a type representation

Let $G$ be a topological group, $J$ an open subgroup of $G$ that is compact modulo a central subgroup $Z$, and $\Lambda$ a character of $J$ with open kernel whose intertwining is $J$. Let $\pi = c\text{-}\mathrm{Ind}_J^G \Lambda$ and let $f_0$ be the vector `Langlands.cIndBasic`. This file proves that the contragredient of $\pi$ is isomorphic to $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$, when $\pi$ is admissible and each open subgroup of $G$ contains a compact open subgroup. For $G = GL_2(K)$ both conditions hold. With this, the file proves `Langlands.LocalGL2.TypeRepContragredient` (Bushnell and Henniart, 19.4).

## Main definitions

* `Langlands.LocalGL2.contraFun`: the function $x \mapsto \lambda(\pi(x^{-1}) f_0)$ on $G$, for a linear form $\lambda$ on $\pi$.
* `Langlands.LocalGL2.contraMap`: the map $\lambda \mapsto (x \mapsto \lambda(\pi(x^{-1}) f_0))$ from $\pi^\vee$ to $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$.
* `Langlands.LocalGL2.TameDatum.inv`: the datum for $\xi^{-1}$ made from a datum for $\xi$, with $\xi_0^{-1}$, $-\alpha$, $\Lambda_0^{-1}$ and $\chi^{-1}$.

## Main results

* `Langlands.LocalGL2.iso_contragredient_of_iso`: isomorphic representations have isomorphic contragredients.
* `Langlands.LocalGL2.exists_finset_contraFun`: for a smooth linear form $\lambda$, the support of `contraFun` lies in finitely many cosets $J s$.
* `Langlands.LocalGL2.contragredient_cInd_iso`: $(c\text{-}\mathrm{Ind}_J^G \Lambda)^\vee \cong c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$, for an admissible $\pi$.
* `Langlands.LocalGL2.contragredient_cInd_iso_GL2`: the same statement for $GL_2(K)$, with no admissibility hypothesis.
* `Langlands.LocalGL2.level_inv_char`, `Langlands.LocalGL2.IsMinimal.inv`, `Langlands.LocalGL2.IsMinimalElt.neg`, `Langlands.LocalGL2.inv_mem_cuspTypes`: the inputs for the inverse datum.
* `Langlands.LocalGL2.TameDatum.inv_rep_iso`: the representation of the inverse datum is $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda^{-1}$.
* `Langlands.LocalGL2.typeRepContragredient`: `Langlands.LocalGL2.TypeRepContragredient K` holds.

## Proof

The map $\Psi : \lambda \mapsto f_\lambda$, $f_\lambda(x) = \lambda(\pi(x^{-1}) f_0)$, is linear and commutes with $G$. The relation $\pi(j) f_0 = \Lambda(j) f_0$ gives $f_\lambda(j x) = \Lambda(j)^{-1} f_\lambda(x)$. If $\lambda$ is fixed by an open subgroup $U$, then $f_\lambda$ is invariant on the right under $U$. For the support, let $K' \subseteq U$ be compact and open. If $f_\lambda(x) \neq 0$, then $\Lambda$ is trivial on $J \cap x K' x^{-1}$, and the admissibility of $\pi$ puts $x$ in one of finitely many double cosets $J t K'$. Each double coset is a finite union of cosets $J s$, because $K' \cap t^{-1} J t$ is open in the compact group $K'$. So $f_\lambda$ lies in $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$. The map $\Psi$ is injective, because the translates of $f_0$ span $\pi$. Its image is a nonzero stable subspace, and $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$ is irreducible by `Langlands.isIrreducible_cInd`, since $\Lambda^{-1}$ has the same intertwining as $\Lambda$. So $\Psi$ is bijective.

For a datum $D$ for $(L/K, \xi)$, the data $\xi_0^{-1}$, $-\alpha$, $\Lambda_0^{-1}$, $\chi^{-1}$ form a datum for $\xi^{-1}$ with the same $\psi$ and basis. The level of $\xi_0^{-1}$ is the level of $\xi_0$, so the group $J_\alpha$ does not change, and the character of the new datum is $\Lambda^{-1}$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§11, 15 and 19.
-/

namespace Langlands.LocalGL2

universe w

open SmoothRep

section Contragredient

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let $f : \pi \to \pi'$ be a linear map that commutes with $G$. If $\lambda$ is a smooth linear form on $\pi'$, then $\lambda \circ f$ is a smooth linear form on $\pi$. -/
theorem comp_mem_smoothVectors {π π' : SmoothRep G} (f : π.V →ₗ[ℂ] π'.V)
    (hf : ∀ g v, f (π.ρ g v) = π'.ρ g (f v)) {l : Module.Dual ℂ π'.V}
    (hl : l ∈ smoothVectors π'.ρ.dual) : l ∘ₗ f ∈ smoothVectors π.ρ.dual := by
  change IsOpen (vecStabilizer π.ρ.dual (l ∘ₗ f) : Set G)
  refine Subgroup.isOpen_mono (H₁ := vecStabilizer π'.ρ.dual l) (fun g hg => ?_) hl
  rw [mem_vecStabilizer] at hg ⊢
  refine LinearMap.ext fun v => ?_
  have h := LinearMap.congr_fun hg (f v)
  change l (f (π.ρ g⁻¹ v)) = l (f v)
  rw [hf]
  exact h

/-- **Isomorphic representations have isomorphic contragredients.** If $\pi \cong \pi'$, then $\pi^\vee \cong \pi'^\vee$, by $\lambda \mapsto \lambda \circ e^{-1}$. -/
theorem iso_contragredient_of_iso {π π' : SmoothRep G} (h : π.Iso π') :
    π.contragredient.Iso π'.contragredient := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e.symm (π'.ρ g v) = π.ρ g (e.symm v) := fun g v =>
    e.injective (by rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  let E : π.contragredient.V ≃ₗ[ℂ] π'.contragredient.V :=
    { toFun := fun l => ⟨(l.1 : Module.Dual ℂ π.V) ∘ₗ (e.symm : π'.V →ₗ[ℂ] π.V),
        comp_mem_smoothVectors (e.symm : π'.V →ₗ[ℂ] π.V) he' l.2⟩
      invFun := fun l => ⟨(l.1 : Module.Dual ℂ π'.V) ∘ₗ (e : π.V →ₗ[ℂ] π'.V),
        comp_mem_smoothVectors (e : π.V →ₗ[ℂ] π'.V) he l.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
        change (l.1 : Module.Dual ℂ π.V) (e.symm (e v)) = _
        rw [LinearEquiv.symm_apply_apply])
      right_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
        change (l.1 : Module.Dual ℂ π'.V) (e (e.symm v)) = _
        rw [LinearEquiv.apply_symm_apply]) }
  refine ⟨E, fun g l => Subtype.ext (LinearMap.ext fun v => ?_)⟩
  change (l.1 : Module.Dual ℂ π.V) (π.ρ g⁻¹ (e.symm v)) = (l.1 : Module.Dual ℂ π.V) (e.symm (π'.ρ g⁻¹ v))
  rw [he']

variable {J : Subgroup G} {Λ : J →* ℂˣ}

variable (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))

/-- The function $x \mapsto \lambda(\pi(x^{-1}) f_0)$ on $G$, for a linear form $\lambda$ on $\pi = c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
noncomputable def contraFun (l : Module.Dual ℂ (cInd J Λ).V) (x : G) : ℂ :=
  l ((cInd J Λ).ρ x⁻¹ (cIndBasic J Λ hJ hΛ))

/-- The function `contraFun` satisfies $f_\lambda(j x) = \Lambda^{-1}(j) f_\lambda(x)$. -/
theorem contraFun_mul_left (l : Module.Dual ℂ (cInd J Λ).V) (j : J) (x : G) :
    contraFun hJ hΛ l (j * x) = (Λ⁻¹ j : ℂˣ) * contraFun hJ hΛ l x := by
  unfold contraFun
  rw [mul_inv_rev, map_mul, Module.End.mul_apply, ← InvMemClass.coe_inv, ρ_cIndBasic_of_mem,
    map_smul, map_smul, smul_eq_mul, map_inv, MonoidHom.inv_apply]

/-- If $\lambda$ is fixed by $u$ for the dual action, then $f_\lambda(x u) = f_\lambda(x)$. -/
theorem contraFun_mul_right {l : Module.Dual ℂ (cInd J Λ).V} {u : G}
    (hu : u ∈ vecStabilizer (cInd J Λ).ρ.dual l) (x : G) :
    contraFun hJ hΛ l (x * u) = contraFun hJ hΛ l x := by
  unfold contraFun
  rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  exact apply_ρ_of_inv_mem_vecStabilizer (by rwa [inv_inv]) _

/-- **The support of `contraFun` is finite modulo $J$.** Assume that each open subgroup of $G$ contains a compact open subgroup and that $\pi = c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible. For a smooth linear form $\lambda$ on $\pi$, there is a finite set $S$ such that $f_\lambda(x) \neq 0$ gives $x s^{-1} \in J$ for some $s \in S$. -/
theorem exists_finset_contraFun
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ K' : Subgroup G, K' ≤ U ∧ IsOpen (K' : Set G) ∧ IsCompact (K' : Set G))
    (hadm : (cInd J Λ).IsAdmissible) (l : smoothVectors (cInd J Λ).ρ.dual) :
    ∃ S : Finset G, ∀ x, contraFun hJ hΛ (l.1 : Module.Dual ℂ (cInd J Λ).V) x ≠ 0 →
      ∃ s ∈ S, x * s⁻¹ ∈ J := by
  classical
  obtain ⟨K', hK'l, hK'o, hK'⟩ := hK _ l.2
  obtain ⟨T, hT⟩ := exists_finset_of_finiteDimensional hK' hK'o hJ (hadm K' hK'o)
  have : CompactSpace K' := isCompact_iff_compactSpace.1 hK'
  let L : G → Subgroup K' := fun t => (J.comap (MulAut.conj t).toMonoidHom).subgroupOf K'
  have hfin : ∀ t, Finite (K' ⧸ L t) := fun t => Subgroup.quotient_finite_of_isOpen (L t)
    ((isOpen_comap_conj hJ t).preimage continuous_subtype_val)
  let S₀ : Set G := ⋃ t ∈ T, Set.range fun q : K' ⧸ L t => t * ((q.out : K') : G)⁻¹
  have hS₀ : S₀.Finite := Set.Finite.biUnion T.finite_toSet fun t _ => by
    have := hfin t
    exact Set.finite_range _
  refine ⟨hS₀.toFinset, fun x hx => ?_⟩
  have h1 := trivialOnConj_of_ne_zero hJ hΛ hK'l hx
  rw [inv_inv] at h1
  obtain ⟨t, ht, j, hj, k, hk, rfl⟩ := hT x h1
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (L t) (⟨k, hk⟩ : K')⁻¹
  refine ⟨t * (((QuotientGroup.mk ((⟨k, hk⟩ : K')⁻¹) : K' ⧸ L t).out : K') : G)⁻¹,
    hS₀.mem_toFinset.2 (Set.mem_biUnion (Finset.mem_coe.2 ht) ⟨_, rfl⟩), ?_⟩
  have hm' : t * ((m : K') : G) * t⁻¹ ∈ J := by
    have := m.2
    rwa [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at this
  rw [hm]
  convert J.mul_mem hj hm' using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group

/-- The vector $f_\lambda$ of $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$ of a smooth linear form $\lambda$ on $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
noncomputable def contraVec
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ K' : Subgroup G, K' ≤ U ∧ IsOpen (K' : Set G) ∧ IsCompact (K' : Set G))
    (hadm : (cInd J Λ).IsAdmissible) (l : (cInd J Λ).contragredient.V) : (cInd J Λ⁻¹).V :=
  (⟨contraFun hJ hΛ (l.1 : Module.Dual ℂ (cInd J Λ).V),
    fun j x => contraFun_mul_left hJ hΛ _ j x,
    ⟨vecStabilizer (cInd J Λ).ρ.dual (l.1 : Module.Dual ℂ (cInd J Λ).V), l.2,
      fun x _ hu => contraFun_mul_right hJ hΛ hu x⟩,
    exists_finset_contraFun hJ hΛ hK hadm l⟩ : cIndSpace J Λ⁻¹)

/-- The map $\Psi : \lambda \mapsto f_\lambda$ from $(c\text{-}\mathrm{Ind}_J^G \Lambda)^\vee$ to $c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$. -/
noncomputable def contraMap
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ K' : Subgroup G, K' ≤ U ∧ IsOpen (K' : Set G) ∧ IsCompact (K' : Set G))
    (hadm : (cInd J Λ).IsAdmissible) : (cInd J Λ).contragredient.V →ₗ[ℂ] (cInd J Λ⁻¹).V where
  toFun := contraVec hJ hΛ hK hadm
  map_add' _ _ := cInd.ext fun _ => rfl
  map_smul' _ _ := cInd.ext fun _ => rfl

include hJ hΛ in
/-- **The contragredient of a compact induction** (Bushnell and Henniart, 11.4 and 19.4). Let $J$ be an open subgroup of $G$ that is compact modulo a central subgroup $Z$, and $\Lambda$ a character of $J$ with open kernel whose intertwining is $J$. Assume that each open subgroup of $G$ contains a compact open subgroup and that $c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible. Then $(c\text{-}\mathrm{Ind}_J^G \Lambda)^\vee \cong c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$. -/
theorem contragredient_cInd_iso {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hc : IsCompactModCenter J Z) (hI : ∀ g, Intertwines J Λ g → g ∈ J)
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ K' : Subgroup G, K' ≤ U ∧ IsOpen (K' : Set G) ∧ IsCompact (K' : Set G))
    (hadm : (cInd J Λ).IsAdmissible) : (cInd J Λ).contragredient.Iso (cInd J Λ⁻¹) := by
  set Ψ := contraMap hJ hΛ hK hadm with hΨ
  have hequiv : ∀ g l, Ψ ((cInd J Λ).contragredient.ρ g l) = (cInd J Λ⁻¹).ρ g (Ψ l) := by
    intro g l
    refine cInd.ext fun x => ?_
    change (l.1 : Module.Dual ℂ (cInd J Λ).V) ((cInd J Λ).ρ g⁻¹ ((cInd J Λ).ρ x⁻¹
      (cIndBasic J Λ hJ hΛ))) = (l.1 : Module.Dual ℂ (cInd J Λ).V) ((cInd J Λ).ρ (x * g)⁻¹
      (cIndBasic J Λ hJ hΛ))
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro l hl
    refine Subtype.ext (LinearMap.ext_on_range (span_translate_cIndBasic J Λ hJ hΛ) fun g => ?_)
    have h := congrArg (fun f => cInd.toFun f g⁻¹) hl
    change (l.1 : Module.Dual ℂ (cInd J Λ).V) ((cInd J Λ).ρ g⁻¹⁻¹ (cIndBasic J Λ hJ hΛ)) = 0 at h
    rw [inv_inv] at h
    exact h
  have hΛ' : IsOpen ((Λ⁻¹).ker : Set J) := by rw [ker_inv_char]; exact hΛ
  have hI' : ∀ g, Intertwines J Λ⁻¹ g → g ∈ J := by
    intro g hg
    refine hI g fun x h => ?_
    have := hg x h
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at this
    exact inv_injective this
  have hirr := isIrreducible_cInd J Λ⁻¹ hJ hΛ' hZc hc hI'
  have hstab : IsStableSubspace (cInd J Λ⁻¹).ρ (LinearMap.range Ψ) := by
    rintro g _ ⟨l, rfl⟩
    exact ⟨_, hequiv g l⟩
  have hsurj : Function.Surjective Ψ := by
    rcases hirr.2 _ hstab with h | h
    · exfalso
      have h1 : Ψ (cIndEvalOne J Λ hJ hΛ) ∈ LinearMap.range Ψ := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (fun f => cInd.toFun f 1) h1
      change cInd.toFun ((cInd J Λ).ρ (1 : G)⁻¹ (cIndBasic J Λ hJ hΛ)) 1 = 0 at h2
      rw [inv_one, map_one, Module.End.one_apply, cInd.toFun_cIndBasic,
        cIndBasicFun_of_mem J Λ J.one_mem] at h2
      exact Units.ne_zero _ h2
    · exact LinearMap.range_eq_top.1 h
  exact ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, hequiv⟩

end Contragredient

section GL2

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The contragredient of a compact induction for $GL_2(K)$** (Bushnell and Henniart, 11.4 and 19.4). Let $J$ be an open subgroup of $GL_2(K)$ that is compact modulo the centre, and $\Lambda$ a character of $J$ with open kernel whose intertwining is $J$. Then $(c\text{-}\mathrm{Ind}_J^G \Lambda)^\vee \cong c\text{-}\mathrm{Ind}_J^G \Lambda^{-1}$. -/
theorem contragredient_cInd_iso_GL2 {J : Subgroup (GL (Fin 2) K)} {Λ : J →* ℂˣ}
    (hJ : IsOpen (J : Set (GL (Fin 2) K))) (hΛ : IsOpen (Λ.ker : Set J))
    (hc : IsCompactModCenter J (scalarGL K 2).range) (hI : ∀ g, Intertwines J Λ g → g ∈ J) :
    (cInd J Λ).contragredient.Iso (cInd J Λ⁻¹) :=
  contragredient_cInd_iso hJ hΛ range_scalarGL_le_center hc hI exists_isCompact_isOpen_le
    (isAdmissible_cInd_of_intertwining hJ hΛ hc hI)

end GL2

section Transport

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For equal subgroups $J' = J$, the compact induction of $\Lambda$ restricted to $J'$ is isomorphic to $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
theorem cInd_comp_inclusion_iso {J J' : Subgroup G} (h : J' = J) (hle : J' ≤ J) (Λ : J →* ℂˣ) :
    (cInd J' (Λ.comp (Subgroup.inclusion hle))).Iso (cInd J Λ) := by
  subst h
  have e : Λ.comp (Subgroup.inclusion hle) = Λ := MonoidHom.ext fun _ => rfl
  rw [e]
  exact Iso.refl _

end Transport

universe u v

open LocalGL1 ValuativeRel

section Inverse

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E]

/-- The level of $\xi^{-1}$ is the level of $\xi$, because the two characters have the same kernel. -/
theorem level_inv_char (ξ : Eˣ →* ℂˣ) : level ξ⁻¹ = level ξ := by
  have h : (ξ⁻¹).ker = ξ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold level
  rw [h]

/-- **The inverse of a minimal character is minimal.** If $(E/F, \xi)$ is minimal, then $(E/F, \xi^{-1})$ is minimal. -/
theorem IsMinimal.inv {ξ : Eˣ →* ℂˣ} (h : IsMinimal F E ξ) : IsMinimal F E ξ⁻¹ where
  admissible := h.admissible.inv
  not_factor_level := by
    rintro ⟨φ, hφ⟩
    refine h.not_factor_level ⟨φ⁻¹, fun u hu => ?_⟩
    have := hφ u (by rwa [level_inv_char])
    rw [MonoidHom.inv_apply] at this
    rw [MonoidHom.inv_apply, ← this, inv_inv]

variable [Valuation.HasExtension (valuation F) (valuation E)]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- If $\alpha$ is a minimal element of level $n$, then $-\alpha$ is a minimal element of level $n$. -/
theorem IsMinimalElt.neg {n : ℕ} {α : E} (h : IsMinimalElt F n α) : IsMinimalElt F n (-α) := by
  refine ⟨neg_mem_ordBall h.1, fun a ha => h.2 (-a) ?_⟩
  have := neg_mem_ordBall ha
  convert this using 1
  rw [map_neg]
  ring

variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}
variable (hv : IsAdapted A v) (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1))

/-- **The inverse of a cuspidal type.** If $\Lambda$ is a cuspidal type for $(\alpha, \xi)$, then $\Lambda^{-1}$ is a cuspidal type for $(-\alpha, \xi^{-1})$, because $\psi_{-\alpha} = \psi_\alpha^{-1}$. -/
theorem inv_mem_cuspTypes {n : ℕ} {α : E} (hα : Algebra.leftMulMatrix v α ∈ radPow F A (-n))
    (hα' : Algebra.leftMulMatrix v (-α) ∈ radPow F A (-n)) {ξ : Eˣ →* ℂˣ}
    {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ} (h : Λ ∈ cuspTypes hv ψ hψ n α hα ξ) :
    Λ⁻¹ ∈ cuspTypes hv ψ hψ n (-α) hα' ξ⁻¹ := by
  have h' : IsTypeChar hv ψ hψ n α hα ξ ((n + 1) / 2) (by omega) Λ := h
  refine ⟨fun g => ?_, fun y => ?_⟩
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h'.1 g, psiAlpha_apply, psiAlpha_apply,
      map_neg, neg_mul, Matrix.trace_neg, AddChar.map_neg_eq_inv]
  · rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h'.2 y]

/-- A cuspidal type for the level $n$ is a cuspidal type for each level $n' = n$, after the restriction to the equal group. -/
theorem comp_inclusion_mem_cuspTypes {n n' : ℕ} (hn : n' = n) {α : E}
    (hα : Algebra.leftMulMatrix v α ∈ radPow F A (-n))
    (hα' : Algebra.leftMulMatrix v α ∈ radPow F A (-n')) {ξ : Eˣ →* ℂˣ}
    {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ} (h : Λ ∈ cuspTypes hv ψ hψ n α hα ξ)
    (hle : jGroup v hv ((n' + 1) / 2) ≤ jGroup v hv ((n + 1) / 2)) :
    Λ.comp (Subgroup.inclusion hle) ∈ cuspTypes hv ψ hψ n' α hα' ξ := by
  subst hn
  exact h

end Inverse

section Datum

open Langlands.WeilGroup.FiniteExt

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  {ξ : Lˣ →* ℂˣ}

namespace TameDatum

/-- The group $J_\alpha$ for the level of $\xi_0^{-1}$ lies in the group for the level of $\xi_0$. The two groups are equal. -/
theorem jGroup_inv_le (D : TameDatum K L ξ) :
    jGroup D.v D.hv ((level D.ξ₀⁻¹ + 1) / 2) ≤ D.J := by
  rw [level_inv_char]

/-- **The inverse datum** (BH 19.4). From a datum for $(L/K, \xi)$, the characters $\xi_0^{-1}$, $\Lambda_0^{-1}$, $\chi^{-1}$ and the element $-\alpha$, with the same $\psi$ and basis, form a datum for $(L/K, \xi^{-1})$. -/
noncomputable def inv (D : TameDatum K L ξ) : TameDatum K L ξ⁻¹ where
  ψ := D.ψ
  hψ := D.hψ
  A := D.A
  v := D.v
  hv := D.hv
  ξ₀ := D.ξ₀⁻¹
  α := -D.α
  hα := by
    rw [level_inv_char, map_neg]
    exact neg_mem D.hα
  Λ₀ := (D.Λ₀⁻¹).comp (Subgroup.inclusion D.jGroup_inv_le)
  χ := D.χ⁻¹
  Λ := (D.Λ⁻¹).comp (Subgroup.inclusion D.jGroup_inv_le)
  minimal := D.minimal.inv
  odd := by
    rw [level_inv_char]
    exact D.odd
  minElt := by
    rw [level_inv_char]
    exact D.minElt.neg
  mem := comp_inclusion_mem_cuspTypes D.hv D.ψ D.hψ (level_inv_char D.ξ₀) _ _
    (inv_mem_cuspTypes D.hv D.ψ D.hψ D.hα (by rw [map_neg]; exact neg_mem D.hα) D.mem) _
  smooth := LocalGL1.isSmoothChar_inv D.χ D.smooth
  eq := by
    refine MonoidHom.ext fun x => ?_
    have h := congrArg (fun f : Lˣ →* ℂˣ => f x) D.eq
    simp only [twistChar_apply] at h
    simp only [MonoidHom.inv_apply, twistChar_apply, h, mul_inv]
  mul x := by
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, D.mul, detChar, mul_inv]
    rfl

/-- **The representation of the inverse datum** is $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda^{-1}$. -/
theorem inv_rep_iso (D : TameDatum K L ξ) : D.inv.rep.Iso (cInd D.J D.Λ⁻¹) :=
  cInd_comp_inclusion_iso (by rw [level_inv_char]) D.jGroup_inv_le D.Λ⁻¹

/-- **The contragredient of the representation of a datum** is the representation of the inverse datum. -/
theorem contragredient_rep_iso (D : TameDatum K L ξ) : D.rep.contragredient.Iso D.inv.rep :=
  (contragredient_cInd_iso_GL2 (isOpen_jGroup D.hv _) D.isOpen_ker
    (isCompactModCenter_jGroup D.hv _) D.mem_of_intertwines).trans D.inv_rep_iso.symm

end TameDatum

variable (K) in
/-- **The contragredient of a type representation** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 19.4). The statement `Langlands.LocalGL2.TypeRepContragredient K` holds, with the inverse datum. The hypothesis $p \ne 2$ is not used. -/
theorem typeRepContragredient : TypeRepContragredient K :=
  fun _ _ D _ _ hπ hπ' => ⟨D.inv, hπ'.trans ((iso_contragredient_of_iso hπ).trans
    D.contragredient_rep_iso)⟩

end Datum

end Langlands.LocalGL2
