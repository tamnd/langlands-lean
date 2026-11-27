/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.TameGalois
import Langlands.Local.GL1LFactor
import Langlands.Reciprocity.Exists

/-!
# A reduction of the local Langlands correspondence for GL(2), p odd

Let $K$ be a nonarchimedean local field with residue characteristic $p \ne 2$. This file defines the statement `Langlands.LocalLanglandsGL2Odd` of the local Langlands correspondence for $GL_2(K)$, and it proves that the statement follows from six named published theorems. Each theorem is a closed hypothesis of type `Prop` with a citation.

* `Langlands.LocalGL2.ArtinCompat`: compatibility of the local Artin maps of quadratic extensions with conjugation, norm and transfer (Serre, Neukirch, Tate).
* `Langlands.LocalGL2.TameParametrizationGL2`: the parametrization of the supercuspidal representations by admissible pairs, with central character, twists and contragredients (Bushnell and Henniart, 19 and 20.2).
* `Langlands.LocalGL2.GaloisTameParametrization`: each irreducible representation of $W_K$ of dimension 2 is induced from an admissible pair, and the induced representation determines the field (Bushnell and Henniart, 34.1).
* `Langlands.LocalGL2.Rectifier`: the existence of the rectifier $\Delta_\xi$ (Bushnell and Henniart, 34.4).
* `Langlands.LocalGL2.SupercuspidalLFactor`: $L(s, \pi) = 1$ for supercuspidal $\pi$ (Godement and Jacquet; Bushnell and Henniart, 24.2).
* `Langlands.LocalGL2.NonSupercuspidalLLC`: the correspondence between the classes that are not supercuspidal and the parameters that are not irreducible (Jacquet and Langlands; Bushnell and Henniart, chapter 2 and 33).

The reduction does these steps. It glues the two parts of the correspondence. On the supercuspidal part it uses $\pi_{\Delta_\xi \xi} \mapsto \sigma(L, \xi)$ of `Langlands.LocalGL2.tameParam`. It proves the four conditions of `Langlands.IsLanglandsMap` there from the proved properties of `Langlands.LocalGL2.tameParam`: irreducibility, injectivity on classes, twists, determinant, and a new result for duals. It also proves that the L-factor of an irreducible Weil-Deligne representation of dimension 2 is 1. For $GL_1$ it uses `Langlands.LocalGL1.localLanglandsGL_one`.

## Main definitions

* `Langlands.LocalLanglandsGL2Odd`: the local Langlands correspondence for $GL_m(K)$, $m \le 2$, for all $K$ with $p \ne 2$.
* `Langlands.LocalGL2.TamePair`: an admissible pair $(L/K, \xi)$ with $L$ a quadratic separable extension inside $\bar K$.
* `Langlands.LocalGL2.TamePair.Iso`, `Langlands.LocalGL2.TamePair.twist`, `Langlands.LocalGL2.TamePair.inv`, `Langlands.LocalGL2.TamePair.rectify`: isomorphism, twist, inverse and rectification of pairs.
* `Langlands.LocalGL2.TamePair.param`: the parameter $\sigma(L, \xi)$ for a chosen local Artin map of $L$.
* `Langlands.LocalGL2.GL2OddInputs`: the six published theorems for one field.

## Main results

* `Langlands.LocalGL2.tameParam_isDual`: $\sigma(L, \xi^{-1})$ is the dual of $\sigma(L, \xi)$.
* `Langlands.LocalGL2.isIrreducible_of_iso`: irreducibility is invariant under isomorphism.
* `Langlands.LocalGL2.lFactor_eq_one_of_isIrreducible`: an irreducible Weil-Deligne representation of dimension 2 has L-factor 1.
* `Langlands.LocalGL2.mk_param_eq_iff`: $\sigma(P) \cong \sigma(Q)$ exactly when $P$ and $Q$ are isomorphic.
* `Langlands.LocalGL2.exists_isLanglandsMap_two`: the inputs give a bijection for $GL_2(K)$ with the conditions of `Langlands.IsLanglandsMap`.
* `Langlands.localLanglandsGL2_odd_of_inputs`: the inputs for all $K$ give `Langlands.LocalLanglandsGL2Odd`.

## Implementation notes

`Langlands.LocalLanglandsGL` has no ε-factors and no uniqueness clause. Thus the reduction needs no converse theorem, and the rectifier is only required to restrict to $\kappa_{L/K}$ on $K^\times$. The hypothesis `Langlands.LocalGL2.NonSupercuspidalLLC` is coarse: it states the whole correspondence off the supercuspidal classes, and this file does not reduce it to the principal series and the Steinberg representation.

## Still open

* A proof of `Langlands.LocalGL2.NonSupercuspidalLLC` from the classification of the principal series and from the L-factors of Godement and Jacquet.
* A proof of `Langlands.LocalGL2.TameParametrizationGL2` from the cuspidal types of this project.
* The case $p = 2$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), chapters 2 and 4 to 8.
* R. Godement and H. Jacquet, Zeta functions of simple algebras, Lecture Notes in Math. 260.
* H. Jacquet and R. P. Langlands, Automorphic forms on GL(2), Lecture Notes in Math. 114.
* J.-P. Serre, Local fields, chapter XI, section 3.
* J. Tate, Number theoretic background, section 1.
-/

namespace Langlands

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix

open scoped commutatorElement

universe u

/-- **The local Langlands correspondence for $GL_2$, $p$ odd** (Kutzko; Bushnell and Henniart, The local Langlands conjecture for GL(2), Chapter 8). This is `Langlands.LocalLanglandsGL` for $n = 2$, for the nonarchimedean local fields $K$ whose residue characteristic is not $2$. -/
def LocalLanglandsGL2Odd : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art → (2 : 𝓀[K]) ≠ 0 →
      ∃ rec : ∀ m ≤ 2, IrrSmooth (GL (Fin m) K) ≃ WDIso K m, IsLanglandsFamily K art 2 rec

namespace LocalGL2

section Inverse

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E]

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
/-- If $\xi$ is a smooth character, then $\xi^{-1}$ is a smooth character. -/
theorem isSmoothChar_inv {ξ : Eˣ →* ℂˣ} (h : IsSmoothChar E ξ) : IsSmoothChar E ξ⁻¹ := by
  have : (ξ⁻¹).ker = ξ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rw [this]
  exact h

/-- **The inverse of an admissible character is admissible** (BH 18.2). If $(E/F, \xi)$ is admissible, then $(E/F, \xi^{-1})$ is admissible. -/
theorem IsAdmissible.inv {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ) : IsAdmissible F E ξ⁻¹ where
  smooth := isSmoothChar_inv h.smooth
  not_factor := by
    rintro ⟨χ, hχ⟩
    refine h.not_factor ⟨χ⁻¹, MonoidHom.ext fun x => ?_⟩
    have := DFunLike.congr_fun hχ x
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply] at this
    rw [MonoidHom.comp_apply, MonoidHom.inv_apply, ← this, inv_inv]
  unramified_of_factor := by
    rintro ⟨φ, hφ⟩
    refine h.unramified_of_factor ⟨φ⁻¹, fun u hu => ?_⟩
    have := hφ u hu
    rw [MonoidHom.inv_apply] at this
    rw [MonoidHom.inv_apply, ← this, inv_inv]

end Inverse


section Pairs

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- An admissible pair $(L/K, \xi)$ with $L$ a quadratic separable extension of $K$ inside $\bar K$ (BH 18.2). -/
structure TamePair where
  /-- The quadratic extension $L$ inside $\bar K$. -/
  L : IntermediateField K (AlgebraicClosure K)
  /-- The extension $L/K$ is quadratic. -/
  [quad : Algebra.IsQuadraticExtension K L]
  /-- The extension $L/K$ is separable. -/
  [sep : Algebra.IsSeparable K L]
  /-- The character $\xi$ of $L^\times$. -/
  ξ : Lˣ →* ℂˣ
  /-- The character $\xi$ is admissible. -/
  adm : IsAdmissible K L ξ

attribute [instance] TamePair.quad TamePair.sep

variable {K}

namespace TamePair

/-- Two pairs are $K$-isomorphic when $\xi = \xi' \circ j$ for a $K$-isomorphism $j : L \to L'$. -/
def Iso (P Q : TamePair K) : Prop :=
  ∃ j : P.L ≃ₐ[K] Q.L, P.ξ = Q.ξ.comp (unitsMap j)

/-- The setoid of pairs up to $K$-isomorphism. -/
instance setoid : Setoid (TamePair K) where
  r := Iso
  iseqv := by
    refine ⟨fun P => ⟨AlgEquiv.refl, MonoidHom.ext fun x => ?_⟩, ?_, ?_⟩
    · rw [MonoidHom.comp_apply]
      exact congrArg P.ξ (Units.ext rfl)
    · rintro P Q ⟨j, hj⟩
      refine ⟨j.symm, MonoidHom.ext fun y => ?_⟩
      rw [MonoidHom.comp_apply, hj, MonoidHom.comp_apply]
      exact congrArg Q.ξ (Units.ext (by simp))
    · rintro P Q R ⟨j, hj⟩ ⟨k, hk⟩
      refine ⟨j.trans k, MonoidHom.ext fun x => ?_⟩
      rw [hj, MonoidHom.comp_apply, hk, MonoidHom.comp_apply, MonoidHom.comp_apply]
      rfl

/-- The twist $(L/K, \xi \otimes \chi_L)$ of a pair by a smooth character $\chi$ of $K^\times$. -/
noncomputable def twist (P : TamePair K) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) : TamePair K where
  L := P.L
  ξ := twistChar K P.L P.ξ χ
  adm := P.adm.twist hχ

/-- The inverse pair $(L/K, \xi^{-1})$. -/
noncomputable def inv (P : TamePair K) : TamePair K where
  L := P.L
  ξ := P.ξ⁻¹
  adm := P.adm.inv

/-- The pair $(L/K, \Delta \xi)$ for a family $\Delta$ of characters with $\Delta \xi$ admissible. -/
noncomputable def rectify (Δ : ∀ P : TamePair K, P.Lˣ →* ℂˣ) (hΔ : ∀ P : TamePair K, IsAdmissible K P.L (Δ P * P.ξ))
    (P : TamePair K) : TamePair K where
  L := P.L
  ξ := Δ P * P.ξ
  adm := hΔ P

end TamePair

/-- A fixed local Artin map $\mathrm{art}_L$ of a finite extension $L$ of $K$ inside $\bar K$, from `Langlands.exists_isLocalArtinMap`. -/
noncomputable def artOf (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    Lˣ ≃ₜ* WeilGroup.Ab L :=
  (exists_isLocalArtinMap L).choose

/-- The map `Langlands.LocalGL2.artOf` is a local Artin map. -/
theorem isLocalArtinMap_artOf (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    IsLocalArtinMap L (artOf L) :=
  (exists_isLocalArtinMap L).choose_spec

/-- The Galois parameter $\sigma(L, \xi)$ of a pair, for the fixed Artin map `Langlands.LocalGL2.artOf`. -/
noncomputable def TamePair.param (P : TamePair K) : WeilDeligneRep K 2 :=
  tameParam (artOf P.L) P.ξ P.adm.smooth

end Pairs

section Galois

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The extension by zero of $\varphi^{-1}$ at $x$ is the extension by zero of $\varphi$ at $x^{-1}$. -/
theorem extChar_inv {W : Type*} [Group W] {H : Subgroup W} (φ : H →* ℂˣ) (x : W) :
    extChar φ⁻¹ x = extChar φ x⁻¹ := by
  by_cases hx : x ∈ H
  · rw [extChar_of_mem _ hx, extChar_of_mem _ (H.inv_mem hx)]
    have : (⟨x⁻¹, H.inv_mem hx⟩ : H) = (⟨x, hx⟩ : H)⁻¹ := rfl
    rw [this, map_inv, MonoidHom.inv_apply]
  · rw [extChar_of_not_mem _ hx, extChar_of_not_mem _ (fun h => hx (by simpa using H.inv_mem h))]

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  [Algebra.IsSeparable K L]

omit [Algebra.IsSeparable K L] in
/-- The character $(\xi^{-1})_W$ is $(\xi_W)^{-1}$. -/
theorem charW_inv (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) :
    charW (F := K) art ξ⁻¹ = (charW art ξ)⁻¹ :=
  rfl

/-- **The dual of the Galois parameter** (BH 34.1). The class of $\sigma(L, \xi^{-1})$ is the dual of the class of $\sigma(L, \xi)$, in the sense of `Langlands.WDIso.IsDual`. -/
theorem tameParam_isDual (art : Lˣ ≃ₜ* WeilGroup.Ab L) {ξ : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ)
    (hξ' : IsSmoothChar L ξ⁻¹) :
    WDIso.IsDual (WDIso.mk (tameParam art ξ⁻¹ hξ')) (WDIso.mk (tameParam art ξ hξ)) := by
  refine ⟨tameParam art ξ hξ, tameParam art ξ⁻¹ hξ', rfl, rfl, fun w => ?_, by simp⟩
  rw [← map_inv, tameParam_r, tameParam_r, coe_ind, coe_ind]
  ext i j
  rw [transpose_apply, indMatrix_apply, indMatrix_apply, charW_inv, extChar_inv]
  congr 1

end Galois

section WeilDeligne

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Irreducibility is invariant under isomorphism.** If $\rho \cong \rho'$ and $\rho$ is irreducible, then $\rho'$ is irreducible. -/
theorem isIrreducible_of_iso {m : ℕ} {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ')
    (hρ : ρ.IsIrreducible) : ρ'.IsIrreducible := by
  obtain ⟨g, hr, hN⟩ := h
  refine ⟨hρ.1, fun W hW hWN => ?_⟩
  have hGGi : (g : Matrix (Fin m) (Fin m) ℂ) * ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Units.mul_inv g
  have hGiG : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (g : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Units.inv_mul g
  have key : ∀ A A' : Matrix (Fin m) (Fin m) ℂ,
      A' = (g : Matrix (Fin m) (Fin m) ℂ) * A * ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) →
      W ≤ W.comap (toLin' A') →
        W.comap (toLin' (g : Matrix (Fin m) (Fin m) ℂ)) ≤
          (W.comap (toLin' (g : Matrix (Fin m) (Fin m) ℂ))).comap (toLin' A) := by
    intro A A' hA hW' v hv
    simp only [Submodule.mem_comap, toLin'_apply] at hv ⊢
    have h1 : (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ (A *ᵥ v) = A' *ᵥ ((g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v) := by
      rw [hA, mulVec_mulVec, mulVec_mulVec, mul_assoc (_ * A), hGiG, mul_one]
    rw [h1]
    have h2 := hW' hv
    simpa [toLin'_apply] using h2
  rcases hρ.2 _ (fun w => key _ _ (by rw [hr w, Units.val_mul, Units.val_mul]) (hW w))
      (key _ _ hN hWN) with h0 | h0
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) *ᵥ u ∈
        W.comap (toLin' (g : Matrix (Fin m) (Fin m) ℂ)) := by
      simpa only [Submodule.mem_comap, toLin'_apply, mulVec_mulVec, hGGi, one_mulVec] using hu
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg ((g : Matrix (Fin m) (Fin m) ℂ) *ᵥ ·) h1
    simp only [mulVec_mulVec, hGGi, one_mulVec, mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) *ᵥ u ∈
        W.comap (toLin' (g : Matrix (Fin m) (Fin m) ℂ)) := by
      rw [h0]
      exact Submodule.mem_top
    simpa only [Submodule.mem_comap, toLin'_apply, mulVec_mulVec, hGGi, one_mulVec] using h1

/-- **The L-factor of an irreducible representation of dimension 2 is 1** (Tate, Number theoretic background, (4.1.6)). The space $(V^{I_K})_{N = 0}$ is stable, so it is $0$ or $V$. If it is $V$, then $N = 0$ and $r$ factors through the abelian group $W_K / I_K$, so each $r(w)$ is a scalar and each line is stable. -/
theorem lFactor_eq_one_of_isIrreducible {ρ : WeilDeligneRep K 2} (h : ρ.IsIrreducible) :
    ρ.lFactor = fun _ => 1 := by
  have hst : ∀ w, ρ.lSpace ≤ ρ.lSpace.comap (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) :=
    fun w v hv => ρ.lSpace_stable w v hv
  have hN : ρ.lSpace ≤ ρ.lSpace.comap (toLin' ρ.N) := fun v hv => by
    rw [Submodule.mem_comap, toLin'_apply, hv.1]
    exact Submodule.zero_mem _
  rcases h.2 _ hst hN with h0 | h0
  · have : Subsingleton ρ.lSpace := by
      rw [h0]
      infer_instance
    funext s
    rw [WeilDeligneRep.lFactor, LinearMap.det_eq_one_of_subsingleton, inv_one]
  exfalso
  have hall : ∀ v, v ∈ ρ.lSpace := fun v => h0 ▸ Submodule.mem_top
  have hN0 : ρ.N = 0 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [map_zero, LinearMap.zero_apply, toLin'_apply]
    exact (hall v).1)
  have hI : ∀ i ∈ WeilGroup.inertia K, ρ.r i = 1 := fun i hi => Units.ext
    (Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [toLin'_apply, toLin'_apply, Units.val_one, one_mulVec]
      exact (hall v).2 i hi))
  have hc : ∀ a b : WeilGroup K, ρ.r a * ρ.r b = ρ.r b * ρ.r a := fun a b => by
    have hmem : ⁅a, b⁆ ∈ WeilGroup.inertia K :=
      commutator_le_inertia K (Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b))
    have := hI _ hmem
    rw [map_commutatorElement] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hsc : ∀ w, ∃ μ : ℂ, ∀ v, toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) v = μ • v := by
    intro w
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ))
    have hE : ∀ w', Module.End.eigenspace (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) μ ≤
        (Module.End.eigenspace (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) μ).comap
          (toLin' (ρ.r w' : Matrix (Fin 2) (Fin 2) ℂ)) := by
      intro w' v hv
      rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff, toLin'_apply]
      rw [toLin'_apply, mulVec_mulVec, ← Units.val_mul, hc, Units.val_mul, ← mulVec_mulVec, hv,
        mulVec_smul]
    have hEN : Module.End.eigenspace (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) μ ≤
        (Module.End.eigenspace (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) μ).comap
          (toLin' ρ.N) := by
      rw [hN0]
      intro v _
      rw [Submodule.mem_comap, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    rcases h.2 _ hE hEN with hb | ht
    · exact absurd hb (Module.End.hasEigenvalue_iff.1 hμ)
    · refine ⟨μ, fun v => ?_⟩
      have : v ∈ Module.End.eigenspace (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) μ :=
        ht ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 this
  have hW : ∀ w, Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} ≤
      (Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)}).comap
        (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) := by
    intro w v hv
    obtain ⟨μ, hμ⟩ := hsc w
    rw [Submodule.mem_comap, hμ]
    exact Submodule.smul_mem _ μ hv
  have hWN : Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} ≤
      (Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)}).comap (toLin' ρ.N) := by
    rw [hN0]
    intro v _
    rw [Submodule.mem_comap, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  rcases h.2 _ hW hWN with hb | ht
  · have h1 : (Pi.single 0 1 : Fin 2 → ℂ) ∈ Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} :=
      Submodule.subset_span rfl
    rw [hb, Submodule.mem_bot] at h1
    have := congrFun h1 0
    simp at this
  · have h1 : (Pi.single 1 1 : Fin 2 → ℂ) ∈ Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} :=
      ht ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    have := congrFun hc 1
    simp at this

end WeilDeligne

section Glue

/-- **Gluing two bijections.** Let $g : T \to \alpha$ and $f : T \to \beta$ be injective with images $S$ and $I$, and let $e$ be a bijection from the complement of $S$ to the complement of $I$. Then there is a bijection $\alpha \to \beta$ that sends $g(t)$ to $f(t)$ and is $e$ outside $S$. -/
theorem exists_equiv_glue {α β τ : Type*} (S : Set α) (I : Set β) (g : τ → α) (f : τ → β)
    (hg : Function.Injective g) (hf : Function.Injective f) (hgS : ∀ x, x ∈ S ↔ ∃ t, g t = x)
    (hfI : ∀ y, y ∈ I ↔ ∃ t, f t = y) (e : {x // x ∉ S} ≃ {y // y ∉ I}) :
    ∃ rec : α ≃ β, (∀ t, rec (g t) = f t) ∧ ∀ x (hx : x ∉ S), rec x = (e ⟨x, hx⟩).1 := by
  classical
  let e1 : τ ≃ {x // x ∈ S} := Equiv.ofBijective (fun t => ⟨g t, (hgS _).2 ⟨t, rfl⟩⟩)
    ⟨fun a b hab => hg (congrArg Subtype.val hab), fun x => by
      obtain ⟨t, ht⟩ := (hgS x.1).1 x.2
      exact ⟨t, Subtype.ext ht⟩⟩
  let e2 : τ ≃ {y // y ∈ I} := Equiv.ofBijective (fun t => ⟨f t, (hfI _).2 ⟨t, rfl⟩⟩)
    ⟨fun a b hab => hf (congrArg Subtype.val hab), fun y => by
      obtain ⟨t, ht⟩ := (hfI y.1).1 y.2
      exact ⟨t, Subtype.ext ht⟩⟩
  refine ⟨(Equiv.sumCompl (· ∈ S)).symm.trans
    ((Equiv.sumCongr (e1.symm.trans e2) e).trans (Equiv.sumCompl (· ∈ I))), fun t => ?_,
    fun x hx => ?_⟩
  · have h1 : e1.symm ⟨g t, (hgS _).2 ⟨t, rfl⟩⟩ = t := e1.symm_apply_eq.2 rfl
    rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos ((hgS _).2 ⟨t, rfl⟩), Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl, Equiv.trans_apply, h1]
    rfl
  · rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]

end Glue



section Inputs

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Local class field theory for quadratic extensions** (Serre, Local fields, Chapter XI, Section 3; Neukirch, Algebraic number theory, Chapter IV, Section 6, and Chapter V, Section 1; Tate, Number theoretic background, Section 1). For each quadratic separable extension $L$ of $K$ inside $\bar K$, the local Artin maps are compatible with conjugation, with the norm and with the transfer: `Langlands.LocalGL2.ArtinConjCompat`, `Langlands.LocalGL2.ArtinNormCompat` and `Langlands.LocalGL2.ArtinTransferCompat`. -/
def ArtinCompat : Prop :=
  ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L], ArtinConjCompat K L ∧ ArtinNormCompat K L ∧ ArtinTransferCompat K L

/-- The classes in $\mathrm{Irr}(GL_2(K))$ that contain a supercuspidal representation. -/
def scClasses : Set (IrrSmooth (GL (Fin 2) K)) :=
  {x | ∃ π : IrrRep (GL (Fin 2) K), IrrSmooth.mk π = x ∧ π.1.IsSupercuspidal (scalarGL K 2)}

/-- The classes in $\mathrm{WD}_2(W_K)$ that contain an irreducible representation. -/
def irrClasses : Set (WDIso K 2) :=
  {y | ∃ ρ : WeilDeligneRep K 2, WDIso.mk ρ = y ∧ ρ.IsIrreducible}

/-- **The tame parametrization theorem** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 19.1, 19.3, 19.4 and 20.2). Let $p \ne 2$. There is a map $(L/K, \xi) \mapsto \pi_\xi$ from the admissible pairs to $\mathrm{Irr}(GL_2(K))$ with these properties.

1. Each $\pi_\xi$ is supercuspidal, and each supercuspidal class is some $\pi_\xi$.
2. $\pi_\xi = \pi_{\xi'}$ exactly when the pairs are $K$-isomorphic.
3. The central character of $\pi_\xi$ is $\xi|_{K^\times}$.
4. Each twist of $\pi_\xi$ by $\chi \circ \det$ is $\pi_{\xi \otimes \chi_L}$.
5. Each contragredient of $\pi_\xi$ is $\pi_{\xi^{-1}}$.

The construction is $\pi_\xi = c\text{-}\mathrm{Ind}_{J}^{G} \Lambda_\xi$ for a cuspidal type $(J, \Lambda_\xi)$. -/
def TameParametrizationGL2 : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∃ pi : TamePair K → IrrSmooth (GL (Fin 2) K),
    (∀ P, pi P ∈ scClasses K) ∧ (∀ x ∈ scClasses K, ∃ P, pi P = x) ∧
    (∀ P Q, pi P = pi Q ↔ P.Iso Q) ∧
    (∀ (P : TamePair K) (π : IrrRep (GL (Fin 2) K)), IrrSmooth.mk π = pi P →
      π.1.HasCentralChar (P.ξ.comp (Units.map (algebraMap K P.L).toMonoidHom))) ∧
    (∀ (P : TamePair K) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) y,
      IrrSmooth.IsTwist y (pi P) (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ) →
        y = pi (P.twist χ hχ)) ∧
    ∀ (P : TamePair K) y, IrrSmooth.IsContragredient y (pi P) → y = pi P.inv

/-- **The irreducible representations of $W_K$ of dimension 2, $p$ odd** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 34.1 and 41.3; Weil, Exercices dyadiques). Let $p \ne 2$.

1. Each irreducible Weil-Deligne representation of dimension 2 is isomorphic to $\sigma(L, \xi)$ for an admissible pair $(L/K, \xi)$, for each local Artin map $\mathrm{art}_L$.
2. If $\sigma(L, \xi) \cong \sigma(L', \xi')$, then $L = L'$ inside $\bar K$.

Part 1 holds because $p \ne 2$: then $W_K$ has no primitive representations of dimension 2. -/
def GaloisTameParametrization : Prop :=
  (2 : 𝓀[K]) ≠ 0 →
    (∀ ρ : WeilDeligneRep K 2, ρ.IsIrreducible → ∃ P : TamePair K,
      ∀ art : P.Lˣ ≃ₜ* WeilGroup.Ab P.L, IsLocalArtinMap P.L art →
        ρ.Iso (tameParam art P.ξ P.adm.smooth)) ∧
    ∀ P Q : TamePair K, ∀ artP : P.Lˣ ≃ₜ* WeilGroup.Ab P.L, IsLocalArtinMap P.L artP →
      ∀ artQ : Q.Lˣ ≃ₜ* WeilGroup.Ab Q.L, IsLocalArtinMap Q.L artQ →
        (tameParam artP P.ξ P.adm.smooth).Iso (tameParam artQ Q.ξ Q.adm.smooth) → P.L = Q.L

/-- **The rectifier** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 34.4). Let $p \ne 2$. There is a family of tamely ramified characters $\Delta_\xi$ of $L^\times$, one for each admissible pair $(L/K, \xi)$, with these properties.

1. $(L/K, \Delta_\xi \xi)$ is admissible.
2. $\Delta_\xi|_{K^\times} = \kappa_{L/K}$, the quadratic character of $L/K$ (`Langlands.LocalGL2.quadChar`).
3. The map $\xi \mapsto \Delta_\xi \xi$ is a bijection on the $K$-isomorphism classes of pairs.
4. It commutes with the twists $\xi \mapsto \xi \otimes \chi_L$ and with $\xi \mapsto \xi^{-1}$, up to isomorphism.

In Bushnell and Henniart, $\Delta_\xi$ is unramified in the unramified case and is given by a Langlands constant in the ramified case. The statement here does not fix $\Delta_\xi$, since `Langlands.LocalLanglandsGL` has no ε-factors. -/
def Rectifier : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∃ (Δ : ∀ P : TamePair K, P.Lˣ →* ℂˣ)
    (hΔ : ∀ P : TamePair K, IsAdmissible K P.L (Δ P * P.ξ)),
    (∀ (P : TamePair K) (artK : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K artK →
      (Δ P).comp (Units.map (algebraMap K P.L).toMonoidHom) = quadChar P.L artK) ∧
    (∀ P Q : TamePair K, (P.rectify Δ hΔ).Iso (Q.rectify Δ hΔ) ↔ P.Iso Q) ∧
    (∀ Q : TamePair K, ∃ P : TamePair K, (P.rectify Δ hΔ).Iso Q) ∧
    (∀ (P : TamePair K) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
      ((P.twist χ hχ).rectify Δ hΔ).Iso ((P.rectify Δ hΔ).twist χ hχ)) ∧
    ∀ P : TamePair K, (P.inv.rectify Δ hΔ).Iso (P.rectify Δ hΔ).inv

/-- **The L-factor of a supercuspidal representation** (Godement and Jacquet, Zeta functions of simple algebras, LNM 260, Theorem 3.3 and Proposition 4.4; Bushnell and Henniart, The local Langlands conjecture for GL(2), 24.2). If the class of an irreducible representation $\pi$ of $GL_2(K)$ contains a supercuspidal representation, then $L(s, \pi) = 1$. -/
def SupercuspidalLFactor : Prop :=
  ∀ π : IrrRep (GL (Fin 2) K), IrrSmooth.mk π ∈ scClasses K → IsGJLFactor K π.1 (fun _ => 1)

/-- **The correspondence off the supercuspidal representations** (Jacquet and Langlands, Automorphic forms on GL(2), LNM 114, Section 3; Bushnell and Henniart, The local Langlands conjecture for GL(2), Chapter 2, 26.1 and 33.1 to 33.3). There is a bijection $e$ from the classes of $\mathrm{Irr}(GL_2(K))$ that are not supercuspidal to the classes of $\mathrm{WD}_2(W_K)$ that are not irreducible, with these properties.

1. Central characters, twists, contragredients and L-factors are as in `Langlands.IsLanglandsMap`, for the classes in the domain of $e$.
2. A twist or a contragredient of a class that is not supercuspidal is not supercuspidal.

The bijection sends a subrepresentation of $\mathrm{Ind}(\chi_1, \chi_2)$ to $\varphi_1 \oplus \varphi_2$, and a twist of the Steinberg representation to a representation with $N \ne 0$. This explicit form is not part of the statement. -/
def NonSupercuspidalLLC (art : Kˣ ≃ₜ* WeilGroup.Ab K) : Prop :=
  ∃ e : {x // x ∉ scClasses K} ≃ {y // y ∉ irrClasses K},
    (∀ (π : IrrRep (GL (Fin 2) K)) (hπ : IrrSmooth.mk π ∉ scClasses K) (ω : Kˣ →* ℂˣ),
      π.1.HasCentralChar ω → ∀ ρ : WeilDeligneRep K 2, WDIso.mk ρ = (e ⟨_, hπ⟩).1 →
        CharCorrespond K art ω ρ.det) ∧
    (∀ x (hx : x ∉ scClasses K) y (hy : y ∉ scClasses K) (χ : Kˣ →* ℂˣ)
      (hχ : IsSmoothChar K χ),
      IrrSmooth.IsTwist y x (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ) →
        ∀ φ : WeilGroup K →* ℂˣ, CharCorrespond K art χ φ →
          WDIso.IsTwist (e ⟨y, hy⟩).1 (e ⟨x, hx⟩).1 φ) ∧
    (∀ x (hx : x ∉ scClasses K) y (hy : y ∉ scClasses K), IrrSmooth.IsContragredient y x →
      WDIso.IsDual (e ⟨y, hy⟩).1 (e ⟨x, hx⟩).1) ∧
    (∀ (π : IrrRep (GL (Fin 2) K)) (hπ : IrrSmooth.mk π ∉ scClasses K)
      (ρ : WeilDeligneRep K 2), WDIso.mk ρ = (e ⟨_, hπ⟩).1 → IsGJLFactor K π.1 ρ.lFactor) ∧
    (∀ x y (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ), x ∉ scClasses K →
      IrrSmooth.IsTwist y x (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ) → y ∉ scClasses K) ∧
    ∀ x y, x ∉ scClasses K → IrrSmooth.IsContragredient y x → y ∉ scClasses K

/-- The published theorems that the reduction uses, for one field $K$ and one local Artin map $\mathrm{art}_K$. -/
structure GL2OddInputs (art : Kˣ ≃ₜ* WeilGroup.Ab K) : Prop where
  /-- Local class field theory for quadratic extensions. -/
  artin : ArtinCompat K
  /-- The tame parametrization theorem. -/
  tame : TameParametrizationGL2 K
  /-- The irreducible representations of $W_K$ of dimension 2. -/
  galois : GaloisTameParametrization K
  /-- The rectifier. -/
  rectifier : Rectifier K
  /-- The L-factor of a supercuspidal representation. -/
  lFactor : SupercuspidalLFactor K
  /-- The correspondence off the supercuspidal representations. -/
  nonSupercuspidal : NonSupercuspidalLLC K art

end Inputs

section Reduction

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The central character of an irreducible representation is unique. -/
theorem eq_of_hasCentralChar {π : SmoothRep (GL (Fin 2) K)} [Nontrivial π.V] {ω ω' : Kˣ →* ℂˣ}
    (h : π.HasCentralChar ω) (h' : π.HasCentralChar ω') : ω = ω' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  ext1 a
  exact Units.ext (smul_left_injective ℂ hv ((h a v).symm.trans (h' a v)))

/-- **Injectivity of the Galois parameter on classes** (BH 34.1). Given the injectivity in the field (part 2 of `Langlands.LocalGL2.GaloisTameParametrization`), $\sigma(P) \cong \sigma(Q)$ exactly when the pairs $P$ and $Q$ are $K$-isomorphic. -/
theorem mk_param_eq_iff
    (hconj : ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
      [Algebra.IsSeparable K L], ArtinConjCompat K L)
    (hfield : ∀ P Q : TamePair K, ∀ artP : P.Lˣ ≃ₜ* WeilGroup.Ab P.L, IsLocalArtinMap P.L artP →
      ∀ artQ : Q.Lˣ ≃ₜ* WeilGroup.Ab Q.L, IsLocalArtinMap Q.L artQ →
        (tameParam artP P.ξ P.adm.smooth).Iso (tameParam artQ Q.ξ Q.adm.smooth) → P.L = Q.L)
    (P Q : TamePair K) : WDIso.mk P.param = WDIso.mk Q.param ↔ P.Iso Q := by
  rcases P with ⟨L, ξ, hξ⟩
  rcases Q with ⟨L', ξ', hξ'⟩
  constructor
  · intro h
    have hiso := Quotient.exact h
    have hL : L = L' := hfield ⟨L, ξ, hξ⟩ ⟨L', ξ', hξ'⟩ _ (isLocalArtinMap_artOf L) _
      (isLocalArtinMap_artOf L') hiso
    subst hL
    exact exists_algEquiv_of_tameParam_iso (hconj L) (isLocalArtinMap_artOf L) hξ.smooth
      hξ'.smooth hiso
  · rintro ⟨j, hj⟩
    have hL := eq_of_algEquiv j
    subst hL
    exact Quotient.sound (tameParam_iso (hconj L) (isLocalArtinMap_artOf L) hξ.smooth hξ'.smooth j hj)

/-- **The local Langlands correspondence for $GL_2(K)$, $p$ odd, from the inputs.** If $p \ne 2$ and the published theorems in `Langlands.LocalGL2.GL2OddInputs` hold, then there is a bijection $\mathrm{Irr}(GL_2(K)) \to \mathrm{WD}_2(W_K)$ with the conditions of `Langlands.IsLanglandsMap`. On the supercuspidal classes it is $\pi_{\Delta_\xi \xi} \mapsto \sigma(L, \xi)$. -/
theorem exists_isLanglandsMap_two (art : Kˣ ≃ₜ* WeilGroup.Ab K) (hart : IsLocalArtinMap K art)
    (hp : (2 : 𝓀[K]) ≠ 0) (h : GL2OddInputs K art) :
    ∃ rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2, IsLanglandsMap K art 2 rec := by
  obtain ⟨pi, hpa, hpb, hpc, hpd, hpe, hpf⟩ := h.tame hp
  obtain ⟨Δ, hΔ, hres, hinj, hsurj, htw, hinv⟩ := h.rectifier hp
  obtain ⟨gsurj, gfield⟩ := h.galois hp
  obtain ⟨e, ec, et, ed, el, ecl1, ecl2⟩ := h.nonSupercuspidal
  have hconj : ∀ (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
      [Algebra.IsSeparable K L], ArtinConjCompat K L := fun L _ _ => (h.artin L).1
  let R : TamePair K → TamePair K := TamePair.rectify Δ hΔ
  let g : Quotient (TamePair.setoid (K := K)) → IrrSmooth (GL (Fin 2) K) :=
    Quotient.lift (fun P => pi (R P)) (fun P Q hPQ => (hpc _ _).2 ((hinj P Q).2 hPQ))
  let f : Quotient (TamePair.setoid (K := K)) → WDIso K 2 :=
    Quotient.lift (fun P => WDIso.mk P.param) (fun P Q hPQ => (mk_param_eq_iff hconj gfield P Q).2 hPQ)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound ((hinj _ _).1 ((hpc _ _).1 hab))
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound ((mk_param_eq_iff hconj gfield _ _).1 hab)
  have hgS : ∀ x, x ∈ scClasses K ↔ ∃ t, g t = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨Q, hQ⟩ := hpb x hx
      obtain ⟨P, hP⟩ := hsurj Q
      exact ⟨Quotient.mk _ P, ((hpc _ _).2 hP).trans hQ⟩
    · rintro ⟨t, rfl⟩
      induction t using Quotient.ind
      exact hpa _
  have hfI : ∀ y, y ∈ irrClasses K ↔ ∃ t, f t = y := by
    intro y
    constructor
    · rintro ⟨ρ, rfl, hρ⟩
      obtain ⟨P, hP⟩ := gsurj ρ hρ
      exact ⟨Quotient.mk _ P, Quotient.sound (Setoid.symm (hP _ (isLocalArtinMap_artOf P.L)))⟩
    · rintro ⟨t, rfl⟩
      induction t using Quotient.ind
      rename_i P
      exact ⟨P.param, rfl, isIrreducible_tameParam (hconj P.L) (isLocalArtinMap_artOf P.L) P.adm⟩
  obtain ⟨rec, hrg, hre⟩ := exists_equiv_glue _ _ g f hg hf hgS hfI e
  have hrg' : ∀ P, rec (pi (R P)) = WDIso.mk P.param := fun P => hrg (Quotient.mk _ P)
  have hS : ∀ x ∈ scClasses K, ∃ P, x = pi (R P) ∧ rec x = WDIso.mk P.param := by
    intro x hx
    obtain ⟨t, rfl⟩ := (hgS x).1 hx
    induction t using Quotient.ind
    rename_i P
    exact ⟨P, rfl, hrg' P⟩
  refine ⟨rec, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro π ω hω ρ hρ
    by_cases hx : IrrSmooth.mk π ∈ scClasses K
    · obtain ⟨P, hxP, hrP⟩ := hS _ hx
      rw [hrP] at hρ
      have hiso : ρ.Iso P.param := Quotient.exact hρ
      have := π.2.1.1
      have hω' := eq_of_hasCentralChar hω (hpd (R P) π hxP)
      have h2 : (R P).ξ.comp (Units.map (algebraMap K (R P).L).toMonoidHom) =
          quadChar P.L art * P.ξ.comp (Units.map (algebraMap K P.L).toMonoidHom) := by
        rw [← hres P art hart]
        rfl
      rw [← WeilDeligneRep.det_eq_of_iso hiso, hω', h2]
      exact det_tameParam (h.artin P.L).2.2 hart (isLocalArtinMap_artOf P.L) P.ξ P.adm.smooth
    · rw [hre _ hx] at hρ
      exact ec π hx ω hω ρ hρ
  · intro x y χ hχ hxy φ hφ
    by_cases hx : x ∈ scClasses K
    · obtain ⟨P, rfl, hrP⟩ := hS _ hx
      have hy : y = pi (R (P.twist χ hχ)) :=
        (hpe (R P) χ hχ y hxy).trans ((hpc _ _).2 (htw P χ hχ)).symm
      subst hy
      rw [hrP, hrg']
      exact tameParam_isTwist (h.artin P.L).2.1 hart (isLocalArtinMap_artOf P.L) P.adm.smooth hχ hφ
    · have hy := ecl1 x y χ hχ hx hxy
      rw [hre _ hx, hre _ hy]
      exact et x hx y hy χ hχ hxy φ hφ
  · intro x y hxy
    by_cases hx : x ∈ scClasses K
    · obtain ⟨P, rfl, hrP⟩ := hS _ hx
      have hy : y = pi (R P.inv) := (hpf (R P) y hxy).trans ((hpc _ _).2 (hinv P)).symm
      subst hy
      rw [hrP, hrg']
      exact tameParam_isDual (artOf P.L) P.adm.smooth P.inv.adm.smooth
    · have hy := ecl2 x y hx hxy
      rw [hre _ hx, hre _ hy]
      exact ed x hx y hy hxy
  · intro π ρ hρ
    by_cases hx : IrrSmooth.mk π ∈ scClasses K
    · obtain ⟨P, -, hrP⟩ := hS _ hx
      rw [hrP] at hρ
      have hiso : P.param.Iso ρ := Setoid.symm (Quotient.exact hρ)
      have hirr := isIrreducible_of_iso hiso
        (isIrreducible_tameParam (hconj P.L) (isLocalArtinMap_artOf P.L) P.adm)
      rw [lFactor_eq_one_of_isIrreducible hirr]
      exact h.lFactor π hx
    · rw [hre _ hx] at hρ
      exact el π hx ρ hρ

end Reduction

end LocalGL2

/-- **The local Langlands correspondence for $GL_2$, $p$ odd, from published theorems.** If for each nonarchimedean local field $K$ with $p \ne 2$ and each local Artin map $\mathrm{art}_K$ the published theorems in `Langlands.LocalGL2.GL2OddInputs` hold, then `Langlands.LocalLanglandsGL2Odd` holds. The family is $\mathrm{rec}_0$ and $\mathrm{rec}_1$ of `Langlands.LocalGL1.localLanglandsGL_one`, and $\mathrm{rec}_2$ of `Langlands.LocalGL2.exists_isLanglandsMap_two`. -/
theorem localLanglandsGL2_odd_of_inputs
    (h : ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
        (2 : 𝓀[K]) ≠ 0 → LocalGL2.GL2OddInputs K art) :
    LocalLanglandsGL2Odd.{u} := by
  intro K _ _ _ _ art hart hp
  obtain ⟨R1, hR1⟩ := LocalGL1.localLanglandsGL_one K art hart
  obtain ⟨rec2, hrec2⟩ := LocalGL2.exists_isLanglandsMap_two art hart hp (h K art hart hp)
  refine ⟨fun
    | 0, _ => R1 0 (Nat.zero_le 1)
    | 1, _ => R1 1 le_rfl
    | 2, _ => rec2
    | _ + 3, hm => absurd hm (by omega), ?_⟩
  exact
    { gl1 := fun _ => hR1.gl1 le_rfl
      map := fun
        | 0, _ => hR1.map 0 (Nat.zero_le 1)
        | 1, _ => hR1.map 1 le_rfl
        | 2, _ => hrec2
        | _ + 3, hm => absurd hm (by omega) }

end Langlands
