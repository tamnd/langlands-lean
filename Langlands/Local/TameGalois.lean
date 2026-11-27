/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.AdmissiblePairs
import Langlands.Local.WeilInduction
import Langlands.WeilGroup.Embedding
import Langlands.Statements.ClassField

/-!
# The Galois parameter of an admissible pair

Let $F$ be a nonarchimedean local field and let $L / F$ be a quadratic separable extension inside $\bar F$. Let $\mathrm{art}_L : L^\times \to W_L^{ab}$ be a local Artin map and let $\xi$ be a smooth character of $L^\times$. This file defines the character $\xi_W = \xi \circ \mathrm{art}_L^{-1}$ of $W_L$ and the Weil-Deligne representation $\sigma(L, \xi) = (\mathrm{Ind}_{W_L}^{W_F} \xi_W, 0)$ of Bushnell and Henniart, section 34.1. Then it proves the basic properties of the map $(L, \xi) \mapsto \sigma(L, \xi)$.

The proofs use three published theorems of local class field theory. Each one is a named hypothesis of type `Prop`, and each one quantifies over all local Artin maps. None of them mentions admissible pairs.

* `Langlands.LocalGL2.ArtinConjCompat`: the Artin map is compatible with conjugation.
* `Langlands.LocalGL2.ArtinNormCompat`: the inclusion $W_L \to W_F$ corresponds to the norm.
* `Langlands.LocalGL2.ArtinTransferCompat`: the transfer $W_F \to W_L^{ab}$ corresponds to the inclusion $F^\times \to L^\times$.

## Main definitions

* `Langlands.LocalGL2.charW`: the character $\xi_W$ of the subgroup $W_L$ of $W_F$.
* `Langlands.LocalGL2.tameParam`: the Weil-Deligne representation $\sigma(L, \xi)$.
* `Langlands.LocalGL2.twistWD`: the twist of a Weil-Deligne representation by a character.
* `Langlands.LocalGL2.quadChar`: the quadratic character $\kappa_{L/F}$ of $F^\times$.

## Main results

* `Langlands.LocalGL2.isIrreducible_tameParam`: if $(L, \xi)$ is admissible, then $\sigma(L, \xi)$ is irreducible.
* `Langlands.LocalGL2.tameParam_iso`: $F$-isomorphic pairs give isomorphic representations.
* `Langlands.LocalGL2.eq_of_algEquiv`: an $F$-isomorphism of quadratic extensions inside $\bar F$ is an equality.
* `Langlands.LocalGL2.tameParam_twist`, `Langlands.LocalGL2.tameParam_isTwist`: $\sigma(L, \xi \otimes \chi_L) \cong \sigma(L, \xi) \otimes \varphi$ for $\varphi = \chi \circ \mathrm{art}_F^{-1}$.
* `Langlands.LocalGL2.quadChar_eq_one_iff`: the kernel of $\kappa_{L/F}$ is the norm group.
* `Langlands.LocalGL2.det_tameParam`: $\det \sigma(L, \xi)$ corresponds to $\kappa_{L/F} \cdot \xi|_{F^\times}$.
* `Langlands.LocalGL2.eq_or_eq_comp_of_tameParam_iso`, `Langlands.LocalGL2.exists_algEquiv_of_tameParam_iso`: if $\sigma(L, \xi) \cong \sigma(L, \xi')$, then $\xi' = \xi$ or $\xi' = \xi \circ \sigma$.

## Implementation notes

The field $L$ is an intermediate field of $\bar F / F$, so that $W_L$ is a subgroup of $W_F$. By `Langlands.LocalGL2.eq_of_algEquiv`, two $F$-isomorphic such fields are equal. Thus injectivity for a fixed $L$ is injectivity for $F$-isomorphic fields. The results use one fixed Artin map $\mathrm{art}_L$ for each field.

## Still open

* Independence of the choice of $\mathrm{art}_L$. This needs the uniqueness of the local Artin map.
* A bridge to `Langlands.LocalGL2.AdmissiblePair`, where $E$ is an abstract field and not a subfield of $\bar F$.
* Injectivity for two fields $L \neq L'$. This needs the fact that the restriction of $\sigma(L, \xi)$ to $W_L$ determines $L$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), sections 29.2 and 34.1.
* J.-P. Serre, Local fields, chapter XI, section 3.
* J. Neukirch, Algebraic number theory, chapter IV, section 6, and chapter V, section 1.
* J. Tate, Number theoretic background, section 1.
-/

namespace Langlands.LocalGL2

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt

universe u

section Transfer

variable {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex] {A B : Type*} [CommGroup A]
  [CommGroup B]

/-- The transfer is natural in the target: $(\psi \circ \phi)^{\mathrm{tr}} = \psi \circ \phi^{\mathrm{tr}}$. -/
theorem transfer_comp (ψ : A →* B) (ϕ : H →* A) (g : G) :
    (ψ.comp ϕ).transfer g = ψ (ϕ.transfer g) := by
  rw [MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [Subgroup.leftTransversals.diff, map_prod]
  rfl

end Transfer

section Character

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {L : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F L]

variable (F L) in
/-- The map from the subgroup $W_L$ of $W_F$ to $W_L^{ab}$, through the isomorphism `Langlands.WeilGroup.weilEquiv` of $W_L$ with the subgroup. -/
noncomputable def toAbSub : restrictSubgroup F L →* WeilGroup.Ab L :=
  (QuotientGroup.mk' _).comp (weilEquiv F L).symm.toMulEquiv.toMonoidHom

/-- On $W_L$, the map `toAbSub` is the quotient map $W_L \to W_L^{ab}$. -/
theorem toAbSub_weilEquiv (w : WeilGroup L) :
    toAbSub F L (weilEquiv F L w) = (QuotientGroup.mk w : WeilGroup.Ab L) := by
  change QuotientGroup.mk' _ ((weilEquiv F L).symm (weilEquiv F L w)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- The map `toAbSub` is continuous. -/
theorem continuous_toAbSub : Continuous (toAbSub F L) :=
  QuotientGroup.continuous_mk.comp (weilEquiv F L).symm.continuous

/-- The map `toAbSub` is surjective. -/
theorem toAbSub_surjective : Function.Surjective (toAbSub F L) := by
  intro a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  exact ⟨weilEquiv F L w, toAbSub_weilEquiv w⟩

/-- The character $\xi_W = \xi \circ \mathrm{art}_L^{-1}$ of the subgroup $W_L$ of $W_F$, for a character $\xi$ of $L^\times$. -/
noncomputable def charW (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) : restrictSubgroup F L →* ℂˣ :=
  ξ.comp (art.symm.toMulEquiv.toMonoidHom.comp (toAbSub F L))

/-- The value of $\xi_W$ at $h$ is $\xi(\mathrm{art}_L^{-1}(h))$. -/
theorem charW_apply (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) (h : restrictSubgroup F L) :
    charW art ξ h = ξ (art.symm (toAbSub F L h)) := rfl

/-- If the image of $h$ in $W_L^{ab}$ is $\mathrm{art}_L(x)$, then $\xi_W(h) = \xi(x)$. -/
theorem charW_eq_of_toAbSub (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ)
    {h : restrictSubgroup F L} {x : Lˣ} (hx : toAbSub F L h = art x) : charW art ξ h = ξ x := by
  rw [charW_apply, hx]
  simp

/-- If the class of $w \in W_L$ is $\mathrm{art}_L(x)$, then $\xi_W(w) = \xi(x)$. -/
theorem charW_weilEquiv (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) {w : WeilGroup L} {x : Lˣ}
    (hx : (QuotientGroup.mk w : WeilGroup.Ab L) = art x) : charW art ξ (weilEquiv F L w) = ξ x :=
  charW_eq_of_toAbSub art ξ ((toAbSub_weilEquiv w).trans hx)

/-- The map $\xi \mapsto \xi_W$ is injective. -/
theorem charW_injective (art : Lˣ ≃ₜ* WeilGroup.Ab L) :
    Function.Injective (charW (F := F) art) := by
  intro ξ ξ' h
  ext1 x
  obtain ⟨g, hg⟩ := toAbSub_surjective (F := F) (L := L) (art x)
  rw [← charW_eq_of_toAbSub art ξ hg, ← charW_eq_of_toAbSub art ξ' hg, h]

/-- If $\xi$ is smooth, then $\xi_W$ has an open kernel. -/
theorem isOpen_ker_charW (art : Lˣ ≃ₜ* WeilGroup.Ab L) {ξ : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ) :
    IsOpen ((charW art ξ).ker : Set (restrictSubgroup F L)) :=
  hξ.preimage (art.symm.continuous.comp continuous_toAbSub)

end Character

section Abstract

open Matrix

variable {W : Type*} [Group W] {H : Subgroup W}

/-- Isomorphism of representations is symmetric. -/
theorem RepIso.symm {n : ℕ} {ρ ρ' : W →* GL (Fin n) ℂ} (h : RepIso ρ ρ') : RepIso ρ' ρ := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun w => by rw [hg w]; group⟩

/-- **The constituents of an induced representation.** If $\mathrm{Ind}_H^W \varphi \cong \mathrm{Ind}_H^W \varphi'$, then $\varphi' = \varphi$ or $\varphi' = \varphi^s$. The image of the first basis vector under the isomorphism is an eigenvector of $H$ with the character $\varphi'$, and on $H$ the representation $\mathrm{Ind}_H^W \varphi$ is the diagonal sum $\varphi \oplus \varphi^s$. -/
theorem eq_or_eq_conjChar_of_repIso (hH : H.index = 2) {s : W} (hs : s ∉ H) {φ φ' : H →* ℂˣ}
    (h : RepIso (ind hH hs φ) (ind hH hs φ')) : φ' = φ ∨ φ' = conjChar hH s φ := by
  obtain ⟨g, hg⟩ := h
  set e : Fin 2 → ℂ := Pi.single 0 1
  set v : Fin 2 → ℂ := ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e
  have hv : v ≠ 0 := by
    intro h0
    have : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = e := by
      simp only [v, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [h0, mulVec_zero] at this
    have h1 := congrFun this 0
    simp [e] at h1
  have heig : ∀ (k : H) (i : Fin 2), ![(φ k : ℂ), (conjChar hH s φ k : ℂ)] i * v i =
      (φ' k : ℂ) * v i := by
    intro k i
    have h1 : ((ind hH hs φ k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v =
        ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
          (((ind hH hs φ' k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e) := by
      rw [hg k]
      simp only [v, mulVec_mulVec, ← Units.val_mul]
      congr 2
      group
    have h2 : ((ind hH hs φ' k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e =
        (φ' k : ℂ) • e := by
      rw [ind_apply_of_mem hH hs]
      ext j
      fin_cases j <;> simp [e, mulVec_diagonal]
    rw [h2, mulVec_smul, ind_apply_of_mem hH hs] at h1
    have h3 := congrFun h1 i
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext j
      fin_cases j
      · exact h0
      · exact h1
    right
    ext k
    exact (mul_right_cancel₀ h1 (heig k 1)).symm
  · left
    ext k
    exact (mul_right_cancel₀ h0 (heig k 0)).symm

end Abstract

section Hypotheses

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]

/-- **Functoriality of the Artin map under conjugation** (Serre, Local fields, Chapter XI, Section 3; Neukirch, Algebraic number theory, Chapter IV, Section 6, and Chapter V, Section 1; Tate, Number theoretic background, Section 1). Let $s \in W_F$ with $s(L) = L$, and let $\tau$ be the automorphism $y \mapsto s(y)$ of $L$. Then the conjugation $h \mapsto s h s^{-1}$ of $W_L$ corresponds to $\tau$ on $L^\times$ through each local Artin map $\mathrm{art}_L$: $\mathrm{art}_L(\tau x) = s \, \mathrm{art}_L(x) \, s^{-1}$. Here $W_L$ is seen in $W_F$ through `Langlands.WeilGroup.weilHom`. -/
def ArtinConjCompat : Prop :=
  ∀ art : Lˣ ≃ₜ* WeilGroup.Ab L, IsLocalArtinMap L art →
    ∀ (s : WeilGroup F) (τ : L ≃ₐ[F] L),
      (∀ y : L, ((τ y : L) : AlgebraicClosure F) = toGalois F s • (y : AlgebraicClosure F)) →
      ∀ (x : Lˣ) (w w' : WeilGroup L), weilHom F L w' = s * weilHom F L w * s⁻¹ →
        (QuotientGroup.mk w : WeilGroup.Ab L) = art x →
        (QuotientGroup.mk w' : WeilGroup.Ab L) = art (unitsMap τ x)

/-- **The norm corresponds to the inclusion** (Serre, Local fields, Chapter XI, Section 3; Neukirch, Algebraic number theory, Chapter IV, Section 6, and Chapter V, Section 1; Tate, Number theoretic background, Section 1). For local Artin maps $\mathrm{art}_F$ and $\mathrm{art}_L$, the map $W_L^{ab} \to W_F^{ab}$ induced by the inclusion $W_L \to W_F$ corresponds to the norm $N_{L/F} : L^\times \to F^\times$. -/
def ArtinNormCompat : Prop :=
  ∀ artF : Fˣ ≃ₜ* WeilGroup.Ab F, IsLocalArtinMap F artF →
    ∀ artL : Lˣ ≃ₜ* WeilGroup.Ab L, IsLocalArtinMap L artL →
      ∀ (x : Lˣ) (w : WeilGroup L), (QuotientGroup.mk w : WeilGroup.Ab L) = artL x →
        (QuotientGroup.mk (weilHom F L w) : WeilGroup.Ab F) = artF (normUnits F L x)

/-- **The transfer corresponds to the inclusion** (Serre, Local fields, Chapter XI, Section 3; Neukirch, Algebraic number theory, Chapter IV, Section 6, and Chapter V, Section 1; Tate, Number theoretic background, Section 1). For local Artin maps $\mathrm{art}_F$ and $\mathrm{art}_L$, the transfer $W_F^{ab} \to W_L^{ab}$ corresponds to the inclusion $F^\times \to L^\times$. -/
def ArtinTransferCompat : Prop :=
  ∀ artF : Fˣ ≃ₜ* WeilGroup.Ab F, IsLocalArtinMap F artF →
    ∀ artL : Lˣ ≃ₜ* WeilGroup.Ab L, IsLocalArtinMap L artL →
      ∀ (a : Fˣ) (w : WeilGroup F), (QuotientGroup.mk w : WeilGroup.Ab F) = artF a →
        (toAbSub F L).transfer w = artL (Units.map (algebraMap F L).toMonoidHom a)

end Hypotheses

section Param

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {L : IntermediateField F (AlgebraicClosure F)} [Algebra.IsQuadraticExtension F L]
  [Algebra.IsSeparable F L]

/-- The subgroup $W_L$ has index $2$ in $W_F$. -/
theorem index_restrictSubgroup_quad : (restrictSubgroup F L).index = 2 :=
  index_restrictSubgroup_eq_two (Algebra.IsQuadraticExtension.finrank_eq_two F L)

variable (F L) in
/-- There is an element of $W_F$ outside $W_L$. -/
theorem exists_notMem_restrictSubgroup : ∃ s : WeilGroup F, s ∉ restrictSubgroup F L := by
  by_contra h
  push Not at h
  have h1 : restrictSubgroup F L = ⊤ := eq_top_iff.2 fun x _ => h x
  have h2 := index_restrictSubgroup_quad (F := F) (L := L)
  rw [h1, Subgroup.index_top] at h2
  omega

variable (F L) in
/-- A fixed element $s$ of $W_F$ outside $W_L$. -/
noncomputable def outElt : WeilGroup F :=
  (exists_notMem_restrictSubgroup F L).choose

/-- The element `outElt F L` is not in $W_L$. -/
theorem outElt_notMem : outElt F L ∉ restrictSubgroup F L :=
  (exists_notMem_restrictSubgroup F L).choose_spec

/-- An element $s$ of $W_F$ outside $W_L$ acts on $L$ as the Galois conjugation $\sigma$. -/
theorem galConj_eq_smul {s : WeilGroup F} (hs : s ∉ restrictSubgroup F L) (y : L) :
    ((galConj F L y : L) : AlgebraicClosure F) = toGalois F s • (y : AlgebraicClosure F) := by
  have : Normal F L := Algebra.IsQuadraticExtension.normal F L
  set τ : L ≃ₐ[F] L := (galEquiv F (toGalois F s)).restrictNormal L
  have hτ : ∀ z : L, ((τ z : L) : AlgebraicClosure F) = toGalois F s • (z : AlgebraicClosure F) :=
    fun z => AlgEquiv.restrictNormal_commutes _ L z
  have hne : τ ≠ 1 := by
    intro h1
    apply hs
    rw [mem_restrictSubgroup]
    intro x hx
    have := hτ ⟨x, hx⟩
    rw [h1] at this
    exact this.symm
  rcases eq_one_or_eq_galConj F L τ with h | h
  · exact absurd h hne
  · rw [← h]
    exact hτ y

/-- **The Galois parameter of a pair** (BH 34.1). For a quadratic separable extension $L/F$ inside $\bar F$, a local Artin map $\mathrm{art}_L$ and a smooth character $\xi$ of $L^\times$, the Weil-Deligne representation $\sigma(L, \xi) = (\mathrm{Ind}_{W_L}^{W_F} \xi_W, 0)$ with $\xi_W = \xi \circ \mathrm{art}_L^{-1}$. -/
noncomputable def tameParam (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) (hξ : IsSmoothChar L ξ) :
    WeilDeligneRep F 2 :=
  indWD (Algebra.IsQuadraticExtension.finrank_eq_two F L) (outElt_notMem (F := F) (L := L))
    (charW art ξ) (isOpen_ker_charW art hξ)

/-- The representation of $\sigma(L, \xi)$ is $\mathrm{Ind}_{W_L}^{W_F} \xi_W$. -/
theorem tameParam_r (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) (hξ : IsSmoothChar L ξ) :
    (tameParam art ξ hξ).r =
      ind index_restrictSubgroup_quad (outElt_notMem (F := F) (L := L)) (charW art ξ) := rfl

/-- The monodromy of $\sigma(L, \xi)$ is $0$. -/
@[simp]
theorem tameParam_N (art : Lˣ ≃ₜ* WeilGroup.Ab L) (ξ : Lˣ →* ℂˣ) (hξ : IsSmoothChar L ξ) :
    (tameParam art ξ hξ).N = 0 := rfl

/-- **Conjugation of characters** (BH 34.1). For $s \in W_F$ outside $W_L$, $(\xi_W)^s = (\xi \circ \sigma)_W$. This uses the functoriality of the Artin map under conjugation. -/
theorem conjChar_charW (hconj : ArtinConjCompat F L) {art : Lˣ ≃ₜ* WeilGroup.Ab L}
    (hart : IsLocalArtinMap L art) {s : WeilGroup F} (hs : s ∉ restrictSubgroup F L)
    (ξ : Lˣ →* ℂˣ) :
    conjChar index_restrictSubgroup_quad s (charW art ξ) =
      charW art (ξ.comp (galConjUnits F L)) := by
  ext1 h
  obtain ⟨w, rfl⟩ := (weilEquiv F L).surjective h
  set x := art.symm (QuotientGroup.mk w : WeilGroup.Ab L)
  have hx : (QuotientGroup.mk w : WeilGroup.Ab L) = art x := by simp [x]
  obtain ⟨w', hw'⟩ := (weilEquiv F L).surjective
    ⟨s⁻¹ * (weilEquiv F L w : WeilGroup F) * s,
      conj_mem index_restrictSubgroup_quad s (weilEquiv F L w).2⟩
  have hw'' : weilHom F L w' = s⁻¹ * weilHom F L w * s⁻¹⁻¹ := by
    rw [inv_inv]
    exact congrArg Subtype.val hw'
  have hinv : s⁻¹ ∉ restrictSubgroup F L := fun h =>
    hs (by simpa using (restrictSubgroup F L).inv_mem h)
  have h1 := hconj art hart s⁻¹ (galConj F L) (galConj_eq_smul hinv) x w w' hw'' hx
  rw [conjChar_apply, ← hw', charW_weilEquiv art ξ h1, charW_weilEquiv art _ hx]
  rfl

/-- **Irreducibility** (BH 34.1). If $(L, \xi)$ is admissible, then $\sigma(L, \xi)$ is irreducible. -/
theorem isIrreducible_tameParam (hconj : ArtinConjCompat F L) {art : Lˣ ≃ₜ* WeilGroup.Ab L}
    (hart : IsLocalArtinMap L art) {ξ : Lˣ →* ℂˣ} (hξ : IsAdmissible F L ξ) :
    (tameParam art ξ hξ.smooth).IsIrreducible := by
  refine isIrreducible_indWD _ _ _ ?_
  rw [conjChar_charW hconj hart outElt_notMem]
  exact fun h => hξ.comp_galConjUnits_ne (charW_injective art h)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra.IsSeparable F L] in
/-- An $F$-isomorphism of quadratic extensions inside $\bar F$ is an equality: $L / F$ is normal, so each $F$-embedding of $L$ in $\bar F$ has image $L$. -/
theorem eq_of_algEquiv {L' : IntermediateField F (AlgebraicClosure F)} (j : L ≃ₐ[F] L') : L = L' := by
  have : Normal F L := Algebra.IsQuadraticExtension.normal F L
  rw [← AlgHom.fieldRange_of_normal (L'.val.comp j.toAlgHom)]
  ext x
  rw [AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨y, rfl⟩
    exact (j y).2
  · intro hx
    exact ⟨j.symm ⟨x, hx⟩, by simp⟩

/-- **Invariance under isomorphism** (BH 34.1). If $\xi = \xi' \circ j$ for an $F$-automorphism $j$ of $L$, then $\sigma(L, \xi) \cong \sigma(L, \xi')$. -/
theorem tameParam_iso (hconj : ArtinConjCompat F L) {art : Lˣ ≃ₜ* WeilGroup.Ab L}
    (hart : IsLocalArtinMap L art) {ξ ξ' : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ)
    (hξ' : IsSmoothChar L ξ') (j : L ≃ₐ[F] L) (hj : ξ = ξ'.comp (unitsMap j)) :
    (tameParam art ξ hξ).Iso (tameParam art ξ' hξ') := by
  have hrep : RepIso (tameParam art ξ hξ).r (tameParam art ξ' hξ').r := by
    rw [tameParam_r, tameParam_r]
    rcases eq_one_or_eq_galConj F L j with rfl | rfl
    · have : ξ = ξ' := by
        rw [hj]
        ext x
        rfl
      subst this
      exact ⟨1, fun w => by simp⟩
    · rw [hj, ← conjChar_charW hconj hart outElt_notMem]
      exact (repIso_ind_conjChar _ _ _).symm
  obtain ⟨g, hg⟩ := hrep
  exact ⟨g, hg, by simp⟩

/-- The twist $(\varphi r, N)$ of a Weil-Deligne representation $(r, N)$ by a smooth character $\varphi$ of $W_F$. -/
noncomputable def twistWD {m : ℕ} (φ : WeilGroup F →* ℂˣ) (hφ : IsOpen (φ.ker : Set (WeilGroup F)))
    (ρ : WeilDeligneRep F m) : WeilDeligneRep F m where
  r := twistRep φ ρ.r
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := φ.ker ⊓ ρ.r.ker) (fun w hw => ?_) (hφ.inter ρ.isOpen_ker)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hw
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [coe_twistRep, hw.1, hw.2]
    simp
  N := ρ.N
  isNilpotent := ρ.isNilpotent
  conj w := by
    have hinv : (((twistRep φ ρ.r w)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) =
        ((φ w)⁻¹ : ℂˣ) • (((ρ.r w)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
      rw [← map_inv, coe_twistRep, map_inv, map_inv]
      rfl
    rw [hinv, coe_twistRep, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Units.smul_def,
      smul_smul, Units.mul_inv, one_smul, ρ.conj w]
  semisimple w := by
    rw [coe_twistRep, map_smul]
    exact Module.End.IsSemisimple_smul _ (ρ.semisimple w)

/-- A character of $W_F$ that corresponds to a smooth character of $F^\times$ is smooth. -/
theorem isOpen_ker_of_charCorrespond {artF : Fˣ ≃ₜ* WeilGroup.Ab F} {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar F χ) {φ : WeilGroup F →* ℂˣ} (hφ : CharCorrespond F artF χ φ) :
    IsOpen (φ.ker : Set (WeilGroup F)) := by
  have he : ∀ w, φ w = χ (artF.symm (QuotientGroup.mk w)) := fun w =>
    (hφ _ w (by simp)).symm
  have : (φ.ker : Set (WeilGroup F)) =
      (fun w => artF.symm (QuotientGroup.mk w : WeilGroup.Ab F)) ⁻¹' (χ.ker : Set Fˣ) := by
    ext w
    simp [he w]
  rw [this]
  exact hχ.preimage (artF.symm.continuous.comp QuotientGroup.continuous_mk)

/-- If $\xi$ and $\chi$ are smooth, then the twist $\xi \otimes \chi_L$ is smooth. -/
theorem isSmoothChar_twistChar {ξ : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar F χ) : IsSmoothChar L (twistChar F L ξ χ) := by
  refine Subgroup.isOpen_mono (H₁ := ξ.ker ⊓ (χ.comp (normUnits F L)).ker) (fun x hx => ?_)
    (hξ.inter (isSmoothChar_comp_normUnits (E := L) hχ))
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  rw [MonoidHom.mem_ker, twistChar_apply, hx.1, hx.2, mul_one]

omit [Algebra.IsSeparable F L] in
/-- **Twisted characters** (BH 34.1). $(\xi \otimes \chi_L)_W = \xi_W \cdot \varphi|_{W_L}$ when $\varphi = \chi \circ \mathrm{art}_F^{-1}$. This uses the compatibility of the Artin maps with the norm. -/
theorem charW_twistChar (hnorm : ArtinNormCompat F L) {artF : Fˣ ≃ₜ* WeilGroup.Ab F}
    (hartF : IsLocalArtinMap F artF) {artL : Lˣ ≃ₜ* WeilGroup.Ab L} (hartL : IsLocalArtinMap L artL)
    (ξ : Lˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) {φ : WeilGroup F →* ℂˣ} (hφ : CharCorrespond F artF χ φ) :
    charW artL (twistChar F L ξ χ) = charW artL ξ * φ.comp (restrictSubgroup F L).subtype := by
  ext1 h
  obtain ⟨w, rfl⟩ := (weilEquiv F L).surjective h
  set x := artL.symm (QuotientGroup.mk w : WeilGroup.Ab L)
  have hx : (QuotientGroup.mk w : WeilGroup.Ab L) = artL x := by simp [x]
  rw [MonoidHom.mul_apply, charW_weilEquiv artL _ hx, charW_weilEquiv artL _ hx, twistChar_apply,
    MonoidHom.comp_apply, hφ _ _ (hnorm artF hartF artL hartL x w hx)]
  rfl

/-- **Twist equivariance** (BH 34.1). Let $\chi$ be a smooth character of $F^\times$ and $\varphi = \chi \circ \mathrm{art}_F^{-1}$. Then $\sigma(L, \xi \otimes \chi_L) \cong \sigma(L, \xi) \otimes \varphi$. -/
theorem tameParam_twist (hnorm : ArtinNormCompat F L) {artF : Fˣ ≃ₜ* WeilGroup.Ab F}
    (hartF : IsLocalArtinMap F artF) {artL : Lˣ ≃ₜ* WeilGroup.Ab L} (hartL : IsLocalArtinMap L artL)
    {ξ : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ) {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar F χ)
    {φ : WeilGroup F →* ℂˣ}
    (hφ : CharCorrespond F artF χ φ) :
    (tameParam artL (twistChar F L ξ χ) (isSmoothChar_twistChar hξ hχ)).Iso
      (twistWD φ (isOpen_ker_of_charCorrespond hχ hφ) (tameParam artL ξ hξ)) := by
  have h := repIso_ind_mul_restrict index_restrictSubgroup_quad
    (outElt_notMem (F := F) (L := L)) (charW artL ξ) φ
  rw [← charW_twistChar hnorm hartF hartL ξ χ hφ] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg, by simp [twistWD]⟩

/-- **Twist equivariance on classes** (BH 34.1). The class of $\sigma(L, \xi \otimes \chi_L)$ is the twist of the class of $\sigma(L, \xi)$ by $\varphi = \chi \circ \mathrm{art}_F^{-1}$, in the sense of `Langlands.WDIso.IsTwist`. -/
theorem tameParam_isTwist (hnorm : ArtinNormCompat F L) {artF : Fˣ ≃ₜ* WeilGroup.Ab F}
    (hartF : IsLocalArtinMap F artF) {artL : Lˣ ≃ₜ* WeilGroup.Ab L} (hartL : IsLocalArtinMap L artL)
    {ξ : Lˣ →* ℂˣ} (hξ : IsSmoothChar L ξ) {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar F χ)
    {φ : WeilGroup F →* ℂˣ}
    (hφ : CharCorrespond F artF χ φ) :
    WDIso.IsTwist (WDIso.mk (tameParam artL (twistChar F L ξ χ) (isSmoothChar_twistChar hξ hχ)))
      (WDIso.mk (tameParam artL ξ hξ)) φ :=
  ⟨tameParam artL ξ hξ, twistWD φ (isOpen_ker_of_charCorrespond hχ hφ) (tameParam artL ξ hξ), rfl,
    Quotient.sound (Setoid.symm (tameParam_twist hnorm hartF hartL hξ hχ hφ)),
    fun w => coe_twistRep φ _ w, rfl⟩

/-- The kernel of the sign character of $W_F / W_L$ is $W_L$. -/
theorem ker_signChar : (signChar (index_restrictSubgroup_quad (F := F) (L := L))).ker =
    restrictSubgroup F L := by
  ext w
  rw [MonoidHom.mem_ker]
  simp only [signChar, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with hw
  · simp [hw]
  · simp only [hw, iff_false]
    intro h
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    norm_num at this

variable (F L) in
/-- The sign character of $W_F / W_L$, as a character of $W_F^{ab}$. -/
noncomputable def signAb : WeilGroup.Ab F →* ℂˣ :=
  QuotientGroup.lift _ (signChar (index_restrictSubgroup_quad (F := F) (L := L)))
    (Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (by rw [ker_signChar]; exact Subgroup.isClosed_of_isOpen _ (isOpen_restrictSubgroup F L)))

variable (L) in
/-- The quadratic character $\kappa_{L/F} = \mathrm{sign}_{W_F / W_L} \circ \mathrm{art}_F$ of $F^\times$. By `Langlands.LocalGL2.quadChar_eq_one_iff` its kernel is the norm group $N_{L/F}(L^\times)$. -/
noncomputable def quadChar (artF : Fˣ ≃ₜ* WeilGroup.Ab F) : Fˣ →* ℂˣ :=
  (signAb F L).comp artF.toMulEquiv.toMonoidHom

/-- If the class of $w$ is $\mathrm{art}_F(a)$, then $\kappa_{L/F}(a)$ is the sign of $w$ in $W_F / W_L$. -/
theorem quadChar_eq_signChar {artF : Fˣ ≃ₜ* WeilGroup.Ab F} {a : Fˣ} {w : WeilGroup F}
    (hw : (QuotientGroup.mk w : WeilGroup.Ab F) = artF a) :
    quadChar L artF a = signChar (index_restrictSubgroup_quad (F := F) (L := L)) w := by
  change signAb F L (artF a) = _
  rw [← hw]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A quadratic separable extension is abelian. -/
theorem isAbelianGalois_quad : IsAbelianGalois F L where
  is_comm := ⟨fun a b => by
    rcases eq_one_or_eq_galConj F L a with rfl | rfl <;>
      rcases eq_one_or_eq_galConj F L b with rfl | rfl <;> simp⟩

/-- **The kernel of the quadratic character** (local class field theory). $\kappa_{L/F}(a) = 1$ exactly when $a$ is a norm from $L^\times$. -/
theorem quadChar_eq_one_iff {artF : Fˣ ≃ₜ* WeilGroup.Ab F} (hartF : IsLocalArtinMap F artF)
    (a : Fˣ) : quadChar L artF a = 1 ↔ a ∈ normGroup F L := by
  have := isAbelianGalois_quad (F := F) (L := L)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (artF a)
  rw [← hartF.ker L a, quadChar_eq_signChar hw, ← MonoidHom.mem_ker, ker_signChar, ← hw,
    Ab.restrict_mk, ← MonoidHom.mem_ker, ← restrictSubgroup_eq_ker]

/-- **The determinant** (BH 34.1, with BH 29.2). The determinant of $\sigma(L, \xi)$ corresponds through $\mathrm{art}_F$ to the character $\kappa_{L/F} \cdot \xi|_{F^\times}$ of $F^\times$. This uses the compatibility of the Artin maps with the transfer. -/
theorem det_tameParam (htr : ArtinTransferCompat F L) {artF : Fˣ ≃ₜ* WeilGroup.Ab F}
    (hartF : IsLocalArtinMap F artF) {artL : Lˣ ≃ₜ* WeilGroup.Ab L} (hartL : IsLocalArtinMap L artL)
    (ξ : Lˣ →* ℂˣ) (hξ : IsSmoothChar L ξ) :
    CharCorrespond F artF (quadChar L artF * ξ.comp (Units.map (algebraMap F L).toMonoidHom))
      (tameParam artL ξ hξ).det := by
  intro a w hw
  change _ = (ind index_restrictSubgroup_quad outElt_notMem (charW artL ξ) w).det
  rw [det_ind_eq_signChar_mul_transfer, MonoidHom.mul_apply, quadChar_eq_signChar hw, charW,
    transfer_comp, transfer_comp, htr artF hartF artL hartL a w hw]
  simp only [MonoidHom.comp_apply]
  exact congrArg _ (congrArg ξ (artL.symm_apply_apply _).symm)

/-- **Injectivity for a fixed field** (BH 34.1). If $\sigma(L, \xi) \cong \sigma(L, \xi')$, then $\xi' = \xi$ or $\xi' = \xi \circ \sigma$. -/
theorem eq_or_eq_comp_of_tameParam_iso (hconj : ArtinConjCompat F L)
    {art : Lˣ ≃ₜ* WeilGroup.Ab L} (hart : IsLocalArtinMap L art) {ξ ξ' : Lˣ →* ℂˣ}
    (hξ : IsSmoothChar L ξ) (hξ' : IsSmoothChar L ξ')
    (h : (tameParam art ξ hξ).Iso (tameParam art ξ' hξ')) :
    ξ' = ξ ∨ ξ' = ξ.comp (galConjUnits F L) := by
  obtain ⟨g, hg, -⟩ := h
  rcases eq_or_eq_conjChar_of_repIso index_restrictSubgroup_quad outElt_notMem
      (⟨g, hg⟩ : RepIso (tameParam art ξ hξ).r (tameParam art ξ' hξ').r) with h | h
  · exact Or.inl (charW_injective art h)
  · rw [conjChar_charW hconj hart outElt_notMem] at h
    exact Or.inr (charW_injective art h)

/-- **Injectivity on isomorphism classes for a fixed field** (BH 34.1). If $\sigma(L, \xi) \cong \sigma(L, \xi')$, then the pairs $(L, \xi)$ and $(L, \xi')$ are $F$-isomorphic: $\xi = \xi' \circ j$ for an $F$-automorphism $j$ of $L$. -/
theorem exists_algEquiv_of_tameParam_iso (hconj : ArtinConjCompat F L)
    {art : Lˣ ≃ₜ* WeilGroup.Ab L} (hart : IsLocalArtinMap L art) {ξ ξ' : Lˣ →* ℂˣ}
    (hξ : IsSmoothChar L ξ) (hξ' : IsSmoothChar L ξ')
    (h : (tameParam art ξ hξ).Iso (tameParam art ξ' hξ')) :
    ∃ j : L ≃ₐ[F] L, ξ = ξ'.comp (unitsMap j) := by
  rcases eq_or_eq_comp_of_tameParam_iso hconj hart hξ hξ' h with rfl | rfl
  · exact ⟨1, by ext x; rfl⟩
  · refine ⟨galConj F L, ?_⟩
    ext x
    change (ξ x : ℂ) = ξ (unitsMap (galConj F L) (unitsMap (galConj F L) x))
    congr 2
    exact Units.ext (galConj_galConj (x : L)).symm

end Param

end Langlands.LocalGL2
