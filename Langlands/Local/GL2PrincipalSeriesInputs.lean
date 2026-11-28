/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2NonSupercuspidal
import Langlands.Smooth.CuspidalCoefficients

/-!
# Inputs on the principal series of GL(2)

Let $K$ be a nonarchimedean local field. The structure `Langlands.LocalGL2.NonSupercuspidalInputs` of `Langlands/Local/GL2NonSupercuspidal.lean` collects eight published theorems on the irreducible subrepresentations of the principal series $\mathrm{Ind}(\chi_1, \chi_2)$ of $GL_2(K)$. This file proves five of them outright from the results on the normalized principal series in `Langlands/Smooth`. It proves the other three from six smaller published facts, which it states as named hypotheses of type `Prop` with a citation.

The main tool is the socle of the normalized principal series: a nonzero stable subspace $S$ that is contained in each nonzero stable subspace. If $\mathrm{Ind}(\chi_1, \chi_2)$ is irreducible, then $S$ is the whole space. If $\chi_2 = \chi_1 |\cdot|$, then $S$ is the line of $\chi \circ \det$. If $\chi_1 = \chi_2 |\cdot|$, then $S$ is the Steinberg subspace. Each irreducible representation with a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$ is isomorphic to the subrepresentation on $S$.

## Main definitions

* `Langlands.LocalGL2.PSSupercuspidalJacquet`: a supercuspidal representation has zero Jacquet module.
* `Langlands.LocalGL2.PSContragredientIso`: the contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$.
* `Langlands.LocalGL2.SmoothDualExtends`: smooth linear forms extend along injective maps of representations.
* `Langlands.LocalGL2.PSLFactorIrreducible`, `Langlands.LocalGL2.PSLFactorDetChar`, `Langlands.LocalGL2.PSLFactorSteinberg`: the L-factors of an irreducible principal series, of a character $\chi \circ \det$ and of a twisted Steinberg representation.
* `Langlands.LocalGL2.PSInputProps`: the six facts for one field.

## Main results

* `Langlands.LocalGL2.psSubExists`, `Langlands.LocalGL2.psSubUnique`, `Langlands.LocalGL2.psSubRigid`, `Langlands.LocalGL2.psSubSwap`, `Langlands.LocalGL2.psExhaustion`: five of the eight inputs, with no hypothesis.
* `Langlands.LocalGL2.psSubNotSupercuspidal_of`, `Langlands.LocalGL2.psSubContragredient_of`, `Langlands.LocalGL2.psSubLFactor_of`: the other three inputs from the six facts.
* `Langlands.LocalGL2.nonSupercuspidalInputs_of_psInputProps`: the six facts give `Langlands.LocalGL2.NonSupercuspidalInputs`.
* `Langlands.LocalGL2.psIso_sub_of_hasHom`, `Langlands.LocalGL2.psExists_socle`: the socle argument and the socle of the normalized principal series.
* `Langlands.LocalGL2.psEq_of_hasHom_sub`: in the reducible case, the subrepresentation determines the inducing pair.
* `Langlands.LocalGL2.psHasHom_swap_of_surjective`: an irreducible quotient of the principal series of $(\chi_1, \chi_2)$ is in the principal series of $(\chi_2, \chi_1)$.
* `Langlands.LocalGL2.psIsGJLFactor_of_iso`: the Godement-Jacquet L-factor is an invariant of the isomorphism class.

## Still open

* Proofs of the six facts in `Langlands.LocalGL2.PSInputProps`. The fact `Langlands.LocalGL2.PSSupercuspidalJacquet` is the converse of `Langlands.SmoothRep.isSupercuspidal_of_isJacquetCuspidal`. The two facts on the contragredient need the invariant integral over $B \backslash G$ and the projection onto the vectors fixed by a compact open subgroup. The three facts on L-factors need the computation of the zeta integrals of Godement and Jacquet for $GL_2$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, chapter 1, sections 2 and 3, chapter 2, sections 9 and 10, and chapter 6, section 26.
* R. Godement and H. Jacquet, Zeta functions of simple algebras, Lecture Notes in Math. 260.
* H. Jacquet and R. P. Langlands, Automorphic forms on GL(2), Lecture Notes in Math. 114, sections 2 and 3.
-/

namespace Langlands

universe u

open Representation Matrix

namespace LocalGL2

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The relation `HasHom` does not change if the target is replaced by an isomorphic representation. -/
theorem psHasHom_of_iso_right {σ π π' : SmoothRep G} (h : σ.HasHom π) (e : π.Iso π') :
    σ.HasHom π' := by
  obtain ⟨f, hf, hfg⟩ := h
  obtain ⟨e, he⟩ := e
  refine ⟨(e : π.V →ₗ[ℂ] π'.V) ∘ₗ f, fun h0 => hf (LinearMap.ext fun v => e.injective ?_),
    fun g v => ?_⟩
  · simpa using LinearMap.congr_fun h0 v
  · simp [hfg, he]

omit [IsTopologicalGroup G] in
/-- An isomorphism from a nonzero representation is a nonzero map of representations. -/
theorem psHasHom_of_iso {σ π : SmoothRep G} [Nontrivial σ.V] (e : σ.Iso π) : σ.HasHom π := by
  obtain ⟨e, he⟩ := e
  refine ⟨e, fun h0 => ?_, he⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : σ.V)
  exact hv (e.injective (by simpa using LinearMap.congr_fun h0 v))

/-- The inclusion of a nonzero stable subspace is a nonzero map of representations. -/
theorem psHasHom_sub (π : SmoothRep G) {S : Submodule ℂ π.V} (hS : IsStableSubspace π.ρ S)
    (hS0 : S ≠ ⊥) : (π.sub S hS).HasHom π := by
  refine ⟨S.subtype, fun h0 => hS0 ?_, fun _ _ => rfl⟩
  rw [eq_bot_iff]
  intro v hv
  have := LinearMap.congr_fun h0 ⟨v, hv⟩
  exact (Submodule.mem_bot ℂ).2 this

/-- **The socle argument.** Let $S \ne 0$ be a stable subspace of $\pi$ that is contained in each nonzero stable subspace. Then each irreducible representation $\sigma$ with a nonzero map to $\pi$ is isomorphic to the subrepresentation on $S$. The image of $\sigma$ is a nonzero stable subspace, so it contains $S$. The preimage of $S$ is a nonzero stable subspace of $\sigma$, so it is the whole space. -/
theorem psIso_sub_of_hasHom {σ π : SmoothRep G} (hσ : σ.IsIrreducible) {S : Submodule ℂ π.V}
    (hS : IsStableSubspace π.ρ S) (hS0 : S ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ π.V, IsStableSubspace π.ρ W → W ≠ ⊥ → S ≤ W)
    (h : σ.HasHom π) : σ.Iso (π.sub S hS) := by
  obtain ⟨f, hf, hfg⟩ := h
  have hinj := injective_of_isIrreducible hσ hf hfg
  have hR : IsStableSubspace π.ρ (LinearMap.range f) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨σ.ρ g v, hfg g v⟩
  have hSR : S ≤ LinearMap.range f := hmin _ hR fun h0 => hf (LinearMap.range_eq_bot.1 h0)
  have hP : IsStableSubspace σ.ρ (S.comap f) := fun g v hv => by
    show f (σ.ρ g v) ∈ S
    rw [hfg]
    exact hS g hv
  have hRS : ∀ v, f v ∈ S := by
    rcases hσ.2 _ hP with h0 | h0
    · exfalso
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
      obtain ⟨v, rfl⟩ := hSR hs
      have hv : v ∈ S.comap f := hs
      rw [h0, Submodule.mem_bot] at hv
      exact hs0 (by rw [hv, map_zero])
    · intro v
      have hv : v ∈ S.comap f := by rw [h0]; trivial
      exact hv
  refine ⟨LinearEquiv.ofBijective (f.codRestrict S hRS)
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun s => ?_⟩, fun g v => Subtype.ext (hfg g v)⟩
  obtain ⟨v, hv⟩ := hSR s.2
  exact ⟨v, Subtype.ext hv⟩

omit [IsTopologicalGroup G] in
/-- A nonzero map between two irreducible representations gives an isomorphism. -/
theorem psIso_of_hasHom {σ π : SmoothRep G} (hσ : σ.IsIrreducible) (hπ : π.IsIrreducible)
    (h : σ.HasHom π) : σ.Iso π := by
  obtain ⟨f, hf, hfg⟩ := h
  have hR : IsStableSubspace π.ρ (LinearMap.range f) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨σ.ρ g v, hfg g v⟩
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    exact (hπ.2 _ hR).resolve_left fun h0 => hf (LinearMap.range_eq_bot.1 h0)
  exact ⟨LinearEquiv.ofBijective f ⟨injective_of_isIrreducible hσ hf hfg, hsurj⟩, hfg⟩

/-- Let $f : \sigma \to \pi$ be a map of representations. If $\lambda$ is a smooth linear form on $\pi$, then $\lambda \circ f$ is a smooth linear form on $\sigma$, since the stabilizer of $\lambda$ fixes $\lambda \circ f$. -/
theorem psComp_mem_smoothVectors {σ π : SmoothRep G} {f : σ.V →ₗ[ℂ] π.V}
    (hfg : ∀ g v, f (σ.ρ g v) = π.ρ g (f v)) {l : Module.Dual ℂ π.V}
    (hl : l ∈ smoothVectors π.ρ.dual) : l ∘ₗ f ∈ smoothVectors σ.ρ.dual := by
  refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ.dual l) (fun g hg => ?_) hl
  rw [mem_vecStabilizer] at hg ⊢
  ext v
  have := LinearMap.congr_fun hg (f v)
  simp only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] at this ⊢
  rw [hfg, this]

/-- The zeta integrals of Godement and Jacquet do not change under an isomorphism $e : \pi \to \pi'$: the zeta integral of $\pi'$ for $e(v)$ and $\lambda$ is the zeta integral of $\pi$ for $v$ and $\lambda \circ e$. -/
theorem psGjZeta_iso {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} {π π' : SmoothRep (GL (Fin n) K)} (e : π.V ≃ₗ[ℂ] π'.V)
    (he : ∀ g v, e (π.ρ g v) = π'.ρ g (e v)) (Φ : Matrix (Fin n) (Fin n) K → ℂ) (v : π.V)
    (l : Module.Dual ℂ π'.V) (s : ℂ) :
    gjZeta K π' Φ (e v) l s = gjZeta K π Φ v (l ∘ₗ (e : π.V →ₗ[ℂ] π'.V)) s := by
  simp only [gjZeta, SmoothRep.coeff, LinearMap.comp_apply, LinearEquiv.coe_coe, ← he]

/-- **The L-factor is an invariant of the isomorphism class.** If $\pi \cong \pi'$ and $L$ is the Godement-Jacquet L-factor of $\pi$, then $L$ is the Godement-Jacquet L-factor of $\pi'$. -/
theorem psIsGJLFactor_of_iso {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} {π π' : SmoothRep (GL (Fin n) K)} (e : π.Iso π')
    {L : ℂ → ℂ} (h : IsGJLFactor K π L) : IsGJLFactor K π' L := by
  obtain ⟨e, he⟩ := e
  have he' : ∀ g v, e.symm (π'.ρ g v) = π.ρ g (e.symm v) := fun g v => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  obtain ⟨h1, h2, j, Φ, v, l, A, k, s₀, hΦ, hL⟩ := h
  refine ⟨h1, fun Φ' v' l' hΦ' => ?_, j, Φ, fun i => e (v i),
    fun i => ⟨(l i).1 ∘ₗ (e.symm : π'.V →ₗ[ℂ] π.V), psComp_mem_smoothVectors he' (l i).2⟩,
    A, k, s₀, hΦ, fun s hs => ?_⟩
  · obtain ⟨A, k, s₀, hA⟩ := h2 Φ' (e.symm v')
      ⟨l'.1 ∘ₗ (e : π.V →ₗ[ℂ] π'.V), psComp_mem_smoothVectors he l'.2⟩ hΦ'
    refine ⟨A, k, s₀, fun s hs => ?_⟩
    rw [← hA s hs]
    have := psGjZeta_iso e he Φ' (e.symm v') l'.1 s
    rwa [LinearEquiv.apply_symm_apply] at this
  · rw [hL s hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [psGjZeta_iso e he]
    congr 2
    ext w
    simp

end General

section Socle

open LocalGL1 GL2 SmoothRep

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The Steinberg condition `IsSt K χ₁ χ₂` is the equation $\chi_1 = \chi_2 |\cdot|$ of characters. -/
theorem psIsSt_iff {χ₁ χ₂ : Kˣ →* ℂˣ} : IsSt K χ₁ χ₂ ↔ χ₁ = χ₂ * absChar K := by
  constructor
  · intro h
    ext x
    rw [MonoidHom.mul_apply, Units.val_mul, absChar_apply]
    exact h x
  · rintro rfl x
    rw [MonoidHom.mul_apply, Units.val_mul, absChar_apply]

/-- The group acts on each vector of the line `Langlands.detLine` by the character $\chi \circ \det$. -/
theorem psρ_of_mem_detLine {θ : GL2.borel K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (GL2.borel K))}
    {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hθχ : ∀ b : GL2.borel K, θ b = detChar K 2 χ b)
    {v : (SmoothRep.ind (GL2.borel K) (charRep θ hθ)).V} (hv : v ∈ detLine θ hθ hχ hθχ) (g : GL (Fin 2) K) :
    (SmoothRep.ind (GL2.borel K) (charRep θ hθ)).ρ g v = (detChar K 2 χ g : ℂ) • v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [map_smul, ρ_detVec, smul_comm]

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- The character $\gamma = \chi_1 |\cdot|^{1/2} \otimes \chi_2 |\cdot|^{-1/2}$ of the diagonal torus, by which the torus acts on the Jacquet module of the subrepresentation in the reducible case. -/
noncomputable abbrev psGamma (χ₁ χ₂ : Kˣ →* ℂˣ) : torus K →* ℂˣ :=
  torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹)

variable (hχ₁ hχ₂) in
/-- **The socle of the principal series** (Bushnell and Henniart, Chapter 2, Section 9). The normalized principal series of $(\chi_1, \chi_2)$ has a nonzero stable subspace $S$ that is contained in each nonzero stable subspace. Either the principal series is irreducible, or $S$ is contained in the subspace of vectors on which the torus acts on the Jacquet module by $\gamma$. -/
theorem psExists_socle : ∃ (S : Submodule ℂ (Π).V) (_ : IsStableSubspace (Π).ρ S), S ≠ ⊥ ∧
    (∀ W : Submodule ℂ (Π).V, IsStableSubspace (Π).ρ W → W ≠ ⊥ → S ≤ W) ∧
    ((Π).IsIrreducible ∨ S ≤ jacquetEigenSub (Π) (psGamma χ₁ χ₂)) := by
  by_cases h₁ : χ₁ = χ₂ * absChar K
  · exact ⟨_, normSteinbergSub_stable h₁, normSteinbergSub_ne_bot h₁,
      fun _ hW h0 => normSteinbergSub_le_of_ne_bot h₁ hW h0, Or.inr le_rfl⟩
  by_cases h₂ : χ₂ = χ₁ * absChar K
  · have hD := (normPrincipalSeries_isStableSubspace_iff (hχ₁ := hχ₁) (hχ₂ := hχ₂) h₂ _).2
      (Or.inr (Or.inl rfl))
    refine ⟨_, hD, detLine_ne_bot _ _, fun W hW h0 => ?_, Or.inr ?_⟩
    · rcases (normPrincipalSeries_isStableSubspace_iff h₂ W).1 hW with h | h | h
      · exact absurd h h0
      · exact h.ge
      · rw [h]
        exact le_top
    · intro v hv t
      have h3 := psρ_of_mem_detLine (hχ₁.mul isSmoothChar_sqrtAbsChar)
        (borelChar_mul_sqrtModulus_eq_detChar h₂) hv (t : GL (Fin 2) K)
      have e : (psGamma χ₁ χ₂ t : ℂ) =
          (detChar K 2 (χ₁ * sqrtAbsChar K) (t : GL (Fin 2) K) : ℂ) := by
        rw [psGamma, torusChar, MonoidHom.comp_apply, ← borelChar_mul_sqrtModulus,
          borelChar_mul_sqrtModulus_eq_detChar h₂]
        rfl
      rw [show (Π).ρ (t : GL (Fin 2) K) v = _ from h3, e]
      convert ((Π).jacquetKer (unipotent K)).zero_mem using 1
      exact sub_self _
  · have hirr := normPrincipalSeries_irreducible (hχ₁ := hχ₁) (hχ₂ := hχ₂) h₁ h₂
    have := hirr.1
    exact ⟨⊤, fun _ _ _ => trivial, top_ne_bot,
      fun W hW h0 => ((hirr.2 W hW).resolve_left h0).ge, Or.inl hirr⟩

/-- If an irreducible representation has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then it is isomorphic to the subrepresentation of the normalized principal series on each socle $S$. -/
theorem psIso_socle (π : IrrRep (GL (Fin 2) K)) (h : π.1.HasHom (principalSeries K χ₁ χ₂))
    {S : Submodule ℂ (Π).V} (hS : IsStableSubspace (Π).ρ S) (hS0 : S ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ (Π).V, IsStableSubspace (Π).ρ W → W ≠ ⊥ → S ≤ W) :
    π.1.Iso ((Π).sub S hS) :=
  psIso_sub_of_hasHom π.2.1 hS hS0 hmin
    (psHasHom_of_iso_right h (normPrincipalSeries_iso hχ₁ hχ₂).symm)

/-- **The torus action on the Jacquet module of the socle** (Bushnell and Henniart, Chapter 2, Section 9). Let $S$ be a stable subspace of the normalized principal series of $(\chi_1, \chi_2)$, on which the torus acts on the Jacquet module by $\gamma = \chi_1 |\cdot|^{1/2} \otimes \chi_2 |\cdot|^{-1/2}$. If the subrepresentation on $S$ has a nonzero map to the normalized principal series of $(\psi_1, \psi_2)$, then $(\psi_1, \psi_2) = (\chi_1, \chi_2)$. The proof uses Frobenius reciprocity and the exactness of the Jacquet functor. -/
theorem psEq_of_hasHom_sub {S : Submodule ℂ (Π).V} (hS : IsStableSubspace (Π).ρ S)
    (hSγ : S ≤ jacquetEigenSub (Π) (psGamma χ₁ χ₂)) {ψ₁ ψ₂ : Kˣ →* ℂˣ}
    (hψ₁ : IsSmoothChar K ψ₁) (hψ₂ : IsSmoothChar K ψ₂)
    (h : ((Π).sub S hS).HasHom (normPrincipalSeries ψ₁ ψ₂ hψ₁ hψ₂)) : ψ₁ = χ₁ ∧ ψ₂ = χ₂ := by
  set σ := (Π).sub S hS
  rw [normPrincipalSeries_eq hψ₁ hψ₂] at h
  obtain ⟨f, hf, hfg⟩ := h
  set Φ := f.intertwiningMap_of_isIntertwiningMap σ.ρ _ hfg
  have hΦ : Φ ≠ 0 := fun h0 => hf (LinearMap.ext fun v => congrArg (fun F => F v) h0)
  set φ := σ.jacquetFrobenius (hψ₁.mul isSmoothChar_sqrtAbsChar)
    (hψ₂.mul isSmoothChar_sqrtAbsChar.inv) Φ
  have hφ : φ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hΦ
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ (IntertwiningMap.ext (LinearMap.ext hc))
  obtain ⟨v, rfl⟩ := σ.jacquetMk_surjective _ _ torus_le_normalizer_unipotent x
  have hv : ∀ t : torus K, σ.jacquetMk _ _ torus_le_normalizer_unipotent (σ.ρ t v) =
      (psGamma χ₁ χ₂ t : ℂ) • σ.jacquetMk _ _ torus_le_normalizer_unipotent v := by
    intro t
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    apply jacquetMap_unipotent_injective torus_le_normalizer_unipotent ((Π).subIncl S hS)
      Subtype.val_injective
    rw [jacquetMap_mk, map_zero, jacquetMk_eq_zero_iff]
    exact hSγ v.2 t
  have hx0 : (φ (σ.jacquetMk _ _ torus_le_normalizer_unipotent v)).down ≠ 0 := fun h0 =>
    hx (ULift.ext h0)
  have key : torusChar (ψ₁ * sqrtAbsChar K) (ψ₂ * (sqrtAbsChar K)⁻¹) = psGamma χ₁ χ₂ := by
    ext t
    have h1 := IntertwiningMap.isIntertwining _ _ φ t
      (σ.jacquetMk _ _ torus_le_normalizer_unipotent v)
    rw [← jacquetMk_ρ, hv, map_smul] at h1
    have h2 := congrArg ULift.down h1
    exact (mul_right_cancel₀ hx0 h2).symm
  obtain ⟨e₁, e₂⟩ := torusChar_inj.1 key
  exact ⟨mul_right_cancel e₁, mul_right_cancel e₂⟩

/-- **A quotient of the principal series is in the swapped principal series** (Bushnell and Henniart, Chapter 2, Section 9). If an irreducible representation $\pi'$ is a quotient of the normalized principal series of $(\chi_1, \chi_2)$, then $\pi'$ has a nonzero map to the normalized principal series of $(\chi_2, \chi_1)$. If the kernel is $0$, then the principal series is irreducible and isomorphic to the swapped one. Otherwise Frobenius reciprocity gives a nonzero map to the swapped principal series that vanishes on the kernel. -/
theorem psHasHom_swap_of_surjective {π' : SmoothRep (GL (Fin 2) K)} (hπ' : π'.IsIrreducible)
    (q : IntertwiningMap (Π).ρ π'.ρ) (hq : Function.Surjective q) :
    π'.HasHom (normPrincipalSeries χ₂ χ₁ hχ₂ hχ₁) := by
  have := hπ'.1
  have hW : IsStableSubspace (Π).ρ (LinearMap.ker q.toLinearMap) := fun g v hv => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, IntertwiningMap.toLinearMap_apply,
      IntertwiningMap.isIntertwining, ← IntertwiningMap.toLinearMap_apply, LinearMap.mem_ker.1 hv,
      map_zero]
  by_cases hW0 : LinearMap.ker q.toLinearMap = ⊥
  · have e := iso_of_bijective q ⟨LinearMap.ker_eq_bot.1 hW0, hq⟩
    have hirr := hπ'.of_iso e.symm
    exact psHasHom_of_iso (e.symm.trans ((normPrincipalSeries_iso_iff hirr).2 (Or.inr ⟨rfl, rfl⟩)))
  have hWt : LinearMap.ker q.toLinearMap ≠ ⊤ := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : π'.V)
    obtain ⟨x, rfl⟩ := hq y
    exact hy (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top (x := x)))
  obtain ⟨Φ, hΦ, hΦW⟩ := normPrincipalSeries_exists_hom_of_quotient hW hW0
    (normPrincipalSeries_quotient_jacquet_nontrivial hW hWt)
  have hΦW' : LinearMap.ker q.toLinearMap ≤ LinearMap.ker Φ.toLinearMap := fun x hx => hΦW x hx
  let E := q.toLinearMap.quotKerEquivOfSurjective hq
  let F : π'.V →ₗ[ℂ] (normPrincipalSeries χ₂ χ₁ hχ₂ hχ₁).V :=
    (LinearMap.ker q.toLinearMap).liftQ Φ.toLinearMap hΦW' ∘ₗ E.symm.toLinearMap
  have hF : ∀ x, F (q x) = Φ x := by
    intro x
    have : E.symm (q x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply,
      IntertwiningMap.toLinearMap_apply]
  refine ⟨F, fun h0 => hΦ (IntertwiningMap.ext (LinearMap.ext fun x => ?_)), fun g y => ?_⟩
  · rw [IntertwiningMap.toLinearMap_apply, ← hF, h0]
    rfl
  · obtain ⟨x, rfl⟩ := hq y
    rw [← IntertwiningMap.isIntertwining _ _ q g x, hF, hF, IntertwiningMap.isIntertwining _ _ Φ g x]

end Socle

section Proved

open LocalGL1 GL2 SmoothRep

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Existence of an irreducible subrepresentation** (Bushnell and Henniart, Chapter 2, Section 9). The subrepresentation of the normalized principal series on its socle is irreducible and admissible, and it has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$. -/
theorem psSubExists : PSSubExists K := by
  intro χ₁ χ₂ hχ₁ hχ₂
  obtain ⟨S, hS, hS0, hmin, -⟩ := psExists_socle hχ₁ hχ₂
  exact ⟨⟨_, (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).sub_isIrreducible_of_le hS hS0 hmin,
    (normPrincipalSeries_isAdmissible hχ₁ hχ₂).sub S hS⟩,
    psHasHom_of_iso_right (psHasHom_sub _ hS hS0) (normPrincipalSeries_iso hχ₁ hχ₂)⟩

/-- **Uniqueness of the irreducible subrepresentation** (Bushnell and Henniart, Chapter 2, Section 9). Both representations are isomorphic to the subrepresentation on the socle. -/
theorem psSubUnique : PSSubUnique K := by
  intro χ₁ χ₂ hχ₁ hχ₂ π π' h h'
  obtain ⟨S, hS, hS0, hmin, -⟩ := psExists_socle hχ₁ hχ₂
  exact (psIso_socle π h hS hS0 hmin).trans (psIso_socle π' h' hS hS0 hmin).symm

/-- **The swap of an irreducible principal series** (Bushnell and Henniart, Chapter 2, Section 9). -/
theorem psSubSwap : PSSubSwap K := by
  intro χ₁ χ₂ hχ₁ hχ₂ h₁ h₂ π h
  have hirr := normPrincipalSeries_irreducible (hχ₁ := hχ₁) (hχ₂ := hχ₂)
    (fun e => h₁ (psIsSt_iff.2 e)) (fun e => h₂ (psIsSt_iff.2 e))
  have e := (normPrincipalSeries_iso_iff (hχ₁' := hχ₂) (hχ₂' := hχ₁) hirr).2 (Or.inr ⟨rfl, rfl⟩)
  exact psHasHom_of_iso_right (psHasHom_of_iso_right
    (psHasHom_of_iso_right h (normPrincipalSeries_iso hχ₁ hχ₂).symm) e)
    (normPrincipalSeries_iso hχ₂ hχ₁)

/-- **The inducing pair is unique up to the swap** (Bushnell and Henniart, Chapter 2, Section 9). In the irreducible case a nonzero map between two normalized principal series forces the pairs to be equal or swapped. In the reducible case the torus acts on the Jacquet module of the subrepresentation by one character, and Frobenius reciprocity fixes the pair. -/
theorem psSubRigid : PSSubRigid K := by
  intro χ₁ χ₂ ψ₁ ψ₂ hχ₁ hχ₂ hψ₁ hψ₂ π h h'
  obtain ⟨S, hS, hS0, hmin, hcase⟩ := psExists_socle hχ₁ hχ₂
  have h'' := psHasHom_of_iso_right h' (normPrincipalSeries_iso hψ₁ hψ₂).symm
  rcases hcase with hirr | hSγ
  · have hσ : (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).HasHom (normPrincipalSeries ψ₁ ψ₂ hψ₁ hψ₂) :=
      hasHom_of_iso (psIso_of_hasHom π.2.1 hirr
        (psHasHom_of_iso_right h (normPrincipalSeries_iso hχ₁ hχ₂).symm)).symm h''
    obtain ⟨f, hf, hfg⟩ := hσ
    rcases normPrincipalSeries_hom_eq (f.intertwiningMap_of_isIntertwiningMap _ _ hfg)
      (fun h0 => hf (LinearMap.ext fun v => congrArg (fun F => F v) h0)) with h | ⟨e₁, e₂⟩
    · exact Or.inl h
    · rw [normPrincipalSeries_isIrreducible_iff] at hirr
      exact Or.inr ⟨e₁, e₂, fun e => hirr.1 (psIsSt_iff.1 e), fun e => hirr.2 (psIsSt_iff.1 e)⟩
  · exact Or.inl (psEq_of_hasHom_sub hS hSγ hψ₁ hψ₂
      (hasHom_of_iso (psIso_socle π h hS hS0 hmin).symm h''))

/-- **Each representation that is not supercuspidal is in a principal series** (Bushnell and Henniart, Chapter 2, Sections 9 and 10). A representation that is not supercuspidal is not Jacquet cuspidal. Then the classification of the irreducible admissible representations with nonzero Jacquet module gives an irreducible principal series, a character $\chi \circ \det$ or a twisted Steinberg representation, and each of them is in a principal series. -/
theorem psExhaustion : NonSupercuspidalExhaustion K := by
  intro π hsc
  have hc : ¬π.1.IsJacquetCuspidal := fun hc => hsc (isSupercuspidal_of_isJacquetCuspidal π.1 hc)
  have := π.2.1.1
  rcases classification_of_isAdmissible π.1 π.2.1 π.2.2 hc with
    ⟨χ₁, χ₂, hχ₁, hχ₂, -, e⟩ | ⟨χ, hχ, e⟩ | ⟨χ₁, χ₂, hχ₁, hχ₂, h, e⟩
  · exact ⟨χ₁, χ₂, hχ₁, hχ₂, psHasHom_of_iso (e.trans (normPrincipalSeries_iso hχ₁ hχ₂))⟩
  · obtain ⟨χ₁, rfl⟩ : ∃ χ₁, χ₁ * sqrtAbsChar K = χ :=
      ⟨χ * (sqrtAbsChar K)⁻¹, by ext x; simp⟩
    have hχ₁ : IsSmoothChar K χ₁ := by
      have e : χ₁ * sqrtAbsChar K * (sqrtAbsChar K)⁻¹ = χ₁ := by ext x; simp
      have := hχ.mul isSmoothChar_sqrtAbsChar.inv
      rwa [e] at this
    have hχ₂ := hχ₁.mul isSmoothChar_absChar
    refine ⟨χ₁, χ₁ * absChar K, hχ₁, hχ₂, hasHom_of_iso e ?_⟩
    exact psHasHom_of_iso_right (normPrincipalSeries_hasHom_detChar (hχ₂ := hχ₂) rfl)
      (normPrincipalSeries_iso hχ₁ hχ₂)
  · exact ⟨χ₁, χ₂, hχ₁, hχ₂, hasHom_of_iso e (psHasHom_of_iso_right
      (psHasHom_sub _ _ (normSteinbergSub_ne_bot h)) (normPrincipalSeries_iso hχ₁ hχ₂))⟩

end Proved

section Props

open LocalGL1 GL2 SmoothRep

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Supercuspidal representations have zero Jacquet module** (Bushnell and Henniart, Chapter 2, Section 10, the characterization of cuspidal representations by their coefficients; Jacquet and Langlands, LNM 114, Section 2). If the matrix coefficients of an irreducible admissible representation $\pi$ of $GL_2(K)$ have compact support modulo the center, then the Jacquet module $\pi_N$ is $0$. The converse is `Langlands.SmoothRep.isSupercuspidal_of_isJacquetCuspidal`. -/
def PSSupercuspidalJacquet : Prop :=
  ∀ π : IrrRep (GL (Fin 2) K), π.1.IsSupercuspidal (scalarGL K 2) → π.1.IsJacquetCuspidal

/-- **The contragredient of the principal series** (Bushnell and Henniart, Chapter 1, Section 3.5, duality for induced representations, and Chapter 2, Section 9). The contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is isomorphic to $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$. The pairing is the integral of $f f'$ over $B \backslash G$, which exists for the normalized induction. -/
def PSContragredientIso : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    (principalSeries K χ₁ χ₂).contragredient.Iso (principalSeries K χ₁⁻¹ χ₂⁻¹)

/-- **Smooth linear forms extend** (Bushnell and Henniart, Chapter 1, Section 2.10, the exactness of the contragredient). Let $f : \sigma \to \pi$ be an injective map of smooth representations of $GL_2(K)$. Then each smooth linear form on $\sigma$ is $\lambda \circ f$ for a smooth linear form $\lambda$ on $\pi$. The proof uses the projection of $V$ onto $V^U$ for a compact open subgroup $U$. -/
def SmoothDualExtends : Prop :=
  ∀ (σ π : SmoothRep (GL (Fin 2) K)) (f : σ.V →ₗ[ℂ] π.V), Function.Injective f →
    (∀ g v, f (σ.ρ g v) = π.ρ g (f v)) →
      ∀ l ∈ smoothVectors σ.ρ.dual, ∃ l' ∈ smoothVectors π.ρ.dual, l' ∘ₗ f = l

/-- **The L-factor of an irreducible principal series** (Bushnell and Henniart, Chapter 6, Section 26; Godement and Jacquet, LNM 260, Theorem 3.3; Jacquet and Langlands, LNM 114, Section 3). If $\chi_1 \chi_2^{-1} \ne |\cdot|^{\pm 1}$, then $L(s, \mathrm{Ind}(\chi_1, \chi_2)) = L(s, \chi_1) L(s, \chi_2)$. -/
def PSLFactorIrreducible : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ → ¬IsSt K χ₁ χ₂ → ¬IsSt K χ₂ χ₁ →
    IsGJLFactor K (principalSeries K χ₁ χ₂) fun s =>
      charLFactor K (unif K) χ₁ s * charLFactor K (unif K) χ₂ s

/-- **The L-factor of a character of $GL_2(K)$** (Bushnell and Henniart, Chapter 6, Section 26; Godement and Jacquet, LNM 260, Theorem 3.3; Jacquet and Langlands, LNM 114, Section 3). For a smooth character $\chi$ and $\chi' = \chi |\cdot|^{1/2}$, the L-factor of the representation $\chi' \circ \det$ is $L(s, \chi) L(s, \chi |\cdot|)$. -/
def PSLFactorDetChar : Prop :=
  ∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
    IsGJLFactor K (charRep (detChar K 2 (χ * sqrtAbsChar K))
      (isOpen_ker_detChar K 2 _ (hχ.mul isSmoothChar_sqrtAbsChar))) fun s =>
        charLFactor K (unif K) χ s * charLFactor K (unif K) (χ * absChar K) s

/-- **The L-factor of a twisted Steinberg representation** (Bushnell and Henniart, Chapter 6, Section 26; Godement and Jacquet, LNM 260, Theorem 3.3; Jacquet and Langlands, LNM 114, Section 3). If $\chi_1 = \chi_2 |\cdot|$, then the L-factor of the irreducible subrepresentation `Langlands.steinbergSub` of the principal series is $L(s, \chi_1)$. -/
def PSLFactorSteinberg : Prop :=
  ∀ (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂)
    (h : χ₁ = χ₂ * absChar K),
    IsGJLFactor K (steinbergSub χ₁ χ₂ hχ₁ hχ₂ h) fun s => charLFactor K (unif K) χ₁ s

/-- The published facts that remain open for the eight inputs on the principal series of $GL_2(K)$. -/
structure PSInputProps : Prop where
  /-- Supercuspidal representations have zero Jacquet module. -/
  supercuspidalJacquet : PSSupercuspidalJacquet K
  /-- The contragredient of the principal series. -/
  contragredientIso : PSContragredientIso K
  /-- Smooth linear forms extend along injective maps. -/
  dualExtends : SmoothDualExtends K
  /-- The L-factor of an irreducible principal series. -/
  lFactorIrreducible : PSLFactorIrreducible K
  /-- The L-factor of a character $\chi \circ \det$. -/
  lFactorDetChar : PSLFactorDetChar K
  /-- The L-factor of a twisted Steinberg representation. -/
  lFactorSteinberg : PSLFactorSteinberg K

variable {K}

/-- **A subrepresentation of the principal series is not supercuspidal**, from `Langlands.LocalGL2.PSSupercuspidalJacquet`. A nonzero map to the principal series gives a nonzero map from the Jacquet module to a character by Frobenius reciprocity, so the Jacquet module is not $0$. -/
theorem psSubNotSupercuspidal_of (hJ : PSSupercuspidalJacquet K) : PSSubNotSupercuspidal K := by
  intro χ₁ χ₂ hχ₁ hχ₂ π h hsc
  have : Subsingleton (π.1.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V :=
    hJ π hsc
  have h' := psHasHom_of_iso_right h (normPrincipalSeries_iso hχ₁ hχ₂).symm
  rw [normPrincipalSeries_eq hχ₁ hχ₂] at h'
  obtain ⟨f, hf, hfg⟩ := h'
  have hΦ : f.intertwiningMap_of_isIntertwiningMap _ _ hfg ≠ 0 := fun h0 =>
    hf (LinearMap.ext fun v => congrArg (fun F => F v) h0)
  refine (LinearEquiv.map_ne_zero_iff (π.1.jacquetFrobenius _ _)).2 hΦ
    (IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **The contragredient of a subrepresentation of the principal series**, from `Langlands.LocalGL2.PSContragredientIso` and `Langlands.LocalGL2.SmoothDualExtends`. Restriction of linear forms makes $\pi^\vee$ a quotient of $\mathrm{Ind}(\chi_1, \chi_2)^\vee \cong \mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$, and a quotient of $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$ is in $\mathrm{Ind}(\chi_2^{-1}, \chi_1^{-1})$. -/
theorem psSubContragredient_of (hD : PSContragredientIso K) (hE : SmoothDualExtends K) :
    PSSubContragredient K := by
  intro χ₁ χ₂ hχ₁ hχ₂ π π' h e'
  obtain ⟨f, hf, hfg⟩ := h
  have hinj := injective_of_isIrreducible π.2.1 hf hfg
  let r : (principalSeries K χ₁ χ₂).contragredient.V →ₗ[ℂ] π.1.contragredient.V :=
    { toFun := fun l => ⟨l.1 ∘ₗ f, psComp_mem_smoothVectors hfg l.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : ∀ g l, r ((principalSeries K χ₁ χ₂).contragredient.ρ g l) =
      π.1.contragredient.ρ g (r l) := by
    intro g l
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    change l.1 ((principalSeries K χ₁ χ₂).ρ g⁻¹ (f v)) = l.1 (f (π.1.ρ g⁻¹ v))
    rw [hfg]
  have hrs : Function.Surjective r := by
    intro l
    obtain ⟨l', hl', e⟩ := hE π.1 _ f hinj hfg l.1 l.2
    exact ⟨⟨l', hl'⟩, Subtype.ext e⟩
  obtain ⟨A, hA⟩ := ((normPrincipalSeries_iso hχ₁.inv hχ₂.inv).trans
    (hD χ₁ χ₂ hχ₁ hχ₂).symm).exists_bijective
  obtain ⟨B, hB⟩ := e'.symm.exists_bijective
  let q := (B.toLinearMap ∘ₗ r ∘ₗ A.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _
    fun g v => by
      simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply]
      rw [IntertwiningMap.isIntertwining _ _ A, hr, IntertwiningMap.isIntertwining _ _ B]
  have hq : Function.Surjective q := hB.2.comp (hrs.comp hA.2)
  exact psHasHom_of_iso_right (psHasHom_swap_of_surjective π'.2.1 q hq)
    (normPrincipalSeries_iso hχ₂.inv hχ₁.inv)

/-- **The L-factor of a subrepresentation of the principal series**, from `Langlands.LocalGL2.PSLFactorIrreducible`, `Langlands.LocalGL2.PSLFactorDetChar` and `Langlands.LocalGL2.PSLFactorSteinberg`. The representation is isomorphic to the twisted Steinberg representation, to a character $\chi \circ \det$, or to the irreducible principal series, and the L-factor is an invariant of the isomorphism class. -/
theorem psSubLFactor_of (h1 : PSLFactorIrreducible K) (h2 : PSLFactorDetChar K)
    (h3 : PSLFactorSteinberg K) : PSSubLFactor K := by
  intro χ₁ χ₂ hχ₁ hχ₂ π h
  by_cases e₁ : χ₁ = χ₂ * absChar K
  · have hπ : π.1.Iso (steinbergSub χ₁ χ₂ hχ₁ hχ₂ e₁) :=
      psIso_socle π h (normSteinbergSub_stable e₁) (normSteinbergSub_ne_bot e₁)
        fun _ hW h0 => normSteinbergSub_le_of_ne_bot e₁ hW h0
    simp only [show IsSt K χ₁ χ₂ from psIsSt_iff.2 e₁, ↓reduceIte, mul_one]
    exact psIsGJLFactor_of_iso hπ.symm (h3 χ₁ χ₂ hχ₁ hχ₂ e₁)
  simp only [show ¬IsSt K χ₁ χ₂ from fun e => e₁ (psIsSt_iff.1 e), ↓reduceIte]
  by_cases e₂ : χ₂ = χ₁ * absChar K
  · subst e₂
    have hc := charRep_isIrreducible (detChar K 2 (χ₁ * sqrtAbsChar K))
      (isOpen_ker_detChar K 2 _ (hχ₁.mul isSmoothChar_sqrtAbsChar))
    have hπ := psSubUnique K χ₁ _ hχ₁ hχ₂ π ⟨_, hc⟩ h (psHasHom_of_iso_right
      (normPrincipalSeries_hasHom_detChar (hχ₂ := hχ₂) rfl) (normPrincipalSeries_iso hχ₁ hχ₂))
    exact psIsGJLFactor_of_iso hπ.symm (h2 χ₁ hχ₁)
  have hirr := (normPrincipalSeries_irreducible (hχ₁ := hχ₁) (hχ₂ := hχ₂) e₁ e₂).of_iso
    (normPrincipalSeries_iso hχ₁ hχ₂)
  exact psIsGJLFactor_of_iso (psIso_of_hasHom π.2.1 hirr h).symm
    (h1 χ₁ χ₂ hχ₁ hχ₂ (fun e => e₁ (psIsSt_iff.1 e)) fun e => e₂ (psIsSt_iff.1 e))

/-- **The eight inputs on the principal series** from the published facts in `Langlands.LocalGL2.PSInputProps`. Five of the eight inputs are proved outright: `Langlands.LocalGL2.psSubExists`, `Langlands.LocalGL2.psSubUnique`, `Langlands.LocalGL2.psSubRigid`, `Langlands.LocalGL2.psSubSwap` and `Langlands.LocalGL2.psExhaustion`. -/
theorem nonSupercuspidalInputs_of_psInputProps (h : PSInputProps K) : NonSupercuspidalInputs K where
  subExists := psSubExists K
  subUnique := psSubUnique K
  subRigid := psSubRigid K
  subSwap := psSubSwap K
  exhaustion := psExhaustion K
  notSupercuspidal := psSubNotSupercuspidal_of h.supercuspidalJacquet
  contragredient := psSubContragredient_of h.contragredientIso h.dualExtends
  lFactor := psSubLFactor_of h.lFactorIrreducible h.lFactorDetChar h.lFactorSteinberg

end Props

end LocalGL2

end Langlands
