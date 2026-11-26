/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.LengthTwo
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Classification of the non-cuspidal irreducible representations of $GL_2$

Let $K$ be a nonarchimedean local field and $G = GL_2(K)$, with Borel subgroup $B$, upper unipotent subgroup $N$ and diagonal torus $T$. Let $\pi$ be an irreducible smooth representation of $G$ whose Jacquet module $\pi_N$ is not zero. This file shows, in the style of Bernstein and Zelevinsky, that $\pi$ is a subrepresentation of a principal series, and that $\pi$ is isomorphic to an irreducible principal series, to a character $\chi \circ \det$, or to a twisted Steinberg representation. It also shows that two irreducible normalized principal series are isomorphic if and only if their pairs of characters agree up to order.

The file assumes that $\pi_N$ has finite dimension. This is a hypothesis of each main result. For an irreducible smooth representation it is a theorem (Jacquet), but its proof needs admissibility, which is not in this repository.

## Main definitions

* `Langlands.SmoothRep.charHom`: the map of representations to a character given by a linear form that is an eigenvector of each transpose.
* `Langlands.GL2.diagTorusHom`: the isomorphism $K^\times \times K^\times \to T$ as a group homomorphism.
* `Langlands.SmoothRep.IsJacquetCuspidal`: the Jacquet module $\pi_N$ is zero.

## Main results

* `Langlands.SmoothRep.exists_dual_char`: a smooth representation of a commutative group on a nonzero space of finite dimension has a quotient that is a smooth character.
* `Langlands.GL2.exists_torusChar_eq`: each smooth character of $T$ is $\alpha_1 \otimes \alpha_2$ for smooth characters $\alpha_1, \alpha_2$ of $K^\times$.
* `Langlands.exists_injective_principalSeriesInd`: if $\pi$ is irreducible and $\pi_N$ is not zero and has finite dimension, there is an injective map of representations $\pi \to \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$.
* `Langlands.classification_principalSeriesInd`: the same $\pi$ is isomorphic to the irreducible $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$, or $\alpha_1 = \alpha_2$ and $\pi \cong \alpha_1 \circ \det$, or $\alpha_1 = \alpha_2 |\cdot|^2$ and $\pi$ is isomorphic to the subrepresentation $W_0$ of `Langlands.jacquetEigenSub`.
* `Langlands.classification`: the same $\pi$ is isomorphic to an irreducible normalized principal series, to a character $\chi \circ \det$, or to `Langlands.steinbergSub` of $(\chi_1, \chi_2)$ with $\chi_1 = \chi_2 |\cdot|$.
* `Langlands.isJacquetCuspidal_or_classification`: an irreducible $\pi$ with $\pi_N$ of finite dimension is Jacquet cuspidal or is one of the representations of `Langlands.classification`.
* `Langlands.normPrincipalSeries_iso_iff`: if $\pi(\chi_1, \chi_2)$ is irreducible, then $\pi(\chi_1, \chi_2) \cong \pi(\chi_1', \chi_2')$ if and only if $(\chi_1', \chi_2')$ is $(\chi_1, \chi_2)$ or $(\chi_2, \chi_1)$.

## Method

The torus $T$ is commutative and acts on $\pi_N$, which has finite dimension. The transposes of the action on the dual space commute, so they have a common eigenvector $l$ in a minimal nonzero invariant subspace. Then $l$ is a map of $T$-representations from $\pi_N$ to a character $\theta$ of $T$, and $\theta$ is smooth since $l(t v) = l(v)$ for each $t$ that fixes a vector $v$ with $l(v) \neq 0$. Thus $\theta = \alpha_1 \otimes \alpha_2$. Frobenius reciprocity `Langlands.SmoothRep.jacquetFrobenius` gives a nonzero map $\pi \to \Psi = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$, which is injective since $\pi$ is irreducible. Its image $W$ is a nonzero stable subspace of $\Psi$. If $W = \Psi$, then $\Psi$ is irreducible and $\pi \cong \Psi$. If not, $\Psi$ is not irreducible, so by `Langlands.principalSeriesInd_isIrreducible` either $\alpha_1 = \alpha_2$ or $\alpha_1 = \alpha_2 |\cdot|^2$. In the first case $W$ is the line of $\alpha_1 \circ \det$ by `Langlands.stable_eq_selfDetLine`. In the second case $W = W_0$ by `Langlands.stable_eq_jacquetEigenSub`. The normalized form follows with $\chi_1 = \alpha_1 |\cdot|^{-1/2}$ and $\chi_2 = \alpha_2 |\cdot|^{1/2}$. For the isomorphism classes, a nonzero map between two normalized principal series forces the pairs to agree up to order by `Langlands.normPrincipalSeries_hom_eq`, and `Langlands.principalSeriesInd_exists_bijective_of_isIrreducible` gives $\pi(\chi_1, \chi_2) \cong \pi(\chi_2, \chi_1)$ when $\chi_1 \neq \chi_2$.

## Open parts

* The finite dimension of $\pi_N$ is a hypothesis, not a theorem.
* The file does not prove that `Langlands.SmoothRep.IsJacquetCuspidal` agrees with `Langlands.SmoothRep.IsSupercuspidal`, which uses matrix coefficients.
* The file does not prove that `Langlands.steinbergSub` is isomorphic to `Langlands.steinbergQuotient`.
* The file does not prove that the three families of `Langlands.classification` are pairwise not isomorphic, or that two twisted Steinberg representations are isomorphic only for equal characters.

## References

* I. N. Bernstein, A. V. Zelevinsky, *Induced representations of reductive p-adic groups. I*, Ann. Sci. École Norm. Sup. 10 (1977).
* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 2, sections 9 and 10.
-/

universe u

open Representation Matrix

namespace Langlands

section Eigen

variable {T : Type u} [Group T] [TopologicalSpace T]

namespace SmoothRep

/-- A smooth representation of a commutative group on a nonzero space of finite dimension has a nonzero linear form $l$ that is an eigenvector of each transpose: for each $t$ there is $c$ with $l(\sigma(t) v) = c \, l(v)$ for each $v$. -/
theorem exists_dual_eigen (σ : SmoothRep T) (hcomm : ∀ s t : T, s * t = t * s)
    [FiniteDimensional ℂ σ.V] [Nontrivial σ.V] :
    ∃ l : Module.Dual ℂ σ.V, l ≠ 0 ∧ ∀ t : T, ∃ c : ℂ, ∀ v, l (σ.ρ t v) = c * l v := by
  let A : T → Module.End ℂ (Module.Dual ℂ σ.V) := fun t => (σ.ρ t).dualMap
  have hA : ∀ t l v, A t l v = l (σ.ρ t v) := fun _ _ _ => rfl
  have hcommA : ∀ s t x, A s (A t x) = A t (A s x) := by
    intro s t x
    ext v
    rw [hA, hA, hA, hA, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  have hpos : 0 < Module.finrank ℂ (Module.Dual ℂ σ.V) := by
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  have : Nontrivial (Module.Dual ℂ σ.V) := Module.nontrivial_of_finrank_pos hpos
  let a : Set (Submodule ℂ (Module.Dual ℂ σ.V)) :=
    {S | S ≠ ⊥ ∧ ∀ t, ∀ x ∈ S, A t x ∈ S}
  have ha : a.Nonempty := ⟨⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨S, ⟨hS0, hSinv⟩, hSmin⟩ := IsArtinian.set_has_minimal a ha
  have hscal : ∀ t, ∃ c : ℂ, ∀ x ∈ S, A t x = c • x := by
    intro t
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
    let f : Module.End ℂ S := (A t).restrict (hSinv t)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
    let E : Submodule ℂ (Module.Dual ℂ σ.V) := S ⊓ LinearMap.ker (A t - c • LinearMap.id)
    have hmemE : ∀ x, x ∈ E ↔ x ∈ S ∧ A t x = c • x := by
      intro x
      simp [E, sub_eq_zero]
    have hyE : (y : Module.Dual ℂ σ.V) ∈ E :=
      (hmemE _).2 ⟨y.2, congrArg Subtype.val hy.apply_eq_smul⟩
    have hE0 : E ≠ ⊥ := by
      intro h
      have : (y : Module.Dual ℂ σ.V) = 0 := by
        rw [h] at hyE
        exact hyE
      exact hy.2 (Subtype.ext this)
    have hEinv : ∀ s, ∀ x ∈ E, A s x ∈ E := by
      intro s x hx
      rw [hmemE] at hx ⊢
      refine ⟨hSinv s x hx.1, ?_⟩
      rw [hcommA, hx.2, map_smul]
    have hES : E = S := by
      by_contra hne
      exact hSmin E ⟨hE0, hEinv⟩ (lt_of_le_of_ne inf_le_left hne)
    refine ⟨c, fun x hx => ?_⟩
    rw [← hES, hmemE] at hx
    exact hx.2
  obtain ⟨l, hlS, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine ⟨l, hl0, fun t => ?_⟩
  obtain ⟨c, hc⟩ := hscal t
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun m => m v) (hc l hlS)
  simpa [hA] using this

variable [IsTopologicalGroup T]

/-- A smooth representation of a commutative group on a nonzero space of finite dimension has a character $\theta$ with open kernel as a quotient: there is a nonzero linear form $l$ with $l(\sigma(t) v) = \theta(t) l(v)$. -/
theorem exists_dual_char (σ : SmoothRep T) (hcomm : ∀ s t : T, s * t = t * s)
    [FiniteDimensional ℂ σ.V] [Nontrivial σ.V] :
    ∃ (l : Module.Dual ℂ σ.V) (θ : T →* ℂˣ), l ≠ 0 ∧ IsOpen (θ.ker : Set T) ∧
      ∀ t v, l (σ.ρ t v) = θ t * l v := by
  obtain ⟨l, hl0, hl⟩ := σ.exists_dual_eigen hcomm
  obtain ⟨v₀, hv₀⟩ : ∃ v, l v ≠ 0 := by
    by_contra h
    push Not at h
    exact hl0 (LinearMap.ext h)
  let c : T → ℂ := fun t => l (σ.ρ t v₀) / l v₀
  have hc : ∀ t v, l (σ.ρ t v) = c t * l v := by
    intro t v
    obtain ⟨d, hd⟩ := hl t
    have h0 := hd v₀
    have : c t = d := by
      simp only [c, h0]
      field_simp
    rw [this, hd]
  have hc1 : c 1 = 1 := by
    simp only [c, map_one, Module.End.one_apply]
    exact div_self hv₀
  have hcmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    have h := hc (s * t) v₀
    rw [map_mul, Module.End.mul_apply, hc s, hc t, ← mul_assoc] at h
    exact (mul_right_cancel₀ hv₀ h).symm
  have hcne : ∀ t, c t ≠ 0 := by
    intro t h
    have := hcmul t t⁻¹
    rw [mul_inv_cancel, hc1, h, zero_mul] at this
    exact one_ne_zero this
  let θ : T →* ℂˣ :=
    { toFun := fun t => Units.mk0 (c t) (hcne t)
      map_one' := Units.ext hc1
      map_mul' := fun s t => Units.ext (hcmul s t) }
  refine ⟨l, θ, hl0, ?_, fun t v => hc t v⟩
  refine Subgroup.isOpen_mono (H₁ := vecStabilizer σ.ρ v₀) ?_ (σ.smooth v₀)
  intro t ht
  rw [mem_vecStabilizer] at ht
  rw [MonoidHom.mem_ker]
  refine Units.ext ?_
  change c t = 1
  simp only [c, ht]
  exact div_self hv₀

/-- The map of representations $v \mapsto l(v)$ from $\sigma$ to a character $\theta$, for a linear form $l$ with $l(\sigma(t) v) = \theta(t) l(v)$. -/
noncomputable def charHom (σ : SmoothRep T) {θ : T →* ℂˣ} (hθ : IsOpen (θ.ker : Set T))
    (l : Module.Dual ℂ σ.V) (hl : ∀ t v, l (σ.ρ t v) = θ t * l v) :
    IntertwiningMap σ.ρ (charRep θ hθ).ρ :=
  ((ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm.toLinearMap ∘ₗ l).intertwiningMap_of_isIntertwiningMap
    σ.ρ (charRep θ hθ).ρ
    (fun t v => ULift.ext (by
      change l (σ.ρ t v) = (θ t : ℂ) * l v
      exact hl t v))

/-- The map `charHom` is not zero if $l$ is not zero. -/
theorem charHom_ne_zero (σ : SmoothRep T) {θ : T →* ℂˣ} (hθ : IsOpen (θ.ker : Set T))
    {l : Module.Dual ℂ σ.V} (hl : ∀ t v, l (σ.ρ t v) = θ t * l v) (hl0 : l ≠ 0) :
    σ.charHom hθ l hl ≠ 0 := by
  intro h
  refine hl0 (LinearMap.ext fun v => ?_)
  have := congrArg (fun F : IntertwiningMap σ.ρ (charRep θ hθ).ρ => (F v).down) h
  exact (show l v = ((σ.charHom hθ l hl) v).down from rfl).trans (this.trans rfl)

end SmoothRep

end Eigen

section Torus

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

namespace GL2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The homomorphism $(a, d) \mapsto \mathrm{diag}(a, d)$ from $K^\times \times K^\times$ to $T$. -/
noncomputable def diagTorusHom : Kˣ × Kˣ →* torus K where
  toFun p := diagTorus K p.1 p.2
  map_one' := Subtype.ext (Units.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagTorus]))
  map_mul' p q := Subtype.ext (Units.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagTorus, Matrix.mul_apply, Fin.sum_univ_two]))

omit [IsNonarchimedeanLocalField K] [ValuativeRel K] in
/-- The map $(a, d) \mapsto \mathrm{diag}(a, d)$ is continuous. -/
theorem continuous_diagTorusHom [IsTopologicalRing K] :
    Continuous (diagTorusHom (K := K)) := by
  have h : ∀ f : Kˣ × Kˣ → Matrix (Fin 2) (Fin 2) K, (∀ i j, Continuous fun x => f x i j) →
      Continuous f := fun f hf => continuous_pi fun i => continuous_pi fun j => hf i j
  refine Continuous.subtype_mk
    (Units.continuous_iff.mpr ⟨h _ fun i j => ?_, h _ fun i j => ?_⟩) _
  · change Continuous fun p : Kˣ × Kˣ => !![(p.1 : K), 0; 0, (p.2 : K)] i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun p : Kˣ × Kˣ => !![((p.1⁻¹ : Kˣ) : K), 0; 0, ((p.2⁻¹ : Kˣ) : K)] i j
    fin_cases i <;> fin_cases j <;> simp <;> first
      | fun_prop
      | exact (Units.continuous_coe_inv.comp continuous_fst).congr fun p => Units.val_inv_eq_inv_val p.1
      | exact (Units.continuous_coe_inv.comp continuous_snd).congr fun p => Units.val_inv_eq_inv_val p.2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Each $t \in T$ is $\mathrm{diag}(a, d)$ for its diagonal entries $a$ and $d$. -/
theorem eq_diagTorus (t : torus K) :
    t = diagTorus K (diagFst ⟨t, torus_le_borel t.2⟩) (diagSnd ⟨t, torus_le_borel t.2⟩) := by
  have ht := (mem_torus _).1 t.2
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTorus, val_diagFst, val_diagSnd, ht.1, ht.2]

/-- Each smooth character $\theta$ of $T$ is $\alpha_1 \otimes \alpha_2$ for two smooth characters $\alpha_1, \alpha_2$ of $K^\times$. -/
theorem exists_torusChar_eq (θ : torus K →* ℂˣ) (hθ : IsOpen (θ.ker : Set (torus K))) :
    ∃ α₁ α₂ : Kˣ →* ℂˣ, IsSmoothChar K α₁ ∧ IsSmoothChar K α₂ ∧ torusChar α₁ α₂ = θ := by
  let α₁ : Kˣ →* ℂˣ := (θ.comp diagTorusHom).comp (MonoidHom.inl Kˣ Kˣ)
  let α₂ : Kˣ →* ℂˣ := (θ.comp diagTorusHom).comp (MonoidHom.inr Kˣ Kˣ)
  have hc₁ : Continuous fun a : Kˣ => diagTorusHom (K := K) (a, 1) :=
    continuous_diagTorusHom.comp (continuous_id.prodMk continuous_const)
  have hc₂ : Continuous fun d : Kˣ => diagTorusHom (K := K) (1, d) :=
    continuous_diagTorusHom.comp (continuous_const.prodMk continuous_id)
  refine ⟨α₁, α₂, hc₁.isOpen_preimage _ hθ, hc₂.isOpen_preimage _ hθ, ?_⟩
  have key : ∀ a d : Kˣ, torusChar α₁ α₂ (diagTorus K a d) = θ (diagTorus K a d) := by
    intro a d
    rw [torusChar_diagTorus]
    change θ (diagTorusHom (a, 1)) * θ (diagTorusHom (1, d)) = θ (diagTorusHom (a, d))
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  refine MonoidHom.ext fun t => ?_
  have := key (diagFst ⟨t, torus_le_borel t.2⟩) (diagSnd ⟨t, torus_le_borel t.2⟩)
  rwa [← eq_diagTorus t] at this

end GL2

end Torus

section Iso

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

omit [IsTopologicalGroup G] in
/-- The image of a map of representations is a stable subspace. -/
theorem isStableSubspace_range {π σ : SmoothRep G} (Φ : IntertwiningMap π.ρ σ.ρ) :
    IsStableSubspace σ.ρ (LinearMap.range Φ.toLinearMap) := by
  rintro g _ ⟨v, rfl⟩
  exact ⟨π.ρ g v, IntertwiningMap.isIntertwining _ _ Φ g v⟩

/-- An injective map of representations is an isomorphism onto its image. -/
theorem iso_sub_range {π σ : SmoothRep G} (Φ : IntertwiningMap π.ρ σ.ρ)
    (hΦ : Function.Injective Φ) :
    π.Iso (σ.sub (LinearMap.range Φ.toLinearMap) (isStableSubspace_range Φ)) :=
  ⟨LinearEquiv.ofInjective Φ.toLinearMap hΦ, fun g v =>
    Subtype.ext (IntertwiningMap.isIntertwining _ _ Φ g v)⟩

omit [IsTopologicalGroup G] in
/-- A bijective map of representations gives an isomorphism. -/
theorem iso_of_bijective {π σ : SmoothRep G} (Φ : IntertwiningMap π.ρ σ.ρ)
    (hΦ : Function.Bijective Φ) : π.Iso σ :=
  ⟨LinearEquiv.ofBijective Φ.toLinearMap hΦ, fun g v =>
    IntertwiningMap.isIntertwining _ _ Φ g v⟩

/-- Two equal stable subspaces give isomorphic subrepresentations. -/
theorem sub_iso_of_eq (σ : SmoothRep G) {W W' : Submodule ℂ σ.V} (h : W = W')
    (hW : IsStableSubspace σ.ρ W) (hW' : IsStableSubspace σ.ρ W') :
    (σ.sub W hW).Iso (σ.sub W' hW') := by
  subst h
  exact Iso.refl _

omit [IsTopologicalGroup G] in
/-- An isomorphism of representations gives a bijective map of representations. -/
theorem Iso.exists_bijective {π σ : SmoothRep G} (h : π.Iso σ) :
    ∃ Φ : IntertwiningMap π.ρ σ.ρ, Function.Bijective Φ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.toLinearMap.intertwiningMap_of_isIntertwiningMap π.ρ σ.ρ he, e.bijective⟩

omit [IsTopologicalGroup G] in
/-- A representation that is isomorphic to an irreducible one is irreducible. -/
theorem IsIrreducible.of_iso {π σ : SmoothRep G} (hπ : π.IsIrreducible) (h : π.Iso σ) :
    σ.IsIrreducible := by
  obtain ⟨Φ, hΦ⟩ := h.exists_bijective
  exact hπ.of_bijective Φ hΦ

end SmoothRep

end Iso

section Embedding

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- **Jacquet's embedding.** Let $\pi$ be an irreducible smooth representation of $GL_2(K)$ whose Jacquet module $\pi_N$ is not zero and has finite dimension. Then $\pi$ is a subrepresentation of a principal series: there are smooth characters $\alpha_1, \alpha_2$ and an injective map of representations $\pi \to \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ (unnormalized induction). The character $\alpha_1 \otimes \alpha_2$ of $T$ is a quotient of $\pi_N$. -/
theorem exists_injective_principalSeriesInd (π : SmoothRep (GL (Fin 2) K))
    (hπ : π.IsIrreducible)
    [FiniteDimensional ℂ (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V]
    [Nontrivial (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V] :
    ∃ (α₁ α₂ : Kˣ →* ℂˣ) (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂)
      (Φ : IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ), Function.Injective Φ := by
  obtain ⟨l, θ, hl0, hθ, hl⟩ :=
    (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).exists_dual_char
      torus_mul_comm
  obtain ⟨α₁, α₂, hα₁, hα₂, he⟩ := exists_torusChar_eq θ hθ
  have hl' : ∀ t v, l ((π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).ρ t v) =
      torusChar α₁ α₂ t * l v := by
    rw [he]
    exact hl
  let φ := charHom _ (isOpen_ker_torusChar hα₁ hα₂) l hl'
  refine ⟨α₁, α₂, hα₁, hα₂, (π.jacquetFrobenius hα₁ hα₂).symm φ, hπ.injective _ ?_⟩
  rw [LinearEquiv.map_ne_zero_iff]
  exact charHom_ne_zero _ _ hl' hl0

end Embedding

section Cases

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- If `Langlands.bigCellChar` of $(\alpha_1, \alpha_2)$ is trivial on each $\mathrm{diag}(a, a^{-1})$, then $\alpha_1 = \alpha_2 |\cdot|^2$. -/
theorem eq_mul_absChar_sq_of_bigCellChar {α₁ α₂ : Kˣ →* ℂˣ}
    (h : ∀ a : Kˣ, bigCellChar α₁ α₂ (diagTorus K a a⁻¹) = 1) : α₁ = α₂ * absChar K ^ 2 := by
  refine MonoidHom.ext fun a => Units.ext ?_
  have ha := congrArg Units.val (h a)
  rw [bigCellChar, torusChar_diagTorus] at ha
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_one] at ha
  have h0 : (α₁ a : ℂ) ≠ 0 := Units.ne_zero _
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp at ha
  linear_combination -ha

/-- The subrepresentation on the line of $\chi \circ \det$ in $\mathrm{Ind}_B^G(\chi \otimes \chi)$ is the character $\chi \circ \det$. -/
theorem sub_selfDetLine_iso {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) :
    ((principalSeriesInd χ χ hχ hχ).sub (selfDetLine hχ) selfDetLine_stable).Iso
      (charRep (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ)) := by
  have hf₀ : selfDetVec hχ ≠ 0 := detVec_ne_zero hχ (borelChar_self_apply χ)
  let e : (charRep (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ)).V ≃ₗ[ℂ] selfDetLine hχ :=
    (ULift.moduleEquiv (R := ℂ) (M := ℂ)).trans
      (LinearEquiv.toSpanNonzeroSingleton ℂ _ (selfDetVec hχ) hf₀)
  refine Iso.symm ⟨e, fun g c => Subtype.ext ?_⟩
  change ((detChar K 2 χ g : ℂ) * c.down) • selfDetVec hχ =
    (principalSeriesInd χ χ hχ hχ).ρ g (c.down • selfDetVec hχ)
  have h := ρ_detVec (θ := borelChar χ χ) (hθ := isOpen_ker_borelChar hχ hχ) hχ
    (borelChar_self_apply χ) g
  rw [map_smul, show (principalSeriesInd χ χ hχ hχ).ρ g (selfDetVec hχ) =
    (detChar K 2 χ g : ℂ) • selfDetVec hχ from h, smul_smul, mul_comm]

/-- Normalized and unnormalized principal series agree when the characters match: if $\chi_1 |\cdot|^{1/2} = \alpha_1$ and $\chi_2 |\cdot|^{-1/2} = \alpha_2$, then the normalized principal series of $(\chi_1, \chi_2)$ is $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$. -/
theorem normPrincipalSeries_eq_of {χ₁ χ₂ α₁ α₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂)
    (h₁ : χ₁ * sqrtAbsChar K = α₁) (h₂ : χ₂ * (sqrtAbsChar K)⁻¹ = α₂) :
    normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂ = principalSeriesInd α₁ α₂ hα₁ hα₂ := by
  rw [normPrincipalSeries_eq]
  subst h₁ h₂
  rfl

/-- The twisted Steinberg representation `Langlands.steinbergSub` of $(\chi_1, \chi_2)$, with $\chi_1 = \chi_2 |\cdot|$, is the subrepresentation $W_0$ of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ for $\alpha_1 = \chi_1 |\cdot|^{1/2}$ and $\alpha_2 = \chi_2 |\cdot|^{-1/2}$. -/
theorem steinbergSub_iso {χ₁ χ₂ α₁ α₂ : Kˣ →* ℂˣ} (hχ₁ : IsSmoothChar K χ₁)
    (hχ₂ : IsSmoothChar K χ₂) (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂)
    (h : χ₁ = χ₂ * absChar K) (hα : α₁ = α₂ * absChar K ^ 2)
    (h₁ : χ₁ * sqrtAbsChar K = α₁) (h₂ : χ₂ * (sqrtAbsChar K)⁻¹ = α₂) :
    (steinbergSub χ₁ χ₂ hχ₁ hχ₂ h).Iso ((principalSeriesInd α₁ α₂ hα₁ hα₂).sub
      (jacquetEigenSub _ (torusChar α₁ α₂)) (jacquetEigenSub_stable hα)) := by
  subst h₁ h₂
  have key : ∀ P : SmoothRep (GL (Fin 2) K), P = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) hα₁ hα₂ →
      ∀ hP : IsStableSubspace P.ρ (jacquetEigenSub P
        (torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹))),
      (P.sub _ hP).Iso ((principalSeriesInd _ _ hα₁ hα₂).sub
        (jacquetEigenSub _ (torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹)))
        (jacquetEigenSub_stable hα)) := by
    intro P hP
    subst hP
    intro _
    exact Iso.refl _
  exact key _ (normPrincipalSeries_eq hχ₁ hχ₂) _

end Cases

section Classification

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- **Classification, unnormalized form.** Let $\pi$ be an irreducible smooth representation of $GL_2(K)$ whose Jacquet module $\pi_N$ is not zero and has finite dimension. Then there are smooth characters $\alpha_1, \alpha_2$ such that one of these holds: (1) $\Psi = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ is irreducible and $\pi \cong \Psi$; (2) $\alpha_1 = \alpha_2$ and $\pi \cong \alpha_1 \circ \det$; (3) $\alpha_1 = \alpha_2 |\cdot|^2$ and $\pi$ is isomorphic to the subrepresentation $W_0$ of $\Psi$. -/
theorem classification_principalSeriesInd (π : SmoothRep (GL (Fin 2) K))
    (hπ : π.IsIrreducible)
    [FiniteDimensional ℂ (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V]
    [Nontrivial (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V] :
    ∃ (α₁ α₂ : Kˣ →* ℂˣ) (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂),
      ((principalSeriesInd α₁ α₂ hα₁ hα₂).IsIrreducible ∧
        π.Iso (principalSeriesInd α₁ α₂ hα₁ hα₂)) ∨
      (α₁ = α₂ ∧ π.Iso (charRep (detChar K 2 α₁) (isOpen_ker_detChar K 2 α₁ hα₁))) ∨
      (∃ h : α₁ = α₂ * absChar K ^ 2, π.Iso ((principalSeriesInd α₁ α₂ hα₁ hα₂).sub
        (jacquetEigenSub _ (torusChar α₁ α₂)) (jacquetEigenSub_stable h))) := by
  obtain ⟨α₁, α₂, hα₁, hα₂, Φ, hΦ⟩ := exists_injective_principalSeriesInd π hπ
  refine ⟨α₁, α₂, hα₁, hα₂, ?_⟩
  have hW := isStableSubspace_range Φ
  have h0 : LinearMap.range Φ.toLinearMap ≠ ⊥ := by
    intro h
    have := hπ.1
    obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
    apply hv
    apply hΦ
    have hmem : Φ.toLinearMap v ∈ LinearMap.range Φ.toLinearMap := ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hmem.trans (map_zero Φ).symm
  by_cases htop : LinearMap.range Φ.toLinearMap = ⊤
  · have hb : Function.Bijective Φ := ⟨hΦ, LinearMap.range_eq_top.mp htop⟩
    exact Or.inl ⟨hπ.of_bijective Φ hb, iso_of_bijective Φ hb⟩
  right
  have hred : ¬ (principalSeriesInd α₁ α₂ hα₁ hα₂).IsIrreducible := fun hirr =>
    htop ((hirr.2 _ hW).resolve_left h0)
  by_cases h12 : α₁ = α₂
  · subst h12
    exact Or.inl ⟨rfl, (iso_sub_range Φ hΦ).trans ((sub_iso_of_eq _
      (stable_eq_selfDetLine hW h0 htop) _ selfDetLine_stable).trans (sub_selfDetLine_iso hα₁))⟩
  have h : α₁ = α₂ * absChar K ^ 2 := by
    by_contra hne
    refine hred (principalSeriesInd_isIrreducible h12 ?_)
    by_contra hc
    push Not at hc
    exact hne (eq_mul_absChar_sq_of_bigCellChar hc)
  exact Or.inr ⟨h, (iso_sub_range Φ hΦ).trans
    (sub_iso_of_eq _ (stable_eq_jacquetEigenSub h hW h0 htop) _ _)⟩

/-- **Classification.** Let $\pi$ be an irreducible smooth representation of $GL_2(K)$ whose Jacquet module $\pi_N$ is not zero and has finite dimension. Then $\pi$ is isomorphic to one of these: (1) an irreducible normalized principal series $\pi(\chi_1, \chi_2)$; (2) a character $\chi \circ \det$; (3) a twisted Steinberg representation `Langlands.steinbergSub` of $(\chi_1, \chi_2)$ with $\chi_1 = \chi_2 |\cdot|$. -/
theorem classification (π : SmoothRep (GL (Fin 2) K)) (hπ : π.IsIrreducible)
    [FiniteDimensional ℂ (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V]
    [Nontrivial (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V] :
    (∃ (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂),
      (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).IsIrreducible ∧
        π.Iso (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂)) ∨
    (∃ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
      π.Iso (charRep (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ))) ∨
    (∃ (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂)
      (h : χ₁ = χ₂ * absChar K), π.Iso (steinbergSub χ₁ χ₂ hχ₁ hχ₂ h)) := by
  obtain ⟨α₁, α₂, hα₁, hα₂, hc | ⟨_, hc⟩ | ⟨hα, hc⟩⟩ := classification_principalSeriesInd π hπ
  · have hχ₁ := hα₁.mul isSmoothChar_sqrtAbsChar.inv
    have hχ₂ := hα₂.mul isSmoothChar_sqrtAbsChar
    have he : normPrincipalSeries _ _ hχ₁ hχ₂ = principalSeriesInd α₁ α₂ hα₁ hα₂ :=
      normPrincipalSeries_eq_of _ _ _ _ (inv_mul_cancel_right α₁ _) (mul_inv_cancel_right α₂ _)
    exact Or.inl ⟨_, _, hχ₁, hχ₂, he ▸ hc⟩
  · exact Or.inr (Or.inl ⟨α₁, hα₁, hc⟩)
  · have hχ₂ := hα₂.mul isSmoothChar_sqrtAbsChar
    have hχ₁ := hχ₂.mul isSmoothChar_absChar
    have h₁ : α₂ * sqrtAbsChar K * absChar K * sqrtAbsChar K = α₁ := by
      rw [hα, ← sqrtAbsChar_sq]
      ext x
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have h₂ : α₂ * sqrtAbsChar K * (sqrtAbsChar K)⁻¹ = α₂ := mul_inv_cancel_right α₂ _
    exact Or.inr (Or.inr ⟨_, _, hχ₁, hχ₂, rfl,
      hc.trans (steinbergSub_iso hχ₁ hχ₂ hα₁ hα₂ rfl hα h₁ h₂).symm⟩)

/-- A smooth representation $\pi$ of $GL_2(K)$ is Jacquet cuspidal if its Jacquet module $\pi_N$ for the upper unipotent subgroup $N$ is zero. This is the algebraic form of supercuspidality. It is not proved here to agree with `Langlands.SmoothRep.IsSupercuspidal`, which uses matrix coefficients. -/
def SmoothRep.IsJacquetCuspidal (π : SmoothRep (GL (Fin 2) K)) : Prop :=
  Subsingleton (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V

/-- **Dichotomy.** Let $\pi$ be an irreducible smooth representation of $GL_2(K)$ whose Jacquet module has finite dimension. Then $\pi$ is Jacquet cuspidal, or $\pi$ is isomorphic to an irreducible normalized principal series, to a character $\chi \circ \det$, or to a twisted Steinberg representation. -/
theorem isJacquetCuspidal_or_classification (π : SmoothRep (GL (Fin 2) K))
    (hπ : π.IsIrreducible)
    [FiniteDimensional ℂ (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V] :
    π.IsJacquetCuspidal ∨
    (∃ (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂),
      (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).IsIrreducible ∧
        π.Iso (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂)) ∨
    (∃ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
      π.Iso (charRep (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ))) ∨
    (∃ (χ₁ χ₂ : Kˣ →* ℂˣ) (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂)
      (h : χ₁ = χ₂ * absChar K), π.Iso (steinbergSub χ₁ χ₂ hχ₁ hχ₂ h)) := by
  rcases subsingleton_or_nontrivial
      (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).V with h | h
  · exact Or.inl h
  · exact Or.inr (classification π hπ)

/-- **Isomorphism classes of principal series.** Let the normalized principal series $\pi(\chi_1, \chi_2)$ be irreducible. Then $\pi(\chi_1, \chi_2) \cong \pi(\chi_1', \chi_2')$ if and only if $(\chi_1', \chi_2')$ is $(\chi_1, \chi_2)$ or $(\chi_2, \chi_1)$. -/
theorem normPrincipalSeries_iso_iff {χ₁ χ₂ χ₁' χ₂' : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁}
    {hχ₂ : IsSmoothChar K χ₂} {hχ₁' : IsSmoothChar K χ₁'} {hχ₂' : IsSmoothChar K χ₂'}
    (hirr : (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).IsIrreducible) :
    (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).Iso (normPrincipalSeries χ₁' χ₂' hχ₁' hχ₂') ↔
      (χ₁' = χ₁ ∧ χ₂' = χ₂) ∨ (χ₁' = χ₂ ∧ χ₂' = χ₁) := by
  constructor
  · intro h
    obtain ⟨Φ, hΦ⟩ := h.exists_bijective
    refine normPrincipalSeries_hom_eq Φ fun h0 => ?_
    have := hirr.1
    obtain ⟨v, hv⟩ := exists_ne (0 : (normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂).V)
    exact hv (hΦ.1 ((congrArg (fun F => F v) h0).trans (map_zero Φ).symm))
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> obtain rfl := h₁.symm <;> obtain rfl := h₂.symm
  · exact Iso.refl _
  by_cases h12 : χ₁ = χ₂
  · subst h12
    exact Iso.refl _
  have hα₁ := hχ₁.mul isSmoothChar_sqrtAbsChar
  have hα₂ := hχ₂.mul isSmoothChar_sqrtAbsChar.inv
  have e₁ := normPrincipalSeries_eq hχ₁ hχ₂
  have e₂ : normPrincipalSeries χ₂ χ₁ hχ₂ hχ₁ = principalSeriesInd
      (χ₂ * (sqrtAbsChar K)⁻¹ * absChar K) (χ₁ * sqrtAbsChar K * (absChar K)⁻¹)
      (hα₂.mul isSmoothChar_absChar) (hα₁.mul isSmoothChar_absChar.inv) :=
    normPrincipalSeries_eq_of _ _ _ _ (mul_sqrtAbsChar_inv_mul_absChar χ₂).symm
      (mul_sqrtAbsChar_mul_absChar_inv χ₁).symm
  rw [e₁] at hirr
  rw [e₁, e₂]
  have hne : ∃ t, torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹) t ≠
      bigCellChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹) t := by
    by_contra hc
    push Not at hc
    have h := (torusChar_inj.mp (MonoidHom.ext hc)).1
    rw [mul_sqrtAbsChar_inv_mul_absChar] at h
    exact h12 (mul_right_cancel h)
  obtain ⟨Φ, hΦ⟩ := principalSeriesInd_exists_bijective_of_isIrreducible hirr hne
  exact iso_of_bijective Φ hΦ

end Classification

end Langlands
