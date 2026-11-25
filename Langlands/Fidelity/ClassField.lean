/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Mathlib.Topology.Algebra.Group.Units

/-!
# Fidelity checks for the statements of class field theory

This file has the checks F2 (positive instances) and F3 (negative instances) of spec 06.3 for the statements of `Langlands.Statements.ClassField`. A positive instance is a proof of a known special case of a statement. It shows that the hypotheses are not contradictory in that case, and that the conclusion has the expected meaning there. A negative instance is a proof that a wrong variant of a statement is false or trivial. It shows that each condition of the statement does work.

* `Langlands.Fidelity.normGroup_bot`: the norm group of the trivial extension is the full group of units.
* `Langlands.Fidelity.localExistence_top`: the conclusion of `LocalExistence` holds for the open subgroup $U = K^\times$.
* `Langlands.Fidelity.kroneckerWeber_bot`: the conclusion of `KroneckerWeber` holds for the trivial extension of $\mathbb{Q}$.
* `Langlands.Fidelity.finiteAbelian_of_localReciprocityGL1` (F2): `LocalReciprocityGL1` implies finite abelian local reciprocity, which the NYLL port proves (`Langlands.Bridge.finiteAbelianLocalReciprocity`). So the statement agrees with a known theorem.
* `Langlands.Fidelity.not_existsUnique_unnormalized` (F3): without the condition at a uniformizer, the reciprocity map is never unique, because $x \mapsto \mathrm{rec}(x)^{-1}$ is a second solution. So the condition `IsLocalArtinMap.uniformizer` is necessary for the uniqueness in `LocalReciprocityGL1`. The proof uses no hypothesis.
* `Langlands.Fidelity.isArtinMap_bot` (F2): the trivial map is an Artin map for the trivial extension of a number field. So the conditions of `IsArtinMap` are not contradictory.
* `Langlands.Fidelity.isArtinMap_iff_isArtinMapArith_invArt` (F3): a map is an Artin map in the geometric normalization if and only if $x \mapsto \mathrm{art}(x^{-1})$ is an Artin map in the arithmetic normalization. So the two normalizations are different conditions on the same map, and `GlobalReciprocity` fixes the geometric one.

The positive instance `KroneckerWeber` from `GlobalReciprocity` of spec 06.3 needs the conductor of a character and the ray class fields of $\mathbb{Q}$. It is a target of milestone S2.
-/

namespace Langlands.Fidelity

open IntermediateField

variable (K : Type*) [Field K]

instance isAbelianGalois_bot (E : Type*) [Field E] [Algebra K E] :
    IsAbelianGalois K (⊥ : IntermediateField K E) where
  is_comm := ⟨fun σ τ => by
    have key : ∀ ρ : Gal((⊥ : IntermediateField K E)/K), ρ = 1 := fun ρ => AlgEquiv.ext fun x => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp x.2
      have hx : x = algebraMap K _ a := Subtype.ext ha.symm
      rw [hx, AlgEquiv.commutes, AlgEquiv.one_apply]
    rw [key σ, key τ]⟩

/-- The norm group of the trivial extension of $K$ is $K^\times$. -/
theorem normGroup_bot (E : Type*) [Field E] [Algebra K E] :
    normGroup K (⊥ : IntermediateField K E) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ⟨Units.map (algebraMap K (⊥ : IntermediateField K E)).toMonoidHom x, ?_⟩
  ext
  simp [Algebra.norm_algebraMap, IntermediateField.finrank_bot]

/-- The conclusion of `LocalExistence` for the subgroup $U = K^\times$: the trivial extension has norm group $K^\times$. -/
theorem localExistence_top (E : Type*) [Field E] [Algebra K E] :
    ∃ L : IntermediateField K E, FiniteDimensional K L ∧ IsAbelianGalois K L ∧ normGroup K L = ⊤ :=
  ⟨⊥, inferInstance, inferInstance, normGroup_bot K E⟩

/-- The conclusion of `KroneckerWeber` for the trivial extension of $\mathbb{Q}$: it is contained in $\mathbb{Q}(\zeta_1) = \mathbb{Q}$. -/
theorem kroneckerWeber_bot :
    ∃ (n : ℕ) (ζ : AlgebraicClosure ℚ), 0 < n ∧ IsPrimitiveRoot ζ n ∧
      (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤ IntermediateField.adjoin ℚ {ζ} :=
  ⟨1, 1, one_pos, IsPrimitiveRoot.one, bot_le⟩

section Local

universe u

open WeilGroup ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **F2 for `LocalReciprocityGL1`.** The statement implies finite abelian local reciprocity: for each finite abelian extension $L/F$ there is a surjective homomorphism $F^\times \to \mathrm{Gal}(L/F)$ with kernel $N_{L/F}(L^\times)$. -/
theorem finiteAbelian_of_localReciprocityGL1 (h : LocalReciprocityGL1.{u})
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] [IsAbelianGalois F L] :
    ∃ artin : Fˣ →* Gal(L/F), Function.Surjective artin ∧ ∀ x : Fˣ, artin x = 1 ↔ x ∈ normGroup F L := by
  obtain ⟨rec, hrec, -⟩ := h F
  exact ⟨(Ab.restrict F L).comp rec.toMulEquiv.toMonoidHom, hrec.surjective L, hrec.ker L⟩

/-- The conditions of `IsLocalArtinMap` without the condition at a uniformizer. -/
structure IsLocalArtinMapUnnormalized (rec : Fˣ ≃ₜ* WeilGroup.Ab F) : Prop where
  /-- For each finite abelian extension, the map to its Galois group is surjective. -/
  surjective : ∀ (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    [IsAbelianGalois F L], Function.Surjective (WeilGroup.Ab.restrict F L ∘ rec)
  /-- For each finite abelian extension, the kernel of the map to its Galois group is the norm group. -/
  ker : ∀ (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    [IsAbelianGalois F L] (x : Fˣ), WeilGroup.Ab.restrict F L (rec x) = 1 ↔ x ∈ normGroup F L

/-- Inversion on $W_F^{ab}$ as a topological isomorphism. -/
noncomputable def invEquiv : WeilGroup.Ab F ≃ₜ* WeilGroup.Ab F :=
  { MulEquiv.inv (WeilGroup.Ab F) with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }

/-- A nonarchimedean local field has a unit $x$ with $x^2 \ne 1$: a uniformizer. -/
theorem exists_sq_ne_one : ∃ x : Fˣ, x ^ 2 ≠ 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have h0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 _ h0, fun h => hπ.not_isUnit ?_⟩
  have : (π : F) * π = 1 := by simpa [pow_two] using congrArg Units.val h
  exact IsUnit.of_mul_eq_one π (Subtype.ext (by simpa using this))

/-- If `rec` satisfies the conditions without the uniformizer, then so does $x \mapsto \mathrm{rec}(x)^{-1}$. -/
theorem isLocalArtinMapUnnormalized_inv {rec : Fˣ ≃ₜ* WeilGroup.Ab F}
    (h : IsLocalArtinMapUnnormalized F rec) :
    IsLocalArtinMapUnnormalized F (rec.trans (invEquiv F)) where
  surjective L _ _ g := by
    obtain ⟨x, hx⟩ := h.surjective L g⁻¹
    refine ⟨x, ?_⟩
    simp only [Function.comp_apply] at hx
    change Ab.restrict F L (rec x)⁻¹ = g
    rw [map_inv, hx, inv_inv]
  ker L _ _ x := by
    change Ab.restrict F L (rec x)⁻¹ = 1 ↔ _
    rw [map_inv, inv_eq_one]
    exact h.ker L x

/-- **F3 for `LocalReciprocityGL1`.** Without the condition at a uniformizer there is no unique reciprocity map. If `rec` is one, then $x \mapsto \mathrm{rec}(x)^{-1}$ is another, and the two are equal only if $x^2 = 1$ for each $x \in F^\times$, which is false for a uniformizer. -/
theorem not_existsUnique_unnormalized :
    ¬ ∃! rec : Fˣ ≃ₜ* WeilGroup.Ab F, IsLocalArtinMapUnnormalized F rec := by
  rintro ⟨rec, hrec, huniq⟩
  have h2 := huniq _ (isLocalArtinMapUnnormalized_inv F hrec)
  obtain ⟨x, hx⟩ := exists_sq_ne_one F
  apply hx
  apply rec.injective
  have : (rec x)⁻¹ = rec x := congrArg (fun e : Fˣ ≃ₜ* WeilGroup.Ab F => e x) h2
  rw [map_pow, map_one, pow_two]
  calc rec x * rec x = rec x * (rec x)⁻¹ := by rw [this]
    _ = 1 := mul_inv_cancel _

end Local

section Global

universe u

open NumberField IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F]

/-- The properties of an Artin map in the arithmetic normalization: the image of a uniformizer is the arithmetic Frobenius, not its inverse. This is the wrong variant of `IsArtinMap` for the check F3. -/
structure IsArtinMapArith (L : IntermediateField F (AlgebraicClosure F))
    (art : IdeleClassGroup (𝓞 F) F →* Gal(L/F)) : Prop where
  /-- The map is continuous. -/
  continuous : Continuous art
  /-- The map is surjective. -/
  surjective : Function.Surjective art
  /-- At an unramified prime, the image of a uniformizer is the arithmetic Frobenius. -/
  frobenius : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Ideal (𝓞 L)) [w.IsMaximal],
    w.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w →
      ∀ ϖ : (v.adicCompletion F)ˣ, IsUniformizer (ϖ : v.adicCompletion F) →
        IsArithFrobAt (𝓞 F) (art (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v ϖ)) w

/-- The map $x \mapsto \mathrm{art}(x^{-1})$. -/
noncomputable def invArt {L : IntermediateField F (AlgebraicClosure F)}
    (art : IdeleClassGroup (𝓞 F) F →* Gal(L/F)) : IdeleClassGroup (𝓞 F) F →* Gal(L/F) where
  toFun x := art x⁻¹
  map_one' := by simp
  map_mul' x y := by rw [← map_mul]; congr 1; exact mul_inv x y

/-- **F3 for `GlobalReciprocity`.** A map is an Artin map in the geometric normalization if and only if $x \mapsto \mathrm{art}(x^{-1})$ is an Artin map in the arithmetic normalization. -/
theorem isArtinMap_iff_isArtinMapArith_invArt (L : IntermediateField F (AlgebraicClosure F))
    (art : IdeleClassGroup (𝓞 F) F →* Gal(L/F)) :
    IsArtinMap F L art ↔ IsArtinMapArith F L (invArt F art) := by
  have hinv : ∀ x, invArt F art x = (art x)⁻¹ := fun x => map_inv art x
  constructor
  · intro h
    refine ⟨h.continuous.comp continuous_inv, fun g => ?_, fun v w _ hw hun ϖ hϖ => ?_⟩
    · obtain ⟨x, hx⟩ := h.surjective g
      exact ⟨x⁻¹, by rw [hinv, map_inv, inv_inv, hx]⟩
    · rw [hinv]
      exact h.frobenius v w hw hun ϖ hϖ
  · intro h
    refine ⟨?_, fun g => ?_, fun v w _ hw hun ϖ hϖ => ?_⟩
    · have := h.continuous.comp (continuous_inv : Continuous fun x : IdeleClassGroup (𝓞 F) F => x⁻¹)
      convert this using 1
      ext x
      simp [hinv]
    · obtain ⟨x, hx⟩ := h.surjective g
      exact ⟨x⁻¹, by rw [← hx, hinv, map_inv]⟩
    · have := h.frobenius v w hw hun ϖ hϖ
      rwa [hinv] at this

/-- Each integer of the trivial extension $\bot$ of $F$ comes from an integer of $F$. -/
theorem exists_algebraMap_ringOfIntegers_bot (x : 𝓞 (⊥ : IntermediateField F (AlgebraicClosure F))) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 (⊥ : IntermediateField F (AlgebraicClosure F))) a = x := by
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp (x : (⊥ : IntermediateField F (AlgebraicClosure F))).2
  have hint : IsIntegral ℤ k := by
    have hx : IsIntegral ℤ ((x : (⊥ : IntermediateField F (AlgebraicClosure F))) : AlgebraicClosure F) :=
      (x.2).map (IsScalarTower.toAlgHom ℤ (⊥ : IntermediateField F (AlgebraicClosure F)) (AlgebraicClosure F))
    rw [← hk] at hx
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F (AlgebraicClosure F)) (algebraMap F _).injective).mp hx
  refine ⟨⟨k, hint⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hk

/-- The Galois group of the trivial extension has one element. -/
instance subsingleton_gal_bot : Subsingleton Gal((⊥ : IntermediateField F (AlgebraicClosure F))/F) := by
  refine ⟨fun f g => AlgEquiv.ext fun x => ?_⟩
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp x.2
  have : x = algebraMap F (⊥ : IntermediateField F (AlgebraicClosure F)) k := Subtype.ext hk.symm
  rw [this, f.commutes, g.commutes]

/-- **F2 for `GlobalReciprocity`.** The trivial map is an Artin map for the trivial extension. The condition at each prime is the congruence $a^q \equiv a$ modulo $v$, for $a \in \mathcal{O}_F$ and $q = |\mathcal{O}_F / v|$. So the conditions of `IsArtinMap` are not contradictory. -/
theorem isArtinMap_bot : IsArtinMap F (⊥ : IntermediateField F (AlgebraicClosure F)) 1 := by
  refine ⟨continuous_const, fun g => ⟨1, Subsingleton.elim _ _⟩, fun v w _ hw _ ϖ _ => ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := exists_algebraMap_ringOfIntegers_bot F x
  simp only [MonoidHom.one_apply, inv_one, MulSemiringAction.toAlgHom_apply, one_smul]
  rw [← map_pow, ← map_sub, ← Ideal.mem_comap, ← Ideal.under_def, ← hw.over,
    ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
  have : v.asIdeal.IsMaximal := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  have := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  rw [Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

end Global

end Langlands.Fidelity
