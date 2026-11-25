/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.TorusInduced
import Langlands.Torus.Split

/-!
# The local Langlands correspondence for induced tori

This file proves `Langlands.LocalLanglandsTorusInduced`. The proof needs only that $\mathrm{rec}_L$ is an isomorphism of topological groups, Shapiro's lemma `Langlands.Shapiro.shapiro`, and the isomorphism `Langlands.WeilGroup.weilEquiv` of $W_L$ with an open subgroup of $W_K$.

* `Langlands.inducedParameter`: the class of a character $\chi$ of $L^\times$. It is the inverse image under Shapiro's isomorphism of $\chi \circ \mathrm{rec}_L^{-1}$, seen on $W_L$.
* `Langlands.inducedCharacter`: the character of $L^\times$ of a class $c$.
* `Langlands.localLanglandsTorusInduced`: the statement `LocalLanglandsTorusInduced`.
-/

namespace Langlands

universe u

open WeilGroup WeilGroup.FiniteExt

section Proof

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L]

/-- The continuous homomorphism $W_L \to \mathbb{C}^\times$, seen on `restrictSubgroup K L`, of a character $\chi$ of $L^\times$ through $\mathrm{rec}_L$. -/
noncomputable def inducedParameterHom (recL : Lˣ ≃ₜ* WeilGroup.Ab L)
    (χ : ContinuousMonoidHom Lˣ ℂˣ) : ContinuousMonoidHom (restrictSubgroup K L) ℂˣ where
  toFun y := χ (recL.symm (QuotientGroup.mk ((weilEquiv K L).symm y)))
  map_one' := by simp
  map_mul' a b := by simp
  continuous_toFun :=
    χ.continuous.comp (recL.symm.continuous.comp
      (continuous_quot_mk.comp (weilEquiv K L).symm.continuous))

/-- The class in $H^1(W_K, \mathrm{Coind}_{W_L}^{W_K} \mathbb{C}^\times)$ of a character $\chi$ of $L^\times$. -/
noncomputable def inducedParameter (recL : Lˣ ≃ₜ* WeilGroup.Ab L)
    (χ : ContinuousMonoidHom Lˣ ℂˣ) :
    Shapiro.H1 (WeilGroup K) (Shapiro.Coind (restrictSubgroup K L) ℂˣ) :=
  (Shapiro.shapiro (isOpen_restrictSubgroup K L)).symm (inducedParameterHom recL χ)

/-- The character of $L^\times$ of a class $c$: the composite of $\mathrm{rec}_L$ with the homomorphism $W_L^{ab} \to \mathbb{C}^\times$ given by Shapiro's isomorphism. -/
noncomputable def inducedCharacter (recL : Lˣ ≃ₜ* WeilGroup.Ab L)
    (c : Shapiro.H1 (WeilGroup K) (Shapiro.Coind (restrictSubgroup K L) ℂˣ)) :
    ContinuousMonoidHom Lˣ ℂˣ :=
  (WeilGroup.Ab.lift (((Shapiro.shapiro (isOpen_restrictSubgroup K L) c)).comp
    ⟨(weilEquiv K L).toMulEquiv.toMonoidHom, (weilEquiv K L).continuous⟩)).comp
    ⟨recL.toMulEquiv.toMonoidHom, recL.continuous⟩

theorem inducedTorusCorrespond_inducedParameter (recL : Lˣ ≃ₜ* WeilGroup.Ab L)
    (χ : ContinuousMonoidHom Lˣ ℂˣ) :
    InducedTorusCorrespond K L recL χ (inducedParameter recL χ) := by
  intro x w hw
  rw [inducedParameter, MulEquiv.apply_symm_apply]
  change χ (recL.symm (QuotientGroup.mk ((weilEquiv K L).symm (weilEquiv K L w)))) = χ x
  rw [ContinuousMulEquiv.symm_apply_apply, hw, ContinuousMulEquiv.symm_apply_apply]

theorem eq_inducedParameter (recL : Lˣ ≃ₜ* WeilGroup.Ab L) (χ : ContinuousMonoidHom Lˣ ℂˣ)
    (c : Shapiro.H1 (WeilGroup K) (Shapiro.Coind (restrictSubgroup K L) ℂˣ))
    (h : InducedTorusCorrespond K L recL χ c) : c = inducedParameter recL χ := by
  rw [inducedParameter, MulEquiv.eq_symm_apply]
  refine ContinuousMonoidHom.ext fun y => ?_
  obtain ⟨w, rfl⟩ := (weilEquiv K L).surjective y
  have := h (recL.symm (QuotientGroup.mk w)) w (recL.apply_symm_apply _).symm
  rw [weilEquiv_apply, this]
  change _ = χ (recL.symm (QuotientGroup.mk ((weilEquiv K L).symm (weilEquiv K L w))))
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem inducedTorusCorrespond_inducedCharacter (recL : Lˣ ≃ₜ* WeilGroup.Ab L)
    (c : Shapiro.H1 (WeilGroup K) (Shapiro.Coind (restrictSubgroup K L) ℂˣ)) :
    InducedTorusCorrespond K L recL (inducedCharacter recL c) c := by
  intro x w hw
  change _ = WeilGroup.Ab.lift _ (recL x)
  rw [← hw, WeilGroup.Ab.lift_mk]
  rfl

/-- **The local Langlands correspondence for induced tori.** The proof uses only that $\mathrm{rec}_L$ is an isomorphism of topological groups, Shapiro's lemma, and the identification of $W_L$ with an open subgroup of $W_K$. -/
theorem localLanglandsTorusInduced : LocalLanglandsTorusInduced.{u} := by
  intro K _ _ _ _ L _ recL _
  exact ⟨fun χ => ⟨inducedParameter recL χ, inducedTorusCorrespond_inducedParameter recL χ,
      fun c h => eq_inducedParameter recL χ c h⟩,
    fun c => ⟨inducedCharacter recL c, inducedTorusCorrespond_inducedCharacter recL c⟩⟩

end Proof

end Langlands
