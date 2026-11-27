/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Torus

/-!
# The local Langlands correspondence for split tori

This file proves `Langlands.LocalLanglandsTorusSplit`. The proof uses only that $\mathrm{rec}_K$ is an isomorphism of topological groups. Together with `Langlands.LocalReciprocityGL1` it gives the correspondence for the split torus $\mathbb{G}_m^n$.

* `Langlands.WeilGroup.Ab.lift`: a continuous homomorphism from $W_K$ to a commutative Hausdorff group factors through $W_K^{ab}$.
* `Langlands.torusParameter`: the homomorphism $W_K \to (\mathbb{C}^\times)^n$ of a character $\chi$ of $(K^\times)^n$. Its component $i$ is $w \mapsto \chi(e_i(\mathrm{rec}_K^{-1}[w]))$, where $e_i$ puts an element of $K^\times$ in the place $i$.
* `Langlands.torusCharacter`: the character $x \mapsto \prod_i \varphi_i(\mathrm{rec}_K(x_i))$ of a homomorphism $\varphi$.
* `Langlands.localLanglandsTorusSplit`: the statement `LocalLanglandsTorusSplit n` for each $n$.
-/

namespace Langlands

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace WeilGroup

/-- A continuous homomorphism from $W_K$ to a commutative Hausdorff topological group factors through the topological abelianization $W_K^{ab}$. -/
noncomputable def Ab.lift {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (φ : ContinuousMonoidHom (WeilGroup K) A) : ContinuousMonoidHom (Ab K) A where
  toMonoidHom := QuotientGroup.lift _ φ.toMonoidHom <| by
    refine Subgroup.topologicalClosure_minimal _ (Group.Abelianization.commutator_le_ker _) ?_
    exact isClosed_singleton.preimage φ.continuous
  continuous_toFun := by
    apply continuous_quot_lift
    exact φ.continuous

@[simp]
theorem Ab.lift_mk {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (φ : ContinuousMonoidHom (WeilGroup K) A) (w : WeilGroup K) :
    Ab.lift φ (QuotientGroup.mk w) = φ w :=
  rfl

end WeilGroup

/-- The homomorphism $W_K \to (\mathbb{C}^\times)^n$ of a continuous character $\chi$ of $(K^\times)^n$ through $\mathrm{rec}_K$. -/
noncomputable def torusParameter {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (χ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ) : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ) where
  toFun w i := χ (Pi.mulSingle i (rec.symm (QuotientGroup.mk w)))
  map_one' := by
    funext i
    simp
  map_mul' v w := by
    funext i
    simp [Pi.mulSingle_mul]
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    refine χ.continuous.comp ?_
    refine (continuous_mulSingle i).comp ?_
    exact rec.symm.continuous.comp continuous_quot_mk

/-- The continuous character $x \mapsto \prod_i \varphi_i(\mathrm{rec}_K(x_i))$ of $(K^\times)^n$ of a homomorphism $\varphi : W_K \to (\mathbb{C}^\times)^n$. -/
noncomputable def torusCharacter {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (φ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ)) : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ where
  toFun x := ∏ i, WeilGroup.Ab.lift φ (rec (x i)) i
  map_one' := by simp
  map_mul' x y := by
    simp [Finset.prod_mul_distrib]
  continuous_toFun := by
    refine continuous_finsetProd _ fun i _ => ?_
    exact (continuous_apply i).comp
      ((WeilGroup.Ab.lift φ).continuous.comp (rec.continuous.comp (continuous_apply i)))

theorem torusCorrespond_torusParameter {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (χ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ) :
    TorusCorrespond K rec χ (torusParameter rec χ) := by
  intro x w hw
  have hx : x = ∏ i, Pi.mulSingle i (x i) := (Finset.univ_prod_mulSingle x).symm
  change χ x = ∏ i, χ (Pi.mulSingle i (rec.symm (QuotientGroup.mk (w i))))
  simp_rw [hw, ContinuousMulEquiv.symm_apply_apply]
  conv_lhs => rw [hx]
  exact map_prod χ _ _

theorem eq_torusParameter {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (χ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ) (ψ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ))
    (h : TorusCorrespond K rec χ ψ) : ψ = torusParameter rec χ := by
  ext w j
  have hc := h (Pi.mulSingle j (rec.symm (QuotientGroup.mk w))) (Pi.mulSingle j w) (by
    intro i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.mulSingle_eq_of_ne hij])
  rw [Finset.prod_eq_single j (fun i _ hij => by simp [Pi.mulSingle_eq_of_ne hij])
    (fun hj => absurd (Finset.mem_univ j) hj)] at hc
  simp only [Pi.mulSingle_eq_same] at hc
  rw [← hc]
  rfl

theorem torusCorrespond_torusCharacter {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (φ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ)) :
    TorusCorrespond K rec (torusCharacter rec φ) φ := by
  intro x w hw
  change ∏ i, WeilGroup.Ab.lift φ (rec (x i)) i = _
  simp_rw [← hw, WeilGroup.Ab.lift_mk]

/-- **The local Langlands correspondence for split tori.** The proof needs only that $\mathrm{rec}_K$ is an isomorphism of topological groups. -/
theorem localLanglandsTorusSplit (n : ℕ) : LocalLanglandsTorusSplit.{u} n := by
  intro K _ _ _ _ rec _
  exact ⟨fun χ => ⟨torusParameter rec χ, torusCorrespond_torusParameter rec χ,
      fun ψ h => eq_torusParameter rec χ ψ h⟩,
    fun φ => ⟨torusCharacter rec φ, torusCorrespond_torusCharacter rec φ⟩⟩

end Langlands
