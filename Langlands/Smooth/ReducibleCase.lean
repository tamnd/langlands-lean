/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.IrreducibilityCriterion

/-!
# The reducible case of the principal series of $GL_2$

Let $K$ be a nonarchimedean local field, let $G = GL_2(K)$ and $B$ the Borel subgroup of the upper triangular matrices. Let $\chi_1, \chi_2$ be smooth characters of $K^\times$. The normalized principal series of `Langlands/Smooth/PrincipalSeries.lean` is $\mathrm{Ind}_B^G((\chi_1 \otimes \chi_2)\delta_B^{1/2})$, with $\delta_B(b) = |a/d|$. The file `Langlands/Smooth/IrreducibilityCriterion.lean` proves that it is irreducible if $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$. This file proves that it is reducible if $\chi_2 = \chi_1 |\cdot|$, that is, if $\chi_1 \chi_2^{-1} = |\cdot|^{-1}$. Then $(\chi_1 \otimes \chi_2)\delta_B^{1/2}(b) = \chi(ad) = \chi(\det b)$ with $\chi = \chi_1 |\cdot|^{1/2}$, so the function $g \mapsto \chi(\det g)$ is in the principal series and spans a stable line.

## Main definitions

* `Langlands.detVec`: the vector $g \mapsto \chi(\det g)$ of $\mathrm{Ind}_B^G \theta$, for a character $\theta$ of $B$ with $\theta(b) = \chi(\det b)$.
* `Langlands.detLine`: the line spanned by `Langlands.detVec`.
* `Langlands.detQuotient`: the quotient of $\mathrm{Ind}_B^G \theta$ by this line.
* `Langlands.steinbergQuotient`: for $\chi_2 = \chi_1 |\cdot|$, the quotient of the normalized principal series by the line of $\chi \circ \det$, that is, the twisted Steinberg representation $\chi \mathrm{St}$.

## Main results

* `Langlands.ρ_detVec`: $G$ acts on $\chi \circ \det$ by the character $\chi \circ \det$.
* `Langlands.detLine_stable`, `Langlands.detLine_ne_bot`, `Langlands.detLine_ne_top`: the line of $\chi \circ \det$ is a stable subspace that is neither $0$ nor the whole space.
* `Langlands.ind_not_isIrreducible`, `Langlands.principalSeriesInd_not_isIrreducible`: thus $\mathrm{Ind}_B^G \theta$ and the unnormalized principal series $\mathrm{Ind}_B^G(\chi \otimes \chi)$ are not irreducible.
* `Langlands.normPrincipalSeries_exists_detVec`, `Langlands.normPrincipalSeries_exists_stable_finrank_one`, `Langlands.normPrincipalSeries_hasHom_detChar`: for $\chi_2 = \chi_1 |\cdot|$, the function $\chi \circ \det$ spans a stable line of the normalized principal series, and the character $\chi \circ \det$ maps to it.
* `Langlands.normPrincipalSeries_not_isIrreducible`: for $\chi_2 = \chi_1 |\cdot|$ the normalized principal series is not irreducible.
* `Langlands.normPrincipalSeries_isIrreducible_iff_of_ne`: if $\chi_1 \neq \chi_2 |\cdot|$, the normalized principal series is irreducible exactly when $\chi_2 \neq \chi_1 |\cdot|$.
* `Langlands.two_le_rank_steinbergQuotient`, `Langlands.steinbergQuotient_not_iso_charRep`: the twisted Steinberg quotient has rank at least $2$, so it is not given by a character.

## Method

The line of $\chi \circ \det$ is not the whole space because of a vector $f_0$ with $f_0(1) = 1$ and support in $B U_1$, for a congruence subgroup $U_1$ of level $1$ on which $\chi \circ \det$ is trivial. An element whose lower row $(r, s)$ has $v(r) \ge v(s)$ is not in $B U_1$, so $f_0$ vanishes at $w$ and at $\bar n(\pm 1)$. The classes of $w f_0$ and $n(1) w f_0$ in the quotient are linearly independent: the values of $\chi \circ \det$, $w f_0$ and $n(1) w f_0$ at $1$, $w$ and $w n(-1)$ form a triangular matrix with nonzero diagonal.

## Open parts

The other reducible case, $\chi_1 = \chi_2 |\cdot|$, is not proved. In that case the principal series has the character $\chi \circ \det$ with $\chi = \chi_2 |\cdot|^{1/2}$ as a quotient, not as a subspace. The map onto it is $f \mapsto \int_{GL_2(\mathcal{O}_K)} \chi^{-1}(\det k) f(k) \, dk$, and its $G$-invariance needs the integration over $B \backslash G$, which the project does not have. The full criterion, irreducibility exactly when $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$, follows from that case. The file also does not prove that the Steinberg quotient is irreducible, nor that the principal series has length $2$.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
-/

universe u

open Representation Matrix

namespace Langlands

section DetVector

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep ValuativeRel

variable {θ : borel K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (borel K))} {χ : Kˣ →* ℂˣ}
  (hχ : IsSmoothChar K χ)

local notation "I" => SmoothRep.ind (borel K) (SmoothRep.charRep θ hθ)

include hχ in
/-- The function $g \mapsto \chi(\det g)$ is in $\mathrm{Ind}_B^G \theta$ if $\theta(b) = \chi(\det b)$ for each $b \in B$. -/
theorem detFun_mem (hθχ : ∀ b : borel K, θ b = detChar K 2 χ b) :
    (fun g : GL (Fin 2) K => (ULift.up (detChar K 2 χ g : ℂ) : ULift.{u} ℂ)) ∈
      indSpace (borel K) (charRep θ hθ) := by
  refine ⟨fun b g => ?_, (detChar K 2 χ).ker, isOpen_ker_detChar K 2 χ hχ, fun g u hu => ?_⟩
  · change ULift.up (detChar K 2 χ ((b : GL (Fin 2) K) * g) : ℂ) =
      (θ b : ℂ) • ULift.up (detChar K 2 χ g : ℂ)
    apply ULift.ext
    change ((detChar K 2 χ ((b : GL (Fin 2) K) * g) : ℂˣ) : ℂ) = (θ b : ℂ) * (detChar K 2 χ g : ℂ)
    rw [map_mul, Units.val_mul, hθχ]
  · rw [MonoidHom.mem_ker] at hu
    change (ULift.up (detChar K 2 χ (g * u) : ℂ) : ULift.{u} ℂ) = ULift.up (detChar K 2 χ g : ℂ)
    rw [map_mul, hu, mul_one]

variable (θ hθ) in
/-- The vector $g \mapsto \chi(\det g)$ of $\mathrm{Ind}_B^G \theta$, for $\theta(b) = \chi(\det b)$. -/
noncomputable def detVec (hθχ : ∀ b : borel K, θ b = detChar K 2 χ b) : (I).V :=
  show indSpace (borel K) (charRep θ hθ) from ⟨_, detFun_mem hχ hθχ⟩

variable (hθχ : ∀ b : borel K, θ b = detChar K 2 χ b)

/-- The value of `detVec` at $g$ is $\chi(\det g)$. -/
theorem detVec_apply (g : GL (Fin 2) K) :
    ind.toFun (detVec θ hθ hχ hθχ) g = ULift.up (detChar K 2 χ g : ℂ) :=
  rfl

/-- The group acts on `detVec` by the character: $g \cdot f = \chi(\det g) f$. -/
theorem ρ_detVec (g : GL (Fin 2) K) :
    (I).ρ g (detVec θ hθ hχ hθχ) = (detChar K 2 χ g : ℂ) • detVec θ hθ hχ hθχ := by
  apply ind.toFun_injective
  funext x
  apply ULift.ext
  change ((detChar K 2 χ (x * g) : ℂˣ) : ℂ) = (detChar K 2 χ g : ℂ) * (detChar K 2 χ x : ℂ)
  rw [map_mul, Units.val_mul, mul_comm]

/-- The vector `detVec` is not zero, since its value at $1$ is $1$. -/
theorem detVec_ne_zero : detVec θ hθ hχ hθχ ≠ 0 := by
  intro h
  have h1 : (ind.toFun (detVec θ hθ hχ hθχ) 1).down = (ind.toFun (0 : (I).V) 1).down := by rw [h]
  rw [detVec_apply, map_one, Units.val_one] at h1
  exact one_ne_zero h1

variable (θ hθ) in
/-- The line $\mathbb{C} f$ spanned by the vector $f = \chi \circ \det$ of $\mathrm{Ind}_B^G \theta$. -/
noncomputable def detLine : Submodule ℂ (I).V :=
  ℂ ∙ detVec θ hθ hχ hθχ

/-- The line spanned by $\chi \circ \det$ is stable under $G$. -/
theorem detLine_stable : IsStableSubspace (I).ρ (detLine θ hθ hχ hθχ) := by
  intro g v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  change (I).ρ g (c • detVec θ hθ hχ hθχ) ∈ detLine θ hθ hχ hθχ
  rw [map_smul, ρ_detVec, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The line spanned by $\chi \circ \det$ is not $0$. -/
theorem detLine_ne_bot : detLine θ hθ hχ hθχ ≠ ⊥ := by
  rw [detLine, Ne, Submodule.span_singleton_eq_bot]
  exact detVec_ne_zero hχ hθχ

/-- The line spanned by $\chi \circ \det$ has dimension $1$. -/
theorem finrank_detLine : Module.finrank ℂ (detLine θ hθ hχ hθχ) = 1 :=
  finrank_span_singleton (detVec_ne_zero hχ hθχ)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- If $v(m_{11} - 1) < 1$ and $v(m_{10}) < 1$ for the product $m = b^{-1} g$ with $b \in B$, then the lower row $(r, s)$ of $g$ has $v(r) < v(s)$. The proof only uses the lower row of $b^{-1} g$, which is $d^{-1}(r, s)$. -/
theorem lowerRow_of_mem_congruence {b g : GL (Fin 2) K} (hb : b ∈ GL2.borel K)
    (h1 : valuation K ((b⁻¹ * g).1 1 1 - 1) < 1) (h0 : valuation K ((b⁻¹ * g).1 1 0) < 1) :
    valuation K (g.1 1 0) < valuation K (g.1 1 1) := by
  have hb' : b⁻¹ ∈ GL2.borel K := (GL2.borel K).inv_mem hb
  have e1 : (b⁻¹ * g).1 1 1 = (b⁻¹).1 1 1 * g.1 1 1 := by
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (mem_borel _).1 hb', zero_mul, zero_add]
  have e0 : (b⁻¹ * g).1 1 0 = (b⁻¹).1 1 1 * g.1 1 0 := by
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (mem_borel _).1 hb', zero_mul, zero_add]
  have hv : valuation K ((b⁻¹ * g).1 1 1) = 1 := by
    have := Valuation.map_eq_of_sub_lt (valuation K) (x := 1) (y := (b⁻¹ * g).1 1 1)
      (by rw [map_one]; exact h1)
    rwa [map_one] at this
  rw [e1, map_mul] at hv
  rw [e0, map_mul] at h0
  have hd : valuation K ((b⁻¹).1 1 1) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact val_one_one_ne_zero hb'
  calc valuation K (g.1 1 0) = valuation K ((b⁻¹).1 1 1) * valuation K (g.1 1 0) /
        valuation K ((b⁻¹).1 1 1) := by field_simp
    _ < 1 / valuation K ((b⁻¹).1 1 1) := by
        have : 0 < valuation K ((b⁻¹).1 1 1) := zero_lt_iff.2 hd
        gcongr
    _ = valuation K (g.1 1 1) := by
        rw [← hv]
        field_simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element $g$ whose lower row $(r, s)$ has $v(r) \ge v(s)$ is not in $B U_1$, where $U_1$ is the congruence subgroup of level $1$. -/
theorem not_mem_borel_mul_congruence {g : GL (Fin 2) K}
    (hg : valuation K (g.1 1 1) ≤ valuation K (g.1 1 0)) (b : GL2.borel K) :
    (b : GL (Fin 2) K)⁻¹ * g ∉ congruence K 1 one_ne_zero le_rfl := by
  intro h
  have h1 := h.1 1 1
  have h0 := h.1 1 0
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h0
  exact (lowerRow_of_mem_congruence b.2 h1 h0).not_ge hg

include hχ hθχ in
/-- The induced representation $\mathrm{Ind}_B^G \theta$ has a vector $f_0$ with $f_0(1) = 1$ that vanishes at $w$ and at the lower unipotent matrices $\bar n(\pm 1)$. It is the vector with support $B U_1$ for a congruence subgroup $U_1$ on which $\chi \circ \det$ is trivial. -/
theorem exists_vec_eq_one_weyl_eq_zero : ∃ f : (I).V, ind.toFun f 1 = ULift.up 1 ∧
    ind.toFun f weyl = 0 ∧ ind.toFun f (lowerUnip 1) = 0 ∧ ind.toFun f (lowerUnip (-1)) = 0 := by
  set U := (detChar K 2 χ).ker ⊓ congruence K 1 one_ne_zero le_rfl
  have hU : IsOpen (U : Set (GL (Fin 2) K)) :=
    (isOpen_ker_detChar K 2 χ hχ).inter (isOpen_congruence 1 one_ne_zero le_rfl)
  have hθU : ∀ b : GL2.borel K, (b : GL (Fin 2) K) ∈ U → θ b = 1 := fun b hb => by
    rw [hθχ]
    exact (Subgroup.mem_inf.1 hb).1
  obtain ⟨f, hf1, hf0⟩ := exists_ind_charRep_support θ hθ U hU hθU
  have hz : ∀ g : GL (Fin 2) K, valuation K (g.1 1 1) ≤ valuation K (g.1 1 0) →
      ind.toFun f g = 0 := fun g hg =>
    hf0 g fun b hb => not_mem_borel_mul_congruence hg b (Subgroup.mem_inf.1 hb).2
  refine ⟨f, ?_, hz _ ?_, hz _ ?_, hz _ ?_⟩
  · rw [hf1 1 1 (by simp [U.one_mem]), map_one, Units.val_one]
  · rw [weyl_val]
    simp
  · change valuation K (!![(1 : K), 0; 1, 1] 1 1) ≤ valuation K (!![(1 : K), 0; 1, 1] 1 0)
    simp
  · change valuation K (!![(1 : K), 0; -1, 1] 1 1) ≤ valuation K (!![(1 : K), 0; -1, 1] 1 0)
    simp

/-- The line spanned by $\chi \circ \det$ is not the whole space. The vector $f_0$ of `exists_vec_eq_one_weyl_eq_zero` is not a multiple of $\chi \circ \det$, since $f_0(1) = 1$ and $f_0(w) = 0$, but $\chi(\det w) \neq 0$. -/
theorem detLine_ne_top : detLine θ hθ hχ hθχ ≠ ⊤ := by
  intro h
  obtain ⟨f, hf1, hfw, -, -⟩ := exists_vec_eq_one_weyl_eq_zero hχ hθχ (hθ := hθ)
  have hf : f ∈ detLine θ hθ hχ hθχ := h ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hf
  have e1 : c * (detChar K 2 χ 1 : ℂ) = 1 := by
    have := congrArg (fun v : (I).V => (ind.toFun v 1).down) hc
    rw [hf1] at this
    exact this
  have ew : c * (detChar K 2 χ weyl : ℂ) = 0 := by
    have := congrArg (fun v : (I).V => (ind.toFun v weyl).down) hc
    rw [hfw] at this
    exact this
  rw [map_one, Units.val_one, mul_one] at e1
  rw [e1, one_mul] at ew
  exact Units.ne_zero _ ew

include hχ hθχ in
/-- If $\theta(b) = \chi(\det b)$ for each $b \in B$, then $\mathrm{Ind}_B^G \theta$ is not irreducible: the line spanned by $\chi \circ \det$ is a stable subspace that is neither $0$ nor the whole space. -/
theorem ind_not_isIrreducible : ¬ (I).IsIrreducible := fun h =>
  (h.2 _ (detLine_stable hχ hθχ)).elim (detLine_ne_bot hχ hθχ) (detLine_ne_top hχ hθχ)

include hθχ in
/-- The map $\mathbb{C} \to \mathrm{Ind}_B^G \theta$, $c \mapsto c \, (\chi \circ \det)$, is a nonzero map of representations from the character $\chi \circ \det$. -/
theorem hasHom_detChar_ind :
    (charRep (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ)).HasHom (I) := by
  refine ⟨{ toFun := fun c => (show ULift.{u} ℂ from c).down • detVec θ hθ hχ hθχ
            map_add' := fun a b => add_smul _ _ _
            map_smul' := fun r a => mul_smul _ _ _ }, fun h0 => ?_, fun g v => ?_⟩
  · have h1 := LinearMap.congr_fun h0 (show (charRep (detChar K 2 χ)
      (isOpen_ker_detChar K 2 χ hχ)).V from ULift.up 1)
    change (1 : ℂ) • detVec θ hθ hχ hθχ = 0 at h1
    exact detVec_ne_zero hχ hθχ (by rwa [one_smul] at h1)
  · change ((detChar K 2 χ g : ℂ) * (show ULift.{u} ℂ from v).down) • detVec θ hθ hχ hθχ =
      (I).ρ g ((show ULift.{u} ℂ from v).down • detVec θ hθ hχ hθχ)
    rw [map_smul, ρ_detVec, smul_smul, mul_comm]

variable (θ hθ) in
/-- The quotient of $\mathrm{Ind}_B^G \theta$ by the line spanned by $\chi \circ \det$. For the normalized principal series of $(\chi |\cdot|^{-1/2}, \chi |\cdot|^{1/2})$ it is the twist $\chi \mathrm{St}$ of the Steinberg representation. -/
noncomputable def detQuotient : SmoothRep (GL (Fin 2) K) :=
  (I).quotient (detLine θ hθ hχ hθχ) (detLine_stable hχ hθχ)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The product $w \, n(-1) \, n(1) \, w$ is $1$. -/
theorem weyl_mul_unip_neg_mul_unip_mul_weyl :
    (weyl : GL (Fin 2) K) * unip (-1) * unip 1 * weyl = 1 := by
  rw [mul_assoc weyl, ← unip_add, neg_add_cancel, unip_zero, mul_one, weyl_mul_weyl]

/-- The quotient of $\mathrm{Ind}_B^G \theta$ by the line of $\chi \circ \det$ has two linearly independent vectors: the classes of $f_1 = w f_0$ and $f_2 = n(1) w f_0$. The values of $\chi \circ \det$, $f_1$ and $f_2$ at the points $1$, $w$ and $w n(-1)$ form a triangular matrix with nonzero diagonal. -/
theorem detQuotient_exists_linearIndependent :
    ∃ x y : (detQuotient θ hθ hχ hθχ).V, LinearIndependent ℂ ![x, y] := by
  obtain ⟨f, hf1, hfw, hfl, hfl'⟩ := exists_vec_eq_one_weyl_eq_zero hχ hθχ (hθ := hθ)
  set f₁ : (I).V := (I).ρ weyl f
  set f₂ : (I).V := (I).ρ (unip 1) ((I).ρ weyl f)
  refine ⟨Submodule.Quotient.mk f₁, Submodule.Quotient.mk f₂,
    LinearIndependent.pair_iff.2 fun s t hst => ?_⟩
  have hq : (Submodule.Quotient.mk (s • f₁ + t • f₂) : (I).V ⧸ detLine θ hθ hχ hθχ) = 0 := hst
  rw [Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hq
  have ev : ∀ x : GL (Fin 2) K, c * (detChar K 2 χ x : ℂ) =
      s * (ind.toFun f (x * weyl)).down + t * (ind.toFun f (x * unip 1 * weyl)).down :=
    fun x => congrArg (fun v : (I).V => (ind.toFun v x).down) hc
  have hb : ind.toFun f (unip 1 * weyl) = 0 := by
    have := ind.toFun_mul_left f ⟨unip 1, unipotent_le_borel (unip_mem 1)⟩ weyl
    rw [hfw, map_zero] at this
    exact this
  have e1 := ev 1
  rw [one_mul, one_mul, hfw, hb, map_one, Units.val_one, mul_one] at e1
  have e2 := ev weyl
  rw [weyl_mul_weyl, weyl_mul_unip_mul_weyl, hf1, hfl] at e2
  have e3 := ev (weyl * unip (-1))
  rw [weyl_mul_unip_mul_weyl, weyl_mul_unip_neg_mul_unip_mul_weyl, hf1, hfl'] at e3
  change c = s * (0 : ℂ) + t * 0 at e1
  simp only [mul_zero, add_zero] at e1
  subst e1
  change 0 * _ = s * 1 + t * (0 : ℂ) at e2
  change 0 * _ = s * (0 : ℂ) + t * 1 at e3
  simp only [zero_mul, mul_one, mul_zero, add_zero, zero_add] at e2 e3
  exact ⟨e2.symm, e3.symm⟩

/-- The quotient of $\mathrm{Ind}_B^G \theta$ by the line of $\chi \circ \det$ has rank at least $2$. In particular it is not of dimension one. -/
theorem two_le_rank_detQuotient : 2 ≤ Module.rank ℂ (detQuotient θ hθ hχ hθχ).V := by
  obtain ⟨x, y, h⟩ := detQuotient_exists_linearIndependent hχ hθχ (hθ := hθ)
  simpa using h.cardinal_lift_le_rank

/-- The quotient of $\mathrm{Ind}_B^G \theta$ by the line of $\chi \circ \det$ is not isomorphic to a representation of dimension one given by a character. -/
theorem detQuotient_not_iso_charRep (θ' : GL (Fin 2) K →* ℂˣ)
    (hθ' : IsOpen (θ'.ker : Set (GL (Fin 2) K))) :
    ¬ (detQuotient θ hθ hχ hθχ).Iso (charRep θ' hθ') := by
  rintro ⟨e, -⟩
  obtain ⟨x, y, h⟩ := detQuotient_exists_linearIndependent hχ hθχ (hθ := hθ)
  have : FiniteDimensional ℂ (charRep θ' hθ').V := inferInstanceAs (FiniteDimensional ℂ (ULift.{u} ℂ))
  have h2 := (h.map' e.toLinearMap e.ker).fintype_card_le_finrank
  have h1 : Module.finrank ℂ (charRep θ' hθ').V = 1 := by
    change Module.finrank ℂ (ULift.{u} ℂ) = 1
    rw [ULift.moduleEquiv.finrank_eq, Module.finrank_self]
  rw [h1, Fintype.card_fin] at h2
  omega

end DetVector

section Normalized

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The character $\chi \otimes \chi$ of $B$ is $b \mapsto \chi(\det b)$, since $\det b = ad$ for $b$ with diagonal $(a, d)$. -/
theorem borelChar_self_apply (χ : Kˣ →* ℂˣ) (b : GL2.borel K) :
    borelChar χ χ b = detChar K 2 χ b := by
  rw [borelChar_apply, ← map_mul]
  change χ _ = χ (Matrix.GeneralLinearGroup.det (b : GL (Fin 2) K))
  congr 1
  refine Units.ext ?_
  rw [Units.val_mul, val_diagFst, val_diagSnd, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, (mem_borel _).1 b.2, mul_zero, sub_zero]

/-- The unnormalized principal series $\mathrm{Ind}_B^G(\chi \otimes \chi)$ is not irreducible: it contains the line of $\chi \circ \det$. -/
theorem principalSeriesInd_not_isIrreducible {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) :
    ¬ (principalSeriesInd χ χ hχ hχ).IsIrreducible :=
  ind_not_isIrreducible (θ := borelChar χ χ) (hθ := isOpen_ker_borelChar hχ hχ) hχ
    (borelChar_self_apply χ)

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- If $\chi_2 = \chi_1 |\cdot|$, then the character $(\chi_1 \otimes \chi_2)\delta_B^{1/2}$ of $B$ is $b \mapsto \chi(\det b)$ with $\chi = \chi_1 |\cdot|^{1/2}$. Both sides are $\chi_1(ad)|ad|^{1/2}$. -/
theorem borelChar_mul_sqrtModulus_eq_detChar (h : χ₂ = χ₁ * absChar K) (b : GL2.borel K) :
    (borelChar χ₁ χ₂ * sqrtModulus K) b = detChar K 2 (χ₁ * sqrtAbsChar K) b := by
  have e : χ₂ * (sqrtAbsChar K)⁻¹ = χ₁ * sqrtAbsChar K := by
    rw [h, ← sqrtAbsChar_sq]
    ext x
    simp [pow_two, mul_assoc]
  rw [borelChar_mul_sqrtModulus, e, borelChar_self_apply]

/-- The reducible case, first part. Let $\chi_2 = \chi_1 |\cdot|$, that is, $\chi_1 \chi_2^{-1} = |\cdot|^{-1}$, and put $\chi = \chi_1 |\cdot|^{1/2}$. Then the function $g \mapsto \chi(\det g)$ is a nonzero vector of the normalized principal series, and $G$ acts on it by the character $\chi \circ \det$. -/
theorem normPrincipalSeries_exists_detVec (h : χ₂ = χ₁ * absChar K) :
    ∃ f : (Π).V, f ≠ 0 ∧
      (∀ g, ind.toFun f g = ULift.up (detChar K 2 (χ₁ * sqrtAbsChar K) g : ℂ)) ∧
      ∀ g, (Π).ρ g f = (detChar K 2 (χ₁ * sqrtAbsChar K) g : ℂ) • f :=
  ⟨detVec _ (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (borelChar_mul_sqrtModulus_eq_detChar h),
    detVec_ne_zero _ _, fun _ => rfl, ρ_detVec _ _⟩

/-- If $\chi_2 = \chi_1 |\cdot|$, then the normalized principal series has a $G$-stable subspace of dimension $1$ that is not the whole space: the line of $\chi \circ \det$ with $\chi = \chi_1 |\cdot|^{1/2}$. -/
theorem normPrincipalSeries_exists_stable_finrank_one (h : χ₂ = χ₁ * absChar K) :
    ∃ W : Submodule ℂ (Π).V, IsStableSubspace (Π).ρ W ∧ Module.finrank ℂ W = 1 ∧ W ≠ ⊤ :=
  ⟨detLine _ (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (borelChar_mul_sqrtModulus_eq_detChar h),
    detLine_stable _ _, finrank_detLine _ _, detLine_ne_top _ _⟩

/-- If $\chi_2 = \chi_1 |\cdot|$, then the character $\chi \circ \det$ with $\chi = \chi_1 |\cdot|^{1/2}$ has a nonzero map of representations to the normalized principal series. -/
theorem normPrincipalSeries_hasHom_detChar (h : χ₂ = χ₁ * absChar K) :
    (charRep (detChar K 2 (χ₁ * sqrtAbsChar K))
      (isOpen_ker_detChar K 2 _ (hχ₁.mul isSmoothChar_sqrtAbsChar))).HasHom (Π) :=
  hasHom_detChar_ind (θ := borelChar χ₁ χ₂ * sqrtModulus K)
    (hθ := isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
    (borelChar_mul_sqrtModulus_eq_detChar h)

/-- The reducible case: if $\chi_2 = \chi_1 |\cdot|$, then the normalized principal series of $(\chi_1, \chi_2)$ is not irreducible. -/
theorem normPrincipalSeries_not_isIrreducible (h : χ₂ = χ₁ * absChar K) : ¬ (Π).IsIrreducible :=
  ind_not_isIrreducible (θ := borelChar χ₁ χ₂ * sqrtModulus K)
    (hθ := isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
    (borelChar_mul_sqrtModulus_eq_detChar h)

/-- The criterion in the case $\chi_1 \neq \chi_2 |\cdot|$: the normalized principal series of $(\chi_1, \chi_2)$ is irreducible exactly when $\chi_2 \neq \chi_1 |\cdot|$. The case $\chi_1 = \chi_2 |\cdot|$ is not covered. -/
theorem normPrincipalSeries_isIrreducible_iff_of_ne (h₁ : χ₁ ≠ χ₂ * absChar K) :
    (Π).IsIrreducible ↔ χ₂ ≠ χ₁ * absChar K :=
  ⟨fun hirr h => normPrincipalSeries_not_isIrreducible h hirr,
    normPrincipalSeries_irreducible h₁⟩

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The twisted Steinberg representation $\chi \mathrm{St}$ with $\chi = \chi_1 |\cdot|^{1/2}$, for $\chi_2 = \chi_1 |\cdot|$: the quotient of the normalized principal series of $(\chi_1, \chi_2)$ by the line of $\chi \circ \det$. -/
noncomputable def steinbergQuotient (h : χ₂ = χ₁ * absChar K) : SmoothRep (GL (Fin 2) K) :=
  detQuotient (borelChar χ₁ χ₂ * sqrtModulus K) (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂)
    (hχ₁.mul isSmoothChar_sqrtAbsChar) (borelChar_mul_sqrtModulus_eq_detChar h)

/-- The twisted Steinberg quotient has rank at least $2$. -/
theorem two_le_rank_steinbergQuotient (h : χ₂ = χ₁ * absChar K) :
    2 ≤ Module.rank ℂ (steinbergQuotient χ₁ χ₂ hχ₁ hχ₂ h).V :=
  two_le_rank_detQuotient _ _

/-- The twisted Steinberg quotient is not of dimension one: it is not isomorphic to a representation given by a character of $G$. -/
theorem steinbergQuotient_not_iso_charRep (h : χ₂ = χ₁ * absChar K) (θ : GL (Fin 2) K →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set (GL (Fin 2) K))) :
    ¬ (steinbergQuotient χ₁ χ₂ hχ₁ hχ₂ h).Iso (charRep θ hθ) :=
  detQuotient_not_iso_charRep _ _ θ hθ

end Normalized

end Langlands
