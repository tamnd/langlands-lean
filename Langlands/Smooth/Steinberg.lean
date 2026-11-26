/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.ReducibleQuotient

/-!
# The twisted Steinberg representation of $GL_2$

Let $K$ be a nonarchimedean local field and $G = GL_2(K)$. Let $\chi_1, \chi_2$ be smooth characters of $K^\times$ with $\chi_2 = \chi_1 |\cdot|$, and let $\chi = \chi_1 |\cdot|^{1/2}$. The file `Langlands/Smooth/ReducibleCase.lean` shows that the line of $\chi \circ \det$ is a stable subspace of the normalized principal series, and calls the quotient by this line the twisted Steinberg quotient. This file proves that this quotient is irreducible, and that the line of $\chi \circ \det$ is the only stable subspace that is neither $0$ nor the whole space. Thus the normalized principal series has length $2$ in this case.

## Main definitions

* `Langlands.selfDetVec`: the vector $g \mapsto \chi(\det g)$ of the unnormalized principal series $\mathrm{Ind}_B^G(\chi \otimes \chi)$.
* `Langlands.selfDetLine`: the line spanned by `Langlands.selfDetVec`.

## Main results

* `Langlands.principalSeriesInd_self_exists_decomp`: modulo $V(N)$, each $f$ is $f(1) f_0 + c f_1$, with $f_1$ an eigenvector of the torus for the big cell character.
* `Langlands.eq_top_of_selfDetLine_le`: a stable subspace that contains the line of $\chi \circ \det$ and is larger than it is the whole space.
* `Langlands.selfDetVec_mem_of_sup_eq_top`: a stable complement of the line contains $\chi \circ \det$, so no stable complement exists.
* `Langlands.stable_eq_selfDetLine`: a stable subspace of $\mathrm{Ind}_B^G(\chi \otimes \chi)$ that is neither $0$ nor the whole space is the line of $\chi \circ \det$.
* `Langlands.quotient_selfDetLine_isIrreducible`, `Langlands.detQuotient_isIrreducible_of_eq`: the quotient by this line is irreducible.
* `Langlands.steinbergQuotient_isIrreducible`: for $\chi_2 = \chi_1 |\cdot|$, the twisted Steinberg quotient is irreducible.
* `Langlands.normPrincipalSeries_stable_eq_detLine`, `Langlands.normPrincipalSeries_isStableSubspace_iff`, `Langlands.normPrincipalSeries_existsUnique_stable`: for $\chi_2 = \chi_1 |\cdot|$, the stable subspaces of the normalized principal series are $0$, the line of $\chi \circ \det$ and the whole space, so the length is $2$.

## Method

Let $W$ be a stable subspace. If $W$ contains the line $L$ of $\chi \circ \det$ and is larger than $L$, then $W$ meets the big cell part, so $W$ contains $V(N)$. Modulo $V(N)$ the space is spanned by $f_0 = \chi \circ \det$ and an eigenvector $f_1$ for the character $\beta$ of the big cell. If $f_1 \notin W$, the class of $f_1$ in $V / W$ is a multiple of the class of $f_0$, so the torus acts on it by both $\chi \circ \det$ and $\beta$. The Weyl element then gives $\beta(w t w) = \beta(t)$, and $t = \mathrm{diag}(x, 1)$ gives $|x|^2 = 1$ for all $x$, which is false. Thus $W$ is the whole space. If $W \neq 0$ does not contain $L$, then $W + L$ is the whole space, and $V / W$ is the character $\chi \circ \det$. The same Weyl argument shows that $f_0 \in W$, which is a contradiction. The normalized case follows by the identity $(\chi_1 \otimes \chi_2) \delta_B^{1/2} = (\chi \otimes \chi)$.

## Open parts

The other reducible case, $\chi_1 = \chi_2 |\cdot|$, is not proved. There $\chi \circ \det$ is a quotient and not a subspace, and the unique proper nonzero stable subspace is the kernel of the map onto it. A proof without integration would show that each nonzero stable subspace contains $V(N)$ and the torus eigenvector for $\chi_1 \otimes \chi_2$ modulo $V(N)$, but this is not done here. The file also does not give a name to $\chi \mathrm{St}$ apart from the quotient of `Langlands/Smooth/ReducibleCase.lean`.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
-/

universe u

open Representation Matrix

namespace Langlands

section Absolute

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- There is an element $x$ of $K^\times$ with $|x|^2 \neq 1$. -/
theorem exists_absChar_sq_ne_one : ∃ x : Kˣ, (absChar K x : ℂ) * absChar K x ≠ 1 ∧
    (absChar K x : ℂ) ≠ 1 := by
  obtain ⟨x, hx⟩ : ∃ x : Kˣ, absChar K x ≠ 1 := by
    by_contra hc
    push Not at hc
    exact absChar_ne_one (MonoidHom.ext hc)
  have hx' : (absChar K x : ℂ) ≠ 1 := fun h => hx (Units.ext h)
  refine ⟨x, fun h => hx' ?_, hx'⟩
  rw [absChar_apply] at h hx' ⊢
  have hp := normAbs_pos x.ne_zero
  have h2 : normAbs K (x : K) * normAbs K (x : K) = 1 := by exact_mod_cast h
  have h3 : normAbs K (x : K) = 1 := by nlinarith
  rw [h3, Complex.ofReal_one]

end Absolute

namespace GL2

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The conjugate $w \, \mathrm{diag}(a, d) \, w$ by the Weyl element is $\mathrm{diag}(d, a)$. -/
theorem weyl_mul_diagTorus_mul_weyl (a d : Kˣ) :
    (weyl : GL (Fin 2) K) * (diagTorus K a d : GL (Fin 2) K) * weyl = (diagTorus K d a : GL (Fin 2) K) := by
  refine Units.ext ?_
  change weyl.1 * (diagTorus K a d : GL (Fin 2) K).1 * weyl.1 = (diagTorus K d a : GL (Fin 2) K).1
  rw [weyl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTorus, Matrix.mul_apply, Fin.sum_univ_two]

end GL2

section QuotientClass

variable {G : Type u} [Group G] {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Let $W$ be a stable subspace. If $v \equiv c u$ modulo $W$, then $g v \equiv c \, g u$ modulo $W$ for each $g$. -/
theorem quotient_mk_ρ_eq {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsStableSubspace ρ W) (g : G) {v u : V} {c : ℂ}
    (h : (Submodule.Quotient.mk v : V ⧸ W) = c • Submodule.Quotient.mk u) :
    (Submodule.Quotient.mk (ρ g v) : V ⧸ W) = c • Submodule.Quotient.mk (ρ g u) := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
  have := hW g h
  rwa [Submodule.mem_comap, map_sub, map_smul] at this

end QuotientClass

section Core

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

variable {χ : Kˣ →* ℂˣ} {hχ : IsSmoothChar K χ}

local notation "Ψ" => principalSeriesInd χ χ hχ hχ

local notation "ev" => principalSeriesJacquetEval χ χ hχ hχ

local notation "mk" => SmoothRep.jacquetMk (principalSeriesInd χ χ hχ hχ) (unipotent K) (torus K)
  torus_le_normalizer_unipotent

local notation "VN" => SmoothRep.jacquetKer (principalSeriesInd χ χ hχ hχ) (unipotent K)

local notation "Vw" => principalSeriesBigCell χ χ hχ hχ

variable (hχ) in
/-- The vector $\chi \circ \det$ of $\mathrm{Ind}_B^G(\chi \otimes \chi)$. -/
noncomputable def selfDetVec : (Ψ).V :=
  detVec (borelChar χ χ) (isOpen_ker_borelChar hχ hχ) hχ (borelChar_self_apply χ)

variable (hχ) in
/-- The line spanned by $\chi \circ \det$ in $\mathrm{Ind}_B^G(\chi \otimes \chi)$. -/
noncomputable def selfDetLine : Submodule ℂ (Ψ).V :=
  ℂ ∙ selfDetVec hχ

local notation "L" => selfDetLine hχ

local notation "f₀" => selfDetVec hχ

/-- The value of $\chi \circ \det$ at $g$ is $\chi(\det g)$. -/
theorem selfDetVec_apply (g : GL (Fin 2) K) :
    (ind.toFun f₀ g).down = (detChar K 2 χ g : ℂ) :=
  rfl

/-- The vector $\chi \circ \det$ has the value $1$ at $1$. -/
theorem selfDetVec_apply_one : (ind.toFun f₀ 1).down = 1 := by
  rw [selfDetVec_apply, map_one, Units.val_one]

/-- The structure of $\mathrm{Ind}_B^G(\chi \otimes \chi)$ modulo $V(N)$. There is a vector $f_1$ with $t f_1 \equiv \beta(t) f_1$ modulo $V(N)$ for each $t \in T$, where $\beta$ is `bigCellChar`, and each $f$ is congruent to $f(1) f_0 + c f_1$ modulo $V(N)$, where $f_0 = \chi \circ \det$. -/
theorem principalSeriesInd_self_exists_decomp : ∃ f₁ : (Ψ).V,
    (∀ t : torus K, (Ψ).ρ (t : GL (Fin 2) K) f₁ - (bigCellChar χ χ t : ℂ) • f₁ ∈ VN) ∧
    ∀ f : (Ψ).V, ∃ c : ℂ, f - (ind.toFun f 1).down • f₀ - c • f₁ ∈ VN := by
  obtain ⟨x₀, y₁, -, -, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := χ) (χ₂ := χ) (hχ₁ := hχ) (hχ₂ := hχ)
  obtain ⟨f₁, hf₁⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent y₁
  obtain ⟨c₀, hc₀⟩ := hspan (mk f₀)
  have he0 : (ev (mk f₀)).down = 1 := selfDetVec_apply_one (hχ := hχ)
  rw [he0, one_smul] at hc₀
  refine ⟨f₁, fun t => ?_, fun f => ?_⟩
  · rw [← (Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, map_smul,
      (Ψ).jacquetMk_ρ torus_le_normalizer_unipotent t, hf₁]
    exact sub_eq_zero.2 (hρy t)
  · obtain ⟨c, hc⟩ := hspan (mk f)
    refine ⟨c - (ind.toFun f 1).down * c₀, ?_⟩
    have hev : (ev (mk f)).down = (ind.toFun f 1).down := rfl
    rw [hev] at hc
    rw [← (Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, map_sub, map_smul,
      map_smul, hf₁, hc, hc₀]
    generalize (ind.toFun f 1).down = a at *
    change (a • x₀ + c • y₁ - a • (x₀ + c₀ • y₁) - (c - a * c₀) • y₁ :
      (principalSeriesJacquet χ χ hχ hχ).V) = 0
    module

/-- Let $W$ be a stable subspace of $\mathrm{Ind}_B^G(\chi \otimes \chi)$ that contains the line of $\chi \circ \det$ and is not contained in it. Then $W$ contains $V(N)$. For $f \in W$ outside the line, $f - f(1) f_0$ is a nonzero vector of $W$ that vanishes at $1$, so $W$ meets the big cell subspace $V_w$. -/
theorem jacquetKer_le_of_detLine_le {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W)
    (hL : L ≤ W) (hWL : ¬ W ≤ L) : VN ≤ W := by
  obtain ⟨f, hfW, hfL⟩ := Set.not_subset.1 hWL
  refine jacquetKer_le_of_inf_ne_bot hW fun hb => hfL ?_
  have hf₀ : f₀ ∈ L := Submodule.mem_span_singleton_self _
  have hmem : f - (ind.toFun f 1).down • f₀ ∈ W ⊓ Vw := by
    refine Submodule.mem_inf.2 ⟨W.sub_mem hfW (W.smul_mem _ (hL hf₀)), ?_⟩
    change ind.toFun (f - (ind.toFun f 1).down • f₀) 1 = 0
    apply ULift.ext
    change (ind.toFun f 1).down - (ind.toFun f 1).down * (ind.toFun f₀ 1).down = 0
    rw [selfDetVec_apply_one (hχ := hχ), mul_one, sub_self]
  rw [hb, Submodule.mem_bot, sub_eq_zero] at hmem
  rw [hmem]
  exact Submodule.smul_mem _ _ hf₀

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- On the torus, the character $\chi \circ \det$ is $\chi \otimes \chi$. -/
theorem detChar_torus (t : torus K) :
    detChar K 2 χ (t : GL (Fin 2) K) = torusChar χ χ t :=
  (borelChar_self_apply χ ⟨t, torus_le_borel t.2⟩).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- On the unipotent radical $N$, the character $\chi \circ \det$ is trivial. -/
theorem detChar_unipotent {n : GL (Fin 2) K} (hn : n ∈ unipotent K) :
    (detChar K 2 χ n : ℂ) = 1 := by
  rw [← borelChar_self_apply χ ⟨n, unipotent_le_borel hn⟩, borelChar_unipotent χ χ _ hn,
    Units.val_one]

/-- The values of `bigCellChar` for $(\chi, \chi)$ at $\mathrm{diag}(x, 1)$ and $\mathrm{diag}(1, x)$ are $\chi(x)|x|$ and $\chi(x)|x|^{-1}$. -/
theorem bigCellChar_self_diagTorus (x : Kˣ) :
    (bigCellChar χ χ (diagTorus K x 1) : ℂ) = χ x * absChar K x ∧
      (bigCellChar χ χ (diagTorus K 1 x) : ℂ) = χ x * (absChar K x)⁻¹ := by
  simp [bigCellChar, torusChar_diagTorus]

/-- Let $W$ be a stable subspace of $\mathrm{Ind}_B^G(\chi \otimes \chi)$ that contains the line of $\chi \circ \det$ and is not contained in it. Then $W$ is the whole space. Suppose not. Then $W$ contains $V(N)$, and $V / W$ is spanned by the class of $f_1$, on which $t \in T$ acts by $\beta(t)$. The Weyl element $w$ acts on this line by a scalar, so $\beta(w t w) = \beta(t)$. For $t = \mathrm{diag}(x, 1)$ this gives $|x|^2 = 1$ for each $x$, which is false. -/
theorem eq_top_of_selfDetLine_le {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W)
    (hL : L ≤ W) (hWL : ¬ W ≤ L) : W = ⊤ := by
  have hN := jacquetKer_le_of_detLine_le hW hL hWL
  obtain ⟨f₁, hf₁t, hdec⟩ := principalSeriesInd_self_exists_decomp (hχ := hχ)
  have hf₀ : f₀ ∈ W := hL (Submodule.mem_span_singleton_self _)
  have hq : ∀ v, ∃ c : ℂ,
      (Submodule.Quotient.mk v : (Ψ).V ⧸ W) = c • Submodule.Quotient.mk f₁ := by
    intro v
    obtain ⟨c, hc⟩ := hdec v
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have := W.add_mem (hN hc) (W.smul_mem (ind.toFun v 1).down hf₀)
    rwa [sub_right_comm, sub_add_cancel] at this
  by_contra htop
  have hf₁ : f₁ ∉ W := by
    intro hf₁
    refine htop (eq_top_iff.2 fun v _ => ?_)
    obtain ⟨c, hc⟩ := hq v
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hc
    simpa using W.add_mem hc (W.smul_mem c hf₁)
  have hne : (Submodule.Quotient.mk f₁ : (Ψ).V ⧸ W) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hT : ∀ t : torus K, (Submodule.Quotient.mk ((Ψ).ρ (t : GL (Fin 2) K) f₁) : (Ψ).V ⧸ W) =
      (bigCellChar χ χ t : ℂ) • Submodule.Quotient.mk f₁ := fun t => by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hN (hf₁t t)
  obtain ⟨c, hc⟩ := hq ((Ψ).ρ weyl f₁)
  have h1 : (Submodule.Quotient.mk f₁ : (Ψ).V ⧸ W) = (c * c) • Submodule.Quotient.mk f₁ := by
    have := quotient_mk_ρ_eq hW weyl hc
    rwa [← Module.End.mul_apply, ← map_mul, weyl_mul_weyl, map_one, Module.End.one_apply, hc,
      smul_smul] at this
  have hcc : c * c = 1 := (smul_left_injective ℂ hne
    (show (1 : ℂ) • _ = (c * c) • _ by rw [one_smul]; exact h1)).symm
  obtain ⟨x, hx, -⟩ := exists_absChar_sq_ne_one (K := K)
  have h3 := quotient_mk_ρ_eq hW (diagTorus K x 1 : GL (Fin 2) K) hc
  rw [hT, smul_smul] at h3
  have h4 := quotient_mk_ρ_eq hW weyl h3
  rw [hc, smul_smul] at h4
  have e : (Ψ).ρ weyl ((Ψ).ρ (diagTorus K x 1 : GL (Fin 2) K) ((Ψ).ρ weyl f₁)) =
      (Ψ).ρ (diagTorus K 1 x : GL (Fin 2) K) f₁ := by
    rw [← weyl_mul_diagTorus_mul_weyl x 1, map_mul, map_mul]
    rfl
  rw [e, hT] at h4
  have h5 := smul_left_injective ℂ hne h4
  obtain ⟨b1, b2⟩ := bigCellChar_self_diagTorus (χ := χ) x
  rw [b1, b2] at h5
  apply hx
  have hχx : (χ x : ℂ) ≠ 0 := Units.ne_zero _
  have hax : (absChar K x : ℂ) ≠ 0 := Units.ne_zero _
  have h6 : (χ x : ℂ) * (absChar K x)⁻¹ = (χ x : ℂ) * absChar K x := by
    rw [h5]
    linear_combination (χ x * (absChar K x : ℂ)) * hcc
  rw [Units.val_inv_eq_inv_val, eq_comm] at h6
  exact (mul_eq_one_iff_eq_inv₀ hax).2 (mul_left_cancel₀ hχx h6)

/-- The line of $\chi \circ \det$ has no stable complement in $\mathrm{Ind}_B^G(\chi \otimes \chi)$: a stable subspace $W$ with $W + \mathbb{C} f_0 = V$ contains $f_0$. Suppose not. Then $V / W$ is the character $\chi \circ \det$, so $W$ contains $V(N)$. The class of $f_1$ is $c f_0$ with $c \beta(t) = c \chi(\det t)$, so $c = 0$, and $f \equiv f(1) f_0$ modulo $W$ for each $f$. Then $f(g) = \chi(\det g) f(1)$ for each $f$ and $g$, so $V = \mathbb{C} f_0$, which is false. -/
theorem selfDetVec_mem_of_sup_eq_top {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W)
    (htop : W ⊔ L = ⊤) : f₀ ∈ W := by
  by_contra hf₀
  obtain ⟨f₁, hf₁t, hdec⟩ := principalSeriesInd_self_exists_decomp (hχ := hχ)
  have hq : ∀ v, ∃ c : ℂ,
      (Submodule.Quotient.mk v : (Ψ).V ⧸ W) = c • Submodule.Quotient.mk f₀ := by
    intro v
    obtain ⟨w, hw, l, hl, hwl⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : v ∈ W ⊔ L)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hl
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← hwl, add_sub_cancel_right]
    exact hw
  have hne : (Submodule.Quotient.mk f₀ : (Ψ).V ⧸ W) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hG : ∀ g, (Submodule.Quotient.mk ((Ψ).ρ g f₀) : (Ψ).V ⧸ W) =
      (detChar K 2 χ g : ℂ) • Submodule.Quotient.mk f₀ := fun g => by
    rw [← Submodule.Quotient.mk_smul]
    exact congrArg _ (ρ_detVec _ _ g)
  have hN : VN ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨n, v⟩, rfl⟩
    obtain ⟨c, hc⟩ := hq v
    have h1 := quotient_mk_ρ_eq hW (n : GL (Fin 2) K) hc
    rw [hG, detChar_unipotent n.2, one_smul, ← hc] at h1
    change (Ψ).ρ (n : GL (Fin 2) K) v - v ∈ W
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact h1
  obtain ⟨c₁, hc₁⟩ := hq f₁
  obtain ⟨x, -, hx⟩ := exists_absChar_sq_ne_one (K := K)
  have hA : (Submodule.Quotient.mk ((Ψ).ρ (diagTorus K x 1 : GL (Fin 2) K) f₁) : (Ψ).V ⧸ W) =
      (bigCellChar χ χ (diagTorus K x 1) : ℂ) • Submodule.Quotient.mk f₁ := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hN (hf₁t _)
  have hB := quotient_mk_ρ_eq hW (diagTorus K x 1 : GL (Fin 2) K) hc₁
  rw [hG, hA, hc₁, smul_smul, smul_smul, detChar_torus] at hB
  have hs := smul_left_injective ℂ hne hB
  rw [(bigCellChar_self_diagTorus x).1, torusChar_diagTorus] at hs
  have hc0 : c₁ = 0 := by
    by_contra hc0
    apply hx
    have hχx : (χ x : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_one, mul_one] at hs
    have : (χ x : ℂ) * absChar K x = χ x := mul_left_cancel₀ hc0 (by rw [← hs]; ring)
    calc (absChar K x : ℂ) = (χ x : ℂ) * absChar K x / χ x := by field_simp
      _ = 1 := by rw [this, div_self hχx]
  rw [hc0, zero_smul] at hc₁
  have hv : ∀ v : (Ψ).V, (Submodule.Quotient.mk v : (Ψ).V ⧸ W) =
      (ind.toFun v 1).down • Submodule.Quotient.mk f₀ := by
    intro v
    obtain ⟨c, hc⟩ := hdec v
    have := (Submodule.Quotient.mk_eq_zero W).2 (hN hc)
    rwa [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_smul, hc₁, smul_zero, sub_zero, sub_eq_zero] at this
  have hLtop : L = ⊤ := by
    refine eq_top_iff.2 fun v _ => Submodule.mem_span_singleton.2 ⟨(ind.toFun v 1).down, ?_⟩
    apply ind.toFun_injective
    funext g
    apply ULift.ext
    have h1 := hv ((Ψ).ρ g v)
    rw [quotient_mk_ρ_eq hW g (hv v), hG, smul_smul] at h1
    have h2 := smul_left_injective ℂ hne h1
    change (ind.toFun v 1).down * (detChar K 2 χ g : ℂ) = (ind.toFun v g).down
    rw [h2]
    change (ind.toFun v (1 * g)).down = _
    rw [one_mul]
  exact detLine_ne_top (θ := borelChar χ χ) (hθ := isOpen_ker_borelChar hχ hχ) hχ
    (borelChar_self_apply χ) hLtop

/-- The line of $\chi \circ \det$ is a stable subspace. -/
theorem selfDetLine_stable : IsStableSubspace (Ψ).ρ L :=
  detLine_stable hχ (borelChar_self_apply χ)

/-- The composition series of $\mathrm{Ind}_B^G(\chi \otimes \chi)$: a stable subspace that is neither $0$ nor the whole space is the line of $\chi \circ \det$. -/
theorem stable_eq_selfDetLine {W : Submodule ℂ (Ψ).V} (hW : IsStableSubspace (Ψ).ρ W)
    (h0 : W ≠ ⊥) (htop : W ≠ ⊤) : W = L := by
  by_cases hle : W ≤ L
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hle hw)
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw0 (zero_smul _ _)
    refine le_antisymm hle (Submodule.span_le.2 ?_)
    rintro _ rfl
    simpa [smul_smul, inv_mul_cancel₀ hc] using W.smul_mem c⁻¹ hw
  · exfalso
    have hS : IsStableSubspace (Ψ).ρ (W ⊔ L) := fun g =>
      sup_le ((hW g).trans (Submodule.comap_mono le_sup_left))
        ((selfDetLine_stable g).trans (Submodule.comap_mono le_sup_right))
    have hsup := eq_top_of_selfDetLine_le hS le_sup_right fun h => hle (le_sup_left.trans h)
    have hf₀ := selfDetVec_mem_of_sup_eq_top hW hsup
    have hLW : L ≤ W := Submodule.span_le.2 (by simpa using hf₀)
    rw [sup_eq_left.2 hLW] at hsup
    exact htop hsup

/-- The quotient of $\mathrm{Ind}_B^G(\chi \otimes \chi)$ by the line of $\chi \circ \det$ is irreducible. A stable subspace of the quotient is the image of a stable subspace $W$ that contains the line, and $W$ is the line or the whole space by `eq_top_of_selfDetLine_le`. -/
theorem quotient_selfDetLine_isIrreducible :
    ((Ψ).quotient L selfDetLine_stable).IsIrreducible := by
  obtain ⟨x, y, hxy⟩ := detQuotient_exists_linearIndependent hχ (borelChar_self_apply χ)
    (θ := borelChar χ χ) (hθ := isOpen_ker_borelChar hχ hχ)
  have hnt : Nontrivial (detQuotient (borelChar χ χ) (isOpen_ker_borelChar hχ hχ) hχ
      (borelChar_self_apply χ)).V := nontrivial_of_ne x 0 (by simpa using hxy.ne_zero 0)
  refine ⟨hnt, fun W' hW' => ?_⟩
  set W : Submodule ℂ (Ψ).V := W'.comap (Submodule.mkQ L)
  have hW : IsStableSubspace (Ψ).ρ W := fun g _ hv => hW' g hv
  have hL : L ≤ W := fun v hv => by
    change Submodule.Quotient.mk v ∈ W'
    rw [(Submodule.Quotient.mk_eq_zero _).2 hv]
    exact W'.zero_mem
  by_cases hWL : W ≤ L
  · refine Or.inl ((Submodule.eq_bot_iff _).2 fun x hx => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 (hWL hx)
  · have htop := eq_top_of_selfDetLine_le hW hL hWL
    refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    exact hv

end Core


section Normalized

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- Let $\theta = \chi \otimes \chi$ as characters of $B$. Then the quotient of $\mathrm{Ind}_B^G \theta$ by the line of $\chi \circ \det$ is irreducible. -/
theorem detQuotient_isIrreducible_of_eq {θ : borel K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (borel K))}
    {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hθχ : ∀ b : borel K, θ b = detChar K 2 χ b)
    (he : θ = borelChar χ χ) : (detQuotient θ hθ hχ hθχ).IsIrreducible := by
  subst he
  exact quotient_selfDetLine_isIrreducible (hχ := hχ)

/-- Let $\theta = \chi \otimes \chi$ as characters of $B$. Then a stable subspace of $\mathrm{Ind}_B^G \theta$ that is neither $0$ nor the whole space is the line of $\chi \circ \det$. -/
theorem stable_eq_detLine_of_eq {θ : borel K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (borel K))}
    {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hθχ : ∀ b : borel K, θ b = detChar K 2 χ b)
    (he : θ = borelChar χ χ) {W : Submodule ℂ (ind (borel K) (charRep θ hθ)).V}
    (hW : IsStableSubspace (ind (borel K) (charRep θ hθ)).ρ W) (h0 : W ≠ ⊥) (htop : W ≠ ⊤) :
    W = detLine θ hθ hχ hθχ := by
  subst he
  exact stable_eq_selfDetLine hW h0 htop

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- If $\chi_2 = \chi_1 |\cdot|$, then $(\chi_1 \otimes \chi_2)\delta_B^{1/2} = \chi \otimes \chi$ with $\chi = \chi_1 |\cdot|^{1/2}$. -/
theorem borelChar_mul_sqrtModulus_eq_self (h : χ₂ = χ₁ * absChar K) :
    borelChar χ₁ χ₂ * sqrtModulus K =
      borelChar (χ₁ * sqrtAbsChar K) (χ₁ * sqrtAbsChar K) := by
  rw [borelChar_mul_sqrtModulus]
  congr 1
  rw [h, ← sqrtAbsChar_sq]
  ext x
  simp [pow_two, mul_assoc]

/-- The twisted Steinberg representation is irreducible: if $\chi_2 = \chi_1 |\cdot|$, then the quotient of the normalized principal series of $(\chi_1, \chi_2)$ by the line of $\chi \circ \det$, $\chi = \chi_1 |\cdot|^{1/2}$, is irreducible. -/
theorem steinbergQuotient_isIrreducible (h : χ₂ = χ₁ * absChar K) :
    (steinbergQuotient χ₁ χ₂ hχ₁ hχ₂ h).IsIrreducible :=
  detQuotient_isIrreducible_of_eq _ _ (borelChar_mul_sqrtModulus_eq_self h)

/-- Let $\chi_2 = \chi_1 |\cdot|$. Then a stable subspace of the normalized principal series of $(\chi_1, \chi_2)$ that is neither $0$ nor the whole space is the line of $\chi \circ \det$, $\chi = \chi_1 |\cdot|^{1/2}$. -/
theorem normPrincipalSeries_stable_eq_detLine (h : χ₂ = χ₁ * absChar K)
    {W : Submodule ℂ (Π).V} (hW : IsStableSubspace (Π).ρ W) (h0 : W ≠ ⊥) (htop : W ≠ ⊤) :
    W = detLine (borelChar χ₁ χ₂ * sqrtModulus K)
      (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (borelChar_mul_sqrtModulus_eq_detChar h) :=
  stable_eq_detLine_of_eq _ _ (borelChar_mul_sqrtModulus_eq_self h) hW h0 htop

/-- Let $\chi_2 = \chi_1 |\cdot|$. The stable subspaces of the normalized principal series of $(\chi_1, \chi_2)$ are exactly $0$, the line of $\chi \circ \det$ and the whole space. Thus the principal series has length $2$, with the character $\chi \circ \det$ as subrepresentation and $\chi \mathrm{St}$ as quotient. -/
theorem normPrincipalSeries_isStableSubspace_iff (h : χ₂ = χ₁ * absChar K)
    (W : Submodule ℂ (Π).V) :
    IsStableSubspace (Π).ρ W ↔ W = ⊥ ∨ W = detLine (borelChar χ₁ χ₂ * sqrtModulus K)
      (isOpen_ker_borelChar_mul_sqrtModulus hχ₁ hχ₂) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (borelChar_mul_sqrtModulus_eq_detChar h) ∨ W = ⊤ := by
  refine ⟨fun hW => ?_, ?_⟩
  · by_cases h0 : W = ⊥
    · exact Or.inl h0
    by_cases htop : W = ⊤
    · exact Or.inr (Or.inr htop)
    exact Or.inr (Or.inl (normPrincipalSeries_stable_eq_detLine h hW h0 htop))
  · rintro (rfl | rfl | rfl)
    · exact fun g _ hv => by
        rw [Submodule.mem_bot] at hv
        rw [hv]
        exact Submodule.zero_mem _
    · exact detLine_stable _ _
    · exact fun g _ _ => Submodule.mem_top

/-- Let $\chi_2 = \chi_1 |\cdot|$. Then the normalized principal series of $(\chi_1, \chi_2)$ has exactly one stable subspace that is neither $0$ nor the whole space. -/
theorem normPrincipalSeries_existsUnique_stable (h : χ₂ = χ₁ * absChar K) :
    ∃! W : Submodule ℂ (Π).V, IsStableSubspace (Π).ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤ :=
  ⟨_, ⟨detLine_stable _ _, detLine_ne_bot _ _, detLine_ne_top _ _⟩,
    fun _ hW => normPrincipalSeries_stable_eq_detLine h hW.1 hW.2.1 hW.2.2⟩

end Normalized

end Langlands
