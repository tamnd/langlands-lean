/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.Steinberg

/-!
# The reducible quotient case of the principal series of $GL_2$ has length two

Let $K$ be a nonarchimedean local field and $G = GL_2(K)$. Let $\chi_1, \chi_2$ be smooth characters of $K^\times$ with $\chi_1 = \chi_2 |\cdot|$. The file `Langlands/Smooth/ReducibleQuotient.lean` shows that the normalized principal series of $(\chi_1, \chi_2)$ is not irreducible. This file describes its stable subspaces. Let $\gamma = (\chi_1 \otimes \chi_2)\delta_B^{1/2}$ on the torus $T$, and let $W_0$ be the subspace of the vectors $f$ with $t f \equiv \gamma(t) f$ modulo $V(N)$ for each $t \in T$. Then $W_0$ is the only stable subspace that is neither $0$ nor the whole space, $W_0$ has codimension $1$, and $W_0$ is irreducible as a representation. Thus the normalized principal series has length $2$, and $W_0$ is the model of the twisted Steinberg representation in this case.

## Main definitions

* `Langlands.jacquetEigenSub`: for a smooth representation of $G$ and a character $\gamma$ of $T$, the subspace of the vectors $f$ with $t f - \gamma(t) f \in V(N)$ for each $t \in T$.
* `Langlands.normSteinbergSub`: the subspace $W_0$ of the normalized principal series.
* `Langlands.steinbergSub`: for $\chi_1 = \chi_2 |\cdot|$, the subrepresentation of the normalized principal series on $W_0$.

## Main results

* `Langlands.jacquetEigenSub_le_of_ne_bot`: if $\alpha_1 = \alpha_2 |\cdot|^2$, then each nonzero stable subspace of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ contains $W_0$.
* `Langlands.le_jacquetEigenSub_of_ne_top`: if $\alpha_1 = \alpha_2 |\cdot|^2$, then each stable subspace that is not the whole space is contained in $W_0$.
* `Langlands.stable_eq_jacquetEigenSub`, `Langlands.jacquetEigenSub_stable`: thus $W_0$ is stable, and it is the only stable subspace that is neither $0$ nor the whole space.
* `Langlands.finrank_quotient_jacquetEigenSub`: the subspace $W_0$ has codimension $1$.
* `Langlands.normPrincipalSeries_stable_eq_normSteinbergSub`, `Langlands.normPrincipalSeries_isStableSubspace_iff_of_eq_mul`, `Langlands.normPrincipalSeries_existsUnique_stable_of_eq_mul`: for $\chi_1 = \chi_2 |\cdot|$, the stable subspaces of the normalized principal series are exactly $0$, $W_0$ and the whole space.
* `Langlands.finrank_quotient_normSteinbergSub`: for $\chi_1 = \chi_2 |\cdot|$, the subspace $W_0$ of the normalized principal series has codimension $1$.
* `Langlands.ρ_sub_detChar_mem_jacquetEigenSub`, `Langlands.normPrincipalSeries_ρ_sub_detChar_mem_normSteinbergSub`: $G$ acts on the quotient $V / W_0$ by the character $\chi \circ \det$, with $\chi = \alpha_2 |\cdot| = \chi_2 |\cdot|^{1/2}$.
* `Langlands.steinbergSub_isIrreducible`: for $\chi_1 = \chi_2 |\cdot|$, the representation on $W_0$ is irreducible.

## Method

The normalized principal series is $V = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ with $\alpha_1 = \chi_1 |\cdot|^{1/2}$ and $\alpha_2 = \chi_2 |\cdot|^{-1/2}$, so $\alpha_1 = \alpha_2 |\cdot|^2$. Let $\gamma = \alpha_1 \otimes \alpha_2$ and $\beta = $ `Langlands.bigCellChar`. Let $W \neq 0$ be a stable subspace. Since $\alpha_1 \neq \alpha_2$, the space $W$ meets the big cell part $V_w$ by `Langlands.eq_of_inf_principalSeriesBigCell_eq_bot`, so $W$ contains $V(N)$. Then $N$ and the lower unipotent matrices act trivially on $V / W$, so $s = \mathrm{diag}(a, a^{-1})$ acts trivially on $V / W$. For $f \in W_0$ this gives $(\gamma(s) - 1) f \in W$, and $\gamma(s) = |a|^2 \neq 1$ for some $a$. Thus $W_0 \le W$. Modulo $V(N)$ the space is spanned by a torus eigenvector $f_0$ for $\gamma$ and a torus eigenvector $f_1$ for $\beta$. Choose $t_0$ with $\gamma(t_0) \neq \beta(t_0)$. The vector $f_0$ is a lift of $(t_0 - \beta(t_0)) x_0 / (\gamma(t_0) - \beta(t_0))$, where $x_0$ is a vector of the Jacquet module with value $1$ at $1$. Then $f_0 \in W_0$ and $f_1 \notin W_0$. If $W \neq V$, then $f_1 \notin W$, and each vector of $W$ is congruent to a multiple of $f_0$ modulo $V(N)$, so $W \le W_0$. The principal series has a proper nonzero stable subspace by `Langlands.principalSeriesInd_not_isIrreducible_of_eq_mul_sq`, so this subspace is $W_0$, and $W_0$ is stable. A nonzero stable subspace of $W_0$ contains $W_0$, so $W_0$ is irreducible. On the quotient $V / W_0$, each $g$ acts by a scalar. This scalar is $1$ on $N$ and $\beta = \chi \otimes \chi$ on $T$, and the Weyl element $w$ acts by a scalar $c$ with $c^2 = 1$. Thus the lower unipotent matrices act trivially. The identity $w = n(-1) \bar n(1) n(-1) \mathrm{diag}(1, -1)$ and the Bruhat decomposition then show that $g$ acts by $\chi(\det g)$.

## Open parts

The file does not prove that the representation on $W_0$ is isomorphic to the twist of the Steinberg quotient of `Langlands/Smooth/ReducibleCase.lean`.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
-/

universe u

open Representation Matrix

namespace Langlands

section EigenSubspace

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

/-- For a smooth representation $\pi$ of $GL_2(K)$ and a character $\gamma$ of the torus $T$, the subspace of the vectors $f$ with $\pi(t) f - \gamma(t) f \in V(N)$ for each $t \in T$. -/
def jacquetEigenSub (π : SmoothRep (GL (Fin 2) K)) (γ : torus K →* ℂˣ) : Submodule ℂ π.V where
  carrier := {f | ∀ t : torus K, π.ρ (t : GL (Fin 2) K) f - (γ t : ℂ) • f ∈ π.jacquetKer (unipotent K)}
  add_mem' {a b} ha hb t := by
    rw [map_add, smul_add, add_sub_add_comm]
    exact add_mem (ha t) (hb t)
  zero_mem' t := by
    rw [map_zero, smul_zero, sub_zero]
    exact zero_mem _
  smul_mem' c f hf t := by
    rw [map_smul, smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ c (hf t)

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Membership in `jacquetEigenSub`. -/
theorem mem_jacquetEigenSub {π : SmoothRep (GL (Fin 2) K)} {γ : torus K →* ℂˣ} {f : π.V} :
    f ∈ jacquetEigenSub π γ ↔
      ∀ t : torus K, π.ρ (t : GL (Fin 2) K) f - (γ t : ℂ) • f ∈ π.jacquetKer (unipotent K) :=
  Iff.rfl

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The subspace $V(N)$ is contained in `jacquetEigenSub`, since $V(N)$ is stable under $T$. -/
theorem jacquetKer_le_jacquetEigenSub (π : SmoothRep (GL (Fin 2) K)) (γ : torus K →* ℂˣ) :
    π.jacquetKer (unipotent K) ≤ jacquetEigenSub π γ := fun _ hv t =>
  sub_mem (π.jacquetKer_stable torus_le_normalizer_unipotent t hv) (Submodule.smul_mem _ _ hv)

end EigenSubspace

section Transfer

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let $W \neq 0$ be a stable subspace of $\pi$ that is contained in each nonzero stable subspace. Then the subrepresentation on $W$ is irreducible. A nonzero stable subspace $U$ of $W$ is a nonzero stable subspace of $\pi$, so $W \le U$. -/
theorem SmoothRep.sub_isIrreducible_of_le (π : SmoothRep G) {W : Submodule ℂ π.V}
    (hW : IsStableSubspace π.ρ W) (hW0 : W ≠ ⊥)
    (hmin : ∀ U : Submodule ℂ π.V, IsStableSubspace π.ρ U → U ≠ ⊥ → W ≤ U) :
    (π.sub W hW).IsIrreducible := by
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    exact ⟨⟨⟨w, hw⟩, 0, fun e => hw0 (congrArg Subtype.val e)⟩⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  have hS : IsStableSubspace π.ρ (U.map W.subtype) := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hU g hu, rfl⟩
  have hne : U.map W.subtype ≠ ⊥ := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    intro hb
    have hm : W.subtype u ∈ U.map W.subtype := Submodule.mem_map_of_mem hu
    rw [hb, Submodule.mem_bot] at hm
    exact hu0 (Subtype.ext hm)
  have hle := hmin _ hS hne
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨u, hu, hu'⟩ := hle w.2
  have e : u = w := Subtype.ext hu'
  rw [← e]
  exact hu

end Transfer

namespace GL2

variable {K : Type u} [Field K]

/-- The Weyl element is $w = n(-1) \, \bar n(1) \, n(-1) \, \mathrm{diag}(1, -1)$, a product of upper and lower unipotent matrices and a diagonal matrix. -/
theorem weyl_eq_unip_mul_lowerUnip :
    (weyl : GL (Fin 2) K) =
      unip (-1) * lowerUnip 1 * unip (-1) * ((diagTorus K 1 (-1) : torus K) : GL (Fin 2) K) := by
  apply Units.ext
  change !![(0 : K), 1; 1, 0] = !![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -1; 0, 1] *
    !![((1 : Kˣ) : K), 0; 0, ((-1 : Kˣ) : K)]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end GL2

section Core

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

variable {α₁ α₂ : Kˣ →* ℂˣ} {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}

local notation "Ψ" => principalSeriesInd α₁ α₂ hα₁ hα₂

local notation "ΨN" => principalSeriesJacquet α₁ α₂ hα₁ hα₂

local notation "ev" => principalSeriesJacquetEval α₁ α₂ hα₁ hα₂

local notation "mk" => SmoothRep.jacquetMk (principalSeriesInd α₁ α₂ hα₁ hα₂) (unipotent K)
  (torus K) torus_le_normalizer_unipotent

local notation "VN" => SmoothRep.jacquetKer (principalSeriesInd α₁ α₂ hα₁ hα₂) (unipotent K)

local notation "W₀" => jacquetEigenSub (principalSeriesInd α₁ α₂ hα₁ hα₂) (torusChar α₁ α₂)

/-- A vector $f$ is in $W_0$ exactly when its class in the Jacquet module is an eigenvector of $T$ for $\alpha_1 \otimes \alpha_2$. -/
theorem mem_jacquetEigenSub_iff_mk {f : (Ψ).V} :
    f ∈ W₀ ↔ ∀ t : torus K, (ΨN).ρ t (mk f) = (torusChar α₁ α₂ t : ℂ) • mk f :=
  forall_congr' fun t => by
    rw [← (Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, map_smul,
      (Ψ).jacquetMk_ρ torus_le_normalizer_unipotent t, sub_eq_zero]
    rfl

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $\alpha_1 \neq \alpha_2$, since $|x|^2 \neq 1$ for some $x$. -/
theorem ne_of_eq_mul_absChar_sq (h : α₁ = α₂ * absChar K ^ 2) : α₁ ≠ α₂ := by
  intro he
  obtain ⟨x, hx, -⟩ := exists_absChar_sq_ne_one (K := K)
  have h1 := DFunLike.congr_fun (he.symm.trans h) x
  rw [MonoidHom.mul_apply, pow_two, MonoidHom.mul_apply] at h1
  have h2 := mul_eq_left.1 h1.symm
  exact hx (by rw [← Units.val_mul, h2, Units.val_one])

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $(\alpha_1 \otimes \alpha_2)(\mathrm{diag}(a, a^{-1})) = |a|^2 \neq 1$ for some $a$. -/
theorem exists_torusChar_diagTorus_ne_one (h : α₁ = α₂ * absChar K ^ 2) :
    ∃ a : Kˣ, (torusChar α₁ α₂ (diagTorus K a a⁻¹) : ℂ) ≠ 1 := by
  obtain ⟨x, hx, -⟩ := exists_absChar_sq_ne_one (K := K)
  refine ⟨x, fun he => hx ?_⟩
  have he' : torusChar α₁ α₂ (diagTorus K x x⁻¹) = 1 := Units.ext he
  rw [torusChar_diagTorus, h, map_inv, MonoidHom.mul_apply, pow_two, MonoidHom.mul_apply] at he'
  have h2 := mul_eq_left.1 (mul_inv_eq_one.1 he')
  rw [← Units.val_mul, h2, Units.val_one]

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then the characters $\alpha_1 \otimes \alpha_2$ and `bigCellChar` of $T$ differ. -/
theorem exists_torusChar_ne_bigCellChar (h : α₁ = α₂ * absChar K ^ 2) :
    ∃ t, torusChar α₁ α₂ t ≠ bigCellChar α₁ α₂ t := by
  by_contra hc
  push Not at hc
  have he := (torusChar_inj.1 (MonoidHom.ext hc)).1
  apply absChar_ne_one (K := K)
  refine MonoidHom.ext fun x => ?_
  have h1 := DFunLike.congr_fun (h.symm.trans he) x
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, pow_two, MonoidHom.mul_apply,
    ← mul_assoc] at h1
  exact mul_eq_left.1 h1

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then a nonzero stable subspace $W$ of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ contains $V(N)$. Since $\alpha_1 \neq \alpha_2$, the space $W$ meets the big cell part $V_w$. -/
theorem jacquetKer_le_of_ne_bot (h : α₁ = α₂ * absChar K ^ 2) {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (h0 : W ≠ ⊥) : VN ≤ W :=
  jacquetKer_le_of_inf_ne_bot hW fun hb =>
    ne_of_eq_mul_absChar_sq h (eq_of_inf_principalSeriesBigCell_eq_bot hW h0 hb)

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then each nonzero stable subspace $W$ of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ contains $W_0$. The space $W$ contains $V(N)$, so $s = \mathrm{diag}(a, a^{-1})$ acts trivially on $V / W$. For $f \in W_0$ this gives $(\gamma(s) - 1) f \in W$, with $\gamma(s) = |a|^2 \neq 1$ for some $a$. -/
theorem jacquetEigenSub_le_of_ne_bot (h : α₁ = α₂ * absChar K ^ 2) {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (h0 : W ≠ ⊥) : W₀ ≤ W := by
  have hN := jacquetKer_le_of_ne_bot h hW h0
  obtain ⟨a, ha⟩ := exists_torusChar_diagTorus_ne_one h
  have htop : IsStableSubspace (Ψ).ρ (⊤ : Submodule ℂ (Ψ).V) := fun _ => le_top
  have hS : ∀ x : K, unip x ∈ relStab (Ψ) ⊤ W htop := fun x v _ =>
    hN ((Ψ).sub_mem_jacquetKer (unip_mem x) v)
  intro f hf
  set s : torus K := diagTorus K a a⁻¹
  set c : ℂ := (torusChar α₁ α₂ s : ℂ)
  have h1 : (Ψ).ρ (s : GL (Fin 2) K) f - f ∈ W :=
    diagTorus_mem_relStab htop hW hS a f Submodule.mem_top
  have h2 : (Ψ).ρ (s : GL (Fin 2) K) f - c • f ∈ W := hN (hf s)
  have h3 := W.sub_mem h1 h2
  have e : (Ψ).ρ (s : GL (Fin 2) K) f - f - ((Ψ).ρ (s : GL (Fin 2) K) f - c • f) =
      (c - 1) • f := by
    rw [sub_smul, one_smul]
    abel
  rw [e] at h3
  have hc : c - 1 ≠ 0 := sub_ne_zero.2 ha
  simpa [smul_smul, inv_mul_cancel₀ hc] using W.smul_mem (c - 1)⁻¹ h3

/-- If $\alpha_1 \otimes \alpha_2 \neq$ `bigCellChar` on $T$, then the Jacquet module of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ has an eigenvector $x$ of $T$ for $\alpha_1 \otimes \alpha_2$ with value $1$ under the evaluation at $1$. For $t_0$ with $\gamma(t_0) \neq \beta(t_0)$, the vector is $x = (t_0 - \beta(t_0)) x_0 / (\gamma(t_0) - \beta(t_0))$. -/
theorem principalSeriesJacquet_exists_torusChar_vec
    (h : ∃ t, torusChar α₁ α₂ t ≠ bigCellChar α₁ α₂ t) :
    ∃ x : (ΨN).V, (ev x).down = 1 ∧ ∀ t, (ΨN).ρ t x = (torusChar α₁ α₂ t : ℂ) • x := by
  obtain ⟨t₀, ht₀⟩ := h
  obtain ⟨x₀, y₁, hx₀, -, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := α₁) (χ₂ := α₂) (hχ₁ := hα₁) (hχ₂ := hα₂)
  set γ₀ : ℂ := (torusChar α₁ α₂ t₀ : ℂ)
  set β₀ : ℂ := (bigCellChar α₁ α₂ t₀ : ℂ)
  have hγβ : γ₀ - β₀ ≠ 0 := sub_ne_zero.2 fun e => ht₀ (Units.ext e)
  have hcomm : ∀ (t s : torus K) (v : (ΨN).V),
      (ΨN).ρ t ((ΨN).ρ s v) = (ΨN).ρ s ((ΨN).ρ t v) := by
    intro t s v
    rw [← Module.End.mul_apply, ← map_mul, torus_mul_comm, map_mul, Module.End.mul_apply]
  refine ⟨(γ₀ - β₀)⁻¹ • ((ΨN).ρ t₀ x₀ - β₀ • x₀), ?_, fun t => ?_⟩
  · rw [map_smul, map_sub, map_smul]
    change (γ₀ - β₀)⁻¹ * ((ev ((ΨN).ρ t₀ x₀)).down - β₀ * (ev x₀).down) = 1
    rw [principalSeriesJacquetEval_ρ, hx₀]
    change (γ₀ - β₀)⁻¹ * (γ₀ * 1 - β₀ * 1) = 1
    rw [mul_one, mul_one, inv_mul_cancel₀ hγβ]
  · set γ : ℂ := (torusChar α₁ α₂ t : ℂ)
    obtain ⟨c, hc⟩ := hspan ((ΨN).ρ t x₀ - γ • x₀)
    have hz : (ev ((ΨN).ρ t x₀ - γ • x₀)).down = 0 := by
      rw [map_sub, map_smul]
      change (ev ((ΨN).ρ t x₀)).down - γ * (ev x₀).down = 0
      rw [principalSeriesJacquetEval_ρ]
      ring
    rw [hz, zero_smul, zero_add] at hc
    have hk : (ΨN).ρ t₀ ((ΨN).ρ t x₀ - γ • x₀) - β₀ • ((ΨN).ρ t x₀ - γ • x₀) = 0 := by
      rw [hc, map_smul, hρy, smul_comm, sub_self]
    rw [map_sub, map_smul] at hk
    rw [map_smul, map_sub, map_smul, hcomm t t₀]
    linear_combination (norm := module) (γ₀ - β₀)⁻¹ • hk

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, there are vectors $f_0 \in W_0$ with $f_0 \notin V(N)$ and $f_1 \notin W_0$ of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ such that each $v$ is congruent to $a f_0 + b f_1$ modulo $V(N)$. The vector $f_1$ is a lift of the eigenvector $y_1$ of $T$ for `bigCellChar`. -/
theorem principalSeriesInd_exists_decomp_of_eq_mul_sq (h : α₁ = α₂ * absChar K ^ 2) :
    ∃ f₀ f₁ : (Ψ).V, f₀ ∈ W₀ ∧ f₀ ∉ VN ∧ f₁ ∉ W₀ ∧
      (∀ t : torus K, (Ψ).ρ (t : GL (Fin 2) K) f₁ - (bigCellChar α₁ α₂ t : ℂ) • f₁ ∈ VN) ∧
      ∀ v : (Ψ).V, ∃ a b : ℂ, v - a • f₀ - b • f₁ ∈ VN := by
  have hne := exists_torusChar_ne_bigCellChar h
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨x, hx1, hxt⟩ := principalSeriesJacquet_exists_torusChar_vec ⟨t₀, ht₀⟩
    (hα₁ := hα₁) (hα₂ := hα₂)
  obtain ⟨x₀, y₁, hx₀, hy0, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := α₁) (χ₂ := α₂) (hχ₁ := hα₁) (hχ₂ := hα₂)
  obtain ⟨f₀, hf₀⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent x
  obtain ⟨f₁, hf₁⟩ := (Ψ).jacquetMk_surjective _ _ torus_le_normalizer_unipotent y₁
  refine ⟨f₀, f₁, mem_jacquetEigenSub_iff_mk.2 fun t => by rw [hf₀]; exact hxt t,
    fun hv => ?_, fun hf => ?_, fun t => ?_, fun v => ?_⟩
  · have h0 := ((Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent f₀).2 hv
    have h0' : x = (0 : (ΨN).V) := by rw [← hf₀]; exact h0
    rw [h0', map_zero] at hx1
    exact zero_ne_one hx1
  · have h1 := mem_jacquetEigenSub_iff_mk.1 hf t₀
    rw [hf₁, hρy] at h1
    exact ht₀ (Units.ext (smul_left_injective ℂ hy0 h1).symm)
  · rw [← (Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, map_smul,
      (Ψ).jacquetMk_ρ torus_le_normalizer_unipotent t, hf₁]
    exact sub_eq_zero.2 (hρy t)
  · obtain ⟨d, hd⟩ := hspan x
    rw [hx1, one_smul] at hd
    obtain ⟨c, hc⟩ := hspan (mk v)
    refine ⟨(ev (mk v)).down, c - (ev (mk v)).down * d, ?_⟩
    rw [← (Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent, map_sub, map_sub, map_smul,
      map_smul, hf₀, hf₁, hd]
    generalize (ev (mk v)).down = e at hc ⊢
    rw [hc]
    change (e • x₀ + c • y₁ - e • (x₀ + d • y₁) - (c - e * d) • y₁ : (ΨN).V) = 0
    module

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then each stable subspace $W$ of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ that is not the whole space is contained in $W_0$. If $W \neq 0$, then $W$ contains $W_0$, so $f_1 \notin W$, and each vector of $W$ is congruent to a multiple of $f_0$ modulo $V(N)$. -/
theorem le_jacquetEigenSub_of_ne_top (h : α₁ = α₂ * absChar K ^ 2) {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (htop : W ≠ ⊤) : W ≤ W₀ := by
  by_cases h0 : W = ⊥
  · rw [h0]
    exact bot_le
  have hle := jacquetEigenSub_le_of_ne_bot h hW h0
  have hN : VN ≤ W := (jacquetKer_le_jacquetEigenSub _ _).trans hle
  obtain ⟨f₀, f₁, hf₀, -, -, -, hdec⟩ := principalSeriesInd_exists_decomp_of_eq_mul_sq h
  have hf₁W : f₁ ∉ W := by
    intro hf
    apply htop
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨a, b, hab⟩ := hdec v
    have := W.add_mem (W.add_mem (hN hab) (W.smul_mem b hf)) (W.smul_mem a (hle hf₀))
    rwa [sub_add_cancel, sub_add_cancel] at this
  intro v hv
  obtain ⟨a, b, hab⟩ := hdec v
  have hb : b = 0 := by
    by_contra hb
    have h1 : b • f₁ ∈ W := by
      have := W.sub_mem (W.sub_mem hv (W.smul_mem a (hle hf₀))) (hN hab)
      rwa [sub_sub_cancel] at this
    exact hf₁W (by simpa [smul_smul, inv_mul_cancel₀ hb] using W.smul_mem b⁻¹ h1)
  rw [hb, zero_smul, sub_zero] at hab
  have := Submodule.add_mem _ (jacquetKer_le_jacquetEigenSub _ _ hab) (Submodule.smul_mem _ a hf₀)
  rwa [sub_add_cancel] at this

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then a stable subspace of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ that is neither $0$ nor the whole space is $W_0$. -/
theorem stable_eq_jacquetEigenSub (h : α₁ = α₂ * absChar K ^ 2) {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (h0 : W ≠ ⊥) (htop : W ≠ ⊤) : W = W₀ :=
  le_antisymm (le_jacquetEigenSub_of_ne_top h hW htop) (jacquetEigenSub_le_of_ne_bot h hW h0)

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $W_0$ is a stable subspace of $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$. The principal series is not irreducible, so it has a stable subspace that is neither $0$ nor the whole space, and this subspace is $W_0$. -/
theorem jacquetEigenSub_stable (h : α₁ = α₂ * absChar K ^ 2) : IsStableSubspace (Ψ).ρ W₀ := by
  obtain ⟨W, hW, h0, htop⟩ : ∃ W : Submodule ℂ (Ψ).V,
      IsStableSubspace (Ψ).ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hc
    refine principalSeriesInd_not_isIrreducible_of_eq_mul_sq h
      ⟨principalSeriesInd_nontrivial hα₁ hα₂, fun W hW => ?_⟩
    by_contra h'
    rw [not_or] at h'
    exact hc ⟨W, hW, h'.1, h'.2⟩
  rw [← stable_eq_jacquetEigenSub h hW h0 htop]
  exact hW

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $W_0$ is not $0$. -/
theorem jacquetEigenSub_ne_bot (h : α₁ = α₂ * absChar K ^ 2) : W₀ ≠ ⊥ := by
  obtain ⟨f₀, -, hf₀, hf₀N, -, -, -⟩ := principalSeriesInd_exists_decomp_of_eq_mul_sq h
    (hα₁ := hα₁) (hα₂ := hα₂)
  intro hb
  rw [hb, Submodule.mem_bot] at hf₀
  exact hf₀N (hf₀ ▸ zero_mem _)

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $W_0$ is not the whole space. -/
theorem jacquetEigenSub_ne_top (h : α₁ = α₂ * absChar K ^ 2) : W₀ ≠ ⊤ := by
  obtain ⟨-, f₁, -, -, hf₁, -, -⟩ := principalSeriesInd_exists_decomp_of_eq_mul_sq h
    (hα₁ := hα₁) (hα₂ := hα₂)
  intro ht
  exact hf₁ (ht ▸ Submodule.mem_top)

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $W_0$ has codimension $1$ in $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$: the quotient is spanned by the class of $f_1$, which is not zero. -/
theorem finrank_quotient_jacquetEigenSub (h : α₁ = α₂ * absChar K ^ 2) :
    Module.finrank ℂ ((Ψ).V ⧸ W₀) = 1 := by
  obtain ⟨f₀, f₁, hf₀, -, hf₁, -, hdec⟩ := principalSeriesInd_exists_decomp_of_eq_mul_sq h
    (hα₁ := hα₁) (hα₂ := hα₂)
  have hne : (Submodule.Quotient.mk f₁ : (Ψ).V ⧸ W₀) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  refine (finrank_eq_one_iff_of_nonzero' _ hne).2 fun q => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, b, hab⟩ := hdec v
  refine ⟨b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
  have := Submodule.add_mem _ (jacquetKer_le_jacquetEigenSub _ _ hab) (Submodule.smul_mem _ a hf₀)
  rwa [sub_add_eq_add_sub, sub_add_cancel] at this

/-- If $\alpha_1 = \alpha_2 |\cdot|^2$, then $G$ acts on the quotient $V / W_0$ of $V = \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ by the character $\chi \circ \det$ with $\chi = \alpha_2 |\cdot|$: $g v - \chi(\det g) v \in W_0$ for each $g$ and $v$. The quotient is spanned by the class of $f_1$, so each $g$ acts on it by a scalar. This scalar is $1$ on $N$ and $\beta = \chi \otimes \chi$ on $T$. The Weyl element acts by a scalar $c$ with $c^2 = 1$, so the lower unipotent matrices act trivially. Then $w = n(-1) \bar n(1) n(-1) \mathrm{diag}(1, -1)$ and the Bruhat decomposition give the result for each $g$. -/
theorem ρ_sub_detChar_mem_jacquetEigenSub (h : α₁ = α₂ * absChar K ^ 2) (g : GL (Fin 2) K)
    (v : (Ψ).V) : (Ψ).ρ g v - (detChar K 2 (α₂ * absChar K) g : ℂ) • v ∈ W₀ := by
  have hW := jacquetEigenSub_stable h (hα₁ := hα₁) (hα₂ := hα₂)
  obtain ⟨f₀, f₁, hf₀, -, hf₁, hf₁t, hdec⟩ := principalSeriesInd_exists_decomp_of_eq_mul_sq h
    (hα₁ := hα₁) (hα₂ := hα₂)
  have hne : (Submodule.Quotient.mk f₁ : (Ψ).V ⧸ W₀) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hq : ∀ v : (Ψ).V, ∃ b : ℂ,
      (Submodule.Quotient.mk v : (Ψ).V ⧸ W₀) = b • Submodule.Quotient.mk f₁ := by
    intro v
    obtain ⟨a, b, hab⟩ := hdec v
    refine ⟨b, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have := Submodule.add_mem _ (jacquetKer_le_jacquetEigenSub _ _ hab) (Submodule.smul_mem _ a hf₀)
    rwa [sub_add_eq_add_sub, sub_add_cancel] at this
  have hsc : ∀ (g : GL (Fin 2) K) (c : ℂ),
      (Submodule.Quotient.mk ((Ψ).ρ g f₁) : (Ψ).V ⧸ W₀) = c • Submodule.Quotient.mk f₁ →
      ∀ v : (Ψ).V, (Submodule.Quotient.mk ((Ψ).ρ g v) : (Ψ).V ⧸ W₀) =
        c • Submodule.Quotient.mk v := by
    intro g c hc v
    obtain ⟨b, hb⟩ := hq v
    rw [quotient_mk_ρ_eq hW g hb, hc, hb, smul_comm]
  let P : GL (Fin 2) K → Prop := fun g => ∀ v : (Ψ).V,
    (Submodule.Quotient.mk ((Ψ).ρ g v) : (Ψ).V ⧸ W₀) =
      (detChar K 2 (α₂ * absChar K) g : ℂ) • Submodule.Quotient.mk v
  have hmul : ∀ g g', P g → P g' → P (g * g') := by
    intro g g' hg hg' v
    rw [map_mul, Module.End.mul_apply, hg, hg', smul_smul, map_mul, Units.val_mul]
  have hN : ∀ n ∈ unipotent K, P n := by
    intro n hn v
    rw [detChar_unipotent hn, one_smul, Submodule.Quotient.eq]
    exact jacquetKer_le_jacquetEigenSub _ _ ((Ψ).sub_mem_jacquetKer hn v)
  have hχ : α₁ * (absChar K)⁻¹ = α₂ * absChar K := by
    rw [h]; ext x; simp [pow_two, mul_assoc]
  have hT : ∀ t : torus K, P t := by
    intro t
    refine hsc _ _ ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have e : (detChar K 2 (α₂ * absChar K) (t : GL (Fin 2) K) : ℂ) = bigCellChar α₁ α₂ t := by
      rw [detChar_torus, bigCellChar, hχ]
    rw [e]
    exact jacquetKer_le_jacquetEigenSub _ _ (hf₁t t)
  obtain ⟨c, hc⟩ := hq ((Ψ).ρ weyl f₁)
  have hw := hsc weyl c hc
  have hcc : c * c = 1 := by
    have h1 := hw ((Ψ).ρ weyl f₁)
    rw [← Module.End.mul_apply, ← map_mul, weyl_mul_weyl, map_one, Module.End.one_apply, hc,
      smul_smul] at h1
    exact (smul_left_injective ℂ hne
      (show (1 : ℂ) • _ = (c * c) • _ by rw [one_smul]; exact h1)).symm
  have hθw : (detChar K 2 (α₂ * absChar K) weyl : ℂ) * detChar K 2 (α₂ * absChar K) weyl = 1 := by
    rw [← Units.val_mul, ← map_mul, weyl_mul_weyl, map_one, Units.val_one]
  have hL : ∀ x : K, P (lowerUnip x) := by
    intro x v
    rw [← weyl_mul_unip_mul_weyl, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hw, hN _ (unip_mem x), hw, smul_smul, smul_smul, detChar_unipotent (unip_mem x),
      map_mul, map_mul, Units.val_mul, Units.val_mul, detChar_unipotent (unip_mem x)]
    congr 1
    linear_combination hcc - hθw
  have hWe : P weyl := by
    rw [weyl_eq_unip_mul_lowerUnip]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hN _ (unip_mem _)) (hL 1)) (hN _ (unip_mem _))) (hT _)
  have hG : ∀ g, P g := by
    intro g
    rcases bruhat g with hb | ⟨b, hb, n, hn, rfl⟩
    · obtain ⟨t, n, hn, e⟩ := borel_eq_torus_mul_unipotent ⟨g, hb⟩
      change g = t * n at e
      rw [e]
      exact hmul _ _ (hT t) (hN n hn)
    · obtain ⟨t, n', hn', e⟩ := borel_eq_torus_mul_unipotent ⟨b, hb⟩
      change b = t * n' at e
      rw [e]
      exact hmul _ _ (hmul _ _ (hmul _ _ (hT t) (hN n' hn')) hWe) (hN n hn)
  have := hG g v
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at this

end Core

section Normalized

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2 SmoothRep

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- If $\chi_1 = \chi_2 |\cdot|$, then the unnormalized characters $\alpha_1 = \chi_1 |\cdot|^{1/2}$ and $\alpha_2 = \chi_2 |\cdot|^{-1/2}$ satisfy $\alpha_1 = \alpha_2 |\cdot|^2$. -/
theorem mul_sqrtAbsChar_eq_mul_absChar_sq (h : χ₁ = χ₂ * absChar K) :
    χ₁ * sqrtAbsChar K = χ₂ * (sqrtAbsChar K)⁻¹ * absChar K ^ 2 := by
  rw [h, ← sqrtAbsChar_sq]
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, pow_two, Units.val_mul,
    Units.val_inv_eq_inv_val]
  have hs : (sqrtAbsChar K x : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The subspace $W_0$ of the normalized principal series of $(\chi_1, \chi_2)$: the vectors $f$ with $t f \equiv \gamma(t) f$ modulo $V(N)$ for each $t \in T$, where $\gamma = (\chi_1 \otimes \chi_2)\delta_B^{1/2} = \chi_1 |\cdot|^{1/2} \otimes \chi_2 |\cdot|^{-1/2}$ on $T$. -/
noncomputable def normSteinbergSub : Submodule ℂ (Π).V :=
  jacquetEigenSub (Π) (torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹))

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then $W_0$ is a stable subspace of the normalized principal series. -/
theorem normSteinbergSub_stable (h : χ₁ = χ₂ * absChar K) :
    IsStableSubspace (Π).ρ (normSteinbergSub χ₁ χ₂ hχ₁ hχ₂) := by
  unfold normSteinbergSub
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact jacquetEigenSub_stable (mul_sqrtAbsChar_eq_mul_absChar_sq h)

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then $W_0$ is not $0$. -/
theorem normSteinbergSub_ne_bot (h : χ₁ = χ₂ * absChar K) :
    normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ ≠ ⊥ := by
  unfold normSteinbergSub
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact jacquetEigenSub_ne_bot (mul_sqrtAbsChar_eq_mul_absChar_sq h)

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then $W_0$ is not the whole space. -/
theorem normSteinbergSub_ne_top (h : χ₁ = χ₂ * absChar K) :
    normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ ≠ ⊤ := by
  unfold normSteinbergSub
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact jacquetEigenSub_ne_top (mul_sqrtAbsChar_eq_mul_absChar_sq h)

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then $W_0$ has codimension $1$ in the normalized principal series. -/
theorem finrank_quotient_normSteinbergSub (h : χ₁ = χ₂ * absChar K) :
    Module.finrank ℂ ((Π).V ⧸ normSteinbergSub χ₁ χ₂ hχ₁ hχ₂) = 1 := by
  unfold normSteinbergSub
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact finrank_quotient_jacquetEigenSub (mul_sqrtAbsChar_eq_mul_absChar_sq h)

/-- Let $\chi_1 = \chi_2 |\cdot|$ and $\chi = \chi_2 |\cdot|^{1/2}$. Then $G$ acts on the quotient of the normalized principal series by $W_0$ by the character $\chi \circ \det$: $g v - \chi(\det g) v \in W_0$ for each $g$ and $v$. -/
theorem normPrincipalSeries_ρ_sub_detChar_mem_normSteinbergSub (h : χ₁ = χ₂ * absChar K)
    (g : GL (Fin 2) K) (v : (Π).V) :
    (Π).ρ g v - (detChar K 2 (χ₂ * sqrtAbsChar K) g : ℂ) • v ∈ normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ := by
  have e : χ₂ * sqrtAbsChar K = χ₂ * (sqrtAbsChar K)⁻¹ * absChar K := by
    rw [← sqrtAbsChar_sq]; ext x; simp [pow_two, mul_assoc]
  rw [e]
  unfold normSteinbergSub
  revert v
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact ρ_sub_detChar_mem_jacquetEigenSub (mul_sqrtAbsChar_eq_mul_absChar_sq h) g

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then each nonzero stable subspace of the normalized principal series contains $W_0$. -/
theorem normSteinbergSub_le_of_ne_bot (h : χ₁ = χ₂ * absChar K) {W : Submodule ℂ (Π).V}
    (hW : IsStableSubspace (Π).ρ W) (h0 : W ≠ ⊥) : normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ ≤ W := by
  unfold normSteinbergSub
  revert W
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact fun hW h0 => jacquetEigenSub_le_of_ne_bot (mul_sqrtAbsChar_eq_mul_absChar_sq h) hW h0

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then a stable subspace of the normalized principal series of $(\chi_1, \chi_2)$ that is neither $0$ nor the whole space is $W_0$. -/
theorem normPrincipalSeries_stable_eq_normSteinbergSub (h : χ₁ = χ₂ * absChar K)
    {W : Submodule ℂ (Π).V} (hW : IsStableSubspace (Π).ρ W) (h0 : W ≠ ⊥) (htop : W ≠ ⊤) :
    W = normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ := by
  unfold normSteinbergSub
  revert W
  rw [normPrincipalSeries_eq hχ₁ hχ₂]
  exact fun hW h0 htop =>
    stable_eq_jacquetEigenSub (mul_sqrtAbsChar_eq_mul_absChar_sq h) hW h0 htop

/-- Let $\chi_1 = \chi_2 |\cdot|$. The stable subspaces of the normalized principal series of $(\chi_1, \chi_2)$ are exactly $0$, $W_0$ and the whole space. Thus the principal series has length $2$, with $W_0$ as subrepresentation and a quotient of dimension $1$. -/
theorem normPrincipalSeries_isStableSubspace_iff_of_eq_mul (h : χ₁ = χ₂ * absChar K)
    (W : Submodule ℂ (Π).V) :
    IsStableSubspace (Π).ρ W ↔ W = ⊥ ∨ W = normSteinbergSub χ₁ χ₂ hχ₁ hχ₂ ∨ W = ⊤ := by
  refine ⟨fun hW => ?_, ?_⟩
  · by_cases h0 : W = ⊥
    · exact Or.inl h0
    by_cases htop : W = ⊤
    · exact Or.inr (Or.inr htop)
    exact Or.inr (Or.inl (normPrincipalSeries_stable_eq_normSteinbergSub h hW h0 htop))
  · rintro (rfl | rfl | rfl)
    · exact fun g _ hv => by
        rw [Submodule.mem_bot] at hv
        rw [hv]
        exact Submodule.zero_mem _
    · exact normSteinbergSub_stable h
    · exact fun g _ _ => Submodule.mem_top

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then the normalized principal series of $(\chi_1, \chi_2)$ has exactly one stable subspace that is neither $0$ nor the whole space. -/
theorem normPrincipalSeries_existsUnique_stable_of_eq_mul (h : χ₁ = χ₂ * absChar K) :
    ∃! W : Submodule ℂ (Π).V, IsStableSubspace (Π).ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤ :=
  ⟨_, ⟨normSteinbergSub_stable h, normSteinbergSub_ne_bot h, normSteinbergSub_ne_top h⟩,
    fun _ hW => normPrincipalSeries_stable_eq_normSteinbergSub h hW.1 hW.2.1 hW.2.2⟩

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The twisted Steinberg representation for $\chi_1 = \chi_2 |\cdot|$, in the model of a subrepresentation: the representation of $G$ on the subspace $W_0$ of the normalized principal series of $(\chi_1, \chi_2)$. -/
noncomputable def steinbergSub (h : χ₁ = χ₂ * absChar K) : SmoothRep (GL (Fin 2) K) :=
  (Π).sub (normSteinbergSub χ₁ χ₂ hχ₁ hχ₂) (normSteinbergSub_stable h)

/-- Let $\chi_1 = \chi_2 |\cdot|$. Then the representation on $W_0$ is irreducible, since each nonzero stable subspace of the normalized principal series contains $W_0$. -/
theorem steinbergSub_isIrreducible (h : χ₁ = χ₂ * absChar K) :
    (steinbergSub χ₁ χ₂ hχ₁ hχ₂ h).IsIrreducible :=
  (Π).sub_isIrreducible_of_le _ (normSteinbergSub_ne_bot h) fun _ hU h0 =>
    normSteinbergSub_le_of_ne_bot h hU h0

end Normalized

end Langlands
