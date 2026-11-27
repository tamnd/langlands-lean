/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.ChainOrders
import Langlands.Smooth.Induction

/-!
# Cuspidal types of GL(2) and compact induction

Let $F$ be a nonarchimedean local field, $\mathfrak{A}$ a chain order of $M_2(F)$, and $E/F$ a quadratic extension embedded in $M_2(F)$ by a basis adapted to $\mathfrak{A}$. This file defines the group $J = E^\times U^m_{\mathfrak{A}}$ and proves that it is open, that it contains the centre $F^\times$, and that it lies in the normalizer $\mathfrak{K}_{\mathfrak{A}}$. For a simple stratum $(\mathfrak{A}, n, \alpha)$ with $\alpha \in E$ and $m = [(n+1)/2]$ this is the group $J_\alpha$ of BH §15.

Let $\psi$ be a character of $F$ of level one and $\xi$ a character of $E^\times$. A type character for $(\alpha, \xi)$ is a character $\Lambda$ of $J$ that agrees with $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$ and with $\xi$ on $E^\times$. The pair $(\alpha, \xi)$ is compatible if $\xi(y) = \psi(\mathrm{tr}_{E/F}(\alpha(y - 1)))$ for $y \in U^{[n/2]+1}_E$. The file proves that $\psi_\alpha$ is invariant under conjugation by $E^\times$, and that for a compatible pair $\psi_\alpha$ and $\xi$ agree on $E^\times \cap U^{[n/2]+1}_{\mathfrak{A}}$. On $E^\times U^{[n/2]+1}_{\mathfrak{A}}$ a type character exists exactly when the pair is compatible, and then it is unique: it is $\Lambda(y u) = \xi(y) \psi_\alpha(u)$. For odd $n$ this group is $J_\alpha$, so the set of cuspidal types has one member for a compatible pair and no member otherwise.

Last, for a subgroup $J$ of a topological group $G$ and a character $\Lambda$ of $J$, the file defines the compactly induced representation $c\text{-}\mathrm{Ind}_J^G \Lambda$ as a smooth representation of $G$. It proves that it is not zero when $J$ is open and $\Lambda$ has open kernel. It proves the first step of the irreducibility criterion (BH 11.1 to 11.4): a function $\varphi$ with $\varphi(j g j') = \Lambda(j) \varphi(g) \Lambda(j')$ vanishes outside the intertwining of $\Lambda$. So if the intertwining is $J$, each vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ on which $J$ acts by $\Lambda$ is a multiple of the vector that is $\Lambda$ on $J$ and $0$ outside $J$.

## Main definitions

* `Langlands.LocalGL2.jGroup`: the group $J = E^\times U^m_{\mathfrak{A}}$.
* `Langlands.LocalGL2.psiAlphaUnits`: the character $\psi_\alpha$ with values in $\mathbb{C}^\times$.
* `Langlands.LocalGL2.IsCompatible`: $\xi(y) = \psi(\mathrm{tr}_{E/F}(\alpha(y - 1)))$ on $U^{[n/2]+1}_E$.
* `Langlands.LocalGL2.IsTypeChar`: $\Lambda$ agrees with $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$ and with $\xi$ on $E^\times$.
* `Langlands.LocalGL2.typeChar`: the type character $\Lambda(y u) = \xi(y) \psi_\alpha(u)$ of $E^\times U^{[n/2]+1}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.cuspTypes`: the cuspidal types, the type characters of $J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.cuspInd`: the representation $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ of $GL_2(F)$.
* `Langlands.cIndSpace`, `Langlands.SmoothRep.cInd`: the compactly induced representation $c\text{-}\mathrm{Ind}_J^G \Lambda$.
* `Langlands.cIndBasic`: the vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ that is $\Lambda$ on $J$ and $0$ outside $J$.
* `Langlands.Intertwines`: $g$ intertwines $\Lambda$.
* `Langlands.IsBiEquivariant`: $\varphi(j g j') = \Lambda(j) \varphi(g) \Lambda(j')$.

## Main results

* `Langlands.LocalGL2.IsAdapted.conj_mem_unitsFilt`: $E^\times$ normalizes $U^m_{\mathfrak{A}}$.
* `Langlands.LocalGL2.mem_jGroup_iff_exists_mul`: $J$ is the set of products $y u$.
* `Langlands.LocalGL2.isOpen_jGroup`, `Langlands.LocalGL2.unitsFilt_le_jGroup`, `Langlands.LocalGL2.jGroup_le_normalizer`, `Langlands.LocalGL2.scalarGL_mem_jGroup`: $J$ is open, $U^m_{\mathfrak{A}} \subseteq J \subseteq \mathfrak{K}_{\mathfrak{A}}$, and $F^\times \subseteq J$.
* `Langlands.LocalGL2.psiAlphaUnits_conj`: $\psi_\alpha$ is invariant under conjugation by $E^\times$.
* `Langlands.LocalGL2.psiAlpha_embGL_eq`: for a compatible pair, $\psi_\alpha$ and $\xi$ agree on $E^\times \cap U^{[n/2]+1}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.existsUnique_isTypeChar_iff`: on $E^\times U^{[n/2]+1}_{\mathfrak{A}}$ a type character exists, and is unique, exactly when the pair is compatible.
* `Langlands.LocalGL2.existsUnique_mem_cuspTypes_iff`: for odd $n$, there is exactly one cuspidal type exactly when the pair is compatible.
* `Langlands.LocalGL2.isCompatible_of_mem_cuspTypes`: for each $n$, a cuspidal type exists only for a compatible pair.
* `Langlands.LocalGL2.IsTypeChar.isOpen_ker`, `Langlands.LocalGL2.nontrivial_cuspInd`: a type character has open kernel, and $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ is not zero.
* `Langlands.nontrivial_cInd`: $c\text{-}\mathrm{Ind}_J^G \Lambda$ is not zero for $J$ open and $\Lambda$ with open kernel.
* `Langlands.intertwines_of_mem`: $J$ intertwines $\Lambda$.
* `Langlands.IsBiEquivariant.intertwines`, `Langlands.IsBiEquivariant.eq_smul_cIndBasicFun`: a bi-equivariant function vanishes outside the intertwining, so it is a multiple of the extension of $\Lambda$ by $0$ when the intertwining is $J$.
* `Langlands.eq_smul_cIndBasic_of_isotypic`: if the intertwining is $J$, the vectors of $c\text{-}\mathrm{Ind}_J^G \Lambda$ on which $J$ acts by $\Lambda$ form a line.

## Implementation notes

The group $J$ is the set of $g$ with $y^{-1} g \in U^m_{\mathfrak{A}}$ for some $y \in E^\times$. It is a group because $E^\times$ normalizes $U^m_{\mathfrak{A}}$. The statement that $J$ is open and compact modulo the centre is given in the form of the existing API: $J$ contains the open compact group $U^m_{\mathfrak{A}}$, it contains $F^\times$, and it lies in $\mathfrak{K}_{\mathfrak{A}}$. The type character is defined by a choice of $y$, and the proof that its value does not depend on $y$ uses the compatibility on $E^\times \cap U^{[n/2]+1}_{\mathfrak{A}}$. The support condition of $c\text{-}\mathrm{Ind}_J^G \Lambda$ is that the support lies in finitely many cosets $J s$. For $J$ open and compact modulo the centre this is the condition of compact support modulo the centre. The definition of $c\text{-}\mathrm{Ind}_J^G \Lambda$ does not need $J$ open.

## Still open

* The case of even $n$. Then $J_\alpha = E^\times U^{n/2}_{\mathfrak{A}}$ is larger than $E^\times U^{n/2+1}_{\mathfrak{A}}$, and a cuspidal type is an extension of `typeChar` to $J_\alpha$. Its existence needs that $\psi_\alpha$ extends to $U^1_E U^{n/2}_{\mathfrak{A}}$, which uses the alternating form $(x, y) \mapsto \psi_\alpha([x, y])$ on $U^{n/2}_{\mathfrak{A}} / U^{n/2+1}_{\mathfrak{A}}$ (BH §15.6). The file proves only that a cuspidal type gives a compatible pair.
* The computation of the intertwining of a cuspidal type, $I_G(\Lambda) = J_\alpha$ (BH §15.1 and §19). It needs the intertwining of the simple stratum, $I_G(\psi_\alpha) = J_\alpha$, which uses the adjoint map $a_\alpha$ and the exact sequences of BH §13.
* The irreducibility of $c\text{-}\mathrm{Ind}_J^G \Lambda$ when the intertwining of $\Lambda$ is $J$ (BH 11.4). The file proves the step on the $\Lambda$-isotypic vectors. Two further steps are missing. First, each nonzero stable subspace $W$ contains a nonzero vector on which $J$ acts by $\Lambda$. For this one averages $\Lambda(j)^{-1} \pi(j) w$ over the finite group $J / F^\times K$, where $K$ is an open normal subgroup of $J$ that fixes $w$ and lies in the kernel of $\Lambda$. This needs that $F^\times$ acts on $c\text{-}\mathrm{Ind}_J^G \Lambda$ by $\Lambda$, and that $J / F^\times U^{n+1}_{\mathfrak{A}}$ is finite, which is the honest form of compactness modulo the centre and is not proved here. Second, the translates of `cIndBasic` span $c\text{-}\mathrm{Ind}_J^G \Lambda$, which is a finite sum over representatives of the cosets $J s$.
* The proof that $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ is supercuspidal, and the bijection between minimal pairs and these representations (BH §19 and §20).
-/

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel Matrix

section JGroup

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

/-- For an adapted basis, conjugation by $y \in E^\times$ preserves $U^m_{\mathfrak{A}}$. -/
theorem IsAdapted.conj_mem_unitsFilt (hv : IsAdapted A v) (y : Eˣ) {m : ℕ} {g : GL (Fin 2) F}
    (hg : g ∈ unitsFilt F A m) : embGL v y * g * (embGL v y)⁻¹ ∈ unitsFilt F A m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact hv.conj_mem_radPow y hg.1
  · rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    exact hv.conj_mem_radPow y hg.2.1
  · have h : ((embGL v y * g * (embGL v y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
        ((embGL v y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((g : Matrix (Fin 2) (Fin 2) F) - 1) *
          (((embGL v y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [h]
    exact hv.conj_mem_radPow y hg.2.2

/-- For an adapted basis, conjugation by $y^{-1}$ for $y \in E^\times$ preserves $U^m_{\mathfrak{A}}$. -/
theorem IsAdapted.inv_conj_mem_unitsFilt (hv : IsAdapted A v) (y : Eˣ) {m : ℕ} {g : GL (Fin 2) F}
    (hg : g ∈ unitsFilt F A m) : (embGL v y)⁻¹ * g * embGL v y ∈ unitsFilt F A m := by
  have := hv.conj_mem_unitsFilt y⁻¹ hg
  rwa [map_inv, inv_inv] at this

variable (v) in
/-- The group $J = E^\times U^m_{\mathfrak{A}}$ for a basis $v$ adapted to $\mathfrak{A}$: the elements $g$ of $GL_2(F)$ with $y^{-1} g \in U^m_{\mathfrak{A}}$ for some $y \in E^\times$. For a simple stratum $(\mathfrak{A}, n, \alpha)$ with $E = F[\alpha]$, the group $J_\alpha$ of BH §15 is the group with $m = [(n+1)/2]$. -/
def jGroup (hv : IsAdapted A v) (m : ℕ) : Subgroup (GL (Fin 2) F) where
  carrier := {g | ∃ y : Eˣ, (embGL v y)⁻¹ * g ∈ unitsFilt F A m}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y * z, ?_⟩
    have e : (embGL v (y * z))⁻¹ * (g * h) =
        ((embGL v z)⁻¹ * ((embGL v y)⁻¹ * g) * embGL v z) * ((embGL v z)⁻¹ * h) := by
      rw [map_mul]
      group
    rw [e]
    exact (unitsFilt F A m).mul_mem (hv.inv_conj_mem_unitsFilt z hy) hz
  inv_mem' := by
    rintro g ⟨y, hy⟩
    refine ⟨y⁻¹, ?_⟩
    have e : (embGL v y⁻¹)⁻¹ * g⁻¹ = embGL v y * ((embGL v y)⁻¹ * g)⁻¹ * (embGL v y)⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    exact hv.conj_mem_unitsFilt y ((unitsFilt F A m).inv_mem hy)

/-- Membership in $J = E^\times U^m_{\mathfrak{A}}$. -/
theorem mem_jGroup (hv : IsAdapted A v) (m : ℕ) (g : GL (Fin 2) F) :
    g ∈ jGroup v hv m ↔ ∃ y : Eˣ, (embGL v y)⁻¹ * g ∈ unitsFilt F A m := Iff.rfl

/-- An element of $J = E^\times U^m_{\mathfrak{A}}$ is a product $y u$ with $y \in E^\times$ and $u \in U^m_{\mathfrak{A}}$. -/
theorem mem_jGroup_iff_exists_mul (hv : IsAdapted A v) (m : ℕ) (g : GL (Fin 2) F) :
    g ∈ jGroup v hv m ↔ ∃ y : Eˣ, ∃ u ∈ unitsFilt F A m, g = embGL v y * u := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, _, hy, by group⟩
  · rintro ⟨y, u, hu, rfl⟩
    exact ⟨y, by simpa using hu⟩

/-- The group $U^m_{\mathfrak{A}}$ lies in $J = E^\times U^m_{\mathfrak{A}}$. -/
theorem unitsFilt_le_jGroup (hv : IsAdapted A v) (m : ℕ) : unitsFilt F A m ≤ jGroup v hv m :=
  fun g hg => ⟨1, by simpa using hg⟩

/-- The group $E^\times$ lies in $J = E^\times U^m_{\mathfrak{A}}$. -/
theorem embGL_mem_jGroup (hv : IsAdapted A v) (m : ℕ) (y : Eˣ) : embGL v y ∈ jGroup v hv m :=
  ⟨y, by simp⟩

/-- The groups $J = E^\times U^m_{\mathfrak{A}}$ decrease with $m$. -/
theorem jGroup_anti (hv : IsAdapted A v) {m m' : ℕ} (h : m ≤ m') : jGroup v hv m' ≤ jGroup v hv m :=
  fun _ ⟨y, hy⟩ => ⟨y, unitsFilt_anti h hy⟩

/-- The group $J = E^\times U^m_{\mathfrak{A}}$ is open in $GL_2(F)$. -/
theorem isOpen_jGroup (hv : IsAdapted A v) (m : ℕ) : IsOpen (jGroup v hv m : Set (GL (Fin 2) F)) :=
  Subgroup.isOpen_mono (unitsFilt_le_jGroup hv m) (isOpen_unitsFilt A m)

/-- The group $J = E^\times U^m_{\mathfrak{A}}$ lies in the normalizer $\mathfrak{K}_{\mathfrak{A}}$. With `isOpen_jGroup` and the compactness of $U^m_{\mathfrak{A}}$, this is the statement that $J$ is open and compact modulo the centre. -/
theorem jGroup_le_normalizer (hv : IsAdapted A v) (m : ℕ) : jGroup v hv m ≤ normalizer F A := by
  rintro g ⟨y, hy⟩
  have h := (normalizer F A).mul_mem (hv.embGL_mem_normalizer y)
    (unitsFilt_le_normalizer A (unitsFilt_anti (Nat.zero_le m) hy))
  rwa [mul_inv_cancel_left] at h

/-- The centre $F^\times$ of $GL_2(F)$ lies in $J = E^\times U^m_{\mathfrak{A}}$. -/
theorem scalarGL_mem_jGroup (hv : IsAdapted A v) (m : ℕ) (c : Fˣ) :
    Langlands.scalarGL F 2 c ∈ jGroup v hv m := by
  have h : Langlands.scalarGL F 2 c = embGL v (Units.map (algebraMap F E).toMonoidHom c) := by
    ext : 1
    rw [val_embGL]
    simp [Langlands.scalarGL, Matrix.algebraMap_eq_diagonal]
  rw [h]
  exact embGL_mem_jGroup hv m _

end JGroup

section TypeChar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If $X$ commutes with $b$, then $\psi_X(b^{-1} g b) = \psi_X(g)$. -/
theorem psiAlphaFun_conj (ψ : AddChar F ℂ) (X : Matrix (Fin 2) (Fin 2) F) (b g : GL (Fin 2) F)
    (hb : X * (b : Matrix (Fin 2) (Fin 2) F) = b * X) :
    psiAlphaFun F ψ X (b⁻¹ * g * b) = psiAlphaFun F ψ X g := by
  unfold psiAlphaFun
  congr 1
  set B : Matrix (Fin 2) (Fin 2) F := (b : Matrix (Fin 2) (Fin 2) F)
  set Bi : Matrix (Fin 2) (Fin 2) F := ((b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  have h1 : Bi * B = 1 := Units.inv_mul b
  have h2 : B * Bi = 1 := Units.mul_inv b
  have hXi : X * Bi = Bi * X := by
    calc X * Bi = Bi * (B * X) * Bi := by rw [← mul_assoc, h1, one_mul]
      _ = Bi * (X * B) * Bi := by rw [hb]
      _ = Bi * X := by rw [mul_assoc, mul_assoc, h2, mul_one]
  have e : X * (Bi * G * B - 1) = Bi * (X * (G - 1)) * B := by
    calc X * (Bi * G * B - 1) = X * (Bi * G * B - Bi * B) := by rw [h1]
      _ = X * Bi * (G - 1) * B := by simp only [mul_sub, sub_mul, mul_one, mul_assoc]
      _ = Bi * (X * (G - 1)) * B := by rw [hXi, mul_assoc Bi X]
  rw [Units.val_mul, Units.val_mul, e, Matrix.trace_mul_comm, ← mul_assoc, h2, one_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The matrix of $\alpha \in E$ commutes with the image of $E^\times$. -/
theorem leftMulMatrix_mul_embGL (α : E) (y : Eˣ) :
    Algebra.leftMulMatrix v α * ((embGL v y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((embGL v y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α := by
  rw [val_embGL, ← map_mul, mul_comm, map_mul]

variable (hv : IsAdapted A v) (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) (n : ℕ) (α : E)
  (hα : Algebra.leftMulMatrix v α ∈ radPow F A (-n)) (ξ : Eˣ →* ℂˣ)

/-- The character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ with values in $\mathbb{C}^\times$. -/
noncomputable def psiAlphaUnits : unitsFilt F A (n / 2 + 1) →* ℂˣ :=
  (psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα).toHomUnits

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The value of `psiAlphaUnits` is the value of $\psi_\alpha$. -/
theorem coe_psiAlphaUnits (g : unitsFilt F A (n / 2 + 1)) :
    (psiAlphaUnits ψ hψ n α hα g : ℂ) = psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα g :=
  rfl

/-- The character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ is invariant under conjugation by $E^\times$. -/
theorem psiAlphaUnits_conj (y : Eˣ) (g : unitsFilt F A (n / 2 + 1)) :
    psiAlphaUnits ψ hψ n α hα ⟨(embGL v y)⁻¹ * g * embGL v y, hv.inv_conj_mem_unitsFilt y g.2⟩ =
      psiAlphaUnits ψ hψ n α hα g := by
  apply Units.ext
  exact psiAlphaFun_conj ψ _ _ _ (leftMulMatrix_mul_embGL α y)

/-- The pair $(\alpha, \xi)$ is compatible if $\xi(y) = \psi(\mathrm{tr}_{E/F}(\alpha(y - 1)))$ for each $y \in U^{[n/2]+1}_E$. -/
def IsCompatible : Prop :=
  ∀ y ∈ unitFilt E (n / 2 + 1), (ξ y : ℂ) = ψ (Algebra.trace F E (α * ((y : E) - 1)))

include hv in
/-- The compatibility on $E^\times \cap U^{[n/2]+1}_{\mathfrak{A}}$: if $\xi(y) = \psi(\mathrm{tr}_{E/F}(\alpha(y - 1)))$ on $U^{[n/2]+1}_E$, then $\psi_\alpha$ and $\xi$ agree on $E^\times \cap U^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem psiAlpha_embGL_eq (hξ : IsCompatible ψ n α ξ) (y : Eˣ)
    (h : embGL v y ∈ unitsFilt F A (n / 2 + 1)) :
    psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα ⟨embGL v y, h⟩ = ξ y := by
  change psiAlphaFun F ψ _ _ = _
  rw [psiAlphaFun_embGL, hξ y ((hv.embGL_mem_unitsFilt_iff _ y).1 h)]

/-- The value $\xi(y) \psi_\alpha(y^{-1} g)$ for $g \in E^\times U^{[n/2]+1}_{\mathfrak{A}}$ and a choice of $y \in E^\times$ with $y^{-1} g \in U^{[n/2]+1}_{\mathfrak{A}}$. -/
noncomputable def typeCharAux (g : GL (Fin 2) F) (y : Eˣ)
    (hy : (embGL v y)⁻¹ * g ∈ unitsFilt F A (n / 2 + 1)) : ℂˣ :=
  ξ y * psiAlphaUnits ψ hψ n α hα ⟨_, hy⟩

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- A formula for `typeCharAux` with a given element of $U^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem typeCharAux_eq (g : GL (Fin 2) F) (y : Eˣ)
    (hy : (embGL v y)⁻¹ * g ∈ unitsFilt F A (n / 2 + 1)) (w : unitsFilt F A (n / 2 + 1))
    (hw : (embGL v y)⁻¹ * g = w) :
    typeCharAux ψ hψ n α hα ξ g y hy = ξ y * psiAlphaUnits ψ hψ n α hα w := by
  rw [typeCharAux, show (⟨_, hy⟩ : unitsFilt F A (n / 2 + 1)) = w from Subtype.ext hw]

include hv in
/-- For a compatible pair, the value $\xi(y) \psi_\alpha(y^{-1} g)$ does not depend on the choice of $y$. -/
theorem typeCharAux_indep (hξ : IsCompatible ψ n α ξ) (g : GL (Fin 2) F) (y y' : Eˣ)
    (hy : (embGL v y)⁻¹ * g ∈ unitsFilt F A (n / 2 + 1))
    (hy' : (embGL v y')⁻¹ * g ∈ unitsFilt F A (n / 2 + 1)) :
    typeCharAux ψ hψ n α hα ξ g y hy = typeCharAux ψ hψ n α hα ξ g y' hy' := by
  set z := y'⁻¹ * y with hzdef
  have ez : embGL v z = ((embGL v y')⁻¹ * g) * ((embGL v y)⁻¹ * g)⁻¹ := by
    rw [hzdef, map_mul, map_inv]
    group
  have hz : embGL v z ∈ unitsFilt F A (n / 2 + 1) := by
    rw [ez]
    exact (unitsFilt F A _).mul_mem hy' ((unitsFilt F A _).inv_mem hy)
  have hc := psiAlpha_embGL_eq hv ψ hψ n α hα ξ hξ z hz
  have hξz : ξ y = ξ y' * ξ z := by
    rw [← map_mul, hzdef, mul_inv_cancel_left]
  rw [typeCharAux_eq ψ hψ n α hα ξ g y' hy' (⟨embGL v z, hz⟩ * ⟨_, hy⟩) (by
    change _ = embGL v z * ((embGL v y)⁻¹ * g)
    rw [ez]
    group)]
  rw [typeCharAux, map_mul, hξz]
  apply Units.ext
  simp only [Units.val_mul, coe_psiAlphaUnits, hc]
  ring

/-- The character $\Lambda$ of $E^\times U^{[n/2]+1}_{\mathfrak{A}}$ given by a compatible pair: $\Lambda(y u) = \xi(y) \psi_\alpha(u)$ for $y \in E^\times$ and $u \in U^{[n/2]+1}_{\mathfrak{A}}$. For odd $n$ this group is $J_\alpha$. -/
noncomputable def typeChar (hξ : IsCompatible ψ n α ξ) : jGroup v hv (n / 2 + 1) →* ℂˣ where
  toFun g := typeCharAux ψ hψ n α hα ξ g ((mem_jGroup hv _ g).1 g.2).choose
    ((mem_jGroup hv _ g).1 g.2).choose_spec
  map_one' := by
    rw [typeCharAux_indep hv ψ hψ n α hα ξ hξ _ _ 1 _ (by simp),
      typeCharAux_eq ψ hψ n α hα ξ _ 1 _ 1 (by simp)]
    simp
  map_mul' g h := by
    obtain ⟨y, hy⟩ := (mem_jGroup hv _ g).1 g.2
    obtain ⟨z, hz⟩ := (mem_jGroup hv _ h).1 h.2
    have hyz : (embGL v (y * z))⁻¹ * ((g * h : jGroup v hv (n / 2 + 1)) : GL (Fin 2) F) ∈
        unitsFilt F A (n / 2 + 1) := by
      have e : (embGL v (y * z))⁻¹ * ((g * h : jGroup v hv (n / 2 + 1)) : GL (Fin 2) F) =
          ((embGL v z)⁻¹ * ((embGL v y)⁻¹ * g) * embGL v z) * ((embGL v z)⁻¹ * h) := by
        rw [map_mul, Subgroup.coe_mul]
        group
      rw [e]
      exact (unitsFilt F A _).mul_mem (hv.inv_conj_mem_unitsFilt z hy) hz
    rw [typeCharAux_indep hv ψ hψ n α hα ξ hξ _ _ (y * z) _ hyz,
      typeCharAux_indep hv ψ hψ n α hα ξ hξ _ _ y _ hy,
      typeCharAux_indep hv ψ hψ n α hα ξ hξ _ _ z _ hz,
      typeCharAux_eq ψ hψ n α hα ξ _ (y * z) hyz
        (⟨_, hv.inv_conj_mem_unitsFilt z hy⟩ * ⟨_, hz⟩) (by
          rw [map_mul, Subgroup.coe_mul]
          change _ = (embGL v z)⁻¹ * ((embGL v y)⁻¹ * g) * embGL v z * ((embGL v z)⁻¹ * h)
          group),
      map_mul, map_mul, psiAlphaUnits_conj hv ψ hψ n α hα z ⟨_, hy⟩, typeCharAux, typeCharAux]
    ac_rfl

/-- The value of $\Lambda$ at $g$ is $\xi(y) \psi_\alpha(y^{-1} g)$ for each $y \in E^\times$ with $y^{-1} g \in U^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem typeChar_apply (hξ : IsCompatible ψ n α ξ) (g : jGroup v hv (n / 2 + 1)) (y : Eˣ)
    (hy : (embGL v y)⁻¹ * g ∈ unitsFilt F A (n / 2 + 1)) :
    typeChar hv ψ hψ n α hα ξ hξ g = typeCharAux ψ hψ n α hα ξ g y hy :=
  typeCharAux_indep hv ψ hψ n α hα ξ hξ _ _ _ _ hy

/-- The character $\Lambda$ agrees with $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem typeChar_apply_unitsFilt (hξ : IsCompatible ψ n α ξ) (g : unitsFilt F A (n / 2 + 1)) :
    (typeChar hv ψ hψ n α hα ξ hξ ⟨g, unitsFilt_le_jGroup hv _ g.2⟩ : ℂ) =
      psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα g := by
  rw [typeChar_apply hv ψ hψ n α hα ξ hξ _ 1 (by simp),
    typeCharAux_eq ψ hψ n α hα ξ _ 1 _ g (by simp)]
  simp [coe_psiAlphaUnits]

/-- The character $\Lambda$ restricts to $\xi$ on $E^\times$. -/
theorem typeChar_apply_embGL (hξ : IsCompatible ψ n α ξ) (y : Eˣ) :
    typeChar hv ψ hψ n α hα ξ hξ ⟨embGL v y, embGL_mem_jGroup hv _ y⟩ = ξ y := by
  rw [typeChar_apply hv ψ hψ n α hα ξ hξ _ y (by simp),
    typeCharAux_eq ψ hψ n α hα ξ _ y _ 1 (by simp)]
  simp

/-- A character $\Lambda$ of $E^\times U^m_{\mathfrak{A}}$, for $m \le [n/2] + 1$, is a type character for $(\alpha, \xi)$ if it agrees with $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$ and with $\xi$ on $E^\times$ (BH §15). -/
def IsTypeChar (m : ℕ) (hm : m ≤ n / 2 + 1) (Λ : jGroup v hv m →* ℂˣ) : Prop :=
  (∀ g : unitsFilt F A (n / 2 + 1),
    (Λ ⟨g, unitsFilt_le_jGroup hv m (unitsFilt_anti hm g.2)⟩ : ℂ) =
      psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα g) ∧
  ∀ y : Eˣ, Λ ⟨embGL v y, embGL_mem_jGroup hv m y⟩ = ξ y

/-- If a type character for $(\alpha, \xi)$ exists, then the pair is compatible. -/
theorem IsTypeChar.isCompatible {m : ℕ} {hm : m ≤ n / 2 + 1} {Λ : jGroup v hv m →* ℂˣ}
    (h : IsTypeChar hv ψ hψ n α hα ξ m hm Λ) : IsCompatible ψ n α ξ := by
  intro y hy
  have hmem := (hv.embGL_mem_unitsFilt_iff _ y).2 hy
  have h1 : (ξ y : ℂ) = psiAlpha F ψ hψ A n (Algebra.leftMulMatrix v α) hα ⟨embGL v y, hmem⟩ := by
    rw [← h.2 y]
    exact h.1 ⟨embGL v y, hmem⟩
  rw [h1]
  exact psiAlphaFun_embGL ψ v α y

/-- For a compatible pair, `typeChar` is a type character. -/
theorem isTypeChar_typeChar (hξ : IsCompatible ψ n α ξ) :
    IsTypeChar hv ψ hψ n α hα ξ (n / 2 + 1) le_rfl (typeChar hv ψ hψ n α hα ξ hξ) :=
  ⟨typeChar_apply_unitsFilt hv ψ hψ n α hα ξ hξ, typeChar_apply_embGL hv ψ hψ n α hα ξ hξ⟩

/-- A type character of $E^\times U^{[n/2]+1}_{\mathfrak{A}}$ is unique: it is `typeChar`. -/
theorem IsTypeChar.eq_typeChar {Λ : jGroup v hv (n / 2 + 1) →* ℂˣ}
    (h : IsTypeChar hv ψ hψ n α hα ξ (n / 2 + 1) le_rfl Λ) :
    Λ = typeChar hv ψ hψ n α hα ξ h.isCompatible := by
  ext g
  obtain ⟨y, hy⟩ := (mem_jGroup hv _ g).1 g.2
  have hg : Λ g = Λ ⟨embGL v y, embGL_mem_jGroup hv _ y⟩ *
      Λ ⟨(embGL v y)⁻¹ * g, unitsFilt_le_jGroup hv _ hy⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp)
  rw [typeChar_apply hv ψ hψ n α hα ξ _ g y hy, typeCharAux, hg, h.2 y, Units.val_mul,
    Units.val_mul, coe_psiAlphaUnits]
  congr 1
  exact h.1 ⟨_, hy⟩

/-- A type character of $E^\times U^{[n/2]+1}_{\mathfrak{A}}$ for $(\alpha, \xi)$ exists exactly when the pair is compatible, and then it is unique. -/
theorem existsUnique_isTypeChar_iff :
    (∃! Λ : jGroup v hv (n / 2 + 1) →* ℂˣ, IsTypeChar hv ψ hψ n α hα ξ (n / 2 + 1) le_rfl Λ) ↔
      IsCompatible ψ n α ξ := by
  constructor
  · rintro ⟨Λ, hΛ, -⟩
    exact hΛ.isCompatible
  · intro hξ
    exact ⟨_, isTypeChar_typeChar hv ψ hψ n α hα ξ hξ, fun Λ hΛ => hΛ.eq_typeChar⟩

/-- The cuspidal type data of BH §15 for the simple stratum $(\mathfrak{A}, n, \alpha)$ and the character $\xi$ of $E^\times$: the characters $\Lambda$ of $J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$ that agree with $\psi_\alpha$ on $U^{[n/2]+1}_{\mathfrak{A}}$ and restrict to $\xi$ on $E^\times$. -/
def cuspTypes : Set (jGroup v hv ((n + 1) / 2) →* ℂˣ) :=
  {Λ | IsTypeChar hv ψ hψ n α hα ξ ((n + 1) / 2) (by omega) Λ}

/-- Each member of `cuspTypes` gives a compatible pair. -/
theorem isCompatible_of_mem_cuspTypes {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ}
    (h : Λ ∈ cuspTypes hv ψ hψ n α hα ξ) : IsCompatible ψ n α ξ :=
  IsTypeChar.isCompatible hv ψ hψ n α hα ξ (hm := by omega) h

/-- For odd $n$, `cuspTypes` has exactly one member when the pair $(\alpha, \xi)$ is compatible, and no member otherwise (BH §15). -/
theorem existsUnique_mem_cuspTypes_iff (hodd : Odd n) :
    (∃! Λ, Λ ∈ cuspTypes hv ψ hψ n α hα ξ) ↔ IsCompatible ψ n α ξ := by
  have key : ∀ m (hm : m = n / 2 + 1),
      (∃! Λ : jGroup v hv m →* ℂˣ, IsTypeChar hv ψ hψ n α hα ξ m hm.le Λ) ↔
        IsCompatible ψ n α ξ := by
    intro m hm
    subst hm
    exact existsUnique_isTypeChar_iff hv ψ hψ n α hα ξ
  obtain ⟨k, rfl⟩ := hodd
  exact key _ (by omega)

end TypeChar

end Langlands.LocalGL2

namespace Langlands

universe w

section CompactInduction

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (J : Subgroup G) (Λ : J →* ℂˣ)

/-- The space of the compactly induced representation $c\text{-}\mathrm{Ind}_J^G \Lambda$: the functions $f : G \to \mathbb{C}$ with $f(jg) = \Lambda(j) f(g)$ for $j \in J$, that are invariant on the right under an open subgroup, and whose support lies in finitely many cosets $J s$. For $J$ open and compact modulo the centre, the last condition says that the support is compact modulo the centre. -/
def cIndSpace : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ (j : J) (g : G), f (j * g) = Λ j * f g) ∧
    (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, f (g * u) = f g) ∧
    ∃ S : Finset G, ∀ g, f g ≠ 0 → ∃ s ∈ S, g * s⁻¹ ∈ J}
  add_mem' := by
    classical
    rintro f f' ⟨h1, ⟨U, hU, hfU⟩, S, hS⟩ ⟨h1', ⟨U', hU', hfU'⟩, S', hS'⟩
    refine ⟨fun j g => ?_, ⟨U ⊓ U', hU.inter hU', fun g u hu => ?_⟩, S ∪ S', fun g hg => ?_⟩
    · simp only [Pi.add_apply, h1, h1', mul_add]
    · simp [hfU g u (Subgroup.mem_inf.1 hu).1, hfU' g u (Subgroup.mem_inf.1 hu).2]
    · by_cases h : f g = 0
      · have h' : f' g ≠ 0 := by simpa [h] using hg
        obtain ⟨s, hs, hsJ⟩ := hS' g h'
        exact ⟨s, Finset.mem_union_right _ hs, hsJ⟩
      · obtain ⟨s, hs, hsJ⟩ := hS g h
        exact ⟨s, Finset.mem_union_left _ hs, hsJ⟩
  zero_mem' := ⟨fun _ _ => by simp, ⟨⊤, by simp, fun _ _ _ => rfl⟩, ∅, fun _ hg => absurd rfl hg⟩
  smul_mem' c f := by
    rintro ⟨h1, ⟨U, hU, hfU⟩, S, hS⟩
    refine ⟨fun j g => ?_, ⟨U, hU, fun g u hu => ?_⟩, S, fun g hg => hS g ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1]
      ring
    · simp [hfU g u hu]
    · intro h
      apply hg
      simp [h]

/-- The space $c\text{-}\mathrm{Ind}_J^G \Lambda$ is stable under right translation. -/
theorem cIndSpace_stable : IsStableSubspace (rightTranslation G ℂ) (cIndSpace J Λ) := by
  classical
  rintro g f ⟨h1, ⟨U, hU, hfU⟩, S, hS⟩
  refine ⟨fun j x => ?_, ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, isOpen_comap_conj hU _,
    fun x u hu => ?_⟩, S.image (· * g⁻¹), fun x hx => ?_⟩
  · change f (j * x * g) = Λ j * f (x * g)
    rw [mul_assoc, h1]
  · change f (x * u * g) = f (x * g)
    have := hfU (x * g) _ (Subgroup.mem_comap.1 hu)
    simpa [mul_assoc] using this
  · obtain ⟨s, hs, hsJ⟩ := hS (x * g) hx
    refine ⟨s * g⁻¹, Finset.mem_image_of_mem _ hs, ?_⟩
    simpa [mul_assoc] using hsJ

namespace SmoothRep

/-- The compactly induced representation $c\text{-}\mathrm{Ind}_J^G \Lambda$ of a character $\Lambda$ of a subgroup $J$, with $G$ acting by right translation $(g \cdot f)(x) = f(xg)$. Its action is a group homomorphism from $G$ to the linear maps, and it is smooth. -/
def cInd : SmoothRep G where
  V := cIndSpace J Λ
  ρ := (rightTranslation G ℂ).subrepresentation _ (cIndSpace_stable J Λ)
  smooth f := by
    obtain ⟨U, hU, hfU⟩ := f.2.2.1
    refine Subgroup.isOpen_mono (H₁ := U) ?_ hU
    intro u hu
    rw [mem_vecStabilizer]
    exact Subtype.ext (funext fun g => hfU g u hu)

variable {J Λ}

/-- The function $G \to \mathbb{C}$ of a vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
def cInd.toFun (f : (cInd J Λ).V) : G → ℂ :=
  (show cIndSpace J Λ from f).1

/-- A vector $f$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ satisfies $f(jg) = \Lambda(j) f(g)$. -/
theorem cInd.toFun_mul_left (f : (cInd J Λ).V) (j : J) (g : G) :
    cInd.toFun f (j * g) = Λ j * cInd.toFun f g :=
  (show cIndSpace J Λ from f).2.1 j g

/-- The group $G$ acts on $c\text{-}\mathrm{Ind}_J^G \Lambda$ by right translation. -/
theorem cInd.toFun_ρ (f : (cInd J Λ).V) (g x : G) :
    cInd.toFun ((cInd J Λ).ρ g f) x = cInd.toFun f (x * g) :=
  rfl

/-- A vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ is determined by its function. -/
theorem cInd.ext {f f' : (cInd J Λ).V} (h : ∀ x, cInd.toFun f x = cInd.toFun f' x) : f = f' :=
  Subtype.ext (funext h)

end SmoothRep

open scoped Classical in
/-- The function on $G$ that is $\Lambda$ on $J$ and $0$ outside $J$. -/
noncomputable def cIndBasicFun (x : G) : ℂ :=
  if h : x ∈ J then (Λ ⟨x, h⟩ : ℂ) else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The value of `cIndBasicFun` on $J$. -/
theorem cIndBasicFun_of_mem {x : G} (h : x ∈ J) : cIndBasicFun J Λ x = Λ ⟨x, h⟩ := by
  simp [cIndBasicFun, h]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The value of `cIndBasicFun` outside $J$. -/
theorem cIndBasicFun_of_not_mem {x : G} (h : x ∉ J) : cIndBasicFun J Λ x = 0 := by
  simp [cIndBasicFun, h]

omit [IsTopologicalGroup G] in
/-- For an open subgroup $J$ and a character $\Lambda$ with open kernel, the extension of $\Lambda$ by $0$ lies in $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
theorem cIndBasicFun_mem (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    cIndBasicFun J Λ ∈ cIndSpace J Λ := by
  refine ⟨fun j x => ?_, ⟨Λ.ker.map J.subtype, ?_, fun x u hu => ?_⟩, {1}, fun x hx => ?_⟩
  · by_cases hx : x ∈ J
    · rw [cIndBasicFun_of_mem J Λ (J.mul_mem j.2 hx), cIndBasicFun_of_mem J Λ hx, ← Units.val_mul,
        ← map_mul]
      rfl
    · rw [cIndBasicFun_of_not_mem J Λ hx, cIndBasicFun_of_not_mem J Λ
        (fun h => hx ((J.mul_mem_cancel_left j.2).1 h)), mul_zero]
  · rw [Subgroup.coe_map]
    exact hJ.isOpenMap_subtype_val _ hΛ
  · obtain ⟨k, hk, rfl⟩ := hu
    change cIndBasicFun J Λ (x * k) = _
    by_cases hx : x ∈ J
    · rw [cIndBasicFun_of_mem J Λ (J.mul_mem hx k.2), cIndBasicFun_of_mem J Λ hx]
      have e : (⟨x * k, J.mul_mem hx k.2⟩ : J) = ⟨x, hx⟩ * k := rfl
      rw [e, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
    · rw [cIndBasicFun_of_not_mem J Λ hx, cIndBasicFun_of_not_mem J Λ
        (fun h => hx ((J.mul_mem_cancel_right k.2).1 h))]
  · by_cases h : x ∈ J
    · exact ⟨1, Finset.mem_singleton_self 1, by simpa using h⟩
    · exact absurd (cIndBasicFun_of_not_mem J Λ h) hx

/-- The vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ that is $\Lambda$ on $J$ and $0$ outside $J$. -/
noncomputable def cIndBasic (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    (SmoothRep.cInd J Λ).V :=
  (⟨cIndBasicFun J Λ, cIndBasicFun_mem J Λ hJ hΛ⟩ : cIndSpace J Λ)

/-- The function of `cIndBasic`. -/
theorem cInd.toFun_cIndBasic (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    SmoothRep.cInd.toFun (cIndBasic J Λ hJ hΛ) = cIndBasicFun J Λ :=
  rfl

/-- For an open subgroup $J$ and a character $\Lambda$ with open kernel, $c\text{-}\mathrm{Ind}_J^G \Lambda$ is not zero. -/
theorem nontrivial_cInd (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    Nontrivial (SmoothRep.cInd J Λ).V := by
  refine ⟨⟨cIndBasic J Λ hJ hΛ, 0, fun h => ?_⟩⟩
  have h1 := congrArg (fun f => SmoothRep.cInd.toFun f 1) h
  simp only [cInd.toFun_cIndBasic, cIndBasicFun_of_mem J Λ J.one_mem] at h1
  have h0 : SmoothRep.cInd.toFun (0 : (SmoothRep.cInd J Λ).V) 1 = 0 := rfl
  rw [h0] at h1
  have : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [this, map_one, Units.val_one] at h1
  exact one_ne_zero h1

/-- An element $g \in G$ intertwines $\Lambda$ if $\Lambda(g x g^{-1}) = \Lambda(x)$ for each $x \in J \cap g^{-1} J g$. The intertwining of $\Lambda$ is the set of these $g$. -/
def Intertwines (g : G) : Prop :=
  ∀ x : J, ∀ h : g * x * g⁻¹ ∈ J, Λ ⟨g * x * g⁻¹, h⟩ = Λ x

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Each element of $J$ intertwines $\Lambda$. -/
theorem intertwines_of_mem {g : G} (hg : g ∈ J) : Intertwines J Λ g := by
  intro x h
  have e : (⟨g * x * g⁻¹, h⟩ : J) = ⟨g, hg⟩ * x * (⟨g, hg⟩ : J)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-- A function $\varphi : G \to \mathbb{C}$ is bi-equivariant for $\Lambda$ if $\varphi(j g j') = \Lambda(j) \varphi(g) \Lambda(j')$ for $j, j' \in J$. The bi-equivariant functions with compact support modulo the centre form the Hecke algebra of $\Lambda$, which is $\mathrm{End}_G(c\text{-}\mathrm{Ind}_J^G \Lambda)$. -/
def IsBiEquivariant (φ : G → ℂ) : Prop :=
  ∀ (j : J) (g : G) (j' : J), φ (j * g * j') = Λ j * φ g * Λ j'

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A bi-equivariant function is zero outside the intertwining of $\Lambda$ (BH 11.1). -/
theorem IsBiEquivariant.intertwines {φ : G → ℂ} (hφ : IsBiEquivariant J Λ φ) {g : G}
    (hg : φ g ≠ 0) : Intertwines J Λ g := by
  intro x h
  have e1 := hφ ⟨_, h⟩ g 1
  have e2 := hφ 1 g x
  have e : ((⟨g * x * g⁻¹, h⟩ : J) : G) * g * ((1 : J) : G) = ((1 : J) : G) * g * x := by
    simp [mul_assoc]
  rw [e, e2, map_one] at e1
  simp only [Units.val_one, one_mul, mul_one] at e1
  apply Units.ext
  apply mul_left_cancel₀ hg
  linear_combination -e1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If the intertwining of $\Lambda$ is $J$, then each bi-equivariant function is $\varphi(1)$ times the extension of $\Lambda$ by $0$. So the Hecke algebra of $\Lambda$ has dimension at most one. -/
theorem IsBiEquivariant.eq_smul_cIndBasicFun (hI : ∀ g, Intertwines J Λ g → g ∈ J)
    {φ : G → ℂ} (hφ : IsBiEquivariant J Λ φ) (g : G) : φ g = φ 1 * cIndBasicFun J Λ g := by
  by_cases hg : g ∈ J
  · have e := hφ ⟨g, hg⟩ 1 1
    rw [cIndBasicFun_of_mem J Λ hg]
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one] at e
    rw [e, mul_comm]
  · rw [cIndBasicFun_of_not_mem J Λ hg, mul_zero]
    by_contra h
    exact hg (hI g (hφ.intertwines J Λ h))

/-- Let $J$ be open, $\Lambda$ a character of $J$ with open kernel, and assume that the intertwining of $\Lambda$ is $J$. Then each vector $f$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ on which $J$ acts by $\Lambda$ is a multiple of the vector `cIndBasic`, which is supported on $J$. This is the main step of the irreducibility criterion of BH 11.4. -/
theorem eq_smul_cIndBasic_of_isotypic (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))
    (hI : ∀ g, Intertwines J Λ g → g ∈ J) (f : (SmoothRep.cInd J Λ).V)
    (hf : ∀ j : J, (SmoothRep.cInd J Λ).ρ j f = (Λ j : ℂ) • f) :
    f = SmoothRep.cInd.toFun f 1 • cIndBasic J Λ hJ hΛ := by
  have hφ : IsBiEquivariant J Λ (SmoothRep.cInd.toFun f) := by
    intro j g j'
    rw [mul_assoc, SmoothRep.cInd.toFun_mul_left, ← SmoothRep.cInd.toFun_ρ, hf j']
    change Λ j * ((Λ j' : ℂ) * SmoothRep.cInd.toFun f g) = _
    ring
  refine SmoothRep.cInd.ext fun x => ?_
  rw [hφ.eq_smul_cIndBasicFun J Λ hI x]
  rfl

end CompactInduction

end Langlands

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel Matrix

section CuspidalInduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}
variable (hv : IsAdapted A v) (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) (n : ℕ) (α : E)
  (hα : Algebra.leftMulMatrix v α ∈ radPow F A (-n)) (ξ : Eˣ →* ℂˣ)

/-- A type character is trivial on $U^{n+1}_{\mathfrak{A}}$, so its kernel is open. -/
theorem IsTypeChar.isOpen_ker {m : ℕ} {hm : m ≤ n / 2 + 1} {Λ : jGroup v hv m →* ℂˣ}
    (h : IsTypeChar hv ψ hψ n α hα ξ m hm Λ) : IsOpen (Λ.ker : Set (jGroup v hv m)) := by
  refine Subgroup.isOpen_mono (H₁ := (unitsFilt F A (n + 1)).subgroupOf (jGroup v hv m)) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hg' : (g : GL (Fin 2) F) ∈ unitsFilt F A (n / 2 + 1) := unitsFilt_anti (by omega) hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have h1 := h.1 ⟨g, hg'⟩
    rw [psiAlpha_eq_one ψ hψ A n _ hα ⟨g, hg'⟩ hg] at h1
    exact h1
  · rw [Subgroup.coe_subgroupOf]
    exact (isOpen_unitsFilt A (n + 1)).preimage continuous_subtype_val

/-- The representation $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ of $GL_2(F)$ for a cuspidal type $\Lambda$ (BH §15). -/
def cuspInd (Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ) : SmoothRep (GL (Fin 2) F) :=
  SmoothRep.cInd (jGroup v hv ((n + 1) / 2)) Λ

/-- For a cuspidal type $\Lambda$, the representation $c\text{-}\mathrm{Ind}_{J_\alpha}^G \Lambda$ is not zero. -/
theorem nontrivial_cuspInd {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ}
    (h : Λ ∈ cuspTypes hv ψ hψ n α hα ξ) : Nontrivial (cuspInd hv n Λ).V :=
  nontrivial_cInd _ Λ (isOpen_jGroup hv _) (IsTypeChar.isOpen_ker hv ψ hψ n α hα ξ (hm := by omega) h)

end CuspidalInduction

end Langlands.LocalGL2
