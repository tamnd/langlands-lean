/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.GroupTheory.Transfer
import Langlands.WeilGroup.Restrict
import Langlands.WeilGroup.Dense
import Langlands.Statements.WeilDeligne

/-!
# Induction from a subgroup of index 2

Let $H$ be a subgroup of index $2$ of a group $W$, let $s \in W$ with $s \notin H$, and let $\varphi : H \to \mathbb{C}^\times$ be a character. This file defines the induced representation $\mathrm{Ind}_H^W \varphi : W \to GL_2(\mathbb{C})$ as an explicit matrix representation in the basis $1, s$, and proves its basic properties. Then it applies this to $H = W_L \le W_K$ for a quadratic separable extension $L / K$ of a nonarchimedean local field $K$.

Let $\dot\varphi$ be the extension of $\varphi$ by zero. The matrix of $\mathrm{Ind}_H^W \varphi$ at $w$ has the entry $\dot\varphi(g_i^{-1} w g_j)$ at $(i, j)$, with $g_0 = 1$ and $g_1 = s$. The conjugate character is $\varphi^s(h) = \varphi(s^{-1} h s)$.

## Main definitions

* `Langlands.LocalGL2.ind`: the induced representation $\mathrm{Ind}_H^W \varphi$.
* `Langlands.LocalGL2.conjChar`: the conjugate character $\varphi^s$.
* `Langlands.LocalGL2.IsIrreducibleRep`: irreducibility of a representation $W \to GL_n(\mathbb{C})$.
* `Langlands.LocalGL2.RepIso`: isomorphism of representations $W \to GL_n(\mathbb{C})$.
* `Langlands.LocalGL2.twistRep`: the twist of a representation by a character of $W$.
* `Langlands.LocalGL2.signChar`: the sign character of $W / H$.
* `Langlands.LocalGL2.indWD`: the Weil-Deligne representation $(\mathrm{Ind}_{W_L}^{W_K} \varphi, 0)$ for a quadratic separable extension $L / K$.

## Main results

* `Langlands.LocalGL2.ind_apply_of_mem`: on $H$, the representation $\mathrm{Ind}_H^W \varphi$ is $\varphi \oplus \varphi^s$.
* `Langlands.LocalGL2.isIrreducibleRep_ind_iff`: $\mathrm{Ind}_H^W \varphi$ is irreducible if and only if $\varphi^s \ne \varphi$.
* `Langlands.LocalGL2.repIso_ind_conjChar`: $\mathrm{Ind}_H^W \varphi \cong \mathrm{Ind}_H^W \varphi^s$.
* `Langlands.LocalGL2.repIso_ind_mul_restrict`: $\mathrm{Ind}_H^W (\varphi \cdot \chi|_H) \cong \chi \otimes \mathrm{Ind}_H^W \varphi$.
* `Langlands.LocalGL2.det_ind_eq_signChar_mul_transfer`: $\det \mathrm{Ind}_H^W \varphi$ is the sign character of $W / H$ times the transfer of $\varphi$.
* `Langlands.LocalGL2.isOpen_ker_ind`: if $H$ is open and $\varphi$ is smooth, then $\mathrm{Ind}_H^W \varphi$ is smooth.
* `Langlands.LocalGL2.isSemisimple_ind`: each matrix $\mathrm{Ind}_H^W \varphi(w)$ is semisimple.
* `Langlands.LocalGL2.repIso_ind_of_eigenvector`: Frobenius reciprocity, the easy direction. If $\varphi^s \ne \varphi$ and $H$ acts by $\varphi$ on a nonzero vector of a 2-dimensional representation $\rho$, then $\rho \cong \mathrm{Ind}_H^W \varphi$.
* `Langlands.LocalGL2.index_restrictSubgroup`: for a finite separable extension $L / K$, the subgroup $W_L$ of $W_K$ has index $[L : K]$. It is open by `Langlands.WeilGroup.isOpen_restrictSubgroup`.
* `Langlands.LocalGL2.WeilDeligneRep.N_eq_zero_of_isIrreducibleRep`: if the representation part of a Weil-Deligne representation is irreducible, then $N = 0$.
* `Langlands.LocalGL2.isIrreducible_indWD`: `indWD` is irreducible if $\varphi^s \ne \varphi$.
* `Langlands.LocalGL2.iso_indWD_of_eigenvector`: Frobenius reciprocity for `indWD`.

## Implementation notes

The induced representation is a concrete matrix representation. It does not use the general induced module of Mathlib. The proofs use only that $H$ has index $2$, so that $a s \in H$ exactly when $a \notin H$.

The index of $W_L$ is computed with the action of $W_K$ on the $K$-embeddings $L \to \bar K$. The action is transitive because the image of $W_K$ in $\mathrm{Gal}(\bar K / K)$ is dense. The number of embeddings is the separable degree, so the separability of $L / K$ is necessary here: the field $\bar K$ is the algebraic closure and not the separable closure.

## References

* J.-P. Serre, Linear representations of finite groups, Section 7. Mackey's irreducibility criterion is in 7.4.
* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Chapter 7.

## What is still open

* The converse direction of Frobenius reciprocity, and the general statement $\mathrm{Hom}_W(\rho, \mathrm{Ind}_H^W \varphi) \cong \mathrm{Hom}_H(\rho|_H, \varphi)$, are not proved.
* The file does not prove that the isomorphism class of `indWD` is independent of the choice of $s$.
* The link between the transfer $W_K \to W_L^{ab}$ and the norm map of local class field theory is not proved here.
-/

namespace Langlands.LocalGL2

open Matrix

section Abstract

variable {W : Type*} [Group W] {H : Subgroup W}

/-- The extension by zero of a character of $H$ to a function on $W$. -/
noncomputable def extChar (φ : H →* ℂˣ) (w : W) : ℂ := by
  classical
  exact if h : w ∈ H then ((φ ⟨w, h⟩ : ℂˣ) : ℂ) else 0

/-- On $H$, the extension by zero is $\varphi$. -/
theorem extChar_of_mem (φ : H →* ℂˣ) {w : W} (h : w ∈ H) : extChar φ w = φ ⟨w, h⟩ := by
  simp [extChar, h]

/-- Outside $H$, the extension by zero is $0$. -/
theorem extChar_of_not_mem (φ : H →* ℂˣ) {w : W} (h : w ∉ H) : extChar φ w = 0 := by
  simp [extChar, h]

/-- The extension by zero is multiplicative when the left factor is in $H$. -/
theorem extChar_mul_of_mem_left (φ : H →* ℂˣ) {a : W} (b : W) (ha : a ∈ H) :
    extChar φ (a * b) = extChar φ a * extChar φ b := by
  by_cases hb : b ∈ H
  · rw [extChar_of_mem φ (H.mul_mem ha hb), extChar_of_mem φ ha, extChar_of_mem φ hb,
      ← Units.val_mul, ← map_mul]
    rfl
  · rw [extChar_of_not_mem φ hb, extChar_of_not_mem φ (by rwa [H.mul_mem_cancel_left ha]),
      mul_zero]

/-- The extension by zero is multiplicative when the right factor is in $H$. -/
theorem extChar_mul_of_mem_right (φ : H →* ℂˣ) (a : W) {b : W} (hb : b ∈ H) :
    extChar φ (a * b) = extChar φ a * extChar φ b := by
  by_cases ha : a ∈ H
  · exact extChar_mul_of_mem_left φ b ha
  · rw [extChar_of_not_mem φ ha, extChar_of_not_mem φ (by rwa [H.mul_mem_cancel_right hb]),
      zero_mul]

/-- The extension by zero takes the value $1$ at $1$. -/
theorem extChar_one (φ : H →* ℂˣ) : extChar φ (1 : W) = 1 := by
  rw [extChar_of_mem φ H.one_mem]
  simp [show (⟨1, H.one_mem⟩ : H) = 1 from rfl]

/-- The extension by zero is invariant under conjugation by elements of $H$, because $\mathbb{C}^\times$ is commutative. -/
theorem extChar_conj_of_mem (φ : H →* ℂˣ) {h : W} (hh : h ∈ H) (x : W) :
    extChar φ (h⁻¹ * x * h) = extChar φ x := by
  rw [extChar_mul_of_mem_right φ _ hh, extChar_mul_of_mem_left φ _ (H.inv_mem hh), mul_comm,
    ← mul_assoc, ← extChar_mul_of_mem_left φ _ hh, mul_inv_cancel, extChar_one, one_mul]

section IndexTwo

variable (hH : H.index = 2) {s : W} (hs : s ∉ H)
include hH hs

/-- For $s \notin H$, the product $a s$ is in $H$ if and only if $a$ is not in $H$. -/
theorem mul_s_mem_iff (a : W) : a * s ∈ H ↔ a ∉ H := by
  rw [Subgroup.mul_mem_iff_of_index_two hH]; tauto

/-- For $s \notin H$, the product $s^{-1} a$ is in $H$ if and only if $a$ is not in $H$. -/
theorem s_inv_mul_mem_iff (a : W) : s⁻¹ * a ∈ H ↔ a ∉ H := by
  rw [Subgroup.mul_mem_iff_of_index_two hH, H.inv_mem_iff]; tauto

/-- For $s \notin H$, the square $s s$ is in $H$. -/
theorem s_mul_s_mem : s * s ∈ H := by
  rw [mul_s_mem_iff hH hs]; exact hs

/-- The key identity behind the multiplicativity of the induced matrices. -/
theorem extChar_mul_add (φ : H →* ℂˣ) (a c : W) :
    extChar φ a * extChar φ c + extChar φ (a * s) * extChar φ (s⁻¹ * c) = extChar φ (a * c) := by
  by_cases ha : a ∈ H
  · rw [extChar_of_not_mem φ (w := a * s) (by rw [mul_s_mem_iff hH hs]; exact not_not.2 ha), zero_mul,
      add_zero, extChar_mul_of_mem_left φ _ ha]
  · have has : a * s ∈ H := (mul_s_mem_iff hH hs a).2 ha
    rw [extChar_of_not_mem φ ha, zero_mul, zero_add, ← extChar_mul_of_mem_left φ _ has,
      show a * s * (s⁻¹ * c) = a * c by group]

end IndexTwo

/-- The coset representatives $1, s$ of $H$ in $W$. -/
def reps (s : W) : Fin 2 → W := ![1, s]

/-- The matrix of $\mathrm{Ind}_H^W \varphi$ at $w$ in the basis $1, s$: the entry $(i, j)$ is $\dot\varphi(g_i^{-1} w g_j)$, where $g_0 = 1$, $g_1 = s$ and $\dot\varphi$ is the extension of $\varphi$ by zero. -/
noncomputable def indMatrix (φ : H →* ℂˣ) (s w : W) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => extChar φ ((reps s i)⁻¹ * w * reps s j)

/-- The entries of `indMatrix`. -/
theorem indMatrix_apply (φ : H →* ℂˣ) (s w : W) (i j : Fin 2) :
    indMatrix φ s w i j = extChar φ ((reps s i)⁻¹ * w * reps s j) := rfl

/-- The first coset representative is $1$. -/
@[simp] theorem reps_zero (s : W) : reps s 0 = 1 := rfl
/-- The second coset representative is $s$. -/
@[simp] theorem reps_one (s : W) : reps s 1 = s := rfl

/-- The matrices of the induced representation are multiplicative. -/
theorem indMatrix_mul (hH : H.index = 2) {s : W} (hs : s ∉ H) (φ : H →* ℂˣ) (v w : W) :
    indMatrix φ s (v * w) = indMatrix φ s v * indMatrix φ s w := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [indMatrix_apply, reps_zero, reps_one, inv_one, mul_one, one_mul]
  have := extChar_mul_add hH hs φ ((reps s i)⁻¹ * v) (w * reps s j)
  simp only [mul_assoc] at this ⊢
  exact this.symm

/-- The matrix of the induced representation at $1$ is the identity. -/
theorem indMatrix_one {s : W} (hs : s ∉ H) (φ : H →* ℂˣ) :
    indMatrix φ s 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [indMatrix_apply, extChar_one, extChar_of_not_mem φ hs,
      extChar_of_not_mem φ (show s⁻¹ ∉ H by rwa [H.inv_mem_iff])]


/-- The induced representation $\mathrm{Ind}_H^W \varphi : W \to GL_2(\mathbb{C})$ for a subgroup $H$ of index $2$ and an element $s \notin H$, in the basis $1, s$. -/
noncomputable def ind (hH : H.index = 2) {s : W} (hs : s ∉ H) (φ : H →* ℂˣ) : W →* GL (Fin 2) ℂ :=
  MonoidHom.toHomUnits
    { toFun := indMatrix φ s
      map_one' := indMatrix_one hs φ
      map_mul' := indMatrix_mul hH hs φ }

section IndexTwo

variable (hH : H.index = 2) {s : W} (hs : s ∉ H)
include hH hs

/-- The matrix of `ind` at $w$ is `indMatrix`. -/
theorem coe_ind (φ : H →* ℂˣ) (w : W) :
    ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = indMatrix φ s w := rfl

/-- The entries of the matrix of `ind` at $w$. -/
theorem ind_apply (φ : H →* ℂˣ) (w : W) (i j : Fin 2) :
    ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      extChar φ ((reps s i)⁻¹ * w * reps s j) := rfl

omit hs in
/-- For $H$ of index $2$, the subgroup $H$ is normal, so $s^{-1} h s \in H$ for $h \in H$. -/
theorem conj_mem (s : W) {h : W} (hh : h ∈ H) : s⁻¹ * h * s ∈ H := by
  simpa using (Subgroup.normal_of_index_eq_two hH).conj_mem h hh s⁻¹

/-- The conjugate character $\varphi^s(h) = \varphi(s^{-1} h s)$ of $H$. -/
noncomputable def conjChar (s : W) (φ : H →* ℂˣ) : H →* ℂˣ where
  toFun h := φ ⟨s⁻¹ * h * s, conj_mem hH s h.2⟩
  map_one' := by
    rw [show (⟨s⁻¹ * ((1 : H) : W) * s, conj_mem hH s (1 : H).2⟩ : H) = 1 from
      Subtype.ext (by simp), map_one]
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])

omit hs in
/-- The value of the conjugate character. -/
theorem conjChar_apply (s : W) (φ : H →* ℂˣ) (h : H) :
    conjChar hH s φ h = φ ⟨s⁻¹ * h * s, conj_mem hH s h.2⟩ := rfl

/-- The extension by zero of $\varphi^s$ at $x$ is the extension by zero of $\varphi$ at $s^{-1} x s$. -/
theorem extChar_conj (φ : H →* ℂˣ) (x : W) :
    extChar (conjChar hH s φ) x = extChar φ (s⁻¹ * x * s) := by
  by_cases hx : x ∈ H
  · rw [extChar_of_mem _ hx, extChar_of_mem _ (conj_mem hH s hx)]; rfl
  · have : s⁻¹ * x * s ∉ H := by
      rwa [mul_s_mem_iff hH hs, s_inv_mul_mem_iff hH hs, not_not]
    rw [extChar_of_not_mem _ hx, extChar_of_not_mem _ this]

/-- On $H$, the induced representation is $\varphi \oplus \varphi^s$. -/
theorem ind_apply_of_mem (φ : H →* ℂˣ) (h : H) :
    ((ind hH hs φ h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![(φ h : ℂ), (conjChar hH s φ h : ℂ)] := by
  ext i j
  have h1 : (h : W) * s ∉ H := by rw [mul_s_mem_iff hH hs, not_not]; exact h.2
  have h2 : s⁻¹ * (h : W) ∉ H := by rw [s_inv_mul_mem_iff hH hs, not_not]; exact h.2
  fin_cases i <;> fin_cases j <;>
    simp [ind_apply, extChar_of_mem φ h.2, extChar_of_not_mem φ h1, extChar_of_not_mem φ h2,
      conjChar_apply, extChar_of_mem φ (conj_mem hH s h.2)]

/-- The action of the matrix of `ind` at $w$ on a vector of $\mathbb{C}^2$. -/
theorem ind_mulVec (φ : H →* ℂˣ) (w : W) (v : Fin 2 → ℂ) :
    ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v =
      ![extChar φ w * v 0 + extChar φ (w * s) * v 1,
        extChar φ (s⁻¹ * w) * v 0 + extChar φ (s⁻¹ * w * s) * v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ind_apply]

omit hH in
/-- The extension by zero vanishes at $s$. -/
theorem extChar_s (φ : H →* ℂˣ) : extChar φ s = 0 := extChar_of_not_mem φ hs

/-- The extension by zero does not vanish at $s s$. -/
theorem extChar_s_mul_s_ne_zero (φ : H →* ℂˣ) : extChar φ (s * s) ≠ 0 := by
  rw [extChar_of_mem φ (s_mul_s_mem hH hs)]; exact Units.ne_zero _

/-- The action of the matrix of `ind` at $s$ on a vector of $\mathbb{C}^2$. -/
theorem ind_s_mulVec (φ : H →* ℂˣ) (v : Fin 2 → ℂ) :
    ((ind hH hs φ s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v =
      ![extChar φ (s * s) * v 1, v 0] := by
  rw [ind_mulVec hH hs]
  ext i
  fin_cases i <;> simp [extChar_s hs, extChar_one]

end IndexTwo

/-- A representation $\rho : W \to GL_n(\mathbb{C})$ is irreducible if $n > 0$ and the only subspaces of $\mathbb{C}^n$ stable under $\rho(W)$ are $0$ and $\mathbb{C}^n$. This is the condition of `Langlands.WeilDeligneRep.IsIrreducible` without the monodromy operator. -/
def IsIrreducibleRep {n : ℕ} (ρ : W →* GL (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ V : Submodule ℂ (Fin n → ℂ),
    (∀ w, V ≤ V.comap (Matrix.toLin' (ρ w : Matrix (Fin n) (Fin n) ℂ))) → V = ⊥ ∨ V = ⊤

section IndexTwo

variable (hH : H.index = 2) {s : W} (hs : s ∉ H)
include hH hs

/-- If $\varphi^s \ne \varphi$, then $\mathrm{Ind}_H^W \varphi$ is irreducible. -/
theorem isIrreducibleRep_ind {φ : H →* ℂˣ} (hφ : conjChar hH s φ ≠ φ) :
    IsIrreducibleRep (ind hH hs φ) := by
  refine ⟨two_pos, fun V hV => ?_⟩
  have hV' : ∀ w, ∀ x ∈ V,
      ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x ∈ V := fun w x hx => by
    simpa [Matrix.toLin'_apply] using hV w hx
  obtain ⟨h0, hh0⟩ := DFunLike.ne_iff.1 hφ
  set a : ℂ := (φ h0 : ℂ)
  set b : ℂ := (conjChar hH s φ h0 : ℂ)
  have hab : a - b ≠ 0 := sub_ne_zero.2 fun h => hh0 (Units.val_injective h).symm
  have hdiag : ∀ x : Fin 2 → ℂ,
      ((ind hH hs φ h0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x = ![a * x 0, b * x 1] := by
    intro x
    rw [ind_apply_of_mem hH hs]
    ext i; fin_cases i <;> simp [Matrix.mulVec_diagonal, a, b]
  have hc : extChar φ (s * s) ≠ 0 := extChar_s_mul_s_ne_zero hH hs φ
  have e01 : (![1, 0] : Fin 2 → ℂ) ∈ V → (![0, 1] : Fin 2 → ℂ) ∈ V := fun h => by
    have := hV' s _ h
    rw [ind_s_mulVec hH hs] at this
    simpa using this
  have e10 : (![0, 1] : Fin 2 → ℂ) ∈ V → (![1, 0] : Fin 2 → ℂ) ∈ V := fun h => by
    have := V.smul_mem (extChar φ (s * s))⁻¹ (hV' s _ h)
    rw [ind_s_mulVec hH hs] at this
    convert this using 1
    ext i; fin_cases i <;> simp [inv_mul_cancel₀ hc]
  have htop : (![1, 0] : Fin 2 → ℂ) ∈ V → V = ⊤ := fun h0 => by
    have h1 := e01 h0
    refine Submodule.eq_top_iff'.2 fun x => ?_
    convert V.add_mem (V.smul_mem (x 0) h0) (V.smul_mem (x 1) h1) using 1
    ext i; fin_cases i <;> simp
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  by_cases hx : v 0 = 0
  · have hy : v 1 ≠ 0 := fun hy => hv0 (by ext i; fin_cases i <;> simp [hx, hy])
    have hmem := V.smul_mem ((b - a) * v 1)⁻¹ (V.sub_mem (hV' h0 v hv) (V.smul_mem a hv))
    rw [hdiag] at hmem
    refine htop (e10 ?_)
    convert hmem using 1
    ext i; fin_cases i
    · simp [Matrix.vecHead, Matrix.vecTail, hx]
    · have : b - a ≠ 0 := fun h => hab (by linear_combination -h)
      simp [Matrix.vecHead, Matrix.vecTail]; field_simp
  · have hmem := V.smul_mem ((a - b) * v 0)⁻¹ (V.sub_mem (hV' h0 v hv) (V.smul_mem b hv))
    rw [hdiag] at hmem
    refine htop ?_
    convert hmem using 1
    ext i; fin_cases i
    · simp [Matrix.vecHead, Matrix.vecTail]; field_simp
    · simp [Matrix.vecHead, Matrix.vecTail]

/-- If $\varphi^s = \varphi$, then $\mathrm{Ind}_H^W \varphi$ is not irreducible: an eigenvector of $\rho(s)$ spans a stable line. -/
theorem not_isIrreducibleRep_ind {φ : H →* ℂˣ} (hφ : conjChar hH s φ = φ) :
    ¬ IsIrreducibleRep (ind hH hs φ) := by
  rintro ⟨-, hirr⟩
  set c := extChar φ (s * s)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  set v : Fin 2 → ℂ := ![r, 1]
  have hstab : ∀ w, (ℂ ∙ v) ≤ (ℂ ∙ v).comap
      (Matrix.toLin' ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    intro w
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, Matrix.toLin'_apply,
      ind_mulVec hH hs, Submodule.mem_span_singleton]
    by_cases hw : w ∈ H
    · refine ⟨extChar φ w, ?_⟩
      have h1 : w * s ∉ H := by rw [mul_s_mem_iff hH hs, not_not]; exact hw
      have h2 : s⁻¹ * w ∉ H := by rw [s_inv_mul_mem_iff hH hs, not_not]; exact hw
      have h3 : extChar φ (s⁻¹ * w * s) = extChar φ w := by
        rw [← extChar_conj hH hs, hφ]
      ext i; fin_cases i <;> simp [v, extChar_of_not_mem φ h1, extChar_of_not_mem φ h2, h3, mul_comm]
    · refine ⟨extChar φ (s⁻¹ * w) * r, ?_⟩
      have h1 : s⁻¹ * w * s ∉ H := by
        rwa [mul_s_mem_iff hH hs, s_inv_mul_mem_iff hH hs, not_not]
      have h3 : extChar φ (w * s) = c * extChar φ (s⁻¹ * w) := by
        rw [show w * s = s * s * (s⁻¹ * (s⁻¹ * w) * s) by group,
          extChar_mul_of_mem_left φ _ (s_mul_s_mem hH hs), ← extChar_conj hH hs, hφ]
      ext i; fin_cases i
      · simp [v, extChar_of_not_mem φ hw, h3, ← hr]; ring
      · simp [v, extChar_of_not_mem φ h1]
  rcases hirr _ hstab with h | h
  · have : v ∈ (ℂ ∙ v) := Submodule.mem_span_singleton_self v
    rw [h, Submodule.mem_bot] at this
    simpa [v] using congrFun this 1
  · have : (![1, 0] : Fin 2 → ℂ) ∈ (ℂ ∙ v) := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 this
    have h0 := congrFun ht 0
    have h1 := congrFun ht 1
    simp [v] at h0 h1
    simp [h1] at h0

/-- $\mathrm{Ind}_H^W \varphi$ is irreducible exactly when $\varphi^s \ne \varphi$ (Serre, Linear representations of finite groups, 7.4, Mackey's criterion). -/
theorem isIrreducibleRep_ind_iff (φ : H →* ℂˣ) :
    IsIrreducibleRep (ind hH hs φ) ↔ conjChar hH s φ ≠ φ :=
  ⟨fun h hφ => not_isIrreducibleRep_ind hH hs hφ h, isIrreducibleRep_ind hH hs⟩

end IndexTwo

/-- Two representations $\rho, \rho' : W \to GL_n(\mathbb{C})$ are isomorphic if one matrix $g$ conjugates $\rho$ to $\rho'$. -/
def RepIso {n : ℕ} (ρ ρ' : W →* GL (Fin n) ℂ) : Prop :=
  ∃ g : GL (Fin n) ℂ, ∀ w, ρ' w = g * ρ w * g⁻¹

/-- A matrix $g$ with $\rho'(w) g = g \rho(w)$ for all $w$ gives an isomorphism of $\rho$ with $\rho'$. -/
theorem repIso_of_mul_eq {n : ℕ} {ρ ρ' : W →* GL (Fin n) ℂ} (g : GL (Fin n) ℂ)
    (h : ∀ w, (ρ' w : Matrix (Fin n) (Fin n) ℂ) * g = g * ρ w) : RepIso ρ ρ' :=
  ⟨g, fun w => eq_mul_inv_iff_mul_eq.2 (Units.ext (by simpa using h w))⟩

/-- Irreducibility is preserved by isomorphism of representations. -/
theorem isIrreducibleRep_of_repIso {n : ℕ} {ρ ρ' : W →* GL (Fin n) ℂ} (h : RepIso ρ ρ')
    (hρ : IsIrreducibleRep ρ) : IsIrreducibleRep ρ' := by
  obtain ⟨g, hg⟩ := h
  have hgg : ∀ y : Fin n → ℂ, (g : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      ((g⁻¹ : GL (Fin n) ℂ) *ᵥ y) = y := fun y => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hcomm : ∀ w x, (ρ' w : Matrix (Fin n) (Fin n) ℂ) *ᵥ ((g : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) =
      (g : Matrix (Fin n) (Fin n) ℂ) *ᵥ ((ρ w : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) := fun w x => by
    rw [mulVec_mulVec, mulVec_mulVec, hg w, ← Units.val_mul, ← Units.val_mul,
      mul_assoc (g * ρ w) g⁻¹ g, inv_mul_cancel, mul_one]
  refine ⟨hρ.1, fun V hV => ?_⟩
  let V' : Submodule ℂ (Fin n → ℂ) := V.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ))
  have hV' : ∀ w, V' ≤ V'.comap (Matrix.toLin' (ρ w : Matrix (Fin n) (Fin n) ℂ)) := by
    intro w x hx
    simp only [V', Submodule.mem_comap, Matrix.toLin'_apply] at hx ⊢
    rw [← hcomm]
    simpa [Matrix.toLin'_apply] using hV w hx
  have hmem : ∀ y, y ∈ V ↔ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ y ∈ V' := by
    intro y
    simp only [V', Submodule.mem_comap, Matrix.toLin'_apply, hgg]
  rcases hρ.2 V' hV' with h0 | h1
  · left
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [hmem, h0, Submodule.mem_bot] at hy
    rw [← hgg y, hy, mulVec_zero]
  · right
    rw [Submodule.eq_top_iff']
    intro y
    rw [hmem, h1]
    exact Submodule.mem_top

/-- The twist $w \mapsto \chi(w) \rho(w)$ of a representation $\rho$ by a character $\chi$. -/
noncomputable def twistRep {n : ℕ} (χ : W →* ℂˣ) (ρ : W →* GL (Fin n) ℂ) : W →* GL (Fin n) ℂ :=
  MonoidHom.toHomUnits
    { toFun := fun w => (χ w : ℂ) • (ρ w : Matrix (Fin n) (Fin n) ℂ)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, map_mul, Units.val_mul, Units.val_mul, smul_mul_smul_comm] }

/-- The matrix of the twist at $w$. -/
theorem coe_twistRep {n : ℕ} (χ : W →* ℂˣ) (ρ : W →* GL (Fin n) ℂ) (w : W) :
    ((twistRep χ ρ w : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (χ w : ℂ) • (ρ w : Matrix (Fin n) (Fin n) ℂ) := rfl

/-- The extension by zero of $\varphi \cdot \chi|_H$ is the extension by zero of $\varphi$ times $\chi$. -/
theorem extChar_mul_restrict (φ : H →* ℂˣ) (χ : W →* ℂˣ) (x : W) :
    extChar (φ * χ.comp H.subtype) x = extChar φ x * χ x := by
  by_cases hx : x ∈ H
  · rw [extChar_of_mem _ hx, extChar_of_mem _ hx]; simp
  · rw [extChar_of_not_mem _ hx, extChar_of_not_mem _ hx, zero_mul]

/-- The sign character of $W / H$: it is $1$ on $H$ and $-1$ outside $H$. -/
noncomputable def signChar (hH : H.index = 2) : W →* ℂˣ where
  toFun w := by classical exact if w ∈ H then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    classical
    simp only [Subgroup.mul_mem_iff_of_index_two hH]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]

section IndexTwo

variable (hH : H.index = 2) {s : W} (hs : s ∉ H)
include hH hs

/-- $\mathrm{Ind}_H^W \varphi \cong \mathrm{Ind}_H^W \varphi^s$. The matrix $\rho(s)$ is an isomorphism. -/
theorem repIso_ind_conjChar (φ : H →* ℂˣ) :
    RepIso (ind hH hs φ) (ind hH hs (conjChar hH s φ)) := by
  refine repIso_of_mul_eq (ind hH hs φ s) fun w => ?_
  have hss := s_mul_s_mem hH hs
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [ind_apply, extChar_conj hH hs]
  fin_cases i <;> fin_cases j <;>
    simp [extChar_s hs, extChar_one, ← mul_assoc]
  · rw [show s⁻¹ * w * s * s = s⁻¹ * w * (s * s) by group, extChar_mul_of_mem_right φ _ hss,
      mul_comm]
  · rw [mul_comm]
  · rw [show s⁻¹ * s⁻¹ * w * s * s = (s * s)⁻¹ * w * (s * s) by group,
      extChar_conj_of_mem φ hss]
  · rw [show w * s = s * s * (s⁻¹ * s⁻¹ * w * s) by group, extChar_mul_of_mem_left φ _ hss,
      mul_comm]

/-- $\mathrm{Ind}_H^W (\varphi \otimes \chi|_H) \cong (\mathrm{Ind}_H^W \varphi) \otimes \chi$ for a character $\chi$ of $W$. The isomorphism is the diagonal matrix with entries $1, \chi(s)$. -/
theorem repIso_ind_mul_restrict (φ : H →* ℂˣ) (χ : W →* ℂˣ) :
    RepIso (ind hH hs (φ * χ.comp H.subtype)) (twistRep χ (ind hH hs φ)) := by
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, (χ s : ℂ)]) (by simp)
  have hD : (D : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![1, (χ s : ℂ)] := rfl
  refine repIso_of_mul_eq D fun w => ?_
  rw [hD, coe_twistRep, coe_ind, coe_ind, Matrix.smul_mul]
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, indMatrix_apply, indMatrix_apply,
    extChar_mul_restrict, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [map_mul]
  all_goals first | ring1 | field_simp

/-- On $H$, the determinant of $\mathrm{Ind}_H^W \varphi$ is $\varphi \varphi^s$. -/
theorem det_ind_of_mem (φ : H →* ℂˣ) (h : H) :
    (ind hH hs φ h : GL (Fin 2) ℂ).det = φ h * conjChar hH s φ h := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ind_apply_of_mem hH hs, Matrix.det_diagonal,
    Fin.prod_univ_two]
  simp

/-- Outside $H$, the determinant of $\mathrm{Ind}_H^W \varphi$ is $-\varphi(s^{-1} w) \varphi(w s)$. -/
theorem det_ind_of_not_mem (φ : H →* ℂˣ) {w : W} (hw : w ∉ H) :
    (ind hH hs φ w : GL (Fin 2) ℂ).det =
      -(φ ⟨s⁻¹ * w, (s_inv_mul_mem_iff hH hs w).2 hw⟩ * φ ⟨w * s, (mul_s_mem_iff hH hs w).2 hw⟩) := by
  apply Units.ext
  have h1 : s⁻¹ * w * s ∉ H := by rwa [mul_s_mem_iff hH hs, s_inv_mul_mem_iff hH hs, not_not]
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [ind_apply, reps_zero, reps_one, inv_one, one_mul, mul_one,
    extChar_of_not_mem φ hw, extChar_of_not_mem φ h1,
    extChar_of_mem φ ((s_inv_mul_mem_iff hH hs w).2 hw), extChar_of_mem φ ((mul_s_mem_iff hH hs w).2 hw)]
  simp [mul_comm]

/-- The kernel of $\mathrm{Ind}_H^W \varphi$ contains the elements $h$ of $H$ with $\varphi(h) = \varphi(s^{-1} h s) = 1$. -/
theorem ind_eq_one (φ : H →* ℂˣ) (h : H) (h1 : φ h = 1) (h2 : conjChar hH s φ h = 1) :
    ind hH hs φ h = 1 := by
  apply Units.ext
  rw [ind_apply_of_mem hH hs, h1, h2]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- If $H$ is open in $W$ and $\varphi$ has open kernel, then $\mathrm{Ind}_H^W \varphi$ has open kernel: it is smooth. -/
theorem isOpen_ker_ind [TopologicalSpace W] [IsTopologicalGroup W] (hHo : IsOpen (H : Set W))
    (φ : H →* ℂˣ) (hφ : IsOpen (φ.ker : Set H)) :
    IsOpen ((ind hH hs φ).ker : Set W) := by
  set K : Subgroup W := φ.ker.map H.subtype
  have hK : IsOpen (K : Set W) := by
    have : (K : Set W) = Subtype.val '' (φ.ker : Set H) := by
      ext x; simp [K]
    rw [this]
    exact hHo.isOpenMap_subtype_val _ hφ
  set K' : Subgroup W := K.comap (MulAut.conj s⁻¹).toMonoidHom
  have hK' : IsOpen (K' : Set W) := by
    have hc : Continuous fun w : W => s⁻¹ * w * s⁻¹⁻¹ := by fun_prop
    exact hK.preimage hc
  refine Subgroup.isOpen_mono (H₁ := K ⊓ K') ?_ (hK.inter hK')
  rintro w ⟨hw1, hw2⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hw1
  obtain ⟨h', hh', hh'e⟩ := Subgroup.mem_map.1 (show s⁻¹ * h * s⁻¹⁻¹ ∈ K from hw2)
  refine ind_eq_one hH hs φ h hh ?_
  rw [conjChar_apply]
  have : (⟨s⁻¹ * h * s, conj_mem hH s h.2⟩ : H) = h' := Subtype.ext (by simpa using hh'e.symm)
  rw [this]
  exact hh'

/-- Frobenius reciprocity, the easy direction. Let $\rho$ be a $2$-dimensional representation of $W$ and let $v \ne 0$ be a vector on which $H$ acts by $\varphi$. If $\varphi^s \ne \varphi$, then $\rho \cong \mathrm{Ind}_H^W \varphi$. The isomorphism sends the basis $1, s$ to $v, \rho(s) v$. -/
theorem repIso_ind_of_eigenvector (ρ : W →* GL (Fin 2) ℂ) {φ : H →* ℂˣ}
    (hφ : conjChar hH s φ ≠ φ) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : ∀ h : H, (ρ h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (φ h : ℂ) • v) :
    RepIso (ind hH hs φ) ρ := by
  have hmul : ∀ x y : W, ∀ z : Fin 2 → ℂ, (ρ (x * y) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z =
      (ρ x : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((ρ y : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) := by
    intro x y z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  set u := (ρ s : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v with hu_def
  have key : ∀ x : W, (ρ x : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v =
      extChar φ x • v + extChar φ (s⁻¹ * x) • u := by
    intro x
    by_cases hx : x ∈ H
    · rw [extChar_of_not_mem φ (w := s⁻¹ * x) (by rw [s_inv_mul_mem_iff hH hs, not_not]; exact hx),
        extChar_of_mem φ hx, zero_smul, add_zero]
      exact heig ⟨x, hx⟩
    · have hx' : s⁻¹ * x ∈ H := (s_inv_mul_mem_iff hH hs x).2 hx
      rw [extChar_of_not_mem φ hx, zero_smul, zero_add, extChar_of_mem φ hx']
      conv_lhs => rw [show x = s * (s⁻¹ * x) by group]
      rw [hmul, heig ⟨_, hx'⟩, Matrix.mulVec_smul]
  have hu : u ≠ 0 := by
    intro h0
    apply hv
    have := hmul s⁻¹ s v
    rw [inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec, ← hu_def, h0,
      Matrix.mulVec_zero] at this
    exact this
  obtain ⟨h0, hh0⟩ := DFunLike.ne_iff.1 hφ
  set a : ℂ := (φ h0 : ℂ)
  set b : ℂ := (conjChar hH s φ h0 : ℂ)
  have hab : b - a ≠ 0 := sub_ne_zero.2 fun h => hh0 (Units.val_injective h)
  have hu_eig : (ρ h0 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u = b • u := by
    rw [hu_def, ← hmul, key, extChar_of_not_mem φ (w := (h0 : W) * s)
      (by rw [mul_s_mem_iff hH hs, not_not]; exact h0.2), zero_smul, zero_add,
      extChar_of_mem φ (w := s⁻¹ * ((h0 : W) * s)) (by simpa [mul_assoc] using conj_mem hH s h0.2)]
    simp only [b, conjChar_apply, u]
    congr 3
    simp [mul_assoc]
  set P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => ![v, u] j i
  have hP : ∀ y : Fin 2 → ℂ, P *ᵥ y = y 0 • v + y 1 • u := by
    intro y; ext i
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdet : P.det ≠ 0 := by
    intro h
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    rw [hP] at hy
    have h2 := congrArg ((ρ h0 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ·) hy
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, heig, hu_eig, Matrix.mulVec_zero] at h2
    change y 0 • a • v + y 1 • b • u = 0 at h2
    have h3 : (y 0 * (b - a)) • v = 0 := by
      linear_combination (norm := module) b • hy - h2
    have hy00 : y 0 = 0 := by
      rcases smul_eq_zero.1 h3 with h | h
      · exact (mul_eq_zero.1 h).resolve_right hab
      · exact absurd h hv
    rw [hy00, zero_smul, zero_add] at hy
    have hy1 : y 1 = 0 := (smul_eq_zero.1 hy).resolve_right hu
    exact hy0 (by ext i; fin_cases i <;> simp [hy00, hy1])
  refine repIso_of_mul_eq (Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet) fun w => ?_
  have hPv : (Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet : Matrix (Fin 2) (Fin 2) ℂ) = P := rfl
  rw [hPv, coe_ind]
  have k0 := key w
  have k1 := key (w * s)
  rw [hmul] at k1
  ext i j
  have e0 := congrFun k0 i
  have e1 := congrFun k1 i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at e0 e1
  fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, P, indMatrix_apply]
    linear_combination e0
  · simp [Matrix.mul_apply, Fin.sum_univ_two, P, indMatrix_apply]
    simp [u, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 ⊢
    rw [← mul_assoc s⁻¹ w s] at e1
    linear_combination e1

omit hH hs in
/-- A matrix annihilated by a squarefree polynomial gives a semisimple endomorphism. -/
theorem isSemisimple_toLin'_of_aeval {M : Matrix (Fin 2) (Fin 2) ℂ} {p : Polynomial ℂ}
    (hp : Squarefree p) (h : Polynomial.aeval M p = 0) :
    Module.End.IsSemisimple (Matrix.toLin' M) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp ?_
  have := Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin 2)).toAlgHom M p
  rw [h, map_zero] at this
  exact this

/-- Each matrix $\mathrm{Ind}_H^W \varphi(w)$ is semisimple. -/
theorem isSemisimple_ind (φ : H →* ℂˣ) (w : W) :
    Module.End.IsSemisimple
      (Matrix.toLin' ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  open Polynomial in
  by_cases hw : w ∈ H
  · have hM := ind_apply_of_mem hH hs φ ⟨w, hw⟩
    simp only at hM
    rw [hM]
    set a : ℂ := (φ ⟨w, hw⟩ : ℂ)
    set b : ℂ := (conjChar hH s φ ⟨w, hw⟩ : ℂ)
    by_cases hab : a = b
    · refine isSemisimple_toLin'_of_aeval (p := X - C a) (separable_X_sub_C).squarefree ?_
      rw [← hab]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]
    · refine isSemisimple_toLin'_of_aeval (p := (X - C a) * (X - C b))
        ((separable_X_sub_C.mul separable_X_sub_C
          (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit)).squarefree) ?_
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.algebraMap_eq_diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  · have hww : w * w ∈ H := by rw [Subgroup.mul_mem_iff_of_index_two hH]
    have hc : extChar φ (w * w) ≠ 0 := by rw [extChar_of_mem φ hww]; exact Units.ne_zero _
    set c := extChar φ (w * w)
    have hsq : ((ind hH hs φ w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 =
        Matrix.scalar (Fin 2) c := by
      have hws : w⁻¹ * s ∈ H := by rw [Subgroup.mul_mem_iff_of_index_two hH, H.inv_mem_iff]; tauto
      have hconj : extChar φ (s⁻¹ * (w * w) * s) = c := by
        rw [show s⁻¹ * (w * w) * s = (w⁻¹ * s)⁻¹ * (w * w) * (w⁻¹ * s) by group,
          extChar_conj_of_mem φ hws]
      have hconj' : (conjChar hH s φ ⟨w * w, hww⟩ : ℂ) = c := by
        rw [conjChar_apply, ← extChar_of_mem φ (conj_mem hH s hww)]
        exact hconj
      have hφ' : (φ ⟨w * w, hww⟩ : ℂ) = c := (extChar_of_mem φ hww).symm
      have := ind_apply_of_mem hH hs φ ⟨w * w, hww⟩
      simp only at this
      rw [sq, ← Units.val_mul, ← map_mul, this]
      rw [hconj', hφ']
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    refine isSemisimple_toLin'_of_aeval (p := X ^ 2 - C c)
      (separable_X_pow_sub_C c (by norm_num) hc).squarefree ?_
    simp [hsq, Matrix.algebraMap_eq_diagonal]

omit hH hs in
/-- The coset of $x$ is the trivial coset if and only if $x \in H$. -/
theorem mk_eq_one_iff (x : W) : (x : W ⧸ H) = ((1 : W) : W ⧸ H) ↔ x ∈ H := by
  rw [QuotientGroup.eq, mul_one, H.inv_mem_iff]

/-- For $x \notin H$, the coset of $x$ is the coset of $s$. -/
theorem mk_eq_s_of_not_mem {x : W} (hx : x ∉ H) : (x : W ⧸ H) = (s : W ⧸ H) := by
  rw [QuotientGroup.eq, Subgroup.mul_mem_iff_of_index_two hH, H.inv_mem_iff]; tauto

/-- Each coset of $H$ is the coset of $1$ or the coset of $s$. -/
theorem quotient_eq_one_or_eq_s (q : W ⧸ H) : q = ((1 : W) : W ⧸ H) ∨ q = (s : W ⧸ H) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    by_cases hx : x ∈ H
    · exact Or.inl ((mk_eq_one_iff (H := H) x).2 hx)
    · exact Or.inr (mk_eq_s_of_not_mem hH hs hx)

open Subgroup in
/-- The determinant of $\mathrm{Ind}_H^W \varphi$ is the sign character of $W / H$ times the transfer $W \to H^{ab} \to \mathbb{C}^\times$ of $\varphi$. The proof computes the transfer with the transversal $\{1, s\}$. -/
theorem det_ind_eq_signChar_mul_transfer [H.FiniteIndex] (φ : H →* ℂˣ) (w : W) :
    (ind hH hs φ w : GL (Fin 2) ℂ).det = signChar hH w * φ.transfer w := by
  classical
  let f : W ⧸ H → W := fun q => if q = ((1 : W) : W ⧸ H) then 1 else s
  have hs1 : (s : W ⧸ H) ≠ ((1 : W) : W ⧸ H) := fun h => hs ((mk_eq_one_iff s).1 h)
  have hf : ∀ q, (f q : W ⧸ H) = q := by
    intro q
    rcases quotient_eq_one_or_eq_s hH hs q with rfl | rfl
    · simp [f]
    · simp [f, hs1]
  have hfmk : ∀ x : W, f x = if x ∈ H then 1 else s := by
    intro x
    simp only [f, mk_eq_one_iff]
  let T : H.LeftTransversal := ⟨_, isComplement_range_left hf⟩
  have hα : ∀ q, (T.2.leftQuotientEquiv q : W) = f q := fun q => IsComplement.leftQuotientEquiv_apply hf q
  have hβ : ∀ q, ((w • T).2.leftQuotientEquiv q : W) = w * f (w⁻¹ • q) := by
    intro q
    rw [smul_apply_eq_smul_apply_inv_smul, hα, smul_eq_mul]
  rw [MonoidHom.transfer_def φ T w, Subgroup.leftTransversals.diff]
  let := H.fintypeQuotientOfFiniteIndex
  rw [Fintype.prod_eq_mul ((1 : W) : W ⧸ H) (s : W ⧸ H) hs1.symm (fun q hq =>
    absurd (quotient_eq_one_or_eq_s hH hs q) (by tauto))]
  apply Units.ext
  simp only [Units.val_mul]
  rw [← extChar_of_mem φ, ← extChar_of_mem φ]
  simp only [hα, hβ, MulAction.Quotient.smul_mk, smul_eq_mul, hfmk]
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [ind_apply, reps_zero, reps_one, inv_one, one_mul, mul_one]
  by_cases hw : w ∈ H
  · have h1 : w⁻¹ ∈ H := H.inv_mem hw
    have h2 : w⁻¹ * s ∉ H := by rw [mul_s_mem_iff hH hs, not_not]; exact h1
    have h3 : w * s ∉ H := by rw [mul_s_mem_iff hH hs, not_not]; exact hw
    have h4 : s⁻¹ * w ∉ H := by rw [s_inv_mul_mem_iff hH hs, not_not]; exact hw
    simp [h1, h2, hs, signChar, hw, extChar_of_not_mem φ h3, extChar_of_not_mem φ h4, mul_assoc]
  · have h1 : w⁻¹ ∉ H := by rwa [H.inv_mem_iff]
    have h2 : w⁻¹ * s ∈ H := by rw [mul_s_mem_iff hH hs]; exact h1
    have h3 : s⁻¹ * w * s ∉ H := by rwa [mul_s_mem_iff hH hs, s_inv_mul_mem_iff hH hs, not_not]
    simp [h1, h2, hs, signChar, hw, extChar_of_not_mem φ hw, extChar_of_not_mem φ h3]

end IndexTwo

end Abstract

section WeilIndex

open Langlands.WeilGroup
open scoped Pointwise

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : IntermediateField K (AlgebraicClosure K))

/-- An element of the absolute Galois group, seen as an automorphism of the algebraic closure. -/
def galEquiv (g : Field.absoluteGaloisGroup K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g

/-- The Weil group $W_K$ acts on the $K$-embeddings $L \to \bar K$ through the Galois group. -/
noncomputable instance embAction : MulAction (WeilGroup K) (L →ₐ[K] AlgebraicClosure K) where
  smul w τ := (galEquiv K (toGalois K w)).toAlgHom.comp τ
  one_smul τ := by ext; rfl
  mul_smul v w τ := by ext; rfl

/-- The action of $w$ on an embedding $\tau$ is $x \mapsto w(\tau(x))$. -/
theorem smul_emb_apply (w : WeilGroup K) (τ : L →ₐ[K] AlgebraicClosure K) (x : L) :
    (w • τ) x = toGalois K w • τ x := rfl

/-- The stabilizer of the inclusion $L \to \bar K$ is $W_L$. -/
theorem stabilizer_val :
    MulAction.stabilizer (WeilGroup K) (L.val) = restrictSubgroup K L := by
  ext w
  rw [MulAction.mem_stabilizer_iff, mem_restrictSubgroup]
  constructor
  · intro h x hx
    exact congrArg (fun τ : L →ₐ[K] AlgebraicClosure K => τ ⟨x, hx⟩) h
  · intro h
    ext x
    exact h x x.2

/-- Each $K$-embedding $L \to \bar K$ is the image of the inclusion under an element of $W_K$. An embedding extends to an element of $\mathrm{Gal}(\bar K / K)$, and the image of $W_K$ is dense, so it meets the open coset of the elements that agree with this element on $L$. -/
theorem exists_smul_val_eq [FiniteDimensional K L] (τ : L →ₐ[K] AlgebraicClosure K) :
    ∃ w : WeilGroup K, w • L.val = τ := by
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofBijective (τ.liftNormal (AlgebraicClosure K))
      (AlgHom.normal_bijective K _ _ _)
  have hσ : ∀ x : L, σ x = τ x := fun x => τ.liftNormal_commutes (AlgebraicClosure K) x
  have ho : IsOpen (σ • (L.fixingSubgroup : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))) :=
    L.fixingSubgroup_isOpen.leftCoset σ
  obtain ⟨w, hw⟩ := (denseRange_toGalois K).exists_mem_open ho
    ⟨σ, ⟨1, L.fixingSubgroup.one_mem, mul_one σ⟩⟩
  refine ⟨w, ?_⟩
  obtain ⟨g, hg, hgw⟩ := hw
  ext x
  rw [smul_emb_apply, ← hgw, ← hσ]
  change σ (g x) = σ x
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x x.2

/-- For a finite separable extension $L / K$, the index of $W_L$ in $W_K$ is $[L : K]$. -/
theorem index_restrictSubgroup [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (restrictSubgroup K L).index = Module.finrank K L := by
  have : MulAction.IsPretransitive (WeilGroup K) (L →ₐ[K] AlgebraicClosure K) := by
    refine ⟨fun τ τ' => ?_⟩
    obtain ⟨u, hu⟩ := exists_smul_val_eq K L τ
    obtain ⟨v, hv⟩ := exists_smul_val_eq K L τ'
    exact ⟨v * u⁻¹, by rw [mul_smul, ← hu, inv_smul_smul, hv]⟩
  rw [← stabilizer_val, MulAction.index_stabilizer_of_transitive,
    ← Field.finSepDegree_eq_of_isAlgClosed, Field.finSepDegree_eq_finrank_of_isSeparable]


/-- If the representation part of a Weil-Deligne representation is irreducible, then its monodromy operator is zero. -/
theorem WeilDeligneRep.N_eq_zero_of_isIrreducibleRep {m : ℕ} (ρ : WeilDeligneRep K m)
    (hρ : IsIrreducibleRep ρ.r) : ρ.N = 0 := by
  set V : Submodule ℂ (Fin m → ℂ) := LinearMap.ker (Matrix.toLin' ρ.N) with hVdef
  have hst : ∀ w, V ≤ V.comap (Matrix.toLin' (ρ.r w : Matrix (Fin m) (Fin m) ℂ)) := by
    intro w v hv
    simp only [V, Submodule.mem_comap, LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    have h := ρ.conj w⁻¹
    have hinv : (((ρ.r w⁻¹)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = ρ.r w := by
      rw [← map_inv, inv_inv]
    rw [hinv] at h
    have h2 : ρ.N * (ρ.r w : Matrix (Fin m) (Fin m) ℂ) =
        (ρ.r w : Matrix (Fin m) (Fin m) ℂ) * (weilNorm K w⁻¹ • ρ.N) := by
      rw [← h, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
        Units.val_one, one_mul]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hv, smul_zero,
      Matrix.mulVec_zero]
  rcases hρ.2 V hst with hV | hV
  · exfalso
    have : NeZero m := ⟨hρ.1.ne'⟩
    have hnil : IsNilpotent (Matrix.toLinAlgEquiv' ρ.N) := ρ.isNilpotent.map _
    exact hnil.not_isUnit ((LinearMap.isUnit_iff_ker_eq_bot _).2 hV)
  · exact Matrix.toLin'.injective ((LinearMap.ker_eq_top.1 hV).trans (map_zero _).symm)

section WeilDeligne

variable {K} {L}
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- If $[L : K] = 2$, then $W_L$ has index 2 in $W_K$. -/
theorem index_restrictSubgroup_eq_two (hL : Module.finrank K L = 2) :
    (restrictSubgroup K L).index = 2 :=
  (index_restrictSubgroup K L).trans hL

/-- The induced Weil-Deligne representation $(\mathrm{Ind}_{W_L}^{W_K} \varphi, 0)$ for a quadratic separable extension $L / K$ and a smooth character $\varphi$ of $W_L$. -/
noncomputable def indWD (hL : Module.finrank K L = 2) {s : WeilGroup K}
    (hs : s ∉ restrictSubgroup K L) (φ : restrictSubgroup K L →* ℂˣ)
    (hφ : IsOpen (φ.ker : Set (restrictSubgroup K L))) : WeilDeligneRep K 2 where
  r := ind (index_restrictSubgroup_eq_two hL) hs φ
  isOpen_ker := isOpen_ker_ind _ hs (isOpen_restrictSubgroup K L) φ hφ
  N := 0
  isNilpotent := IsNilpotent.zero
  conj w := by simp
  semisimple := isSemisimple_ind _ hs φ

/-- The monodromy operator of `indWD` is zero. -/
@[simp]
theorem indWD_N (hL : Module.finrank K L = 2) {s : WeilGroup K}
    (hs : s ∉ restrictSubgroup K L) (φ : restrictSubgroup K L →* ℂˣ)
    (hφ : IsOpen (φ.ker : Set (restrictSubgroup K L))) : (indWD hL hs φ hφ).N = 0 := rfl

/-- If $\varphi^s \ne \varphi$, then `indWD` is irreducible. -/
theorem isIrreducible_indWD (hL : Module.finrank K L = 2) {s : WeilGroup K}
    (hs : s ∉ restrictSubgroup K L) {φ : restrictSubgroup K L →* ℂˣ}
    (hφ : IsOpen (φ.ker : Set (restrictSubgroup K L)))
    (hne : conjChar (index_restrictSubgroup_eq_two hL) s φ ≠ φ) :
    (indWD hL hs φ hφ).IsIrreducible :=
  ⟨two_pos, fun V hV _ => (isIrreducibleRep_ind _ hs hne).2 V hV⟩

/-- Frobenius reciprocity for `indWD`. Let $\rho$ be a Weil-Deligne representation of dimension 2. Suppose that some nonzero vector $v$ satisfies $\rho(h) v = \varphi(h) v$ for all $h \in W_L$, and that $\varphi^s \ne \varphi$. Then $\rho$ is isomorphic to `indWD`. -/
theorem iso_indWD_of_eigenvector (hL : Module.finrank K L = 2) {s : WeilGroup K}
    (hs : s ∉ restrictSubgroup K L) {φ : restrictSubgroup K L →* ℂˣ}
    (hφ : IsOpen (φ.ker : Set (restrictSubgroup K L)))
    (hne : conjChar (index_restrictSubgroup_eq_two hL) s φ ≠ φ) (ρ : WeilDeligneRep K 2)
    {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : ∀ h : restrictSubgroup K L, (ρ.r h : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = (φ h : ℂ) • v) :
    (indWD hL hs φ hφ).Iso ρ := by
  have hiso := repIso_ind_of_eigenvector _ hs ρ.r hne hv heig
  have hirr := isIrreducibleRep_of_repIso hiso (isIrreducibleRep_ind _ hs hne)
  obtain ⟨g, hg⟩ := hiso
  refine ⟨g, hg, ?_⟩
  rw [WeilDeligneRep.N_eq_zero_of_isIrreducibleRep _ ρ hirr]
  simp

end WeilDeligne


end WeilIndex

end Langlands.LocalGL2
