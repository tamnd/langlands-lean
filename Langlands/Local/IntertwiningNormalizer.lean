/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.StrataIntertwining

/-!
# The intertwining of a simple stratum outside the normalizer

Let $F$ be a nonarchimedean local field, $\mathfrak{A}$ the maximal or the Iwahori chain order of $M_2(F)$, and $E/F$ a quadratic extension embedded in $M_2(F)$ by a basis adapted to $\mathfrak{A}$. This file proves the part of BH §15.1 outside the normalizer $\mathfrak{K}_{\mathfrak{A}}$: for $\alpha \in E$ minimal of level $n \ge 1$, each $g \in GL_2(F)$ that intertwines the character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ lies in $\mathfrak{K}_{\mathfrak{A}}$. This is the hypothesis `hK` of `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType`. Thus the intertwining of $\psi_\alpha$ and the intertwining of each cuspidal type $\Lambda$ of $J_\alpha$ are exactly $J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$.

The first step is a decomposition $GL_2(F) = \mathfrak{K}_{\mathfrak{A}} \, \{\mathrm{diag}(1, d)\} \, \mathfrak{K}_{\mathfrak{A}}$ with $d \in \mathcal{O}_F \setminus \{0\}$, for both chain orders. This is a weak form of the Cartan decomposition and of the Iwahori decomposition (BH §12), and it is sufficient for the proof.

## Main definitions

* `Langlands.LocalGL2.lowerGL`, `Langlands.LocalGL2.upperGL`: the unipotent elements $\begin{pmatrix} 1 & 0 \\ l & 1 \end{pmatrix}$ and $\begin{pmatrix} 1 & u \\ 0 & 1 \end{pmatrix}$ of $GL_2(F)$.
* `Langlands.LocalGL2.diagGL`: the diagonal element $\mathrm{diag}(a, b)$ of $GL_2(F)$.
* `Langlands.LocalGL2.swapGL`: the permutation element $w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ of $GL_2(F)$.

## Main results

* `Langlands.LocalGL2.exists_normalizer_mul_diag_mul`: each $g \in GL_2(F)$ has the form $g = a \, \mathrm{diag}(1, d) \, b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}}$ and $\mathrm{ord}(d) \ge 0$.
* `Langlands.LocalGL2.mem_normalizer_of_intertwines_psiAlpha`: if $\alpha$ is minimal of level $n \ge 1$, each $g$ that intertwines $\psi_\alpha$ lies in $\mathfrak{K}_{\mathfrak{A}}$ (BH §15.1 outside $\mathfrak{K}_{\mathfrak{A}}$).
* `Langlands.LocalGL2.intertwines_psiAlpha_iff_mem_jGroup`: $g$ intertwines $\psi_\alpha$ exactly when $g \in J_\alpha$.
* `Langlands.LocalGL2.intertwines_cuspType_iff_mem_jGroup`: $g$ intertwines a cuspidal type $\Lambda$ of $J_\alpha$ exactly when $g \in J_\alpha$.
* `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType_of_isMinimalElt`: the intertwining of a cuspidal type is $J_\alpha$, without the hypothesis `hK`, in the form of the hypothesis of `Langlands.eq_smul_cIndBasic_of_isotypic`.
* `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType_ramBasis`: the same statement with no minimality hypothesis, for ramified $E/F$, odd $n$, $\mathrm{ord}_E(\alpha) = -n$, the Iwahori order and the basis $(\varpi_E, 1)$.

## Implementation notes

The proof does not use the duality $(L \cap L')^\perp = L^\perp + L'^\perp$ of two lattices, and it does not use the uniqueness of the chain order of a simple stratum. It uses the decomposition and a direct computation. For the decomposition, take the largest $k$ with $g \in \mathfrak{P}^k_{\mathfrak{A}}$. Then $h = \Pi^{-k} g \in \mathfrak{A} \setminus \mathfrak{P}_{\mathfrak{A}}$, so some entry of $h$ is a unit at its position. Multiplication by $w$ (maximal order) or conjugation by $\Pi$ (Iwahori order) moves this entry to the position $(0, 0)$, and the $LDU$ factorization finishes the decomposition.

Let $g = a D b$ with $D = \mathrm{diag}(1, d)$. If $\mathrm{ord}(d) = 0$, then $D \in U^0_{\mathfrak{A}}$ and $g \in \mathfrak{K}_{\mathfrak{A}}$. If $\mathrm{ord}(d) \ge 1$, put $\gamma = a^{-1} \alpha a$, $\beta = b \alpha b^{-1}$ and $m = [n/2] + 1$. The intertwining gives $\psi(\mathrm{tr}((D^{-1} \gamma D - \beta) X)) = 1$ for each $X \in \mathfrak{P}^m_{\mathfrak{A}}$ with $D X D^{-1} \in \mathfrak{P}^m_{\mathfrak{A}}$. The test matrices $X = c E_{01}$ give $\gamma_{10} \in \mathfrak{p}^{b(1-n, 1, 0)}_F$, where $b(n, i, j)$ is the exponent of the entry $(i, j)$ of $\mathfrak{P}^n_{\mathfrak{A}}$. The minimality of $\alpha$ gives $\mathrm{ord}_E(\alpha - \gamma_{00}) = -n$, so $\delta = \gamma - \gamma_{00}$ is a conjugate of an element whose inverse lies in $\mathfrak{p}^n_E$. Then $1 = (\delta^{-1} \delta)_{00} = \delta^{-1}_{01} \gamma_{10} \in \mathfrak{p}_F$, which is a contradiction.

## Still open

* For unramified $E/F$, the minimality $\alpha \notin F + \mathfrak{p}^{1-n}_E$ of the element of a minimal pair, and its link to the adapted basis of `Langlands/Local/AdaptedUnramified.lean`. This file does not import that module. Thus the unconditional corollary for the maximal order has the hypothesis `IsMinimalElt F n α`. For the Iwahori order and ramified $E/F$ the corollary `mem_jGroup_of_intertwines_cuspType_ramBasis` has no such hypothesis.
* The case of even $n$ of the cuspidal types, where $J_\alpha$ is larger than the group of `typeChar` (see `Langlands/Local/CuspidalTypes.lean`). The results on $\psi_\alpha$ here hold for each $n \ge 1$.
* The general statement that a simple stratum determines its chain order up to conjugacy, and the duality of an intersection of two lattices. The proof here does not need them, but they are not proved.

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, Chapter 3 and 4, §§12 to 15.
-/

namespace Langlands.LocalGL2

universe u v

open LocalGL1 ValuativeRel Matrix

section Decomposition

variable {F : Type u} [Field F]

variable (F) in
/-- The lower unipotent element $\begin{pmatrix} 1 & 0 \\ l & 1 \end{pmatrix}$ of $GL_2(F)$. -/
def lowerGL (l : F) : GL (Fin 2) F where
  val := !![1, 0; l, 1]
  inv := !![1, 0; -l, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

variable (F) in
/-- The upper unipotent element $\begin{pmatrix} 1 & u \\ 0 & 1 \end{pmatrix}$ of $GL_2(F)$. -/
def upperGL (u : F) : GL (Fin 2) F where
  val := !![1, u; 0, 1]
  inv := !![1, -u; 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

variable (F) in
/-- The diagonal element $\mathrm{diag}(a, b)$ of $GL_2(F)$ for $a, b \in F^\times$. -/
def diagGL (a b : Fˣ) : GL (Fin 2) F where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

variable (F) in
/-- The permutation element $w = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ of $GL_2(F)$. -/
def swapGL : GL (Fin 2) F where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

/-- The matrix of the lower unipotent element. -/
theorem val_lowerGL (l : F) : ((lowerGL F l : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; l, 1] :=
  rfl

/-- The matrix of the inverse of the lower unipotent element. -/
theorem val_lowerGL_inv (l : F) :
    (((lowerGL F l)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -l, 1] :=
  rfl

/-- The matrix of the upper unipotent element. -/
theorem val_upperGL (u : F) : ((upperGL F u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, u; 0, 1] :=
  rfl

/-- The matrix of the inverse of the upper unipotent element. -/
theorem val_upperGL_inv (u : F) :
    (((upperGL F u)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -u; 0, 1] :=
  rfl

/-- The matrix of the diagonal element. -/
theorem val_diagGL (a b : Fˣ) :
    ((diagGL F a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, (b : F)] :=
  rfl

/-- The matrix of the inverse of the diagonal element. -/
theorem val_diagGL_inv (a b : Fˣ) :
    (((diagGL F a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] :=
  rfl

/-- The matrix of the permutation element. -/
theorem val_swapGL : ((swapGL F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] :=
  rfl

/-- The matrix of the inverse of the permutation element. -/
theorem val_swapGL_inv : (((swapGL F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] :=
  rfl

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The matrix of the inverse of $\Pi_{\mathfrak{A}}$. -/
theorem val_piGL_inv (A : ChainOrder) :
    (((piGL F A)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = piInvMat F A :=
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The element $w$ is its own inverse. -/
theorem swapGL_mul_self : swapGL F * swapGL F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The element $w$ cancels itself on the left. -/
theorem swapGL_mul_swapGL_mul (x : GL (Fin 2) F) : swapGL F * (swapGL F * x) = x := by
  rw [← mul_assoc, swapGL_mul_self, one_mul]

/-- The unit $1$ lies in the diagonal ball of level $0$. -/
theorem one_mem_ordBall_bd_zero (A : ChainOrder) (i : Fin 2) : (1 : F) ∈ ordBall F (A.bd 0 i i) := by
  rw [A.bd_zero_self]
  exact one_mem_ordBall le_rfl

/-- A unit of $\mathcal{O}_F$ lies in the diagonal ball of level $0$. -/
theorem mem_ordBall_bd_zero_of_ord {A : ChainOrder} (i : Fin 2) {x : F} (hx : x ≠ 0)
    (h : 0 ≤ ord F x) : x ∈ ordBall F (A.bd 0 i i) := by
  rw [A.bd_zero_self]
  exact mem_ordBall_of_le hx h

/-- For $l \in \mathfrak{p}^{b(0, 1, 0)}_F$ the lower unipotent element lies in $U^0_{\mathfrak{A}}$. -/
theorem lowerGL_mem_unitsFilt {A : ChainOrder} {l : F} (hl : l ∈ ordBall F (A.bd 0 1 0)) :
    lowerGL F l ∈ unitsFilt F A 0 := by
  rw [mem_unitsFilt_zero, val_lowerGL, val_lowerGL_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [one_mem_ordBall_bd_zero, zero_mem_ordBall, hl, neg_mem_ordBall hl]

/-- For $u \in \mathfrak{p}^{b(0, 0, 1)}_F$ the upper unipotent element lies in $U^0_{\mathfrak{A}}$. -/
theorem upperGL_mem_unitsFilt {A : ChainOrder} {u : F} (hu : u ∈ ordBall F (A.bd 0 0 1)) :
    upperGL F u ∈ unitsFilt F A 0 := by
  rw [mem_unitsFilt_zero, val_upperGL, val_upperGL_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [one_mem_ordBall_bd_zero, zero_mem_ordBall, hu, neg_mem_ordBall hu]

/-- For units $a, b$ of $\mathcal{O}_F$ the element $\mathrm{diag}(a, b)$ lies in $U^0_{\mathfrak{A}}$. -/
theorem diagGL_mem_unitsFilt {A : ChainOrder} {a b : Fˣ} (ha : ord F (a : F) = 0)
    (hb : ord F (b : F) = 0) : diagGL F a b ∈ unitsFilt F A 0 := by
  have ha' : ord F ((a : F)⁻¹) = 0 := by
    rw [ord_inv a.ne_zero, ha, neg_zero]
  have hb' : ord F ((b : F)⁻¹) = 0 := by
    rw [ord_inv b.ne_zero, hb, neg_zero]
  rw [mem_unitsFilt_zero, val_diagGL, val_diagGL_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [zero_mem_ordBall, mem_ordBall_bd_zero_of_ord, ha, hb, ha', hb']

/-- The element $w$ lies in $U^0_{\mathfrak{M}} = GL_2(\mathcal{O}_F)$. -/
theorem swapGL_mem_unitsFilt : swapGL F ∈ unitsFilt F ChainOrder.maximal 0 := by
  rw [mem_unitsFilt_zero, val_swapGL, val_swapGL_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e, zero_mem_ordBall, one_mem_ordBall]

/-- A pivot form: if $h \in \mathfrak{A}$, $g = a h b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}}$ and $h_{00}$ is a unit, then the pivot data exists for $g$. -/
theorem exists_pivot_of_eq {A : ChainOrder} {g a b h : GL (Fin 2) F} (ha : a ∈ normalizer F A)
    (hb : b ∈ normalizer F A) (hH : (h : Matrix (Fin 2) (Fin 2) F) ∈ order F A)
    (h0 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0) (hord : ord F ((h : Matrix (Fin 2) (Fin 2) F) 0 0) = 0)
    (hg : g = a * h * b) :
    ∃ a ∈ normalizer F A, ∃ b ∈ normalizer F A, ∃ h : GL (Fin 2) F,
      (h : Matrix (Fin 2) (Fin 2) F) ∈ order F A ∧ (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧
        ord F ((h : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 ∧ g = a * h * b :=
  ⟨a, ha, b, hb, h, hH, h0, hord, hg⟩

/-- Each $g \in GL_2(F)$ has the form $g = a h b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}}$, $h \in \mathfrak{A}$ and $h_{00} \in \mathcal{O}_F^\times$. -/
theorem exists_pivot (A : ChainOrder) (g : GL (Fin 2) F) :
    ∃ a ∈ normalizer F A, ∃ b ∈ normalizer F A, ∃ h : GL (Fin 2) F,
      (h : Matrix (Fin 2) (Fin 2) F) ∈ order F A ∧ (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧
        ord F ((h : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 ∧ g = a * h * b := by
  obtain ⟨k, hk, hkmax⟩ := exists_greatest_radPow A (g : Matrix (Fin 2) (Fin 2) F) g.ne_zero
  set h := piGL F A ^ (-k) * g with hh
  have hH : (h : Matrix (Fin 2) (Fin 2) F) ∈ order F A := by
    have := (zpow_mul_mem_iff A (-k) k _).1 hk
    rw [add_neg_cancel] at this
    rw [hh, Units.val_mul]
    exact this
  have hH1 : (h : Matrix (Fin 2) (Fin 2) F) ∉ radPow F A 1 := by
    intro h1
    have := (zpow_mul_mem_iff A k 1 _).1 h1
    rw [hh, Units.val_mul, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_mul] at this
    have := hkmax _ this
    omega
  have hg : g = piGL F A ^ k * h * 1 := by
    rw [mul_one, hh, ← mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hPk : piGL F A ^ k ∈ normalizer F A := (normalizer F A).zpow_mem (piGL_mem_normalizer A) k
  obtain ⟨i, j, hij⟩ : ∃ i j, (h : Matrix (Fin 2) (Fin 2) F) i j ∉ ordBall F (A.bd 1 i j) := by
    by_contra hc
    exact hH1 fun i j => by_contra fun h' => hc ⟨i, j, h'⟩
  have h0 : (h : Matrix (Fin 2) (Fin 2) F) i j ≠ 0 := fun h0 => hij (h0 ▸ zero_mem_ordBall _)
  have hle := (mem_ordBall_bd_iff h0).1 (hH i j)
  have hlt : ¬ (1 ≤ A.e * ord F ((h : Matrix (Fin 2) (Fin 2) F) i j) + A.wt j - A.wt i) :=
    fun h' => hij ((mem_ordBall_bd_iff h0).2 h')
  have hN1 := (normalizer F A).one_mem
  cases A <;> fin_cases i <;> fin_cases j <;>
    simp [ChainOrder.e, ChainOrder.wt] at hle hlt h0
  · exact exists_pivot_of_eq hPk hN1 hH h0 (by omega) hg
  · have hw := unitsFilt_le_normalizer _ (swapGL_mem_unitsFilt (F := F))
    refine exists_pivot_of_eq hPk hw ((order F _).mul_mem hH (swapGL_mem_unitsFilt (F := F)).1)
      (h := h * swapGL F) ?_ ?_ ?_
    · simpa [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two] using h0
    · simp [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two]
      omega
    · rw [hg]
      simp only [mul_assoc, swapGL_mul_self, mul_one]
  · have hw := unitsFilt_le_normalizer _ (swapGL_mem_unitsFilt (F := F))
    refine exists_pivot_of_eq ((normalizer F _).mul_mem hPk hw) hN1
      ((order F _).mul_mem (swapGL_mem_unitsFilt (F := F)).1 hH) (h := swapGL F * h) ?_ ?_ ?_
    · simpa [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two] using h0
    · simp [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two]
      omega
    · rw [hg]
      simp only [mul_assoc, swapGL_mul_swapGL_mul, mul_one]
  · have hw := unitsFilt_le_normalizer _ (swapGL_mem_unitsFilt (F := F))
    refine exists_pivot_of_eq ((normalizer F _).mul_mem hPk hw) hw
      ((order F _).mul_mem ((order F _).mul_mem (swapGL_mem_unitsFilt (F := F)).1 hH)
        (swapGL_mem_unitsFilt (F := F)).1) (h := swapGL F * h * swapGL F) ?_ ?_ ?_
    · simpa [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using h0
    · simp [val_swapGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      omega
    · rw [hg]
      simp only [mul_assoc, swapGL_mul_swapGL_mul, swapGL_mul_self, mul_one]
  · exact exists_pivot_of_eq hPk hN1 hH h0 (by omega) hg
  · omega
  · omega
  · have hP := piGL_mem_normalizer (F := F) ChainOrder.iwahori
    refine exists_pivot_of_eq ((normalizer F _).mul_mem hPk ((normalizer F _).inv_mem hP)) hP
      (hP _ hH).1 (h := piGL F _ * h * (piGL F _)⁻¹) ?_ ?_ ?_
    · rw [Units.val_mul, Units.val_mul, val_piGL, val_piGL_inv]
      simpa [piMat, piInvMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using h0
    · rw [Units.val_mul, Units.val_mul, val_piGL, val_piGL_inv]
      simp [piMat, piInvMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      omega
    · rw [hg]
      group

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The $LDU$ identity $\begin{pmatrix} 1 & 0 \\ z/x & 1 \end{pmatrix} \mathrm{diag}(x, 1) \, \mathrm{diag}(1, (xw - yz)/x) \begin{pmatrix} 1 & y/x \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} x & y \\ z & w \end{pmatrix}$ for $x \ne 0$. -/
theorem ldu_fin_two {x y z w : F} (hx : x ≠ 0) :
    !![1, 0; z / x, 1] * !![x, 0; 0, 1] * !![1, 0; 0, (x * w - y * z) * x⁻¹] * !![1, y / x; 0, 1] =
      !![x, y; z, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  ring

/-- The decomposition $GL_2(F) = \mathfrak{K}_{\mathfrak{A}} \, \{\mathrm{diag}(1, d)\} \, \mathfrak{K}_{\mathfrak{A}}$ (a form of the Cartan and Iwahori decompositions, BH §12): each $g \in GL_2(F)$ has the form $g = a \, \mathrm{diag}(1, d) \, b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}}$ and $d \in \mathcal{O}_F \setminus \{0\}$. -/
theorem exists_normalizer_mul_diag_mul (A : ChainOrder) (g : GL (Fin 2) F) :
    ∃ a ∈ normalizer F A, ∃ b ∈ normalizer F A, ∃ d : Fˣ,
      0 ≤ ord F (d : F) ∧ g = a * diagGL F 1 d * b := by
  obtain ⟨a, ha, b, hb, h, hH, h0, hord, rfl⟩ := exists_pivot A g
  set H : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F) with hHdef
  have hdet : H.det ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
  have hδ : H.det * (H 0 0)⁻¹ ≠ 0 := mul_ne_zero hdet (inv_ne_zero h0)
  have hinv : (H 0 0)⁻¹ ∈ ordBall F 0 :=
    mem_ordBall_of_le (inv_ne_zero h0) (by rw [ord_inv h0, hord, neg_zero])
  have hl : H 1 0 / H 0 0 ∈ ordBall F (A.bd 0 1 0) := by
    rw [div_eq_mul_inv]
    exact mem_ordBall_congr (add_zero _) (mul_mem_ordBall_add (hH 1 0) hinv)
  have hu : H 0 1 / H 0 0 ∈ ordBall F (A.bd 0 0 1) := by
    rw [div_eq_mul_inv]
    exact mem_ordBall_congr (add_zero _) (mul_mem_ordBall_add (hH 0 1) hinv)
  have hunit : diagGL F (Units.mk0 (H 0 0) h0) 1 ∈ unitsFilt F A 0 :=
    diagGL_mem_unitsFilt (by rw [Units.val_mk0, hord]) (by rw [Units.val_one, ord_one])
  refine ⟨a * lowerGL F (H 1 0 / H 0 0) * diagGL F (Units.mk0 (H 0 0) h0) 1, ?_,
    upperGL F (H 0 1 / H 0 0) * b, ?_, Units.mk0 _ hδ, ?_, ?_⟩
  · exact (normalizer F A).mul_mem ((normalizer F A).mul_mem ha
      (unitsFilt_le_normalizer A (lowerGL_mem_unitsFilt hl))) (unitsFilt_le_normalizer A hunit)
  · exact (normalizer F A).mul_mem (unitsFilt_le_normalizer A (upperGL_mem_unitsFilt hu)) hb
  · have hd0 := (mem_ordBall_of_ne_zero hdet).1 (det_mem_ordBall_zero hH)
    rw [Units.val_mk0, ord_mul hdet (inv_ne_zero h0), ord_inv h0, hord]
    omega
  · have e : h = lowerGL F (H 1 0 / H 0 0) * diagGL F (Units.mk0 (H 0 0) h0) 1 *
        diagGL F 1 (Units.mk0 _ hδ) * upperGL F (H 0 1 / H 0 0) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, val_lowerGL, val_diagGL, val_diagGL,
        val_upperGL, Units.val_mk0, Units.val_mk0, Units.val_one, Matrix.det_fin_two, ldu_fin_two h0]
      exact Matrix.eta_fin_two H
    rw [e]
    simp only [mul_assoc]

end Decomposition

section Intertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The value $\psi_\alpha(a z a^{-1}) = \psi_{a^{-1} \alpha a}(z)$. -/
theorem psiAlphaFun_conj_eq_conj (ψ : AddChar F ℂ) (α : Matrix (Fin 2) (Fin 2) F)
    (a z : GL (Fin 2) F) :
    psiAlphaFun F ψ α (a * z * a⁻¹) = psiAlphaFun F ψ
      (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * α * (a : Matrix (Fin 2) (Fin 2) F)) z := by
  unfold psiAlphaFun
  congr 1
  set G : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F)
  set Gi : Matrix (Fin 2) (Fin 2) F := ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set Z : Matrix (Fin 2) (Fin 2) F := (z : Matrix (Fin 2) (Fin 2) F)
  have e1 : ((a * z * a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 = G * (Z - 1) * Gi := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [e1, show α * (G * (Z - 1) * Gi) = (α * G * (Z - 1)) * Gi by simp only [mul_assoc],
    Matrix.trace_mul_comm]
  simp only [mul_assoc]

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

variable (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) {n : ℕ} {α : E}
  (hαA : Algebra.leftMulMatrix v α ∈ radPow F A (-n))

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- The reduction to a middle factor. Let $a, b \in \mathfrak{K}_{\mathfrak{A}}$ and let $g = a D b$ intertwine $\psi_\alpha$. Put $\gamma = a^{-1} \alpha a$ and $\beta = b \alpha b^{-1}$. Then $\psi(\mathrm{tr}((D^{-1} \gamma D - \beta) X)) = 1$ for each $X \in \mathfrak{P}^{[n/2]+1}_{\mathfrak{A}}$ with $D X D^{-1} \in \mathfrak{P}^{[n/2]+1}_{\mathfrak{A}}$. -/
theorem psi_trace_eq_one_of_intertwines {a b D : GL (Fin 2) F} (ha : a ∈ normalizer F A)
    (hb : b ∈ normalizer F A)
    (hI : Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) (a * D * b))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ radPow F A ((n / 2 + 1 : ℕ) : ℤ))
    (hDX : (D : Matrix (Fin 2) (Fin 2) F) * X * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈
      radPow F A ((n / 2 + 1 : ℕ) : ℤ)) :
    ψ ((((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
          (a : Matrix (Fin 2) (Fin 2) F)) * (D : Matrix (Fin 2) (Fin 2) F) -
        (b : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
          ((b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * X).trace = 1 := by
  have hm : 1 ≤ n / 2 + 1 := by omega
  obtain ⟨y, hy, hyX⟩ := exists_unitsFilt_eq_one_add hm hX
  have hx : b⁻¹ * y * b ∈ unitsFilt F A (n / 2 + 1) := by
    have := conj_mem_unitsFilt_of_mem_normalizer ((normalizer F A).inv_mem hb) hm hy
    rwa [inv_inv] at this
  have hz : D * y * D⁻¹ ∈ unitsFilt F A (n / 2 + 1) := by
    rw [mem_unitsFilt_iff hm]
    have e : ((D * y * D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
        (D : Matrix (Fin 2) (Fin 2) F) * X * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Units.val_mul, Units.val_mul, hyX, mul_add, mul_one, add_mul, Units.mul_inv,
        add_sub_cancel_left]
    rw [e]
    exact hDX
  have hgx : a * D * b * (b⁻¹ * y * b) * (a * D * b)⁻¹ = a * (D * y * D⁻¹) * a⁻¹ := by group
  have hmem : a * D * b * (b⁻¹ * y * b) * (a * D * b)⁻¹ ∈ unitsFilt F A (n / 2 + 1) := by
    rw [hgx]
    exact conj_mem_unitsFilt_of_mem_normalizer ha hm hz
  have h1 := congrArg Units.val (hI ⟨_, hx⟩ hmem)
  rw [coe_psiAlphaUnits, coe_psiAlphaUnits] at h1
  change psiAlphaFun F ψ _ (a * D * b * (b⁻¹ * y * b) * (a * D * b)⁻¹) =
    psiAlphaFun F ψ _ (b⁻¹ * y * b) at h1
  rw [hgx, psiAlphaFun_conj_eq_conj, psiAlphaFun_conj_eq_conj,
    show b⁻¹ * y * b = b⁻¹ * y * b⁻¹⁻¹ by rw [inv_inv], psiAlphaFun_conj_eq_conj, inv_inv] at h1
  unfold psiAlphaFun at h1
  rw [hyX, add_sub_cancel_left] at h1
  rw [sub_mul, Matrix.trace_sub]
  generalize (((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
        (a : Matrix (Fin 2) (Fin 2) F)) * (D : Matrix (Fin 2) (Fin 2) F) * X).trace = s at h1 ⊢
  generalize ((b : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
      ((b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X).trace = t at h1 ⊢
  have h2 : ψ (s - t) * ψ t = ψ t := by rw [← AddChar.map_add_eq_mul, sub_add_cancel, h1]
  exact mul_right_cancel₀ (addChar_apply_ne_zero ψ _) (h2.trans (one_mul _).symm)

include hψ in
/-- The core computation of BH §15.1 outside $\mathfrak{K}_{\mathfrak{A}}$. Let $\alpha \in E$ be minimal of level $n \ge 1$, $a, b \in \mathfrak{K}_{\mathfrak{A}}$, $\gamma = a^{-1} \alpha a$, $\beta = b \alpha b^{-1}$ and $D = \mathrm{diag}(1, d)$ with $\mathrm{ord}(d) \ge 1$. Then $\psi(\mathrm{tr}((D^{-1} \gamma D - \beta) X)) = 1$ does not hold for each $X \in \mathfrak{P}^{[n/2]+1}_{\mathfrak{A}} \cap D^{-1} \mathfrak{P}^{[n/2]+1}_{\mathfrak{A}} D$. The test matrices $X = c E_{01}$ give $\gamma_{10} \in \mathfrak{p}^{b(1-n, 1, 0)}_F$. Then $\delta = \gamma - \gamma_{00}$ is a conjugate of $\alpha - \gamma_{00}$, whose inverse lies in $\mathfrak{p}^n_E$ by minimality, and $(\delta^{-1} \delta)_{00} = \delta^{-1}_{01} \gamma_{10} \in \mathfrak{p}_F$ is a contradiction. -/
theorem false_of_forall_psi_trace (hv : IsAdapted A v) (hα : IsMinimalElt F n α) (hn : 1 ≤ n)
    {a b : GL (Fin 2) F} (ha : a ∈ normalizer F A) (hb : b ∈ normalizer F A) {d : Fˣ}
    (hd : 1 ≤ ord F (d : F))
    (h : ∀ X ∈ radPow F A ((n / 2 + 1 : ℕ) : ℤ),
      ((diagGL F 1 d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X *
          (((diagGL F 1 d)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈
        radPow F A ((n / 2 + 1 : ℕ) : ℤ) →
      ψ (((((diagGL F 1 d)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
            (a : Matrix (Fin 2) (Fin 2) F)) *
          ((diagGL F 1 d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
        (b : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
          ((b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * X).trace = 1) :
    False := by
  set m : ℤ := ((n / 2 + 1 : ℕ) : ℤ) with hmdef
  set L : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v α with hL
  set Am : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F)
  set Ai : Matrix (Fin 2) (Fin 2) F := ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set γ : Matrix (Fin 2) (Fin 2) F := Ai * L * Am with hγ
  set β : Matrix (Fin 2) (Fin 2) F :=
    (b : Matrix (Fin 2) (Fin 2) F) * L * ((b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  have hαA : L ∈ radPow F A (-n) := (hv.leftMulMatrix_mem_radPow_iff _ α).2 hα.1
  have haA : a⁻¹ ∈ normalizer F A := (normalizer F A).inv_mem ha
  have hγn : γ ∈ radPow F A (-n) := by
    have := conj_mem_radPow_of_mem_normalizer haA hαA
    rwa [inv_inv] at this
  have hβn : β ∈ radPow F A (-n) := conj_mem_radPow_of_mem_normalizer hb hαA
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  -- The entry `(1, 0)` of `D⁻¹ γ D - β`.
  set Y : Matrix (Fin 2) (Fin 2) F :=
    (((diagGL F 1 d)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * γ *
      ((diagGL F 1 d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - β with hYdef
  have hY : Y 1 0 ∈ ordBall F (1 - (A.bd m 0 1 + ord F (d : F))) := by
    have key := (hψ.forall_mul_iff (A.bd m 0 1 + ord F (d : F)) (Y 1 0)).1 fun c hc => by
      have hc' : c ∈ ordBall F (A.bd m 0 1) := ordBall_anti (by omega) hc
      have hX : Matrix.single 0 1 c ∈ radPow F A m := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hc', zero_mem_ordBall]
      have hDX : ((diagGL F 1 d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Matrix.single 0 1 c *
          (((diagGL F 1 d)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
            Matrix.single 0 1 (c * (d : F)⁻¹) := by
        rw [val_diagGL, val_diagGL_inv]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.vecMul, dotProduct]
      have hcd : c * (d : F)⁻¹ ∈ ordBall F (A.bd m 0 1) := by
        rw [mul_comm, mul_mem_ordBall_iff (inv_ne_zero hd0), ord_inv hd0, sub_neg_eq_add]
        exact hc
      have hX2 : Matrix.single 0 1 (c * (d : F)⁻¹) ∈ radPow F A m := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hcd, zero_mem_ordBall]
      have := h _ hX (by rw [hDX]; exact hX2)
      rwa [Matrix.trace_mul_single, op_smul_eq_mul, mul_comm] at this
    exact mem_ordBall_congr (by ring) key
  have hY10 : Y 1 0 = (d : F)⁻¹ * γ 1 0 - β 1 0 := by
    rw [hYdef, val_diagGL, val_diagGL_inv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hγ10 : γ 1 0 = (d : F) * Y 1 0 + (d : F) * β 1 0 := by
    rw [hY10, mul_sub, mul_inv_cancel_left₀ hd0, sub_add_cancel]
  have hb1 : A.bd (1 - n) 1 0 ≤ 1 - A.bd m 0 1 :=
    le_trans (A.bd_mono (by omega) 1 0) (A.bd_one_sub_le m 1 0)
  have hb2 : A.bd (1 - n) 1 0 ≤ A.bd (-n) 1 0 + 1 := by
    have e := A.bd_add_mul (-n) 1 1 0
    rw [mul_one] at e
    rw [← e]
    exact A.bd_mono (by have := A.e_pos; omega) 1 0
  have hγ10m : γ 1 0 ∈ ordBall F (A.bd (1 - n) 1 0) := by
    rw [hγ10]
    refine add_mem_ordBall (ordBall_anti hb1 ?_) (ordBall_anti hb2 ?_)
    · rw [mul_mem_ordBall_iff hd0]
      exact mem_ordBall_congr (by ring) hY
    · exact mem_ordBall_congr (by ring) (mul_mem_ordBall_add (mem_ordBall_of_le hd0 hd) (hβn 1 0))
  -- The minimality of `α` gives the inverse of `α - γ₀₀` in `𝔭^n_E`.
  have hc00 : γ 0 0 ∈ ordBall F (A.bd (-n) 0 0) := hγn 0 0
  have hc11 : γ 0 0 ∈ ordBall F (A.bd (-n) 1 1) := by
    rw [A.bd_self (-n) 1 0]
    exact hc00
  have hcz : algebraMap F E (γ 0 0) ∈ ordBall E (-n) := by
    rw [← hv.leftMulMatrix_mem_radPow_iff, AlgHom.commutes]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_matrix_apply, zero_mem_ordBall, hc00, hc11]
  have hsub : α - algebraMap F E (γ 0 0) ∈ ordBall E (-n) := by
    rw [sub_eq_add_neg]
    exact add_mem_ordBall hα.1 (neg_mem_ordBall hcz)
  obtain ⟨hne, hle⟩ := hα.sub_ne_zero_and (γ 0 0)
  have hord : ord E (α - algebraMap F E (γ 0 0)) = -n :=
    le_antisymm hle ((mem_ordBall_of_ne_zero hne).1 hsub)
  have hinvb : (α - algebraMap F E (γ 0 0))⁻¹ ∈ ordBall E n :=
    mem_ordBall_of_le (inv_ne_zero hne) (by rw [ord_inv hne, hord, neg_neg])
  set P : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v (α - algebraMap F E (γ 0 0)) with hP
  set Q : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v (α - algebraMap F E (γ 0 0))⁻¹ with hQ
  have hQP : Q * P = 1 := by rw [hP, hQ, ← map_mul, inv_mul_cancel₀ hne, map_one]
  have hQn : Q ∈ radPow F A n := (hv.leftMulMatrix_mem_radPow_iff _ _).2 hinvb
  have hδi : Ai * Q * Am ∈ radPow F A n := by
    have := conj_mem_radPow_of_mem_normalizer haA hQn
    rwa [inv_inv] at this
  have hAA : Am * Ai = 1 := Units.mul_inv a
  have hAA' : Ai * Am = 1 := Units.inv_mul a
  have hδiδ : (Ai * Q * Am) * (Ai * P * Am) = 1 := by
    calc (Ai * Q * Am) * (Ai * P * Am) = Ai * (Q * (Am * Ai) * P) * Am := by
          simp only [mul_assoc]
      _ = 1 := by rw [hAA, mul_one, hQP, mul_one, hAA']
  have hδ : Ai * P * Am = γ - (γ 0 0) • 1 := by
    rw [hP, map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_one, hAA']
  have key := congrFun (congrFun hδiδ 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, hδ] at key
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    sub_self, mul_zero, zero_add] at key
  rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero] at key
  have hmem := mul_mem_ordBall_bd (hδi 0 1) hγ10m
  rw [key, show (n : ℤ) + (1 - n) = 1 by ring, mem_ordBall_of_ne_zero one_ne_zero, ord_one] at hmem
  have := A.one_le_bd_self (le_refl 1) 0
  omega

/-- BH §15.1 outside $\mathfrak{K}_{\mathfrak{A}}$. Let $v$ be adapted to $\mathfrak{A}$ and $\alpha \in E$ minimal of level $n \ge 1$. Each $g \in GL_2(F)$ that intertwines the character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ lies in $\mathfrak{K}_{\mathfrak{A}}$. This is the hypothesis `hK` of `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType`. -/
theorem mem_normalizer_of_intertwines_psiAlpha (hv : IsAdapted A v) (hα : IsMinimalElt F n α)
    (hn : 1 ≤ n) {g : GL (Fin 2) F}
    (hI : Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g) :
    g ∈ normalizer F A := by
  obtain ⟨a, ha, b, hb, d, hd, rfl⟩ := exists_normalizer_mul_diag_mul A g
  by_cases hd0 : ord F (d : F) = 0
  · exact (normalizer F A).mul_mem ((normalizer F A).mul_mem ha (unitsFilt_le_normalizer A
      (diagGL_mem_unitsFilt (by rw [Units.val_one, ord_one]) hd0))) hb
  · exact (false_of_forall_psi_trace ψ hψ hv hα hn ha hb (by omega)
      fun X hX hDX => psi_trace_eq_one_of_intertwines ψ hψ hαA ha hb hI hX hDX).elim

variable [Algebra.IsQuadraticExtension F E]

/-- The intertwining of $\psi_\alpha$ (BH §15.1). Let $v$ be adapted to $\mathfrak{A}$ and $\alpha \in E$ minimal of level $n \ge 1$. An element $g \in GL_2(F)$ intertwines the character $\psi_\alpha$ of $U^{[n/2]+1}_{\mathfrak{A}}$ exactly when $g \in J_\alpha = E^\times U^{[(n+1)/2]}_{\mathfrak{A}}$. -/
theorem intertwines_psiAlpha_iff_mem_jGroup (hv : IsAdapted A v) (hα : IsMinimalElt F n α)
    (hn : 1 ≤ n) (g : GL (Fin 2) F) :
    Intertwines (unitsFilt F A (n / 2 + 1)) (psiAlphaUnits ψ hψ n α hαA) g ↔
      g ∈ jGroup v hv ((n + 1) / 2) :=
  ⟨fun hI => (intertwines_psiAlpha_iff hv ψ hψ hαA hα hn
      (mem_normalizer_of_intertwines_psiAlpha ψ hψ hαA hv hα hn hI)).1 hI,
    intertwines_psiAlpha_of_mem_jGroup hv ψ hψ hαA hα hn⟩

variable (ξ : Eˣ →* ℂˣ)

/-- The intertwining of a cuspidal type (BH §15.1 and §15.6). Let $v$ be adapted to $\mathfrak{A}$, $\alpha \in E$ minimal of level $n \ge 1$ and $\Lambda$ a cuspidal type of $J_\alpha$. An element $g \in GL_2(F)$ intertwines $\Lambda$ exactly when $g \in J_\alpha$. -/
theorem intertwines_cuspType_iff_mem_jGroup (hv : IsAdapted A v) (hα : IsMinimalElt F n α)
    (hn : 1 ≤ n) {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ} (hΛ : Λ ∈ cuspTypes hv ψ hψ n α hαA ξ)
    (g : GL (Fin 2) F) :
    Intertwines (jGroup v hv ((n + 1) / 2)) Λ g ↔ g ∈ jGroup v hv ((n + 1) / 2) :=
  ⟨fun hI => (intertwines_psiAlpha_iff_mem_jGroup ψ hψ hαA hv hα hn g).1
      (intertwines_psiAlpha_of_mem_cuspTypes hv ψ hψ hαA ξ hΛ hI),
    fun hJ => intertwines_of_mem _ Λ hJ⟩

/-- The intertwining of a cuspidal type is $J_\alpha$, without the hypothesis `hK` of `Langlands.LocalGL2.mem_jGroup_of_intertwines_cuspType`. This is the form that the irreducibility criterion `Langlands.eq_smul_cIndBasic_of_isotypic` uses. -/
theorem mem_jGroup_of_intertwines_cuspType_of_isMinimalElt (hv : IsAdapted A v)
    (hα : IsMinimalElt F n α) (hn : 1 ≤ n) {Λ : jGroup v hv ((n + 1) / 2) →* ℂˣ}
    (hΛ : Λ ∈ cuspTypes hv ψ hψ n α hαA ξ) :
    ∀ g, Intertwines (jGroup v hv ((n + 1) / 2)) Λ g → g ∈ jGroup v hv ((n + 1) / 2) :=
  mem_jGroup_of_intertwines_cuspType hv ψ hψ hαA ξ hα hn
    (fun _ hI => mem_normalizer_of_intertwines_psiAlpha ψ hψ hαA hv hα hn hI) hΛ

end Intertwining

section Ramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)] [Algebra.IsQuadraticExtension F E]

/-- The ramified case (BH §15.1 for $\mathfrak{A} = \mathfrak{J}$). Let $E/F$ be ramified, $n$ odd and $\alpha \in E$ with $\mathrm{ord}_E(\alpha) = -n$, embedded by the basis $(\varpi_E, 1)$. The intertwining of each cuspidal type $\Lambda$ of $J_\alpha$ is $J_\alpha$. -/
theorem mem_jGroup_of_intertwines_cuspType_ramBasis (hr : IsTotallyRamifiedExt F E)
    (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1)) {n : ℕ} (hodd : Odd n) {α : E} (hα0 : α ≠ 0)
    (hord : ord E α = -n)
    (hαA : Algebra.leftMulMatrix (ramBasis F E hr) α ∈ radPow F ChainOrder.iwahori (-n))
    (ξ : Eˣ →* ℂˣ)
    {Λ : jGroup (ramBasis F E hr) (isAdapted_ramBasis hr) ((n + 1) / 2) →* ℂˣ}
    (hΛ : Λ ∈ cuspTypes (isAdapted_ramBasis hr) ψ hψ n α hαA ξ) :
    ∀ g, Intertwines (jGroup (ramBasis F E hr) (isAdapted_ramBasis hr) ((n + 1) / 2)) Λ g →
      g ∈ jGroup (ramBasis F E hr) (isAdapted_ramBasis hr) ((n + 1) / 2) :=
  mem_jGroup_of_intertwines_cuspType_of_isMinimalElt ψ hψ hαA ξ (isAdapted_ramBasis hr)
    (isMinimalElt_of_ramified hr hodd hα0 hord) (by obtain ⟨k, hk⟩ := hodd; omega) hΛ

end Ramified

end Langlands.LocalGL2
