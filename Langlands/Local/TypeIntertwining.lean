/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.TypeInjective

/-!
# Intertwining types have the same chain order and the same level

Let $K$ be a nonarchimedean local field. Let $D$ be a cuspidal type datum for an admissible pair $(L/K, \xi)$, with chain order $\mathfrak{A}$, level $n$ and character $\Lambda$ of $J_\alpha$, and let $D'$ be a datum for $(L'/K, \xi')$ with $\mathfrak{A}'$, $n'$ and $\Lambda'$. This file proves the first step of Bushnell and Henniart 15.7 for the statement `Langlands.LocalGL2.TypeIntertwiningIso`: if some $g \in GL_2(K)$ intertwines $\Lambda$ with $\Lambda'$, then $\mathfrak{A}' = \mathfrak{A}$, $n' = n$ and $g \in \mathfrak{K}_{\mathfrak{A}}$. Thus `Langlands.LocalGL2.TypeIntertwiningIso` is equivalent to the statement `Langlands.LocalGL2.TypeIntertwiningNormalizerIso`, which has these three facts as hypotheses.

## Main definitions

* `Langlands.LocalGL2.TypeIntertwiningNormalizerIso`: the statement that an element $g \in \mathfrak{K}_{\mathfrak{A}}$ that intertwines the characters of two data with the same chain order $\mathfrak{A}$ and the same level gives $K$-isomorphic pairs.

## Main results

* `Langlands.LocalGL2.conj_apply_not_mem_ordBall`: for $\alpha$ minimal of level $n$, $a \in \mathfrak{K}_{\mathfrak{A}}$ and $i \ne j$, the entry $(a^{-1} \alpha a)_{ij}$ does not lie in $\mathfrak{p}^{b(1-n, i, j)}_K$.
* `Langlands.LocalGL2.eq_and_mem_normalizer_of_forall_psiAlphaFun`: if $\psi_\alpha(g x g^{-1}) = 1$ for each $x \in U^{k_0}_{\mathfrak{A}}$ of determinant $1$ with $g x g^{-1} \in U^m_{\mathfrak{A}}$, and $1 \le k_0 \le n + 1$, then $k_0 = n + 1$ and $g \in \mathfrak{K}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.TameDatum.level_eq_and_mem_normalizer_of_A_eq`: intertwining data with the same chain order have the same level, and the intertwining element lies in $\mathfrak{K}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.TameDatum.false_of_maximal_iwahori`: no element intertwines the character of a datum for the maximal order with the character of a datum for the Iwahori order.
* `Langlands.LocalGL2.TameDatum.A_eq_and_level_eq_of_intertwinesWith`: intertwining data have the same chain order and the same level, and the intertwining element lies in $\mathfrak{K}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.typeIntertwiningIso_iff_typeIntertwiningNormalizerIso`: `Langlands.LocalGL2.TypeIntertwiningIso K` is equivalent to `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K`.
* `Langlands.LocalGL2.typeRepInjective_of_typeIntertwiningNormalizerIso`: `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K` gives `Langlands.LocalGL2.TypeRepInjective K`.

## Proof

The two data have their own additive characters $\psi$ and $\psi'$ of level one, and their own twisting characters $\chi$ and $\chi'$. The proof uses only test elements of determinant $1$, so that $\chi \circ \det$ and $\chi' \circ \det$ do not occur. On these elements of $U^{(n+1)/2}_{\mathfrak{A}}$ the character $\Lambda$ is $\psi_\alpha$, and on these elements of $U^{n+1}_{\mathfrak{A}}$ it is trivial.

Let $U^{k_0}_{\mathfrak{A}'} \subseteq U^{n+1}_{\mathfrak{A}}$. Then $\psi'_{\alpha'}(g x g^{-1}) = 1$ for each $x \in U^{k_0}_{\mathfrak{A}'}$ of determinant $1$ with $g x g^{-1} \in U^{(n'+1)/2}_{\mathfrak{A}'}$. Write $g = a \, \mathrm{diag}(1, d) \, b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}'}$. The test elements $b^{-1} \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix} b$ give a bound on the entry $(1, 0)$ of $a^{-1} \alpha' a$. The minimality of $\alpha'$ contradicts this bound, unless $\mathrm{ord}(d) = 0$ and $k_0 = n' + 1$.

For the same chain order, take $k_0 = n + 1$ in both directions. This gives $n = n'$ and $g \in \mathfrak{K}_{\mathfrak{A}}$. For the maximal order $\mathfrak{M}$ and the Iwahori order $\mathfrak{J}$, the inclusions $U^{2k}_{\mathfrak{J}} \subseteq U^k_{\mathfrak{M}}$ and $U^{k+1}_{\mathfrak{M}} \subseteq U^{2k+1}_{\mathfrak{J}}$ exclude each odd $n'$ except $n' = 2n + 1$ and $n' = 2n - 1$. In these two border cases, the element $g$ or $g^{-1}$ normalizes the order. Then a unipotent test element in both groups gives $\psi'(c \gamma') = \psi(c \beta)$ for each $c$ in a ball, with a known bound on $\beta$. This bound passes to $\gamma'$, and the minimality contradicts it again.

## Still open

* The statement `Langlands.LocalGL2.TypeIntertwiningNormalizerIso`, thus `Langlands.LocalGL2.TypeIntertwiningIso` and `Langlands.LocalGL2.TypeRepInjective`. For $g \in \mathfrak{K}_{\mathfrak{A}}$ it remains to show that $L$ and $L'$ are $K$-isomorphic and that $\xi = \xi' \circ j$ (Bushnell and Henniart, 15.7 and 20.2). This needs the comparison $\psi' = \psi(u \, \cdot)$ of two characters of level one, the uniqueness of the unramified quadratic extension, and for ramified $L$ the square class of the discriminant of $\alpha$. With a $K$-isomorphism $j$ and an element $h$ with $h \iota(y) h^{-1} = \iota'(j(y))$, the result `Langlands.LocalGL2.TameDatum.iso_of_intertwinesWith_conj` finishes the proof.

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, §§12 to 15 and §20.
-/

namespace Langlands

universe w

section IntertwiningInverse

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If $g$ intertwines $\Lambda$ with $\Lambda'$, then $g^{-1}$ intertwines $\Lambda'$ with $\Lambda$. -/
theorem IntertwinesWith.inv {J J' : Subgroup G} {Λ : J →* ℂˣ} {Λ' : J' →* ℂˣ} {g : G}
    (h : IntertwinesWith J J' Λ Λ' g) : IntertwinesWith J' J Λ' Λ g⁻¹ := by
  intro y hy
  have hx : g * (g⁻¹ * (y : G) * g⁻¹⁻¹) * g⁻¹ ∈ J' := by
    simp [mul_assoc]
  have e := h ⟨_, hy⟩ hx
  rw [← e]
  congr 1
  ext
  simp [mul_assoc]

end IntertwiningInverse

end Langlands

namespace Langlands.LocalGL2

universe u v

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section Unipotent

variable {F : Type u} [Field F]

/-- The determinant of the upper unipotent element is $1$. -/
theorem det_upperGL (c : F) : Matrix.GeneralLinearGroup.det (upperGL F c) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, val_upperGL, Matrix.det_fin_two_of]

/-- The determinant of the lower unipotent element is $1$. -/
theorem det_lowerGL (c : F) : Matrix.GeneralLinearGroup.det (lowerGL F c) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, val_lowerGL, Matrix.det_fin_two_of]

/-- Conjugation by $\mathrm{diag}(1, d)$ maps the upper unipotent element of $c$ to the upper unipotent element of $c d^{-1}$. -/
theorem diagGL_mul_upperGL_mul_inv (c : F) (d : Fˣ) :
    diagGL F 1 d * upperGL F c * (diagGL F 1 d)⁻¹ = upperGL F (c * (d : F)⁻¹) := by
  ext i j
  rw [Units.val_mul, Units.val_mul, val_diagGL, val_diagGL_inv, val_upperGL, val_upperGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The value $\psi_Y$ of the upper unipotent element of $c$ is $\psi(c Y_{10})$. -/
theorem psiAlphaFun_upperGL (ψ : AddChar F ℂ) (Y : Matrix (Fin 2) (Fin 2) F) (c : F) :
    psiAlphaFun F ψ Y (upperGL F c) = ψ (c * Y 1 0) := by
  unfold psiAlphaFun
  rw [val_upperGL]
  congr 1
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  ring

/-- The value $\psi_Y$ of the lower unipotent element of $c$ is $\psi(c Y_{01})$. -/
theorem psiAlphaFun_lowerGL (ψ : AddChar F ℂ) (Y : Matrix (Fin 2) (Fin 2) F) (c : F) :
    psiAlphaFun F ψ Y (lowerGL F c) = ψ (c * Y 0 1) := by
  unfold psiAlphaFun
  rw [val_lowerGL]
  congr 1
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  ring

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- For $k \ge 1$ and $c \in \mathfrak{p}^{b(k, 0, 1)}_F$ the upper unipotent element of $c$ lies in $U^k_{\mathfrak{A}}$. -/
theorem upperGL_mem_unitsFilt_of_one_le {A : ChainOrder} {k : ℕ} (hk : 1 ≤ k) {c : F}
    (hc : c ∈ ordBall F (A.bd k 0 1)) : upperGL F c ∈ unitsFilt F A k := by
  rw [mem_unitsFilt_iff hk, val_upperGL]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, hc, zero_mem_ordBall]

/-- For $k \ge 1$ and $c \in \mathfrak{p}^{b(k, 1, 0)}_F$ the lower unipotent element of $c$ lies in $U^k_{\mathfrak{A}}$. -/
theorem lowerGL_mem_unitsFilt_of_one_le {A : ChainOrder} {k : ℕ} (hk : 1 ≤ k) {c : F}
    (hc : c ∈ ordBall F (A.bd k 1 0)) : lowerGL F c ∈ unitsFilt F A k := by
  rw [mem_unitsFilt_iff hk, val_lowerGL]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two, hc, zero_mem_ordBall]

/-- The inclusion $U^{2k}_{\mathfrak{J}} \subseteq U^k_{\mathfrak{M}}$ for $k \ge 1$. -/
theorem unitsFilt_iwahori_le_maximal {k : ℕ} (hk : 1 ≤ k) :
    unitsFilt F iwahori (2 * k) ≤ unitsFilt F maximal k := by
  intro x hx
  rw [mem_unitsFilt_iff (by omega)] at hx
  rw [mem_unitsFilt_iff hk]
  intro i j
  refine ordBall_anti ?_ (hx i j)
  fin_cases i <;> fin_cases j <;> simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e] <;> omega

/-- The inclusion $U^{k+1}_{\mathfrak{M}} \subseteq U^{2k+1}_{\mathfrak{J}}$. -/
theorem unitsFilt_maximal_le_iwahori (k : ℕ) :
    unitsFilt F maximal (k + 1) ≤ unitsFilt F iwahori (2 * k + 1) := by
  intro x hx
  rw [mem_unitsFilt_iff (by omega)] at hx
  rw [mem_unitsFilt_iff (by omega)]
  intro i j
  refine ordBall_anti ?_ (hx i j)
  fin_cases i <;> fin_cases j <;> simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e] <;> omega

/-- Let $\psi$ and $\psi'$ have level one and let $b \in \mathfrak{p}^r_F$. If $\psi'(c a) = \psi(c b)$ for each $c \in \mathfrak{p}^{1-r}_F$, then $a \in \mathfrak{p}^r_F$. -/
theorem mem_ordBall_of_forall_psi_mul_eq {ψ ψ' : AddChar F ℂ} (hψ : IsConductor ψ (-1))
    (hψ' : IsConductor ψ' (-1)) {r : ℤ} {a b : F} (hb : b ∈ ordBall F r)
    (h : ∀ c ∈ ordBall F (1 - r), ψ' (c * a) = ψ (c * b)) : a ∈ ordBall F r := by
  have key := (hψ'.forall_mul_iff (1 - r) a).1 fun c hc => by
    rw [h c hc]
    exact hψ.trivial _ (by
      rw [neg_neg]
      exact mem_ordBall_congr (by ring) (mul_mem_ordBall_add hc hb))
  exact mem_ordBall_congr (by ring) key

end Unipotent

section Strata

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E} {n : ℕ} {α : E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For $i \ne j$, the entry $(j, j)$ of $M (N - N_{jj})$ is $M_{ji} N_{ij}$. -/
theorem mul_sub_smul_one_apply_self (M N : Matrix (Fin 2) (Fin 2) F) {i j : Fin 2} (hij : i ≠ j) :
    (M * (N - N j j • 1)) j j = M j i * N i j := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij |
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The off-diagonal entries of a conjugate of a minimal element.** Let $v$ be adapted to $\mathfrak{A}$, $\alpha \in E$ minimal of level $n$ and $a \in \mathfrak{K}_{\mathfrak{A}}$. Put $\gamma = a^{-1} \alpha a$. For $i \ne j$ the entry $\gamma_{ij}$ does not lie in $\mathfrak{p}^{b(1-n, i, j)}_F$. The element $\delta = \gamma - \gamma_{jj}$ is a conjugate of $\alpha - \gamma_{jj}$, whose inverse lies in $\mathfrak{p}^n_E$ by minimality, and $1 = (\delta^{-1} \delta)_{jj} = \delta^{-1}_{ji} \gamma_{ij}$. -/
theorem conj_apply_not_mem_ordBall (hv : IsAdapted A v) (hα : IsMinimalElt F n α)
    {a : GL (Fin 2) F} (ha : a ∈ normalizer F A) {i j : Fin 2} (hij : i ≠ j) :
    (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v α *
      (a : Matrix (Fin 2) (Fin 2) F)) i j ∉ ordBall F (A.bd (1 - n) i j) := by
  intro hγij
  set L : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v α with hL
  set Am : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F)
  set Ai : Matrix (Fin 2) (Fin 2) F := ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  set γ : Matrix (Fin 2) (Fin 2) F := Ai * L * Am with hγ
  have hαA : L ∈ radPow F A (-n) := (hv.leftMulMatrix_mem_radPow_iff _ α).2 hα.1
  have haA : a⁻¹ ∈ normalizer F A := (normalizer F A).inv_mem ha
  have hγn : γ ∈ radPow F A (-n) := by
    have := conj_mem_radPow_of_mem_normalizer haA hαA
    rwa [inv_inv] at this
  have hcd : ∀ k, γ j j ∈ ordBall F (A.bd (-n) k k) := fun k => by
    rw [A.bd_self (-n) k j]
    exact hγn j j
  have hcz : algebraMap F E (γ j j) ∈ ordBall E (-n) := by
    rw [← hv.leftMulMatrix_mem_radPow_iff, AlgHom.commutes]
    intro k l
    by_cases hkl : k = l
    · subst hkl
      simpa [Matrix.algebraMap_matrix_apply] using hcd k
    · simp [Matrix.algebraMap_matrix_apply, hkl, zero_mem_ordBall]
  have hsub : α - algebraMap F E (γ j j) ∈ ordBall E (-n) := by
    rw [sub_eq_add_neg]
    exact add_mem_ordBall hα.1 (neg_mem_ordBall hcz)
  obtain ⟨hne, hle⟩ := hα.sub_ne_zero_and (γ j j)
  have hord : ord E (α - algebraMap F E (γ j j)) = -n :=
    le_antisymm hle ((mem_ordBall_of_ne_zero hne).1 hsub)
  have hinvb : (α - algebraMap F E (γ j j))⁻¹ ∈ ordBall E n :=
    mem_ordBall_of_le (inv_ne_zero hne) (by rw [ord_inv hne, hord, neg_neg])
  set P : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v (α - algebraMap F E (γ j j)) with hP
  set Q : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix v (α - algebraMap F E (γ j j))⁻¹
    with hQ
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
  have hδ : Ai * P * Am = γ - γ j j • 1 := by
    rw [hP, map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_one, hAA']
  have key := congrFun (congrFun hδiδ j) j
  rw [hδ, mul_sub_smul_one_apply_self _ _ hij, Matrix.one_apply_eq] at key
  have hmem := mul_mem_ordBall_bd (hδi j i) hγij
  rw [key, show (n : ℤ) + (1 - n) = 1 by ring, mem_ordBall_of_ne_zero one_ne_zero, ord_one] at hmem
  have := A.one_le_bd_self (le_refl 1) j
  omega

variable (ψ : AddChar F ℂ) (hψ : IsConductor ψ (-1))

include hψ in
/-- **The core computation.** Let $v$ be adapted to $\mathfrak{A}$, $\alpha \in E$ minimal of level $n$ and $1 \le m \le n$, $1 \le k_0 \le n + 1$. Assume that $\psi_\alpha(g x g^{-1}) = 1$ for each $x \in U^{k_0}_{\mathfrak{A}}$ of determinant $1$ with $g x g^{-1} \in U^m_{\mathfrak{A}}$. If $g = a \, \mathrm{diag}(1, d) \, b$ with $a, b \in \mathfrak{K}_{\mathfrak{A}}$ and $\mathrm{ord}(d) \ge 0$, then $k_0 = n + 1$ and $\mathrm{ord}(d) = 0$. The test elements are the conjugates $b^{-1} \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix} b$. -/
theorem eq_and_ord_eq_zero_of_forall_psiAlphaFun (hv : IsAdapted A v) (hα : IsMinimalElt F n α)
    {m k₀ : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (hk1 : 1 ≤ k₀) (hkn : k₀ ≤ n + 1) {g : GL (Fin 2) F}
    (H : ∀ x ∈ unitsFilt F A k₀, Matrix.GeneralLinearGroup.det x = 1 →
      g * x * g⁻¹ ∈ unitsFilt F A m →
        psiAlphaFun F ψ (Algebra.leftMulMatrix v α) (g * x * g⁻¹) = 1)
    {a b : GL (Fin 2) F} (ha : a ∈ normalizer F A) (hb : b ∈ normalizer F A) {d : Fˣ}
    (hd : 0 ≤ ord F (d : F)) (hg : g = a * diagGL F 1 d * b) :
    k₀ = n + 1 ∧ ord F (d : F) = 0 := by
  set γ : Matrix (Fin 2) (Fin 2) F := ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    Algebra.leftMulMatrix v α * (a : Matrix (Fin 2) (Fin 2) F) with hγ
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  set N : ℤ := max (A.bd k₀ 0 1) (A.bd m 0 1 + ord F (d : F)) with hN
  have hψc : ∀ c ∈ ordBall F N, ψ (c * ((d : F)⁻¹ * γ 1 0)) = 1 := by
    intro c hc
    have hc1 : c ∈ ordBall F (A.bd k₀ 0 1) := ordBall_anti (le_max_left _ _) hc
    have hc2 : c * (d : F)⁻¹ ∈ ordBall F (A.bd m 0 1) := by
      rw [mul_comm, mul_mem_ordBall_iff (inv_ne_zero hd0), ord_inv hd0, sub_neg_eq_add]
      exact ordBall_anti (le_max_right _ _) hc
    have hu := upperGL_mem_unitsFilt_of_one_le hk1 hc1
    have hx : b⁻¹ * upperGL F c * b ∈ unitsFilt F A k₀ := by
      have := conj_mem_unitsFilt_of_mem_normalizer ((normalizer F A).inv_mem hb) hk1 hu
      rwa [inv_inv] at this
    have hdet : Matrix.GeneralLinearGroup.det (b⁻¹ * upperGL F c * b) = 1 := by
      rw [map_mul, map_mul, det_upperGL, mul_one, map_inv, inv_mul_cancel]
    have hgx : g * (b⁻¹ * upperGL F c * b) * g⁻¹ = a * upperGL F (c * (d : F)⁻¹) * a⁻¹ := by
      rw [← diagGL_mul_upperGL_mul_inv, hg]
      group
    have hmem : g * (b⁻¹ * upperGL F c * b) * g⁻¹ ∈ unitsFilt F A m := by
      rw [hgx]
      exact conj_mem_unitsFilt_of_mem_normalizer ha hm1 (upperGL_mem_unitsFilt_of_one_le hm1 hc2)
    have e := H _ hx hdet hmem
    rw [hgx, psiAlphaFun_conj_eq_conj, psiAlphaFun_upperGL] at e
    rw [← e]
    congr 1
    ring
  have h1 := (hψ.forall_mul_iff N _).1 hψc
  have h2 : γ 1 0 ∈ ordBall F (1 - N + ord F (d : F)) := by
    have := (mul_mem_ordBall_iff (inv_ne_zero hd0) _ _).1 h1
    rw [ord_inv hd0] at this
    exact mem_ordBall_congr (by ring) this
  have hnot := conj_apply_not_mem_ordBall hv hα ha (by decide : (1 : Fin 2) ≠ 0)
  have hlt : 1 - N + ord F (d : F) < A.bd (1 - n) 1 0 := by
    by_contra hle
    exact hnot (ordBall_anti (not_lt.1 hle) h2)
  have hB1 : A.bd (1 - n) 1 0 ≤ 1 - A.bd m 0 1 :=
    le_trans (A.bd_mono (by omega) 1 0) (A.bd_one_sub_le m 1 0)
  have hB2 : A.bd (1 - n) 1 0 ≤ 1 - A.bd k₀ 0 1 + 1 := by
    have e := A.bd_add_mul (1 - k₀) 1 1 0
    rw [mul_one] at e
    have := A.bd_mono (show (1 : ℤ) - n ≤ 1 - k₀ + A.e by have := A.e_pos; omega) 1 0
    have := A.bd_one_sub_le k₀ 1 0
    omega
  have hB3 : k₀ ≤ n → A.bd (1 - n) 1 0 ≤ 1 - A.bd k₀ 0 1 := fun h =>
    le_trans (A.bd_mono (by omega) 1 0) (A.bd_one_sub_le k₀ 1 0)
  by_cases hk : k₀ ≤ n
  · have := hB3 hk
    omega
  · omega

include hψ in
/-- **An intertwining condition forces the normalizer.** Let $v$ be adapted to $\mathfrak{A}$, $\alpha \in E$ minimal of level $n$, $1 \le m \le n$ and $1 \le k_0 \le n + 1$. Assume that $\psi_\alpha(g x g^{-1}) = 1$ for each $x \in U^{k_0}_{\mathfrak{A}}$ of determinant $1$ with $g x g^{-1} \in U^m_{\mathfrak{A}}$. Then $k_0 = n + 1$ and $g \in \mathfrak{K}_{\mathfrak{A}}$. -/
theorem eq_and_mem_normalizer_of_forall_psiAlphaFun (hv : IsAdapted A v)
    (hα : IsMinimalElt F n α) {m k₀ : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (hk1 : 1 ≤ k₀)
    (hkn : k₀ ≤ n + 1) {g : GL (Fin 2) F}
    (H : ∀ x ∈ unitsFilt F A k₀, Matrix.GeneralLinearGroup.det x = 1 →
      g * x * g⁻¹ ∈ unitsFilt F A m →
        psiAlphaFun F ψ (Algebra.leftMulMatrix v α) (g * x * g⁻¹) = 1) :
    k₀ = n + 1 ∧ g ∈ normalizer F A := by
  obtain ⟨a, ha, b, hb, d, hd, hg⟩ := exists_normalizer_mul_diag_mul A g
  obtain ⟨hk, hd0⟩ := eq_and_ord_eq_zero_of_forall_psiAlphaFun ψ hψ hv hα hm1 hmn hk1 hkn H ha hb
    hd hg
  refine ⟨hk, ?_⟩
  rw [hg]
  exact (normalizer F A).mul_mem ((normalizer F A).mul_mem ha (unitsFilt_le_normalizer A
    (diagGL_mem_unitsFilt (by rw [Units.val_one, ord_one]) hd0))) hb

end Strata

section Datum

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

variable {L L' : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  [Algebra.IsQuadraticExtension K L'] {ξ : Lˣ →* ℂˣ} {ξ' : L'ˣ →* ℂˣ}

/-- The level $n$ of a datum is odd, thus $[n/2] + 1 = (n + 1)/2$. -/
theorem level_div_two_add_one (D : TameDatum K L ξ) : level D.ξ₀ / 2 + 1 = (level D.ξ₀ + 1) / 2 := by
  obtain ⟨k, hk⟩ := D.odd
  omega

/-- On the elements of $U^{(n+1)/2}_{\mathfrak{A}}$ of determinant $1$ the character $\Lambda$ of a datum is $\psi_\alpha$. -/
theorem Λ_eq_psiAlphaFun (D : TameDatum K L ξ) {x : GL (Fin 2) K}
    (hx : x ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2))
    (hdet : Matrix.GeneralLinearGroup.det x = 1) (hJ : x ∈ D.J) :
    (D.Λ ⟨x, hJ⟩ : ℂ) = psiAlphaFun K D.ψ (Algebra.leftMulMatrix D.v D.α) x := by
  rw [D.mul, Units.val_mul, detChar, MonoidHom.comp_apply, hdet, map_one, Units.val_one, mul_one]
  rw [← D.level_div_two_add_one] at hx
  exact D.mem.1 ⟨x, hx⟩

/-- The character $\Lambda$ of a datum of level $n$ is trivial on the elements of $U^{n+1}_{\mathfrak{A}}$ of determinant $1$. -/
theorem Λ_eq_one_of_mem_unitsFilt (D : TameDatum K L ξ) {x : GL (Fin 2) K}
    (hx : x ∈ unitsFilt K D.A (level D.ξ₀ + 1)) (hdet : Matrix.GeneralLinearGroup.det x = 1)
    (hJ : x ∈ D.J) : D.Λ ⟨x, hJ⟩ = 1 := by
  apply Units.ext
  rw [D.Λ_eq_psiAlphaFun (unitsFilt_anti (by omega) hx) hdet hJ, Units.val_one]
  have h := (mem_unitsFilt_iff (by omega)).1 hx
  exact D.hψ.trivial _
    (by rw [neg_neg]; exact trace_mul_mem_ordBall_one (by push_cast; omega) D.hα h)

/-- **The intertwining condition on the target.** Let $g$ intertwine the character $\Lambda$ of a datum $D$ of level $n$ with the character $\Lambda'$ of a datum $D'$ of level $n'$. Let $U^{k_0}_{\mathfrak{A}'} \subseteq U^{n+1}_{\mathfrak{A}}$. Then $\psi_{\alpha'}(g x g^{-1}) = 1$ for each $x \in U^{k_0}_{\mathfrak{A}'}$ of determinant $1$ with $g x g^{-1} \in U^{(n'+1)/2}_{\mathfrak{A}'}$. -/
theorem psiAlphaFun_eq_one_of_intertwinesWith (D : TameDatum K L ξ) (D' : TameDatum K L' ξ')
    {g : GL (Fin 2) K} (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) {k₀ : ℕ}
    (hk : unitsFilt K D'.A k₀ ≤ unitsFilt K D.A (level D.ξ₀ + 1)) :
    ∀ x ∈ unitsFilt K D'.A k₀, Matrix.GeneralLinearGroup.det x = 1 →
      g * x * g⁻¹ ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2) →
        psiAlphaFun K D'.ψ (Algebra.leftMulMatrix D'.v D'.α) (g * x * g⁻¹) = 1 := by
  intro x hx hdet hx'
  have hxs := hk hx
  have hJ : x ∈ D.J := unitsFilt_le_jGroup D.hv _ (unitsFilt_anti (by omega) hxs)
  have hJ' : g * x * g⁻¹ ∈ D'.J := unitsFilt_le_jGroup D'.hv _ hx'
  have hdet' : Matrix.GeneralLinearGroup.det (g * x * g⁻¹) = 1 := by
    rw [map_mul, map_mul, hdet, mul_one, map_inv, mul_inv_cancel]
  have e : D'.Λ ⟨g * x * g⁻¹, hJ'⟩ = D.Λ ⟨x, hJ⟩ := hg ⟨x, hJ⟩ hJ'
  rw [← D'.Λ_eq_psiAlphaFun hx' hdet' hJ', e, D.Λ_eq_one_of_mem_unitsFilt hxs hdet hJ,
    Units.val_one]

/-- **Intertwining data of one chain order have the same level** (Bushnell and Henniart, 15.7). Let $D$ and $D'$ be data with the same chain order $\mathfrak{A}$. If $g$ intertwines $\Lambda$ with $\Lambda'$, then the levels agree and $g \in \mathfrak{K}_{\mathfrak{A}}$. -/
theorem level_eq_and_mem_normalizer_of_A_eq (D : TameDatum K L ξ) (D' : TameDatum K L' ξ')
    (hA : D'.A = D.A) {g : GL (Fin 2) K} (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) :
    level D'.ξ₀ = level D.ξ₀ ∧ g ∈ normalizer K D.A := by
  have h1 := D.one_le_level
  have h2 := D'.one_le_level
  by_cases hle : level D.ξ₀ ≤ level D'.ξ₀
  · obtain ⟨hk, hgN⟩ := eq_and_mem_normalizer_of_forall_psiAlphaFun D'.ψ D'.hψ D'.hv D'.minElt
      (m := (level D'.ξ₀ + 1) / 2) (k₀ := level D.ξ₀ + 1) (by omega) (by omega) (by omega)
      (by omega) (D.psiAlphaFun_eq_one_of_intertwinesWith D' hg (by rw [hA]))
    exact ⟨by omega, hA ▸ hgN⟩
  · obtain ⟨hk, -⟩ := eq_and_mem_normalizer_of_forall_psiAlphaFun D.ψ D.hψ D.hv D.minElt
      (m := (level D.ξ₀ + 1) / 2) (k₀ := level D'.ξ₀ + 1) (by omega) (by omega) (by omega)
      (by omega) (D'.psiAlphaFun_eq_one_of_intertwinesWith D hg.inv (by rw [hA]))
    omega

/-- The first border case. Let $D$ be a datum of level $n$ for the maximal order and $D'$ a datum of level $n' = 2n + 1$ for the Iwahori order. No $g \in \mathfrak{K}_{\mathfrak{J}}$ intertwines $\Lambda$ with $\Lambda'$. The test elements are $\begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$ with $c \in \mathfrak{p}^{n+1}_K$. -/
theorem false_of_maximal_iwahori_of_eq_two_mul_add_one (D : TameDatum K L ξ)
    (D' : TameDatum K L' ξ') (hA : D.A = maximal) (hA' : D'.A = iwahori) {g : GL (Fin 2) K}
    (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) (hn : level D'.ξ₀ = 2 * level D.ξ₀ + 1)
    (hgN : g ∈ normalizer K iwahori) : False := by
  have h1 := D.one_le_level
  have hY : Algebra.leftMulMatrix D.v D.α 0 1 ∈ ordBall K (-(level D.ξ₀ : ℤ)) := by
    have := D.hα 0 1
    rw [hA] at this
    exact mem_ordBall_congr (by simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]) this
  have key : (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      Algebra.leftMulMatrix D'.v D'.α * (g : Matrix (Fin 2) (Fin 2) K)) 0 1 ∈
        ordBall K (-(level D.ξ₀ : ℤ)) := by
    refine mem_ordBall_of_forall_psi_mul_eq D.hψ D'.hψ hY fun c hc => ?_
    have hx : lowerGL K c ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2) := by
      rw [hA]
      refine lowerGL_mem_unitsFilt_of_one_le (by omega) (ordBall_anti ?_ hc)
      simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
      omega
    have hx' : g * lowerGL K c * g⁻¹ ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2) := by
      rw [hA', hn]
      refine conj_mem_unitsFilt_of_mem_normalizer hgN (by omega)
        (lowerGL_mem_unitsFilt_of_one_le (by omega) (ordBall_anti ?_ hc))
      simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
      omega
    have hJ : lowerGL K c ∈ D.J := unitsFilt_le_jGroup D.hv _ hx
    have hJ' : g * lowerGL K c * g⁻¹ ∈ D'.J := unitsFilt_le_jGroup D'.hv _ hx'
    have hdet' : Matrix.GeneralLinearGroup.det (g * lowerGL K c * g⁻¹) = 1 := by
      rw [map_mul, map_mul, det_lowerGL, mul_one, map_inv, mul_inv_cancel]
    have e := congrArg Units.val (show D'.Λ ⟨g * lowerGL K c * g⁻¹, hJ'⟩ = D.Λ ⟨lowerGL K c, hJ⟩
      from hg ⟨_, hJ⟩ hJ')
    rw [D'.Λ_eq_psiAlphaFun hx' hdet' hJ', D.Λ_eq_psiAlphaFun hx (det_lowerGL c) hJ,
      psiAlphaFun_conj_eq_conj, psiAlphaFun_lowerGL, psiAlphaFun_lowerGL] at e
    exact e
  refine conj_apply_not_mem_ordBall D'.hv D'.minElt (hA' ▸ hgN) (by decide : (0 : Fin 2) ≠ 1) ?_
  rw [hA', hn]
  refine mem_ordBall_congr ?_ key
  simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
  omega

/-- The second border case. Let $D$ be a datum of level $n$ for the maximal order and $D'$ a datum of level $n' = 2n - 1$ for the Iwahori order. No $g$ with $g^{-1} \in \mathfrak{K}_{\mathfrak{M}}$ intertwines $\Lambda$ with $\Lambda'$. The test elements are $g^{-1} \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix} g$ with $c \in \mathfrak{p}^n_K$. -/
theorem false_of_maximal_iwahori_of_add_one_eq_two_mul (D : TameDatum K L ξ)
    (D' : TameDatum K L' ξ') (hA : D.A = maximal) (hA' : D'.A = iwahori) {g : GL (Fin 2) K}
    (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) (hn : level D'.ξ₀ + 1 = 2 * level D.ξ₀)
    (hgN : g⁻¹ ∈ normalizer K maximal) : False := by
  have h1 := D.one_le_level
  have hY : Algebra.leftMulMatrix D'.v D'.α 1 0 ∈ ordBall K (1 - (level D.ξ₀ : ℤ)) := by
    have := D'.hα 1 0
    rw [hA'] at this
    refine mem_ordBall_congr ?_ this
    simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
    omega
  have key : ((((g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      Algebra.leftMulMatrix D.v D.α * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 ∈
        ordBall K (1 - (level D.ξ₀ : ℤ)) := by
    refine mem_ordBall_of_forall_psi_mul_eq D'.hψ D.hψ hY fun c hc => ?_
    have hz : upperGL K c ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2) := by
      rw [hA', hn]
      refine upperGL_mem_unitsFilt_of_one_le (by omega) (ordBall_anti ?_ hc)
      simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
      omega
    have hx : g⁻¹ * upperGL K c * g⁻¹⁻¹ ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2) := by
      rw [hA]
      refine conj_mem_unitsFilt_of_mem_normalizer hgN (by omega)
        (upperGL_mem_unitsFilt_of_one_le (by omega) (ordBall_anti ?_ hc))
      simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]
      omega
    have hgx : g * (g⁻¹ * upperGL K c * g⁻¹⁻¹) * g⁻¹ = upperGL K c := by group
    have hx' : g * (g⁻¹ * upperGL K c * g⁻¹⁻¹) * g⁻¹ ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2) := by
      rw [hgx]
      exact hz
    have hJ : g⁻¹ * upperGL K c * g⁻¹⁻¹ ∈ D.J := unitsFilt_le_jGroup D.hv _ hx
    have hJ' : g * (g⁻¹ * upperGL K c * g⁻¹⁻¹) * g⁻¹ ∈ D'.J := unitsFilt_le_jGroup D'.hv _ hx'
    have hdet : Matrix.GeneralLinearGroup.det (g⁻¹ * upperGL K c * g⁻¹⁻¹) = 1 := by
      rw [map_mul, map_mul, det_upperGL, mul_one, inv_inv, map_inv, inv_mul_cancel]
    have hdet' : Matrix.GeneralLinearGroup.det (g * (g⁻¹ * upperGL K c * g⁻¹⁻¹) * g⁻¹) = 1 := by
      rw [hgx, det_upperGL]
    have e := congrArg Units.val (show D'.Λ ⟨_, hJ'⟩ = D.Λ ⟨_, hJ⟩ from hg ⟨_, hJ⟩ hJ')
    rw [D'.Λ_eq_psiAlphaFun hx' hdet' hJ', D.Λ_eq_psiAlphaFun hx hdet hJ, hgx,
      psiAlphaFun_conj_eq_conj, psiAlphaFun_upperGL, psiAlphaFun_upperGL] at e
    exact e.symm
  refine conj_apply_not_mem_ordBall D.hv D.minElt (hA ▸ hgN) (by decide : (1 : Fin 2) ≠ 0) ?_
  rw [hA]
  refine mem_ordBall_congr ?_ key
  simp [ChainOrder.bd, ChainOrder.wt, ChainOrder.e]

/-- **No intertwining between the two chain orders** (Bushnell and Henniart, 15.7). Let $D$ be a datum for the maximal order and $D'$ a datum for the Iwahori order. No $g \in GL_2(K)$ intertwines $\Lambda$ with $\Lambda'$. -/
theorem false_of_maximal_iwahori (D : TameDatum K L ξ) (D' : TameDatum K L' ξ')
    (hA : D.A = maximal) (hA' : D'.A = iwahori) {g : GL (Fin 2) K}
    (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) : False := by
  have h1 := D.one_le_level
  obtain ⟨k', hk'⟩ := D'.odd
  by_cases hle : 2 * level D.ξ₀ + 1 ≤ level D'.ξ₀
  · have hinc : unitsFilt K D'.A (2 * (level D.ξ₀ + 1)) ≤ unitsFilt K D.A (level D.ξ₀ + 1) := by
      rw [hA, hA']
      exact unitsFilt_iwahori_le_maximal (by omega)
    obtain ⟨hk, hgN⟩ := eq_and_mem_normalizer_of_forall_psiAlphaFun D'.ψ D'.hψ D'.hv D'.minElt
      (m := (level D'.ξ₀ + 1) / 2) (by omega) (by omega) (by omega) (by omega)
      (D.psiAlphaFun_eq_one_of_intertwinesWith D' hg hinc)
    exact D.false_of_maximal_iwahori_of_eq_two_mul_add_one D' hA hA' hg (by omega) (hA' ▸ hgN)
  · have hinc : unitsFilt K D.A (k' + 2) ≤ unitsFilt K D'.A (level D'.ξ₀ + 1) := by
      rw [hA, hA']
      exact (unitsFilt_maximal_le_iwahori (k' + 1)).trans (unitsFilt_anti (by omega))
    obtain ⟨hk, hgN⟩ := eq_and_mem_normalizer_of_forall_psiAlphaFun D.ψ D.hψ D.hv D.minElt
      (m := (level D.ξ₀ + 1) / 2) (by omega) (by omega) (by omega) (by omega)
      (D'.psiAlphaFun_eq_one_of_intertwinesWith D hg.inv hinc)
    exact D.false_of_maximal_iwahori_of_add_one_eq_two_mul D' hA hA' hg (by omega) (hA ▸ hgN)

/-- **Intertwining data have the same chain order, the same level, and the intertwining element normalizes the chain order** (Bushnell and Henniart, 15.7). If $g \in GL_2(K)$ intertwines the character $\Lambda$ of a datum $D$ with the character $\Lambda'$ of a datum $D'$, then $\mathfrak{A}' = \mathfrak{A}$, the levels agree and $g \in \mathfrak{K}_{\mathfrak{A}}$. -/
theorem A_eq_and_level_eq_of_intertwinesWith (D : TameDatum K L ξ) (D' : TameDatum K L' ξ')
    {g : GL (Fin 2) K} (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) :
    D'.A = D.A ∧ level D'.ξ₀ = level D.ξ₀ ∧ g ∈ normalizer K D.A := by
  cases hA : D.A <;> cases hA' : D'.A
  · obtain ⟨h1, h2⟩ := D.level_eq_and_mem_normalizer_of_A_eq D' (hA'.trans hA.symm) hg
    rw [hA] at h2
    exact ⟨rfl, h1, h2⟩
  · exact (D.false_of_maximal_iwahori D' hA hA' hg).elim
  · exact (D'.false_of_maximal_iwahori D hA' hA hg.inv).elim
  · obtain ⟨h1, h2⟩ := D.level_eq_and_mem_normalizer_of_A_eq D' (hA'.trans hA.symm) hg
    rw [hA] at h2
    exact ⟨rfl, h1, h2⟩

end TameDatum

end Datum

section Reduction

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Intertwining types in the normalizer come from isomorphic pairs** (Bushnell and Henniart, 15.7 and 20.2). Let $p \ne 2$. Let $D$ be a datum for $(L/K, \xi)$ and $D'$ a datum for $(L'/K, \xi')$ with the same chain order $\mathfrak{A}$ and the same level. If some $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\Lambda$ with $\Lambda'$, then the pairs are $K$-isomorphic. This is the part of `Langlands.LocalGL2.TypeIntertwiningIso` that this file does not prove. -/
def TypeIntertwiningNormalizerIso : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    (g : GL (Fin 2) K), D'.A = D.A → level D'.ξ₀ = level D.ξ₀ → g ∈ normalizer K D.A →
      IntertwinesWith D.J D'.J D.Λ D'.Λ g → P.Iso Q

/-- **The reduction to the normalizer.** `Langlands.LocalGL2.TypeIntertwiningIso K` is equivalent to `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K`, because an intertwining element forces the same chain order, the same level and the normalizer. -/
theorem typeIntertwiningIso_iff_typeIntertwiningNormalizerIso :
    TypeIntertwiningIso K ↔ TypeIntertwiningNormalizerIso K := by
  constructor
  · intro h h2 P Q D D' g _ _ _ hg
    exact h h2 P Q D D' g hg
  · intro h h2 P Q D D' g hg
    obtain ⟨hA, hl, hgN⟩ := D.A_eq_and_level_eq_of_intertwinesWith D' hg
    exact h h2 P Q D D' g hA hl hgN hg

variable {K} in
/-- **Isomorphic type representations come from isomorphic pairs**, if `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K` holds. -/
theorem typeRepInjective_of_typeIntertwiningNormalizerIso (h : TypeIntertwiningNormalizerIso K) :
    TypeRepInjective K :=
  typeRepInjective_of_typeIntertwiningIso
    ((typeIntertwiningIso_iff_typeIntertwiningNormalizerIso K).2 h)

end Reduction

end Langlands.LocalGL2
