/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.TypeIndependent

/-!
# The type characters agree on the units

This file proves `Langlands.LocalGL2.TypeCharUnitsAgree K` for each non-archimedean local field $K$, and so `Langlands.LocalGL2.TypeRepIndependent K` (Bushnell and Henniart, 15.6 and §19). Let $D$ and $D'$ be two data for one tame admissible pair $(L/K, \xi)$ with the same chain order $\mathfrak{A}$ and the same basis. The claim is that $\Lambda$ and $\Lambda'$ agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$, when $p \ne 2$.

The proof does not compare $\psi$ with $\psi'$, $\alpha$ with $\alpha'$ or $\chi$ with $\chi'$. It uses only three facts about the quotient $\theta = \Lambda' \Lambda^{-1}$ on $J = L^\times U^m_{\mathfrak{A}}$: $\theta$ is trivial on $L^\times$, $\theta$ is trivial on $U^N_{\mathfrak{A}}$ for some $N$, and $\theta$ takes values in a commutative group.

## Main definitions

This file has no new definitions.

## Main results

* `Langlands.LocalGL2.exists_embGL_eq_of_commute`: an element of $GL_2(K)$ that commutes with the matrix of $y \in L \setminus K$ is in $L^\times$.
* `Langlands.LocalGL2.unitsFilt_le_of_two_mul_le`: one step of the descent from $U^{2j}_{\mathfrak{A}}$ to $U^j_{\mathfrak{A}}$.
* `Langlands.LocalGL2.unitsFilt_le_of_commutator_mem`: for $p \ne 2$, a subgroup of $GL_2(F)$ that contains $E^\times$, the commutators of $E^\times$ with $U^m_{\mathfrak{A}}$ and some $U^N_{\mathfrak{A}}$ contains $U^m_{\mathfrak{A}}$.
* `Langlands.LocalGL2.TameDatum.exists_Λ_eq_one`: the character $\Lambda$ of a datum is trivial on some $U^N_{\mathfrak{A}}$.
* `Langlands.LocalGL2.typeCharUnitsAgree`: the statement `Langlands.LocalGL2.TypeCharUnitsAgree K`.
* `Langlands.LocalGL2.typeRepIndependent`: the statement `Langlands.LocalGL2.TypeRepIndependent K`.

## Proof

Let $H$ be the kernel of $\theta$, as a subgroup of $GL_2(K)$. It contains $L^\times$, because $\Lambda$ and $\Lambda'$ both equal $\xi$ on $L^\times$. It contains each commutator of $J$, because $\mathbb{C}^\times$ is commutative. It contains $U^N_{\mathfrak{A}}$ for a large $N$, because $\psi_\alpha$ is trivial on $U^{n+1}_{\mathfrak{A}}$ and $\det$ maps $U^{2k}_{\mathfrak{A}}$ into $U^k_K$.

The descent shows that $U^{2j}_{\mathfrak{A}} \le H$ implies $U^j_{\mathfrak{A}} \le H$ for $j \ge m$. Since $p \ne 2$, there is $y \in L \setminus K$ with $y^2 \in K$. Let $g$ be the image of $y$. Then $g^2$ is central. Let $u \in U^j_{\mathfrak{A}}$. The average $p = (u + g u g^{-1}) / 2$ is in $U^j_{\mathfrak{A}}$ and commutes with $g$, so $p \in L^\times$ and $p \in H$. The element $w = p^{-1} u$ satisfies $w + g w g^{-1} = 2$. Let $h = 1 + (w - 1)/2$. Then $g h g^{-1} = 1 - (w - 1)/2$ commutes with $h$, so $h \cdot g h g^{-1}$ commutes with $g$ and is in $H$. Thus $h^2 \in H$, since $h^2$ differs from $h \cdot g h g^{-1}$ by a commutator. Finally $h^{-2} w - 1 = -h^{-2} ((w - 1)/2)^2$ is in $\mathfrak{P}^{2j}_{\mathfrak{A}}$, so $u = p \, h^2 \, (h^{-2} w)$ is in $H$. Start at $U^{2^N m}_{\mathfrak{A}} \le U^N_{\mathfrak{A}}$ and apply the step $N$ times.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§15 and 19.
-/

namespace Langlands.LocalGL2

universe u v

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section Lattice

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- For $k \ge 0$, each entry bound of $\mathfrak{P}^{2k}_{\mathfrak{A}}$ is at least $k$. -/
theorem ChainOrder.le_bd_two_mul (A : ChainOrder) {k : ℤ} (hk : 0 ≤ k) (i j : Fin 2) :
    k ≤ A.bd (2 * k) i j := by
  cases A <;> fin_cases i <;> fin_cases j <;> simp [bd, wt, e] <;> omega

/-- If $X - 1 \in \mathfrak{P}^{2k}_{\mathfrak{A}}$, then $\det X - 1 \in \mathfrak{p}^k_F$. -/
theorem det_sub_one_mem_ordBall_of_two_mul {A : ChainOrder} {k : ℤ} (hk : 0 ≤ k)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X - 1 ∈ radPow F A (2 * k)) : X.det - 1 ∈ ordBall F k := by
  set Z := X - 1 with hZ
  have hXZ : X = 1 + Z := by rw [hZ]; abel
  have hd : X.det - 1 = Z 0 0 + Z 1 1 + Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 := by
    rw [hXZ, Matrix.det_fin_two]
    simp
    ring
  have hb : ∀ i j, Z i j ∈ ordBall F k := fun i j => ordBall_anti (A.le_bd_two_mul hk i j) (hX i j)
  have hkk : k ≤ k + k := by omega
  rw [hd, sub_eq_add_neg]
  exact add_mem_ordBall (add_mem_ordBall (add_mem_ordBall (hb 0 0) (hb 1 1))
    (ordBall_anti hkk (mul_mem_ordBall_add (hb 0 0) (hb 1 1))))
    (neg_mem_ordBall (ordBall_anti hkk (mul_mem_ordBall_add (hb 0 1) (hb 1 0))))

/-- If $g \in U^{2k}_{\mathfrak{A}}$ with $k \ge 1$, then $\det g \in U^k_F$. -/
theorem det_mem_unitFilt_of_two_mul {A : ChainOrder} {k : ℕ} (hk : 1 ≤ k) {g : GL (Fin 2) F}
    (hg : g ∈ unitsFilt F A (2 * k)) : Matrix.GeneralLinearGroup.det g ∈ unitFilt F k := by
  have h1 := (mem_unitsFilt_iff (by omega)).1 hg
  have h2 : (g : Matrix (Fin 2) (Fin 2) F).det - 1 ∈ ordBall F k :=
    det_sub_one_mem_ordBall_of_two_mul (by omega) (by exact_mod_cast h1)
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact (sub_one_mem_ordBall_one (ordBall_anti (by exact_mod_cast hk) h2)).2
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact h2

end Lattice

section Conj

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- If $2 \ne 0$ in $F$, then the quadratic extension $E$ has an element $y \notin F$ with $y^2 \in F$: take $y = z - \sigma(z)$ for $z \notin F$. -/
theorem exists_not_mem_range_mul_self_mem_range (h2 : (2 : F) ≠ 0) :
    ∃ y : E, y ∉ Set.range (algebraMap F E) ∧ y * y ∈ Set.range (algebraMap F E) := by
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero_iff _ (algebraMap F E).injective).2 h2
  obtain ⟨z, hz⟩ : ∃ z : E, galConj F E z ≠ z := by
    by_contra hc
    push Not at hc
    exact galConj_ne_one F E (AlgEquiv.ext hc)
  set y := z - galConj F E z with hy
  have hσ : galConj F E y = -y := by
    rw [hy, map_sub, galConj_galConj]
    ring
  have hy0 : y ≠ 0 := by
    rw [hy, sub_ne_zero]
    exact fun h => hz h.symm
  refine ⟨y, fun ⟨c, hc⟩ => ?_, ?_⟩
  · have h := hσ
    rw [← hc, AlgEquiv.commutes, hc] at h
    have : (2 : E) * y = 0 := by linear_combination h
    exact hy0 ((mul_eq_zero.1 this).resolve_left h2E)
  · rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    rcases eq_one_or_eq_galConj F E τ with rfl | rfl
    · rfl
    · rw [map_mul, hσ, neg_mul_neg]

end Conj

section Descent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]
variable {A : ChainOrder} {v : Module.Basis (Fin 2) F E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- If $y \in E \setminus F$ and $q \in GL_2(F)$ commutes with the matrix of $y$, then $q$ is the image of an element of $E^\times$. -/
theorem exists_embGL_eq_of_commute {y : E} (hy : y ∉ Set.range (algebraMap F E)) {q : GL (Fin 2) F}
    (hq : Algebra.leftMulMatrix v y * (q : Matrix (Fin 2) (Fin 2) F) =
      (q : Matrix (Fin 2) (Fin 2) F) * Algebra.leftMulMatrix v y) :
    ∃ e : Eˣ, q = embGL v e := by
  have hX : adjointMap F (Algebra.leftMulMatrix v y) (q : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [adjointMap_apply, hq, sub_self]
  have h := eq_leftMulMatrix_of_adjointMap_eq_zero v hy hX
  have he : act v (q : Matrix (Fin 2) (Fin 2) F) 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    have h1 := q.mul_inv
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  exact ⟨Units.mk0 _ he, Units.ext h⟩

variable [Algebra.IsSeparable F E]

/-- **One step of the descent.** Let $p \ne 2$, and let $H \le GL_2(F)$ be a subgroup that contains $E^\times$ and the commutators $y b y^{-1} b^{-1}$ for $y \in E^\times$ and $b \in U^m_{\mathfrak{A}}$. If $1 \le j$, $m \le j$ and $U^{2j}_{\mathfrak{A}} \le H$, then $U^j_{\mathfrak{A}} \le H$. -/
theorem unitsFilt_le_of_two_mul_le (hv : IsAdapted A v) (h2 : (2 : 𝓀[F]) ≠ 0)
    {H : Subgroup (GL (Fin 2) F)} (hE : ∀ y : Eˣ, embGL v y ∈ H) {m : ℕ}
    (hc : ∀ y : Eˣ, ∀ b ∈ unitsFilt F A m, embGL v y * b * (embGL v y)⁻¹ * b⁻¹ ∈ H)
    {j : ℕ} (hj : 1 ≤ j) (hjm : m ≤ j) (h2j : unitsFilt F A (2 * j) ≤ H) :
    unitsFilt F A j ≤ H := by
  intro u hu
  have h20 : (2 : F) ≠ 0 := two_ne_zero_of_residue h2
  have h2o : (2 : F)⁻¹ ∈ ordBall F 0 :=
    mem_ordBall_of_le (inv_ne_zero h20) (by rw [ord_inv h20, ord_two_eq_zero h2, neg_zero])
  obtain ⟨y, hyF, c, hc'⟩ := exists_not_mem_range_mul_self_mem_range (E := E) h20
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyF ⟨0, map_zero _⟩
  obtain ⟨g, hg⟩ : ∃ g, g = embGL v (Units.mk0 y hy0) := ⟨_, rfl⟩
  have hG : (g : Matrix (Fin 2) (Fin 2) F) = Algebra.leftMulMatrix v y := by rw [hg]; rfl
  -- The square of `g` is a scalar matrix, so it is central.
  have hC : ∀ Y : Matrix (Fin 2) (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) * g * Y = Y * (g * g) := by
    intro Y
    rw [hG, ← map_mul, ← hc', AlgHom.commutes, Algebra.commutes]
  have hCG : ∀ x : GL (Fin 2) F, g * g * x = x * (g * g) := fun x =>
    Units.ext (by simp only [Units.val_mul]; exact hC x)
  -- An element that commutes with `g` is in `E^×`, so it is in `H`.
  have hcomm : ∀ q : GL (Fin 2) F, g * q = q * g → q ∈ H := by
    intro q hq
    have hq' := congrArg Units.val hq
    rw [Units.val_mul, Units.val_mul, hG] at hq'
    obtain ⟨e, rfl⟩ := exists_embGL_eq_of_commute hyF hq'
    exact hE e
  -- The average `p` of `u` and `g u g⁻¹` commutes with `g`.
  obtain ⟨u', hu'e⟩ : ∃ u', u' = g * u * g⁻¹ := ⟨_, rfl⟩
  have hu' : u' ∈ unitsFilt F A j := hu'e ▸ hg ▸ hv.conj_mem_unitsFilt _ hu
  have hUU' : (g : Matrix (Fin 2) (Fin 2) F) * u' = u * g := by
    rw [hu'e, Units.val_mul, Units.val_mul]
    simp only [← mul_assoc]
    rw [hC]
    simp only [mul_assoc, Units.mul_inv, mul_one]
  have hU'U : (u' : Matrix (Fin 2) (Fin 2) F) * g = g * u := by
    rw [hu'e, Units.val_mul, Units.val_mul]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have hX : (2 : F)⁻¹ • ((u : Matrix (Fin 2) (Fin 2) F) + u') - 1 ∈ radPow F A j := by
    have e : (2 : F)⁻¹ • ((u : Matrix (Fin 2) (Fin 2) F) + u') - 1 =
        (2 : F)⁻¹ • (((u : Matrix (Fin 2) (Fin 2) F) - 1) + ((u' : Matrix (Fin 2) (Fin 2) F) - 1)) := by
      rw [show ((u : Matrix (Fin 2) (Fin 2) F) - 1) + ((u' : Matrix (Fin 2) (Fin 2) F) - 1) =
        ((u : Matrix (Fin 2) (Fin 2) F) + u') - (2 : F) • 1 by rw [two_smul]; abel,
        smul_sub, smul_smul, inv_mul_cancel₀ h20, one_smul]
    rw [e]
    have := smul_mem_radPow h2o (add_mem hu.2.2 hu'.2.2)
    rwa [mul_zero, add_zero] at this
  obtain ⟨p, hp, hpM⟩ := exists_unitsFilt_eq_one_add hj hX
  have hpM' : (p : Matrix (Fin 2) (Fin 2) F) = (2 : F)⁻¹ • ((u : Matrix (Fin 2) (Fin 2) F) + u') := by
    rw [hpM]
    abel
  have hgp : g * p = p * g := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hpM', Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul,
      hUU', hU'U, add_comm])
  have hpH : p ∈ H := hcomm p hgp
  -- The element `w = p⁻¹ u` satisfies `w + g w g⁻¹ = 2`.
  obtain ⟨w, hwe⟩ : ∃ w, w = p⁻¹ * u := ⟨_, rfl⟩
  have hw : w ∈ unitsFilt F A j := hwe ▸ (unitsFilt F A j).mul_mem ((unitsFilt F A j).inv_mem hp) hu
  have hgpi : g * p⁻¹ = p⁻¹ * g := Commute.inv_right hgp
  have hw' : g * w * g⁻¹ = p⁻¹ * u' := by
    rw [hwe, hu'e, ← mul_assoc g, hgpi]
    group
  have hS : (u : Matrix (Fin 2) (Fin 2) F) + u' = (2 : F) • (p : Matrix (Fin 2) (Fin 2) F) := by
    rw [hpM', smul_smul, mul_inv_cancel₀ h20, one_smul]
  have hWc : (g : Matrix (Fin 2) (Fin 2) F) * w * (g⁻¹ : GL (Fin 2) F) =
      (2 : F) • 1 - (w : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hw', eq_sub_iff_add_eq, hwe, Units.val_mul, Units.val_mul,
      ← mul_add, add_comm, hS, Matrix.mul_smul, Units.inv_mul]
  -- The element `h = 1 + (w - 1) / 2` satisfies `g h g⁻¹ = 1 - (w - 1) / 2`.
  obtain ⟨V, hVe⟩ : ∃ V, V = (2 : F)⁻¹ • ((w : Matrix (Fin 2) (Fin 2) F) - 1) := ⟨_, rfl⟩
  have hV : V ∈ radPow F A j := by
    have := smul_mem_radPow h2o hw.2.2
    rwa [mul_zero, add_zero, ← hVe] at this
  obtain ⟨h, hh, hhM⟩ := exists_unitsFilt_eq_one_add hj hV
  have hgV : (g : Matrix (Fin 2) (Fin 2) F) * V * (g⁻¹ : GL (Fin 2) F) = -V := by
    rw [hVe, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one, Units.mul_inv, hWc,
      show (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) - w - 1 = -((w : Matrix (Fin 2) (Fin 2) F) - 1) by
        rw [two_smul]; abel, smul_neg]
  obtain ⟨t, hte⟩ : ∃ t, t = g * h * g⁻¹ := ⟨_, rfl⟩
  have htM : (t : Matrix (Fin 2) (Fin 2) F) = 1 - V := by
    rw [hte, Units.val_mul, Units.val_mul, hhM, mul_add, mul_one, add_mul, Units.mul_inv, hgV,
      sub_eq_add_neg]
  have hth : t * h = h * t := Units.ext (by
    rw [Units.val_mul, Units.val_mul, htM, hhM]
    noncomm_ring)
  -- So `h t` commutes with `g`, and `h h` is in `H`.
  have hhtH : h * t ∈ H := by
    apply hcomm
    have e1 : g * (h * t) = t * (g * g * h * g⁻¹ * g⁻¹) * g := by
      rw [hte]
      group
    have e2 : g * g * h * g⁻¹ * g⁻¹ = h := by
      rw [hCG h]
      group
    rw [e1, e2, hth]
  have hhH : h * h ∈ H := by
    have hb : h⁻¹ ∈ unitsFilt F A m := unitsFilt_anti hjm ((unitsFilt F A j).inv_mem hh)
    have e : h * h = h * t * (embGL v (Units.mk0 y hy0) * h⁻¹ * (embGL v (Units.mk0 y hy0))⁻¹ * h⁻¹⁻¹) := by
      rw [← hg, hte]
      group
    rw [e]
    exact H.mul_mem hhtH (hc _ _ hb)
  -- The rest `r = h⁻¹ h⁻¹ w` is in `U^{2j}`.
  have hr : h⁻¹ * h⁻¹ * w ∈ unitsFilt F A (2 * j) := by
    rw [mem_unitsFilt_iff (by omega)]
    have hW : (w : Matrix (Fin 2) (Fin 2) F) = 1 + (2 : F) • V := by
      rw [hVe, smul_smul, mul_inv_cancel₀ h20, one_smul]
      abel
    have hHi : ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (1 + V) = 1 := by
      rw [← hhM, Units.inv_mul]
    have e : ((h⁻¹ * h⁻¹ * w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
        -(((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (h⁻¹ : GL (Fin 2) F) * (V * V)) := by
      have e1 : ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (h⁻¹ : GL (Fin 2) F) *
          ((1 + V) * (1 + V)) = 1 := by
        rw [mul_assoc, ← mul_assoc _ (1 + V), hHi, one_mul, hHi]
      rw [Units.val_mul, Units.val_mul]
      conv_lhs => rw [← e1, ← mul_sub, hW, two_smul]
      rw [← mul_neg]
      congr 1
      noncomm_ring
    rw [e]
    have hi0 : ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ radPow F A 0 := hh.2.1
    have := neg_mem (mul_mem_radPow (mul_mem_radPow hi0 hi0) (mul_mem_radPow hV hV))
    convert this using 2
    push_cast
    ring
  have e : u = p * (h * h) * (h⁻¹ * h⁻¹ * w) := by
    rw [hwe]
    group
  rw [e]
  exact H.mul_mem (H.mul_mem hpH hhH) (h2j hr)

/-- **The descent.** Let $p \ne 2$ and $m \ge 1$. Let $H \le GL_2(F)$ be a subgroup that contains $E^\times$, the commutators $y b y^{-1} b^{-1}$ for $y \in E^\times$ and $b \in U^m_{\mathfrak{A}}$, and the group $U^N_{\mathfrak{A}}$ for some $N$. Then $U^m_{\mathfrak{A}} \le H$. -/
theorem unitsFilt_le_of_commutator_mem (hv : IsAdapted A v) (h2 : (2 : 𝓀[F]) ≠ 0)
    {H : Subgroup (GL (Fin 2) F)} (hE : ∀ y : Eˣ, embGL v y ∈ H) {m : ℕ} (hm : 1 ≤ m)
    (hc : ∀ y : Eˣ, ∀ b ∈ unitsFilt F A m, embGL v y * b * (embGL v y)⁻¹ * b⁻¹ ∈ H)
    {N : ℕ} (hN : unitsFilt F A N ≤ H) : unitsFilt F A m ≤ H := by
  have key : ∀ i, unitsFilt F A (2 ^ (N - i) * m) ≤ H := by
    intro i
    induction i with
    | zero =>
      refine le_trans (unitsFilt_anti ?_) hN
      have := Nat.lt_two_pow_self (n := N)
      rw [Nat.sub_zero]
      nlinarith
    | succ i ih =>
      by_cases hi : i < N
      · have e : N - i = (N - (i + 1)) + 1 := by omega
        rw [e, pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, mul_comm _ 2] at ih
        refine unitsFilt_le_of_two_mul_le hv h2 hE hc ?_ ?_ ih
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega))
        · exact Nat.le_mul_of_pos_left m (pow_pos two_pos _)
      · have e : N - (i + 1) = N - i := by omega
        rwa [e]
  simpa using key N

end Descent

section Datum

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  {ξ : Lˣ →* ℂˣ}

/-- The character $\Lambda = \psi_\alpha \cdot (\chi \circ \det)$ of a datum is trivial on $U^N_{\mathfrak{A}}$ for some $N$: take $N \ge n + 1$ for $\psi_\alpha$, and $N \ge 2k$ with $U^k_K$ in the kernel of $\chi$. -/
theorem exists_Λ_eq_one (D : TameDatum K L ξ) :
    ∃ N : ℕ, ∀ u : GL (Fin 2) K, u ∈ unitsFilt K D.A N → ∀ hJ : u ∈ D.J, D.Λ ⟨u, hJ⟩ = 1 := by
  obtain ⟨k, hk⟩ := (isSmoothChar_iff_exists_unitFilt_le D.χ).1 D.smooth
  refine ⟨max (level D.ξ₀ + 1) (2 * max k 1), fun u hu hJ => ?_⟩
  have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega)
      D.Λ₀ := D.mem
  have hu1 : u ∈ unitsFilt K D.A (level D.ξ₀ + 1) := unitsFilt_anti (le_max_left _ _) hu
  have hu2 : u ∈ unitsFilt K D.A (level D.ξ₀ / 2 + 1) := unitsFilt_anti (by omega) hu1
  have h0 : D.Λ₀ ⟨u, hJ⟩ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact (hmem.1 ⟨u, hu2⟩).trans (psiAlpha_eq_one _ _ _ _ _ _ ⟨u, hu2⟩ hu1)
  have hd : Matrix.GeneralLinearGroup.det u ∈ unitFilt K (max k 1) :=
    det_mem_unitFilt_of_two_mul (le_max_right _ _) (unitsFilt_anti (le_max_right _ _) hu)
  have h1 : detChar K 2 D.χ u = 1 := hk (unitFilt_anti (le_max_left _ _) hd)
  rw [D.mul, h0, h1, one_mul]

end TameDatum

variable (K) in
/-- **The type characters agree on $U^m_{\mathfrak{A}}$** (Bushnell and Henniart, §15 and §19). This is `Langlands.LocalGL2.TypeCharUnitsAgree K`: for $p \ne 2$ and two data of one pair with the same chain order and the same basis, the characters $\Lambda$ and $\Lambda'$ agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$. -/
theorem typeCharUnitsAgree : TypeCharUnitsAgree K := by
  intro h2 P D D' hA hv u hu hu'
  have hl := D.level_eq D'
  have hJ : D.J ≤ D'.J := by
    intro x hx
    rw [mem_jGroup] at hx ⊢
    rw [hA, hv, hl]
    exact hx
  -- The quotient `θ = Λ' Λ⁻¹` on `J`, and its kernel `H` in `GL_2(K)`.
  let θ : D.J →* ℂˣ := D'.Λ.comp (Subgroup.inclusion hJ) * D.Λ⁻¹
  let H : Subgroup (GL (Fin 2) K) := θ.ker.map D.J.subtype
  have hmemH : ∀ x (hx : x ∈ D.J), θ ⟨x, hx⟩ = 1 → x ∈ H := fun x hx h => ⟨⟨x, hx⟩, h, rfl⟩
  have hE : ∀ y, embGL D.v y ∈ H := by
    intro y
    apply hmemH _ (embGL_mem_jGroup D.hv _ y)
    simp only [θ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply]
    have e : (Subgroup.inclusion hJ ⟨embGL D.v y, embGL_mem_jGroup D.hv _ y⟩ : D'.J) =
        ⟨embGL D'.v y, embGL_mem_jGroup D'.hv _ y⟩ := Subtype.ext (by change embGL D.v y = embGL D'.v y; rw [hv])
    rw [e, D'.Λ_embGL, D.Λ_embGL, mul_inv_cancel]
  have hc : ∀ y : P.Lˣ, ∀ b ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2),
      embGL D.v y * b * (embGL D.v y)⁻¹ * b⁻¹ ∈ H := by
    intro y b hb
    have hg := embGL_mem_jGroup D.hv ((level D.ξ₀ + 1) / 2) y
    have hbJ := unitsFilt_le_jGroup D.hv _ hb
    let a : D.J := ⟨embGL D.v y, hg⟩
    let c : D.J := ⟨b, hbJ⟩
    have hk : a * c * a⁻¹ * c⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul, mul_comm]
    have e : embGL D.v y * b * (embGL D.v y)⁻¹ * b⁻¹ = D.J.subtype (a * c * a⁻¹ * c⁻¹) := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype, a, c]
    rw [e]
    exact Subgroup.mem_map_of_mem _ hk
  obtain ⟨N₁, hN₁⟩ := D.exists_Λ_eq_one
  obtain ⟨N₂, hN₂⟩ := D'.exists_Λ_eq_one
  have hN : unitsFilt K D.A (max (max N₁ N₂) ((level D.ξ₀ + 1) / 2)) ≤ H := by
    intro x hx
    have hxJ := unitsFilt_le_jGroup D.hv _ (unitsFilt_anti (le_max_right _ _) hx)
    apply hmemH x hxJ
    simp only [θ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply]
    have e : (Subgroup.inclusion hJ ⟨x, hxJ⟩ : D'.J) = ⟨x, hJ hxJ⟩ := rfl
    have hx₂ : x ∈ unitsFilt K D'.A N₂ := by
      rw [hA]
      exact unitsFilt_anti (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    rw [e, hN₁ x (unitsFilt_anti (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hxJ,
      hN₂ x hx₂ (hJ hxJ), inv_one, mul_one]
  have hm1 : 1 ≤ (level D.ξ₀ + 1) / 2 := by
    have := D.one_le_level
    omega
  obtain ⟨⟨x, hx⟩, hθ, rfl⟩ := unitsFilt_le_of_commutator_mem D.hv h2 hE hm1 hc hN hu
  replace hθ : θ ⟨x, hx⟩ = 1 := hθ
  simp only [θ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
    mul_inv_eq_one] at hθ
  exact hθ

/-- **The type representation does not depend on the choices** (Bushnell and Henniart, 15.6 and §19). For $p \ne 2$ and $K$-isomorphic tame admissible pairs, the representations $c\text{-}\mathrm{Ind}_{J_\alpha}^{GL_2(K)} \Lambda$ of any two data are isomorphic. -/
theorem typeRepIndependent : TypeRepIndependent K :=
  typeRepIndependent_of_typeCharUnitsAgree (typeCharUnitsAgree K)

end Datum

end Langlands.LocalGL2
