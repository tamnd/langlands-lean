/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.Module.Cardinality
import Langlands.Tate.HeckeTrivial

/-!
# The L-functions of class group characters

Let $K$ be a number field with discriminant $d_K$, different $\mathfrak{d}$ and class group $\mathrm{Cl}_K$. Let $\psi : \mathrm{Cl}_K \to \mathbb{C}^\times$ be a character. This file proves the analytic continuation and the functional equation of the $L$-function $$L(u, \psi) = \sum_{I \neq 0} \psi([I]) N(I)^{-u}, \qquad \mathrm{Re}\, u > 1,$$ with the method of Hecke. These are the Hecke $L$-functions of the characters of the idele class group that are unramified at all places and trivial on the connected component of the infinite part. For $\psi = 1$ the function $L(u, \psi)$ is the Dedekind zeta function.

Let $\psi_{\mathfrak{a}}$ be the function of `Langlands/Tate/DedekindFE.lean`, choose an ideal $\mathfrak{a}_C$ in each class $C$ and put $$\xi(u, \psi) = c_K \sum_C \psi(C^{-1}) \psi_{\mathfrak{a}_C}(u), \qquad c_K = \frac{2^{r - r_2} n R_K}{w_K}.$$

## Main definitions

* `Langlands.Tate.classCharL`: the $L$-series $L(u, \psi)$.
* `Langlands.Tate.classCharXi`: the completed function $\xi(u, \psi)$.
* `Langlands.Tate.classCharLambda`: the entire continuation of $\xi(u, \psi)$ for $\psi \neq 1$.

## Main results

* `Langlands.Tate.classCharXi_eq`: $\xi(u, \psi) = |d_K|^{u/2} \Gamma_K(u) L(u, \psi)$ for $\mathrm{Re}\, u > 1$.
* `Langlands.Tate.classCharXi_one`: $\xi(u, 1)$ is the completed Dedekind zeta function.
* `Langlands.Tate.classCharXi_one_sub`: the functional equation $\xi(1 - u, \psi) = \psi([\mathfrak{d}]) \xi(u, \psi^{-1})$ for $u \neq 0, 1$.
* `Langlands.Tate.differentiable_classCharLambda`, `Langlands.Tate.classCharLambda_eq`: for $\psi \neq 1$ the function $\xi(u, \psi)$ extends to an entire function.
* `Langlands.Tate.classCharLambda_one_sub`: the functional equation of the entire function, at all $u$.

## Proof

The functional equation of $\psi_{\mathfrak{a}}$ is $\psi_{\mathfrak{a}}(1 - u) = \psi_{\mathfrak{a}^\vee}(u)$, and the class of $\mathfrak{a}_C^\vee$ is $D = (C [\mathfrak{d}])^{-1}$. Then $\psi(C^{-1}) = \psi([\mathfrak{d}]) \psi^{-1}(D^{-1})$, and the sum over $D$ gives the functional equation. The file `Langlands/Tate/HeckeTrivial.lean` writes each $\psi_{\mathfrak{a}}$ in the form $E(u) + F_0(u)/u + F_1(u)/(u - 1)$. The residues of $\psi_{\mathfrak{a}}$ do not depend on $\mathfrak{a}$, so the residues of $\xi(u, \psi)$ are multiples of $\sum_C \psi(C)$. This sum is $0$ for $\psi \neq 1$, so the poles cancel.

## References

* E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen, Math. Z. 1 (1918).
* J. Neukirch, Algebraic number theory, chapter VII, section 8.
-/

namespace Langlands.Tate

open Filter Topology Module NumberField NumberField.InfinitePlace NumberField.Units

open scoped Classical nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

section Series

/-- The $L$-series $L(u, \psi) = \sum_{I \neq 0} \psi([I]) N(I)^{-u}$ of a class group character $\psi$. -/
noncomputable def classCharL (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  ∑' I : (Ideal (𝓞 K))⁰, (ψ (ClassGroup.mk0 I) : ℂ) *
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u)

/-- The completed function $\xi(u, \psi) = c_K \sum_C \psi(C^{-1}) \psi_{\mathfrak{a}_C}(u)$. -/
noncomputable def classCharXi (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) * classXi (classRepUnit K C) u

/-- For $\mathrm{Re}\, u > 1$, the sum $\sum_C \psi(C^{-1}) \psi_{\mathfrak{a}_C}(u)$ is a Dirichlet series with the weights $\psi([I])$. -/
theorem hasSum_classCharXi (ψ : ClassGroup (𝓞 K) →* ℂˣ) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => (ψ (ClassGroup.mk0 I) : ℂ) * xiTerm u I)
      (∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) * classXi (classRepUnit K C) u) := by
  have h := hasSum_sum (s := Finset.univ) fun C _ =>
    (hasSum_classXi (classRepUnit K C) hu).mul_left (ψ C⁻¹ : ℂ)
  convert h using 1
  funext I
  simp only [mk_classRepUnit]
  rw [Finset.sum_eq_single (ClassGroup.mk0 I)⁻¹ (fun C _ hC => by
    have h' : ClassGroup.mk0 I ≠ C⁻¹ := fun h => hC (by rw [h, inv_inv])
    simp [h']) (fun h => absurd (Finset.mem_univ _) h)]
  simp

private theorem hasSum_classCharL_aux (ψ : ClassGroup (𝓞 K) →* ℂˣ) {u : ℂ} (hu : 1 < u.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => (ψ (ClassGroup.mk0 I) : ℂ) *
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u))
      ((∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) * classXi (classRepUnit K C) u) /
        ((torsionOrder K : ℂ) * (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u) /
          ((unitConst K * 2 ^ rank K : ℝ) : ℂ))) := by
  have hw : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  have hΓ : gammaK K u ≠ 0 := gammaK_ne_zero (by linarith)
  have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
  have h := (hasSum_classCharXi ψ hu).div_const ((torsionOrder K : ℂ) *
    (((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u) / ((unitConst K * 2 ^ rank K : ℝ) : ℂ))
  convert h using 1
  funext I
  rw [xiTerm, Complex.ofReal_natCast]
  field_simp

/-- For $\mathrm{Re}\, u > 1$, the series $L(u, \psi)$ converges. -/
theorem summable_classCharL (ψ : ClassGroup (𝓞 K) →* ℂˣ) {u : ℂ} (hu : 1 < u.re) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => (ψ (ClassGroup.mk0 I) : ℂ) *
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-u)) :=
  (hasSum_classCharL_aux ψ hu).summable

/-- For $\mathrm{Re}\, u > 1$, $\xi(u, \psi) = |d_K|^{u/2} \Gamma_K(u) L(u, \psi)$. -/
theorem classCharXi_eq (ψ : ClassGroup (𝓞 K) →* ℂˣ) {u : ℂ} (hu : 1 < u.re) :
    classCharXi ψ u = ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u * classCharL ψ u := by
  have hw : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hA : ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))).ne'))
  have hΓ : gammaK K u ≠ 0 := gammaK_ne_zero (by linarith)
  have hC : ((unitConst K * 2 ^ rank K : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos (unitConst_pos K) (by positivity)).ne'
  rw [classCharL, (hasSum_classCharL_aux ψ hu).tsum_eq, classCharXi, xiConst]
  field_simp

/-- For the trivial character, $\xi(u, 1)$ is the completed Dedekind zeta function $\xi_K(u)$. -/
theorem classCharXi_one (u : ℂ) : classCharXi (1 : ClassGroup (𝓞 K) →* ℂˣ) u = dedekindXi K u := by
  simp [classCharXi, dedekindXi, xiConst]

/-- The root number relation $\psi(C^{-1}) = \psi([\mathfrak{d}]) \psi^{-1}(D^{-1})$ with $D = (C [\mathfrak{d}])^{-1}$. -/
theorem classChar_inv_eq (ψ : ClassGroup (𝓞 K) →* ℂˣ) (C : ClassGroup (𝓞 K)) :
    (ψ C⁻¹ : ℂ) = (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) * ((ψ⁻¹) (dualClass K C)⁻¹ : ℂ) := by
  rw [← Units.val_mul]
  congr 1
  change ψ C⁻¹ = ψ (ClassGroup.mk K (differentUnit K)) *
    (ψ⁻¹) ((C * ClassGroup.mk K (differentUnit K))⁻¹)⁻¹
  rw [inv_inv, MonoidHom.inv_apply, map_mul, mul_inv_rev, mul_inv_cancel_left, map_inv]

/-- **The functional equation.** For $u \neq 0, 1$, $\xi(1 - u, \psi) = \psi([\mathfrak{d}]) \xi(u, \psi^{-1})$. -/
theorem classCharXi_one_sub (ψ : ClassGroup (𝓞 K) →* ℂˣ) {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    classCharXi ψ (1 - u) =
      (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) * classCharXi ψ⁻¹ u := by
  rw [classCharXi, classCharXi, ← (dualClass K).sum_comp
    (fun D => ((ψ⁻¹) D⁻¹ : ℂ) * classXi (classRepUnit K D) u), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [classXi_one_sub, classXi_eq_of_mk_eq (b := classRepUnit K (dualClass K C))
    (by rw [mk_dualUnit_classRepUnit, mk_classRepUnit]) hu0 hu1, classChar_inv_eq ψ C]
  ring

end Series

section Entire

/-- The entire part $E$ of $\xi(u, \psi)$. -/
noncomputable def classCharE (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) * (classFactor (classRepUnit K C) u *
    (unitThetaFEPair (classRepUnit K C)).Λ₀ ((finrank ℚ K : ℂ) * u / 2))

/-- The numerator $F_0$ of the pole of $\xi(u, \psi)$ at $0$. -/
noncomputable def classCharF₀ (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) *
    (-(2 / (finrank ℚ K : ℂ)) * classFactor (classRepUnit K C) u)

/-- The numerator $F_1$ of the pole of $\xi(u, \psi)$ at $1$. -/
noncomputable def classCharF₁ (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  xiConst K * ∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) *
    (2 * (unitThetaFEPair (classRepUnit K C)).ε / (finrank ℚ K : ℂ) *
      classFactor (classRepUnit K C) u)

/-- The function $\xi(u, \psi)$ in the form $E(u) + F_0(u)/u + F_1(u)/(u-1)$. -/
theorem classCharXi_eq_poleShape (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) :
    classCharXi ψ u = classCharE ψ u + classCharF₀ ψ u / u + classCharF₁ ψ u / (u - 1) := by
  have h : ∀ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) * classXi (classRepUnit K C) u =
      (ψ C⁻¹ : ℂ) * (classFactor (classRepUnit K C) u *
        (unitThetaFEPair (classRepUnit K C)).Λ₀ ((finrank ℚ K : ℂ) * u / 2)) +
      (ψ C⁻¹ : ℂ) * (-(2 / (finrank ℚ K : ℂ)) * classFactor (classRepUnit K C) u) / u +
      (ψ C⁻¹ : ℂ) * (2 * (unitThetaFEPair (classRepUnit K C)).ε / (finrank ℚ K : ℂ) *
        classFactor (classRepUnit K C) u) / (u - 1) := fun C => by
    rw [classXi_eq_poleShape]
    ring
  rw [classCharXi, Finset.sum_congr rfl fun C _ => h C, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, classCharE, classCharF₀,
    classCharF₁]
  ring

theorem differentiable_classCharE (ψ : ClassGroup (𝓞 K) →* ℂˣ) :
    Differentiable ℂ (classCharE ψ) := by
  refine Differentiable.const_mul (Differentiable.fun_sum fun C _ => ?_) _
  exact ((differentiable_classFactor _).mul ((unitThetaFEPair _).differentiable_Λ₀.comp
    (by fun_prop : Differentiable ℂ fun u : ℂ => (finrank ℚ K : ℂ) * u / 2))).const_mul _

theorem differentiable_classCharF₀ (ψ : ClassGroup (𝓞 K) →* ℂˣ) :
    Differentiable ℂ (classCharF₀ ψ) :=
  Differentiable.const_mul (Differentiable.fun_sum fun _ _ =>
    ((differentiable_classFactor _).const_mul _).const_mul _) _

theorem differentiable_classCharF₁ (ψ : ClassGroup (𝓞 K) →* ℂˣ) :
    Differentiable ℂ (classCharF₁ ψ) :=
  Differentiable.const_mul (Differentiable.fun_sum fun _ _ =>
    ((differentiable_classFactor _).const_mul _).const_mul _) _

/-- **The orthogonality of characters.** For $\psi \neq 1$, $\sum_C \psi(C^{-1}) = 0$. -/
theorem sum_classChar_inv (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) :
    ∑ C : ClassGroup (𝓞 K), (ψ C⁻¹ : ℂ) = 0 := by
  have hf : (Units.coeHom ℂ).comp ψ ≠ 1 := fun h => hψ (MonoidHom.ext fun C =>
    Units.ext (by simpa using DFunLike.congr_fun h C))
  refine (Fintype.sum_equiv (Equiv.inv (ClassGroup (𝓞 K))) (fun C => (ψ C⁻¹ : ℂ))
    (fun C => (ψ C : ℂ)) fun C => rfl).trans ?_
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp ψ) hf

/-- For $\psi \neq 1$, $F_0(0) = 0$. -/
theorem classCharF₀_zero (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) : classCharF₀ ψ 0 = 0 := by
  simp only [classCharF₀, classFactor_zero, mul_one]
  rw [← Finset.sum_mul, sum_classChar_inv ψ hψ, zero_mul, mul_zero]

/-- For $\psi \neq 1$, $F_1(1) = 0$. -/
theorem classCharF₁_one (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) : classCharF₁ ψ 1 = 0 := by
  have h : ∀ C : ClassGroup (𝓞 K), 2 * (unitThetaFEPair (classRepUnit K C)).ε /
      (finrank ℚ K : ℂ) * classFactor (classRepUnit K C) 1 = 2 / (finrank ℚ K : ℂ) := by
    intro C
    rw [div_mul_eq_mul_div, mul_assoc, ε_mul_classFactor_one, mul_one]
  simp only [classCharF₁, h]
  rw [← Finset.sum_mul, sum_classChar_inv ψ hψ, zero_mul, mul_zero]

/-- The function $E(u) + (F_0(u) - F_0(0))/u + (F_1(u) - F_1(1))/(u - 1)$, extended to $u = 0$ and $u = 1$ by the derivatives. For $\psi \neq 1$ this is the entire continuation of $\xi(u, \psi)$. -/
noncomputable def classCharLambda (ψ : ClassGroup (𝓞 K) →* ℂˣ) (u : ℂ) : ℂ :=
  classCharE ψ u + dslope (classCharF₀ ψ) 0 u + dslope (classCharF₁ ψ) 1 u

/-- The function `classCharLambda ψ` is entire. -/
theorem differentiable_classCharLambda (ψ : ClassGroup (𝓞 K) →* ℂˣ) :
    Differentiable ℂ (classCharLambda ψ) := by
  have h₀ : Differentiable ℂ (dslope (classCharF₀ ψ) 0) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem, differentiableOn_univ]
    exact differentiable_classCharF₀ ψ
  have h₁ : Differentiable ℂ (dslope (classCharF₁ ψ) 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem, differentiableOn_univ]
    exact differentiable_classCharF₁ ψ
  exact ((differentiable_classCharE ψ).add h₀).add h₁

/-- For $\psi \neq 1$ and $u \neq 0, 1$, the entire function `classCharLambda ψ` is equal to $\xi(u, \psi)$. -/
theorem classCharLambda_eq (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) {u : ℂ} (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) : classCharLambda ψ u = classCharXi ψ u := by
  rw [classCharLambda, classCharXi_eq_poleShape, dslope_of_ne _ hu0, dslope_of_ne _ hu1,
    slope_def_field, slope_def_field, classCharF₀_zero ψ hψ, classCharF₁_one ψ hψ]
  simp only [sub_zero]

/-- For $\psi \neq 1$ and $\mathrm{Re}\, u > 1$, the entire function `classCharLambda ψ` is $|d_K|^{u/2} \Gamma_K(u) L(u, \psi)$. -/
theorem classCharLambda_eq_classCharL (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) {u : ℂ}
    (hu : 1 < u.re) :
    classCharLambda ψ u = ((√|(discr K : ℝ)| : ℝ) : ℂ) ^ u * gammaK K u * classCharL ψ u := by
  have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; linarith
  have hu1 : u ≠ 1 := fun h => by rw [h, Complex.one_re] at hu; linarith
  rw [classCharLambda_eq ψ hψ hu0 hu1, classCharXi_eq ψ hu]

/-- **Hecke's theorem for class group characters.** For $\psi \neq 1$, the entire continuation of $\xi(u, \psi)$ satisfies $\xi(1 - u, \psi) = \psi([\mathfrak{d}]) \xi(u, \psi^{-1})$ for all $u \in \mathbb{C}$. -/
theorem classCharLambda_one_sub (ψ : ClassGroup (𝓞 K) →* ℂˣ) (hψ : ψ ≠ 1) (u : ℂ) :
    classCharLambda ψ (1 - u) =
      (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) * classCharLambda ψ⁻¹ u := by
  have hψ' : ψ⁻¹ ≠ 1 := fun h => hψ (MonoidHom.ext fun C => by
    simpa using DFunLike.congr_fun h C)
  have hd : Dense ({0, 1} : Set ℂ)ᶜ := (Set.toFinite _).countable.dense_compl ℝ
  have hf : Continuous fun v => classCharLambda ψ (1 - v) :=
    (differentiable_classCharLambda ψ).continuous.comp (continuous_const.sub continuous_id)
  have hg : Continuous fun v => (ψ (ClassGroup.mk K (differentUnit K)) : ℂ) *
      classCharLambda ψ⁻¹ v :=
    continuous_const.mul (differentiable_classCharLambda ψ⁻¹).continuous
  refine congr_fun (Continuous.ext_on hd hf hg fun v hv => ?_) u
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hv
  have h0 : 1 - v ≠ 0 := sub_ne_zero.2 (Ne.symm hv.2)
  have h1 : 1 - v ≠ 1 := fun h => hv.1 (by linear_combination -h)
  rw [classCharLambda_eq ψ hψ h0 h1, classCharLambda_eq ψ⁻¹ hψ' hv.1 hv.2,
    classCharXi_one_sub ψ hv.1 hv.2]

end Entire

end Langlands.Tate
