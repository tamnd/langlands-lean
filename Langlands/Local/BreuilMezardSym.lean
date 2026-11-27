/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.BreuilMezardLattices
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Irreducibility of the Serre weights, and the types over a general field

This file has two parts that the Breuil-Mézard conjecture needs.

First, it proves that the Serre weight $\sigma_{a,b} = \mathrm{Sym}^a k^2 \otimes \det^b$ is irreducible when $k$ has characteristic $p$ and $a < p$. The group is $SL_2(\mathbb{F}_p)$, $GL_2(\mathbb{F}_p)$, or any group whose image in $GL_2(k)$ contains the lower unipotent matrix and the Weyl element.

Second, it defines the multiplicity $n_{a,b}(\lambda, \tau)$ for a representation $\tau$ over any field $C$, shows that it agrees with `typeMultiplicity` for a base change from $\mathbb{C}$, and shows that it depends only on the isomorphism class of $\tau$ when $O$ is a discrete valuation ring with fraction field $C$ (by Brauer-Nesbitt). In particular this holds for $O = O_E$ and $C = E$.

## Main definitions

* `Langlands.dehom`: the map $P(X_0, X_1) \mapsto P(X, 1)$ from homogeneous polynomials of degree $a$ to polynomials in one variable.
* `Langlands.lowerUnipotent`, `Langlands.weylElement`: the matrices $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ and $\begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$.
* `Langlands.slFpTo`, `Langlands.glFpTo`: the maps $SL_2(\mathbb{F}_p) \to GL_2(k)$ and $GL_2(\mathbb{F}_p) \to GL_2(k)$.
* `Langlands.typeRep`: the representation $\mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} C^2 \otimes \det^{\lambda_2} \otimes \tau$.
* `Langlands.typeMultiplicityOf`: the multiplicity $n_{a,b}(\lambda, \tau)$ for a representation $\tau$ over a field $C$.

## Main results

* `Langlands.eq_top_of_stable`: a nonzero subspace of $\mathrm{Sym}^a k^2$ that is stable under the lower unipotent matrix and the Weyl element is everything, for $a < p$.
* `Langlands.isIrreducible_serreWeightRep`: $\sigma_{a,b}$ is irreducible for $a < p$ when the image of the group contains the two matrices.
* `Langlands.isIrreducible_serreWeightRep_slFpTo`, `Langlands.isIrreducible_serreWeightRep_glFpTo`: the same for $SL_2(\mathbb{F}_p)$ and $GL_2(\mathbb{F}_p)$.
* `Langlands.reductionMultiplicity_congr`, `Langlands.serreMultiplicity_congr`: the multiplicities depend only on the isomorphism class.
* `Langlands.typeMultiplicity_eq_typeMultiplicityOf`: `typeMultiplicity` is `typeMultiplicityOf` of the base change.
* `Langlands.typeMultiplicityOf_congr`, `Langlands.typeMultiplicityOf_integer_congr`: Brauer-Nesbitt for the types, over a discrete valuation ring and over $O_E$.

## Implementation notes

For irreducibility we identify $\mathrm{Sym}^a k^2$ with the polynomials of degree at most $a$ by $P \mapsto P(X, 1)$. The lower unipotent matrix acts as $f \mapsto f(X + 1)$. For $1 \le \deg f < p$ the difference $f(X + 1) - f$ has degree exactly $\deg f - 1$. So a nonzero stable subspace contains $1$, which is the image of $X_1^a$. The Weyl element sends $X_1^a$ to $X_0^a$, which is $X^a$, and then the differences give all polynomials of degree at most $a$.

The multiplicity `typeMultiplicity` takes a ring map $\iota : \mathbb{C} \to C$. When the residue field of $O$ has characteristic $p$ and $O$ is a discrete valuation ring with fraction field $C$, no such ring map exists, because the valuation on the image of $\mathbb{C}$ would be nontrivial with a divisible value group. Thus `typeMultiplicity_eq_of_equiv` does not apply in that case, and the Breuil-Mézard statement must use `typeMultiplicityOf` for a model of $\sigma(\tau)$ over $E$.

## References

* C. Breuil and A. Mézard, Multiplicités modulaires et représentations de $GL_2(\mathbb{Z}_p)$ et de $\mathrm{Gal}(\overline{\mathbb{Q}}_p / \mathbb{Q}_p)$ en $\ell = p$, Duke Math. J. 115 (2002).
* J. L. Alperin, Local representation theory, chapter 1.
-/

namespace Langlands

section ForwardDifference

open Polynomial

variable {k : Type*} [Field k]

/-- The coefficients of $f(X + 1)$. -/
theorem coeff_comp_X_add_one (f : k[X]) (m : ℕ) :
    (f.comp (X + 1)).coeff m = ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * (i.choose m) := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
  simp only [sum_comp, mul_comp, C_comp, X_pow_comp, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_one_pow]

/-- The forward difference $f(X + 1) - f$ has no coefficient in degree $\ge \deg f$. -/
theorem coeff_fwdDiff_eq_zero (f : k[X]) {m : ℕ} (hm : f.natDegree ≤ m) :
    (f.comp (X + 1) - f).coeff m = 0 := by
  rw [coeff_sub, coeff_comp_X_add_one, Finset.sum_eq_single m]
  · simp
  · intro i hi him
    have : i < m := lt_of_le_of_ne ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hm) him
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hm'
    have : f.natDegree < m := by simpa [Nat.lt_succ_iff] using hm'
    simp [coeff_eq_zero_of_natDegree_lt this]

/-- The forward difference lowers the degree. -/
theorem natDegree_fwdDiff_le (f : k[X]) : (f.comp (X + 1) - f).natDegree ≤ f.natDegree - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  exact coeff_fwdDiff_eq_zero f (by omega)

/-- The coefficient of $X^n$ in $f(X + 1) - f$ is $(n + 1) a_{n + 1}$ if $\deg f = n + 1$. -/
theorem coeff_fwdDiff_of_natDegree_eq (f : k[X]) {n : ℕ} (hn : f.natDegree = n + 1) :
    (f.comp (X + 1) - f).coeff n = (n + 1 : k) * f.coeff (n + 1) := by
  rw [coeff_sub, coeff_comp_X_add_one, hn, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun i hi => by
      simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]]
  simp [Nat.choose_succ_self_right]
  ring

variable (p : ℕ) [CharP k p]

/-- If $1 \le \deg f < p$, then the coefficient of $X^{\deg f - 1}$ in $f(X + 1) - f$ is not zero. -/
theorem coeff_fwdDiff_ne_zero {f : k[X]} {n : ℕ} (hn : f.natDegree = n + 1) (hp : n + 1 < p) :
    (f.comp (X + 1) - f).coeff n ≠ 0 := by
  rw [coeff_fwdDiff_of_natDegree_eq f hn]
  refine mul_ne_zero ?_ ?_
  · have : ((n + 1 : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]
      exact fun h => absurd (Nat.le_of_dvd (Nat.succ_pos n) h) (by omega)
    simpa using this
  · rw [← hn, coeff_natDegree, Ne, leadingCoeff_eq_zero]
    rintro rfl
    simp at hn

/-- If $1 \le \deg f < p$, then $f(X + 1) - f$ has degree $\deg f - 1$. -/
theorem natDegree_fwdDiff_of_lt {f : k[X]} {n : ℕ} (hn : f.natDegree = n + 1) (hp : n + 1 < p) :
    (f.comp (X + 1) - f).natDegree = n := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (coeff_fwdDiff_ne_zero p hn hp))
  have := natDegree_fwdDiff_le f
  omega

/-- Let $U$ be a space of polynomials that contains $X^a$ and is stable under $f \mapsto f(X + 1)$. If $a < p$, then $U$ contains each polynomial of degree at most $a$. -/
theorem mem_of_natDegree_le {U : Submodule k k[X]} {a : ℕ} (ha : a < p) (hXa : X ^ a ∈ U)
    (hU : ∀ f ∈ U, f.comp (X + 1) ∈ U) {f : k[X]} (hf : f.natDegree ≤ a) : f ∈ U := by
  have hg : ∀ j ≤ a, ∃ g ∈ U, g.natDegree = a - j ∧ g.coeff (a - j) ≠ 0 := by
    intro j hj
    induction j with
    | zero => exact ⟨X ^ a, hXa, by simp, by simp⟩
    | succ j ih =>
      obtain ⟨g, hgU, hgd, -⟩ := ih (by omega)
      have hgd' : g.natDegree = a - (j + 1) + 1 := by omega
      exact ⟨g.comp (X + 1) - g, sub_mem (hU g hgU) hgU,
        natDegree_fwdDiff_of_lt p hgd' (by omega), coeff_fwdDiff_ne_zero p hgd' (by omega)⟩
  have key : ∀ n ≤ a, ∀ f : k[X], f.natDegree ≤ n → f ∈ U := by
    intro n
    induction n with
    | zero =>
      intro _ f hf
      obtain ⟨g, hgU, hgd, hgc⟩ := hg a le_rfl
      rw [Nat.sub_self] at hgd hgc
      have hf' := eq_C_of_natDegree_le_zero hf
      have hg' := eq_C_of_natDegree_eq_zero hgd
      have : f = (f.coeff 0 / g.coeff 0) • g := by
        rw [smul_eq_C_mul, hg', ← C_mul, coeff_C_zero, div_mul_cancel₀ _ hgc, hf', coeff_C_zero]
      rw [this]
      exact U.smul_mem _ hgU
    | succ n ih =>
      intro hn f hf
      obtain ⟨g, hgU, hgd, hgc⟩ := hg (a - (n + 1)) (by omega)
      rw [Nat.sub_sub_self hn] at hgd hgc
      set c := f.coeff (n + 1) / g.coeff (n + 1)
      have hh : (f - c • g).natDegree ≤ n := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [coeff_sub, coeff_smul, smul_eq_mul]
        rcases (Nat.succ_le_of_lt hN).eq_or_lt with h | h
        · rw [← h, div_mul_cancel₀ _ hgc, sub_self]
        · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt h),
            coeff_eq_zero_of_natDegree_lt (hgd.trans_lt h), mul_zero, sub_zero]
      have := U.add_mem (ih (by omega) _ hh) (U.smul_mem c hgU)
      rwa [sub_add_cancel] at this
  exact key a le_rfl f hf

end ForwardDifference

section Dehomogenize

open Polynomial

variable {k : Type*} [Field k] (a : ℕ)

/-- The dehomogenization $P \mapsto P(X, 1)$ of the homogeneous polynomials of degree $a$ in two variables. -/
noncomputable def dehom : MvPolynomial.homogeneousSubmodule (Fin 2) k a →ₗ[k] k[X] :=
  (MvPolynomial.aeval ![(X : k[X]), 1]).toLinearMap ∘ₗ
    (MvPolynomial.homogeneousSubmodule (Fin 2) k a).subtype

variable {a}

/-- The value of `dehom`. -/
theorem dehom_apply (P : MvPolynomial.homogeneousSubmodule (Fin 2) k a) :
    dehom a P = MvPolynomial.aeval ![(X : k[X]), 1] (P : MvPolynomial (Fin 2) k) :=
  rfl

/-- The homogenization of $P(X, 1)$ in degree $a$ is $P$. -/
theorem homogenize_dehom (P : MvPolynomial.homogeneousSubmodule (Fin 2) k a) :
    (dehom a P).homogenize a = P :=
  homogenize_eq_of_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule _ _).1 P.2) rfl

/-- The dehomogenization is injective. -/
theorem dehom_injective : Function.Injective (dehom (k := k) a) := by
  intro P Q h
  apply Subtype.ext
  rw [← homogenize_dehom P, ← homogenize_dehom Q, h]

/-- The dehomogenization of a polynomial of degree $a$ has degree at most $a$. -/
theorem natDegree_dehom_le (P : MvPolynomial.homogeneousSubmodule (Fin 2) k a) :
    (dehom a P).natDegree ≤ a := by
  have hP := (MvPolynomial.mem_homogeneousSubmodule _ _).1 P.2
  rw [dehom_apply, (P : MvPolynomial (Fin 2) k).as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hm' : m 0 + m 1 = a := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one,
    algebraMap_eq]
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- Each polynomial of degree at most $a$ is the dehomogenization of a homogeneous polynomial of degree $a$. -/
theorem dehom_homogenize {f : k[X]} (hf : f.natDegree ≤ a) :
    dehom a ⟨f.homogenize a, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (isHomogeneous_homogenize f)⟩ = f :=
  aeval_homogenize_X_one f hf

/-- The lower unipotent matrix $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$. -/
def lowerUnipotent {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 1, 1]

/-- The Weyl element $\begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def weylElement {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- The lower unipotent matrix acts on dehomogenizations by $f \mapsto f(X + 1)$. -/
theorem dehom_symPowEnd_lowerUnipotent (P : MvPolynomial.homogeneousSubmodule (Fin 2) k a) :
    dehom a (symPowEnd a lowerUnipotent P) = (dehom a P).comp (X + 1) := by
  rw [dehom_apply, dehom_apply, comp_eq_aeval, MvPolynomial.comp_aeval_apply]
  change MvPolynomial.aeval _ (MvPolynomial.bind₁ _ (P : MvPolynomial (Fin 2) k)) = _
  rw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun v => MvPolynomial.aeval v (P : MvPolynomial (Fin 2) k)) ?_
  funext i
  fin_cases i <;> simp [linearForm, lowerUnipotent, Fin.sum_univ_two]

/-- The Weyl element sends $X_1^a$ to $X_0^a$. -/
theorem symPowEnd_weylElement_X_one_pow :
    ((symPowEnd a weylElement ⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 ^ a := by
  change MvPolynomial.bind₁ _ _ = _
  simp [linearForm, weylElement, Fin.sum_univ_two]

end Dehomogenize

section SymIrreducible

open Polynomial

variable {k : Type*} [Field k] (p : ℕ) [CharP k p] {a : ℕ}

/-- The dehomogenization of $X_1^a$ is $1$. -/
theorem dehom_X_one_pow :
    dehom a (⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) = 1 := by
  simp [dehom_apply]

/-- The dehomogenization of $X_0^a$ is $X^a$. -/
theorem dehom_X_zero_pow :
    dehom a (⟨MvPolynomial.X 0 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) = X ^ a := by
  simp [dehom_apply]

/-- **The fixed line.** Let $a < p$. A nonzero subspace $W$ of $\mathrm{Sym}^a k^2$ that is stable under the lower unipotent matrix contains $X_1^a$. -/
theorem X_one_pow_mem_of_stable (ha : a < p)
    {W : Submodule k (MvPolynomial.homogeneousSubmodule (Fin 2) k a)}
    (hl : ∀ P ∈ W, symPowEnd a lowerUnipotent P ∈ W) (hW : W ≠ ⊥) :
    (⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) ∈ W := by
  classical
  have hex : ∃ n, ∃ P ∈ W, P ≠ 0 ∧ (dehom a P).natDegree = n := by
    obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨_, P, hP, hP0, rfl⟩
  obtain ⟨P, hP, hP0, hPd⟩ := Nat.find_spec hex
  have hd0 : Nat.find hex = 0 := by
    by_contra h
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
    have hPd' : (dehom a P).natDegree = n + 1 := hPd.trans hn
    have hlt : n + 1 < p := by have := natDegree_dehom_le P; omega
    apply Nat.find_min hex (show n < Nat.find hex by omega)
    refine ⟨symPowEnd a lowerUnipotent P - P, W.sub_mem (hl P hP) hP, ?_, ?_⟩
    · intro h0
      have := congrArg (dehom a) h0
      rw [map_sub, dehom_symPowEnd_lowerUnipotent, map_zero] at this
      apply coeff_fwdDiff_ne_zero p hPd' hlt
      rw [this, coeff_zero]
    · rw [map_sub, dehom_symPowEnd_lowerUnipotent]
      exact natDegree_fwdDiff_of_lt p hPd' hlt
  rw [hd0] at hPd
  have hPC := eq_C_of_natDegree_eq_zero hPd
  have hc : (dehom a P).coeff 0 ≠ 0 := by
    intro hc
    apply hP0
    apply dehom_injective
    rw [map_zero, hPC, hc, map_zero]
  have : (⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) = ((dehom a P).coeff 0)⁻¹ • P := by
    apply dehom_injective
    rw [dehom_X_one_pow, map_smul, hPC, smul_eq_C_mul, ← C_mul, coeff_C_zero,
      inv_mul_cancel₀ (by rwa [hPC, coeff_C_zero] at hc), C_1]
  rw [this]
  exact W.smul_mem _ hP

/-- **Irreducibility of $\mathrm{Sym}^a$.** Let $a < p$. A nonzero subspace of $\mathrm{Sym}^a k^2$ that is stable under the lower unipotent matrix and the Weyl element is the whole space. -/
theorem eq_top_of_stable (ha : a < p)
    {W : Submodule k (MvPolynomial.homogeneousSubmodule (Fin 2) k a)}
    (hl : ∀ P ∈ W, symPowEnd a lowerUnipotent P ∈ W)
    (hw : ∀ P ∈ W, symPowEnd a weylElement P ∈ W) (hW : W ≠ ⊥) : W = ⊤ := by
  have h₁ := X_one_pow_mem_of_stable p ha hl hW
  have h₀ : (⟨MvPolynomial.X 0 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) ∈ W := by
    convert hw _ h₁ using 1
    exact Subtype.ext symPowEnd_weylElement_X_one_pow.symm
  have hU : ∀ f ∈ W.map (dehom a), f.comp (X + 1) ∈ W.map (dehom a) := by
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨_, hl P hP, dehom_symPowEnd_lowerUnipotent P⟩
  have hXa : X ^ a ∈ W.map (dehom a) := ⟨_, h₀, dehom_X_zero_pow⟩
  refine eq_top_iff.2 fun Q _ => ?_
  obtain ⟨P, hP, hPQ⟩ := mem_of_natDegree_le p ha hXa hU (natDegree_dehom_le Q)
  rwa [← dehom_injective hPQ]

end SymIrreducible

section SerreWeightIrreducible

variable {k : Type*} [Field k] (p : ℕ) [CharP k p] {G : Type*} [Group G]

/-- If $\theta(g)$ is a matrix $M$ with $\det M = 1$, then $g$ acts on $\sigma_{a,b}$ by $M$. -/
theorem serreWeightRep_apply_of_det_eq_one (θ : G →* GL (Fin 2) k) (a b : ℕ) {g : G}
    {M : Matrix (Fin 2) (Fin 2) k} (hg : (θ g : Matrix (Fin 2) (Fin 2) k) = M) (hM : M.det = 1) :
    serreWeightRep θ a b g = symPowEnd a M := by
  simp only [serreWeightRep, MonoidHom.comp_apply, serreWeight, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [hg, hM, one_pow, one_smul]

/-- The lower unipotent matrix has determinant one. -/
theorem det_lowerUnipotent {R : Type*} [CommRing R] :
    (lowerUnipotent : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [lowerUnipotent, Matrix.det_fin_two]

/-- The Weyl element has determinant one. -/
theorem det_weylElement {R : Type*} [CommRing R] :
    (weylElement : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [weylElement, Matrix.det_fin_two]

/-- **Irreducibility of the Serre weights.** Let $k$ be a field of characteristic $p$ and let $a < p$. If the image of $\theta : G \to GL_2(k)$ contains the lower unipotent matrix and the Weyl element, then $\sigma_{a,b} = \mathrm{Sym}^a k^2 \otimes \det^b$ is irreducible. -/
theorem isIrreducible_serreWeightRep (θ : G →* GL (Fin 2) k) {a : ℕ} (ha : a < p) (b : ℕ)
    (hl : ∃ g, (θ g : Matrix (Fin 2) (Fin 2) k) = lowerUnipotent)
    (hw : ∃ g, (θ g : Matrix (Fin 2) (Fin 2) k) = weylElement) :
    (serreWeightRep θ a b).IsIrreducible := by
  obtain ⟨gl, hgl⟩ := hl
  obtain ⟨gw, hgw⟩ := hw
  have hne : (⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
      MvPolynomial.homogeneousSubmodule (Fin 2) k a) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp at this
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have : (⟨MvPolynomial.X 1 ^ a, MvPolynomial.isHomogeneous_X_pow _ _⟩ :
        MvPolynomial.homogeneousSubmodule (Fin 2) k a) ∈
        (⊤ : Subrepresentation (serreWeightRep θ a b)).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact (Submodule.mem_bot k).1 this
  · by_cases hW : W.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
    · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_of_stable p ha
        (fun P hP => ?_) (fun P hP => ?_) hW))
      · rw [← serreWeightRep_apply_of_det_eq_one θ a b hgl det_lowerUnipotent]
        exact W.apply_mem_toSubmodule gl hP
      · rw [← serreWeightRep_apply_of_det_eq_one θ a b hgw det_weylElement]
        exact W.apply_mem_toSubmodule gw hP

/-- The Serre weight $\sigma_{a,b}$ is a simple module over the group algebra, under the hypotheses of `isIrreducible_serreWeightRep`. -/
theorem isSimpleModule_serreWeightRep (θ : G →* GL (Fin 2) k) {a : ℕ} (ha : a < p) (b : ℕ)
    (hl : ∃ g, (θ g : Matrix (Fin 2) (Fin 2) k) = lowerUnipotent)
    (hw : ∃ g, (θ g : Matrix (Fin 2) (Fin 2) k) = weylElement) :
    IsSimpleModule (MonoidAlgebra k G) (serreWeightRep θ a b).asModule :=
  (Representation.irreducible_iff_isSimpleModule_asModule _).1
    (isIrreducible_serreWeightRep p θ ha b hl hw)

/-- The map $SL_2(\mathbb{F}_p) \to GL_2(k)$ for a field $k$ of characteristic $p$. -/
noncomputable def slFpTo : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) k :=
  (Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl p) k)).comp
    Matrix.SpecialLinearGroup.toGL

/-- The map $GL_2(\mathbb{F}_p) \to GL_2(k)$ for a field $k$ of characteristic $p$. -/
noncomputable def glFpTo : GL (Fin 2) (ZMod p) →* GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl p) k)

/-- The matrix of the image of $g \in SL_2(\mathbb{F}_p)$ in $GL_2(k)$. -/
theorem slFpTo_apply (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    ((slFpTo p g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)).map (ZMod.castHom (dvd_refl p) k) := by
  change ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)).map (ZMod.castHom (dvd_refl p) k) = _
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

/-- The image of $SL_2(\mathbb{F}_p)$ contains the lower unipotent matrix. -/
theorem exists_slFpTo_eq_lowerUnipotent :
    ∃ g, ((slFpTo p g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = lowerUnipotent := by
  refine ⟨_, (slFpTo_apply (k := k) p ⟨lowerUnipotent, det_lowerUnipotent⟩).trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

/-- The image of $SL_2(\mathbb{F}_p)$ contains the Weyl element. -/
theorem exists_slFpTo_eq_weylElement :
    ∃ g, ((slFpTo p g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = weylElement := by
  refine ⟨_, (slFpTo_apply (k := k) p ⟨weylElement, det_weylElement⟩).trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylElement]

/-- **Irreducibility of the Serre weights of $SL_2(\mathbb{F}_p)$.** For a field $k$ of characteristic $p$ and $a < p$, the representation $\mathrm{Sym}^a k^2 \otimes \det^b$ of $SL_2(\mathbb{F}_p)$ is irreducible. -/
theorem isIrreducible_serreWeightRep_slFpTo {a : ℕ} (ha : a < p) (b : ℕ) :
    (serreWeightRep (slFpTo (k := k) p) a b).IsIrreducible :=
  isIrreducible_serreWeightRep p _ ha b (exists_slFpTo_eq_lowerUnipotent p)
    (exists_slFpTo_eq_weylElement p)

/-- **Irreducibility of the Serre weights of $GL_2(\mathbb{F}_p)$.** For a field $k$ of characteristic $p$ and $a < p$, the representation $\mathrm{Sym}^a k^2 \otimes \det^b$ of $GL_2(\mathbb{F}_p)$ is irreducible. -/
theorem isIrreducible_serreWeightRep_glFpTo {a : ℕ} (ha : a < p) (b : ℕ) :
    (serreWeightRep (glFpTo (k := k) p) a b).IsIrreducible := by
  obtain ⟨gl, hgl⟩ := exists_slFpTo_eq_lowerUnipotent (k := k) p
  obtain ⟨gw, hgw⟩ := exists_slFpTo_eq_weylElement (k := k) p
  exact isIrreducible_serreWeightRep p _ ha b ⟨_, hgl⟩ ⟨_, hgw⟩

/-- The Serre weight $\mathrm{Sym}^a k^2 \otimes \det^b$ of $GL_2(\mathbb{F}_p)$ is a simple module over the group algebra for $a < p$. -/
instance isSimpleModule_serreWeightRep_glFpTo {a : ℕ} [Fact (a < p)] (b : ℕ) :
    IsSimpleModule (MonoidAlgebra k (GL (Fin 2) (ZMod p)))
      (serreWeightRep (glFpTo (k := k) p) a b).asModule :=
  (Representation.irreducible_iff_isSimpleModule_asModule _).1
    (isIrreducible_serreWeightRep_glFpTo p Fact.out b)

end SerreWeightIrreducible

section Congr

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {G : Type*} [Group G] {L₁ L₂ : Type*}
  [AddCommGroup L₁] [Module O L₁] [AddCommGroup L₂] [Module O L₂]

/-- Isomorphic representations over $O$ have the same multiplicities in their reductions. -/
theorem reductionMultiplicity_congr {σ₁ : Representation O G L₁} {σ₂ : Representation O G L₂}
    (f : L₁ ≃ₗ[O] L₂) (hf : ∀ g x, f (σ₁ g x) = σ₂ g (f x)) {S : Type*} [AddCommGroup S]
    [Module (ResidueField O) S] (W : Representation (ResidueField O) G S) :
    reductionMultiplicity σ₁ W = reductionMultiplicity σ₂ W := by
  have hf' : ∀ g x, f.symm (σ₂ g x) = σ₁ g (f.symm x) := fun g x =>
    f.injective (by rw [hf, f.apply_symm_apply, f.apply_symm_apply])
  let φ := asModuleHom (reduceHom f.toLinearMap)
    (reduceHom_intertwines f.toLinearMap fun g x => hf g x)
  let ψ := asModuleHom (reduceHom f.symm.toLinearMap)
    (reduceHom_intertwines f.symm.toLinearMap fun g x => hf' g x)
  have h₁ : ∀ z, reduceHom f.symm.toLinearMap (reduceHom f.toLinearMap z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [reduceHom_mk, reduceHom_mk]
    simp
  have h₂ : ∀ z, reduceHom f.toLinearMap (reduceHom f.symm.toLinearMap z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [reduceHom_mk, reduceHom_mk]
    simp
  exact jhMultiplicity_congr _ (LinearEquiv.ofLinearMap φ ψ (LinearMap.ext h₂) (LinearMap.ext h₁))

variable {C : Type*} [Field C] [Algebra O C] {V V' : Type*} [AddCommGroup V] [Module C V]
  [Module O V] [IsScalarTower O C V] [AddCommGroup V'] [Module C V'] [Module O V']
  [IsScalarTower O C V'] {ρ : Representation C G V} {ρ' : Representation C G V'}

omit [IsLocalRing O] in
/-- The image of a stable lattice under an isomorphism of representations is a stable lattice. -/
theorem IsStableLattice.map (e : V ≃ₗ[C] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    {L : Submodule O V} (hL : IsStableLattice ρ L) :
    IsStableLattice ρ' (L.map ((e : V →ₗ[C] V').restrictScalars O)) := by
  refine ⟨⟨hL.1.fg.map _, ?_⟩, ?_⟩
  · change Submodule.span C ((e : V →ₗ[C] V') '' L) = ⊤
    rw [Submodule.span_image, hL.1.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.2 e.surjective]
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hL.2 g v hv, he g v⟩

/-- Isomorphic representations over $C$ have the same multiplicities at corresponding stable lattices. -/
theorem latticeSerreMultiplicity_congr (e : V ≃ₗ[C] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    {L : Submodule O V} (hL : IsStableLattice ρ L) (θ : G →* GL (Fin 2) (ResidueField O))
    (a b : ℕ) :
    latticeSerreMultiplicity ρ L hL.2 θ a b =
      latticeSerreMultiplicity ρ' _ (hL.map e he).2 θ a b := by
  refine reductionMultiplicity_congr
    (Submodule.equivMapOfInjective ((e : V →ₗ[C] V').restrictScalars O) e.injective L)
    (fun g x => Subtype.ext ?_) _
  exact he g x

end Congr

section CongrDVR

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*} [Group G]
  {C : Type*} [Field C] [Algebra O C] [IsFractionRing O C] {V V' : Type*} [AddCommGroup V]
  [Module C V] [Module O V] [IsScalarTower O C V] [AddCommGroup V'] [Module C V'] [Module O V']
  [IsScalarTower O C V'] {ρ : Representation C G V} {ρ' : Representation C G V'}

/-- Over a discrete valuation ring $O$ with fraction field $C$, the multiplicity $n_{a,b}(\rho)$ depends only on the isomorphism class of $\rho$. -/
theorem serreMultiplicity_congr (e : V ≃ₗ[C] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (θ : G →* GL (Fin 2) (ResidueField O)) (a b : ℕ) :
    serreMultiplicity O ρ θ a b = serreMultiplicity O ρ' θ a b := by
  by_cases h : ∃ L : Submodule O V, IsStableLattice ρ L
  · obtain ⟨L, hL⟩ := h
    rw [serreMultiplicity_eq_latticeSerreMultiplicity ρ θ hL,
      serreMultiplicity_eq_latticeSerreMultiplicity ρ' θ (hL.map e he)]
    exact latticeSerreMultiplicity_congr e he hL θ a b
  · have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v =>
      e.injective (by rw [he, e.apply_symm_apply, e.apply_symm_apply])
    have h' : ¬ ∃ L : Submodule O V', IsStableLattice ρ' L :=
      fun ⟨L, hL⟩ => h ⟨_, hL.map e.symm he'⟩
    simp only [serreMultiplicity, h, h', ↓reduceDIte]

end CongrDVR

section TypeMultiplicityOf

open IsLocalRing MvPolynomial ValuativeRel TensorProduct

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] {C : Type*} [Field C]
  [Algebra K C] {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O C]

/-- The representation $\mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} C^2 \otimes \det^{\lambda_2} \otimes \tau$ of $GL_2(\mathcal{O}_K)$, with $\lambda = w$. -/
noncomputable def typeRep (w : ℤ × ℤ) {W : Type*} [AddCommGroup W] [Module C W]
    (τ : Representation C (GL (Fin 2) 𝒪[K]) W) :
    Representation C (GL (Fin 2) 𝒪[K])
      (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W) :=
  (symDetRep (glIntegersTo K) (w.1 - w.2 - 1).toNat w.2).tprod τ

/-- The multiplicity $n_{a,b}(\lambda, \tau)$ for a representation $\tau$ of $GL_2(\mathcal{O}_K)$ with coefficients in any field $C$. This is the multiplicity of $\sigma_{a,b}$ in the reduction of $\mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} C^2 \otimes \det^{\lambda_2} \otimes \tau$, with $\lambda = w$. -/
noncomputable def typeMultiplicityOf (red : 𝒪[K] →+* ResidueField O) (w : ℤ × ℤ) {W : Type*}
    [AddCommGroup W] [Module C W] (τ : Representation C (GL (Fin 2) 𝒪[K]) W) (a b : ℕ) : ℕ :=
  letI := Module.restrictScalars O C (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W)
  haveI := IsScalarTower.restrictScalars O C
    (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W)
  serreMultiplicity O (C := C) (V := homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W)
    (typeRep K w τ) (Matrix.GeneralLinearGroup.map red) a b

variable {K}

/-- The multiplicity `typeMultiplicity` for a type $\sigma$ over $\mathbb{C}$ and a ring map $\iota : \mathbb{C} \to C$ is `typeMultiplicityOf` for the base change of $\sigma$ to $C$. -/
theorem typeMultiplicity_eq_typeMultiplicityOf (ι : ℂ →+* C) (red : 𝒪[K] →+* ResidueField O)
    (w : ℤ × ℤ) (σ : SmoothRep (GL (Fin 2) 𝒪[K])) (hσ : FiniteDimensional ℂ σ.V) (a b : ℕ) :
    typeMultiplicity ι red w σ hσ a b = typeMultiplicityOf K red w (baseChangeRep ι σ hσ) a b :=
  rfl

end TypeMultiplicityOf

section TypeMultiplicityOfDVR

open IsLocalRing MvPolynomial ValuativeRel TensorProduct

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] {C : Type*} [Field C]
  [Algebra K C] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O C]
  [IsFractionRing O C]

omit [TopologicalSpace K] in
/-- Over a discrete valuation ring $O$ with fraction field $C$, the multiplicity $n_{a,b}(\lambda, \tau)$ depends only on the isomorphism class of $\tau$. -/
theorem typeMultiplicityOf_congr (red : 𝒪[K] →+* ResidueField O) (w : ℤ × ℤ) {W W' : Type*}
    [AddCommGroup W] [Module C W] [AddCommGroup W'] [Module C W']
    {τ : Representation C (GL (Fin 2) 𝒪[K]) W} {τ' : Representation C (GL (Fin 2) 𝒪[K]) W'}
    (e : W ≃ₗ[C] W') (he : ∀ g v, e (τ g v) = τ' g (e v)) (a b : ℕ) :
    typeMultiplicityOf K red w τ a b = typeMultiplicityOf K red w τ' a b := by
  let := Module.restrictScalars O C (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W)
  have := IsScalarTower.restrictScalars O C
    (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W)
  let := Module.restrictScalars O C
    (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W')
  have := IsScalarTower.restrictScalars O C
    (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C] W')
  refine serreMultiplicity_congr (TensorProduct.congr (LinearEquiv.refl C _) e)
    (fun g x => ?_) _ a b
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [typeRep, Representation.tprod_apply, he]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- If the base change of $\sigma$ along $\iota : \mathbb{C} \to C$ is isomorphic to $\tau$, then $n_{a,b}(\lambda, \sigma)$ is $n_{a,b}(\lambda, \tau)$. -/
theorem typeMultiplicity_eq_of_equiv (ι : ℂ →+* C) (red : 𝒪[K] →+* ResidueField O) (w : ℤ × ℤ)
    (σ : SmoothRep (GL (Fin 2) 𝒪[K])) (hσ : FiniteDimensional ℂ σ.V) {W : Type*}
    [AddCommGroup W] [Module C W] {τ : Representation C (GL (Fin 2) 𝒪[K]) W}
    (e : (Fin (Module.finrank ℂ σ.V) → C) ≃ₗ[C] W)
    (he : ∀ g v, e (baseChangeRep ι σ hσ g v) = τ g (e v))
    (a b : ℕ) : typeMultiplicity ι red w σ hσ a b = typeMultiplicityOf K red w τ a b :=
  typeMultiplicityOf_congr red w e he a b

end TypeMultiplicityOfDVR

section TypeMultiplicityOverE

open IsLocalRing MvPolynomial ValuativeRel TensorProduct

variable {K : Type*} [Field K] [ValuativeRel K] {E : Type*} [Field E] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra K E]

/-- Over $O_E$, the multiplicity $n_{a,b}(\lambda, \tau)$ depends only on the isomorphism class of the representation $\tau$ over $E$. -/
theorem typeMultiplicityOf_integer_congr (red : 𝒪[K] →+* 𝓀[E]) (w : ℤ × ℤ) {W W' : Type*}
    [AddCommGroup W] [Module E W] [AddCommGroup W'] [Module E W']
    {τ : Representation E (GL (Fin 2) 𝒪[K]) W} {τ' : Representation E (GL (Fin 2) 𝒪[K]) W'}
    (e : W ≃ₗ[E] W') (he : ∀ g v, e (τ g v) = τ' g (e v)) (a b : ℕ) :
    typeMultiplicityOf K red w τ a b = typeMultiplicityOf K red w τ' a b :=
  typeMultiplicityOf_congr red w e he a b

end TypeMultiplicityOverE

end Langlands
