/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.LanglandsFamilyEps
import Langlands.Ported.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity


/-!
# Admissible pairs

Let $F$ be a nonarchimedean local field. An admissible pair $(E/F, \xi)$ is a tamely ramified quadratic extension $E/F$ and a smooth character $\xi$ of $E^\times$ with two properties (BH 18.2). First, $\xi$ does not factor through the norm map $N_{E/F} : E^\times \to F^\times$. Second, if the restriction of $\xi$ to $U^1_E$ factors through $N_{E/F}$, then $E/F$ is unramified. This file defines admissible pairs, their $F$-isomorphism and their twists by characters $\chi \circ N_{E/F}$, and the level of a character. Admissible pairs are the data that parametrize the tame irreducible cuspidal representations of $GL_2(F)$ in BH Chapter 8.

## Main definitions

* `Langlands.LocalGL2.normUnits`: the norm map $N_{E/F} : E^\times \to F^\times$.
* `Langlands.LocalGL2.galConj`: the nontrivial automorphism $\sigma$ of a separable quadratic extension $E/F$.
* `Langlands.LocalGL2.unitFilt`: the unit filtration $U^n_K = 1 + \mathfrak{p}_K^n$ for $n \ge 1$, and $U^0_K = \mathcal{O}_K^\times$.
* `Langlands.LocalGL2.IsLevel`, `Langlands.LocalGL2.level`: a character $\chi$ of $K^\times$ has level $n$ when it is trivial on $U^{n+1}_K$ and not trivial on $U^n_K$.
* `Langlands.LocalGL2.IsUnramifiedExt`, `Langlands.LocalGL2.IsTotallyRamifiedExt`, `Langlands.LocalGL2.IsTameQuadratic`: the ramification of $E/F$.
* `Langlands.LocalGL2.IsAdmissible`: the character $\xi$ of $E^\times$ is admissible over $F$ (BH 18.2).
* `Langlands.LocalGL2.twistChar`: the twist $\xi \otimes \chi_E$, that is $x \mapsto \xi(x) \chi(N_{E/F}(x))$.
* `Langlands.LocalGL2.TameQuadExt`: a tamely ramified quadratic extension of $F$.
* `Langlands.LocalGL2.AdmissiblePair`: an admissible pair $(E/F, \xi)$.
* `Langlands.LocalGL2.AdmissiblePair.Iso`: $F$-isomorphism of admissible pairs.
* `Langlands.LocalGL2.AdmissiblePair.conj`: the pair $(E/F, \xi \circ \sigma)$.
* `Langlands.LocalGL2.AdmissiblePair.twist`: the pair $(E/F, \xi \otimes \chi_E)$.

## Main results

* `Langlands.LocalGL2.exists_extend_char`: each character of a subgroup of an abelian group extends to the group, since $\mathbb{C}^\times$ is divisible.
* `Langlands.LocalGL2.isSeparable_of_two_ne_zero`: a quadratic extension is separable when $2 \ne 0$ in $F$.
* `Langlands.LocalGL2.exists_eq_div_galConj`: Hilbert 90, an element of norm $1$ is $y / \sigma(y)$.
* `Langlands.LocalGL2.exists_eq_comp_normUnits_iff`: $\xi$ factors through $N_{E/F}$ exactly when $\xi \circ \sigma = \xi$.
* `Langlands.LocalGL2.isSmoothChar_iff_exists_unitFilt_le`: a character is smooth exactly when it is trivial on some $U^n_K$.
* `Langlands.LocalGL2.isLevel_level`, `Langlands.LocalGL2.IsLevel.unique`: a smooth character that is not trivial on $U^0_K$ has exactly one level.
* `Langlands.LocalGL2.ord_map`: an $F$-isomorphism $E \to E'$ preserves the normalized valuations.
* `Langlands.LocalGL2.IsAdmissible.twist`: if $\xi$ is admissible and $\chi$ is smooth, then $\xi \otimes \chi_E$ is admissible (BH 18.2).
* `Langlands.LocalGL2.IsAdmissible.comp_galConjUnits_ne`: an admissible character is regular, $\xi \circ \sigma \ne \xi$.
* `Langlands.LocalGL2.IsAdmissible.comp_galConjUnits`: $\xi \circ \sigma$ is admissible.
* `Langlands.LocalGL2.IsAdmissible.isLevel_level_of_ramified`: if $E/F$ is totally ramified, then $\xi$ has a level and the level is at least $1$.
* `Langlands.LocalGL2.AdmissiblePair.iso_equivalence`: $F$-isomorphism is an equivalence relation.
* `Langlands.LocalGL2.AdmissiblePair.iso_conj`: $(E/F, \xi) \cong (E/F, \xi \circ \sigma)$ (BH 18.2).
* `Langlands.LocalGL2.AdmissiblePair.conj_ξ_ne`: $\xi \circ \sigma \ne \xi$ for each admissible pair.
* `Langlands.LocalGL2.AdmissiblePair.Iso.twist`: the twist is compatible with $F$-isomorphism.

## Implementation notes

The extension $E/F$ is bundled in `Langlands.LocalGL2.TameQuadExt`, so that pairs with different fields $E$ have the same type. The fields of this structure are the instances on $E$, the separability of $E/F$, the condition that the valuation of $E$ extends the valuation of $F$, and the tameness. The ramification index is expressed with the normalized valuation `Langlands.LocalGL1.ord`. The proof of `ord_map` uses the fact that $\mathcal{O}_E$ is the integral closure of $\mathcal{O}_F$ in $E$. The proof of `exists_eq_comp_normUnits_iff` uses Hilbert 90 and the extension of characters into the divisible group $\mathbb{C}^\times$.

## What is still open

* Minimal pairs (BH 18.2) and the fact that each admissible pair is a twist of a minimal pair.
* The fact that a minimal pair with $E/F$ ramified has odd level. This needs the equality of the residue fields of $E$ and $F$ and a computation of the norm map on the quotients $U^n_E / U^{n+1}_E$.
* The other level statements of BH 18.2 and 18.3, in particular the statements for $E/F$ unramified.
* The fundamental identity $e(E|F) \in \{1, 2\}$ for a quadratic extension. Here unramified and totally ramified are two separate hypotheses.
* Separability of $E/F$ when $p = 2$ and $E/F$ is unramified. Here it is a field of `TameQuadExt`.

## References

* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, Springer 2006, §18.
-/

namespace Langlands.LocalGL2

universe u v

section Extension

/-- The group $\mathbb{C}^\times$ is divisible: each element has an $n$-th root for each $n \ne 0$. -/
theorem units_complex_surjective_zpow {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun z : ℂˣ => z ^ n) := by
  intro z
  have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn
  rcases Int.natAbs_eq n with h | h
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hk
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hw
      exact z.ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp only
    rw [h, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, hw]
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((z⁻¹ : ℂˣ) : ℂ) hk
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hw
      exact (z⁻¹).ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp only
    rw [h, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_mk0, hw, Units.val_inv_eq_inv_val, inv_inv]

noncomputable instance : DivisibleBy (Additive ℂˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun hn => units_complex_surjective_zpow hn

/-- **Extension of characters.** Each character of a subgroup $H$ of a commutative group $G$ with values in $\mathbb{C}^\times$ is the restriction of a character of $G$, because $\mathbb{C}^\times$ is a divisible group. -/
theorem exists_extend_char {G : Type*} [CommGroup G] (H : Subgroup G) (f : H →* ℂˣ) :
    ∃ g : G →* ℂˣ, ∀ h : H, g h = f h := by
  obtain ⟨g, hg⟩ := Module.Baer.extension_property_addMonoidHom
    (Module.Baer.of_divisible (Additive ℂˣ)) (MonoidHom.toAdditive H.subtype)
    (fun a b h => Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h))) (MonoidHom.toAdditive f)
  refine ⟨AddMonoidHom.toMultiplicative g, fun h => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hg (Additive.ofMul h))

end Extension

section Quadratic

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The norm map $N_{E/F} : E^\times \to F^\times$ on the groups of units. -/
noncomputable def normUnits : Eˣ →* Fˣ :=
  Units.map (Algebra.norm F : E →* F)

variable {F E} in
/-- The value of $N_{E/F}$ on a unit is the norm of the element. -/
theorem val_normUnits (x : Eˣ) : ((normUnits F E x : Fˣ) : F) = Algebra.norm F (x : E) := rfl

variable {F E} in
/-- The map $x \mapsto j(x)$ on units, for an $F$-isomorphism $j : E \to E'$. -/
noncomputable def unitsMap {E' : Type*} [Field E'] [Algebra F E'] (j : E ≃ₐ[F] E') : Eˣ →* E'ˣ :=
  Units.map (j : E →* E')

variable {F E} in
/-- The map $j$ on units sends $x$ to $j(x)$. -/
@[simp]
theorem val_unitsMap {E' : Type*} [Field E'] [Algebra F E'] (j : E ≃ₐ[F] E') (x : Eˣ) :
    ((unitsMap j x : E'ˣ) : E') = j x := rfl

variable {F E} in
/-- An $F$-isomorphism $j : E \to E'$ does not change the norm: $N_{E'/F} \circ j = N_{E/F}$. -/
theorem normUnits_comp_unitsMap {E' : Type*} [Field E'] [Algebra F E'] (j : E ≃ₐ[F] E') :
    (normUnits F E').comp (unitsMap j) = normUnits F E := by
  ext x
  exact Algebra.norm_eq_of_algEquiv j (x : E)

variable [Algebra.IsQuadraticExtension F E]

instance : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)

/-- **Quadratic extensions in characteristic not $2$ are separable.** If $2 \ne 0$ in $F$, then each quadratic extension $E/F$ is separable. The minimal polynomial of $x \in E$ has degree $d \in \{1, 2\}$, so its derivative has the coefficient $d \ne 0$ in degree $d - 1$. -/
theorem isSeparable_of_two_ne_zero (h2 : (2 : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  rw [IsSeparable, Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  have hd1 : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hint
  have hd2 : (minpoly F x).natDegree ≤ 2 :=
    (minpoly.natDegree_le x).trans (Algebra.IsQuadraticExtension.finrank_eq_two F E).le
  intro hder
  have hc := congrArg (fun p => p.coeff ((minpoly F x).natDegree - 1)) hder
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hd1, ← Polynomial.leadingCoeff, (minpoly.monic hint).leadingCoeff,
    one_mul] at hc
  interval_cases h : (minpoly F x).natDegree
  · norm_num at hc
  · norm_num at hc
    exact h2 (by linear_combination hc)

variable [Algebra.IsSeparable F E]

/-- A separable quadratic extension has an $F$-automorphism that is not the identity. -/
theorem exists_algEquiv_ne_one : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 := by
  have h := IsGalois.card_aut_eq_finrank F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h
  by_contra hc
  push Not at hc
  have : Subsingleton (E ≃ₐ[F] E) := ⟨fun a b => (hc a).trans (hc b).symm⟩
  rw [Nat.card_unique] at h
  omega

/-- The Galois conjugation $\sigma$ of the quadratic extension $E/F$: the automorphism of $E$ over $F$ that is not the identity. -/
noncomputable def galConj : E ≃ₐ[F] E :=
  (exists_algEquiv_ne_one F E).choose

/-- The Galois conjugation is not the identity. -/
theorem galConj_ne_one : galConj F E ≠ 1 :=
  (exists_algEquiv_ne_one F E).choose_spec

/-- Each $F$-automorphism of $E$ is $1$ or $\sigma$. -/
theorem eq_one_or_eq_galConj (τ : E ≃ₐ[F] E) : τ = 1 ∨ τ = galConj F E := by
  have h := IsGalois.card_aut_eq_finrank F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h
  by_contra hc
  push Not at hc
  have h3 : 3 ≤ Nat.card (E ≃ₐ[F] E) := by
    classical
    have : ({1, galConj F E, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(galConj_ne_one F E).symm, hc.1.symm⟩
    rw [← this, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

variable {F E}

/-- The norm is $N_{E/F}(x) = x \sigma(x)$. -/
theorem algebraMap_norm_eq_mul (x : E) :
    algebraMap F E (Algebra.norm F x) = x * galConj F E x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, galConj F E} := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact eq_one_or_eq_galConj F E τ
  rw [huniv, Finset.prod_pair (galConj_ne_one F E).symm]
  rfl

/-- The Galois conjugation is an involution: $\sigma(\sigma(x)) = x$. -/
theorem galConj_galConj (x : E) : galConj F E (galConj F E x) = x := by
  rcases eq_one_or_eq_galConj F E (galConj F E * galConj F E) with h | h
  · exact DFunLike.congr_fun h x
  · have : galConj F E = 1 := by
      have h' := congrArg (fun τ => (galConj F E)⁻¹ * τ) h
      simpa using h'
    exact absurd this (galConj_ne_one F E)

variable (F E) in
/-- The map $\sigma$ on $E^\times$. -/
noncomputable abbrev galConjUnits : Eˣ →* Eˣ :=
  unitsMap (galConj F E)

/-- **Hilbert's Theorem 90 for a quadratic extension.** If $N_{E/F}(x) = 1$, then $x = y / \sigma(y)$ for some $y \in E^\times$. -/
theorem exists_eq_div_galConj {x : Eˣ} (hx : normUnits F E x = 1) :
    ∃ y : Eˣ, x = y / galConjUnits F E y := by
  have hn : (x : E) * galConj F E x = 1 := by
    rw [← algebraMap_norm_eq_mul, ← val_normUnits, hx, Units.val_one, map_one]
  by_cases hx1 : (x : E) = -1
  · obtain ⟨z, hz⟩ : ∃ z : E, galConj F E z ≠ z := by
      by_contra hc
      push Not at hc
      exact galConj_ne_one F E (AlgEquiv.ext hc)
    have hy0 : z - galConj F E z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    refine ⟨Units.mk0 _ hy0, Units.ext ?_⟩
    have hσy : galConj F E (z - galConj F E z) = -(z - galConj F E z) := by
      rw [map_sub, galConj_galConj]
      ring
    rw [Units.val_div_eq_div_val, val_unitsMap, Units.val_mk0, hσy, hx1, div_neg, div_self hy0]
  · have hy0 : 1 + (x : E) ≠ 0 := fun h => hx1 (by linear_combination h)
    refine ⟨Units.mk0 _ hy0, Units.ext ?_⟩
    rw [Units.val_div_eq_div_val, val_unitsMap, Units.val_mk0, map_add, map_one]
    have h1 : 1 + galConj F E x = galConj F E x * (1 + x) := by linear_combination -hn
    have hσ0 : galConj F E (x : E) ≠ 0 := by simp
    rw [eq_div_iff (by rw [h1]; exact mul_ne_zero hσ0 hy0)]
    linear_combination hn

/-- The norm does not change under the Galois conjugation: $N_{E/F} \circ \sigma = N_{E/F}$. -/
theorem normUnits_comp_galConjUnits :
    (normUnits F E).comp (galConjUnits F E) = normUnits F E :=
  normUnits_comp_unitsMap _

/-- **Characters that factor through the norm.** A character $\xi$ of $E^\times$ factors through $N_{E/F}$, that is $\xi = \chi \circ N_{E/F}$ for a character $\chi$ of $F^\times$, exactly when $\xi \circ \sigma = \xi$. The proof uses Hilbert's Theorem 90 and the extension of characters from the subgroup $N_{E/F}(E^\times)$ to $F^\times$. -/
theorem exists_eq_comp_normUnits_iff (ξ : Eˣ →* ℂˣ) :
    (∃ χ : Fˣ →* ℂˣ, ξ = χ.comp (normUnits F E)) ↔ ξ.comp (galConjUnits F E) = ξ := by
  constructor
  · rintro ⟨χ, rfl⟩
    rw [MonoidHom.comp_assoc, normUnits_comp_galConjUnits]
  · intro h
    have hker : (normUnits F E).ker ≤ ξ.ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := exists_eq_div_galConj hx
      rw [MonoidHom.mem_ker, map_div, ← MonoidHom.comp_apply, h, div_self']
    let f : (normUnits F E).range →* ℂˣ :=
      (QuotientGroup.lift _ ξ hker).comp
        (QuotientGroup.quotientKerEquivRange (normUnits F E)).symm.toMonoidHom
    obtain ⟨χ, hχ⟩ := exists_extend_char _ f
    refine ⟨χ, MonoidHom.ext fun x => ?_⟩
    rw [MonoidHom.comp_apply]
    have := hχ ⟨normUnits F E x, x, rfl⟩
    rw [this]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    have he : (QuotientGroup.quotientKerEquivRange (normUnits F E)).symm
        ⟨normUnits F E x, x, rfl⟩ = (x : Eˣ ⧸ (normUnits F E).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]

end Quadratic

section Filtration

open LocalGL1 ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The order of $0$ is $0$, by the convention of `Langlands.LocalGL1.ord`. -/
theorem ord_zero' : ord K (0 : K) = 0 := by
  simp [ord]

/-- The unit filtration $U^n_K$ (BH 1.8): $U^0_K = \mathcal{O}_K^\times$, and $U^n_K = 1 + \mathfrak{p}_K^n$ for $n \ge 1$. In both cases it is the group of the units $x$ with $\mathrm{ord}(x) = 0$ and $x - 1 \in \mathfrak{p}_K^n$. -/
def unitFilt (n : ℕ) : Subgroup Kˣ where
  carrier := {x | ord K (x : K) = 0 ∧ (x : K) - 1 ∈ ordBall K n}
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨by rw [Units.val_mul, ord_mul a.ne_zero b.ne_zero, ha0, hb0, add_zero], ?_⟩
    have haO : (a : K) ∈ ordBall K 0 := mem_ordBall_of_le a.ne_zero (by rw [ha0])
    have h1 := mul_mem_ordBall_add haO hb
    rw [zero_add] at h1
    have h2 := add_mem_ordBall h1 ha
    have he : (a : K) * (b - 1) + (a - 1) = (a * b : Kˣ) - 1 := by
      rw [Units.val_mul]
      ring
    rwa [he] at h2
  one_mem' := by
    refine ⟨by rw [Units.val_one, ord_one], ?_⟩
    rw [Units.val_one, sub_self]
    exact zero_mem_ordBall _
  inv_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by rw [Units.val_inv_eq_inv_val, ord_inv x.ne_zero, hx0, neg_zero], ?_⟩
    have hxO : ((x⁻¹ : Kˣ) : K) ∈ ordBall K 0 :=
      mem_ordBall_of_le (x⁻¹).ne_zero (by rw [Units.val_inv_eq_inv_val, ord_inv x.ne_zero, hx0,
        neg_zero])
    have h1 := neg_mem_ordBall (mul_mem_ordBall_add hxO hx)
    rw [zero_add] at h1
    have he : -(((x⁻¹ : Kˣ) : K) * (x - 1)) = ((x⁻¹ : Kˣ) : K) - 1 := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ x.ne_zero]
      ring
    rwa [he] at h1

variable {K}

/-- Membership in $U^n_K$. -/
theorem mem_unitFilt {n : ℕ} {x : Kˣ} :
    x ∈ unitFilt K n ↔ ord K (x : K) = 0 ∧ (x : K) - 1 ∈ ordBall K n := Iff.rfl

/-- The filtration is decreasing: $U^n_K \subseteq U^m_K$ for $m \le n$. -/
theorem unitFilt_anti {m n : ℕ} (h : m ≤ n) : unitFilt K n ≤ unitFilt K m :=
  fun _ hx => ⟨hx.1, ordBall_anti (by exact_mod_cast h) hx.2⟩

/-- Each $U^n_K$ is open in $K^\times$. -/
theorem isOpen_unitFilt (n : ℕ) : IsOpen (unitFilt K n : Set Kˣ) := by
  have hS : IsOpen (ordShell K 0 ∩ (fun y : K => y - 1) ⁻¹' ordBall K n) :=
    (isOpen_ordShell 0).inter ((isOpen_ordBall _).preimage (by fun_prop))
  have : (unitFilt K n : Set Kˣ) = Units.val ⁻¹' (ordShell K 0 ∩ (fun y : K => y - 1) ⁻¹' ordBall K n) := by
    ext x
    simp only [SetLike.mem_coe, mem_unitFilt, Set.mem_preimage, Set.mem_inter_iff, ordShell,
      Set.mem_ofPred_eq, x.ne_zero, ne_eq, not_false_eq_true, true_and]
  rw [this]
  exact hS.preimage Units.continuous_val

/-- **Smooth characters and the filtration.** A character $\chi$ of $K^\times$ is smooth exactly when it is trivial on $U^n_K$ for some $n$. -/
theorem isSmoothChar_iff_exists_unitFilt_le (χ : Kˣ →* ℂˣ) :
    IsSmoothChar K χ ↔ ∃ n, unitFilt K n ≤ χ.ker := by
  constructor
  · intro hχ
    by_cases hu : IsUnramifiedChar χ
    · refine ⟨0, fun x hx => hu x ?_⟩
      exact (normAbs_eq_one_iff x.ne_zero).2 hx.1
    · obtain ⟨a, ha⟩ := exists_isRamifiedConductor hχ hu
      exact ⟨a, fun x hx => ha.trivial x hx.2⟩
  · rintro ⟨n, hn⟩
    exact Subgroup.isOpen_mono hn (isOpen_unitFilt n)

/-- The character $\chi$ of $K^\times$ has level $n$ (BH 1.8): it is trivial on $U^{n+1}_K$ and not trivial on $U^n_K$. A character that is trivial on $U^0_K$ (an unramified character) has no level in this sense. -/
def IsLevel (χ : Kˣ →* ℂˣ) (n : ℕ) : Prop :=
  unitFilt K (n + 1) ≤ χ.ker ∧ ¬ unitFilt K n ≤ χ.ker

/-- The level is unique. -/
theorem IsLevel.unique {χ : Kˣ →* ℂˣ} {m n : ℕ} (hm : IsLevel χ m) (hn : IsLevel χ n) :
    m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hn.2 ((unitFilt_anti h).trans hm.1)
  · exact hm.2 ((unitFilt_anti h).trans hn.1)

/-- **Existence of the level.** A smooth character of $K^\times$ that is not trivial on $U^0_K$ has a level. -/
theorem exists_isLevel {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (h0 : ¬ unitFilt K 0 ≤ χ.ker) :
    ∃ n, IsLevel χ n := by
  classical
  obtain ⟨N, hN⟩ := (isSmoothChar_iff_exists_unitFilt_le χ).1 hχ
  have hP : ∃ n, unitFilt K (n + 1) ≤ χ.ker := ⟨N, (unitFilt_anti (Nat.le_succ N)).trans hN⟩
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  rcases hk : Nat.find hP with _ | k
  · exact h0
  · exact Nat.find_min hP (by omega : k < Nat.find hP)

open scoped Classical in
/-- The level $\ell(\chi)$ of a character $\chi$ of $K^\times$ (BH 1.8): the least $n \ge 0$ such that $\chi$ is trivial on $U^{n+1}_K$. The value is $0$ when no such $n$ exists. -/
noncomputable def level (χ : Kˣ →* ℂˣ) : ℕ :=
  if h : ∃ n, unitFilt K (n + 1) ≤ χ.ker then Nat.find h else 0

/-- A smooth character that is not trivial on $U^0_K$ has level $\ell(\chi)$. -/
theorem isLevel_level {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (h0 : ¬ unitFilt K 0 ≤ χ.ker) :
    IsLevel χ (level χ) := by
  classical
  obtain ⟨n, hn⟩ := exists_isLevel hχ h0
  have hP : ∃ n, unitFilt K (n + 1) ≤ χ.ker := ⟨n, hn.1⟩
  have h1 : level χ = Nat.find hP := dite_eq_left hP
  have h2 : Nat.find hP = n := by
    refine le_antisymm (Nat.find_min' hP hn.1) ?_
    by_contra hlt
    push Not at hlt
    exact hn.2 ((unitFilt_anti (by omega)).trans (Nat.find_spec hP))
  rw [h1, h2]
  exact hn

end Filtration

section LocalExtension

open LocalGL1 ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)]
variable {E' : Type*} [Field E'] [ValuativeRel E'] [TopologicalSpace E']
  [IsNonarchimedeanLocalField E'] [Algebra F E'] [FiniteDimensional F E'] [Algebra.IsSeparable F E']
  [Valuation.HasExtension (valuation F) (valuation E')]

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] in
/-- The orders on $E$ and on $F$ are compatible: $\mathrm{ord}_E(a) \le \mathrm{ord}_E(b)$ exactly when $\mathrm{ord}_F(a) \le \mathrm{ord}_F(b)$, for $a, b \in F^\times$. -/
theorem ord_algebraMap_le_iff {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord E (algebraMap F E a) ≤ ord E (algebraMap F E b) ↔ ord F a ≤ ord F b := by
  have ha' : algebraMap F E a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
  rw [← valuation_le_iff hb' ha', ← valuation_le_iff hb ha]
  exact Valuation.HasExtension.val_map_le_iff (valuation F) (valuation E) b a

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] in
/-- The order on $E$ of $a \in F$ is $\mathrm{ord}_E(a) = e \, \mathrm{ord}_F(a)$, with $e = \mathrm{ord}_E(\varpi_F)$. -/
theorem ord_algebraMap (a : F) :
    ord E (algebraMap F E a) = ord E (algebraMap F E (unif F : F)) * ord F a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, ord_zero', ord_zero', mul_zero]
  set u : Fˣ := Units.mk0 a ha * unif F ^ (-ord F a) with hu
  have hu0 : ord F (u : F) = 0 := ord_mul_unif_zpow (Units.mk0 a ha)
  have hu1 : ord E (algebraMap F E (u : F)) = 0 := by
    have h1 := ord_algebraMap_le_iff (E := E) u.ne_zero one_ne_zero
    have h2 := ord_algebraMap_le_iff (E := E) one_ne_zero u.ne_zero
    rw [map_one, ord_one, ord_one, hu0] at h1 h2
    exact le_antisymm (h1.2 le_rfl) (h2.2 le_rfl)
  have hau : a = (u : F) * (unif F : F) ^ ord F a := by
    rw [hu, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, mul_assoc, ← zpow_add₀
      (unif F).ne_zero, neg_add_cancel, zpow_zero, mul_one]
  conv_lhs => rw [hau]
  rw [map_mul, map_zpow₀, ord_mul ((map_ne_zero _).2 u.ne_zero)
    (zpow_ne_zero _ ((map_ne_zero _).2 (unif F).ne_zero)), hu1, ord_zpow, zero_add, mul_comm]

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] in
/-- The number $e = \mathrm{ord}_E(\varpi_F)$ is positive. -/
theorem ord_algebraMap_unif_pos : 0 < ord E (algebraMap F E (unif F : F)) := by
  have h := ord_algebraMap_le_iff (E := E) (unif F).ne_zero one_ne_zero
  rw [map_one, ord_one, ord_one, ord_unif] at h
  by_contra hc
  push Not at hc
  have := h.1 hc
  omega

omit [Valuation.HasExtension (valuation F) (valuation E')] in
/-- An $F$-isomorphism $j : E \to E'$ sends $\mathcal{O}_E$ into $\mathcal{O}_{E'}$, because $\mathcal{O}_E$ is the integral closure of $\mathcal{O}_F$ in $E$. -/
theorem map_mem_integer (j : E ≃ₐ[F] E') [Valuation.HasExtension (valuation F) (valuation E')]
    {x : E} (hx : x ∈ 𝒪[E]) : j x ∈ 𝒪[E'] := by
  have h1 := LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E
  have h2 := LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E'
  have hi : IsIntegral 𝒪[F] x := h1.isIntegral_iff.2 ⟨⟨x, hx⟩, rfl⟩
  have hj : IsIntegral 𝒪[F] (j x) := hi.map (j.toAlgHom.restrictScalars 𝒪[F])
  obtain ⟨y, hy⟩ := h2.isIntegral_iff.1 hj
  rw [← hy]
  exact y.2

/-- An $F$-isomorphism $j$ preserves the order relation: $\mathrm{ord}(j x) \le \mathrm{ord}(j y)$ exactly when $\mathrm{ord}(x) \le \mathrm{ord}(y)$. -/
theorem ord_map_le_iff (j : E ≃ₐ[F] E') {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord E' (j x) ≤ ord E' (j y) ↔ ord E x ≤ ord E y := by
  have key : ∀ {z : E}, z ≠ 0 → (0 ≤ ord E' (j z) ↔ 0 ≤ ord E z) := by
    intro z hz
    have hjz : j z ≠ 0 := (map_ne_zero j).2 hz
    constructor
    · intro h
      have := map_mem_integer j.symm ((valuation_le_one_iff hjz).2 h)
      rw [AlgEquiv.symm_apply_apply] at this
      exact (valuation_le_one_iff hz).1 this
    · intro h
      exact (valuation_le_one_iff hjz).1 (map_mem_integer j ((valuation_le_one_iff hz).2 h))
  have hyx : y / x ≠ 0 := div_ne_zero hy hx
  have h := key hyx
  rw [map_div₀, div_eq_mul_inv, div_eq_mul_inv, ord_mul ((map_ne_zero j).2 hy)
    (inv_ne_zero ((map_ne_zero j).2 hx)), ord_inv ((map_ne_zero j).2 hx), ord_mul hy
    (inv_ne_zero hx), ord_inv hx] at h
  constructor
  · intro h'
    have := h.1 (by omega)
    omega
  · intro h'
    have := h.2 (by omega)
    omega

/-- **An $F$-isomorphism preserves the order.** For an $F$-isomorphism $j : E \to E'$ of finite separable extensions of $F$, $\mathrm{ord}_{E'}(j x) = \mathrm{ord}_E(x)$. The reason is that the valuation of $E$ is the unique extension of the valuation of $F$. -/
theorem ord_map (j : E ≃ₐ[F] E') (x : E) : ord E' (j x) = ord E x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, ord_zero', ord_zero']
  have hπ : (unif E : E) ≠ 0 := (unif E).ne_zero
  have hk1 : 1 ≤ ord E' (j (unif E : E)) := by
    have h := ord_map_le_iff j hπ one_ne_zero
    rw [map_one, ord_one, ord_one, ord_unif] at h
    by_contra hc
    exact absurd (h.1 (by omega)) (by omega)
  have hk2 : ord E' (j (unif E : E)) ≤ 1 := by
    set y := j.symm (unif E' : E') with hy
    have hy0 : y ≠ 0 := by simp [hy]
    have hjy : j y = unif E' := by simp [hy]
    have h := ord_map_le_iff j hy0 one_ne_zero
    rw [map_one, ord_one, ord_one, hjy, ord_unif] at h
    have hy1 : 1 ≤ ord E y := by
      by_contra hc
      exact absurd (h.2 (by omega)) (by omega)
    have h' := (ord_map_le_iff j hπ hy0).2 (by rw [ord_unif]; exact hy1)
    rwa [hjy, ord_unif] at h'
  have hk : ord E' (j (unif E : E)) = 1 := le_antisymm hk2 hk1
  set u : Eˣ := Units.mk0 x hx * unif E ^ (-ord E x) with hu
  have hu0 : ord E (u : E) = 0 := ord_mul_unif_zpow (Units.mk0 x hx)
  have hu1 : ord E' (j (u : E)) = 0 := by
    have h1 := ord_map_le_iff j u.ne_zero one_ne_zero
    have h2 := ord_map_le_iff j one_ne_zero u.ne_zero
    rw [map_one, ord_one, ord_one, hu0] at h1 h2
    exact le_antisymm (h1.2 le_rfl) (h2.2 le_rfl)
  have hxu : x = (u : E) * (unif E : E) ^ ord E x := by
    rw [hu, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, mul_assoc, ← zpow_add₀ hπ,
      neg_add_cancel, zpow_zero, mul_one]
  conv_lhs => rw [hxu]
  rw [map_mul, map_zpow₀, ord_mul ((map_ne_zero j).2 u.ne_zero)
    (zpow_ne_zero _ ((map_ne_zero j).2 hπ)), hu1, ord_zpow, hk, zero_add, mul_one]

/-- An $F$-isomorphism $j$ preserves the balls: $j(z) \in \mathfrak{p}_{E'}^N$ exactly when $z \in \mathfrak{p}_E^N$. -/
theorem map_mem_ordBall_iff (j : E ≃ₐ[F] E') (z : E) (N : ℤ) :
    j z ∈ ordBall E' N ↔ z ∈ ordBall E N := by
  simp only [ordBall, Set.mem_ofPred_eq, map_eq_zero_iff j j.injective, ord_map]

/-- An $F$-isomorphism $j$ preserves the filtration: $j(x) \in U^n_{E'}$ exactly when $x \in U^n_E$. -/
theorem unitsMap_mem_unitFilt_iff (j : E ≃ₐ[F] E') (x : Eˣ) (n : ℕ) :
    unitsMap j x ∈ unitFilt E' n ↔ x ∈ unitFilt E n := by
  rw [mem_unitFilt, mem_unitFilt, val_unitsMap, ord_map, ← map_mem_ordBall_iff j, map_sub, map_one]

end LocalExtension

section Admissible

open LocalGL1 ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E]

/-- The extension $E/F$ is unramified: $\mathrm{ord}_E(a) = \mathrm{ord}_F(a)$ for each $a \in F$, that is $e(E|F) = 1$. -/
def IsUnramifiedExt : Prop :=
  ∀ a : F, ord E (algebraMap F E a) = ord F a

/-- The extension $E/F$ is totally ramified of degree $2$: $\mathrm{ord}_E(a) = 2 \, \mathrm{ord}_F(a)$ for each $a \in F$, that is $e(E|F) = 2$. -/
def IsTotallyRamifiedExt : Prop :=
  ∀ a : F, ord E (algebraMap F E a) = 2 * ord F a

variable {F E} in
/-- A totally ramified extension is not unramified. -/
theorem IsTotallyRamifiedExt.not_isUnramifiedExt (h : IsTotallyRamifiedExt F E) :
    ¬ IsUnramifiedExt F E := by
  intro hu
  have h1 := h (unif F)
  rw [hu, ord_unif] at h1
  omega

/-- The quadratic extension $E/F$ is tamely ramified: the residue characteristic $p$ of $F$ is not $2$, or $E/F$ is unramified. For a quadratic extension $e(E|F) \in \{1, 2\}$, so this is the condition that $p$ does not divide $e(E|F)$. -/
def IsTameQuadratic : Prop :=
  (2 : 𝓀[F]) ≠ 0 ∨ IsUnramifiedExt F E

/-- **Admissible pairs** (BH 18.2). Let $E/F$ be a tamely ramified quadratic extension. A character $\xi$ of $E^\times$ is admissible over $F$ when it is smooth and has these two properties.

1. $\xi$ does not factor through the norm map $N_{E/F} : E^\times \to F^\times$.
2. If the restriction of $\xi$ to $U^1_E$ factors through $N_{E/F}$, then $E/F$ is unramified.

A character of $U^1_E$ factors through $N_{E/F}$ when it is $\varphi \circ N_{E/F}$ for a character $\varphi$ of $F^\times$. -/
structure IsAdmissible (ξ : Eˣ →* ℂˣ) : Prop where
  /-- The character $\xi$ is smooth. -/
  smooth : IsSmoothChar E ξ
  /-- The character $\xi$ does not factor through $N_{E/F}$. -/
  not_factor : ¬ ∃ χ : Fˣ →* ℂˣ, ξ = χ.comp (normUnits F E)
  /-- If $\xi$ on $U^1_E$ factors through $N_{E/F}$, then $E/F$ is unramified. -/
  unramified_of_factor :
    (∃ φ : Fˣ →* ℂˣ, ∀ u ∈ unitFilt E 1, ξ u = φ (normUnits F E u)) → IsUnramifiedExt F E

/-- The twist $\xi \otimes \chi_E$ of a character $\xi$ of $E^\times$ by a character $\chi$ of $F^\times$ (BH 18.2): the character $x \mapsto \xi(x) \chi(N_{E/F}(x))$. -/
noncomputable def twistChar (ξ : Eˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) : Eˣ →* ℂˣ :=
  ξ * χ.comp (normUnits F E)

variable {F E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The twist has the value $\xi(x) \chi(N_{E/F}(x))$. -/
@[simp]
theorem twistChar_apply (ξ : Eˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (x : Eˣ) :
    twistChar F E ξ χ x = ξ x * χ (normUnits F E x) := rfl

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)]
variable {E' : Type*} [Field E'] [ValuativeRel E'] [TopologicalSpace E']
  [IsNonarchimedeanLocalField E'] [Algebra F E'] [FiniteDimensional F E'] [Algebra.IsSeparable F E']
  [Valuation.HasExtension (valuation F) (valuation E')]

/-- An $F$-isomorphism $j : E \to E'$ preserves the ramification: if $E'/F$ is unramified, then $E/F$ is unramified. -/
theorem IsUnramifiedExt.of_algEquiv (j : E ≃ₐ[F] E') (h : IsUnramifiedExt F E') :
    IsUnramifiedExt F E := by
  intro a
  rw [← ord_map j, AlgEquiv.commutes, h]

/-- **Transport of admissibility.** If $j : E \to E'$ is an $F$-isomorphism and $(E'/F, \xi')$ is admissible, then $(E/F, \xi' \circ j)$ is admissible. -/
theorem IsAdmissible.comp_unitsMap {ξ' : E'ˣ →* ℂˣ} (h : IsAdmissible F E' ξ') (j : E ≃ₐ[F] E') :
    IsAdmissible F E (ξ'.comp (unitsMap j)) where
  smooth := by
    obtain ⟨n, hn⟩ := (isSmoothChar_iff_exists_unitFilt_le ξ').1 h.smooth
    refine (isSmoothChar_iff_exists_unitFilt_le _).2 ⟨n, fun x hx => ?_⟩
    exact hn ((unitsMap_mem_unitFilt_iff j x n).2 hx)
  not_factor := by
    rintro ⟨χ, hχ⟩
    refine h.not_factor ⟨χ, MonoidHom.ext fun y => ?_⟩
    have h1 := DFunLike.congr_fun hχ (unitsMap j.symm y)
    have h2 : unitsMap j (unitsMap j.symm y) = y := Units.ext (by simp)
    have h3 : normUnits F E (unitsMap j.symm y) = normUnits F E' y :=
      DFunLike.congr_fun (normUnits_comp_unitsMap j.symm) y
    simpa [h2, h3] using h1
  unramified_of_factor := by
    rintro ⟨φ, hφ⟩
    refine IsUnramifiedExt.of_algEquiv j (h.unramified_of_factor ⟨φ, fun u hu => ?_⟩)
    have hu' : unitsMap j.symm u ∈ unitFilt E 1 := by
      rw [← unitsMap_mem_unitFilt_iff j, show unitsMap j (unitsMap j.symm u) = u from
        Units.ext (by simp)]
      exact hu
    have h1 := hφ _ hu'
    have h2 : unitsMap j (unitsMap j.symm u) = u := Units.ext (by simp)
    have h3 : normUnits F E (unitsMap j.symm u) = normUnits F E' u :=
      DFunLike.congr_fun (normUnits_comp_unitsMap j.symm) u
    simpa [h2, h3] using h1

/-- **Admissibility is invariant under isomorphism.** For an $F$-isomorphism $j : E \to E'$, $(E'/F, \xi')$ is admissible exactly when $(E/F, \xi' \circ j)$ is admissible. -/
theorem isAdmissible_comp_unitsMap_iff (ξ' : E'ˣ →* ℂˣ) (j : E ≃ₐ[F] E') :
    IsAdmissible F E (ξ'.comp (unitsMap j)) ↔ IsAdmissible F E' ξ' := by
  refine ⟨fun h => ?_, fun h => h.comp_unitsMap j⟩
  have h' := h.comp_unitsMap j.symm
  have he : (ξ'.comp (unitsMap j)).comp (unitsMap j.symm) = ξ' :=
    MonoidHom.ext fun y => by simp [show unitsMap j (unitsMap j.symm y) = y from Units.ext (by simp)]
  rwa [he] at h'

/-- **The norm on the filtration.** Let $e = \mathrm{ord}_E(\varpi_F)$. Then $N_{E/F}(U^{e m}_E) \subseteq U^m_F$. The proof writes $x = 1 + z$, so that $N_{E/F}(x) - 1 = z + \sigma(z) + z \sigma(z)$. -/
theorem normUnits_mem_unitFilt [Algebra.IsQuadraticExtension F E] {m : ℕ} {x : Eˣ}
    (hx : x ∈ unitFilt E ((ord E (algebraMap F E (unif F : F))).toNat * m)) :
    normUnits F E x ∈ unitFilt F m := by
  set e := ord E (algebraMap F E (unif F : F)) with he
  have he0 : 0 < e := ord_algebraMap_unif_pos
  have hcast : (((e.toNat * m : ℕ)) : ℤ) = e * m := by
    rw [Nat.cast_mul, Int.toNat_of_nonneg he0.le]
  obtain ⟨hx0, hx1⟩ := hx
  rw [hcast] at hx1
  set z : E := (x : E) - 1 with hz
  have hσz : galConj F E z ∈ ordBall E (e * m) := (map_mem_ordBall_iff (galConj F E) z _).2 hx1
  have hzz : z * galConj F E z ∈ ordBall E (e * m) := by
    have := mul_mem_ordBall_add hx1 hσz
    exact ordBall_anti (by nlinarith) this
  have hw : algebraMap F E ((normUnits F E x : F) - 1) = z + galConj F E z + z * galConj F E z := by
    rw [map_sub, map_one, val_normUnits, algebraMap_norm_eq_mul, hz, map_sub, map_one]
    ring
  have hwmem : algebraMap F E ((normUnits F E x : F) - 1) ∈ ordBall E (e * m) := by
    rw [hw]
    exact add_mem_ordBall (add_mem_ordBall hx1 hσz) hzz
  refine ⟨?_, ?_⟩
  · have h1 := ord_algebraMap (E := E) (normUnits F E x : F)
    rw [val_normUnits, algebraMap_norm_eq_mul, ord_mul x.ne_zero (by simp), ord_map, hx0,
      add_zero, ← he] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · omega
    · exact h
  · by_cases h0 : (normUnits F E x : F) - 1 = 0
    · rw [h0]
      exact zero_mem_ordBall _
    · refine (mem_ordBall_of_ne_zero h0).2 ?_
      have h1 := (mem_ordBall_of_ne_zero ((map_ne_zero _).2 h0)).1 hwmem
      rw [ord_algebraMap, ← he] at h1
      exact le_of_mul_le_mul_left h1 he0

/-- If $\chi$ is a smooth character of $F^\times$, then $\chi \circ N_{E/F}$ is a smooth character of $E^\times$. -/
theorem isSmoothChar_comp_normUnits [Algebra.IsQuadraticExtension F E] {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar F χ) : IsSmoothChar E (χ.comp (normUnits F E)) := by
  obtain ⟨m, hm⟩ := (isSmoothChar_iff_exists_unitFilt_le χ).1 hχ
  exact (isSmoothChar_iff_exists_unitFilt_le _).2 ⟨(ord E (algebraMap F E (unif F : F))).toNat * m,
    fun x hx => hm (normUnits_mem_unitFilt hx)⟩

/-- **The twist of an admissible pair is admissible** (BH 18.2). If $(E/F, \xi)$ is admissible and $\chi$ is a smooth character of $F^\times$, then $(E/F, \xi \otimes \chi_E)$ is admissible, with $\chi_E = \chi \circ N_{E/F}$. -/
theorem IsAdmissible.twist [Algebra.IsQuadraticExtension F E] {ξ : Eˣ →* ℂˣ}
    (h : IsAdmissible F E ξ) {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar F χ) :
    IsAdmissible F E (twistChar F E ξ χ) where
  smooth := by
    obtain ⟨n, hn⟩ := (isSmoothChar_iff_exists_unitFilt_le ξ).1 h.smooth
    obtain ⟨k, hk⟩ := (isSmoothChar_iff_exists_unitFilt_le _).1
      (isSmoothChar_comp_normUnits (E := E) hχ)
    refine (isSmoothChar_iff_exists_unitFilt_le _).2 ⟨max n k, fun x hx => ?_⟩
    have h1 : ξ x = 1 := hn (unitFilt_anti (le_max_left n k) hx)
    have h2 : χ (normUnits F E x) = 1 := hk (unitFilt_anti (le_max_right n k) hx)
    rw [MonoidHom.mem_ker, twistChar_apply, h1, h2, mul_one]
  not_factor := by
    rintro ⟨χ', hχ'⟩
    refine h.not_factor ⟨χ' * χ⁻¹, MonoidHom.ext fun x => ?_⟩
    have := DFunLike.congr_fun hχ' x
    rw [twistChar_apply, MonoidHom.comp_apply] at this
    rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, ← this]
    group
  unramified_of_factor := by
    rintro ⟨φ, hφ⟩
    refine h.unramified_of_factor ⟨φ * χ⁻¹, fun u hu => ?_⟩
    have := hφ u hu
    rw [twistChar_apply] at this
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ← this]
    group

omit [FiniteDimensional F E] [Valuation.HasExtension (valuation F) (valuation E)] in
/-- **Regularity of admissible characters** (BH 18.2). If $(E/F, \xi)$ is admissible, then $\xi \ne \xi \circ \sigma$, where $\sigma$ is the Galois conjugation of $E/F$. The proof uses Hilbert's Theorem 90: a character with $\xi = \xi \circ \sigma$ is trivial on the kernel of $N_{E/F}$, so it factors through $N_{E/F}$. -/
theorem IsAdmissible.comp_galConjUnits_ne [Algebra.IsQuadraticExtension F E] {ξ : Eˣ →* ℂˣ}
    (h : IsAdmissible F E ξ) : ξ.comp (galConjUnits F E) ≠ ξ :=
  fun he => h.not_factor ((exists_eq_comp_normUnits_iff ξ).2 he)

/-- **The conjugate of an admissible pair is admissible** (BH 18.2). If $(E/F, \xi)$ is admissible, then $(E/F, \xi \circ \sigma)$ is admissible. -/
theorem IsAdmissible.comp_galConjUnits [Algebra.IsQuadraticExtension F E] {ξ : Eˣ →* ℂˣ}
    (h : IsAdmissible F E ξ) : IsAdmissible F E (ξ.comp (galConjUnits F E)) :=
  h.comp_unitsMap (galConj F E)

omit [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- **Admissible characters in the ramified case.** If $E/F$ is totally ramified and $(E/F, \xi)$ is admissible, then $\xi$ is not trivial on $U^1_E$. -/
theorem IsAdmissible.not_unitFilt_one_le_ker {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ)
    (hr : IsTotallyRamifiedExt F E) : ¬ unitFilt E 1 ≤ ξ.ker := by
  intro hle
  refine hr.not_isUnramifiedExt (h.unramified_of_factor ⟨1, fun u hu => ?_⟩)
  rw [MonoidHom.one_apply]
  exact hle hu

omit [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Valuation.HasExtension (valuation F) (valuation E)] in
/-- **The level in the ramified case.** If $E/F$ is totally ramified and $(E/F, \xi)$ is admissible, then $\xi$ has level $\ell(\xi) \ge 1$. -/
theorem IsAdmissible.isLevel_level_of_ramified {ξ : Eˣ →* ℂˣ} (h : IsAdmissible F E ξ)
    (hr : IsTotallyRamifiedExt F E) : IsLevel ξ (level ξ) ∧ 1 ≤ level ξ := by
  have h1 := h.not_unitFilt_one_le_ker hr
  have hl := isLevel_level h.smooth fun h0 => h1 ((unitFilt_anti (Nat.zero_le 1)).trans h0)
  refine ⟨hl, ?_⟩
  by_contra h0
  push Not at h0
  have : level ξ = 0 := by omega
  rw [this] at hl
  exact h1 hl.1

end Admissible

section Bundled

open LocalGL1 ValuativeRel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {F} in
/-- If $2 \ne 0$ in the residue field of $F$, then $2 \ne 0$ in $F$. -/
theorem two_ne_zero_of_residue (h : (2 : 𝓀[F]) ≠ 0) : (2 : F) ≠ 0 := by
  intro h0
  apply h
  have h2 : (2 : 𝒪[F]) = 0 := Subtype.val_injective (by
    change 𝒪[F].subtype 2 = 𝒪[F].subtype 0
    rw [map_ofNat, map_zero]
    exact h0)
  rw [← map_ofNat (IsLocalRing.residue 𝒪[F]) 2, h2, map_zero]

/-- A tamely ramified quadratic extension $E/F$ of nonarchimedean local fields (BH 18.1). The field $E$ is a nonarchimedean local field with an $F$-algebra structure of dimension $2$, its valuation extends the valuation of $F$, $E/F$ is separable, and $E/F$ is tamely ramified (`Langlands.LocalGL2.IsTameQuadratic`). If $p \ne 2$, then the separability and the tameness are automatic, by `Langlands.LocalGL2.isSeparable_of_two_ne_zero`. -/
structure TameQuadExt where
  /-- The field $E$. -/
  E : Type u
  /-- The field structure of $E$. -/
  [instField : Field E]
  /-- The valuation of $E$. -/
  [instValuativeRel : ValuativeRel E]
  /-- The topology of $E$. -/
  [instTopologicalSpace : TopologicalSpace E]
  /-- The field $E$ is a nonarchimedean local field. -/
  [instLocalField : IsNonarchimedeanLocalField E]
  /-- The $F$-algebra structure of $E$. -/
  [instAlgebra : Algebra F E]
  /-- The extension $E/F$ is quadratic. -/
  [instQuadratic : Algebra.IsQuadraticExtension F E]
  /-- The extension $E/F$ is separable. -/
  [instSeparable : Algebra.IsSeparable F E]
  /-- The valuation of $E$ extends the valuation of $F$. -/
  [instHasExtension : Valuation.HasExtension (valuation F) (valuation E)]
  /-- The extension $E/F$ is tamely ramified. -/
  tame : IsTameQuadratic F E

attribute [instance] TameQuadExt.instField TameQuadExt.instValuativeRel
  TameQuadExt.instTopologicalSpace TameQuadExt.instLocalField TameQuadExt.instAlgebra
  TameQuadExt.instQuadratic TameQuadExt.instSeparable TameQuadExt.instHasExtension

/-- **Admissible pairs** (BH 18.2). An admissible pair $(E/F, \xi)$ is a tamely ramified quadratic extension $E/F$ and a character $\xi$ of $E^\times$ that is admissible over $F$ (`Langlands.LocalGL2.IsAdmissible`). -/
structure AdmissiblePair where
  /-- The tamely ramified quadratic extension $E/F$. -/
  ext : TameQuadExt F
  /-- The character $\xi$ of $E^\times$. -/
  ξ : ext.Eˣ →* ℂˣ
  /-- The character $\xi$ is admissible. -/
  admissible : IsAdmissible F ext.E ξ

namespace AdmissiblePair

variable {F}

/-- **Isomorphism of admissible pairs** (BH 18.2). The pairs $(E/F, \xi)$ and $(E'/F, \xi')$ are $F$-isomorphic when there is an $F$-isomorphism $j : E \to E'$ with $\xi = \xi' \circ j$. -/
def Iso (P Q : AdmissiblePair F) : Prop :=
  ∃ j : P.ext.E ≃ₐ[F] Q.ext.E, P.ξ = Q.ξ.comp (unitsMap j)

/-- Each admissible pair is isomorphic to itself. -/
theorem Iso.refl (P : AdmissiblePair F) : P.Iso P :=
  ⟨AlgEquiv.refl, MonoidHom.ext fun x => by
    rw [MonoidHom.comp_apply]
    exact congrArg P.ξ (Units.ext rfl)⟩

/-- Isomorphism of admissible pairs is symmetric. -/
theorem Iso.symm {P Q : AdmissiblePair F} (h : P.Iso Q) : Q.Iso P := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j.symm, MonoidHom.ext fun y => ?_⟩
  rw [MonoidHom.comp_apply, hj, MonoidHom.comp_apply]
  exact congrArg Q.ξ (Units.ext (by simp))

/-- Isomorphism of admissible pairs is transitive. -/
theorem Iso.trans {P Q R : AdmissiblePair F} (h₁ : P.Iso Q) (h₂ : Q.Iso R) : P.Iso R := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  refine ⟨j.trans k, MonoidHom.ext fun x => ?_⟩
  rw [hj, MonoidHom.comp_apply, hk, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rfl

/-- **Isomorphism of admissible pairs is an equivalence relation** (BH 18.2). -/
theorem iso_equivalence : Equivalence (Iso (F := F)) :=
  ⟨Iso.refl, Iso.symm, Iso.trans⟩

/-- The setoid of admissible pairs up to $F$-isomorphism. -/
instance setoid : Setoid (AdmissiblePair F) :=
  ⟨Iso, iso_equivalence⟩

/-- The conjugate pair $(E/F, \xi \circ \sigma)$ of an admissible pair $(E/F, \xi)$, where $\sigma$ is the Galois conjugation of $E/F$. -/
noncomputable def conj (P : AdmissiblePair F) : AdmissiblePair F where
  ext := P.ext
  ξ := P.ξ.comp (galConjUnits F P.ext.E)
  admissible := P.admissible.comp_galConjUnits

/-- **The conjugate pair is isomorphic to the pair** (BH 18.2): $(E/F, \xi) \cong (E/F, \xi \circ \sigma)$, by the $F$-isomorphism $\sigma$. -/
theorem iso_conj (P : AdmissiblePair F) : P.Iso P.conj := by
  refine ⟨galConj F P.ext.E, MonoidHom.ext fun x => ?_⟩
  change P.ξ x = P.ξ (galConjUnits F P.ext.E (unitsMap (galConj F P.ext.E) x))
  exact congrArg P.ξ (Units.ext (galConj_galConj (x : P.ext.E)).symm)

/-- **Regularity** (BH 18.2). The character of an admissible pair is regular: $\xi \circ \sigma \ne \xi$. -/
theorem conj_ξ_ne (P : AdmissiblePair F) : P.conj.ξ ≠ P.ξ :=
  P.admissible.comp_galConjUnits_ne

/-- **The twist of an admissible pair** (BH 18.2): $(E/F, \xi \otimes \chi_E)$ for a smooth character $\chi$ of $F^\times$, with $\chi_E = \chi \circ N_{E/F}$. It is admissible by `Langlands.LocalGL2.IsAdmissible.twist`. -/
noncomputable def twist (P : AdmissiblePair F) (χ : Fˣ →* ℂˣ) (hχ : IsSmoothChar F χ) :
    AdmissiblePair F where
  ext := P.ext
  ξ := twistChar F P.ext.E P.ξ χ
  admissible := P.admissible.twist hχ

/-- **The twist is compatible with isomorphism** (BH 18.2). If $(E/F, \xi) \cong (E'/F, \xi')$, then $(E/F, \xi \otimes \chi_E) \cong (E'/F, \xi' \otimes \chi_{E'})$. -/
theorem Iso.twist {P Q : AdmissiblePair F} (h : P.Iso Q) (χ : Fˣ →* ℂˣ)
    (hχ : IsSmoothChar F χ) : (P.twist χ hχ).Iso (Q.twist χ hχ) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, MonoidHom.ext fun (x : P.ext.Eˣ) => ?_⟩
  change twistChar F P.ext.E P.ξ χ x = twistChar F Q.ext.E Q.ξ χ (unitsMap j x)
  rw [twistChar_apply, twistChar_apply, hj, MonoidHom.comp_apply]
  congr 2
  exact (DFunLike.congr_fun (normUnits_comp_unitsMap j) x).symm

end AdmissiblePair

end Bundled

end Langlands.LocalGL2
