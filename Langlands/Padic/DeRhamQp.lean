/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.DeRham
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The de Rham period ring of $\mathbb{C}_p$ and de Rham representations of $G_{\mathbb{Q}_p}$

This file continues `Langlands.Padic.DeRham`. Let $p$ be a prime and let $R$ be a $p$-adically complete ring in which $p$ is not a unit. The file first gives $B_{dR}^+(R)$ and $B_{dR}(R)$ the structure of $\mathbb{Q}_p$-algebras. The map $\mathbb{Z}_p \cong W(\mathbb{F}_p) \to W(R^\flat)$ comes from the unique ring homomorphism $\mathbb{F}_p \to R^\flat$. It extends to $\mathbb{Q}_p \to W(R^\flat)[1/p]$, because each nonzero $p$-adic integer is a unit times a power of $p$. This map commutes with the maps of $B_{dR}^+$ and $B_{dR}$ of ring homomorphisms, so the action of a group on $R$ commutes with the scalars of $\mathbb{Q}_p$.

Then the file makes the absolute Galois group $G_{\mathbb{Q}_p}$ act on $\mathbb{C}_p$ and on $\mathcal{O}_{\mathbb{C}_p}$. Each $\sigma \in G_{\mathbb{Q}_p}$ preserves the spectral norm of $\overline{\mathbb{Q}}_p$, so it is uniformly continuous and it extends to the completion $\mathbb{C}_p$. The extension preserves the norm, so it preserves $\mathcal{O}_{\mathbb{C}_p}$. The file also proves that $p$ is not a unit in $\mathcal{O}_{\mathbb{C}_p}$ and that $\mathcal{O}_{\mathbb{C}_p}$ is $p$-adically complete. Thus $G_{\mathbb{Q}_p}$ acts on $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$, and the condition to be de Rham has no more hypotheses for representations of $G_{\mathbb{Q}_p}$ over $\mathbb{Q}_p$.

## Main definitions

* `Langlands.Padic.zpToWitt`: the map $\mathbb{Z}_p \to W(R^\flat)$.
* `Langlands.Padic.qpToLoc`, `Langlands.Padic.qpToBdrPlus`: the maps $\mathbb{Q}_p \to W(R^\flat)[1/p]$ and $\mathbb{Q}_p \to B_{dR}^+(R)$.
* `Langlands.Padic.bdrPlusQpAlgebra`, `Langlands.Padic.bdrQpAlgebra`: the $\mathbb{Q}_p$-algebra structures on $B_{dR}^+(R)$ and on $B_{dR}(R)$.
* `Langlands.Padic.galoisCp`: the extension of $\sigma \in G_{\mathbb{Q}_p}$ to $\mathbb{C}_p$.
* `Langlands.Padic.galoisIntAction`: the action of $G_{\mathbb{Q}_p}$ on $\mathcal{O}_{\mathbb{C}_p}$.
* `Langlands.Padic.IsContinuousRep`: a representation of $G_{\mathbb{Q}_p}$ on a $\mathbb{Q}_p$-vector space is continuous.
* `Langlands.Padic.IsDeRhamQp`: a representation of $G_{\mathbb{Q}_p}$ on a finite-dimensional $\mathbb{Q}_p$-vector space is de Rham.

## Main results

* `Langlands.Padic.bdrPlusMap_comp_qpToBdrPlus`, `Langlands.Padic.bdrMap_algebraMap_qp`: the maps of $B_{dR}^+$ and $B_{dR}$ are $\mathbb{Q}_p$-linear.
* `Langlands.Padic.bdrPlus_smulCommClass`, `Langlands.Padic.bdr_smulCommClass`: the group action commutes with the scalars of $\mathbb{Q}_p$.
* `Langlands.Padic.norm_galoisCp`: the extension of $\sigma$ to $\mathbb{C}_p$ preserves the norm.
* `Langlands.Padic.fact_not_isUnit_p`: $p$ is not a unit in $\mathcal{O}_{\mathbb{C}_p}$.
* `Langlands.Padic.isAdicComplete_padicComplexInt`: $\mathcal{O}_{\mathbb{C}_p}$ is $p$-adically complete.
* `Langlands.Padic.nontrivial_bdrPlus_padicComplexInt`: $B_{dR}^+(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring.
* `Langlands.Padic.isContinuousRep_trivial`: the trivial representation is continuous.
* `Langlands.Padic.isDeRhamQp_trivial_of_nontrivial`: if $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation is de Rham.

## Implementation notes

The ring $B_{dR}(R)$ of Mathlib is the localization of $B_{dR}^+(R)$ at the generators of $\ker \theta[1/p]$. This file does not prove that $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring. A proof needs that $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$ is a domain and that $\ker \theta[1/p]$ is not zero, for example with the element $[\varepsilon] - 1$. For this reason the de Rham property of the trivial representation has this hypothesis. The de Rham property of a representation with finite image needs Galois descent for $B_{dR}$ and the theorem of Ax, Sen and Tate, and this file does not prove it.

The predicate `IsDeRhamQp` does not use the continuity of the representation. The continuity is the separate predicate `IsContinuousRep`, for the module topology on $V$.

## References

* J.-M. Fontaine, Le corps des périodes p-adiques, Astérisque 223 (1994).
* O. Brinon and B. Conrad, CMI summer school notes on p-adic Hodge theory, sections 4 and 6.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

section Qp

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S : Type u} [CommRing S]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The map $\mathbb{Z}_p \cong W(\mathbb{F}_p) \to W(R^\flat)$. -/
noncomputable def zpToWitt (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)] :
    ℤ_[p] →+* WittVector p (PreTilt R p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt R p))).comp
    (WittVector.equiv (p := p)).symm.toRingHom

/-- The map $\mathbb{Z}_p \to W(\cdot^\flat)$ commutes with the map of a ring homomorphism. -/
theorem wittMap_comp_zpToWitt (f : R →+* S) :
    (wittMap p f).comp (zpToWitt R p) = zpToWitt S p := by
  have h : (WittVector.map (p := p) (preTiltMap p f)).comp
      (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt R p))) =
        WittVector.map ((preTiltMap p f).comp (ZMod.castHom (dvd_refl p) (PreTilt R p))) := by
    ext x n
    simp
  rw [zpToWitt, zpToWitt, ← RingHom.comp_assoc, wittMap, h,
    Subsingleton.elim ((preTiltMap p f).comp (ZMod.castHom (dvd_refl p) (PreTilt R p)))]

/-- Each nonzero $p$-adic integer is a unit in $W(R^\flat)[1/p]$. -/
theorem isUnit_zpToLoc (y : nonZeroDivisors ℤ_[p]) :
    IsUnit (((algebraMap _ (Localization.Away (p : WittVector p (PreTilt R p)))).comp
      (zpToWitt R p)) y) := by
  have hy : (y : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero y
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_pow, map_natCast]
  refine ((Units.isUnit _).map _).mul (IsUnit.pow _ ?_)
  simpa using IsLocalization.Away.algebraMap_isUnit (p : WittVector p (PreTilt R p))

/-- The map $\mathbb{Q}_p \to W(R^\flat)[1/p]$ that extends $\mathbb{Z}_p \to W(R^\flat)$. -/
noncomputable def qpToLoc (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] : ℚ_[p] →+* Localization.Away (p : WittVector p (PreTilt R p)) :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) isUnit_zpToLoc

/-- The map $\mathbb{Q}_p \to W(R^\flat)[1/p]$ extends $\mathbb{Z}_p \to W(R^\flat)$. -/
theorem qpToLoc_algebraMap (x : ℤ_[p]) :
    qpToLoc R p (algebraMap ℤ_[p] ℚ_[p] x) = algebraMap _ _ (zpToWitt R p x) :=
  IsLocalization.lift_eq _ _

/-- The map $\mathbb{Q}_p \to W(\cdot^\flat)[1/p]$ commutes with the map of a ring homomorphism. -/
theorem locMap_comp_qpToLoc (f : R →+* S) : (locMap p f).comp (qpToLoc R p) = qpToLoc S p := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, qpToLoc_algebraMap, locMap_algebraMap]
  rw [← RingHom.comp_apply (wittMap p f), wittMap_comp_zpToWitt]

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- The map $\mathbb{Q}_p \to B_{dR}^+(R)$. -/
noncomputable def qpToBdrPlus (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] : ℚ_[p] →+* BDeRhamPlus R p :=
  (algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) _)).comp (qpToLoc R p)

/-- The map $\mathbb{Q}_p \to B_{dR}^+(R)$ is the map to $W(R^\flat)[1/p]$ followed by the completion map. -/
theorem qpToBdrPlus_apply (x : ℚ_[p]) :
    qpToBdrPlus R p x = AdicCompletion.of _ _ (qpToLoc R p x) := rfl

/-- The map $\mathbb{Q}_p \to B_{dR}^+(\cdot)$ commutes with the map of a ring homomorphism. -/
theorem bdrPlusMap_comp_qpToBdrPlus (f : R →+* S) :
    (bdrPlusMap p f).comp (qpToBdrPlus R p) = qpToBdrPlus S p := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, qpToBdrPlus_apply, bdrPlusMap_of, ← RingHom.comp_apply (locMap p f),
    locMap_comp_qpToLoc, qpToBdrPlus_apply]

/-- The structure of $\mathbb{Q}_p$-algebra on $B_{dR}^+(R)$. -/
noncomputable instance bdrPlusQpAlgebra : Algebra ℚ_[p] (BDeRhamPlus R p) :=
  (qpToBdrPlus R p).toAlgebra

/-- The structure of $\mathbb{Q}_p$-algebra on $B_{dR}(R)$, through $B_{dR}^+(R)$. -/
noncomputable instance bdrQpAlgebra : Algebra ℚ_[p] (BDeRham R p) :=
  ((algebraMap (BDeRhamPlus R p) (BDeRham R p)).comp (qpToBdrPlus R p)).toAlgebra

/-- The algebra map $\mathbb{Q}_p \to B_{dR}^+(R)$ is `qpToBdrPlus`. -/
theorem algebraMap_bdrPlus_eq : algebraMap ℚ_[p] (BDeRhamPlus R p) = qpToBdrPlus R p := rfl

/-- The maps $\mathbb{Q}_p \to B_{dR}^+(R) \to B_{dR}(R)$ form a scalar tower. -/
instance bdr_isScalarTower : IsScalarTower ℚ_[p] (BDeRhamPlus R p) (BDeRham R p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The map of $B_{dR}^+$ of a ring homomorphism is $\mathbb{Q}_p$-linear. -/
theorem bdrPlusMap_algebraMap (f : R →+* S) (x : ℚ_[p]) :
    bdrPlusMap p f (algebraMap ℚ_[p] (BDeRhamPlus R p) x) = algebraMap ℚ_[p] _ x := by
  rw [algebraMap_bdrPlus_eq, algebraMap_bdrPlus_eq, ← RingHom.comp_apply,
    bdrPlusMap_comp_qpToBdrPlus]

/-- The map of $B_{dR}$ of a ring isomorphism is $\mathbb{Q}_p$-linear. -/
theorem bdrMap_algebraMap_qp (e : R ≃+* S) (x : ℚ_[p]) :
    bdrMap p e (algebraMap ℚ_[p] (BDeRham R p) x) = algebraMap ℚ_[p] _ x := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (BDeRhamPlus R p), bdrMap_algebraMap,
    bdrPlusMap_algebraMap, ← IsScalarTower.algebraMap_apply]

end Qp

section QpAction

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- The action of a monoid $M$ on $B_{dR}^+(R)$ commutes with the scalars of $\mathbb{Q}_p$. -/
instance bdrPlus_smulCommClass (M : Type*) [Monoid M] [MulSemiringAction M R] :
    SMulCommClass M ℚ_[p] (BDeRhamPlus R p) where
  smul_comm g q x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', bdrPlus_smul_def M g (algebraMap _ _ q),
      bdrPlusMap_algebraMap]

/-- The action of a group $G$ on $B_{dR}(R)$ commutes with the scalars of $\mathbb{Q}_p$. -/
instance bdr_smulCommClass (G : Type*) [Group G] [MulSemiringAction G R] :
    SMulCommClass G ℚ_[p] (BDeRham R p) where
  smul_comm g q x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', bdr_smul_def G g (algebraMap _ _ q),
      bdrMap_algebraMap_qp]

end QpAction

section Galois

variable {p : ℕ} [Fact p.Prime]

/-- An element of $\mathbb{C}_p$ is in $\mathcal{O}_{\mathbb{C}_p}$ if and only if its norm is at most $1$. -/
theorem mem_padicComplexInt_iff (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm,
    Valuation.norm_def, ← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one] using!
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

/-- The automorphism of $\overline{\mathbb{Q}}_p$ that an element of the absolute Galois group is. -/
def galoisAlgEquiv (σ : Field.absoluteGaloisGroup ℚ_[p]) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p := σ

/-- Each $\sigma \in G_{\mathbb{Q}_p}$ preserves the norm of $\overline{\mathbb{Q}}_p$. -/
theorem norm_galois_apply (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicAlgCl p) :
    ‖galoisAlgEquiv σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, ← spectralNorm_eq_of_equiv]

/-- Each $\sigma \in G_{\mathbb{Q}_p}$ is continuous on $\overline{\mathbb{Q}}_p$. -/
theorem continuous_galois (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    Continuous (galoisAlgEquiv σ : PadicAlgCl p →+* PadicAlgCl p) :=
  (AddMonoidHomClass.isometry_of_norm (galoisAlgEquiv σ : PadicAlgCl p →+* PadicAlgCl p)
    (norm_galois_apply σ)).continuous

variable (p) in
/-- The extension of $\sigma \in G_{\mathbb{Q}_p}$ to $\mathbb{C}_p$ by continuity. -/
noncomputable def galoisCp (σ : Field.absoluteGaloisGroup ℚ_[p]) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom _ (continuous_galois σ)

/-- The extension of $\sigma$ to $\mathbb{C}_p$ agrees with $\sigma$ on $\overline{\mathbb{Q}}_p$. -/
theorem galoisCp_coe (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicAlgCl p) :
    galoisCp p σ x = (galoisAlgEquiv σ x : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ x

/-- The extension of $\sigma$ to $\mathbb{C}_p$ is continuous. -/
theorem continuous_galoisCp (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    Continuous (galoisCp p σ) :=
  UniformSpace.Completion.continuous_map (f := galoisAlgEquiv σ)

/-- The extension of $\sigma$ to $\mathbb{C}_p$ preserves the norm. -/
theorem norm_galoisCp (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : ℂ_[p]) :
    ‖galoisCp p σ x‖ = ‖x‖ :=
  UniformSpace.Completion.ext' (continuous_galoisCp σ).norm continuous_norm
    (fun a => by rw [galoisCp_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, norm_galois_apply]) x

/-- The extension of $1$ to $\mathbb{C}_p$ is the identity. -/
theorem galoisCp_one : galoisCp p 1 = RingHom.id _ :=
  DFunLike.coe_injective <| UniformSpace.Completion.ext (continuous_galoisCp 1) continuous_id
    fun a => by rw [galoisCp_coe]; rfl

/-- The extension of $\sigma \tau$ to $\mathbb{C}_p$ is the composite of the extensions. -/
theorem galoisCp_mul (σ τ : Field.absoluteGaloisGroup ℚ_[p]) :
    galoisCp p (σ * τ) = (galoisCp p σ).comp (galoisCp p τ) :=
  DFunLike.coe_injective <| UniformSpace.Completion.ext (continuous_galoisCp _)
    ((continuous_galoisCp σ).comp (continuous_galoisCp τ))
    fun a => by simp only [Function.comp_apply, RingHom.coe_comp, galoisCp_coe]; rfl

/-- The extension of $\sigma$ to $\mathbb{C}_p$ preserves $\mathcal{O}_{\mathbb{C}_p}$. -/
theorem galoisCp_mem (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : ℂ_[p]) :
    galoisCp p σ x ∈ PadicComplexInt p ↔ x ∈ PadicComplexInt p := by
  rw [mem_padicComplexInt_iff, mem_padicComplexInt_iff, norm_galoisCp]

variable (p) in
/-- The ring endomorphism of $\mathcal{O}_{\mathbb{C}_p}$ that $\sigma \in G_{\mathbb{Q}_p}$ gives. -/
noncomputable def galoisInt (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    PadicComplexInt p →+* PadicComplexInt p :=
  (galoisCp p σ).restrict _ _ fun x hx => (galoisCp_mem σ x).2 hx

/-- The action of $G_{\mathbb{Q}_p}$ on $\mathcal{O}_{\mathbb{C}_p}$ by ring automorphisms. -/
noncomputable instance galoisIntAction :
    MulSemiringAction (Field.absoluteGaloisGroup ℚ_[p]) (PadicComplexInt p) where
  smul σ x := galoisInt p σ x
  one_smul x := Subtype.ext (by
    change galoisCp p 1 x = x
    rw [galoisCp_one, RingHom.id_apply])
  mul_smul σ τ x := Subtype.ext (by
    change galoisCp p (σ * τ) x = galoisCp p σ (galoisCp p τ x)
    rw [galoisCp_mul, RingHom.comp_apply])
  smul_zero σ := map_zero (galoisInt p σ)
  smul_add σ := map_add (galoisInt p σ)
  smul_one σ := map_one (galoisInt p σ)
  smul_mul σ := map_mul (galoisInt p σ)

/-- In $\mathbb{C}_p$, the action of $\sigma$ on $\mathcal{O}_{\mathbb{C}_p}$ is the extension of $\sigma$. -/
theorem coe_galois_smul (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicComplexInt p) :
    ((σ • x : PadicComplexInt p) : ℂ_[p]) = galoisCp p σ x := rfl

/-- The norm of $p$ in $\mathbb{C}_p$ is $p^{-1}$. -/
theorem norm_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  rw [Padic.norm_p] at h
  simpa using h

/-- The prime $p$ is not a unit in $\mathcal{O}_{\mathbb{C}_p}$. -/
instance fact_not_isUnit_p : Fact ¬IsUnit (p : PadicComplexInt p) := by
  refine ⟨fun h => ?_⟩
  rw [(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one, map_natCast,
    PadicComplex.valuation_p] at h
  rw [one_div, inv_eq_one, Nat.cast_eq_one] at h
  exact (Fact.out : p.Prime).one_lt.ne' h

/-- An element $x$ of $\mathcal{O}_{\mathbb{C}_p}$ is in $p^n \mathcal{O}_{\mathbb{C}_p}$ if and only if $|x| \le p^{-n}$. -/
theorem mem_span_p_pow_iff (n : ℕ) (x : PadicComplexInt p) :
    x ∈ (span {(p : PadicComplexInt p)} ^ n • ⊤ : Ideal (PadicComplexInt p)) ↔
      ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (mem_padicComplexInt_iff _).1 a.2
    push_cast
    rw [norm_mul, norm_pow, norm_p_cp]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro hx
    have hmem : (x : ℂ_[p]) / (p : ℂ_[p]) ^ n ∈ PadicComplexInt p := by
      rw [mem_padicComplexInt_iff, norm_div, norm_pow, norm_p_cp]
      exact div_le_one_of_le₀ hx (by positivity)
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    push_cast
    exact div_mul_cancel₀ _ (pow_ne_zero _ hp0)

/-- The real number $p^{-1}$ is less than $1$. -/
theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)

/-- The ring $\mathcal{O}_{\mathbb{C}_p}$ is $p$-adically complete. -/
instance isAdicComplete_padicComplexInt :
    IsAdicComplete (span {(p : PadicComplexInt p)}) (PadicComplexInt p) where
  haus' x hx := by
    refine Subtype.ext (norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _)))
    refine ge_of_tendsto
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one (p := p)))
      (Filter.Eventually.of_forall fun n => ?_)
    have h := (mem_span_p_pow_iff n x).1 (by simpa [SModEq.sub_mem] using hx n)
    simpa using h
  prec' f hf := by
    have hf' : ∀ {m n}, m ≤ n → ‖(f m : ℂ_[p]) - f n‖ ≤ (p : ℝ)⁻¹ ^ m := fun {m n} h => by
      have := (mem_span_p_pow_iff m (f m - f n)).1 (SModEq.sub_mem.1 (hf h))
      simpa using this
    have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
      refine cauchySeq_of_le_geometric _ 1 (inv_p_lt_one (p := p)) fun n => ?_
      rw [one_mul, dist_eq_norm]
      exact hf' n.le_succ
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
    have hlm : l ∈ PadicComplexInt p := by
      rw [mem_padicComplexInt_iff]
      exact le_of_tendsto hl.norm (Filter.Eventually.of_forall fun n =>
        (mem_padicComplexInt_iff _).1 (f n).2)
    refine ⟨⟨l, hlm⟩, fun n => SModEq.sub_mem.2 ((mem_span_p_pow_iff n _).2 ?_)⟩
    have h := (tendsto_const_nhds (x := (f n : ℂ_[p]))).sub hl
    refine le_of_tendsto h.norm (Filter.eventually_atTop.2 ⟨n, fun k hk => ?_⟩)
    simpa using hf' hk

end Galois

section Nontrivial

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- If $R[1/p]$ is not the zero ring, then $\ker \theta[1/p]$ is a proper ideal. -/
theorem ker_fontaineThetaInvertP_ne_top [Nontrivial (Localization.Away (p : R))] :
    RingHom.ker (fontaineThetaInvertP R p) ≠ ⊤ :=
  RingHom.ker_ne_top _

/-- If $R[1/p]$ is not the zero ring, then $B_{dR}^+(R)$ is not the zero ring. -/
theorem nontrivial_bdrPlus [Nontrivial (Localization.Away (p : R))] :
    Nontrivial (BDeRhamPlus R p) := by
  have := Ideal.Quotient.nontrivial_iff (I := RingHom.ker (fontaineThetaInvertP R p) ^ 1).2
    (by rw [pow_one]; exact ker_fontaineThetaInvertP_ne_top)
  refine Function.Surjective.nontrivial (f := AdicCompletion.evalₐ
    (RingHom.ker (fontaineThetaInvertP R p)) 1) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨AdicCompletion.of _ _ x, AdicCompletion.evalₐ_of _ _ x⟩

end Nontrivial

section DeRhamQp

variable {p : ℕ} [Fact p.Prime]

/-- The ring $\mathbb{C}_p$ inverts $p$ in $\mathcal{O}_{\mathbb{C}_p}$, so $\mathcal{O}_{\mathbb{C}_p}[1/p]$ is not the zero ring. -/
instance nontrivial_localization_padicComplexInt :
    Nontrivial (Localization.Away (p : PadicComplexInt p)) := by
  have hp : (p : PadicComplexInt p) ≠ 0 := fun h => by
    have h' := congrArg Subtype.val h
    push_cast at h'
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 h')
  exact (IsLocalization.injective (Localization.Away (p : PadicComplexInt p))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp)).nontrivial

/-- The ring $B_{dR}^+(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring. -/
instance nontrivial_bdrPlus_padicComplexInt : Nontrivial (BDeRhamPlus (PadicComplexInt p) p) :=
  nontrivial_bdrPlus

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

variable (p) in
/-- A representation of $G_{\mathbb{Q}_p}$ on a $\mathbb{Q}_p$-vector space $V$ is continuous if the map $G_{\mathbb{Q}_p} \times V \to V$ is continuous, for the Krull topology on $G_{\mathbb{Q}_p}$ and the module topology on $V$. For $V$ of finite dimension, the module topology is the topology of $\mathbb{Q}_p^n$. -/
def IsContinuousRep (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V) : Prop :=
  letI : TopologicalSpace V := moduleTopology ℚ_[p] V
  Continuous fun x : Field.absoluteGaloisGroup ℚ_[p] × V => ρ x.1 x.2

variable [FiniteDimensional ℚ_[p] V]

/-- A representation $V$ of $G_{\mathbb{Q}_p}$ on a finite-dimensional $\mathbb{Q}_p$-vector space is de Rham if it is $B_{dR}$-admissible, with $B_{dR} = B_{dR}(\mathcal{O}_{\mathbb{C}_p})$: the rank of $(B_{dR} \otimes_{\mathbb{Q}_p} V)^{G_{\mathbb{Q}_p}}$ over $B_{dR}^{G_{\mathbb{Q}_p}}$ is $\dim_{\mathbb{Q}_p} V$. The condition does not use the continuity of $\rho$, which is the separate condition `IsContinuousRep`. -/
def IsDeRhamQp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V) : Prop :=
  IsDeRham (PadicComplexInt p) p ρ

omit [FiniteDimensional ℚ_[p] V] in
/-- The trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is continuous. -/
theorem isContinuousRep_trivial :
    IsContinuousRep p (Representation.trivial ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) ℚ_[p]) :=
  letI : TopologicalSpace ℚ_[p] := moduleTopology ℚ_[p] ℚ_[p]
  continuous_snd

/-- If $B_{dR}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is de Rham. -/
theorem isDeRhamQp_trivial_of_nontrivial [Nontrivial (BDeRham (PadicComplexInt p) p)] :
    IsDeRhamQp (Representation.trivial ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) ℚ_[p]) :=
  isAdmissible_trivial _

end DeRhamQp

end Langlands.Padic
