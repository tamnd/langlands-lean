/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.LocalLanglands
import Langlands.Statements.PadicGalois
import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.Lattice
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The representation-theory side of the Breuil-Mézard conjecture

This file defines the objects on the $GL_2$ side of the Breuil-Mézard conjecture for $GL_2(\mathbb{Q}_p)$. These objects do not need the period ring $B_{\mathrm{st}}$.

Let $K$ be a nonarchimedean local field. An inertial type of dimension $m$ is an isomorphism class of representations $\tau : I_K \to GL_m(\mathbb{C})$ of the inertia group that extend to a representation of the Weil group $W_K$ with open kernel. Each Weil-Deligne representation has an inertial type.

Let `rec` be a bijection from the irreducible smooth representations of $GL_2(K)$ to the Weil-Deligne representations of dimension $2$. A Henniart type for $\tau$ relative to `rec` is an irreducible finite-dimensional representation $\sigma$ of $GL_2(\mathcal{O}_K)$ such that, for each infinite-dimensional irreducible $\pi$, the space $\mathrm{Hom}_{GL_2(\mathcal{O}_K)}(\sigma, \pi)$ is nonzero if and only if $\mathrm{rec}(\pi)$ has inertial type $\tau$. The crystalline variant also asks that $\mathrm{rec}(\pi)$ has zero monodromy.

Let $O$ be a local ring with residue field $k$, and let $\rho$ be a representation over a field $C$ with $O \to C$. For a $\rho$-stable lattice $L$ the multiplicity $n_{a,b}(\rho, L)$ is the Jordan-Hölder multiplicity of the Serre weight $\sigma_{a,b} = \mathrm{Sym}^a k^2 \otimes \det^b$ in $L / \mathfrak{m} L$. Finally $\sigma(\lambda, \tau) = \mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} C^2 \otimes \det^{\lambda_2} \otimes \sigma(\tau)$.

## Main definitions

* `Langlands.jhMultiplicity`: the multiplicity of a module $S$ as a factor of a composition series of $M$.
* `Langlands.Reduction`, `Langlands.reduction`: the reduction $L / \mathfrak{m} L$ of a representation on an $O$-module $L$.
* `Langlands.IsStableLattice`, `Langlands.latticeRep`: stable lattices and the representations on them.
* `Langlands.serreWeightRep`: the Serre weight $\sigma_{a,b}$ as a representation of a group $G$ through $G \to GL_2(k)$.
* `Langlands.latticeSerreMultiplicity`: the multiplicity $n_{a,b}(\rho, L)$ for a stable lattice $L$.
* `Langlands.SerreMultiplicityIndependent`: the statement that $n_{a,b}(\rho, L)$ does not depend on $L$.
* `Langlands.serreMultiplicity`: the multiplicity $n_{a,b}(\rho)$ at a chosen stable lattice.
* `Langlands.InertialRep`, `Langlands.InertialType`: inertial representations and inertial types.
* `Langlands.WDIso.inertialType`: the inertial type of a Weil-Deligne representation.
* `Langlands.IsHenniartType`, `Langlands.IsHenniartCrysType`: Henniart types and crystalline Henniart types relative to `rec`.
* `Langlands.HasHenniartTypes`: the statement of the existence of Henniart types for `rec`.
* `Langlands.symDetRep`: the representation $\mathrm{Sym}^a C^2 \otimes \det^b$ for $b \in \mathbb{Z}$.
* `Langlands.sigmaLambdaTau`: the representation $\sigma(\lambda, \tau)$ of $GL_2(\mathcal{O}_K)$.
* `Langlands.typeMultiplicity`: the multiplicity $n_{a,b}(\lambda, \tau)$.

## Main results

* `Langlands.compositionCount_eq_of_equivalent`, `Langlands.jhMultiplicity_eq`: the multiplicity does not depend on the composition series (Jordan-Hölder).
* `Langlands.jhMultiplicity_of_isSimpleModule`: the multiplicity of $S$ in a simple module $M$ is $1$ if $M \cong S$ and $0$ otherwise.
* `Langlands.reductionMultiplicity_eq_one_of_equiv`: if the reduction is isomorphic to an irreducible $W$, then the multiplicity of $W$ is $1$.
* `Langlands.reductionMultiplicity_trivial`: the trivial representation on $O$ has $n_{0,0} = 1$.
* `Langlands.serreMultiplicity_eq`: if the multiplicity does not depend on the lattice, then $n_{a,b}(\rho)$ is its value at each stable lattice.
* `Langlands.IsHenniartType.of_iso`, `Langlands.IsHenniartCrysType.of_iso`: these properties depend only on the isomorphism class of $\sigma$.
* `Langlands.symDetRep_natCast`: for $b \ge 0$ the representation $\mathrm{Sym}^a \otimes \det^b$ is the Serre weight `serreWeight a b`.

## Implementation notes

The independence of $n_{a,b}(\rho, L)$ from the lattice $L$ (the Brauer-Nesbitt theorem) is not proved here. It is the hypothesis `SerreMultiplicityIndependent`. The existence of Henniart types is not proved here. It is the statement `HasHenniartTypes rec`. It is a property of `rec`, because `IsLanglandsMap` does not fix `rec` on the supercuspidal representations.

The representation $\sigma(\tau)$ has complex coefficients, as in the rest of the project. A ring map $\iota : \mathbb{C} \to C$ moves it to $C$, for example $C = \overline{\mathbb{Q}}_p$.

## References

* C. Breuil and A. Mézard, Multiplicités modulaires et représentations de $GL_2(\mathbb{Z}_p)$ et de $\mathrm{Gal}(\overline{\mathbb{Q}}_p / \mathbb{Q}_p)$ en $\ell = p$, with an appendix by G. Henniart, Duke Math. J. 115 (2002).
* M. Kisin, The Fontaine-Mazur conjecture for $GL_2$, J. Amer. Math. Soc. 22 (2009).
* J.-P. Serre, Linear representations of finite groups, chapter 15.
-/

namespace Langlands

section JordanHolder

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [AddCommGroup S] [Module R S]

/-- The factor $s_{i+1} / s_i$ of a composition series of submodules. -/
abbrev compositionFactor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type _ :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

open Classical in
/-- The number of factors of a composition series that are isomorphic to `S`. -/
noncomputable def compositionCount (s : CompositionSeries (Submodule R M)) : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => Nonempty (compositionFactor s i ≃ₗ[R] S)).card

/-- Equivalent composition series have the same number of factors isomorphic to `S`. -/
theorem compositionCount_eq_of_equivalent {s t : CompositionSeries (Submodule R M)}
    (h : s.Equivalent t) : compositionCount S s = compositionCount S t := by
  obtain ⟨f, hf⟩ := h
  classical
  unfold compositionCount
  refine Finset.card_nbij' f f.symm ?_ ?_ (fun i _ => f.symm_apply_apply i)
    (fun j _ => f.apply_symm_apply j)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
    obtain ⟨e⟩ := hi
    exact ⟨(JordanHolderLattice.Iso.linearEquiv (hf i)).symm.trans e⟩
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj ⊢
    obtain ⟨e⟩ := hj
    have := hf (f.symm j)
    rw [f.apply_symm_apply] at this
    exact ⟨(JordanHolderLattice.Iso.linearEquiv this).trans e⟩

open Classical in
variable (R M) in
/-- The Jordan-Hölder multiplicity of $S$ in $M$: the number of factors isomorphic to $S$ in a composition series of $M$. Its value is $0$ if $M$ has no composition series. -/
noncomputable def jhMultiplicity : ℕ :=
  if h : ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ then
    compositionCount S h.choose else 0

/-- **Jordan-Hölder.** The multiplicity is the count of factors isomorphic to `S` in each composition series of $M$ from $0$ to $M$. -/
theorem jhMultiplicity_eq (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥)
    (h₁ : s.last = ⊤) : jhMultiplicity R M S = compositionCount S s := by
  have h : ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := ⟨s, h₀, h₁⟩
  simp only [jhMultiplicity, h, ↓reduceDIte]
  exact compositionCount_eq_of_equivalent S (CompositionSeries.jordan_holder _ _
    (h.choose_spec.1.trans h₀.symm) (h.choose_spec.2.trans h₁.symm))

/-- The zero module has multiplicity zero. -/
theorem jhMultiplicity_of_subsingleton [Subsingleton M] : jhMultiplicity R M S = 0 := by
  rw [jhMultiplicity_eq S (RelSeries.singleton _ ⊥) rfl (Subsingleton.elim _ _)]
  simp [compositionCount]

/-- The composition series $0 \subset M$ of a simple module. -/
def simpleSeries [IsSimpleModule R M] : CompositionSeries (Submodule R M) where
  length := 1
  toFun := ![⊥, ⊤]
  step i := by
    fin_cases i
    exact bot_covBy_top

open Classical in
/-- The multiplicity of $S$ in a simple module $M$ is $1$ if $M \cong S$ and $0$ otherwise. -/
theorem jhMultiplicity_of_isSimpleModule [IsSimpleModule R M] :
    jhMultiplicity R M S = if Nonempty (M ≃ₗ[R] S) then 1 else 0 := by
  classical
  rw [jhMultiplicity_eq S simpleSeries rfl rfl]
  let i₀ : Fin (simpleSeries (R := R) (M := M)).length := ⟨0, Nat.one_pos⟩
  have e : compositionFactor (simpleSeries (R := R) (M := M)) i₀ ≃ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ (by simp [simpleSeries, i₀]; exact Submodule.ker_subtype _)).trans
      Submodule.topEquiv
  have hiff : Nonempty (compositionFactor (simpleSeries (R := R) (M := M)) i₀ ≃ₗ[R] S) ↔
      Nonempty (M ≃ₗ[R] S) :=
    ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩
  have hall : ∀ i : Fin (simpleSeries (R := R) (M := M)).length, i = i₀ := fun i => Fin.ext (by
    have := i.2; simp only [simpleSeries] at this; simp [i₀]; omega)
  unfold compositionCount
  split_ifs with hS
  · rw [Finset.card_eq_one]
    refine ⟨i₀, ?_⟩
    ext i
    rw [hall i]
    simpa using hiff.2 hS
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    rw [hall i]
    exact fun h => hS (hiff.1 h)

end JordanHolder

section SimpleRep

variable {k : Type*} [Field k] {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- An isomorphism of representations as an isomorphism of modules over the group algebra. -/
noncomputable def asModuleEquivOfEquiv (φ : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule where
  toFun := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap
  invFun := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ φ.symm.toIntertwiningMap
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv v := φ.symm_apply_apply v
  right_inv w := φ.apply_symm_apply w

/-- A representation whose space is a simple module over $k$ is irreducible. -/
theorem isSimpleModule_asModule_of_isSimpleModule [IsSimpleModule k V] :
    IsSimpleModule (MonoidAlgebra k G) ρ.asModule := by
  have hV : IsSimpleModule k ρ.asModule := ‹IsSimpleModule k V›
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k _
  rw [isSimpleModule_iff]
  refine ⟨fun p => ?_⟩
  rcases hV.eq_bot_or_eq_top (p.restrictScalars k) with h | h
  · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff k _ _).1 h)
  · exact Or.inr ((Submodule.restrictScalars_eq_top_iff k _ _).1 h)

end SimpleRep

section Reduction

open IsLocalRing

variable (O : Type*) [CommRing O] [IsLocalRing O] (L : Type*) [AddCommGroup L] [Module O L]

/-- The reduction $L / \mathfrak{m} L$ of an $O$-module $L$. -/
abbrev Reduction : Type _ :=
  L ⧸ (maximalIdeal O • ⊤ : Submodule O L)

/-- The reduction is a vector space over the residue field. -/
noncomputable instance : Module (ResidueField O) (Reduction O L) :=
  inferInstanceAs (Module (O ⧸ maximalIdeal O) (L ⧸ (maximalIdeal O • ⊤ : Submodule O L)))

variable {O L}

/-- The residue field acts on the reduction through the residue map. -/
theorem residue_smul_mk (r : O) (x : L) :
    residue O r • (Submodule.Quotient.mk x : Reduction O L) = Submodule.Quotient.mk (r • x) :=
  rfl

/-- The reduction of an endomorphism. -/
noncomputable def reduceEnd : Module.End O L →* Module.End (ResidueField O) (Reduction O L) where
  toFun f :=
    { toFun := Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
      map_add' := map_add _
      map_smul' c x := by
        obtain ⟨r, rfl⟩ := residue_surjective c
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [residue_smul_mk, RingHom.id_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
          map_smul, residue_smul_mk] }
  map_one' := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_mul' f g := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The reduction of an endomorphism acts on classes by the endomorphism. -/
theorem reduceEnd_mk (f : Module.End O L) (x : L) :
    reduceEnd f (Submodule.Quotient.mk x : Reduction O L) = Submodule.Quotient.mk (f x) :=
  rfl

variable {G : Type*} [Group G]

/-- The reduction $\bar\sigma$ of a representation $\sigma$ of $G$ on an $O$-module $L$. -/
noncomputable def reduction (σ : Representation O G L) :
    Representation (ResidueField O) G (Reduction O L) :=
  reduceEnd.comp σ

/-- The multiplicity of a representation $W$ over the residue field. -/
noncomputable def reductionMultiplicity (σ : Representation O G L) {S : Type*} [AddCommGroup S]
    [Module (ResidueField O) S] (W : Representation (ResidueField O) G S) : ℕ :=
  jhMultiplicity (MonoidAlgebra (ResidueField O) G) (reduction σ).asModule W.asModule

variable {C : Type*} [Field C] [Algebra O C] {V : Type*} [AddCommGroup V] [Module C V]
  [Module O V] [IsScalarTower O C V]

/-- The subspace $L$ is stable under $\rho$. -/
def IsStable (ρ : Representation C G V) (L : Submodule O V) : Prop :=
  ∀ g, ∀ v ∈ L, ρ g v ∈ L

/-- The subspace $L$ is an $O$-lattice in $V$ that is stable under $\rho$. -/
def IsStableLattice (ρ : Representation C G V) (L : Submodule O V) : Prop :=
  L.IsFullLattice C ∧ IsStable ρ L

/-- The representation on a stable lattice. -/
def latticeRep (ρ : Representation C G V) (L : Submodule O V) (hL : IsStable ρ L) :
    Representation O G L where
  toFun g := ((ρ g).restrictScalars O).restrict fun v hv => hL g v hv
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]; rfl

/-- The multiplicity of $W$ in the reduction of the representation on a stable lattice $L$. -/
noncomputable def latticeMultiplicity (ρ : Representation C G V) (L : Submodule O V)
    (hL : IsStable ρ L) {S : Type*} [AddCommGroup S] [Module (ResidueField O) S]
    (W : Representation (ResidueField O) G S) : ℕ :=
  reductionMultiplicity (latticeRep ρ L hL) W

end Reduction

section SerreWeightMultiplicity

open IsLocalRing MvPolynomial

variable {k : Type*} [Field k] {G : Type*} [Group G]

/-- The Serre weight $\sigma_{a,b} = \mathrm{Sym}^a k^2 \otimes \det^b$ as a representation of $G$ through a homomorphism $\theta : G \to GL_2(k)$. -/
noncomputable def serreWeightRep (θ : G →* GL (Fin 2) k) (a b : ℕ) :
    Representation k G (homogeneousSubmodule (Fin 2) k a) :=
  (serreWeight a b).comp θ

/-- The Serre weight $\sigma_{0,0}$ is the trivial representation. -/
theorem serreWeightRep_zero_zero (θ : G →* GL (Fin 2) k) (g : G) : serreWeightRep θ 0 0 g = 1 :=
  serreWeight_zero_zero _

variable (k) in
/-- The homogeneous polynomials of degree zero are the constants. -/
noncomputable def homogeneousZeroEquiv : homogeneousSubmodule (Fin 2) k 0 ≃ₗ[k] k where
  toFun P := P.1.coeff 0
  invFun c := ⟨C c, isHomogeneous_C _ c⟩
  map_add' P Q := by simp
  map_smul' c P := by simp
  left_inv P := by
    obtain ⟨P, hP⟩ := P
    have hP' := hP
    rw [mem_homogeneousSubmodule, ← totalDegree_zero_iff_isHomogeneous,
      totalDegree_eq_zero_iff_eq_C] at hP'
    exact Subtype.ext hP'.symm
  right_inv c := by simp

/-- The Serre weight $\sigma_{0,0}$ is irreducible. -/
instance isSimpleModule_serreWeightRep_zero_zero (θ : G →* GL (Fin 2) k) :
    IsSimpleModule (MonoidAlgebra k G) (serreWeightRep θ 0 0).asModule := by
  have : IsSimpleModule k (homogeneousSubmodule (Fin 2) k 0) :=
    IsSimpleModule.congr (homogeneousZeroEquiv k)
  exact isSimpleModule_asModule_of_isSimpleModule

variable {O : Type*} [CommRing O] [IsLocalRing O] {L : Type*} [AddCommGroup L] [Module O L]

/-- If the reduction of $\sigma$ is isomorphic to an irreducible representation $W$, then the multiplicity of $W$ in it is one. -/
theorem reductionMultiplicity_eq_one_of_equiv (σ : Representation O G L) {S : Type*}
    [AddCommGroup S] [Module (ResidueField O) S] {W : Representation (ResidueField O) G S}
    [IsSimpleModule (MonoidAlgebra (ResidueField O) G) W.asModule]
    (φ : (reduction σ).Equiv W) : reductionMultiplicity σ W = 1 := by
  have e := asModuleEquivOfEquiv φ
  have : IsSimpleModule (MonoidAlgebra (ResidueField O) G) (reduction σ).asModule :=
    IsSimpleModule.congr e
  rw [reductionMultiplicity, jhMultiplicity_of_isSimpleModule]
  classical
  exact ite_eq_left_iff.2 fun h => (h ⟨e⟩).elim

variable (O) in
/-- The reduction map $O / \mathfrak{m} O \to k$. -/
noncomputable def reductionSelfLinear : Reduction O O →ₗ[ResidueField O] ResidueField O where
  toFun := (maximalIdeal O • ⊤ : Submodule O O).liftQ (Algebra.linearMap O (ResidueField O))
    (Submodule.smul_le.2 fun r hr n _ => by
      rw [LinearMap.mem_ker, Algebra.linearMap_apply, ResidueField.algebraMap_eq,
        residue_eq_zero_iff, smul_eq_mul]
      exact Ideal.mul_mem_right n _ hr)
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := residue_surjective c
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [residue_smul_mk, Submodule.liftQ_apply, Submodule.liftQ_apply]
    simp [ResidueField.algebraMap_eq]

variable (O) in
/-- The reduction $O / \mathfrak{m} O$ is the residue field. -/
noncomputable def reductionSelfEquiv : Reduction O O ≃ₗ[ResidueField O] ResidueField O :=
  LinearEquiv.ofBijective (reductionSelfLinear O) ⟨by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    change residue O y = 0 at hx
    rw [residue_eq_zero_iff] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using Submodule.smul_mem_smul hx (Submodule.mem_top (x := (1 : O))), by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨Submodule.Quotient.mk r, rfl⟩⟩

/-- The reduction of the trivial representation on $O$ is the Serre weight $\sigma_{0,0}$. -/
noncomputable def reductionTrivialEquiv (θ : G →* GL (Fin 2) (ResidueField O)) :
    (reduction (Representation.trivial O G O)).Equiv (serreWeightRep θ 0 0) :=
  Representation.Equiv.mk ((reductionSelfEquiv O).trans (homogeneousZeroEquiv _).symm) fun g =>
    LinearMap.ext fun x => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h : reduction (Representation.trivial O G O) g (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk y := rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h, serreWeightRep_zero_zero,
        Module.End.one_apply]

/-- **Sanity check.** The multiplicity $n_{0,0}$ of the trivial representation of $G$ on $O$ is one. -/
theorem reductionMultiplicity_trivial (θ : G →* GL (Fin 2) (ResidueField O)) :
    reductionMultiplicity (Representation.trivial O G O) (serreWeightRep θ 0 0) = 1 :=
  reductionMultiplicity_eq_one_of_equiv _ (reductionTrivialEquiv θ)

end SerreWeightMultiplicity

section LatticeMultiplicity

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {G : Type*} [Group G]
  {C : Type*} [Field C] [Algebra O C] {V : Type*} [AddCommGroup V] [Module C V]
  [Module O V] [IsScalarTower O C V]

/-- The multiplicity $n_{a,b}(\rho, L)$ of the Serre weight $\sigma_{a,b}$ in the reduction of a stable lattice $L$. -/
noncomputable def latticeSerreMultiplicity (ρ : Representation C G V) (L : Submodule O V)
    (hL : IsStable ρ L) (θ : G →* GL (Fin 2) (ResidueField O)) (a b : ℕ) : ℕ :=
  latticeMultiplicity ρ L hL (serreWeightRep θ a b)

variable (O) in
/-- The statement that $n_{a,b}(\rho, L)$ does not depend on the stable lattice $L$, for all $a$ and $b$. This is a consequence of the Brauer-Nesbitt theorem, and it is not proved here. -/
def SerreMultiplicityIndependent (ρ : Representation C G V)
    (θ : G →* GL (Fin 2) (ResidueField O)) : Prop :=
  ∀ (L L' : Submodule O V) (hL : IsStableLattice ρ L) (hL' : IsStableLattice ρ L') (a b : ℕ),
    latticeSerreMultiplicity ρ L hL.2 θ a b = latticeSerreMultiplicity ρ L' hL'.2 θ a b

open Classical in
variable (O) in
/-- The multiplicity $n_{a,b}(\rho)$, computed at a chosen stable lattice. Its value is $0$ if there is no stable lattice. -/
noncomputable def serreMultiplicity (ρ : Representation C G V)
    (θ : G →* GL (Fin 2) (ResidueField O)) (a b : ℕ) : ℕ :=
  if h : ∃ L : Submodule O V, IsStableLattice ρ L then
    latticeSerreMultiplicity ρ h.choose h.choose_spec.2 θ a b else 0

/-- If the multiplicity does not depend on the lattice, then $n_{a,b}(\rho)$ is the value at each stable lattice $L$. -/
theorem serreMultiplicity_eq (ρ : Representation C G V) (θ : G →* GL (Fin 2) (ResidueField O))
    (hind : SerreMultiplicityIndependent O ρ θ) (L : Submodule O V) (hL : IsStableLattice ρ L)
    (a b : ℕ) : serreMultiplicity O ρ θ a b = latticeSerreMultiplicity ρ L hL.2 θ a b := by
  have h : ∃ L : Submodule O V, IsStableLattice ρ L := ⟨L, hL⟩
  simp only [serreMultiplicity, h, ↓reduceDIte]
  exact hind _ _ h.choose_spec hL a b

end LatticeMultiplicity

section InertialType

open ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A representation of the inertia group $I_K$ that extends to a representation of the Weil group $W_K$ with open kernel. -/
structure InertialRep (m : ℕ) where
  /-- The representation of the inertia group. -/
  τ : WeilGroup.inertia K →* GL (Fin m) ℂ
  /-- The representation extends to $W_K$ with an open kernel. -/
  exists_extension : ∃ r : WeilGroup K →* GL (Fin m) ℂ, IsOpen (r.ker : Set (WeilGroup K)) ∧
    ∀ i : WeilGroup.inertia K, r i = τ i

namespace InertialRep

variable {K} {m : ℕ}

/-- An inertial representation has open kernel. -/
theorem isOpen_ker (τ : InertialRep K m) :
    IsOpen (τ.τ.ker : Set (WeilGroup.inertia K)) := by
  obtain ⟨r, hr, hrτ⟩ := τ.exists_extension
  have : (τ.τ.ker : Set (WeilGroup.inertia K)) = Subtype.val ⁻¹' (r.ker : Set (WeilGroup K)) := by
    ext i
    simp [hrτ]
  rw [this]
  exact continuous_subtype_val.isOpen_preimage _ hr

/-- Two inertial representations are isomorphic if they are conjugate by an element of $GL_m(\mathbb{C})$. -/
def Iso (τ τ' : InertialRep K m) : Prop :=
  ∃ g : GL (Fin m) ℂ, ∀ i, τ'.τ i = g * τ.τ i * g⁻¹

/-- Isomorphism of inertial representations as a setoid. -/
instance setoid : Setoid (InertialRep K m) where
  r := Iso
  iseqv := by
    refine ⟨fun τ => ⟨1, fun i => by simp⟩, ?_, ?_⟩
    · rintro τ τ' ⟨g, h⟩
      exact ⟨g⁻¹, fun i => by simp [h, mul_assoc]⟩
    · rintro τ τ' τ'' ⟨g, h⟩ ⟨g', h'⟩
      exact ⟨g' * g, fun i => by simp [h, h', mul_assoc]⟩

end InertialRep

/-- An inertial type is an isomorphism class of inertial representations. -/
def InertialType (m : ℕ) : Type u :=
  Quotient (InertialRep.setoid (K := K) (m := m))

variable {K}

/-- The inertial type of an inertial representation. -/
def InertialType.mk {m : ℕ} (τ : InertialRep K m) : InertialType K m :=
  Quotient.mk _ τ

/-- The restriction of a Weil-Deligne representation to the inertia group. -/
noncomputable def WeilDeligneRep.inertialRep {m : ℕ} (ρ : WeilDeligneRep K m) :
    InertialRep K m where
  τ := ρ.r.comp (WeilGroup.inertia K).subtype
  exists_extension := ⟨ρ.r, ρ.isOpen_ker, fun _ => rfl⟩

/-- The inertial type of an isomorphism class of Weil-Deligne representations. -/
noncomputable def WDIso.inertialType {m : ℕ} : WDIso K m → InertialType K m :=
  Quotient.map WeilDeligneRep.inertialRep fun _ _ ⟨g, hr, _⟩ => ⟨g, fun i => hr i⟩

/-- The inertial type of the class of $\rho$ is the class of the restriction of $\rho$ to inertia. -/
theorem WDIso.inertialType_mk {m : ℕ} (ρ : WeilDeligneRep K m) :
    (WDIso.mk ρ).inertialType = InertialType.mk ρ.inertialRep :=
  rfl

/-- The class contains a representation with monodromy operator $N = 0$. -/
def WDIso.HasZeroMonodromy {m : ℕ} (x : WDIso K m) : Prop :=
  ∃ ρ : WeilDeligneRep K m, WDIso.mk ρ = x ∧ ρ.N = 0

end InertialType

/-- Irreducibility is invariant under isomorphism. -/
theorem SmoothRep.Iso.isIrreducible {G : Type*} [Group G] [TopologicalSpace G]
    {σ σ' : SmoothRep G} (h : σ.Iso σ') (hσ : σ.IsIrreducible) :
    σ'.IsIrreducible := by
  obtain ⟨e, he⟩ := h
  have := hσ.1
  refine ⟨e.injective.nontrivial, fun W hW => ?_⟩
  have hst : IsStableSubspace σ.ρ (W.comap e.toLinearMap) := fun g v hv => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [he]
    exact hW g hv
  have hmem : ∀ w, w ∈ W ↔ e.symm w ∈ W.comap e.toLinearMap := fun w => by simp
  rcases hσ.2 _ hst with h0 | h1
  · refine Or.inl (eq_bot_iff.2 fun w hw => ?_)
    rw [hmem, h0, Submodule.mem_bot] at hw
    simpa using congrArg e hw
  · exact Or.inr (eq_top_iff.2 fun w _ => by rw [hmem, h1]; trivial)

section HenniartType

open ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The inclusion $GL_n(\mathcal{O}_K) \to GL_n(K)$. -/
noncomputable def glIntegers (n : ℕ) : GL (Fin n) 𝒪[K] →* GL (Fin n) K :=
  Matrix.GeneralLinearGroup.map (𝒪[K]).subtype

variable {K}

/-- There is a nonzero $GL_2(\mathcal{O}_K)$-equivariant map from $\sigma$ to the restriction of $\pi$. -/
def HasTypeHom (σ : SmoothRep (GL (Fin 2) 𝒪[K])) (π : SmoothRep (GL (Fin 2) K)) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.ρ (glIntegers K 2 g) (f v)

/-- The representation $\sigma$ of $GL_2(\mathcal{O}_K)$ is a Henniart type for $\tau$ relative to `rec`. It is irreducible and finite-dimensional, and an infinite-dimensional irreducible $\pi$ contains $\sigma$ if and only if $\mathrm{rec}(\pi)$ has inertial type $\tau$. -/
def IsHenniartType (rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2) (τ : InertialType K 2)
    (σ : SmoothRep (GL (Fin 2) 𝒪[K])) : Prop :=
  σ.IsIrreducible ∧ FiniteDimensional ℂ σ.V ∧
    ∀ π : IrrRep (GL (Fin 2) K), ¬ FiniteDimensional ℂ π.1.V →
      (HasTypeHom σ π.1 ↔ (rec (IrrSmooth.mk π)).inertialType = τ)

/-- The representation $\sigma$ is a crystalline Henniart type for $\tau$ relative to `rec`. An infinite-dimensional irreducible $\pi$ contains $\sigma$ if and only if $\mathrm{rec}(\pi)$ has inertial type $\tau$ and zero monodromy. -/
def IsHenniartCrysType (rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2) (τ : InertialType K 2)
    (σ : SmoothRep (GL (Fin 2) 𝒪[K])) : Prop :=
  σ.IsIrreducible ∧ FiniteDimensional ℂ σ.V ∧
    ∀ π : IrrRep (GL (Fin 2) K), ¬ FiniteDimensional ℂ π.1.V →
      (HasTypeHom σ π.1 ↔
        (rec (IrrSmooth.mk π)).inertialType = τ ∧ (rec (IrrSmooth.mk π)).HasZeroMonodromy)

/-- The statement of the theorem of Henniart for `rec`: each inertial type of dimension $2$ has a Henniart type and a crystalline Henniart type. It is not proved here. -/
def HasHenniartTypes (rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2) : Prop :=
  ∀ τ : InertialType K 2, (∃ σ, IsHenniartType rec τ σ) ∧ ∃ σ, IsHenniartCrysType rec τ σ

variable {σ σ' : SmoothRep (GL (Fin 2) 𝒪[K])}

omit [IsNonarchimedeanLocalField K] in
/-- The property `HasTypeHom` depends only on the isomorphism class of $\sigma$. -/
theorem HasTypeHom.of_iso (h : σ.Iso σ') {π : SmoothRep (GL (Fin 2) K)} (hσ : HasTypeHom σ π) :
    HasTypeHom σ' π := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf, hfg⟩ := hσ
  refine ⟨f ∘ₗ e.symm.toLinearMap, fun h0 => hf ?_, fun g v => ?_⟩
  · ext v
    simpa using LinearMap.congr_fun h0 (e v)
  · have : e.symm (σ'.ρ g v) = σ.ρ g (e.symm v) :=
      e.injective (by rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
    simp [this, hfg]

/-- The property `IsHenniartType` depends only on the isomorphism class of $\sigma$. -/
theorem IsHenniartType.of_iso {rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2} {τ : InertialType K 2}
    (h : σ.Iso σ') (hσ : IsHenniartType rec τ σ) : IsHenniartType rec τ σ' := by
  obtain ⟨e, -⟩ := id h
  have := hσ.2.1
  refine ⟨h.isIrreducible hσ.1, e.finiteDimensional, fun π hπ => ?_⟩
  rw [← hσ.2.2 π hπ]
  exact ⟨HasTypeHom.of_iso h.symm, HasTypeHom.of_iso h⟩

/-- The property `IsHenniartCrysType` depends only on the isomorphism class of $\sigma$. -/
theorem IsHenniartCrysType.of_iso {rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2}
    {τ : InertialType K 2} (h : σ.Iso σ') (hσ : IsHenniartCrysType rec τ σ) :
    IsHenniartCrysType rec τ σ' := by
  obtain ⟨e, -⟩ := id h
  have := hσ.2.1
  refine ⟨h.isIrreducible hσ.1, e.finiteDimensional, fun π hπ => ?_⟩
  rw [← hσ.2.2 π hπ]
  exact ⟨HasTypeHom.of_iso h.symm, HasTypeHom.of_iso h⟩

end HenniartType

section TypeRepresentation

open ValuativeRel MvPolynomial TensorProduct

universe u

variable {C : Type*} [Field C] {G : Type*} [Group G]

/-- The representation $\mathrm{Sym}^a C^2 \otimes \det^b$ for $b \in \mathbb{Z}$. -/
noncomputable def symDetRep (θ : G →* GL (Fin 2) C) (a : ℕ) (b : ℤ) :
    Representation C G (homogeneousSubmodule (Fin 2) C a) where
  toFun g := ((Matrix.GeneralLinearGroup.det (θ g) ^ b : Cˣ) : C) • serreWeight a 0 (θ g)
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

/-- For $b \ge 0$ this is the representation `serreWeight a b`. -/
theorem symDetRep_natCast (θ : G →* GL (Fin 2) C) (a b : ℕ) :
    symDetRep θ a b = (serreWeight a b).comp θ := by
  ext g : 1
  simp [symDetRep, serreWeight]

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- The representation $\pi$ with coefficients moved to $C$ by the ring map $\iota : \mathbb{C} \to C$, in a basis of $\pi$. -/
noncomputable def baseChangeRep (ι : ℂ →+* C) (π : SmoothRep H) (hπ : FiniteDimensional ℂ π.V) :
    Representation C H (Fin (Module.finrank ℂ π.V) → C) :=
  let b := Module.finBasis ℂ π.V
  { toFun := fun g => Matrix.toLin' ((LinearMap.toMatrix b b (π.ρ g)).map ι)
    map_one' := by simp; rfl
    map_mul' := fun g h => by
      simp [LinearMap.toMatrix_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl }

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [Algebra K C]

/-- The map $GL_2(\mathcal{O}_K) \to GL_2(C)$ for a $K$-algebra $C$. -/
noncomputable def glIntegersTo : GL (Fin 2) 𝒪[K] →* GL (Fin 2) C :=
  Matrix.GeneralLinearGroup.map ((algebraMap K C).comp (𝒪[K]).subtype)

variable {K}

/-- The representation $\sigma(\lambda, \tau) = \mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} C^2 \otimes \det^{\lambda_2} \otimes \sigma(\tau)$ of $GL_2(\mathcal{O}_K)$, with $\lambda = w$. -/
noncomputable def sigmaLambdaTau (ι : ℂ →+* C) (w : ℤ × ℤ) (σ : SmoothRep (GL (Fin 2) 𝒪[K]))
    (hσ : FiniteDimensional ℂ σ.V) :
    Representation C (GL (Fin 2) 𝒪[K])
      (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C]
        (Fin (Module.finrank ℂ σ.V) → C)) :=
  (symDetRep (glIntegersTo K) (w.1 - w.2 - 1).toNat w.2).tprod (baseChangeRep ι σ hσ)

variable {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O C]

/-- The multiplicity $n_{a,b}(\lambda, \tau)$ of $\sigma_{a,b}$ in the reduction of a stable lattice in $\sigma(\lambda, \tau)$. The ring map `red` gives the action of $GL_2(\mathcal{O}_K)$ on the Serre weights. -/
noncomputable def typeMultiplicity (ι : ℂ →+* C) (red : 𝒪[K] →+* IsLocalRing.ResidueField O)
    (w : ℤ × ℤ) (σ : SmoothRep (GL (Fin 2) 𝒪[K])) (hσ : FiniteDimensional ℂ σ.V) (a b : ℕ) : ℕ :=
  letI := Module.restrictScalars O C (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C]
    (Fin (Module.finrank ℂ σ.V) → C))
  haveI := IsScalarTower.restrictScalars O C (homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat
    ⊗[C] (Fin (Module.finrank ℂ σ.V) → C))
  serreMultiplicity O (C := C)
    (V := homogeneousSubmodule (Fin 2) C (w.1 - w.2 - 1).toNat ⊗[C]
      (Fin (Module.finrank ℂ σ.V) → C))
    (sigmaLambdaTau ι w σ hσ) (Matrix.GeneralLinearGroup.map red) a b

end TypeRepresentation

end Langlands
