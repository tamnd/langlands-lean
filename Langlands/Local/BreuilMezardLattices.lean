/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.BreuilMezardTypes
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Brauer-Nesbitt for stable lattices, and the coefficients of Breuil-Mézard

This file proves that the Serre weight multiplicities $n_{a,b}(\rho, L)$ of the reduction of a stable lattice $L$ do not depend on $L$, when the ring of coefficients $O$ is a discrete valuation ring with fraction field $C$ (the Brauer-Nesbitt theorem). Thus the hypothesis `SerreMultiplicityIndependent` of `Langlands.Local.BreuilMezardTypes` holds.

It also computes $n_{a,b}$ for the trivial representation, and it sets up the coefficients for the Breuil-Mézard conjecture: a finite extension $E$ of $\mathbb{Q}_p$, its ring of integers $O_E$, its residue field $k$, an embedding $E \hookrightarrow \overline{\mathbb{Q}}_p$ and the map $\mathrm{red} : \mathbb{Z}_p \to k$.

## Main definitions

* `Langlands.IsFactor`: the factor $b / a$ is isomorphic to $S$.
* `Langlands.reduceHom`: the reduction $L_1 / \mathfrak{m} L_1 \to L_2 / \mathfrak{m} L_2$ of a linear map.
* `Langlands.coeffEmbedding`: an embedding $E \hookrightarrow \overline{\mathbb{Q}}_p$ over $\mathbb{Q}_p$.
* `Langlands.integersAlgebraMap`: the ring map $\mathbb{Z}_p \to O_E$.
* `Langlands.coeffRed`: the ring map $\mathrm{red} : \mathbb{Z}_p \to k$.

## Main results

* `Langlands.jhMultiplicity_eq_add_of_exact`: the Jordan-Hölder multiplicity is additive on short exact sequences of modules of finite length.
* `Langlands.reductionMultiplicity_eq_of_comp`: if two torsion-free lattices have equivariant maps $i$ and $j$ with $i \circ j = \varpi$ and $j \circ i = \varpi$, then their reductions have the same multiplicities.
* `Langlands.latticeMultiplicity_eq_of_isStableLattice`: two stable lattices have the same multiplicities (Brauer-Nesbitt).
* `Langlands.serreMultiplicityIndependent`: the hypothesis `SerreMultiplicityIndependent` holds over a discrete valuation ring.
* `Langlands.serreMultiplicity_eq_latticeSerreMultiplicity`: $n_{a,b}(\rho)$ is $n_{a,b}(\rho, L)$ for each stable lattice $L$.
* `Langlands.reductionMultiplicity_trivial_of_ne_zero`: for $a \ne 0$ the trivial representation has $n_{a,b} = 0$.
* `Langlands.reductionMultiplicity_trivial_zero`: the trivial representation has $n_{0,b} = 1$ if $\det^b \circ \theta$ is trivial, and $n_{0,b} = 0$ otherwise.
* `Langlands.charP_residueField`: the residue field $k$ of $O_E$ has characteristic $p$.
* `Langlands.serreMultiplicityIndependent_integer`: Brauer-Nesbitt for $O = O_E$ and $C = E$.

## Implementation notes

The proof of Brauer-Nesbitt compares two stable lattices $L$ and $L'$ through $L \cap L'$. If $\varpi^n L \subseteq L' \subseteq L$, the chain $L' + \varpi^m L$ for $m \le n$ has steps $M' \subseteq M$ with $\varpi M \subseteq M'$. For such a step, the inclusion $i : M' \to M$ and the multiplication $j = \varpi : M \to M'$ give reductions with $\mathrm{range} = \ker$ in both directions. Additivity then gives the same multiplicities.

The field $E$ is a non-archimedean local field with `ValuativeExtension ℚ_[p] E`, so that $O_E$ is a discrete valuation ring and the structure map sends $\mathbb{Z}_p$ into $O_E$.

The multiplicity `typeMultiplicity` of `Langlands.Local.BreuilMezardTypes` uses a ring map $\iota : \mathbb{C} \to C$. There is no such ring map to $C = E$, so the final assembly must move $\sigma(\tau)$ to $E$ in a different way.

## References

* J.-P. Serre, Linear representations of finite groups, chapter 15.
* C. Breuil and A. Mézard, Multiplicités modulaires et représentations de $GL_2(\mathbb{Z}_p)$ et de $\mathrm{Gal}(\overline{\mathbb{Q}}_p / \mathbb{Q}_p)$ en $\ell = p$, Duke Math. J. 115 (2002).
-/

namespace Langlands

section JordanHolderAdditivity

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [AddCommGroup S] [Module R S]

/-- The factor $b / a$ of two submodules $a \le b$ is isomorphic to `S`. -/
def IsFactor (a b : Submodule R M) : Prop :=
  Nonempty ((b ⧸ a.comap b.subtype) ≃ₗ[R] S)

open Classical in
/-- The number of factors isomorphic to $S$ in a composition series is a sum over its steps. -/
theorem compositionCount_eq_sum (s : CompositionSeries (Submodule R M)) :
    compositionCount S s =
      ∑ i : Fin s.length, if IsFactor S (s i.castSucc) (s i.succ) then 1 else 0 := by
  rw [compositionCount, Finset.card_filter]
  rfl

/-- The number of factors isomorphic to $S$ in the concatenation of two composition series is the sum of the two numbers. -/
theorem compositionCount_smash (s t : CompositionSeries (Submodule R M)) (h : s.last = t.head) :
    compositionCount S (s.smash t h) = compositionCount S s + compositionCount S t := by
  classical
  rw [compositionCount_eq_sum, compositionCount_eq_sum, compositionCount_eq_sum]
  refine (Fin.sum_univ_add (fun i : Fin (s.length + t.length) => _)).trans ?_
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_
  · have h₁ : (s.smash t h).toFun (Fin.castAdd t.length x).castSucc = s x.castSucc :=
      RelSeries.smash_castAdd h x
    have h₂ : (s.smash t h).toFun (Fin.castAdd t.length x).succ = s x.succ :=
      RelSeries.smash_succ_castAdd h x
    congr 2
  · have h₁ : (s.smash t h).toFun (Fin.natAdd s.length x).castSucc = t x.castSucc :=
      RelSeries.smash_natAdd h x
    have h₂ : (s.smash t h).toFun (Fin.natAdd s.length x).succ = t x.succ :=
      RelSeries.smash_succ_natAdd h x
    congr 2

variable {S}

/-- A surjective map $b' \to b$ that matches $a'$ with $a$ identifies the factors $b'/a'$ and $b/a$. -/
theorem isFactor_iff_of_surjective {M' : Type*} [AddCommGroup M'] [Module R M']
    {a b : Submodule R M} {a' b' : Submodule R M'} (φ : b' →ₗ[R] b) (hφ : Function.Surjective φ)
    (hker : (a.comap b.subtype).comap φ = a'.comap b'.subtype) :
    IsFactor S a' b' ↔ IsFactor S a b := by
  let ψ := (a.comap b.subtype).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := (Submodule.mkQ_surjective _).comp hφ
  have hk : a'.comap b'.subtype = LinearMap.ker ψ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hker]
  let e := (Submodule.quotEquivOfEq _ _ hk).trans (ψ.quotKerEquivOfSurjective hψ)
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

/-- An injective linear map does not change the factors of a pair of submodules. -/
theorem isFactor_map_iff {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (a b : Submodule R M) :
    IsFactor S (a.map f) (b.map f) ↔ IsFactor S a b := by
  refine (isFactor_iff_of_surjective (Submodule.equivMapOfInjective f hf b).toLinearMap
    (Submodule.equivMapOfInjective f hf b).surjective ?_).symm
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe,
    Submodule.coe_equivMapOfInjective_apply]
  exact hf.mem_set_image

/-- The preimage under a surjective linear map does not change the factors of a pair of submodules. -/
theorem isFactor_comap_iff {P : Type*} [AddCommGroup P] [Module R P] (g : M →ₗ[R] P)
    (hg : Function.Surjective g) (a b : Submodule R P) :
    IsFactor S (a.comap g) (b.comap g) ↔ IsFactor S a b := by
  refine isFactor_iff_of_surjective (g.restrict fun x hx => hx) ?_ ?_
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  · ext x
    simp

/-- A map of composition series that keeps the factors isomorphic to $S$ keeps their number. -/
theorem compositionCount_map {N : Type*} [AddCommGroup N] [Module R N]
    (s : CompositionSeries (Submodule R N))
    (F : RelHom (JordanHolderLattice.IsMaximal (X := Submodule R N))
      (JordanHolderLattice.IsMaximal (X := Submodule R M)))
    (hF : ∀ a b, IsFactor S (F a) (F b) ↔ IsFactor S a b) :
    compositionCount S (s.map F) = compositionCount S s := by
  classical
  rw [compositionCount_eq_sum, compositionCount_eq_sum]
  exact Finset.sum_congr rfl fun i _ => if_congr (hF _ _) rfl rfl

variable (S)

open Classical in
/-- If $M$ has no composition series, then the multiplicity of $S$ in $M$ is zero. -/
theorem jhMultiplicity_eq_zero
    (h : ¬ ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) :
    jhMultiplicity R M S = 0 := by
  simp only [jhMultiplicity, h, ↓reduceDIte]

/-- The series of the images of a composition series under a linear equivalence. -/
def mapSeriesEquiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) : CompositionSeries (Submodule R N) :=
  s.map ⟨Submodule.map e.toLinearMap, Submodule.map_covBy_of_injective e.injective⟩

/-- The image of a composition series under a linear equivalence starts at $\bot$. -/
theorem mapSeriesEquiv_head {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    {s : CompositionSeries (Submodule R M)} (h : s.head = ⊥) : (mapSeriesEquiv e s).head = ⊥ := by
  simp [mapSeriesEquiv, h]

/-- The image of a composition series under a linear equivalence ends at $\top$. -/
theorem mapSeriesEquiv_last {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    {s : CompositionSeries (Submodule R M)} (h : s.last = ⊤) : (mapSeriesEquiv e s).last = ⊤ := by
  simp only [mapSeriesEquiv, RelSeries.last_map, h]
  show Submodule.map e.toLinearMap ⊤ = ⊤
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.2 e.surjective

/-- Isomorphic modules have the same Jordan-Hölder multiplicities. -/
theorem jhMultiplicity_congr {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    jhMultiplicity R M S = jhMultiplicity R N S := by
  by_cases hM : ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤
  · obtain ⟨s, h₀, h₁⟩ := hM
    rw [jhMultiplicity_eq S s h₀ h₁, jhMultiplicity_eq S (mapSeriesEquiv e s)
      (mapSeriesEquiv_head e h₀) (mapSeriesEquiv_last e h₁)]
    exact (compositionCount_map s _ fun a b => isFactor_map_iff e.toLinearMap e.injective a b).symm
  · have hN : ¬ ∃ s : CompositionSeries (Submodule R N), s.head = ⊥ ∧ s.last = ⊤ := by
      rintro ⟨s, h₀, h₁⟩
      exact hM ⟨mapSeriesEquiv e.symm s, mapSeriesEquiv_head _ h₀, mapSeriesEquiv_last _ h₁⟩
    rw [jhMultiplicity_eq_zero S hM, jhMultiplicity_eq_zero S hN]

/-- **Additivity.** For a short exact sequence $0 \to N \to M \to P \to 0$ of modules of finite length, the multiplicity of `S` in $M$ is the sum of the multiplicities in $N$ and in $P$. -/
theorem jhMultiplicity_eq_add_of_exact {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (hM : IsFiniteLength R M) (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    jhMultiplicity R M S = jhMultiplicity R N S + jhMultiplicity R P S := by
  obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp (hM.of_surjective hg)
  obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp (hM.of_injective hf)
  let s' : CompositionSeries (Submodule R M) :=
    s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
  let t' : CompositionSeries (Submodule R M) :=
    t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
  have hfg : Submodule.map f ⊤ = Submodule.comap g ⊥ := by
    rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  have hc : t'.last = s'.head := by simpa [s', t', hs₁, ht₂] using hfg
  rw [jhMultiplicity_eq S (t'.smash s' hc)
      (by simpa [t', ht₁, -Submodule.map_bot] using Submodule.map_bot f)
      (by simpa [s', hs₂, -Submodule.comap_top] using Submodule.comap_top g),
    compositionCount_smash, jhMultiplicity_eq S s hs₁ hs₂, jhMultiplicity_eq S t ht₁ ht₂]
  congr 1
  · exact compositionCount_map t _ fun a b => isFactor_map_iff f hf a b
  · exact compositionCount_map s _ fun a b => isFactor_comap_iff g hg a b

/-- The multiplicity in $M$ is the sum of the multiplicities in the kernel and in the image of a linear map on $M$. -/
theorem jhMultiplicity_eq_ker_add_range {N : Type*} [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (f : M →ₗ[R] N) :
    jhMultiplicity R M S =
      jhMultiplicity R (LinearMap.ker f) S + jhMultiplicity R (LinearMap.range f) S :=
  jhMultiplicity_eq_add_of_exact S hM (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.injective_subtype _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))

/-- Let $f : M \to N$ and $g : N \to M$ be linear maps of modules of finite length with $\mathrm{im} f = \ker g$ and $\mathrm{im} g = \ker f$. Then $M$ and $N$ have the same Jordan-Hölder multiplicities. -/
theorem jhMultiplicity_eq_of_range_eq_ker {N : Type*} [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h₁ : LinearMap.range f = LinearMap.ker g) (h₂ : LinearMap.range g = LinearMap.ker f) :
    jhMultiplicity R M S = jhMultiplicity R N S := by
  rw [jhMultiplicity_eq_ker_add_range S hM f, jhMultiplicity_eq_ker_add_range S hN g,
    jhMultiplicity_congr S (LinearEquiv.ofEq _ _ h₁), jhMultiplicity_congr S
      (LinearEquiv.ofEq _ _ h₂.symm), add_comm]

end JordanHolderAdditivity

section AsModule

variable {k : Type*} [Field k] {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- A linear map that commutes with the actions of $G$, as a map of modules over the group algebra. -/
noncomputable def asModuleHom (φ : V →ₗ[k] W) (h : ∀ g v, φ (ρ g v) = σ g (φ v)) :
    ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
    (φ.intertwiningMap_of_isIntertwiningMap ρ σ h)

/-- The map `asModuleHom φ h` is the map $\varphi$. -/
theorem asModuleHom_apply (φ : V →ₗ[k] W) (h : ∀ g v, φ (ρ g v) = σ g (φ v)) (x : ρ.asModule) :
    asModuleHom φ h x = φ x :=
  rfl

variable (ρ) in
/-- A finite-dimensional representation has finite length as a module over the group algebra. -/
theorem isFiniteLength_asModule [FiniteDimensional k V] :
    IsFiniteLength (MonoidAlgebra k G) ρ.asModule :=
  isFiniteLength_iff_isNoetherian_isArtinian.2
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

end AsModule

section ReductionComparison

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {L₁ L₂ : Type*} [AddCommGroup L₁] [Module O L₁]
  [AddCommGroup L₂] [Module O L₂]

/-- The reduction of a linear map. -/
noncomputable def reduceHom (f : L₁ →ₗ[O] L₂) :
    Reduction O L₁ →ₗ[ResidueField O] Reduction O L₂ where
  toFun := Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := residue_surjective c
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [residue_smul_mk, RingHom.id_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
      map_smul, residue_smul_mk]

/-- The map `reduceHom f` sends the class of $x$ to the class of $f(x)$. -/
theorem reduceHom_mk (f : L₁ →ₗ[O] L₂) (x : L₁) :
    reduceHom f (Submodule.Quotient.mk x : Reduction O L₁) = Submodule.Quotient.mk (f x) :=
  rfl

/-- The action of $O$ on the reduction is the action through the residue field. -/
instance : IsScalarTower O (ResidueField O) (Reduction O L₁) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [ResidueField.algebraMap_eq, residue_smul_mk]
    rfl

/-- The reduction of a finite module is finite over the residue field. -/
instance [Module.Finite O L₁] : Module.Finite (ResidueField O) (Reduction O L₁) :=
  Module.Finite.of_restrictScalars_finite O _ _

/-- A class in the reduction is zero if and only if it is the class of a multiple of $\varpi$. -/
theorem reduction_mk_eq_zero_iff {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ}) (z : L₁) :
    (Submodule.Quotient.mk z : Reduction O L₁) = 0 ↔ ∃ y, ϖ • y = z := by
  rw [Submodule.Quotient.mk_eq_zero, hϖ, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, rfl⟩

/-- Under the maps $i$ and $j$ with $i \circ j = \varpi$ and $j \circ i = \varpi$, the range of the reduction of $i$ is the kernel of the reduction of $j$. -/
theorem mem_range_reduceHom_iff {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ})
    (h₁ : ∀ x : L₁, ϖ • x = 0 → x = 0) (i : L₂ →ₗ[O] L₁) (j : L₁ →ₗ[O] L₂)
    (hij : ∀ x, i (j x) = ϖ • x) (hji : ∀ x, j (i x) = ϖ • x) (z : Reduction O L₁) :
    (∃ y, reduceHom i y = z) ↔ reduceHom j z = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [reduceHom_mk, reduction_mk_eq_zero_iff hϖ]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [reduceHom_mk] at hy
    have h : (Submodule.Quotient.mk (i y - x) : Reduction O L₁) = 0 := by
      rw [Submodule.Quotient.mk_sub, hy, sub_self]
    obtain ⟨w, hw⟩ := (reduction_mk_eq_zero_iff hϖ _).1 h
    refine ⟨y - j w, ?_⟩
    rw [smul_sub, ← hji, ← map_smul, hw, map_sub, sub_sub_cancel]
  · rintro ⟨y, hy⟩
    have h : i y = x := by
      rw [← sub_eq_zero]
      apply h₁
      rw [smul_sub, ← map_smul, hy, hij, sub_self]
    exact ⟨Submodule.Quotient.mk y, by rw [reduceHom_mk, h]⟩

variable {G : Type*} [Group G]

/-- The reduction of an equivariant map is equivariant. -/
theorem reduceHom_intertwines {σ₁ : Representation O G L₁} {σ₂ : Representation O G L₂}
    (f : L₁ →ₗ[O] L₂) (hf : ∀ g x, f (σ₁ g x) = σ₂ g (f x)) (g : G) (z : Reduction O L₁) :
    reduceHom f (reduction σ₁ g z) = reduction σ₂ g (reduceHom f z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  show Submodule.Quotient.mk (f (σ₁ g x)) = Submodule.Quotient.mk (σ₂ g (f x))
  rw [hf]

/-- **Comparison of reductions.** Let $i : L_2 \to L_1$ and $j : L_1 \to L_2$ be $G$-equivariant maps with $i \circ j = \varpi$ and $j \circ i = \varpi$, where $\varpi$ generates the maximal ideal and has no torsion on $L_1$ and $L_2$. Then the reductions of $L_1$ and $L_2$ have the same Jordan-Hölder multiplicities. -/
theorem reductionMultiplicity_eq_of_comp {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ})
    [Module.Finite O L₁] [Module.Finite O L₂] (h₁ : ∀ x : L₁, ϖ • x = 0 → x = 0)
    (h₂ : ∀ x : L₂, ϖ • x = 0 → x = 0) (σ₁ : Representation O G L₁)
    (σ₂ : Representation O G L₂) (i : L₂ →ₗ[O] L₁) (j : L₁ →ₗ[O] L₂)
    (hi : ∀ g x, i (σ₂ g x) = σ₁ g (i x)) (hj : ∀ g x, j (σ₁ g x) = σ₂ g (j x))
    (hij : ∀ x, i (j x) = ϖ • x) (hji : ∀ x, j (i x) = ϖ • x) {S : Type*} [AddCommGroup S]
    [Module (ResidueField O) S] (W : Representation (ResidueField O) G S) :
    reductionMultiplicity σ₁ W = reductionMultiplicity σ₂ W := by
  let f := asModuleHom (ρ := reduction σ₁) (σ := reduction σ₂) (reduceHom j)
    (reduceHom_intertwines j hj)
  let f' := asModuleHom (ρ := reduction σ₂) (σ := reduction σ₁) (reduceHom i)
    (reduceHom_intertwines i hi)
  refine jhMultiplicity_eq_of_range_eq_ker _ (isFiniteLength_asModule _)
    (isFiniteLength_asModule _) f f' ?_ ?_
  · ext z
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact mem_range_reduceHom_iff hϖ h₂ j i hji hij z
  · ext z
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact mem_range_reduceHom_iff hϖ h₁ i j hij hji z

end ReductionComparison

section Lattices

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {G : Type*} [Group G]
  {C : Type*} [Field C] [Algebra O C] {V : Type*} [AddCommGroup V] [Module C V]
  [Module O V] [IsScalarTower O C V] {ρ : Representation C G V}

omit [IsLocalRing O] in
/-- The action of $G$ commutes with the action of $O$. -/
theorem rep_smul (ρ : Representation C G V) (g : G) (r : O) (v : V) : ρ g (r • v) = r • ρ g v :=
  LinearMap.map_smul_of_tower (ρ g) r v

omit [IsLocalRing O] [Algebra O C] [IsScalarTower O C V] in
/-- The intersection of two stable submodules is stable. -/
theorem IsStable.inf {L L' : Submodule O V} (hL : IsStable ρ L) (hL' : IsStable ρ L') :
    IsStable ρ (L ⊓ L') :=
  fun g v hv => ⟨hL g v hv.1, hL' g v hv.2⟩

omit [IsLocalRing O] [Algebra O C] [IsScalarTower O C V] in
/-- The sum of two stable submodules is stable. -/
theorem IsStable.sup {L L' : Submodule O V} (hL : IsStable ρ L) (hL' : IsStable ρ L') :
    IsStable ρ (L ⊔ L') := by
  intro g v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add]
  exact Submodule.add_mem_sup (hL g y hy) (hL' g z hz)

omit [IsLocalRing O] in
/-- The product $I L$ of an ideal $I$ and a stable submodule $L$ is stable. -/
theorem IsStable.smul {L : Submodule O V} (hL : IsStable ρ L) (I : Ideal O) :
    IsStable ρ (I • L) := by
  intro g v hv
  refine Submodule.smul_induction_on hv (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [rep_smul]
    exact Submodule.smul_mem_smul hr (hL g n hn)
  · rw [map_add]
    exact add_mem hx hy

/-- The multiplicity at a lattice depends only on the lattice. -/
theorem latticeMultiplicity_congr {L L' : Submodule O V} (h : L = L') (hL : IsStable ρ L)
    (hL' : IsStable ρ L') {S : Type*} [AddCommGroup S] [Module (ResidueField O) S]
    (W : Representation (ResidueField O) G S) :
    latticeMultiplicity ρ L hL W = latticeMultiplicity ρ L' hL' W := by
  subst h
  rfl

/-- Let $L' \subseteq L$ be stable finitely generated submodules with $\varpi L \subseteq L'$. Then the reductions of $L$ and $L'$ have the same Jordan-Hölder multiplicities. -/
theorem latticeMultiplicity_eq_of_smul_le {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ})
    (hϖ₀ : algebraMap O C ϖ ≠ 0) {L L' : Submodule O V} (hL : IsStable ρ L)
    (hL' : IsStable ρ L') (hfg : L.FG) (hfg' : L'.FG) (hle : L' ≤ L)
    (hstep : ∀ x ∈ L, ϖ • x ∈ L') {S : Type*} [AddCommGroup S] [Module (ResidueField O) S]
    (W : Representation (ResidueField O) G S) :
    latticeMultiplicity ρ L hL W = latticeMultiplicity ρ L' hL' W := by
  have : Module.Finite O L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite O L' := Module.Finite.iff_fg.2 hfg'
  have htf : ∀ (N : Submodule O V) (x : N), ϖ • x = 0 → x = 0 := by
    intro N x hx
    apply Subtype.ext
    have hx' : (ϖ • (x : V)) = 0 := congrArg Subtype.val hx
    rw [← algebraMap_smul C, smul_eq_zero] at hx'
    exact hx'.resolve_left hϖ₀
  refine reductionMultiplicity_eq_of_comp hϖ (htf L) (htf L') (latticeRep ρ L hL)
    (latticeRep ρ L' hL') (Submodule.inclusion hle)
    ((ϖ • L.subtype).codRestrict L' fun x => hstep x x.2) (fun g x => rfl)
    (fun g x => Subtype.ext (rep_smul ρ g ϖ x).symm) (fun x => rfl) (fun x => rfl) W

/-- Let $L' \subseteq L$ be stable submodules with $L$ finitely generated and $\mathfrak{m}^m L \subseteq L'$. Then the reductions of $L$ and $L'$ have the same Jordan-Hölder multiplicities. -/
theorem latticeMultiplicity_eq_of_pow_smul_le [IsNoetherianRing O] {ϖ : O}
    (hϖ : maximalIdeal O = Ideal.span {ϖ}) (hϖ₀ : algebraMap O C ϖ ≠ 0) {L L' : Submodule O V}
    (hL : IsStable ρ L) (hL' : IsStable ρ L') (hfg : L.FG) (hle : L' ≤ L) (m : ℕ)
    (hm : maximalIdeal O ^ m • L ≤ L') {S : Type*} [AddCommGroup S] [Module (ResidueField O) S]
    (W : Representation (ResidueField O) G S) :
    latticeMultiplicity ρ L hL W = latticeMultiplicity ρ L' hL' W := by
  let Λ : ℕ → Submodule O V := fun n => L' ⊔ maximalIdeal O ^ n • L
  have hΛ : ∀ n, IsStable ρ (Λ n) := fun n => hL'.sup (hL.smul _)
  have hΛle : ∀ n, Λ n ≤ L := fun n => sup_le hle Submodule.smul_le_right
  have hΛ₀ : Λ 0 = L := by
    simp only [Λ, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact sup_of_le_right hle
  have hΛm : Λ m = L' := sup_of_le_left hm
  have key : ∀ n, latticeMultiplicity ρ L hL W = latticeMultiplicity ρ (Λ n) (hΛ n) W := by
    intro n
    induction n with
    | zero => exact latticeMultiplicity_congr hΛ₀.symm _ _ W
    | succ n ih =>
      rw [ih]
      refine latticeMultiplicity_eq_of_smul_le hϖ hϖ₀ (hΛ n) (hΛ (n + 1))
        (hfg.of_le (hΛle n)) (hfg.of_le (hΛle (n + 1)))
        (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)) _)
        (fun x hx => ?_) W
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [smul_add]
      refine Submodule.add_mem_sup (L'.smul_mem ϖ hy) ?_
      rw [pow_succ', Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hϖ ▸ Ideal.mem_span_singleton_self ϖ) hz
  rw [key m]
  exact latticeMultiplicity_congr hΛm _ _ W

end Lattices

section DiscreteValuationRing

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*} [Group G]
  {C : Type*} [Field C] [Algebra O C] [IsFractionRing O C] {V : Type*} [AddCommGroup V]
  [Module C V] [Module O V] [IsScalarTower O C V] {ρ : Representation C G V}

/-- Each element of the fraction field becomes integral after multiplication by a power of a uniformizer. -/
theorem exists_pow_mul_eq_algebraMap {ϖ : O} (hirr : Irreducible ϖ) (c : C) :
    ∃ (k : ℕ) (a : O), algebraMap O C (ϖ ^ k) * c = algebraMap O C a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective O c
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hy) hirr
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hu : algebraMap O C ↑u ≠ 0 := (u.isUnit.map _).ne_zero
  have hp : algebraMap O C (ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O C)).2 (pow_ne_zero _ hirr.ne_zero)
  have hinv : algebraMap O C ↑u⁻¹ * algebraMap O C ↑u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul, mul_div_assoc', div_eq_iff (mul_ne_zero hu hp)]
  linear_combination (-(algebraMap O C x * algebraMap O C (ϖ ^ n))) * hinv

/-- If $L'$ spans $V$ over $C$, then each vector of $V$ has a multiple $\varpi^n v$ in $L'$. -/
theorem exists_pow_smul_mem {ϖ : O} (hirr : Irreducible ϖ) {L' : Submodule O V}
    (hL' : Submodule.span C (L' : Set V) = ⊤) (v : V) : ∃ n : ℕ, ϖ ^ n • v ∈ L' := by
  have hv : v ∈ Submodule.span C (L' : Set V) := hL' ▸ trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have h₁ : ϖ ^ (n + m) • x = ϖ ^ m • ϖ ^ n • x := by rw [← mul_smul, ← pow_add, add_comm]
    have h₂ : ϖ ^ (n + m) • y = ϖ ^ n • ϖ ^ m • y := by rw [← mul_smul, ← pow_add]
    rw [smul_add, h₁, h₂]
    exact add_mem (L'.smul_mem _ hn) (L'.smul_mem _ hm)
  | smul c x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, a, hka⟩ := exists_pow_mul_eq_algebraMap hirr c
    refine ⟨k + n, ?_⟩
    have h : ϖ ^ (k + n) • (c • x) = a • (ϖ ^ n • x) := by
      rw [← algebraMap_smul C (ϖ ^ (k + n)), ← algebraMap_smul C a, ← algebraMap_smul C (ϖ ^ n),
        smul_smul, smul_smul, ← hka, pow_add, map_mul]
      congr 1
      ring
    rw [h]
    exact L'.smul_mem a hn

/-- For a finitely generated submodule $L$ and a submodule $L'$ that spans $V$, some power of the maximal ideal moves $L$ into $L'$. -/
theorem exists_pow_smul_le {L L' : Submodule O V} (hfg : L.FG)
    (hL' : Submodule.span C (L' : Set V) = ⊤) : ∃ m : ℕ, maximalIdeal O ^ m • L ≤ L' := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  choose f hf using exists_pow_smul_mem hirr hL'
  obtain ⟨s, rfl⟩ := hfg
  refine ⟨s.sup f, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hirr, Ideal.span_singleton_pow]
  refine Submodule.smul_le.2 fun r hr x hx => ?_
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  apply L'.smul_mem
  suffices h : Submodule.span O (s : Set V) ≤ L'.comap (ϖ ^ s.sup f • LinearMap.id) from h hx
  rw [Submodule.span_le]
  intro y hy
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := f) hy)
  rw [hd, pow_add, mul_comm, mul_smul]
  exact L'.smul_mem _ (hf y)

/-- **Brauer-Nesbitt for lattices.** Over a discrete valuation ring with fraction field $C$, the reductions of two stable lattices have the same Jordan-Hölder multiplicities. -/
theorem latticeMultiplicity_eq_of_isStableLattice {L L' : Submodule O V}
    (hL : IsStableLattice ρ L) (hL' : IsStableLattice ρ L') {S : Type*} [AddCommGroup S]
    [Module (ResidueField O) S] (W : Representation (ResidueField O) G S) :
    latticeMultiplicity ρ L hL.2 W = latticeMultiplicity ρ L' hL'.2 W := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hirr
  have hϖ₀ : algebraMap O C ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O C)).2 hirr.ne_zero
  have := hL.1
  have := hL'.1
  have hfg : L.FG := Submodule.IsLattice.fg (A := C) L
  have hfg' : L'.FG := Submodule.IsLattice.fg (A := C) L'
  obtain ⟨m, hm⟩ := exists_pow_smul_le hfg (Submodule.IsFullLattice.span_eq_top (A := C) (M := L'))
  obtain ⟨m', hm'⟩ := exists_pow_smul_le hfg' (Submodule.IsFullLattice.span_eq_top (A := C) (M := L))
  have hinf := hL.2.inf hL'.2
  rw [latticeMultiplicity_eq_of_pow_smul_le hϖ hϖ₀ hL.2 hinf hfg inf_le_left m
      (le_inf Submodule.smul_le_right hm) W,
    latticeMultiplicity_eq_of_pow_smul_le hϖ hϖ₀ hL'.2 hinf hfg' inf_le_right m'
      (le_inf hm' Submodule.smul_le_right) W]

/-- **Brauer-Nesbitt.** Over a discrete valuation ring with fraction field $C$, the multiplicities $n_{a,b}(\rho, L)$ do not depend on the stable lattice $L$. -/
theorem serreMultiplicityIndependent (ρ : Representation C G V)
    (θ : G →* GL (Fin 2) (ResidueField O)) : SerreMultiplicityIndependent O ρ θ :=
  fun _ _ hL hL' _ _ => latticeMultiplicity_eq_of_isStableLattice hL hL' _

/-- Over a discrete valuation ring with fraction field $C$, the multiplicity $n_{a,b}(\rho)$ is its value at each stable lattice. -/
theorem serreMultiplicity_eq_latticeSerreMultiplicity (ρ : Representation C G V)
    (θ : G →* GL (Fin 2) (ResidueField O)) {L : Submodule O V} (hL : IsStableLattice ρ L)
    (a b : ℕ) : serreMultiplicity O ρ θ a b = latticeSerreMultiplicity ρ L hL.2 θ a b :=
  serreMultiplicity_eq ρ θ (serreMultiplicityIndependent ρ θ) L hL a b

end DiscreteValuationRing

section TrivialSanity

open IsLocalRing MvPolynomial

/-- For $a \ne 0$ the homogeneous polynomials of degree $a$ in two variables do not form a line. -/
theorem isEmpty_homogeneous_equiv {k : Type*} [Field k] {a : ℕ} (ha : a ≠ 0) :
    IsEmpty (homogeneousSubmodule (Fin 2) k a ≃ₗ[k] k) := by
  refine ⟨fun f => ?_⟩
  let v₀ : homogeneousSubmodule (Fin 2) k a :=
    ⟨X 0 ^ a, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow 0 a)⟩
  let v₁ : homogeneousSubmodule (Fin 2) k a :=
    ⟨X 1 ^ a, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow 1 a)⟩
  have h : f (f v₁ • v₀ - f v₀ • v₁) = 0 := by
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  rw [LinearEquiv.map_eq_zero_iff] at h
  have hc := congrArg (fun P : homogeneousSubmodule (Fin 2) k a => P.1.coeff (Finsupp.single 0 a)) h
  have h01 : Finsupp.single (1 : Fin 2) a ≠ Finsupp.single 0 a := by
    rw [Ne, Finsupp.single_left_inj ha]
    decide
  simp [v₀, v₁, coeff_X_pow, h01] at hc

variable {k : Type*} [Field k] {G : Type*} [Group G]

/-- The Serre weight $\sigma_{0,b}$ acts by $\det^b$. -/
theorem serreWeightRep_zero (θ : G →* GL (Fin 2) k) (b : ℕ) (g : G) :
    serreWeightRep θ 0 b g = ((θ g : Matrix (Fin 2) (Fin 2) k).det ^ b) • 1 := by
  have h := serreWeightRep_zero_zero θ g
  simp only [serreWeightRep, MonoidHom.comp_apply, serreWeight, MonoidHom.coe_mk, OneHom.coe_mk,
    pow_zero, one_smul] at h ⊢
  rw [h]

variable {O : Type*} [CommRing O] [IsLocalRing O] {L : Type*} [AddCommGroup L] [Module O L]

open Classical in
/-- If the reduction of $\sigma$ is an irreducible $W_0$, then the multiplicity of $W$ is $1$ if $W \cong W_0$ and $0$ otherwise. -/
theorem reductionMultiplicity_eq_ite {σ : Representation O G L} {S₀ : Type*} [AddCommGroup S₀]
    [Module (ResidueField O) S₀] {W₀ : Representation (ResidueField O) G S₀}
    [IsSimpleModule (MonoidAlgebra (ResidueField O) G) W₀.asModule] (φ : (reduction σ).Equiv W₀)
    {S : Type*} [AddCommGroup S] [Module (ResidueField O) S]
    (W : Representation (ResidueField O) G S) :
    reductionMultiplicity σ W =
      if Nonempty (W₀.asModule ≃ₗ[MonoidAlgebra (ResidueField O) G] W.asModule) then 1 else 0 := by
  rw [reductionMultiplicity, jhMultiplicity_congr _ (asModuleEquivOfEquiv φ),
    jhMultiplicity_of_isSimpleModule]

/-- **Sanity check.** For $a \ne 0$ the multiplicity $n_{a,b}$ of the trivial representation on $O$ is zero. -/
theorem reductionMultiplicity_trivial_of_ne_zero (θ : G →* GL (Fin 2) (ResidueField O)) {a : ℕ}
    (ha : a ≠ 0) (b : ℕ) :
    reductionMultiplicity (Representation.trivial O G O) (serreWeightRep θ a b) = 0 := by
  rw [reductionMultiplicity_eq_ite (reductionTrivialEquiv θ)]
  refine ite_eq_right ?_
  rintro ⟨e⟩
  let e' := ((Representation.asModuleEquiv _).symm.trans (e.restrictScalars (ResidueField O))).trans
    (Representation.asModuleEquiv _)
  exact (isEmpty_homogeneous_equiv ha).elim (e'.symm.trans (homogeneousZeroEquiv _))

open Classical in
/-- **Sanity check.** The multiplicity $n_{0,b}$ of the trivial representation on $O$ is one if $\det^b \circ \theta$ is trivial, and zero otherwise. -/
theorem reductionMultiplicity_trivial_zero (θ : G →* GL (Fin 2) (ResidueField O)) (b : ℕ) :
    reductionMultiplicity (Representation.trivial O G O) (serreWeightRep θ 0 b) =
      if ∀ g, (θ g : Matrix (Fin 2) (Fin 2) (ResidueField O)).det ^ b = 1 then 1 else 0 := by
  classical
  rw [reductionMultiplicity_eq_ite (reductionTrivialEquiv θ)]
  by_cases h : ∀ g, (θ g : Matrix (Fin 2) (Fin 2) (ResidueField O)).det ^ b = 1
  · have hb : serreWeightRep θ 0 b = serreWeightRep θ 0 0 := MonoidHom.ext fun g => by
      rw [serreWeightRep_zero, h g, one_smul, serreWeightRep_zero_zero]
    rw [ite_eq_left h, ite_eq_left]
    rw [hb]
    exact ⟨LinearEquiv.refl _ _⟩
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨e⟩
    apply h
    intro g
    let x : (serreWeightRep θ 0 0).asModule := (homogeneousZeroEquiv _).symm 1
    have h₁ : (MonoidAlgebra.single g (1 : ResidueField O) • x) = x := by
      rw [Representation.single_smul, serreWeightRep_zero_zero, one_smul]
      rfl
    have h₂ : MonoidAlgebra.single g (1 : ResidueField O) • e x =
        (θ g : Matrix (Fin 2) (Fin 2) (ResidueField O)).det ^ b • e x := by
      rw [Representation.single_smul, one_smul, serreWeightRep_zero]
      rfl
    have he := e.map_smul (MonoidAlgebra.single g 1) x
    rw [h₁, h₂] at he
    have hx : e x ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact (LinearEquiv.map_ne_zero_iff _).2 one_ne_zero
    let y : homogeneousSubmodule (Fin 2) (ResidueField O) 0 := e x
    have hy : y ≠ 0 := hx
    have he' : y = (θ g : Matrix (Fin 2) (Fin 2) (ResidueField O)).det ^ b • y := he
    exact smul_left_injective (ResidueField O) hy (he'.symm.trans (one_smul _ y).symm)

end TrivialSanity

section Coefficients

/-! ### The coefficient field

The coefficients are a finite extension $E$ of $\mathbb{Q}_p$ that is itself a non-archimedean local field, and whose valuation extends the valuation of $\mathbb{Q}_p$. -/

open IsLocalRing ValuativeRel

variable (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra ℚ_[p] E]

section Embedding

variable [FiniteDimensional ℚ_[p] E]

/-- A chosen embedding $E \hookrightarrow \overline{\mathbb{Q}}_p$ over $\mathbb{Q}_p$. -/
noncomputable def coeffEmbedding : E →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p] :=
  IsAlgClosed.lift

/-- The embedding $E \hookrightarrow \overline{\mathbb{Q}}_p$ is injective. -/
theorem coeffEmbedding_injective : Function.Injective (coeffEmbedding p E) :=
  (coeffEmbedding p E).toRingHom.injective

end Embedding

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension ℚ_[p] E]

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The structure map $\mathbb{Q}_p \to E$ sends $\mathbb{Z}_p$ into $O_E$. -/
theorem algebraMap_mem_integer {x : ℚ_[p]} (hx : x ∈ 𝒪[ℚ_[p]]) :
    algebraMap ℚ_[p] E x ∈ 𝒪[E] := by
  have h₁ : x ≤ᵥ 1 := by
    rw [Valuation.vle_iff_le (valuation ℚ_[p]), map_one]
    exact hx
  have h₂ := (ValuativeExtension.vle_iff_vle (B := E) (a := x) (b := 1)).2 h₁
  rw [map_one, Valuation.vle_iff_le (valuation E), map_one] at h₂
  exact h₂

/-- The ring map $\mathbb{Z}_p \to O_E$. -/
noncomputable def integersAlgebraMap : 𝒪[ℚ_[p]] →+* 𝒪[E] :=
  ((algebraMap ℚ_[p] E).comp (𝒪[ℚ_[p]]).subtype).codRestrict 𝒪[E]
    fun x => algebraMap_mem_integer p E x.2

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/-- The map $\mathbb{Z}_p \to O_E$ is the restriction of the structure map. -/
@[simp]
theorem integersAlgebraMap_apply (x : 𝒪[ℚ_[p]]) :
    (integersAlgebraMap p E x : E) = algebraMap ℚ_[p] E x :=
  rfl

/-- The map $\mathrm{red} : \mathbb{Z}_p \to k$ to the residue field $k$ of $O_E$. -/
noncomputable def coeffRed : 𝒪[ℚ_[p]] →+* 𝓀[E] :=
  (residue 𝒪[E]).comp (integersAlgebraMap p E)

/-- The image of $p$ in $O_E$ lies in the maximal ideal. -/
theorem integersAlgebraMap_p_mem_maximalIdeal :
    integersAlgebraMap p E (p : 𝒪[ℚ_[p]]) ∈ maximalIdeal 𝒪[E] := by
  have h₁ : (p : ℚ_[p]) <ᵥ 1 := by
    rw [Valuation.vlt_iff_lt (valuation ℚ_[p]), map_one]
    exact Padic.valuation_p_lt_one _
  have h₂ := (ValuativeExtension.vlt_iff_vlt (B := E) (a := (p : ℚ_[p])) (b := 1)).2 h₁
  rw [map_one, Valuation.vlt_iff_lt (valuation E), map_one] at h₂
  rw [mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
  exact h₂.ne

/-- The residue field $k$ of $O_E$ has characteristic $p$. -/
theorem charP_residueField : CharP 𝓀[E] p := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  have h := (residue_eq_zero_iff _).2 (integersAlgebraMap_p_mem_maximalIdeal p E)
  rwa [map_natCast] at h

/-- The ring map $\mathrm{red} : \mathbb{Z}_p \to k$ sends $p$ to zero. -/
theorem coeffRed_p : coeffRed p E (p : 𝒪[ℚ_[p]]) = 0 :=
  (residue_eq_zero_iff _).2 (integersAlgebraMap_p_mem_maximalIdeal p E)

/-- **Brauer-Nesbitt for $O_E$.** For a representation $\rho$ over $E$ the multiplicities $n_{a,b}(\rho, L)$ do not depend on the stable lattice $L \subseteq \rho$ over $O_E$. -/
theorem serreMultiplicityIndependent_integer {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V] (ρ : Representation E G V)
    (θ : G →* GL (Fin 2) 𝓀[E]) : SerreMultiplicityIndependent 𝒪[E] ρ θ :=
  serreMultiplicityIndependent ρ θ

end Coefficients

end Langlands
