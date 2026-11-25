/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.Matrix

/-!
# Smooth representations of p-adic groups

Let $G$ be a topological group, for example $GL_n(K)$ for a nonarchimedean local field $K$. A representation $(\pi, V)$ of $G$ on a complex vector space $V$ is *smooth* if the stabilizer of each vector is an open subgroup of $G$. No topology on $V$ is used. A smooth representation is *admissible* if the space $V^U$ of vectors fixed by $U$ has finite dimension for each open subgroup $U$. It is *irreducible* if $V \neq 0$ and the only stable subspaces are $0$ and $V$. For $G = GL_n(K)$ each irreducible smooth representation is admissible (Jacquet, Bernstein).

The basic operations are these.

* The *contragredient* $\pi^\vee$ is the space of smooth vectors in the algebraic dual $V^*$, with $\pi^\vee(g)\lambda = \lambda \circ \pi(g^{-1})$.
* The *twist* $\pi \otimes \theta$ by a character $\theta : G \to \mathbb{C}^\times$ with open kernel is $g \mapsto \theta(g) \pi(g)$ on the same space. For $GL_n(K)$ the characters are $\chi \circ \det$ for the smooth characters $\chi$ of $K^\times$.
* The *central character* of $\pi$ is the character $\omega_\pi$ of $K^\times$ with $\pi(a \cdot 1) = \omega_\pi(a)$ for each $a \in K^\times$. By Schur's lemma for admissible representations it exists when $\pi$ is irreducible.

For $GL_2(K)$ the file also gives the principal series. For two characters $\chi_1, \chi_2$ of $K^\times$, the normalized induced representation $\mathrm{Ind}(\chi_1, \chi_2)$ is the space of locally constant functions $f : GL_2(K) \to \mathbb{C}$ with $f(bg) = \chi_1(a)\chi_2(d)|a/d|^{1/2} f(g)$ for each upper triangular $b$ with diagonal $(a, d)$. The group acts by right translation.

The *character* of an admissible representation is a locally constant function $\theta_\pi$ on the regular semisimple elements, with $\mathrm{tr}\,\pi(f) = \int f \theta_\pi$ (Harish-Chandra). The file uses the pointwise form: for $g$ regular and $U$ a small compact open subgroup, $\theta_\pi(g)$ is the trace of $\pi(g)$ followed by the projection to $V^U$.

* `Langlands.SmoothRep`: a smooth representation of $G$.
* `Langlands.SmoothRep.IsIrreducible`, `Langlands.SmoothRep.IsAdmissible`.
* `Langlands.IrrSmooth`: the isomorphism classes of irreducible admissible representations.
* `Langlands.SmoothRep.contragredient`, `Langlands.SmoothRep.twist`, `Langlands.SmoothRep.charRep`, `Langlands.SmoothRep.restrict`, `Langlands.SmoothRep.sub`.
* `Langlands.normAbs`: the normalized absolute value $|x| = q^{-v(x)}$ of $K$.
* `Langlands.SmoothRep.HasCentralChar`, `Langlands.SmoothRep.IsSupercuspidal`.
* `Langlands.principalSeries`: the representations $\mathrm{Ind}(\chi_1, \chi_2)$ of $GL_2(K)$.
* `Langlands.SmoothRep.IsCharacterValue`: the value of the Harish-Chandra character at an element.
* `Langlands.SmoothRep.charRep_isIrreducible`: a character gives an irreducible admissible representation of dimension one.
* `Langlands.SmoothRep.charRep_iso_iff`: two characters give isomorphic representations exactly when they are equal.

## Implementation notes

A smooth representation is a bundled structure with the carrier in the same universe as the group, so that the isomorphism classes form a type. The representations of dimension one use `ULift ℂ`.

The operations on isomorphism classes are relations on representatives. For example `IrrSmooth.IsTwist y x θ` says that $y$ is the class of $\pi \otimes \theta$ for some $\pi$ in the class $x$. This avoids the proofs that each operation keeps irreducibility and respects isomorphism, which are true but are not needed for the statements.

The smooth characters of $K^\times$ are the homomorphisms $K^\times \to \mathbb{C}^\times$ with open kernel. These are the continuous characters, since $\mathbb{C}^\times$ has no small subgroups and the groups $1 + \mathfrak{m}^k$ are a basis of neighbourhoods of $1$.

## References

* I. N. Bernstein, A. V. Zelevinsky, Representations of the group GL(n, F) where F is a non-archimedean local field, Russian Math. Surveys 31 (1976).
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapters 1 to 3.
* Harish-Chandra, Admissible invariant distributions on reductive p-adic groups, University Lecture Series 16, AMS, 1999.
-/

namespace Langlands

universe u v

open Matrix ValuativeRel IsLocalRing

section General

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The stabilizer $\{g \in G : \rho(g) v = v\}$ of a vector $v$. -/
def vecStabilizer (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have := congrArg (ρ a⁻¹) ha
    simpa using this.symm

omit [TopologicalSpace G] in
theorem mem_vecStabilizer (ρ : Representation ℂ G V) (v : V) (g : G) :
    g ∈ vecStabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

/-- The space $V^U$ of vectors fixed by a subgroup $U$. -/
def fixedVectors (ρ : Representation ℂ G V) (U : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, ρ g v = v}
  add_mem' ha hb g hg := by simp [ha g hg, hb g hg]
  zero_mem' _ _ := map_zero _
  smul_mem' c _ hv g hg := by simp [hv g hg]

/-- A subspace $W \subseteq V$ is stable if $\rho(g) W \subseteq W$ for each $g$. -/
def IsStableSubspace (ρ : Representation ℂ G V) (W : Submodule ℂ V) : Prop :=
  ∀ g, W ≤ W.comap (ρ g)

/-- A representation is smooth if the stabilizer of each vector is open. -/
def IsSmooth (ρ : Representation ℂ G V) : Prop :=
  ∀ v, IsOpen (vecStabilizer ρ v : Set G)

variable [IsTopologicalGroup G]

/-- The smooth vectors of a representation: the vectors with open stabilizer. They form a stable subspace. -/
def smoothVectors (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {v | IsOpen (vecStabilizer ρ v : Set G)}
  zero_mem' := by
    have : (vecStabilizer ρ 0 : Set G) = Set.univ := by
      ext g; simp [mem_vecStabilizer]
    simp only [Set.mem_ofPred_eq, this, isOpen_univ]
  add_mem' {a b} ha hb := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer ρ a ⊓ vecStabilizer ρ b) ?_ (ha.inter hb)
    intro g hg
    simp only [Subgroup.mem_inf, mem_vecStabilizer] at hg ⊢
    simp [hg.1, hg.2]
  smul_mem' c v hv := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer ρ v) ?_ hv
    intro g hg
    simp only [mem_vecStabilizer] at hg ⊢
    simp [hg]

theorem smoothVectors_stable (ρ : Representation ℂ G V) :
    IsStableSubspace ρ (smoothVectors ρ) := by
  intro g v hv
  change IsOpen (vecStabilizer ρ (ρ g v) : Set G)
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hf : Continuous f := by
    change Continuous fun h => g⁻¹ * h * g⁻¹⁻¹
    fun_prop
  refine Subgroup.isOpen_mono (H₁ := (vecStabilizer ρ v).comap f) ?_
    (by rw [Subgroup.coe_comap]; exact hf.isOpen_preimage _ hv)
  intro h hh
  rw [Subgroup.mem_comap, mem_vecStabilizer] at hh
  rw [mem_vecStabilizer]
  have := congrArg (ρ g) hh
  simpa [f, map_mul] using this

end General

/-- A smooth representation of a topological group $G$ on a complex vector space. The carrier is in the universe of $G$. -/
structure SmoothRep (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The space of the representation. -/
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module ℂ V]
  /-- The action of $G$. -/
  ρ : Representation ℂ G V
  /-- Each vector has an open stabilizer. -/
  smooth : IsSmooth ρ

attribute [instance] SmoothRep.addCommGroup SmoothRep.module

namespace SmoothRep

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Two smooth representations are isomorphic if a linear isomorphism intertwines the actions. -/
def Iso (π π' : SmoothRep G) : Prop :=
  ∃ e : π.V ≃ₗ[ℂ] π'.V, ∀ g v, e (π.ρ g v) = π'.ρ g (e v)

theorem Iso.refl (π : SmoothRep G) : π.Iso π :=
  ⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩

theorem Iso.symm {π π' : SmoothRep G} (h : π.Iso π') : π'.Iso π := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun g v => e.injective ?_⟩
  simp [he]

theorem Iso.trans {π π' π'' : SmoothRep G} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g v => by simp [he, he']⟩

/-- The setoid of isomorphism of smooth representations. -/
instance setoid : Setoid (SmoothRep G) where
  r := Iso
  iseqv := ⟨Iso.refl, Iso.symm, Iso.trans⟩

/-- A smooth representation is irreducible if $V \neq 0$ and the only stable subspaces are $0$ and $V$. -/
def IsIrreducible (π : SmoothRep G) : Prop :=
  Nontrivial π.V ∧ ∀ W : Submodule ℂ π.V, IsStableSubspace π.ρ W → W = ⊥ ∨ W = ⊤

/-- A smooth representation is admissible if $V^U$ has finite dimension for each open subgroup $U$. -/
def IsAdmissible (π : SmoothRep G) : Prop :=
  ∀ U : Subgroup G, IsOpen (U : Set G) → FiniteDimensional ℂ (fixedVectors π.ρ U)

variable [IsTopologicalGroup G]

/-- The twist $g \mapsto \theta(g)\pi(g)$ of $\pi$ by a character $\theta$ of $G$ with open kernel. -/
def twist (π : SmoothRep G) (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)) : SmoothRep G where
  V := π.V
  ρ :=
    { toFun := fun g => (θ g : ℂ) • π.ρ g
      map_one' := by simp
      map_mul' := fun a b => by
        rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul] }
  smooth v := by
    refine Subgroup.isOpen_mono (H₁ := θ.ker ⊓ vecStabilizer π.ρ v) ?_ (hθ.inter (π.smooth v))
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_vecStabilizer] at hg
    rw [mem_vecStabilizer]
    simp [hg.1, hg.2]

/-- The trivial representation of $G$ on $\mathbb{C}$. -/
def trivialRep (G : Type u) [Group G] [TopologicalSpace G] : SmoothRep G where
  V := ULift.{u} ℂ
  ρ := Representation.trivial ℂ G _
  smooth v := by
    have : (vecStabilizer (Representation.trivial ℂ G (ULift.{u} ℂ)) v : Set G) = Set.univ := by
      ext g; simp [mem_vecStabilizer]
    rw [this]; exact isOpen_univ

/-- The representation of dimension one given by a character $\theta : G \to \mathbb{C}^\times$ with open kernel. -/
def charRep (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)) : SmoothRep G :=
  (trivialRep G).twist θ hθ

/-- A matrix coefficient $g \mapsto \lambda(\pi(g) v)$ of $\pi$. -/
def coeff (π : SmoothRep G) (v : π.V) (l : Module.Dual ℂ π.V) (g : G) : ℂ :=
  l (π.ρ g v)

/-- The restriction of $\pi$ along a continuous homomorphism $f : H \to G$, for example the restriction to a closed subgroup. -/
def restrict {H : Type u} [Group H] [TopologicalSpace H] (π : SmoothRep G) (f : H →* G)
    (hf : Continuous f) : SmoothRep H where
  V := π.V
  ρ := π.ρ.comp f
  smooth v := by
    have : (vecStabilizer (π.ρ.comp f) v : Set H) = f ⁻¹' (vecStabilizer π.ρ v : Set G) := by
      ext h; simp [mem_vecStabilizer]
    rw [this]; exact hf.isOpen_preimage _ (π.smooth v)

/-- A nonzero map of representations from $\sigma$ to $\pi$: $\sigma$ is isomorphic to a subrepresentation of $\pi$ when $\sigma$ is irreducible. -/
def HasHom (σ π : SmoothRep G) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.ρ g (f v)

/-- The subrepresentation of $\pi$ on a stable subspace $W$. -/
def sub (π : SmoothRep G) (W : Submodule ℂ π.V) (hW : IsStableSubspace π.ρ W) : SmoothRep G where
  V := W
  ρ := π.ρ.subrepresentation W hW
  smooth w := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ w) ?_ (π.smooth w)
    intro g hg
    rw [mem_vecStabilizer] at hg ⊢
    exact Subtype.ext hg

/-- The value $c$ of the Harish-Chandra character $\theta_\pi$ at $g$, in pointwise form. There is an open subgroup $U_0$ such that, for each compact open subgroup $U \le U_0$, each basis $(x_i)$ of $V^U$ and the dual family $(\lambda_i)$ of $U$-fixed linear forms, the trace $\sum_i \lambda_i(\pi(g) x_i)$ of $\pi(g)$ followed by the projection to $V^U$ is $c$. -/
def IsCharacterValue (π : SmoothRep G) (g : G) (c : ℂ) : Prop :=
  ∃ U₀ : Subgroup G, IsOpen (U₀ : Set G) ∧
    ∀ U : Subgroup G, IsOpen (U : Set G) → IsCompact (U : Set G) → U ≤ U₀ →
      ∀ (m : ℕ) (x : Fin m → π.V) (l : Fin m → Module.Dual ℂ π.V),
        (∀ i, x i ∈ fixedVectors π.ρ U) → (∀ i, l i ∈ fixedVectors π.ρ.dual U) →
        (∀ i j, l i (x j) = if i = j then 1 else 0) →
        (∀ y ∈ fixedVectors π.ρ U, y ∈ Submodule.span ℂ (Set.range x)) →
        ∑ i, l i (π.ρ g (x i)) = c

/-- The contragredient $\pi^\vee$: the smooth vectors of the dual $V^*$, with $\pi^\vee(g)\lambda = \lambda \circ \pi(g^{-1})$. -/
def contragredient (π : SmoothRep G) : SmoothRep G where
  V := smoothVectors π.ρ.dual
  ρ := π.ρ.dual.subrepresentation _ (smoothVectors_stable _)
  smooth w := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ.dual w) ?_ w.2
    intro g hg
    rw [mem_vecStabilizer] at hg ⊢
    exact Subtype.ext hg

/-- A smooth representation of a group with a central subgroup $Z$ (the image of $\iota$) is supercuspidal if each matrix coefficient has support in $C \cdot Z$ for a compact set $C$. For $GL_n(K)$ with $Z = K^\times$ this is the usual definition. -/
def IsSupercuspidal {Z : Type*} [Group Z] (π : SmoothRep G) (ι : Z →* G) : Prop :=
  ∀ (v : π.V) (l : (smoothVectors π.ρ.dual : Submodule ℂ (Module.Dual ℂ π.V))),
    ∃ C : Set G, IsCompact C ∧ ∀ g, π.coeff v l g ≠ 0 → ∃ c ∈ C, ∃ z, g = c * ι z

end SmoothRep

/-- An irreducible admissible smooth representation. -/
abbrev IrrRep (G : Type u) [Group G] [TopologicalSpace G] : Type (u + 1) :=
  {π : SmoothRep G // π.IsIrreducible ∧ π.IsAdmissible}

/-- The isomorphism classes of irreducible admissible smooth representations of $G$. For $GL_n(K)$ these are the isomorphism classes of irreducible smooth representations. -/
def IrrSmooth (G : Type u) [Group G] [TopologicalSpace G] : Type (u + 1) :=
  Quotient (Setoid.comap Subtype.val (SmoothRep.setoid (G := G)) : Setoid (IrrRep G))

namespace IrrSmooth

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The class of an irreducible admissible representation. -/
def mk (π : IrrRep G) : IrrSmooth G :=
  Quotient.mk _ π

/-- `y` is the class of a twist $\pi \otimes \theta$ of a representative $\pi$ of `x`. -/
def IsTwist (y x : IrrSmooth G) (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)) : Prop :=
  ∃ π π' : IrrRep G, mk π = x ∧ mk π' = y ∧ π'.1.Iso (π.1.twist θ hθ)

/-- `y` is the class of the contragredient of a representative of `x`. -/
def IsContragredient (y x : IrrSmooth G) : Prop :=
  ∃ π π' : IrrRep G, mk π = x ∧ mk π' = y ∧ π'.1.Iso π.1.contragredient

end IrrSmooth

section GeneralLinear

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The number $q$ of elements of the residue field of $K$. -/
noncomputable def residueCard : ℕ :=
  Nat.card 𝓀[K]

open scoped Classical in
/-- The normalized absolute value of $K$: $|x| = q^{-v(x)}$ for $x \neq 0$, where $v$ is the normalized valuation, and $|0| = 0$. A uniformizer has absolute value $q^{-1}$. -/
noncomputable def normAbs (x : K) : ℝ :=
  if x = 0 then 0 else
    (residueCard K : ℝ) ^ WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K x))

/-- The smooth characters of $K^\times$: the homomorphisms to $\mathbb{C}^\times$ with open kernel. -/
def IsSmoothChar (χ : Kˣ →* ℂˣ) : Prop :=
  IsOpen (χ.ker : Set Kˣ)

/-- The character $\chi \circ \det$ of $GL_n(K)$. -/
noncomputable def detChar (n : ℕ) (χ : Kˣ →* ℂˣ) : GL (Fin n) K →* ℂˣ :=
  χ.comp Matrix.GeneralLinearGroup.det

theorem isOpen_ker_detChar (n : ℕ) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    IsOpen ((detChar K n χ).ker : Set (GL (Fin n) K)) := by
  have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · simp only [Function.comp_def, Matrix.GeneralLinearGroup.val_det_apply]
      exact (continuous_id.matrix_det).comp Units.continuous_val
    · simp only [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      exact (continuous_id.matrix_det).comp (Units.continuous_val.comp continuous_inv)
  exact hc.isOpen_preimage _ hχ

/-- The embedding $a \mapsto a \cdot 1$ of $K^\times$ as the center of $GL_n(K)$. -/
noncomputable def scalarGL (n : ℕ) : Kˣ →* GL (Fin n) K :=
  Units.map (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K).toMonoidHom

namespace SmoothRep

variable {K}

/-- $\pi$ has central character $\omega$: $\pi(a \cdot 1) = \omega(a)$ for each $a \in K^\times$. -/
def HasCentralChar {n : ℕ} (π : SmoothRep (GL (Fin n) K)) (ω : Kˣ →* ℂˣ) : Prop :=
  ∀ (a : Kˣ) (v : π.V), π.ρ (scalarGL K n a) v = (ω a : ℂ) • v

end SmoothRep

/-- The principal series $\mathrm{Ind}(\chi_1, \chi_2)$ of $GL_2(K)$ as a space of functions: the functions $f$ that are invariant on the right under an open subgroup and satisfy $f(bg) = \chi_1(a)\chi_2(d)|a/d|^{1/2} f(g)$ for each upper triangular $b$ with diagonal $(a, d)$. -/
def principalSeriesSpace (χ₁ χ₂ : Kˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) K → ℂ) where
  carrier := {f | (∀ (b g : GL (Fin 2) K) (a d : Kˣ), (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
      (b : Matrix (Fin 2) (Fin 2) K) 0 0 = a → (b : Matrix (Fin 2) (Fin 2) K) 1 1 = d →
      f (b * g) = (χ₁ a : ℂ) * χ₂ d * (Real.sqrt (normAbs K ((a : K) / d)) : ℂ) * f g) ∧
    ∃ U : Subgroup (GL (Fin 2) K), IsOpen (U : Set (GL (Fin 2) K)) ∧ ∀ g, ∀ u ∈ U, f (g * u) = f g}
  add_mem' {f f'} hf hf' := by
    refine ⟨fun b g a d h1 h2 h3 => ?_, ?_⟩
    · simp only [Pi.add_apply, hf.1 b g a d h1 h2 h3, hf'.1 b g a d h1 h2 h3]; ring
    · obtain ⟨U, hU, hfU⟩ := hf.2
      obtain ⟨U', hU', hfU'⟩ := hf'.2
      exact ⟨U ⊓ U', hU.inter hU', fun g u hu => by
        simp [hfU g u (Subgroup.mem_inf.1 hu).1, hfU' g u (Subgroup.mem_inf.1 hu).2]⟩
  zero_mem' := ⟨fun _ _ _ _ _ _ _ => by simp, ⊤, by simp, fun _ _ _ => rfl⟩
  smul_mem' c f hf := by
    refine ⟨fun b g a d h1 h2 h3 => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.1 b g a d h1 h2 h3]; ring
    · obtain ⟨U, hU, hfU⟩ := hf.2
      exact ⟨U, hU, fun g u hu => by simp [hfU g u hu]⟩

/-- The right regular representation $(h \cdot f)(g) = f(gh)$ on functions on $G$. -/
def rightRegular (G : Type u) [Group G] : Representation ℂ G (G → ℂ) where
  toFun h :=
    { toFun := fun f g => f (g * h)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

theorem principalSeriesSpace_stable (χ₁ χ₂ : Kˣ →* ℂˣ) :
    IsStableSubspace (rightRegular (GL (Fin 2) K)) (principalSeriesSpace K χ₁ χ₂) := by
  intro h f hf
  refine ⟨fun b g a d h1 h2 h3 => ?_, ?_⟩
  · change f (b * g * h) = _ * f (g * h)
    rw [mul_assoc, hf.1 b (g * h) a d h1 h2 h3]
  · obtain ⟨U, hU, hfU⟩ := hf.2
    let c : GL (Fin 2) K →* GL (Fin 2) K := (MulAut.conj h⁻¹).toMonoidHom
    have hc : Continuous c := by
      change Continuous fun x => h⁻¹ * x * h⁻¹⁻¹
      fun_prop
    refine ⟨U.comap c, by rw [Subgroup.coe_comap]; exact hc.isOpen_preimage _ hU, fun g u hu => ?_⟩
    change f (g * u * h) = f (g * h)
    have := hfU (g * h) _ (Subgroup.mem_comap.1 hu)
    simpa [c, mul_assoc] using this

/-- The principal series representation $\mathrm{Ind}(\chi_1, \chi_2)$ of $GL_2(K)$ (normalized induction from the upper triangular Borel subgroup). It is irreducible unless $\chi_1\chi_2^{-1} = |\cdot|^{\pm 1}$. When $\chi_1 = \chi_2 |\cdot|$, its unique irreducible subrepresentation is the twist $\mathrm{St} \otimes (\chi_2|\cdot|^{1/2}) \circ \det$ of the Steinberg representation. When $\chi_1 = \chi_2 |\cdot|^{-1}$, it is the character $(\chi_2 |\cdot|^{-1/2}) \circ \det$. -/
noncomputable def principalSeries (χ₁ χ₂ : Kˣ →* ℂˣ) : SmoothRep (GL (Fin 2) K) where
  V := principalSeriesSpace K χ₁ χ₂
  ρ := (rightRegular (GL (Fin 2) K)).subrepresentation _ (principalSeriesSpace_stable K χ₁ χ₂)
  smooth f := by
    obtain ⟨U, hU, hfU⟩ := f.2.2
    refine Subgroup.isOpen_mono (H₁ := U) ?_ hU
    intro u hu
    rw [mem_vecStabilizer]
    exact Subtype.ext (funext fun g => hfU g u hu)

end GeneralLinear

section Sanity

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance : Module.Finite ℂ (ULift.{u} ℂ) :=
  Module.Finite.equiv ULift.moduleEquiv.symm

/-- The representation of dimension one given by a character is irreducible and admissible. -/
theorem SmoothRep.charRep_isIrreducible (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)) :
    (SmoothRep.charRep θ hθ).IsIrreducible ∧ (SmoothRep.charRep θ hθ).IsAdmissible := by
  refine ⟨⟨inferInstanceAs (Nontrivial (ULift.{u} ℂ)), fun W _ => ?_⟩, fun U _ => ?_⟩
  · by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      rw [eq_top_iff]
      intro x _
      have hw0' : (w : ULift.{u} ℂ).down ≠ 0 := fun h => hw0 (ULift.ext h)
      have : x = (x.down / w.down) • w := by
        apply ULift.ext
        change x.down = x.down / w.down * w.down
        field_simp
      rw [this]
      exact W.smul_mem _ hw
  · have : FiniteDimensional ℂ (charRep θ hθ).V := inferInstanceAs (FiniteDimensional ℂ (ULift.{u} ℂ))
    exact FiniteDimensional.finiteDimensional_submodule _

/-- Two characters give isomorphic representations of dimension one only if they are equal. -/
theorem SmoothRep.charRep_iso_iff (θ θ' : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G))
    (hθ' : IsOpen (θ'.ker : Set G)) :
    (SmoothRep.charRep θ hθ).Iso (SmoothRep.charRep θ' hθ') ↔ θ = θ' := by
  constructor
  · rintro ⟨e, he⟩
    ext g
    have h1 := he g (ULift.up 1)
    have h2 : e ((charRep θ hθ).ρ g (ULift.up 1)) = (θ g : ℂ) • e (ULift.up 1) :=
      e.map_smul (θ g : ℂ) (ULift.up 1)
    have h3 : (charRep θ' hθ').ρ g (e (ULift.up 1)) = (θ' g : ℂ) • e (ULift.up 1) := rfl
    rw [h2, h3] at h1
    have hne : e (ULift.up 1) ≠ 0 := by
      intro h
      have := e.injective (h.trans (map_zero e).symm)
      exact one_ne_zero (congrArg ULift.down this)
    exact smul_left_injective ℂ hne h1
  · rintro rfl
    exact Iso.refl _

end Sanity

end Langlands
