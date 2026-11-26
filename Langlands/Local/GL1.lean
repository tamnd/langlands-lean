/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.LocalLanglands
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# The local Langlands correspondence for $GL_1$

Let $K$ be a nonarchimedean local field and let $\mathrm{art}_K : K^\times \to W_K^{ab}$ be a local Artin map. This file builds the bijection $\mathrm{rec}_1 : \mathrm{Irr}(GL_1(K)) \to \mathrm{WD}_1(W_K)$, $\chi \circ \det \mapsto (\chi \circ \mathrm{art}_K^{-1}, 0)$, and proves conditions 1 to 4 of `Langlands.LocalLanglandsGL` for it. It also builds $\mathrm{rec}_0$ between two sets with one element and proves all its conditions. The one condition that is not proved is condition 5 for $m = 1$: the Godement-Jacquet L-factor of a character is the L-factor of the Weil-Deligne representation. This is Tate's local theory, and it is the named proposition `Langlands.LocalGL1.GL1LFactor`. The file proves that `GL1LFactor` implies `LocalLanglandsGL 1`.

## Main definitions

* `Langlands.LocalGL1.irrChar`: the smooth character $\chi$ of $K^\times$ such that $\pi \cong \chi \circ \det$.
* `Langlands.LocalGL1.irrEquiv`: the bijection between $\mathrm{Irr}(GL_1(K))$ and the smooth characters of $K^\times$.
* `Langlands.LocalGL1.wdOfChar`: the Weil-Deligne representation $(\chi \circ \mathrm{art}_K^{-1}, 0)$ of dimension one.
* `Langlands.LocalGL1.wdEquiv`: the bijection between the smooth characters of $K^\times$ and $\mathrm{WD}_1(W_K)$.
* `Langlands.LocalGL1.rec1`, `Langlands.LocalGL1.rec0`, `Langlands.LocalGL1.recFamily`: the bijections $\mathrm{rec}_1$, $\mathrm{rec}_0$ and the family $(\mathrm{rec}_0, \mathrm{rec}_1)$.
* `Langlands.LocalGL1.charLFactor`: the L-factor $L(s, \chi)$, which is $(1 - \chi(\varpi) q^{-s})^{-1}$ for $\chi$ unramified and $1$ otherwise.
* `Langlands.LocalGL1.GL1LFactor`: the proposition that the Godement-Jacquet L-factor of $\chi \circ \det$ is the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0)$.

## Main results

* `Langlands.LocalGL1.exists_iso_charRep`: an irreducible admissible representation of a commutative group is a character (Schur's lemma).
* `Langlands.LocalGL1.exists_iso_detChar`: each irreducible admissible representation of $GL_1(K)$ is $\chi \circ \det$ for a smooth character $\chi$.
* `Langlands.LocalGL1.rec1_gl1`, `Langlands.LocalGL1.rec1_central`, `Langlands.LocalGL1.rec1_twist`, `Langlands.LocalGL1.rec1_dual`: conditions 1 to 4 for $\mathrm{rec}_1$.
* `Langlands.LocalGL1.isLanglandsMap_rec0`: all the conditions for $\mathrm{rec}_0$.
* `Langlands.LocalGL1.lFactor_wdOfChar_eq`: the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0)$ is $(1 - \chi(\varpi) q^{-s})^{-1}$ if $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup, and $1$ otherwise.
* `Langlands.LocalGL1.charLFactor_eq_lFactor_of_iff`: $L(s, \chi)$ is the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0)$, if $\chi$ is unramified exactly when $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup.
* `Langlands.LocalGL1.localLanglandsGL_one_of_gl1LFactor`: `GL1LFactor` implies `LocalLanglandsGL 1`.

## Implementation notes

`LocalLanglandsGL 1` asks for bijections $\mathrm{rec}_m$ for each $m \le 1$, so it also asks for $m = 0$. The group $GL_0(K)$ is trivial and $M_0(K)$ has one point, so each zeta integral is the value of the integrand times the volume of $M_0(K)$.

Schur's lemma is proved for each commutative group. The fixed vectors of the stabilizer of a vector $v \neq 0$ make a stable subspace, so the representation has finite dimension. Then each element has an eigenvalue, and its eigenspace is stable.

The file does not prove Tate's local theory in the Godement-Jacquet form. It also does not prove $\mathrm{art}_K(\mathcal{O}_K^\times) = I_K^{ab}$, which is necessary to identify the unramified characters on the two sides. The ε-factors are not part of this file.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta functions, thesis (1950).
* R. Godement, H. Jacquet, Zeta functions of simple algebras, Lecture Notes in Math. 260 (1972).
* M. Harris, R. Taylor, The geometry and cohomology of some simple Shimura varieties, Ann. of Math. Stud. 151 (2001).
-/

namespace Langlands.LocalGL1

universe u

open Matrix

section Schur

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- In an irreducible representation of finite dimension of a commutative group, each element acts by a scalar. -/
theorem exists_smul_of_comm (π : SmoothRep G) (hπ : π.IsIrreducible) [FiniteDimensional ℂ π.V]
    (hG : ∀ g h : G, g * h = h * g) (g : G) : ∃ c : ℂ, ∀ v, π.ρ g v = c • v := by
  have := hπ.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (π.ρ g)
  refine ⟨c, ?_⟩
  have hst : IsStableSubspace π.ρ (Module.End.eigenspace (π.ρ g) c) := by
    intro h v hv
    rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff]
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [← Module.End.mul_apply, ← map_mul, hG, map_mul, Module.End.mul_apply, hv, map_smul]
  rcases hπ.2 _ hst with h | h
  · obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hmem : v ∈ Module.End.eigenspace (π.ρ g) c :=
      Module.End.mem_eigenspace_iff.2 hv.apply_eq_smul
    rw [h, Submodule.mem_bot] at hmem
    exact (hv.2 hmem).elim
  · intro v
    have : v ∈ Module.End.eigenspace (π.ρ g) c := h ▸ Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.1 this

omit [IsTopologicalGroup G] in
/-- An irreducible admissible representation of a commutative group has finite dimension: the space $V^U$ for the stabilizer $U$ of a nonzero vector is stable and nonzero, so it is $V$. -/
theorem finiteDimensional_of_comm (π : SmoothRep G) (hπ : π.IsIrreducible) (hadm : π.IsAdmissible)
    (hG : ∀ g h : G, g * h = h * g) : FiniteDimensional ℂ π.V := by
  have := hπ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  have hst : IsStableSubspace π.ρ (fixedVectors π.ρ (vecStabilizer π.ρ v)) := by
    intro g w hw u hu
    rw [← Module.End.mul_apply, ← map_mul, hG, map_mul, Module.End.mul_apply, hw u hu]
  have hvmem : v ∈ fixedVectors π.ρ (vecStabilizer π.ρ v) := fun u hu => hu
  have htop : fixedVectors π.ρ (vecStabilizer π.ρ v) = ⊤ := by
    rcases hπ.2 _ hst with h | h
    · exact absurd (by simpa [h] using hvmem) hv
    · exact h
  have := hadm _ (π.smooth v)
  exact Module.Finite.equiv (LinearEquiv.ofTop _ htop)

/-- **Schur's lemma for a commutative group.** An irreducible admissible representation of a commutative topological group is isomorphic to the representation of dimension one of a character with open kernel. -/
theorem exists_iso_charRep (π : SmoothRep G) (hπ : π.IsIrreducible) (hadm : π.IsAdmissible)
    (hG : ∀ g h : G, g * h = h * g) :
    ∃ (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)), π.Iso (SmoothRep.charRep θ hθ) := by
  have := hπ.1
  have := finiteDimensional_of_comm π hπ hadm hG
  choose c hc using exists_smul_of_comm π hπ hG
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  have hinj : ∀ a b : ℂ, a • v = b • v → a = b := fun a b h => smul_left_injective ℂ hv h
  let θ₀ : G →* ℂ :=
    { toFun := c
      map_one' := hinj _ _ (by rw [← hc, map_one, one_smul]; rfl)
      map_mul' := fun g h => hinj _ _ (by
        rw [← hc, map_mul, Module.End.mul_apply, hc, hc, smul_smul]) }
  let θ := θ₀.toHomUnits
  have hθ : ∀ g, (θ g : ℂ) = c g := fun g => rfl
  have hker : IsOpen (θ.ker : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ v) (fun u hu => ?_) (π.smooth v)
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hθ, Units.val_one]
    exact hinj _ _ (by rw [← hc, one_smul]; exact hu)
  refine ⟨θ, hker, ?_⟩
  have hspan : Submodule.span ℂ {v} = ⊤ := by
    have hst : IsStableSubspace π.ρ (Submodule.span ℂ {v}) := by
      intro g w hw
      rw [Submodule.mem_comap, hc]
      exact Submodule.smul_mem _ _ hw
    rcases hπ.2 _ hst with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.1 h) hv
    · exact h
  let f : ULift.{u} ℂ →ₗ[ℂ] π.V :=
    { toFun := fun a => a.down • v
      map_add' := fun a b => add_smul _ _ _
      map_smul' := fun a b => smul_smul _ _ _ |>.symm }
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => ULift.ext (hinj _ _ h), fun w => ?_⟩
    have hw : w ∈ Submodule.span ℂ {v} := hspan ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨ULift.up a, rfl⟩
  let e : π.V ≃ₗ[ℂ] (SmoothRep.charRep θ hker).V := (LinearEquiv.ofBijective f hbij).symm
  refine ⟨e, fun g w => ?_⟩
  rw [hc, map_smul]
  rfl

end Schur


section Matrix

/-- Two elements of $GL_1(R)$ commute. -/
theorem gl_one_mul_comm {R : Type*} [CommRing R] (g h : GL (Fin 1) R) : g * h = h * g := by
  apply Units.ext
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simp [Matrix.mul_apply, mul_comm]

/-- The embedding $\iota : R^\times \to GL_1(R)$. -/
noncomputable def unitGL (R : Type*) [CommRing R] : Rˣ →* GL (Fin 1) R :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

/-- The entry of the matrix $\iota(c)$ is $c$. -/
theorem unitGL_apply_zero {R : Type*} [CommRing R] (c : Rˣ) :
    ((unitGL R c : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) 0 0 = c := by
  simp [unitGL]

/-- The matrix $\iota(c)$ is the diagonal matrix with entry $c$. -/
theorem val_unitGL {R : Type*} [CommRing R] (c : Rˣ) :
    ((unitGL R c : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) = Matrix.diagonal fun _ => (c : R) := by
  simp [unitGL]

/-- The determinant of $\iota(c)$ is $c$. -/
theorem det_unitGL {R : Type*} [CommRing R] (c : Rˣ) :
    Matrix.GeneralLinearGroup.det (unitGL R c) = c := by
  ext; simp [unitGL]

/-- Each element $g$ of $GL_1(R)$ is $\iota(\det g)$. -/
theorem unitGL_det {R : Type*} [CommRing R] (g : GL (Fin 1) R) :
    unitGL R (Matrix.GeneralLinearGroup.det g) = g := by
  apply Units.ext
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simp [unitGL, Matrix.det_unique]

/-- The embedding $\iota : R^\times \to GL_1(R)$ is injective. -/
theorem unitGL_injective {R : Type*} [CommRing R] : Function.Injective (unitGL R) := by
  intro a b h
  rw [← det_unitGL a, h, det_unitGL]

/-- A matrix of size one acts on $\mathbb{C}^1$ as its entry. -/
theorem toLin'_fin_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    Matrix.toLin' A = A 0 0 • LinearMap.id := by
  ext v i
  obtain rfl := Subsingleton.elim i 0
  simp [Matrix.mulVec, dotProduct]

/-- A nilpotent matrix of size one is zero. -/
theorem eq_zero_of_isNilpotent_fin_one {A : Matrix (Fin 1) (Fin 1) ℂ} (h : IsNilpotent A) : A = 0 := by
  have h0 : IsNilpotent (A 0 0) := h.map (Matrix.uniqueRingEquiv : Matrix (Fin 1) (Fin 1) ℂ ≃+* ℂ).toRingHom
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simpa using h0.eq_zero

end Matrix

section Local

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The embedding $K^\times \to GL_1(K)$ is continuous. -/
theorem continuous_unitGL : Continuous (unitGL K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, val_unitGL]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · simp only [← map_inv, val_unitGL]
    exact (continuous_pi fun _ => Units.continuous_val.comp continuous_inv).matrix_diagonal

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Each character $\theta$ of $GL_1(K)$ is $(\theta \circ \iota) \circ \det$. -/
theorem detChar_comp_unitGL (θ : GL (Fin 1) K →* ℂˣ) : detChar K 1 (θ.comp (unitGL K)) = θ := by
  ext g
  simp [detChar, unitGL_det]

/-- Each irreducible admissible representation of $GL_1(K)$ is $\chi \circ \det$ for a smooth character $\chi$ of $K^\times$. -/
theorem exists_iso_detChar (π : IrrRep (GL (Fin 1) K)) :
    ∃ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
      π.1.Iso (SmoothRep.charRep (detChar K 1 χ) (isOpen_ker_detChar K 1 χ hχ)) := by
  obtain ⟨θ, hθ, hiso⟩ := exists_iso_charRep π.1 π.2.1 π.2.2 gl_one_mul_comm
  have hd := detChar_comp_unitGL K θ
  refine ⟨θ.comp (unitGL K), (continuous_unitGL K).isOpen_preimage _ hθ, ?_⟩
  have key : ∀ (θ' : GL (Fin 1) K →* ℂˣ) (hθ' : IsOpen (θ'.ker : Set (GL (Fin 1) K))),
      θ' = θ → π.1.Iso (SmoothRep.charRep θ' hθ') := by
    rintro _ _ rfl
    exact hiso
  exact key _ _ hd


/-- The smooth character $\chi$ of $K^\times$ such that an irreducible representation $\pi$ of $GL_1(K)$ is $\chi \circ \det$. -/
noncomputable def irrChar (π : IrrRep (GL (Fin 1) K)) : Kˣ →* ℂˣ :=
  Classical.choose (exists_iso_detChar K π)

/-- The character of $\pi$ is smooth. -/
theorem isSmoothChar_irrChar (π : IrrRep (GL (Fin 1) K)) : IsSmoothChar K (irrChar K π) :=
  (Classical.choose_spec (exists_iso_detChar K π)).choose

/-- The representation $\pi$ is isomorphic to $\chi \circ \det$ for its character $\chi$. -/
theorem iso_irrChar (π : IrrRep (GL (Fin 1) K)) :
    π.1.Iso (SmoothRep.charRep (detChar K 1 (irrChar K π))
      (isOpen_ker_detChar K 1 _ (isSmoothChar_irrChar K π))) :=
  (Classical.choose_spec (exists_iso_detChar K π)).choose_spec

/-- If $\pi$ is isomorphic to $\chi \circ \det$, then $\pi(g)$ is multiplication by $\chi(\det g)$. -/
theorem rho_eq_of_iso {π : SmoothRep (GL (Fin 1) K)} {χ : Kˣ →* ℂˣ} {hχ : IsSmoothChar K χ}
    (h : π.Iso (SmoothRep.charRep (detChar K 1 χ) (isOpen_ker_detChar K 1 χ hχ)))
    (g : GL (Fin 1) K) (v : π.V) :
    π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  obtain ⟨e, he⟩ := h
  apply e.injective
  rw [he, map_smul]
  rfl

/-- Each $\pi(g)$ is multiplication by $\chi(\det g)$ for the character $\chi$ of $\pi$. -/
theorem rho_irrChar (π : IrrRep (GL (Fin 1) K)) (g : GL (Fin 1) K) (v : π.1.V) :
    π.1.ρ g v = (irrChar K π (Matrix.GeneralLinearGroup.det g) : ℂ) • v :=
  rho_eq_of_iso K (hχ := isSmoothChar_irrChar K π) (iso_irrChar K π) g v

/-- The character of $\pi$ is the only character $\chi$ with $\pi(g) = \chi(\det g)$. -/
theorem irrChar_eq {π : IrrRep (GL (Fin 1) K)} {χ : Kˣ →* ℂˣ}
    (h : ∀ g (v : π.1.V), π.1.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) :
    irrChar K π = χ := by
  have := π.2.1.1
  obtain ⟨v, hv⟩ := exists_ne (0 : π.1.V)
  ext a
  have h1 := h (unitGL K a) v
  rw [rho_irrChar, det_unitGL] at h1
  exact smul_left_injective ℂ hv h1

/-- Isomorphic representations have the same character. -/
theorem irrChar_congr {π π' : IrrRep (GL (Fin 1) K)} (h : π.1.Iso π'.1) :
    irrChar K π = irrChar K π' := by
  obtain ⟨e, he⟩ := h
  refine irrChar_eq K fun g v => e.injective ?_
  rw [he, rho_irrChar, map_smul]

/-- The bijection between the isomorphism classes of irreducible smooth representations of $GL_1(K)$ and the smooth characters of $K^\times$. -/
noncomputable def irrEquiv : IrrSmooth (GL (Fin 1) K) ≃ {χ : Kˣ →* ℂˣ // IsSmoothChar K χ} where
  toFun := Quotient.lift (fun π => ⟨irrChar K π, isSmoothChar_irrChar K π⟩)
    (fun _ _ h => Subtype.ext (irrChar_congr K h))
  invFun χ := charClass K χ.1 χ.2
  left_inv := by
    refine Quotient.ind fun π => ?_
    exact Quotient.sound (iso_irrChar K π).symm
  right_inv χ := Subtype.ext (irrChar_eq (π := ⟨_, SmoothRep.charRep_isIrreducible _
    (isOpen_ker_detChar K 1 χ.1 χ.2)⟩) K fun _ _ => rfl)

variable (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The character $\chi \circ \mathrm{art}_K^{-1}$ of $W_K$. -/
noncomputable def weilChar (χ : Kˣ →* ℂˣ) : WeilGroup K →* ℂˣ :=
  χ.comp (art.symm.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))

/-- The value of $\chi \circ \mathrm{art}_K^{-1}$ at $w$. -/
theorem weilChar_apply (χ : Kˣ →* ℂˣ) (w : WeilGroup K) :
    weilChar K art χ w = χ (art.symm (QuotientGroup.mk w)) :=
  rfl

/-- The characters $\chi$ and $\chi \circ \mathrm{art}_K^{-1}$ correspond through $\mathrm{art}_K$. -/
theorem charCorrespond_weilChar (χ : Kˣ →* ℂˣ) : CharCorrespond K art χ (weilChar K art χ) := by
  intro x w h
  rw [weilChar_apply, h, ContinuousMulEquiv.symm_apply_apply]

/-- The map $W_K \to K^\times$, $w \mapsto \mathrm{art}_K^{-1}(w)$, is continuous. -/
theorem continuous_artSymm_mk :
    Continuous fun w : WeilGroup K => art.symm (QuotientGroup.mk w : WeilGroup.Ab K) :=
  art.symm.continuous.comp continuous_quot_mk

/-- The Weil-Deligne representation $(\chi \circ \mathrm{art}_K^{-1}, 0)$ of dimension one. -/
noncomputable def wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) : WeilDeligneRep K 1 where
  r := (unitGL ℂ).comp (weilChar K art χ)
  isOpen_ker := by
    have : ((unitGL ℂ).comp (weilChar K art χ)).ker = (weilChar K art χ).ker := by
      ext w
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact ⟨fun h => unitGL_injective (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
    rw [this]
    exact (continuous_artSymm_mk K art).isOpen_preimage _ hχ
  N := 0
  isNilpotent := IsNilpotent.zero
  conj w := by simp
  semisimple w := by
    rw [toLin'_fin_one]
    exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id

/-- The value of $r$ for $(\chi \circ \mathrm{art}_K^{-1}, 0)$. -/
theorem wdOfChar_r (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (w : WeilGroup K) :
    (wdOfChar K art χ hχ).r w = unitGL ℂ (weilChar K art χ w) :=
  rfl

/-- The kernel of $\det r$ is open. -/
theorem isOpen_ker_det {m : ℕ} (ρ : WeilDeligneRep K m) :
    IsOpen (ρ.det.ker : Set (WeilGroup K)) := by
  refine Subgroup.isOpen_mono (fun w hw => ?_) ρ.isOpen_ker
  rw [MonoidHom.mem_ker] at hw ⊢
  simp [WeilDeligneRep.det, hw]

/-- The character $\det r$ of $W_K$, as a character of $W_K^{ab}$. -/
noncomputable def detAb {m : ℕ} (ρ : WeilDeligneRep K m) : WeilGroup.Ab K →* ℂˣ :=
  QuotientGroup.lift _ ρ.det (Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker _) (Subgroup.isClosed_of_isOpen _ (isOpen_ker_det K ρ)))

/-- The character $\det r \circ \mathrm{art}_K$ of $K^\times$. -/
noncomputable def charOfWD {m : ℕ} (ρ : WeilDeligneRep K m) : Kˣ →* ℂˣ :=
  (detAb K ρ).comp art.toMulEquiv.toMonoidHom

/-- The value of $\det r \circ \mathrm{art}_K$ at $x$ is $\det r(w)$ when $w$ maps to $\mathrm{art}_K(x)$. -/
theorem charOfWD_apply {m : ℕ} (ρ : WeilDeligneRep K m) {x : Kˣ} {w : WeilGroup K}
    (h : (QuotientGroup.mk w : WeilGroup.Ab K) = art x) : charOfWD K art ρ x = ρ.det w := by
  change detAb K ρ (art x) = _
  rw [← h]
  rfl

/-- The character $\det r \circ \mathrm{art}_K$ is smooth. -/
theorem isSmoothChar_charOfWD {m : ℕ} (ρ : WeilDeligneRep K m) :
    IsSmoothChar K (charOfWD K art ρ) := by
  have h : IsOpen ((detAb K ρ).ker : Set (WeilGroup.Ab K)) :=
    isOpen_coinduced.2 (isOpen_ker_det K ρ)
  exact art.continuous.isOpen_preimage _ h

/-- The characters $\det r \circ \mathrm{art}_K$ and $\det r$ correspond through $\mathrm{art}_K$. -/
theorem charCorrespond_charOfWD {m : ℕ} (ρ : WeilDeligneRep K m) :
    CharCorrespond K art (charOfWD K art ρ) ρ.det :=
  fun _ _ h => charOfWD_apply K art ρ h

/-- A Weil-Deligne representation of dimension one has $N = 0$. -/
theorem N_eq_zero (ρ : WeilDeligneRep K 1) : ρ.N = 0 :=
  eq_zero_of_isNilpotent_fin_one ρ.isNilpotent

/-- In dimension one, $r(w)$ is the matrix $\det r(w)$. -/
theorem r_eq_unitGL_det (ρ : WeilDeligneRep K 1) (w : WeilGroup K) :
    ρ.r w = unitGL ℂ (ρ.det w) :=
  (unitGL_det _).symm

/-- Two isomorphic Weil-Deligne representations of dimension one are equal on $W_K$. -/
theorem r_eq_of_mk_eq {ρ ρ' : WeilDeligneRep K 1} (h : WDIso.mk ρ = WDIso.mk ρ')
    (w : WeilGroup K) : ρ.r w = ρ'.r w := by
  have := WeilDeligneRep.det_eq_of_iso (Quotient.exact h)
  rw [r_eq_unitGL_det, r_eq_unitGL_det, this]

/-- The bijection between the smooth characters of $K^\times$ and the Weil-Deligne representations of dimension one, given by $\chi \mapsto (\chi \circ \mathrm{art}_K^{-1}, 0)$. -/
noncomputable def wdEquiv : {χ : Kˣ →* ℂˣ // IsSmoothChar K χ} ≃ WDIso K 1 where
  toFun χ := WDIso.mk (wdOfChar K art χ.1 χ.2)
  invFun := Quotient.lift (fun ρ => ⟨charOfWD K art ρ, isSmoothChar_charOfWD K art ρ⟩)
    (fun ρ ρ' h => Subtype.ext (by
      ext x
      obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
      rw [charOfWD_apply K art ρ hw, charOfWD_apply K art ρ' hw, WeilDeligneRep.det_eq_of_iso h]))
  left_inv χ := Subtype.ext (by
    ext x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
    change (charOfWD K art (wdOfChar K art χ.1 χ.2) x : ℂ) = χ.1 x
    rw [charOfWD_apply K art _ hw]
    simp [WeilDeligneRep.det, wdOfChar_r, det_unitGL, weilChar_apply, hw])
  right_inv := by
    refine Quotient.ind fun ρ => Quotient.sound ⟨1, fun w => ?_, ?_⟩
    · have h : charOfWD K art ρ (art.symm (QuotientGroup.mk w)) = ρ.det w :=
        charOfWD_apply K art ρ (art.apply_symm_apply _).symm
      simp only [one_mul, inv_one, mul_one]
      rw [wdOfChar_r, weilChar_apply]
      change ρ.r w = unitGL ℂ (charOfWD K art ρ (art.symm (QuotientGroup.mk w)))
      rw [h, r_eq_unitGL_det]
    · simpa [wdOfChar] using N_eq_zero K ρ

/-- The bijection $\mathrm{rec}_1 : \mathrm{Irr}(GL_1(K)) \to \mathrm{WD}_1(W_K)$, $\chi \mapsto \chi \circ \mathrm{art}_K^{-1}$. -/
noncomputable def rec1 : IrrSmooth (GL (Fin 1) K) ≃ WDIso K 1 :=
  (irrEquiv K).trans (wdEquiv K art)

/-- The value of $\mathrm{rec}_1$ at the class of $\pi$. -/
theorem rec1_mk (π : IrrRep (GL (Fin 1) K)) :
    rec1 K art (IrrSmooth.mk π) = WDIso.mk (wdOfChar K art (irrChar K π) (isSmoothChar_irrChar K π)) :=
  rfl

/-- If $\rho$ represents $\mathrm{rec}_1(\pi)$, then $r(w) = \chi(\mathrm{art}_K^{-1}(w))$ for the character $\chi$ of $\pi$. -/
theorem r_of_rec1 {π : IrrRep (GL (Fin 1) K)} {ρ : WeilDeligneRep K 1}
    (h : WDIso.mk ρ = rec1 K art (IrrSmooth.mk π)) (w : WeilGroup K) :
    ρ.r w = unitGL ℂ (weilChar K art (irrChar K π) w) :=
  r_eq_of_mk_eq K h w

/-- If $\rho$ represents $\mathrm{rec}_1(\pi)$, then $\det r = \chi \circ \mathrm{art}_K^{-1}$ for the character $\chi$ of $\pi$. -/
theorem det_of_rec1 {π : IrrRep (GL (Fin 1) K)} {ρ : WeilDeligneRep K 1}
    (h : WDIso.mk ρ = rec1 K art (IrrSmooth.mk π)) (w : WeilGroup K) :
    ρ.det w = weilChar K art (irrChar K π) w := by
  simp [WeilDeligneRep.det, r_of_rec1 K art h, det_unitGL]

/-- Condition 1 for $\mathrm{rec}_1$: if $\rho$ represents $\mathrm{rec}_1(\chi)$, then $r(w) = \chi(x)$ when $w$ maps to $\mathrm{art}_K(x)$. -/
theorem rec1_gl1 (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (ρ : WeilDeligneRep K 1)
    (h : WDIso.mk ρ = rec1 K art (charClass K χ hχ)) (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : WeilGroup.Ab K) = art x) :
    (ρ.r w : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = χ x := by
  have hc : irrChar K ⟨_, SmoothRep.charRep_isIrreducible _ (isOpen_ker_detChar K 1 χ hχ)⟩ = χ :=
    irrChar_eq K fun _ _ => rfl
  rw [r_of_rec1 (π := ⟨_, SmoothRep.charRep_isIrreducible _ (isOpen_ker_detChar K 1 χ hχ)⟩) K art h,
    unitGL_apply_zero, hc, charCorrespond_weilChar K art χ x w hw]

/-- Condition 2 for $\mathrm{rec}_1$: the central character corresponds to the determinant. -/
theorem rec1_central (π : IrrRep (GL (Fin 1) K)) (ω : Kˣ →* ℂˣ) (hω : π.1.HasCentralChar ω)
    (ρ : WeilDeligneRep K 1) (h : WDIso.mk ρ = rec1 K art (IrrSmooth.mk π)) :
    CharCorrespond K art ω ρ.det := by
  have hω' : irrChar K π = ω := by
    refine irrChar_eq K fun g v => ?_
    have e : scalarGL K 1 (Matrix.GeneralLinearGroup.det g) = g := unitGL_det g
    have := hω (Matrix.GeneralLinearGroup.det g) v
    rwa [e] at this
  intro x w hw
  rw [det_of_rec1 K art h, hω']
  exact charCorrespond_weilChar K art ω x w hw

/-- Condition 3 for $\mathrm{rec}_1$: the bijection commutes with the twists by characters. -/
theorem rec1_twist (x y : IrrSmooth (GL (Fin 1) K)) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (hxy : IrrSmooth.IsTwist y x (detChar K 1 χ) (isOpen_ker_detChar K 1 χ hχ))
    (φ : WeilGroup K →* ℂˣ) (hφ : CharCorrespond K art χ φ) :
    WDIso.IsTwist (rec1 K art y) (rec1 K art x) φ := by
  obtain ⟨π, π', rfl, rfl, ⟨e, he⟩⟩ := hxy
  have hc : irrChar K π' = χ * irrChar K π := by
    let e' : π'.1.V ≃ₗ[ℂ] π.1.V := e
    have he' : ∀ g v, e' (π'.1.ρ g v) = (detChar K 1 χ g : ℂ) • π.1.ρ g (e' v) := he
    refine irrChar_eq K fun g v => e'.injective ?_
    rw [he', map_smul, rho_irrChar, smul_smul]
    simp [detChar]
  refine ⟨wdOfChar K art _ (isSmoothChar_irrChar K π), wdOfChar K art _ (isSmoothChar_irrChar K π'),
    rfl, rfl, fun w => ?_, rfl⟩
  have hφw : (φ w : ℂ) = χ (art.symm (QuotientGroup.mk w)) :=
    congrArg Units.val (hφ _ w (art.apply_symm_apply _).symm).symm
  rw [wdOfChar_r, wdOfChar_r, val_unitGL, val_unitGL, hc, hφw, weilChar_apply, weilChar_apply]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Condition 4 for $\mathrm{rec}_1$: the contragredient goes to the dual. -/
theorem rec1_dual (x y : IrrSmooth (GL (Fin 1) K)) (hxy : IrrSmooth.IsContragredient y x) :
    WDIso.IsDual (rec1 K art y) (rec1 K art x) := by
  obtain ⟨π, π', rfl, rfl, ⟨e, he⟩⟩ := hxy
  have hc : irrChar K π' = (irrChar K π)⁻¹ := by
    refine irrChar_eq K fun g v => e.injective ?_
    rw [he, map_smul]
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    change (e v).1 (π.1.ρ g⁻¹ u) = _
    rw [rho_irrChar, map_smul]
    simp [map_inv]
    rfl
  refine ⟨wdOfChar K art _ (isSmoothChar_irrChar K π), wdOfChar K art _ (isSmoothChar_irrChar K π'),
    rfl, rfl, fun w => ?_, by simp [wdOfChar]⟩
  rw [wdOfChar_r, wdOfChar_r, ← map_inv, val_unitGL, val_unitGL, hc, weilChar_apply, weilChar_apply,
    Matrix.diagonal_transpose]
  simp

/-- Two Weil-Deligne representations with the same $r$ and $N$ are equal. -/
theorem wd_ext {m : ℕ} {ρ ρ' : WeilDeligneRep K m} (hr : ρ.r = ρ'.r) (hN : ρ.N = ρ'.N) : ρ = ρ' := by
  cases ρ
  cases ρ'
  cases hr
  cases hN
  rfl

/-- Each representative of $\mathrm{rec}_1(\pi)$ is $(\chi \circ \mathrm{art}_K^{-1}, 0)$ for the character $\chi$ of $\pi$. -/
theorem eq_wdOfChar_of_rec1 {π : IrrRep (GL (Fin 1) K)} {ρ : WeilDeligneRep K 1}
    (h : WDIso.mk ρ = rec1 K art (IrrSmooth.mk π)) :
    ρ = wdOfChar K art (irrChar K π) (isSmoothChar_irrChar K π) :=
  wd_ext K (MonoidHom.ext (r_of_rec1 K art h)) (N_eq_zero K ρ)

/-- The conditions 2 to 5 for $\mathrm{rec}_1$, when the L-factors of the characters are known. -/
theorem isLanglandsMap_rec1
    (hL : ∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (π : SmoothRep (GL (Fin 1) K)),
      (∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) →
        IsGJLFactor K π (wdOfChar K art χ hχ).lFactor) :
    IsLanglandsMap K art 1 (rec1 K art) where
  central := rec1_central K art
  twist := rec1_twist K art
  dual := rec1_dual K art
  lFactor π ρ h := by
    rw [eq_wdOfChar_of_rec1 K art h]
    exact hL _ _ π.1 (rho_irrChar K π)

end Local

section LFactor

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- For $(\chi \circ \mathrm{art}_K^{-1}, 0)$, the matrix $r(w)$ acts on $\mathbb{C}^1$ by $\chi(\mathrm{art}_K^{-1}(w))$. -/
theorem mulVec_wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (w : WeilGroup K) (v : Fin 1 → ℂ) :
    ((wdOfChar K art χ hχ).r w : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ v = (weilChar K art χ w : ℂ) • v := by
  rw [← Matrix.toLin'_apply, toLin'_fin_one, LinearMap.smul_apply, LinearMap.id_apply, wdOfChar_r,
    unitGL_apply_zero]

/-- A vector is in $(V^{I_K})_{N = 0}$ for $(\chi \circ \mathrm{art}_K^{-1}, 0)$ exactly when the inertia subgroup fixes it. -/
theorem mem_lSpace_wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (v : Fin 1 → ℂ) :
    v ∈ (wdOfChar K art χ hχ).lSpace ↔
      ∀ i ∈ WeilGroup.inertia K, (weilChar K art χ i : ℂ) • v = v := by
  show ((wdOfChar K art χ hχ).N *ᵥ v = 0 ∧ ∀ i ∈ WeilGroup.inertia K,
    ((wdOfChar K art χ hχ).r i : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ v = v) ↔ _
  simp only [mulVec_wdOfChar]
  exact ⟨fun h => h.2, fun h => ⟨by simp [wdOfChar], h⟩⟩

/-- For $(\varphi, 0)$, the geometric Frobenius acts on $(V^{I_K})_{N = 0}$ by $\varphi(\Phi)$. -/
theorem frobOnLSpace_wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    (wdOfChar K art χ hχ).frobOnLSpace = (weilChar K art χ (geomFrob K) : ℂ) • LinearMap.id := by
  ext v : 1
  apply Subtype.ext
  change ((wdOfChar K art χ hχ).r (geomFrob K) : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ v.1 = _
  rw [mulVec_wdOfChar]
  rfl

open scoped Classical in
/-- The L-factor of $(\varphi, 0)$ for $\varphi = \chi \circ \mathrm{art}_K^{-1}$ is $(1 - \varphi(\Phi) q^{-s})^{-1}$ if $\varphi$ is trivial on the inertia subgroup, and $1$ otherwise. -/
theorem lFactor_wdOfChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (s : ℂ) :
    (wdOfChar K art χ hχ).lFactor s =
      if ∀ i ∈ WeilGroup.inertia K, weilChar K art χ i = 1 then
        (1 - (weilChar K art χ (geomFrob K) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ else 1 := by
  rw [WeilDeligneRep.lFactor]
  split_ifs with h
  · have htop : (wdOfChar K art χ hχ).lSpace = ⊤ :=
      eq_top_iff.2 fun v _ => (mem_lSpace_wdOfChar K art χ hχ v).2 fun i hi => by simp [h i hi]
    have hrank : Module.finrank ℂ (wdOfChar K art χ hχ).lSpace = 1 :=
      (LinearEquiv.ofTop _ htop).finrank_eq.trans (Module.finrank_fin_fun ℂ)
    have he : (1 - ((residueCard K : ℂ) ^ (-s)) • (wdOfChar K art χ hχ).frobOnLSpace) =
        (1 - (weilChar K art χ (geomFrob K) : ℂ) * (residueCard K : ℂ) ^ (-s)) • LinearMap.id := by
      rw [frobOnLSpace_wdOfChar]
      ext v : 1
      apply Subtype.ext
      simp [sub_smul, smul_smul, mul_comm]
    rw [he, LinearMap.det_smul, LinearMap.det_id, hrank, pow_one, mul_one]
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    have hne' : (weilChar K art χ i : ℂ) ≠ 1 := fun h1 => hne (Units.ext h1)
    have h0 : ∀ v ∈ (wdOfChar K art χ hχ).lSpace, v = 0 := by
      intro v hv
      have h1 := (mem_lSpace_wdOfChar K art χ hχ v).1 hv i hi
      have h2 : ((weilChar K art χ i : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne')
    have : Subsingleton (wdOfChar K art χ hχ).lSpace :=
      ⟨fun a b => Subtype.ext ((h0 a a.2).trans (h0 b b.2).symm)⟩
    rw [LinearMap.det_eq_one_of_subsingleton, inv_one]

/-- If $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup, then its value at the geometric Frobenius is $\chi(\varpi)$ for each uniformizer $\varpi$. -/
theorem weilChar_geomFrob (hart : IsLocalArtinMap K art) (χ : Kˣ →* ℂˣ)
    (h : ∀ i ∈ WeilGroup.inertia K, weilChar K art χ i = 1) (ϖ : Kˣ) (hϖ : IsUniformizer (ϖ : K)) :
    weilChar K art χ (geomFrob K) = χ ϖ := by
  obtain ⟨Φ, hΦ, hart'⟩ := hart.uniformizer ϖ hϖ
  have hΦ' : WeilGroup.toResidue K Φ = (LocalField.frobenius K)⁻¹ := hΦ
  have hg : WeilGroup.toResidue K (geomFrob K) = (LocalField.frobenius K)⁻¹ :=
    Classical.choose_spec (WeilGroup.exists_isGeometricFrobenius K)
  have hi : Φ⁻¹ * geomFrob K ∈ WeilGroup.inertia K := by
    rw [WeilGroup.inertia, MonoidHom.mem_ker, map_mul, map_inv, hΦ', hg, inv_mul_cancel]
  rw [charCorrespond_weilChar K art χ ϖ Φ hart'.symm, ← mul_inv_cancel_left Φ (geomFrob K), map_mul,
    h _ hi, mul_one]

open scoped Classical in
/-- **The L-factor of a character on the Weil side.** For a uniformizer $\varpi$, $L(s, \chi \circ \mathrm{art}_K^{-1}) = (1 - \chi(\varpi) q^{-s})^{-1}$ if $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup, and $1$ otherwise. -/
theorem lFactor_wdOfChar_eq (hart : IsLocalArtinMap K art) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (ϖ : Kˣ) (hϖ : IsUniformizer (ϖ : K)) (s : ℂ) :
    (wdOfChar K art χ hχ).lFactor s =
      if ∀ i ∈ WeilGroup.inertia K, weilChar K art χ i = 1 then
        (1 - (χ ϖ : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ else 1 := by
  rw [lFactor_wdOfChar]
  split_ifs with h
  · rw [weilChar_geomFrob K art hart χ h ϖ hϖ]
  · rfl

open scoped Classical in
/-- The L-factor $L(s, \chi)$ of a smooth character $\chi$ of $K^\times$ for a uniformizer $\varpi$: $(1 - \chi(\varpi) q^{-s})^{-1}$ if $\chi$ is unramified, that is trivial on the units $|x| = 1$, and $1$ otherwise. -/
noncomputable def charLFactor (ϖ : Kˣ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 then (1 - (χ ϖ : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ else 1

/-- The L-factor of $\chi$ is the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0)$, if $\chi$ is unramified exactly when $\chi \circ \mathrm{art}_K^{-1}$ is trivial on the inertia subgroup. This condition follows from $\mathrm{art}_K(\mathcal{O}_K^\times) = I_K^{ab}$, which this file does not prove. -/
theorem charLFactor_eq_lFactor_of_iff (hart : IsLocalArtinMap K art) (χ : Kˣ →* ℂˣ)
    (hχ : IsSmoothChar K χ) (ϖ : Kˣ) (hϖ : IsUniformizer (ϖ : K))
    (hunr : (∀ x : Kˣ, normAbs K x = 1 → χ x = 1) ↔
      ∀ i ∈ WeilGroup.inertia K, weilChar K art χ i = 1) (s : ℂ) :
    charLFactor K ϖ χ s = (wdOfChar K art χ hχ).lFactor s := by
  rw [lFactor_wdOfChar_eq K art hart χ hχ ϖ hϖ, charLFactor]
  classical
  exact if_congr hunr rfl rfl

end LFactor

section Zero

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The trivial character of $GL_0(K)$ has an open kernel. -/
theorem isOpen_ker_one : IsOpen ((1 : GL (Fin 0) K →* ℂˣ).ker : Set (GL (Fin 0) K)) := by
  rw [MonoidHom.ker_one, Subgroup.coe_top]
  exact isOpen_univ

/-- The trivial representation of the trivial group $GL_0(K)$. -/
noncomputable def irr0 : IrrRep (GL (Fin 0) K) :=
  ⟨SmoothRep.charRep 1 (isOpen_ker_one K), SmoothRep.charRep_isIrreducible _ _⟩

/-- Each irreducible representation of $GL_0(K)$ is isomorphic to the trivial representation. -/
theorem iso_irr0 (π : IrrRep (GL (Fin 0) K)) : π.1.Iso (irr0 K).1 := by
  obtain ⟨θ, hθ, hiso⟩ := exists_iso_charRep π.1 π.2.1 π.2.2 fun _ _ => Subsingleton.elim _ _
  obtain rfl : θ = 1 := MonoidHom.ext fun g => by
    rw [Subsingleton.elim g 1, map_one, MonoidHom.one_apply]
  exact hiso

/-- There is only one irreducible representation of $GL_0(K)$ up to isomorphism. -/
instance : Subsingleton (IrrSmooth (GL (Fin 0) K)) :=
  ⟨Quotient.ind₂ fun π π' => Quotient.sound ((iso_irr0 K π).trans (iso_irr0 K π').symm)⟩

/-- The Weil-Deligne representation of dimension zero. -/
noncomputable def wd0 : WeilDeligneRep K 0 where
  r := 1
  isOpen_ker := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  N := 0
  isNilpotent := IsNilpotent.zero
  conj _ := Subsingleton.elim _ _
  semisimple _ := by
    rw [Subsingleton.elim (Matrix.toLin' _) LinearMap.id]
    exact Module.End.isSemisimple_id

/-- There is only one Weil-Deligne representation of dimension zero up to isomorphism. -/
instance : Subsingleton (WDIso K 0) :=
  ⟨Quotient.ind₂ fun _ _ => Quotient.sound ⟨1, fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- The bijection $\mathrm{rec}_0$ between two sets with one element. -/
noncomputable def rec0 : IrrSmooth (GL (Fin 0) K) ≃ WDIso K 0 where
  toFun _ := WDIso.mk (wd0 K)
  invFun _ := IrrSmooth.mk (irr0 K)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The normalized absolute value of $1$ is $1$. -/
theorem normAbs_one : normAbs K 1 = 1 := by
  simp [normAbs]

open MeasureTheory in
/-- A zeta integral on $M_0(K)$, a space with one point, is the value of the integrand times the volume. -/
theorem gjZeta_zero (π : SmoothRep (GL (Fin 0) K)) (Φ : Matrix (Fin 0) (Fin 0) K → ℂ) (v : π.V)
    (l : Module.Dual ℂ π.V) (s : ℂ) :
    gjZeta K π Φ v l s = ((matrixHaar K 0).real Set.univ : ℂ) * (Φ 0 * l v) := by
  let := matrixBorel K 0
  have hf : ∀ x : Matrix (Fin 0) (Fin 0) K, x = 0 := fun x => Subsingleton.elim x 0
  have h1 : ∀ g : GL (Fin 0) K, π.ρ g v = v := fun g => by
    rw [Subsingleton.elim g 1, map_one]
    rfl
  unfold gjZeta
  calc _ = ∫ _ : Matrix (Fin 0) (Fin 0) K, Φ 0 * l v ∂(matrixHaar K 0) := by
          congr 1
          funext x
          rw [hf x]
          simp [SmoothRep.coeff, h1, normAbs_one]
    _ = _ := by rw [integral_const, Complex.real_smul]

open MeasureTheory in
/-- The Haar measure of the space $M_0(K)$ with one point is not zero. -/
theorem matrixHaar_zero_real_ne_zero : (matrixHaar K 0).real Set.univ ≠ 0 := by
  let := matrixBorel K 0
  have : BorelSpace (Matrix (Fin 0) (Fin 0) K) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin 0) (Fin 0) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin 0 → Fin 0 → K))
  have : CompactSpace (Matrix (Fin 0) (Fin 0) K) :=
    inferInstanceAs (CompactSpace (Fin 0 → Fin 0 → K))
  have : (matrixHaar K 0).IsAddHaarMeasure := by
    unfold matrixHaar
    infer_instance
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨isOpen_univ.measure_ne_zero _ Set.univ_nonempty, isCompact_univ.measure_lt_top.ne⟩

omit [Field K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The constant function $1$ on $M_0(K)$ is a Schwartz-Bruhat function. -/
theorem isSchwartzBruhat_one : IsSchwartzBruhat K (fun _ : Matrix (Fin 0) (Fin 0) K => (1 : ℂ)) :=
  ⟨IsLocallyConstant.const _, (Set.subsingleton_of_subsingleton (s := tsupport _)).isCompact⟩

/-- The constant function $L = 1$ is the Godement-Jacquet L-factor of each irreducible representation of $GL_0(K)$. -/
theorem isGJLFactor_zero (π : IrrRep (GL (Fin 0) K)) (L : ℂ → ℂ) (hL : ∀ s, L s = 1) :
    IsGJLFactor K π.1 L := by
  refine ⟨⟨1, by simp, fun s => by simp [hL]⟩, fun Φ v l _ =>
    ⟨Polynomial.C (((matrixHaar K 0).real Set.univ : ℂ) * (Φ 0 * l.1 v)), 0, 0,
      fun s _ => by simp [gjZeta_zero, hL]⟩, ?_⟩
  have := π.2.1.1
  obtain ⟨v, hv⟩ := exists_ne (0 : π.1.V)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  have hsm : l ∈ smoothVectors π.1.ρ.dual := by
    have : (vecStabilizer π.1.ρ.dual l : Set (GL (Fin 0) K)) = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        rw [Subsingleton.elim g 1]
        exact one_mem _
    change IsOpen (vecStabilizer π.1.ρ.dual l : Set (GL (Fin 0) K))
    rw [this]
    exact isOpen_univ
  have hc : ((matrixHaar K 0).real Set.univ : ℂ) * l v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (matrixHaar_zero_real_ne_zero K)) hl
  refine ⟨1, fun _ _ => 1, fun _ => v, fun _ => ⟨l, hsm⟩,
    fun _ => Polynomial.C (((matrixHaar K 0).real Set.univ : ℂ) * l v)⁻¹, 0, 0,
    fun _ => isSchwartzBruhat_one K, fun s _ => ?_⟩
  simp only [hL, Fin.sum_univ_one, gjZeta_zero, Polynomial.eval_C, pow_zero, div_one, one_mul]
  exact (inv_mul_cancel₀ hc).symm

/-- The L-factor of a Weil-Deligne representation of dimension zero is $1$. -/
theorem lFactor_zero (ρ : WeilDeligneRep K 0) (s : ℂ) : ρ.lFactor s = 1 := by
  simp [WeilDeligneRep.lFactor, LinearMap.det_eq_one_of_subsingleton]

/-- The conditions 2 to 5 hold for $\mathrm{rec}_0$. -/
theorem isLanglandsMap_rec0 (art : Kˣ ≃ₜ* WeilGroup.Ab K) : IsLanglandsMap K art 0 (rec0 K) where
  central π ω hω ρ _ := by
    have := π.2.1.1
    obtain ⟨v, hv⟩ := exists_ne (0 : π.1.V)
    intro x w _
    have h1 : v = (ω x : ℂ) • v := by
      simpa [Subsingleton.elim (scalarGL K 0 x) 1] using hω x v
    have hx : (ω x : ℂ) = 1 := smul_left_injective ℂ hv (h1.symm.trans (one_smul ℂ v).symm)
    ext
    rw [hx]
    simp [WeilDeligneRep.det]
  twist _ _ _ _ _ _ _ := ⟨wd0 K, wd0 K, Subsingleton.elim _ _, Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _, rfl⟩
  dual _ _ _ := ⟨wd0 K, wd0 K, Subsingleton.elim _ _, Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  lFactor π ρ _ := isGJLFactor_zero K π _ (lFactor_zero K ρ)

end Zero

/-- Tate's local theory for $GL_1$ in the Godement-Jacquet form. For each local Artin map $\mathrm{art}_K$, each smooth character $\chi$ of $K^\times$ and each representation $\pi$ of $GL_1(K)$ that acts by $\chi \circ \det$, the L-factor of the Weil-Deligne representation $(\chi \circ \mathrm{art}_K^{-1}, 0)$ is the Godement-Jacquet L-factor of $\pi$. This is the only part of `LocalLanglandsGL 1` that this file does not prove. -/
def GL1LFactor : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (π : SmoothRep (GL (Fin 1) K)),
        (∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) →
          IsGJLFactor K π (wdOfChar K art χ hχ).lFactor

section Family

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The family $(\mathrm{rec}_0, \mathrm{rec}_1)$. -/
noncomputable def recFamily : ∀ m ≤ 1, IrrSmooth (GL (Fin m) K) ≃ WDIso K m
  | 0, _ => rec0 K
  | 1, _ => rec1 K art
  | _ + 2, h => absurd h (by omega)

/-- The family $(\mathrm{rec}_0, \mathrm{rec}_1)$ has the properties of `IsLanglandsFamily`, when the L-factors of the characters are known. -/
theorem isLanglandsFamily_recFamily
    (hL : ∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (π : SmoothRep (GL (Fin 1) K)),
      (∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) →
        IsGJLFactor K π (wdOfChar K art χ hχ).lFactor) :
    IsLanglandsFamily K art 1 (recFamily K art) where
  gl1 _ := rec1_gl1 K art
  map
    | 0, _ => isLanglandsMap_rec0 K art
    | 1, _ => isLanglandsMap_rec1 K art hL
    | _ + 2, h => absurd h (by omega)

end Family

/-- **The local Langlands correspondence for $GL_1$**, reduced to Tate's local theory: `GL1LFactor` implies `LocalLanglandsGL 1`. -/
theorem localLanglandsGL_one_of_gl1LFactor (h : GL1LFactor.{u}) : LocalLanglandsGL.{u} 1 :=
  fun K _ _ _ _ art hart => ⟨recFamily K art, isLanglandsFamily_recFamily K art (h K art hart)⟩

end Langlands.LocalGL1
