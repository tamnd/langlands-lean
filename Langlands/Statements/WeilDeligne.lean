/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Smooth
import Langlands.WeilGroup.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Semisimple

/-!
# Weil-Deligne representations

Let $K$ be a nonarchimedean local field with residue field of $q$ elements, and let $W_K$ be its Weil group. Each $w \in W_K$ acts on the residue field of $\bar K$ as an integer power $\Phi^{d(w)}$ of the geometric Frobenius $\Phi$; the integer $d(w)$ is the degree of $w$. Put $|w| = q^{-d(w)}$. Under a local Artin map that sends uniformizers to geometric Frobenius elements, $|w|$ is the absolute value of the corresponding element of $K^\times$.

A *Weil-Deligne representation* of dimension $m$ is a pair $(r, N)$ where

* $r : W_K \to GL_m(\mathbb{C})$ is a homomorphism with open kernel,
* $N$ is a nilpotent $m \times m$ matrix with $r(w) N r(w)^{-1} = |w| N$ for each $w$,

and $r$ is *Frobenius semisimple*: each $r(w)$ is a semisimple matrix. Two such pairs are isomorphic if one matrix of $GL_m(\mathbb{C})$ conjugates $r$ and $N$ to $r'$ and $N'$.

The operations are these.

* The *determinant* is the character $\det r$ of $W_K$.
* The *twist* by a character $\varphi$ of $W_K$ is $(\varphi r, N)$.
* The *dual* is $(w \mapsto {}^t r(w)^{-1}, -{}^t N)$.

The *L-factor* is
$$L(s, (r, N)) = \det\left(1 - q^{-s} r(\Phi) \mid (V^{I_K})_{N = 0}\right)^{-1},$$
where $V = \mathbb{C}^m$, $I_K$ is the inertia subgroup and $(V^{I_K})_{N=0}$ is the space of vectors fixed by $I_K$ and killed by $N$. This space is stable under $r(W_K)$ since $I_K$ is normal and $N r(w) = |w|^{-1} r(w) N$. The factor does not depend on the choice of $\Phi$, because two geometric Frobenius elements differ by an element of $I_K$.

* `Langlands.WeilDeligneRep`: a Frobenius semisimple Weil-Deligne representation of dimension $m$.
* `Langlands.WDIso`: the isomorphism classes.
* `Langlands.WeilDeligneRep.det`, `Langlands.WeilDeligneRep.lFactor`, `Langlands.WeilDeligneRep.IsIrreducible`.
* `Langlands.WDIso.IsTwist`, `Langlands.WDIso.IsDual`: the twist and the dual on isomorphism classes, as relations.
* `Langlands.CharCorrespond`: a character $\chi$ of $K^\times$ and a character $\varphi$ of $W_K$ that correspond through a local Artin map.
* `Langlands.WeilDeligneRep.det_eq_of_iso`: isomorphic representations have the same determinant.

## Implementation notes

The representation space is $\mathbb{C}^m$, so the representations are matrices. This makes the isomorphism classes a type in the universe of $K$.

A homomorphism $W_K \to GL_m(\mathbb{C})$ is continuous for the discrete topology on the target exactly when its kernel is open. For a Frobenius semisimple representation this is the same as continuity for the usual topology, since $GL_m(\mathbb{C})$ has no small subgroups.

The ε-factors of Deligne and Langlands are not here. Their definition needs the Weil groups of all finite extensions of $K$, induction of representations, and Tate's local constants for characters, together with Deligne's theorem that these data fit together.

## References

* P. Deligne, Les constantes des équations fonctionnelles des fonctions L, LNM 349, 1973, section 8.
* J. Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, part 2, 1979, section 4.
* M. Harris, R. Taylor, The geometry and cohomology of some simple Shimura varieties, Annals of Math. Studies 151, 2001, section I.1.
-/

namespace Langlands

universe u

open Matrix

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The norm $|w| = q^{-d(w)}$ of an element $w$ of degree $d(w)$ of the Weil group. -/
noncomputable def weilNorm (w : WeilGroup K) : ℂ :=
  (residueCard K : ℂ) ^ (-(Multiplicative.toAdd (WeilGroup.degree K w)))

theorem weilNorm_ne_zero (w : WeilGroup K) : weilNorm K w ≠ 0 := by
  have : (residueCard K : ℂ) ≠ 0 := by
    have : 0 < residueCard K := Nat.card_pos
    exact_mod_cast this.ne'
  exact zpow_ne_zero _ this

/-- A fixed geometric Frobenius element of $W_K$. -/
noncomputable def geomFrob : WeilGroup K :=
  Classical.choose (WeilGroup.exists_isGeometricFrobenius K)

/-- A Frobenius semisimple Weil-Deligne representation of $W_K$ of dimension $m$: a homomorphism $r : W_K \to GL_m(\mathbb{C})$ with open kernel and a nilpotent matrix $N$ with $r(w) N r(w)^{-1} = |w| N$, where each $r(w)$ is semisimple. -/
structure WeilDeligneRep (m : ℕ) where
  /-- The representation of the Weil group. -/
  r : WeilGroup K →* GL (Fin m) ℂ
  isOpen_ker : IsOpen (r.ker : Set (WeilGroup K))
  /-- The monodromy operator. -/
  N : Matrix (Fin m) (Fin m) ℂ
  isNilpotent : IsNilpotent N
  conj : ∀ w, (r w : Matrix (Fin m) (Fin m) ℂ) * N * ((r w)⁻¹ : GL (Fin m) ℂ) = weilNorm K w • N
  semisimple : ∀ w, Module.End.IsSemisimple (Matrix.toLin' (r w : Matrix (Fin m) (Fin m) ℂ))

namespace WeilDeligneRep

variable {K} {m : ℕ}

/-- Two Weil-Deligne representations are isomorphic if one matrix $g$ conjugates $r$ to $r'$ and $N$ to $N'$. -/
def Iso (ρ ρ' : WeilDeligneRep K m) : Prop :=
  ∃ g : GL (Fin m) ℂ, (∀ w, ρ'.r w = g * ρ.r w * g⁻¹) ∧
    ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * (g⁻¹ : GL (Fin m) ℂ)

/-- The setoid of isomorphism of Weil-Deligne representations. -/
instance setoid : Setoid (WeilDeligneRep K m) where
  r := Iso
  iseqv := by
    refine ⟨fun ρ => ⟨1, fun w => by simp, by simp⟩, ?_, ?_⟩
    · rintro ρ ρ' ⟨g, hr, hN⟩
      refine ⟨g⁻¹, fun w => by simp [hr, mul_assoc], ?_⟩
      simp [hN, ← mul_assoc]
    · rintro ρ ρ' ρ'' ⟨g, hr, hN⟩ ⟨g', hr', hN'⟩
      refine ⟨g' * g, fun w => by simp [hr, hr', mul_assoc], ?_⟩
      simp [hN, hN', mul_assoc]

/-- The determinant $\det r$, a character of $W_K$. -/
noncomputable def det (ρ : WeilDeligneRep K m) : WeilGroup K →* ℂˣ :=
  Matrix.GeneralLinearGroup.det.comp ρ.r

/-- Isomorphic Weil-Deligne representations have the same determinant. -/
theorem det_eq_of_iso {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') : ρ'.det = ρ.det := by
  obtain ⟨g, hr, -⟩ := h
  ext w
  simp only [det, MonoidHom.comp_apply, hr, map_mul, map_inv]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

/-- A Weil-Deligne representation is irreducible if $m > 0$ and the only subspaces of $\mathbb{C}^m$ stable under $r(W_K)$ and $N$ are $0$ and $\mathbb{C}^m$. Then $N = 0$. -/
def IsIrreducible (ρ : WeilDeligneRep K m) : Prop :=
  0 < m ∧ ∀ W : Submodule ℂ (Fin m → ℂ), (∀ w, W ≤ W.comap (Matrix.toLin' (ρ.r w : Matrix _ _ ℂ))) →
    W ≤ W.comap (Matrix.toLin' ρ.N) → W = ⊥ ∨ W = ⊤

/-- The space $(V^{I_K})_{N = 0}$ of vectors fixed by the inertia subgroup and killed by $N$. -/
def lSpace (ρ : WeilDeligneRep K m) : Submodule ℂ (Fin m → ℂ) where
  carrier := {v | ρ.N *ᵥ v = 0 ∧ ∀ i ∈ WeilGroup.inertia K, (ρ.r i : Matrix (Fin m) (Fin m) ℂ) *ᵥ v = v}
  add_mem' {a b} ha hb := ⟨by simp [mulVec_add, ha.1, hb.1], fun i hi => by
    simp [mulVec_add, ha.2 i hi, hb.2 i hi]⟩
  zero_mem' := ⟨by simp, fun _ _ => by simp⟩
  smul_mem' c v hv := ⟨by simp [mulVec_smul, hv.1], fun i hi => by simp [mulVec_smul, hv.2 i hi]⟩

theorem lSpace_stable (ρ : WeilDeligneRep K m) (w : WeilGroup K) :
    ∀ v ∈ ρ.lSpace, Matrix.toLin' (ρ.r w : Matrix (Fin m) (Fin m) ℂ) v ∈ ρ.lSpace := by
  intro v hv
  rw [Matrix.toLin'_apply]
  refine ⟨?_, fun i hi => ?_⟩
  · have h := congrArg (· * (ρ.r w : Matrix (Fin m) (Fin m) ℂ)) (ρ.conj w)
    simp only [mul_assoc, Units.inv_mul, mul_one] at h
    have h2 := congrArg (· *ᵥ v) h
    simp only [← mulVec_mulVec, hv.1, mulVec_zero, smul_mulVec] at h2
    exact (smul_eq_zero.1 h2.symm).resolve_left (weilNorm_ne_zero K w)
  · have hn : w⁻¹ * i * w⁻¹⁻¹ ∈ WeilGroup.inertia K :=
      (MonoidHom.normal_ker (WeilGroup.toResidue K)).conj_mem i hi w⁻¹
    have hi' := hv.2 _ hn
    have : ρ.r i = ρ.r w * ρ.r (w⁻¹ * i * w⁻¹⁻¹) * (ρ.r w)⁻¹ := by
      simp [map_mul, mul_assoc]
    have key : ((ρ.r w)⁻¹ : GL (Fin m) ℂ).val *ᵥ ((ρ.r w : Matrix (Fin m) (Fin m) ℂ) *ᵥ v) = v := by
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    rw [this, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, key, hi']

/-- The action of the geometric Frobenius on $(V^{I_K})_{N = 0}$. -/
noncomputable def frobOnLSpace (ρ : WeilDeligneRep K m) : Module.End ℂ ρ.lSpace :=
  (Matrix.toLin' (ρ.r (geomFrob K) : Matrix (Fin m) (Fin m) ℂ)).restrict (ρ.lSpace_stable _)

/-- The L-factor $L(s, \rho) = \det(1 - q^{-s} r(\Phi) \mid (V^{I_K})_{N = 0})^{-1}$ of a Weil-Deligne representation. -/
noncomputable def lFactor (ρ : WeilDeligneRep K m) (s : ℂ) : ℂ :=
  (LinearMap.det (1 - ((residueCard K : ℂ) ^ (-s)) • ρ.frobOnLSpace))⁻¹

end WeilDeligneRep

/-- The isomorphism classes of Frobenius semisimple Weil-Deligne representations of $W_K$ of dimension $m$. -/
def WDIso (m : ℕ) : Type u :=
  Quotient (WeilDeligneRep.setoid (K := K) (m := m))

namespace WDIso

variable {K} {m : ℕ}

/-- The class of a Weil-Deligne representation. -/
def mk (ρ : WeilDeligneRep K m) : WDIso K m :=
  Quotient.mk _ ρ

/-- `y` is the class of the twist $(\varphi r, N)$ of a representative $(r, N)$ of `x` by a character $\varphi$ of $W_K$. -/
def IsTwist (y x : WDIso K m) (φ : WeilGroup K →* ℂˣ) : Prop :=
  ∃ ρ ρ' : WeilDeligneRep K m, mk ρ = x ∧ mk ρ' = y ∧
    (∀ w, (ρ'.r w : Matrix (Fin m) (Fin m) ℂ) = (φ w : ℂ) • (ρ.r w : Matrix (Fin m) (Fin m) ℂ)) ∧
    ρ'.N = ρ.N

/-- `y` is the class of the dual $(w \mapsto {}^t r(w)^{-1}, -{}^t N)$ of a representative $(r, N)$ of `x`. -/
def IsDual (y x : WDIso K m) : Prop :=
  ∃ ρ ρ' : WeilDeligneRep K m, mk ρ = x ∧ mk ρ' = y ∧
    (∀ w, (ρ'.r w : Matrix (Fin m) (Fin m) ℂ) = (((ρ.r w)⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ)ᵀ) ∧
    ρ'.N = -ρ.Nᵀ

end WDIso

/-- A character $\chi$ of $K^\times$ and a character $\varphi$ of $W_K$ correspond through the local Artin map $\mathrm{art}_K$: $\chi(x) = \varphi(w)$ whenever the class of $w$ in $W_K^{ab}$ is $\mathrm{art}_K(x)$. So $\varphi = \chi \circ \mathrm{art}_K^{-1}$ on $W_K^{ab}$. -/
def CharCorrespond (art : Kˣ ≃ₜ* WeilGroup.Ab K) (χ : Kˣ →* ℂˣ) (φ : WeilGroup K →* ℂˣ) : Prop :=
  ∀ (x : Kˣ) (w : WeilGroup K), (QuotientGroup.mk w : WeilGroup.Ab K) = art x → χ x = φ w

end Langlands
