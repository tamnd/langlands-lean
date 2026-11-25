/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.GodementJacquet
import Langlands.Statements.WeilDeligne
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Central.Defs
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The local Langlands correspondence for GL(n) and related groups

Let $K$ be a nonarchimedean local field and fix a local Artin map $\mathrm{art}_K : K^\times \to W_K^{ab}$ that sends uniformizers to geometric Frobenius elements (`Langlands.IsLocalArtinMap`). The local Langlands correspondence for $GL_n$ is a family of bijections
$$\mathrm{rec}_m : \mathrm{Irr}(GL_m(K)) \to \{\text{Frobenius semisimple Weil-Deligne representations of dimension } m\}/\cong, \quad m \le n.$$
Henniart showed that at most one family has the following properties, and Harris and Taylor, Henniart and Scholze proved that one exists.

1. For $m = 1$, $\mathrm{rec}_1(\chi) = \chi \circ \mathrm{art}_K^{-1}$.
2. The central character $\omega_\pi$ corresponds to $\det \mathrm{rec}_m(\pi)$ through $\mathrm{art}_K$.
3. $\mathrm{rec}_m(\pi \otimes \chi \circ \det) = \mathrm{rec}_m(\pi) \otimes \mathrm{rec}_1(\chi)$.
4. $\mathrm{rec}_m(\pi^\vee) = \mathrm{rec}_m(\pi)^\vee$.
5. $L(s, \pi \times \pi') = L(s, \mathrm{rec}_m(\pi) \otimes \mathrm{rec}_{m'}(\pi'))$.
6. $\varepsilon(s, \pi \times \pi', \psi) = \varepsilon(s, \mathrm{rec}_m(\pi) \otimes \mathrm{rec}_{m'}(\pi'), \psi)$.

The file states conditions 1 to 4, and condition 5 for $\pi' = 1$, that is for the standard L-factor of Godement and Jacquet. With condition 3 this also gives condition 5 for each $\pi'$ of $GL_1(K)$.

* `Langlands.IsLanglandsMap`, `Langlands.IsLanglandsFamily`, `Langlands.LocalLanglandsGL`.
* `Langlands.LocalLanglandsGL2`: the case $n = 2$ with the explicit form on the principal series and on the supercuspidal representations.
* `Langlands.LocalLanglandsSL2`: the L-packets of $SL_2(K)$, from the restriction of representations of $GL_2(K)$ (Labesse and Langlands).
* `Langlands.JacquetLanglandsGL2`: the local Jacquet-Langlands correspondence between the discrete series of $GL_2(K)$ and the irreducible representations of $D^\times$ for the quaternion division algebra $D$.
* `Langlands.charRep_hasCentralChar`: the central character of the representation $\chi$ of $GL_1(K)$ is $\chi$, so condition 2 for $m = 1$ is condition 1.

## Implementation notes

**What is left out.** The ε-factors (condition 6) and the L-factors of pairs with $m' \ge 2$ are not in the statement. On the Galois side the ε-factors of Deligne and Langlands need the Weil groups of all finite extensions of $K$, induction, and Tate's local constants. On the automorphic side the factors of pairs need the Rankin-Selberg integrals of Jacquet, Piatetski-Shapiro and Shalika on Whittaker models. Without them the conditions do not determine the bijection on the supercuspidal representations: conditions 1 to 5 as stated are satisfied by the true correspondence, but for $n \ge 2$ they are also satisfied by other bijections. So `LocalLanglandsGL n` is the existence part of the theorem of Harris and Taylor, with a weaker list of conditions than the list that characterizes the family. Henniart's uniqueness theorem needs condition 6.

The operations twist, contragredient and dual are relations on isomorphism classes (`Langlands.IrrSmooth.IsTwist`, `Langlands.WDIso.IsTwist` and so on). For example condition 3 says: if $y$ is the class of $\pi \otimes \chi \circ \det$ for some $\pi$ in the class $x$, then $\mathrm{rec}(y)$ is the class of the twist of some representative of $\mathrm{rec}(x)$ by $\chi \circ \mathrm{art}_K^{-1}$.

$SL_2(K)$ is the kernel of $\det$ in $GL_2(K)$, with the subspace topology. $D^\times$ has the topology of units for the canonical topology of the finite dimensional $K$-vector space $D$.

$GSp_4$ (Gan and Takeda) is not stated. A faithful statement needs the L-parameters as $GSp_4(\mathbb{C})$-conjugacy classes of pairs $(\varphi, \nu)$ of a parameter and its similitude character, the component groups that index the L-packets, and the generic member of each tempered packet, which needs Whittaker models and the γ-factors of pairs. This is too large for this file.

## References

* M. Harris, R. Taylor, The geometry and cohomology of some simple Shimura varieties, Annals of Math. Studies 151, 2001.
* G. Henniart, Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique, Invent. Math. 139 (2000).
* G. Henniart, Caractérisation de la correspondance de Langlands locale par les facteurs ε de paires, Invent. Math. 113 (1993).
* P. Scholze, The local Langlands correspondence for GL_n over p-adic fields, Invent. Math. 192 (2013).
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006.
* J.-P. Labesse, R. P. Langlands, L-indistinguishability for SL(2), Canad. J. Math. 31 (1979).
* H. Jacquet, R. P. Langlands, Automorphic forms on GL(2), LNM 114, Springer, 1970.
-/

namespace Langlands

universe u

open Matrix

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The class of the representation $\chi$ of $GL_1(K)$, given by a smooth character $\chi$ of $K^\times$ through $\det$. -/
noncomputable def charClass (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) : IrrSmooth (GL (Fin 1) K) :=
  IrrSmooth.mk ⟨SmoothRep.charRep (detChar K 1 χ) (isOpen_ker_detChar K 1 χ hχ),
    SmoothRep.charRep_isIrreducible _ _⟩

/-- Conditions 2 to 5 for one bijection $\mathrm{rec} : \mathrm{Irr}(GL_m(K)) \to \mathrm{WD}_m(W_K)$, with condition 5 for the standard L-factor only. -/
structure IsLanglandsMap (art : Kˣ ≃ₜ* WeilGroup.Ab K) (m : ℕ)
    (rec : IrrSmooth (GL (Fin m) K) ≃ WDIso K m) : Prop where
  /-- The central character corresponds to the determinant. -/
  central : ∀ (π : IrrRep (GL (Fin m) K)) (ω : Kˣ →* ℂˣ), π.1.HasCentralChar ω →
    ∀ ρ : WeilDeligneRep K m, WDIso.mk ρ = rec (IrrSmooth.mk π) → CharCorrespond K art ω ρ.det
  /-- The bijection commutes with the twists by characters. -/
  twist : ∀ (x y : IrrSmooth (GL (Fin m) K)) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
    IrrSmooth.IsTwist y x (detChar K m χ) (isOpen_ker_detChar K m χ hχ) →
      ∀ φ : WeilGroup K →* ℂˣ, CharCorrespond K art χ φ → WDIso.IsTwist (rec y) (rec x) φ
  /-- The contragredient goes to the dual. -/
  dual : ∀ x y : IrrSmooth (GL (Fin m) K), IrrSmooth.IsContragredient y x →
    WDIso.IsDual (rec y) (rec x)
  /-- The Godement-Jacquet L-factor is the L-factor of the Weil-Deligne representation. -/
  lFactor : ∀ (π : IrrRep (GL (Fin m) K)) (ρ : WeilDeligneRep K m),
    WDIso.mk ρ = rec (IrrSmooth.mk π) → IsGJLFactor K π.1 ρ.lFactor

/-- The conditions on a family $(\mathrm{rec}_m)_{m \le n}$: condition 1 for $m = 1$, and conditions 2 to 5 of `IsLanglandsMap` for each $m \le n$. Condition 6 (ε-factors of pairs) and condition 5 for pairs with $m' \ge 2$ are left out, so these conditions do not determine the family. -/
structure IsLanglandsFamily (art : Kˣ ≃ₜ* WeilGroup.Ab K) (n : ℕ)
    (rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m) : Prop where
  /-- For $m = 1$, $\mathrm{rec}_1(\chi) = \chi \circ \mathrm{art}_K^{-1}$. -/
  gl1 : ∀ (h : 1 ≤ n) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (ρ : WeilDeligneRep K 1),
    WDIso.mk ρ = rec 1 h (charClass K χ hχ) →
      ∀ (x : Kˣ) (w : WeilGroup K), (QuotientGroup.mk w : WeilGroup.Ab K) = art x →
        (ρ.r w : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = χ x
  /-- Conditions 2 to 5 for each $m \le n$. -/
  map : ∀ m (h : m ≤ n), IsLanglandsMap K art m (rec m h)

/-- **The local Langlands correspondence for $GL_n$** (Harris and Taylor, Henniart, Scholze), existence part. For each nonarchimedean local field $K$ and each local Artin map $\mathrm{art}_K$, there are bijections $\mathrm{rec}_m : \mathrm{Irr}(GL_m(K)) \to \mathrm{WD}_m(W_K)$ for $m \le n$ with conditions 1 to 4 and the standard L-factors (condition 5 with $\pi' = 1$). The conditions on ε-factors and on L-factors of pairs with $m' \ge 2$ are not part of this statement, so it does not say that the family is unique, and for $n \ge 2$ these conditions alone do not determine it. -/
def LocalLanglandsGL (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∃ rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m, IsLanglandsFamily K art n rec

open scoped Classical in
/-- **The local Langlands correspondence for $GL_2$** (Kutzko), with the explicit form on the non-supercuspidal representations. There is a bijection $\mathrm{rec} : \mathrm{Irr}(GL_2(K)) \to \mathrm{WD}_2(W_K)$ with conditions 2 to 5 of `IsLanglandsMap` such that:

* if $\pi$ is a subrepresentation of the principal series $\mathrm{Ind}(\chi_1, \chi_2)$, and $\varphi_i = \chi_i \circ \mathrm{art}_K^{-1}$, then $\mathrm{rec}(\pi)$ is $r = \varphi_1 \oplus \varphi_2$ with $N = 0$, except when $\chi_1 = \chi_2 |\cdot|$; then $\pi$ is a twist of the Steinberg representation and $N$ sends the second basis vector to the first;
* $\pi$ is supercuspidal exactly when $\mathrm{rec}(\pi)$ is irreducible.

This covers all of $\mathrm{Irr}(GL_2(K))$, since each irreducible representation that is not supercuspidal is a subrepresentation of a principal series (Jacquet). The ε-factors are left out, as in `LocalLanglandsGL`, so the statement does not determine $\mathrm{rec}$ on the supercuspidal representations. The explicit description of Bushnell and Henniart by tame types and admissible pairs is not here. -/
def LocalLanglandsGL2 : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∃ rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2, IsLanglandsMap K art 2 rec ∧
        (∀ (π : IrrRep (GL (Fin 2) K)) (χ₁ χ₂ : Kˣ →* ℂˣ), IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
          π.1.HasHom (principalSeries K χ₁ χ₂) →
            ∀ φ₁ φ₂ : WeilGroup K →* ℂˣ, CharCorrespond K art χ₁ φ₁ → CharCorrespond K art χ₂ φ₂ →
              ∃ ρ : WeilDeligneRep K 2, WDIso.mk ρ = rec (IrrSmooth.mk π) ∧
                (∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![(φ₁ w : ℂ), φ₂ w]) ∧
                ρ.N = if ∀ x : Kˣ, (χ₁ x : ℂ) = χ₂ x * (normAbs K x : ℂ) then
                  Matrix.single 0 1 1 else 0) ∧
        ∀ π : IrrRep (GL (Fin 2) K), π.1.IsSupercuspidal (scalarGL K 2) ↔
          ∀ ρ : WeilDeligneRep K 2, WDIso.mk ρ = rec (IrrSmooth.mk π) → ρ.IsIrreducible

/-- The group $SL_2(K)$ as the kernel of $\det$ in $GL_2(K)$. -/
noncomputable def slTwo : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker

/-- The restriction of a representation of $GL_2(K)$ to $SL_2(K)$. -/
noncomputable def restrictSL2 (π : SmoothRep (GL (Fin 2) K)) : SmoothRep (slTwo K) :=
  π.restrict (slTwo K).subtype continuous_subtype_val

/-- **The L-packets of $SL_2(K)$** (Labesse and Langlands), in the restriction form. The L-packets of $SL_2(K)$ are the sets of irreducible constituents of the restrictions $\pi|_{SL_2(K)}$ of the irreducible representations $\pi$ of $GL_2(K)$, and they are indexed by the projective classes of the parameters $\mathrm{rec}(\pi)$. The statement has four parts.

* Each irreducible representation of $SL_2(K)$ is a subrepresentation of some $\pi|_{SL_2(K)}$.
* Each $\pi|_{SL_2(K)}$ is a finite direct sum of irreducible representations that are pairwise not isomorphic (multiplicity one).
* $\pi|_{SL_2(K)}$ and $\pi'|_{SL_2(K)}$ have a common irreducible subrepresentation exactly when $\pi' \cong \pi \otimes \chi \circ \det$ for a smooth character $\chi$.
* For each bijection $\mathrm{rec}$ with the conditions of `IsLanglandsMap`, $\pi' \cong \pi \otimes \chi \circ \det$ for some $\chi$ exactly when $\mathrm{rec}(\pi') \cong \mathrm{rec}(\pi) \otimes \varphi$ for some character $\varphi$ of $W_K$.

So the map that sends an L-packet $\Pi$ to the image in $PGL_2(\mathbb{C})$ of $\mathrm{rec}(\pi)$ for $\Pi \subseteq \pi|_{SL_2(K)}$ is a bijection from the L-packets to the projective parameters. Each projective parameter lifts to $GL_2(\mathbb{C})$ (Tate, $H^2(W_K, \mathbb{C}^\times) = 0$), so each projective class occurs. The parametrization of the members of a packet by the characters of the component group $S_\varphi$ is not part of the statement; it needs a choice of a generic character. -/
def LocalLanglandsSL2 : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    (∀ σ : IrrRep (slTwo K), ∃ π : IrrRep (GL (Fin 2) K), σ.1.HasHom (restrictSL2 K π.1)) ∧
    (∀ π : IrrRep (GL (Fin 2) K), ∃ (j : ℕ) (W : Fin j → Submodule ℂ π.1.V)
        (hW : ∀ i, IsStableSubspace (restrictSL2 K π.1).ρ (W i)),
        0 < j ∧ DirectSum.IsInternal W ∧
        (∀ i, ((restrictSL2 K π.1).sub (W i) (hW i)).IsIrreducible) ∧
        ∀ i i', i ≠ i' → ¬ ((restrictSL2 K π.1).sub (W i) (hW i)).Iso
          ((restrictSL2 K π.1).sub (W i') (hW i'))) ∧
    (∀ π π' : IrrRep (GL (Fin 2) K),
      (∃ σ : IrrRep (slTwo K), σ.1.HasHom (restrictSL2 K π.1) ∧ σ.1.HasHom (restrictSL2 K π'.1)) ↔
        ∃ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
          π'.1.Iso (π.1.twist (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ))) ∧
    ∀ (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∀ rec : IrrSmooth (GL (Fin 2) K) ≃ WDIso K 2, IsLanglandsMap K art 2 rec →
        ∀ π π' : IrrRep (GL (Fin 2) K),
          (∃ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
            π'.1.Iso (π.1.twist (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ))) ↔
          ∃ φ : WeilGroup K →* ℂˣ, WDIso.IsTwist (rec (IrrSmooth.mk π')) (rec (IrrSmooth.mk π)) φ

/-- An irreducible representation of $GL_2(K)$ is in the discrete series (essentially square integrable) if it is supercuspidal or a twist of the Steinberg representation, that is a subrepresentation of $\mathrm{Ind}(\chi_2 |\cdot|, \chi_2)$. -/
def IsDiscreteSeries (π : SmoothRep (GL (Fin 2) K)) : Prop :=
  π.IsSupercuspidal (scalarGL K 2) ∨
    ∃ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ ∧ IsSmoothChar K χ₂ ∧
      (∀ x : Kˣ, (χ₁ x : ℂ) = χ₂ x * (normAbs K x : ℂ)) ∧ π.HasHom (principalSeries K χ₁ χ₂)

/-- An element $g$ of $GL_2(K)$ is regular elliptic if its characteristic polynomial is irreducible and separable. -/
def IsRegularElliptic (g : GL (Fin 2) K) : Prop :=
  Irreducible (g : Matrix (Fin 2) (Fin 2) K).charpoly ∧ (g : Matrix (Fin 2) (Fin 2) K).charpoly.Separable

/-- An element $d$ of the quaternion algebra $D$ matches $g \in GL_2(K)$ if the reduced characteristic polynomial of $d$ is the characteristic polynomial of $g$. The characteristic polynomial of left multiplication by $d$ on $D$ is the square of the reduced one. -/
def IsMatching {D : Type u} [Ring D] [Algebra K D] [Module.Free K D] [Module.Finite K D]
    (g : GL (Fin 2) K) (d : Dˣ) : Prop :=
  (g : Matrix (Fin 2) (Fin 2) K).charpoly ^ 2 = LinearMap.charpoly (Algebra.lmul K D (d : D))

/-- **The local Jacquet-Langlands correspondence** (Jacquet and Langlands). Let $D$ be the quaternion division algebra over $K$. There is a unique bijection $\mathrm{JL}$ from the discrete series of $GL_2(K)$ to the irreducible smooth representations of $D^\times$ such that $\theta_\pi(g) = -\theta_{\mathrm{JL}(\pi)}(d)$ for each regular elliptic $g \in GL_2(K)$ and each $d \in D^\times$ that matches $g$. Here $\theta$ is the Harish-Chandra character in the pointwise form of `Langlands.SmoothRep.IsCharacterValue`. -/
def JacquetLanglandsGL2 : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    [TopologicalSpace D] [IsModuleTopology K D], Module.finrank K D = 4 →
      ∃! JL : {x : IrrSmooth (GL (Fin 2) K) // ∃ π : IrrRep (GL (Fin 2) K),
          IrrSmooth.mk π = x ∧ IsDiscreteSeries K π.1} ≃ IrrSmooth Dˣ,
        ∀ x (π : IrrRep (GL (Fin 2) K)) (π' : IrrRep Dˣ), IrrSmooth.mk π = x.1 →
          IrrSmooth.mk π' = JL x → ∀ (g : GL (Fin 2) K) (d : Dˣ), IsRegularElliptic K g →
            IsMatching K g d → ∀ c : ℂ, π.1.IsCharacterValue g c → π'.1.IsCharacterValue d (-c)

/-- The central character of the representation $\chi \circ \det$ of $GL_1(K)$ is $\chi$. So for $m = 1$ condition 2 of `IsLanglandsMap` says that $\det \mathrm{rec}_1(\chi) = \chi \circ \mathrm{art}_K^{-1}$, which is condition 1. -/
theorem charRep_hasCentralChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    (SmoothRep.charRep (detChar K 1 χ) (isOpen_ker_detChar K 1 χ hχ)).HasCentralChar χ := by
  intro a v
  have h : Matrix.GeneralLinearGroup.det (scalarGL K 1 a) = a := by
    ext; simp [scalarGL]
  change ((χ (Matrix.GeneralLinearGroup.det (scalarGL K 1 a)) : ℂ)) • v = _
  rw [h]

end Langlands
