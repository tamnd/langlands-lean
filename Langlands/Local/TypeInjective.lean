/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.TypeCharAgree
import Langlands.Local.CIndSupercuspidal

/-!
# Injectivity of the type representation

This file works toward `Langlands.LocalGL2.TypeRepInjective K` (Bushnell and Henniart, 15.6, 15.7 and 20.2). The claim is that if the representations $c\text{-}\mathrm{Ind}_{J}^{G} \Lambda$ of a datum for $(L/K, \xi)$ and $c\text{-}\mathrm{Ind}_{J'}^{G} \Lambda'$ of a datum for $(L'/K, \xi')$ are isomorphic, then the pairs are $K$-isomorphic. The file proves the representation theoretic steps of the proof and reduces the claim to one statement about two types that intertwine, `Langlands.LocalGL2.TypeIntertwiningIso K`. It also proves that this statement is equivalent to a conjugacy statement, `Langlands.LocalGL2.TypeIntertwiningConj K`.

## Main definitions

* `Langlands.IntertwinesWith`: $g$ intertwines $\Lambda$ with $\Lambda'$, that is $\Lambda'(g x g^{-1}) = \Lambda(x)$ for each $x \in J \cap g^{-1} J' g$.
* `Langlands.LocalGL2.TypeIntertwiningIso`: if the characters of two data intertwine, then the pairs are $K$-isomorphic (BH 15.7 and 20.2).
* `Langlands.LocalGL2.TypeIntertwiningConj`: if the characters of two data intertwine, then some element $h$ intertwines them and conjugates the image of $L^\times$ to the image of $L'^\times$ by a $K$-isomorphism $j : L \to L'$.

## Main results

* `Langlands.exists_intertwinesWith_of_iso`: if $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$, then some $g \in G$ intertwines $\Lambda$ with $\Lambda'$ (one half of BH 11.5, the Mackey argument).
* `Langlands.LocalGL2.TameDatum.comp_algebraMap_eq_of_intertwinesWith`: if the characters of two data intertwine, then $\xi|_{K^\times} = \xi'|_{K^\times}$.
* `Langlands.LocalGL2.TameDatum.iso_of_intertwinesWith_conj`: if $h$ intertwines $\Lambda$ with $\Lambda'$ and $h \iota(y) h^{-1} = \iota'(j(y))$ for a $K$-isomorphism $j$, then $\xi = \xi' \circ j$.
* `Langlands.LocalGL2.TameDatum.Λ_eq_of_eq_basis`: two data of one pair with the same chain order and basis have equal characters on $J$, for $p \ne 2$.
* `Langlands.LocalGL2.TameDatum.exists_conj_of_iso`: for $p \ne 2$ and $K$-isomorphic pairs, the characters of any two data are conjugate by an element $h$ with $h \iota(y) h^{-1} = \iota'(j(y))$.
* `Langlands.LocalGL2.typeIntertwiningIso_iff_typeIntertwiningConj`: the two statements are equivalent.
* `Langlands.LocalGL2.typeRepInjective_of_typeIntertwiningIso`: `Langlands.LocalGL2.TypeIntertwiningIso K` implies `Langlands.LocalGL2.TypeRepInjective K`.

## Proof

Let $e : c\text{-}\mathrm{Ind}_J^G \Lambda \to c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$ be an isomorphism and let $f_0$ be the function that is $\Lambda$ on $J$ and $0$ outside $J$. Then $F = e(f_0)$ is not zero, so $F(g) \ne 0$ for some $g$. The group $J$ acts on $f_0$ by $\Lambda$, so $F(y j) = \Lambda(j) F(y)$. For $j \in J$ with $g j g^{-1} \in J'$ this gives $\Lambda'(g j g^{-1}) F(g) = F(g j) = \Lambda(j) F(g)$, so $g$ intertwines $\Lambda$ with $\Lambda'$.

If $h$ intertwines $\Lambda$ with $\Lambda'$ and $h \iota(y) h^{-1} = \iota'(j(y))$, then $\xi(y) = \Lambda(\iota(y)) = \Lambda'(\iota'(j(y))) = \xi'(j(y))$, because both characters restrict to the characters of the pairs. Conversely, for $K$-isomorphic pairs, transport the second datum along $j$ and rebase it to the basis of the first datum. The two data then have the same group and, by `Langlands.LocalGL2.typeCharUnitsAgree`, the same character. The element $h$ is the inverse of the change of basis.

## Still open

* A proof of `Langlands.LocalGL2.TypeIntertwiningIso K`. This is the theorem that intertwining implies conjugacy for the cuspidal types of BH 15.7, together with the fact that a type determines the pair, BH 20.2. The proof needs the intertwining of two simple strata with possibly different chain orders and levels, which the project has only for one stratum and the element $g$ in the normalizer (see `Langlands/Local/StrataIntertwining.lean` and `Langlands/Local/IntertwiningNormalizer.lean`). It also needs that two simple strata $(\mathfrak{A}, n, \alpha)$ and $(\mathfrak{A}, n, \beta)$ with $\beta - \alpha \in \mathfrak{P}^{1-n}_{\mathfrak{A}}$ give $K$-isomorphic fields, and a comparison of the characters on the two fields.
* The other half of BH 11.5: if some $g$ intertwines $\Lambda$ with $\Lambda'$, then $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$. With it, `Langlands.LocalGL2.TypeIntertwiningIso K` would be equivalent to `Langlands.LocalGL2.TypeRepInjective K`.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§11, 15 and 20.
-/

namespace Langlands

universe w

open SmoothRep

section Mackey

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (J J' : Subgroup G) (Λ : J →* ℂˣ) (Λ' : J' →* ℂˣ) in
/-- An element $g \in G$ intertwines $\Lambda$ with $\Lambda'$ if $\Lambda'(g x g^{-1}) = \Lambda(x)$ for each $x \in J$ with $g x g^{-1} \in J'$. For $J' = J$ and $\Lambda' = \Lambda$ this is `Langlands.Intertwines`. -/
def IntertwinesWith (g : G) : Prop :=
  ∀ x : J, ∀ h : g * x * g⁻¹ ∈ J', Λ' ⟨g * x * g⁻¹, h⟩ = Λ x

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- For one group and one character, `Langlands.IntertwinesWith` is `Langlands.Intertwines`. -/
theorem intertwinesWith_self_iff {J : Subgroup G} {Λ : J →* ℂˣ} {g : G} :
    IntertwinesWith J J Λ Λ g ↔ Intertwines J Λ g :=
  Iff.rfl

/-- The vector $f_0$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ that is $\Lambda$ on $J$ and $0$ outside $J$ is not zero. -/
theorem cIndBasic_ne_zero {J : Subgroup G} {Λ : J →* ℂˣ} (hJ : IsOpen (J : Set G))
    (hΛ : IsOpen (Λ.ker : Set J)) : cIndBasic J Λ hJ hΛ ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => cInd.toFun f 1) h
  simp only [cInd.toFun_cIndBasic, cIndBasicFun_of_mem J Λ J.one_mem] at h1
  have h0 : cInd.toFun (0 : (cInd J Λ).V) 1 = 0 := rfl
  rw [h0] at h1
  have e : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [e, map_one, Units.val_one] at h1
  exact one_ne_zero h1

/-- **Isomorphic compact inductions intertwine** (Bushnell and Henniart, 11.5, one half). Let $J$ be open and let $\Lambda$ have an open kernel. If $c\text{-}\mathrm{Ind}_J^G \Lambda \cong c\text{-}\mathrm{Ind}_{J'}^G \Lambda'$, then some $g \in G$ intertwines $\Lambda$ with $\Lambda'$. The element $g$ is a point where the image of $f_0$ is not zero. -/
theorem exists_intertwinesWith_of_iso {J J' : Subgroup G} {Λ : J →* ℂˣ} {Λ' : J' →* ℂˣ}
    (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) (h : (cInd J Λ).Iso (cInd J' Λ')) :
    ∃ g, IntertwinesWith J J' Λ Λ' g := by
  obtain ⟨e, he⟩ := h
  set f₀ := cIndBasic J Λ hJ hΛ with hf₀def
  have hf₀ : e f₀ ≠ 0 := fun h0 =>
    cIndBasic_ne_zero hJ hΛ (e.injective (h0.trans e.map_zero.symm))
  obtain ⟨x, hx⟩ : ∃ x, cInd.toFun (e f₀) x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf₀ (cInd.ext fun x => hc x)
  refine ⟨x, fun j hj => ?_⟩
  have h1 : cInd.toFun (e f₀) (x * j) = Λ j * cInd.toFun (e f₀) x := by
    rw [← cInd.toFun_ρ, ← he, hf₀def, ρ_cIndBasic_of_mem, map_smul, cInd.toFun_smul]
  have h2 := cInd.toFun_mul_left (e f₀) ⟨x * j * x⁻¹, hj⟩ x
  have e3 : ((⟨x * j * x⁻¹, hj⟩ : J') : G) * x = x * j := by simp
  rw [e3, h1] at h2
  exact Units.ext (mul_right_cancel₀ hx h2.symm)

end Mackey

end Langlands

namespace Langlands.LocalGL2

universe u

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section Datum

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

variable {P Q : TamePair K}

/-- **Intertwining types have the same central character.** If some $g$ intertwines the character of a datum for $(L/K, \xi)$ with the character of a datum for $(L'/K, \xi')$, then $\xi|_{K^\times} = \xi'|_{K^\times}$. A scalar matrix lies in both groups and commutes with $g$. -/
theorem comp_algebraMap_eq_of_intertwinesWith (D : TameDatum K P.L P.ξ)
    (D' : TameDatum K Q.L Q.ξ) {g : GL (Fin 2) K} (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) :
    P.ξ.comp (Units.map (algebraMap K P.L).toMonoidHom) =
      Q.ξ.comp (Units.map (algebraMap K Q.L).toMonoidHom) := by
  ext1 c
  have hz := embGL_mem_jGroup D.hv ((level D.ξ₀ + 1) / 2) (Units.map (algebraMap K P.L).toMonoidHom c)
  have hc : g * embGL D.v (Units.map (algebraMap K P.L).toMonoidHom c) * g⁻¹ =
      embGL D'.v (Units.map (algebraMap K Q.L).toMonoidHom c) := by
    rw [embGL_algebraMap, embGL_algebraMap, (Subgroup.mem_center_iff.1 (scalarGL_mem_center c) g),
      mul_inv_cancel_right]
  have hz' : g * ((⟨_, hz⟩ : D.J) : GL (Fin 2) K) * g⁻¹ ∈ D'.J := by
    change g * embGL D.v _ * g⁻¹ ∈ D'.J
    rw [hc]
    exact embGL_mem_jGroup D'.hv _ _
  have e := hg ⟨_, hz⟩ hz'
  rw [D.Λ_embGL] at e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← e, ← D'.Λ_embGL]
  exact congrArg D'.Λ (Subtype.ext hc)

/-- **Conjugate fields give isomorphic pairs** (Bushnell and Henniart, 20.2). Let $D$ be a datum for $(L/K, \xi)$ and $D'$ a datum for $(L'/K, \xi')$. If $h$ intertwines $\Lambda$ with $\Lambda'$ and $h \iota(y) h^{-1} = \iota'(j(y))$ for each $y \in L^\times$ and a $K$-isomorphism $j : L \to L'$, then $\xi = \xi' \circ j$. The reason is that $\Lambda$ and $\Lambda'$ restrict to $\xi$ and $\xi'$ on the images of $L^\times$ and $L'^\times$. -/
theorem iso_of_intertwinesWith_conj (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    {h : GL (Fin 2) K} (hh : IntertwinesWith D.J D'.J D.Λ D'.Λ h) (j : P.L ≃ₐ[K] Q.L)
    (hc : ∀ y, h * embGL D.v y * h⁻¹ = embGL D'.v (unitsMap j y)) : P.Iso Q := by
  refine ⟨j, MonoidHom.ext fun y => ?_⟩
  have hy := embGL_mem_jGroup D.hv ((level D.ξ₀ + 1) / 2) y
  have hy' : h * ((⟨_, hy⟩ : D.J) : GL (Fin 2) K) * h⁻¹ ∈ D'.J := by
    change h * embGL D.v y * h⁻¹ ∈ D'.J
    rw [hc]
    exact embGL_mem_jGroup D'.hv _ _
  have e := hh ⟨_, hy⟩ hy'
  rw [D.Λ_embGL] at e
  rw [MonoidHom.comp_apply, ← e, ← D'.Λ_embGL]
  exact congrArg D'.Λ (Subtype.ext (hc y))

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  [Algebra.IsSeparable K L] {ξ : Lˣ →* ℂˣ}

/-- **Data with the same basis have the same character.** Let $D$ and $D'$ be two data for $(L/K, \xi)$ with the same chain order and the same basis, whose characters agree on $U^m_{\mathfrak{A}}$, $m = [(n+1)/2]$. Then $\Lambda'(x) = \Lambda(x)$ for each $x$ in the common group $J_\alpha$. -/
theorem Λ_eq_of_eq_basis (D D' : TameDatum K L ξ) (hA : D'.A = D.A) (hv : D'.v = D.v)
    (hU : ∀ (u : GL (Fin 2) K) (hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2))
      (hu' : u ∈ unitsFilt K D'.A ((level D'.ξ₀ + 1) / 2)),
      D'.Λ ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ = D.Λ ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩)
    (x : GL (Fin 2) K) (hx : x ∈ D.J) (hx' : x ∈ D'.J) : D'.Λ ⟨x, hx'⟩ = D.Λ ⟨x, hx⟩ := by
  have hl := D.level_eq D'
  obtain ⟨y, u, hu', hxe⟩ := (mem_jGroup_iff_exists_mul D'.hv _ x).1 hx'
  have hu : u ∈ unitsFilt K D.A ((level D.ξ₀ + 1) / 2) := by
    rwa [hA, hl] at hu'
  have e' : (⟨x, hx'⟩ : D'.J) =
      ⟨embGL D'.v y, embGL_mem_jGroup D'.hv _ y⟩ * ⟨u, unitsFilt_le_jGroup D'.hv _ hu'⟩ :=
    Subtype.ext hxe
  have e : (⟨x, hx⟩ : D.J) =
      ⟨embGL D.v y, embGL_mem_jGroup D.hv _ y⟩ * ⟨u, unitsFilt_le_jGroup D.hv _ hu⟩ :=
    Subtype.ext (show x = embGL D.v y * u by rw [hxe, hv])
  rw [e, e', map_mul, map_mul, Λ_embGL, Λ_embGL, hU u hu hu']

/-- Two data of one pair with the same chain order and the same basis have the same group $J_\alpha$. -/
theorem mem_J_iff_of_eq_basis (D D' : TameDatum K L ξ) (hA : D'.A = D.A) (hv : D'.v = D.v)
    (x : GL (Fin 2) K) : x ∈ D'.J ↔ x ∈ D.J := by
  rw [mem_jGroup, mem_jGroup, hA, hv, D.level_eq D']

end TameDatum

/-- **Types of isomorphic pairs are conjugate** (Bushnell and Henniart, §15 and §19). Let $p \ne 2$, let $D$ be a datum for $P = (L/K, \xi)$, $D'$ a datum for $Q = (L'/K, \xi')$, and $j : L \to L'$ a $K$-isomorphism with $\xi = \xi' \circ j$. Then there is $h \in GL_2(K)$ that intertwines $\Lambda$ with $\Lambda'$ and satisfies $h \iota(y) h^{-1} = \iota'(j(y))$ for each $y \in L^\times$. -/
theorem TameDatum.exists_conj_of_iso (h2 : (2 : 𝓀[K]) ≠ 0) {P Q : TamePair K}
    (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ) (j : P.L ≃ₐ[K] Q.L)
    (hj : P.ξ = Q.ξ.comp (unitsMap j)) :
    ∃ h : GL (Fin 2) K, IntertwinesWith D.J D'.J D.Λ D'.Λ h ∧
      ∀ y, h * embGL D.v y * h⁻¹ = embGL D'.v (unitsMap j y) := by
  set D₁ := (D'.transport j).congrChar hj.symm with hD₁
  have hA := D.A_eq D₁
  have hv' : IsAdapted D₁.A D.v := hA ▸ D.hv
  set D₂ := D₁.rebase D.v hv' with hD₂
  have hU := typeCharUnitsAgree K h2 P D D₂ hA rfl
  set b := basisChangeGL D.v D₁.v with hb
  refine ⟨b⁻¹, fun x hx => ?_, fun y => ?_⟩
  · have hx₂ : (x : GL (Fin 2) K) ∈ D₂.J := (D.mem_J_iff_of_eq_basis D₂ hA rfl x).2 x.2
    have e1 := D.Λ_eq_of_eq_basis D₂ hA rfl hU x x.2 hx₂
    rw [Subtype.coe_eta] at e1
    rw [← e1]
    change D'.Λ _ = D₁.Λ (jGroupBasisChange hv' D₁.hv _ ⟨x, hx₂⟩)
    change D'.Λ _ = D'.Λ (Subgroup.inclusion (D'.transport_jGroup_le j) _)
    congr 1
  · rw [inv_inv, ← embGL_basisChange D.v D₁.v y]
    exact embGL_basis_map D'.v j y

end Datum

section Reduction

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Intertwining types come from isomorphic pairs** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 15.7 and 20.2). Let $p \ne 2$. If some $g \in GL_2(K)$ intertwines the character $\Lambda$ of a datum for $(L/K, \xi)$ with the character $\Lambda'$ of a datum for $(L'/K, \xi')$, then the pairs are $K$-isomorphic. -/
def TypeIntertwiningIso : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    (g : GL (Fin 2) K), IntertwinesWith D.J D'.J D.Λ D'.Λ g → P.Iso Q

/-- **Intertwining types are conjugate with their fields** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 15.7 and 20.2). Let $p \ne 2$. If some $g \in GL_2(K)$ intertwines the character $\Lambda$ of a datum for $(L/K, \xi)$ with the character $\Lambda'$ of a datum for $(L'/K, \xi')$, then there are a $K$-isomorphism $j : L \to L'$ and an element $h$ that intertwines $\Lambda$ with $\Lambda'$ with $h \iota(y) h^{-1} = \iota'(j(y))$ for each $y \in L^\times$. -/
def TypeIntertwiningConj : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    (g : GL (Fin 2) K), IntertwinesWith D.J D'.J D.Λ D'.Λ g →
      ∃ (h : GL (Fin 2) K) (j : P.L ≃ₐ[K] Q.L), IntertwinesWith D.J D'.J D.Λ D'.Λ h ∧
        ∀ y, h * embGL D.v y * h⁻¹ = embGL D'.v (unitsMap j y)

/-- **The two forms of the conjugacy statement are equivalent.** `Langlands.LocalGL2.TypeIntertwiningConj K` gives the isomorphism of pairs by `Langlands.LocalGL2.TameDatum.iso_of_intertwinesWith_conj`, and the isomorphism of pairs gives the conjugating element by `Langlands.LocalGL2.TameDatum.exists_conj_of_iso`. -/
theorem typeIntertwiningIso_iff_typeIntertwiningConj :
    TypeIntertwiningIso K ↔ TypeIntertwiningConj K := by
  constructor
  · intro h h2 P Q D D' g hg
    obtain ⟨j, hj⟩ := h h2 P Q D D' g hg
    obtain ⟨b, hb, hc⟩ := TameDatum.exists_conj_of_iso h2 D D' j hj
    exact ⟨b, j, hb, hc⟩
  · intro h h2 P Q D D' g hg
    obtain ⟨b, j, hb, hc⟩ := h h2 P Q D D' g hg
    exact TameDatum.iso_of_intertwinesWith_conj D D' hb j hc

variable {K} in
/-- **Isomorphic type representations come from isomorphic pairs**, if `Langlands.LocalGL2.TypeIntertwiningIso K` holds. An isomorphism of the representations gives an element that intertwines the two characters, by `Langlands.exists_intertwinesWith_of_iso`. -/
theorem typeRepInjective_of_typeIntertwiningIso (h : TypeIntertwiningIso K) :
    TypeRepInjective K := by
  intro h2 P Q D D' hiso
  obtain ⟨g, hg⟩ := exists_intertwinesWith_of_iso (isOpen_jGroup D.hv _) D.isOpen_ker hiso
  exact h h2 P Q D D' g hg

variable {K} in
/-- **Isomorphic type representations come from isomorphic pairs**, if `Langlands.LocalGL2.TypeIntertwiningConj K` holds. -/
theorem typeRepInjective_of_typeIntertwiningConj (h : TypeIntertwiningConj K) :
    TypeRepInjective K :=
  typeRepInjective_of_typeIntertwiningIso ((typeIntertwiningIso_iff_typeIntertwiningConj K).2 h)

end Reduction

end Langlands.LocalGL2
