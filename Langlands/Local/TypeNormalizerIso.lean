/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.TypeIntertwining
import Langlands.Local.WeilGroupFacts

/-!
# Intertwining types in the normalizer: reduction to one field and one basis

Let $K$ be a nonarchimedean local field. Let $D$ be a cuspidal type datum for $(L/K, \xi)$ and $D'$ a datum for $(L'/K, \xi')$, with the same chain order $\mathfrak{A}$ and the same level. Let $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwine the character $\Lambda$ of $D$ with the character $\Lambda'$ of $D'$. The statement `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K` says that then the pairs are $K$-isomorphic. This file splits that statement into two parts. The first part is a $K$-isomorphism $L \cong L'$. The second part is the comparison of the characters for two data of one field with one basis. The file proves the first part for the maximal order, and it proves the reduction of the full statement to the two parts.

## Main definitions

* `Langlands.LocalGL2.TypeNormalizerRamifiedField`: for the Iwahori order, the fields $L$ and $L'$ of two intertwining data are $K$-isomorphic.
* `Langlands.LocalGL2.TypeNormalizerSameBasisIso`: for two data of one field $L$ with the same basis, the same chain order and the same level, an intertwining element of $\mathfrak{K}_{\mathfrak{A}}$ gives $\xi = \xi' \circ \sigma$ for a $K$-automorphism $\sigma$ of $L$.

## Main results

* `Langlands.LocalGL2.basisChangeGL_mem_normalizer`: the change of basis between two bases adapted to $\mathfrak{A}$ lies in $\mathfrak{K}_{\mathfrak{A}}$.
* `Langlands.LocalGL2.TameDatum.eq_of_maximal`: two data for the maximal order have equal fields, because there is only one unramified quadratic extension of $K$ in $\bar K$.
* `Langlands.LocalGL2.TameDatum.nonempty_algEquiv_of_intertwinesWith`: for `Langlands.LocalGL2.TypeNormalizerRamifiedField K`, the fields of two intertwining data are $K$-isomorphic.
* `Langlands.LocalGL2.TameDatum.eq_of_intertwinesWith_of_mem_J`: for two data of one field with the same basis, an intertwining element in $J_\alpha$ gives $\xi = \xi'$.
* `Langlands.LocalGL2.TameDatum.exists_eq_comp_of_sameBasisIso`: the rebase step, from one basis to two bases of one field.
* `Langlands.LocalGL2.typeIntertwiningNormalizerIso_of_ramifiedField_of_sameBasisIso`: the two statements give `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K`.
* `Langlands.LocalGL2.typeRepInjective_of_ramifiedField_of_sameBasisIso`: the two statements give `Langlands.LocalGL2.TypeRepInjective K`.

## Proof

For the maximal order, the period $e_{\mathfrak{A}} = 1$ is the ramification index of $L/K$ and of $L'/K$. Thus both extensions are unramified, and `Langlands.LocalGL2.uniqueUnramifiedQuad_holds` gives $L = L'$. For a $K$-isomorphism $j : L \to L'$, the transport of $D'$ along $j$ is a datum for $(L/K, \xi' \circ j)$ with the same group $J_\alpha$, the same character, the same chain order and the same level. The rebase of this datum to the basis $v$ of $D$ conjugates $J_\alpha$ and $\Lambda'$ by the change of basis $b$, so $b g$ intertwines $\Lambda$ with the new character. The element $b$ lies in $\mathfrak{K}_{\mathfrak{A}}$, because conjugation by $b$ keeps $\mathfrak{P}^k_{\mathfrak{A}}$. For data with one basis and an intertwining element $g \in J_\alpha$, the value $\xi'(y) = \Lambda'(\iota(y)) = \Lambda(g^{-1} \iota(y) g) = \Lambda(\iota(y)) = \xi(y)$, since $\mathbb{C}^\times$ is commutative.

## Still open

* `Langlands.LocalGL2.TypeNormalizerRamifiedField K`. The intended proof compares the strata. With $\psi' = \psi(u \, \cdot)$ for a unit $u$, the intertwining on the elements of determinant $1$ of $U^{(n+1)/2}_{\mathfrak{A}}$ and trace duality on the matrices of trace $0$ give $u g^{-1} \alpha' g - \alpha \in K + \mathfrak{P}^{1-(n+1)/2}_{\mathfrak{A}}$. Since $\alpha - \mathrm{tr}(\alpha)/2$ is minimal, the discriminants of $\alpha$ and $\alpha'$ then agree up to $u^2 (1 + \mathfrak{p}_K)$, which is a square for $p \ne 2$. The field $L$ is $K$ adjoined a square root of the discriminant of $\alpha$, so $L = L'$. The project has no statement $\psi' = \psi(u \, \cdot)$ for two characters of level one, and no trace duality for the matrices of trace $0$.
* `Langlands.LocalGL2.TypeNormalizerSameBasisIso K`. With the congruence above for one field $L$, the element $\beta = u \alpha' - c$ of $L$ satisfies $g^{-1} \beta g - \alpha \in \mathfrak{P}^{1-(n+1)/2}_{\mathfrak{A}}$. Then $\beta$ is near $\alpha$ or near its conjugate $\bar\alpha$, because $\alpha - \bar\alpha$ has order $-n$. In the first case `Langlands.LocalGL2.IsAdapted.mem_jGroup_iff_conj_sub_mem` gives $g \in J_\alpha$, and `Langlands.LocalGL2.TameDatum.eq_of_intertwinesWith_of_mem_J` gives $\xi = \xi'$. In the second case the same argument applies after the transport of $D'$ along the conjugation of $L/K$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§13, 15 and 20.
-/

namespace Langlands.LocalGL2

universe u v

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section Rebase

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]

/-- **The change of basis normalizes the chain order.** Let $v$ and $v'$ be two bases of $E$ adapted to $\mathfrak{A}$. Then the change of basis from $v$ to $v'$ lies in $\mathfrak{K}_{\mathfrak{A}}$. -/
theorem basisChangeGL_mem_normalizer {A : ChainOrder} {v v' : Module.Basis (Fin 2) F E}
    (hv : IsAdapted A v) (hv' : IsAdapted A v') : basisChangeGL v v' ∈ normalizer F A := by
  intro X hX
  rw [val_basisChangeGL, val_basisChangeGL_inv]
  exact ⟨(mem_radPow_basisChange_iff hv hv' 0 X).2 hX, (mem_radPow_basisChange_iff hv' hv 0 X).2 hX⟩

end Rebase

section Datum

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

variable {L L' : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  [Algebra.IsQuadraticExtension K L'] {ξ : Lˣ →* ℂˣ} {ξ' : L'ˣ →* ℂˣ}

/-- Two data for one field $L$ have the same chain order, because its period is $e(L|K)$. -/
theorem A_eq_of_field {ζ : Lˣ →* ℂˣ} (D : TameDatum K L ξ) (D' : TameDatum K L ζ) :
    D'.A = D.A :=
  ChainOrder.eq_of_e_eq (D'.hv.ramIdx_eq.symm.trans D.hv.ramIdx_eq)

/-- The field of a datum for the maximal order is unramified over $K$. -/
theorem isUnramifiedExt_of_maximal (D : TameDatum K L ξ) (hA : D.A = maximal) :
    IsUnramifiedExt K L := by
  rw [isUnramifiedExt_iff_ramIdx, D.hv.ramIdx_eq, hA]
  rfl

/-- **Data for the maximal order have one field.** If $D$ is a datum for $(L/K, \xi)$ and $D'$ a datum for $(L'/K, \xi')$, both for the maximal order, then $L = L'$. Both extensions are unramified, and there is only one unramified quadratic extension of $K$ in $\bar K$. -/
theorem eq_of_maximal [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] (D : TameDatum K L ξ)
    (D' : TameDatum K L' ξ') (hA : D.A = maximal) (hA' : D'.A = D.A) : L = L' :=
  uniqueUnramifiedQuad_holds L L' (D.isUnramifiedExt_of_maximal hA)
    (D'.isUnramifiedExt_of_maximal (hA'.trans hA))

/-- **The final step for one basis.** Let $D$ and $D'$ be data for $(L/K, \xi)$ and $(L/K, \xi')$ with the same basis. If an element $g \in J_\alpha$ of $D$ intertwines $\Lambda$ with $\Lambda'$, then $\xi = \xi'$. For $y \in L^\times$ the element $g^{-1} \iota(y) g$ lies in $J_\alpha$, and $\xi'(y) = \Lambda'(\iota(y)) = \Lambda(g^{-1} \iota(y) g) = \Lambda(\iota(y)) = \xi(y)$. -/
theorem eq_of_intertwinesWith_of_mem_J {ζ : Lˣ →* ℂˣ} (D : TameDatum K L ξ)
    (D' : TameDatum K L ζ) (hv : D'.v = D.v) {g : GL (Fin 2) K}
    (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) (hgJ : g ∈ D.J) : ξ = ζ := by
  ext1 y
  have hy := embGL_mem_jGroup D.hv ((level D.ξ₀ + 1) / 2) y
  have hx : g⁻¹ * embGL D.v y * g ∈ D.J := D.J.mul_mem (D.J.mul_mem (D.J.inv_mem hgJ) hy) hgJ
  have hc : g * (g⁻¹ * embGL D.v y * g) * g⁻¹ = embGL D'.v y := by
    rw [hv]
    group
  have hx' : g * ((⟨_, hx⟩ : D.J) : GL (Fin 2) K) * g⁻¹ ∈ D'.J := by
    change g * (g⁻¹ * embGL D.v y * g) * g⁻¹ ∈ D'.J
    rw [hc]
    exact embGL_mem_jGroup D'.hv _ _
  have e := hg ⟨_, hx⟩ hx'
  have e1 : (⟨_, hx⟩ : D.J) = (⟨g, hgJ⟩ : D.J)⁻¹ * ⟨_, hy⟩ * ⟨g, hgJ⟩ := rfl
  have e2 : D.Λ ⟨_, hx⟩ = D.Λ ⟨_, hy⟩ := by
    rw [e1, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [e2, D.Λ_embGL] at e
  rw [← e, ← D'.Λ_embGL]
  exact congrArg D'.Λ (Subtype.ext hc)

end TameDatum

end Datum

section Statements

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Intertwining data for the Iwahori order have isomorphic fields** (Bushnell and Henniart, 15.7 and 20.2). Let $p \ne 2$. Let $D$ be a datum for $(L/K, \xi)$ and $D'$ a datum for $(L'/K, \xi')$, both for the Iwahori order and with the same level. If some $g \in \mathfrak{K}_{\mathfrak{J}}$ intertwines $\Lambda$ with $\Lambda'$, then $L$ and $L'$ are $K$-isomorphic. -/
def TypeNormalizerRamifiedField : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    (g : GL (Fin 2) K), D.A = iwahori → D'.A = D.A → level D'.ξ₀ = level D.ξ₀ →
      g ∈ normalizer K D.A → IntertwinesWith D.J D'.J D.Λ D'.Λ g → Nonempty (P.L ≃ₐ[K] Q.L)

/-- **Intertwining data of one field and one basis have conjugate characters** (Bushnell and Henniart, 15.7 and 20.2). Let $p \ne 2$. Let $D$ be a datum for $(L/K, \xi)$ and $D'$ a datum for $(L/K, \xi')$ with the same chain order $\mathfrak{A}$, the same basis and the same level. If some $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\Lambda$ with $\Lambda'$, then $\xi = \xi' \circ \sigma$ for a $K$-automorphism $\sigma$ of $L$. -/
def TypeNormalizerSameBasisIso : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (L : IntermediateField K (AlgebraicClosure K))
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] (ξ ξ' : Lˣ →* ℂˣ)
    (D : TameDatum K L ξ) (D' : TameDatum K L ξ') (g : GL (Fin 2) K), D'.A = D.A → D'.v = D.v →
      level D'.ξ₀ = level D.ξ₀ → g ∈ normalizer K D.A → IntertwinesWith D.J D'.J D.Λ D'.Λ g →
        ∃ σ : L ≃ₐ[K] L, ξ = ξ'.comp (unitsMap σ)

end Statements

section Reduction

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TameDatum

/-- **The fields of intertwining data are isomorphic**, if `Langlands.LocalGL2.TypeNormalizerRamifiedField K` holds. Let $p \ne 2$. For the maximal order the fields are equal by `Langlands.LocalGL2.TameDatum.eq_of_maximal`. For the Iwahori order the statement is the hypothesis. -/
theorem nonempty_algEquiv_of_intertwinesWith (hR : TypeNormalizerRamifiedField K)
    (h2 : (2 : 𝓀[K]) ≠ 0) {P Q : TamePair K} (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ)
    {g : GL (Fin 2) K} (hA : D'.A = D.A) (hl : level D'.ξ₀ = level D.ξ₀)
    (hgN : g ∈ normalizer K D.A) (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) :
    Nonempty (P.L ≃ₐ[K] Q.L) := by
  cases hD : D.A
  · exact ⟨IntermediateField.equivOfEq (D.eq_of_maximal D' hD hA)⟩
  · exact hR h2 P Q D D' g hD hA hl hgN hg

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  [Algebra.IsSeparable K L] {ξ ξ' : Lˣ →* ℂˣ}

/-- **The rebase step.** Let $p \ne 2$ and let `Langlands.LocalGL2.TypeNormalizerSameBasisIso K` hold. Let $D$ and $D'$ be data for $(L/K, \xi)$ and $(L/K, \xi')$ with the same level, and let $g \in \mathfrak{K}_{\mathfrak{A}}$ intertwine $\Lambda$ with $\Lambda'$. Then $\xi = \xi' \circ \sigma$ for a $K$-automorphism $\sigma$ of $L$. The rebase of $D'$ to the basis of $D$ has the character $\Lambda'$ conjugated by the change of basis $b$, and $b g \in \mathfrak{K}_{\mathfrak{A}}$ intertwines $\Lambda$ with it. -/
theorem exists_eq_comp_of_sameBasisIso (hS : TypeNormalizerSameBasisIso K) (h2 : (2 : 𝓀[K]) ≠ 0)
    (D : TameDatum K L ξ) (D' : TameDatum K L ξ') {g : GL (Fin 2) K}
    (hl : level D'.ξ₀ = level D.ξ₀) (hgN : g ∈ normalizer K D.A)
    (hg : IntertwinesWith D.J D'.J D.Λ D'.Λ g) : ∃ σ : L ≃ₐ[K] L, ξ = ξ'.comp (unitsMap σ) := by
  have hA := D.A_eq_of_field D'
  have hv' : IsAdapted D'.A D.v := hA ▸ D.hv
  set D₂ := D'.rebase D.v hv' with hD₂
  set b := basisChangeGL D.v D'.v with hb
  have hbN : b ∈ normalizer K D.A := basisChangeGL_mem_normalizer D.hv (hA ▸ D'.hv)
  refine hS h2 L ξ ξ' D D₂ (b * g) hA rfl hl ((normalizer K D.A).mul_mem hbN hgN) ?_
  intro x hx
  have hmem : b⁻¹ * (b * g * x * (b * g)⁻¹) * b ∈ D'.J :=
    (mem_jGroup_basisChange_iff hv' D'.hv _ _).1 hx
  have e1 : b⁻¹ * (b * g * x * (b * g)⁻¹) * b = g * x * g⁻¹ := by group
  rw [e1] at hmem
  rw [← hg x hmem]
  change D'.Λ ⟨b⁻¹ * (b * g * x * (b * g)⁻¹) * b, _⟩ = _
  exact congrArg D'.Λ (Subtype.ext e1)

end TameDatum

/-- **The reduction of `Langlands.LocalGL2.TypeIntertwiningNormalizerIso`.** The statements `Langlands.LocalGL2.TypeNormalizerRamifiedField K` and `Langlands.LocalGL2.TypeNormalizerSameBasisIso K` give `Langlands.LocalGL2.TypeIntertwiningNormalizerIso K`. A $K$-isomorphism $j : L \to L'$ moves the datum $D'$ to a datum for $(L/K, \xi' \circ j)$ with the same group and character. The rebase step gives $\xi = \xi' \circ j \circ \sigma$. -/
theorem typeIntertwiningNormalizerIso_of_ramifiedField_of_sameBasisIso
    (hR : TypeNormalizerRamifiedField K) (hS : TypeNormalizerSameBasisIso K) :
    TypeIntertwiningNormalizerIso K := by
  intro h2 P Q D D' g hA hl hgN hg
  obtain ⟨j⟩ := D.nonempty_algEquiv_of_intertwinesWith hR h2 D' hA hl hgN hg
  set D₁ := D'.transport j with hD₁
  have hl₁ : level D₁.ξ₀ = level D.ξ₀ :=
    (level_comp_unitsMap D'.minimal.admissible j).trans hl
  have hg₁ : IntertwinesWith D.J D₁.J D.Λ D₁.Λ g := fun x hx =>
    hg x (D'.transport_jGroup_le j hx)
  obtain ⟨σ, hσ⟩ := D.exists_eq_comp_of_sameBasisIso hS h2 D₁ hl₁ hgN hg₁
  refine ⟨σ.trans j, MonoidHom.ext fun y => ?_⟩
  rw [hσ]
  rfl

/-- **Isomorphic type representations come from isomorphic pairs**, if `Langlands.LocalGL2.TypeNormalizerRamifiedField K` and `Langlands.LocalGL2.TypeNormalizerSameBasisIso K` hold. This is `Langlands.LocalGL2.TypeRepInjective K`. -/
theorem typeRepInjective_of_ramifiedField_of_sameBasisIso (hR : TypeNormalizerRamifiedField K)
    (hS : TypeNormalizerSameBasisIso K) : TypeRepInjective K :=
  typeRepInjective_of_typeIntertwiningNormalizerIso
    (typeIntertwiningNormalizerIso_of_ramifiedField_of_sameBasisIso hR hS)

end Reduction

end Langlands.LocalGL2
