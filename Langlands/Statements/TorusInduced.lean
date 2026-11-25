/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Cohomology.Shapiro
import Langlands.Statements.Torus
import Langlands.WeilGroup.Embedding

/-!
# The local Langlands correspondence for induced tori

Let $L$ be a finite extension of a nonarchimedean local field $K$ inside $\bar K$, and let $T = \mathrm{Res}_{L/K} \mathbb{G}_m$. Then $T(K) = L^\times$, and the dual torus is the module $\mathrm{Coind}_{W_L}^{W_K} \mathbb{C}^\times$ of $W_K$, where $W_L$ is the open subgroup `restrictSubgroup K L` of $W_K$. The parameters of $T$ are the classes in $H^1(W_K, \hat T)$.

* `Langlands.InducedTorusCorrespond`: the relation between a character $\chi$ of $L^\times$ and a class $c$ through a reciprocity map $\mathrm{rec}_L$. Shapiro's isomorphism takes $c$ to a homomorphism on $W_L$, and the relation says that this homomorphism takes the value $\chi(x)$ at each $w \in W_L$ with $[w] = \mathrm{rec}_L(x)$.
* `Langlands.LocalLanglandsTorusInduced`: for each local Artin map $\mathrm{rec}_L$, the relation is the graph of a bijection.

## Implementation notes

Shapiro's isomorphism is injective, so the relation fixes the class $c$. The statement thus fixes the bijection, as in `Langlands.LocalLanglandsTorusSplit`.

## References

* R. P. Langlands, Representations of abelian algebraic groups, Pacific J. Math. 181 (1997).
* J. Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, part 2, 1979, section 9.
-/

namespace Langlands

universe u

open WeilGroup WeilGroup.FiniteExt

section Statement

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The relation of the local Langlands correspondence for the induced torus $\mathrm{Res}_{L/K} \mathbb{G}_m$ through a reciprocity map $\mathrm{rec}_L$: the image of the class $c$ under Shapiro's isomorphism takes the value $\chi(x)$ at the image in $W_K$ of each $w \in W_L$ with $[w] = \mathrm{rec}_L(x)$ in $W_L^{ab}$. -/
def InducedTorusCorrespond (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    (recL : Lˣ ≃ₜ* WeilGroup.Ab L) (χ : ContinuousMonoidHom Lˣ ℂˣ)
    (c : Shapiro.H1 (WeilGroup K) (Shapiro.Coind (restrictSubgroup K L) ℂˣ)) : Prop :=
  ∀ (x : Lˣ) (w : WeilGroup L), (QuotientGroup.mk w : WeilGroup.Ab L) = recL x →
    Shapiro.shapiro (isOpen_restrictSubgroup K L) c ⟨weilHom K L w, weilHom_mem K L w⟩ = χ x

/-- **The local Langlands correspondence for induced tori.** For a finite extension $L$ of $K$ and each local Artin map $\mathrm{rec}_L$ of $L$, each continuous character of $L^\times = \mathrm{Res}_{L/K} \mathbb{G}_m (K)$ corresponds to exactly one class in $H^1(W_K, \mathrm{Coind}_{W_L}^{W_K} \mathbb{C}^\times)$, and each such class corresponds to a character. -/
def LocalLanglandsTorusInduced : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    (recL : Lˣ ≃ₜ* WeilGroup.Ab L), IsLocalArtinMap L recL →
      (∀ χ : ContinuousMonoidHom Lˣ ℂˣ, ∃! c, InducedTorusCorrespond K L recL χ c) ∧
        ∀ c, ∃ χ : ContinuousMonoidHom Lˣ ℂˣ, InducedTorusCorrespond K L recL χ c

end Statement

end Langlands
