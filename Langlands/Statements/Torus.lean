/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units

/-!
# The local Langlands correspondence for split tori

Let $T = \mathbb{G}_m^n$ be the split torus of rank $n$ over a nonarchimedean local field $K$. Then $T(K) = (K^\times)^n$, and the dual torus is $\hat T = (\mathbb{C}^\times)^n$ with the trivial action of $W_K$. The local Langlands correspondence for $T$ is a bijection between the continuous characters of $T(K)$ and the continuous homomorphisms $W_K \to \hat T$. For an action that is trivial, $H^1(W_K, \hat T)$ is the group of these homomorphisms.

* `Langlands.TorusCorrespond`: the relation between a character $\chi$ of $(K^\times)^n$ and a homomorphism $\varphi : W_K \to (\mathbb{C}^\times)^n$ through a reciprocity map $\mathrm{rec}_K$. It says that $\chi(x) = \prod_i \varphi_i(w_i)$ when the class of $w_i$ in $W_K^{ab}$ is $\mathrm{rec}_K(x_i)$ for each $i$.
* `Langlands.LocalLanglandsTorusSplit`: for each local Artin map $\mathrm{rec}_K$, the relation `TorusCorrespond` is the graph of a bijection.

## Implementation notes

An abstract isomorphism between the two groups of characters says nothing, because both groups are very large. The statement fixes the bijection: it is the composite with $\mathrm{rec}_K$. This is the normalization of Langlands for tori, in the geometric convention of `Langlands.IsLocalArtinMap`.

The induced tori $\mathrm{Res}_{L/K} \mathbb{G}_m$ need the Weil group of $L$ as an open subgroup of $W_K$ and Shapiro's lemma for continuous cohomology. They are in `Langlands.Statements.TorusInduced`.

## References

* R. P. Langlands, Representations of abelian algebraic groups, Pacific J. Math. 181 (1997).
* J. Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, part 2, 1979, section 9.
-/

namespace Langlands

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The relation of the local Langlands correspondence for $\mathbb{G}_m^n$ through a reciprocity map $\mathrm{rec}_K$: $\chi(x) = \prod_i \varphi_i(w_i)$ for each $x \in (K^\times)^n$ and each $w \in W_K^n$ with $[w_i] = \mathrm{rec}_K(x_i)$ in $W_K^{ab}$. -/
def TorusCorrespond {n : ℕ} (rec : Kˣ ≃ₜ* WeilGroup.Ab K)
    (χ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ)
    (φ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ)) : Prop :=
  ∀ (x : Fin n → Kˣ) (w : Fin n → WeilGroup K),
    (∀ i, (QuotientGroup.mk (w i) : WeilGroup.Ab K) = rec (x i)) → χ x = ∏ i, φ (w i) i

/-- **The local Langlands correspondence for split tori** (Langlands). For each local Artin map $\mathrm{rec}_K$, each continuous character of $(K^\times)^n$ corresponds to exactly one continuous homomorphism $W_K \to (\mathbb{C}^\times)^n$, and each such homomorphism corresponds to a character. -/
def LocalLanglandsTorusSplit (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (rec : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K rec →
      (∀ χ : ContinuousMonoidHom (Fin n → Kˣ) ℂˣ, ∃! φ, TorusCorrespond K rec χ φ) ∧
        ∀ φ : ContinuousMonoidHom (WeilGroup K) (Fin n → ℂˣ), ∃ χ, TorusCorrespond K rec χ φ

end Langlands
