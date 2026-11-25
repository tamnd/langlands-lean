/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Smooth
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Godement-Jacquet L-factor of a representation of GL(n)

Let $K$ be a nonarchimedean local field with residue field of $q$ elements, and let $\pi$ be an irreducible admissible representation of $GL_n(K)$. Godement and Jacquet attach to $\pi$ the zeta integrals
$$Z(\Phi, s, f) = \int_{GL_n(K)} \Phi(g) f(g) |\det g|^{s + (n-1)/2} \, d^\times g,$$
where $\Phi$ is a Schwartz-Bruhat function on $M_n(K)$ (locally constant with compact support) and $f(g) = \lambda(\pi(g) v)$ is a matrix coefficient of $\pi$, with $v \in V$ and $\lambda$ in the contragredient. The integral converges for $\mathrm{Re}(s)$ large. As a function of $q^{-s}$ it is a rational function, and the $\mathbb{C}[q^{s}, q^{-s}]$-span of all the zeta integrals is a fractional ideal with a unique generator of the form $L(s, \pi) = P(q^{-s})^{-1}$, where $P$ is a polynomial with $P(0) = 1$. This $L(s, \pi)$ is the standard L-factor of $\pi$.

On $GL_n(K)$ the multiplicative Haar measure is $d^\times g = |\det g|^{-n} dg$ for an additive Haar measure $dg$ on $M_n(K)$. The file writes the integral on $M_n(K)$ with this density, and the complement of $GL_n(K)$ in $M_n(K)$ has measure zero.

* `Langlands.IsSchwartzBruhat`: a locally constant function with compact support on $M_n(K)$.
* `Langlands.gjZeta`: the zeta integral $Z(\Phi, s, f)$.
* `Langlands.IsGJLFactor`: $L$ is the Godement-Jacquet L-factor of $\pi$.

## Implementation notes

`IsGJLFactor π L` is a characterization, not data. It says that $L(s) = P(q^{-s})^{-1}$ with $P(0) = 1$, that each zeta integral is $R(q^{-s}) L(s)$ for a Laurent polynomial $R$ when $\mathrm{Re}(s)$ is large, and that some finite combination of zeta integrals with Laurent polynomial coefficients is $L(s)$ when $\mathrm{Re}(s)$ is large. Two functions with these properties differ by a unit $c X^k$ of $\mathbb{C}[X, X^{-1}]$, and the normalization $P(0) = 1$ gives $c = 1$ and $k = 0$. So at most one function has these properties, and the theorem of Godement and Jacquet says that one exists.

The additive Haar measure is `MeasureTheory.Measure.addHaar` for the Borel structure of $M_n(K)$. Another Haar measure multiplies each zeta integral by a constant, and this does not change the fractional ideal.

The Lebesgue integral of Lean is zero for a function that is not integrable. The characterization uses the integrals only for $\mathrm{Re}(s)$ larger than a bound, where they converge absolutely.

## References

* R. Godement, H. Jacquet, Zeta functions of simple algebras, LNM 260, Springer, 1972, theorem 3.3.
* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, chapter 6.
-/

namespace Langlands

universe u

open MeasureTheory

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A Schwartz-Bruhat function on $M_n(K)$: a locally constant function with compact support. -/
def IsSchwartzBruhat {n : ℕ} (Φ : Matrix (Fin n) (Fin n) K → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ

/-- The Borel structure on $M_n(K)$. -/
noncomputable abbrev matrixBorel (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) K) :=
  borel _

/-- An additive Haar measure on $M_n(K)$. -/
noncomputable def matrixHaar (n : ℕ) : @Measure (Matrix (Fin n) (Fin n) K) (matrixBorel K n) :=
  letI := matrixBorel K n
  haveI : BorelSpace (Matrix (Fin n) (Fin n) K) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → K))
  Measure.addHaar

open scoped Classical in
/-- The Godement-Jacquet zeta integral $Z(\Phi, s, f) = \int_{M_n(K)} \Phi(x) f(x) |\det x|^{s + (n-1)/2 - n} \, dx$ for the matrix coefficient $f(g) = \lambda(\pi(g) v)$. The integrand is zero off $GL_n(K)$. -/
noncomputable def gjZeta {n : ℕ} (π : SmoothRep (GL (Fin n) K)) (Φ : Matrix (Fin n) (Fin n) K → ℂ)
    (v : π.V) (l : Module.Dual ℂ π.V) (s : ℂ) : ℂ :=
  letI := matrixBorel K n
  ∫ x, (if h : IsUnit x.det then
      Φ x * π.coeff v l (Matrix.nonsingInvUnit x h) *
        ((normAbs K x.det : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n))
    else 0) ∂(matrixHaar K n)

/-- $L$ is the Godement-Jacquet L-factor $L(s, \pi)$. Write $X = q^{-s}$. Then $L(s) = P(X)^{-1}$ for a polynomial $P$ with $P(0) = 1$; each zeta integral $Z(\Phi, s, f)$ with $\lambda$ smooth is $A(X) X^{-k} L(s)$ for $\mathrm{Re}(s)$ large; and $L(s)$ is a finite sum $\sum_i A_i(X) X^{-k} Z(\Phi_i, s, f_i)$ for $\mathrm{Re}(s)$ large. These properties determine $L$. -/
def IsGJLFactor {n : ℕ} (π : SmoothRep (GL (Fin n) K)) (L : ℂ → ℂ) : Prop :=
  (∃ P : Polynomial ℂ, P.coeff 0 = 1 ∧ ∀ s, L s = (P.eval ((residueCard K : ℂ) ^ (-s)))⁻¹) ∧
  (∀ (Φ : Matrix (Fin n) (Fin n) K → ℂ) (v : π.V) (l : smoothVectors π.ρ.dual),
    IsSchwartzBruhat K Φ → ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
      gjZeta K π Φ v l s =
        A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k * L s) ∧
  ∃ (j : ℕ) (Φ : Fin j → Matrix (Fin n) (Fin n) K → ℂ) (v : Fin j → π.V)
    (l : Fin j → smoothVectors π.ρ.dual) (A : Fin j → Polynomial ℂ) (k : ℕ) (s₀ : ℝ),
    (∀ i, IsSchwartzBruhat K (Φ i)) ∧ ∀ s : ℂ, s₀ < s.re →
      L s = ∑ i, (A i).eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k *
        gjZeta K π (Φ i) (v i) (l i) s

end Langlands
