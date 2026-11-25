/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Selberg's eigenvalue conjecture and the Ramanujan conjecture for Maass forms

This file states two rows of 6.2.2 of the spec about the spectrum of the hyperbolic Laplacian on the quotients of the upper half-plane by congruence subgroups. Each statement is a `def` of type `Prop`. Both statements are open conjectures.

* `Langlands.SelbergEigenvalue`: for a congruence subgroup $\Gamma$ of $SL_2(\mathbb{Z})$, each eigenvalue $\lambda \neq 0$ of the hyperbolic Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ satisfies $\lambda \ge 1/4$. This is the conjecture of Selberg.
* `Langlands.RamanujanMaass`: for a Maass cusp form $f$ on $\Gamma_1(N)$ with character $\chi$ and a prime $p \nmid N$, an eigenvalue $c$ of the normalized Hecke operator $T_p$ on $f$ satisfies $|c| \le 2$. This is the Ramanujan conjecture at the finite primes for Maass forms.

The fidelity checks of spec 06.3 for these statements are in `Langlands.Fidelity.Maass`.

## Implementation notes

Mathlib has no Maass forms. The definitions in this file are concrete. A function $f : \mathbb{H} \to \mathbb{C}$ is extended to $\mathbb{C}$ by `UpperHalfPlane.ofComplex`. Its values outside $\mathbb{H}$ are not used, because the Laplacian at a point of the open set $\mathbb{H}$ depends only on the values near the point. The hyperbolic Laplacian is $\Delta_{\mathbb{H}} = -y^2 (\partial_x^2 + \partial_y^2)$, where $\partial_x^2 + \partial_y^2$ is `Laplacian.laplacian` of Mathlib on $\mathbb{C} = \mathbb{R}^2$. With this sign $\Delta_{\mathbb{H}}$ is a nonnegative operator, and the eigenvalue of $y^s$ is $s(1 - s)$.

A function is square integrable on $\Gamma \backslash \mathbb{H}$ for the measure $dx \, dy / y^2$ if $\int_{\mathcal{F}} |f(g z)|^2 \, dx \, dy / y^2 < \infty$ for each $g \in SL_2(\mathbb{Z})$, where $\mathcal{F}$ is the standard fundamental domain `ModularGroup.fd` of $SL_2(\mathbb{Z})$. A congruence subgroup has finite index, so finitely many translates $g \mathcal{F}$ cover a fundamental domain of $\Gamma$, and the two conditions are equivalent.

The eigenfunctions are smooth and the eigenvalue equation holds pointwise. This is not a restriction. By elliptic regularity each eigenfunction of the self-adjoint Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ is real analytic and satisfies the equation pointwise. Conversely, the quotient is complete and has finite area, so a smooth square integrable function $f$ with $\Delta_{\mathbb{H}} f = \lambda f$ is in the domain of the self-adjoint Laplacian. Its eigenvalue is real and nonnegative. So the eigenvalue in the statements is a real number.

The normalization of the Hecke operators is the unitary one: $T_p f(z) = p^{-1/2} \left( \chi(p) f(p z) + \sum_{b = 0}^{p - 1} f\left(\frac{z + b}{p}\right) \right)$. With this normalization the Satake parameters $\alpha_p, \beta_p$ satisfy $\alpha_p + \beta_p = c$ and $\alpha_p \beta_p = \chi(p)$, and the Ramanujan conjecture is $|\alpha_p| = |\beta_p| = 1$, which is equivalent to $|c| \le 2$. In the arithmetic normalization without the factor $p^{-1/2}$ the bound is $2 p^{1/2}$. The trivial bound for the constant function is $p^{1/2} + p^{-1/2}$. The best known bound for cusp forms is $p^{7/64} + p^{-7/64}$, by Kim and Sarnak.

The Maass cusp forms are on $\Gamma_1(N)$ with a character $\chi$ modulo $N$: $f(\gamma z) = \chi(d) f(z)$ for $\gamma \in \Gamma_0(N)$ with lower right entry $d$. A cusp form is a form whose constant term vanishes at each cusp. At the cusp $g \infty$ the function $f \circ g$ is invariant under $z \mapsto z + N$, so the condition is $\int_0^N f(g(x + i y)) \, dx = 0$ for each $g \in SL_2(\mathbb{Z})$ and each $y > 0$.

## References

* A. Selberg, On the estimation of Fourier coefficients of modular forms, Proc. Sympos. Pure Math. 8 (1965).
* H. Iwaniec, Spectral methods of automorphic forms, second edition, 2002, chapters 4 and 11.
* P. Sarnak, Notes on the generalized Ramanujan conjectures, Clay Math. Proc. 4 (2005).
* H. Kim, Functoriality for the exterior square of GL4 and the symmetric fourth of GL2, with appendix 2 by H. Kim and P. Sarnak, J. Amer. Math. Soc. 16 (2003).
-/

namespace Langlands

open UpperHalfPlane CongruenceSubgroup MeasureTheory

open scoped MatrixGroups ContDiff Laplacian

/-! ### The hyperbolic Laplacian -/

/-- A function on $\mathbb{H}$ as a function on $\mathbb{C}$. Its values outside $\mathbb{H}$ are not used. -/
noncomputable def onPlane (f : ℍ → ℂ) : ℂ → ℂ :=
  fun z => f (ofComplex z)

/-- The hyperbolic Laplacian $\Delta_{\mathbb{H}} f = -y^2 (\partial_x^2 f + \partial_y^2 f)$ on the upper half-plane. -/
noncomputable def hyperbolicLaplacian (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  -((τ.im : ℂ) ^ 2) * Δ (onPlane f) (τ : ℂ)

/-- A function $f$ on $\mathbb{H}$ is a square integrable eigenfunction of the hyperbolic Laplacian on $\Gamma \backslash \mathbb{H}$ with eigenvalue $\lambda$ if it is smooth, invariant under $\Gamma$, satisfies $\Delta_{\mathbb{H}} f = \lambda f$, and is square integrable on each translate $g \mathcal{F}$ of the standard fundamental domain of $SL_2(\mathbb{Z})$ for the measure $dx \, dy / y^2$. -/
structure IsL2Eigenfunction (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (ev : ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (onPlane f) {z : ℂ | 0 < z.im}
  invariant : ∀ γ ∈ Γ, ∀ τ : ℍ, f (γ • τ) = f τ
  eigen : ∀ τ : ℍ, hyperbolicLaplacian f τ = ev * f τ
  squareIntegrable : ∀ g : SL(2, ℤ),
    IntegrableOn (fun z : ℂ => ‖f (g • ofComplex z)‖ ^ 2 / z.im ^ 2)
      ((↑) '' ModularGroup.fd)

/-- **Selberg's eigenvalue conjecture** (open). Let $\Gamma$ be a congruence subgroup of $SL_2(\mathbb{Z})$. Each eigenvalue $\lambda \ne 0$ of the hyperbolic Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ satisfies $\lambda \ge 1/4$.

This is the form with the full discrete spectrum. The textbook form is $\lambda_1(\Gamma) \ge 1/4$ for the smallest positive eigenvalue. The two forms are the same. The continuous spectrum, from the Eisenstein series, is $[1/4, \infty)$. For a congruence subgroup the residual spectrum is only the constants, with $\lambda = 0$, so the conjecture is equivalent to the bound $\lambda \ge 1/4$ for the Maass cusp forms. The condition $\lambda \ne 0$ is necessary, because the constant functions are square integrable eigenfunctions with $\lambda = 0$. Selberg proved $\lambda \ge 3/16$, and the best known bound is $\lambda \ge 1/4 - (7/64)^2$, by Kim and Sarnak. -/
def SelbergEigenvalue : Prop :=
  ∀ (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (ev : ℝ), IsCongruenceSubgroup Γ → f ≠ 0 →
    IsL2Eigenfunction Γ f ev → ev ≠ 0 → 1 / 4 ≤ ev

/-! ### Maass cusp forms and Hecke operators -/

/-- A Maass cusp form on $\Gamma_1(N)$ with character $\chi$ and Laplace eigenvalue $\lambda$: a square integrable eigenfunction of the Laplacian with $f(\gamma z) = \chi(d) f(z)$ for $\gamma \in \Gamma_0(N)$, whose constant term $\int_0^N f(g(x + i y)) \, dx$ vanishes at each cusp $g \infty$ and each height $y > 0$. -/
structure IsMaassCuspForm (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (ev : ℝ) :
    Prop where
  eigenfunction : IsL2Eigenfunction (Gamma1 N) f ev
  nebentypus : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ,
    f (γ • τ) = χ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) * f τ
  cuspidal : ∀ (g : SL(2, ℤ)) (y : ℝ), 0 < y →
    ∫ x in (0 : ℝ)..N, f (g • ofComplex (x + y * Complex.I)) = 0

/-- The Hecke operator $T_p f(z) = p^{-1/2} \left( \chi(p) f(p z) + \sum_{b = 0}^{p - 1} f\left(\frac{z + b}{p}\right) \right)$ in the unitary normalization. -/
noncomputable def heckeOperator {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) (f : ℍ → ℂ)
    (τ : ℍ) : ℂ :=
  ((Real.sqrt p)⁻¹ : ℂ) * (χ (p : ZMod N) * f (ofComplex ((p : ℂ) * τ)) +
    ∑ b ∈ Finset.range p, f (ofComplex (((τ : ℂ) + b) / p)))

/-- **The Ramanujan conjecture for Maass forms** (open). Let $f \ne 0$ be a Maass cusp form on $\Gamma_1(N)$ with character $\chi$, and let $p \nmid N$ be a prime. If $T_p f = c f$, then $|c| \le 2$.

The normalization is the unitary one of `heckeOperator`, so $|c| \le 2$ is the condition that the Satake parameters at $p$ have absolute value 1. This is the conjecture at the finite primes. The conjecture at the infinite prime is `SelbergEigenvalue`. The textbook form is for a newform that is an eigenfunction of all the Hecke operators. The statement here is for each eigenvector of the single operator $T_p$. The two forms are equivalent: the space of cusp forms with a given Laplace eigenvalue has finite dimension and a basis of common eigenvectors of the operators $T_n$ with $(n, N) = 1$, and an oldform has the eigenvalues of a newform of lower level. The condition that $f$ is a cusp form is necessary, because the constant function has $c = p^{1/2} + p^{-1/2} > 2$. -/
def RamanujanMaass : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (ev : ℝ), 0 < N → f ≠ 0 →
    IsMaassCuspForm N χ f ev →
    ∀ (p : ℕ) (c : ℂ), p.Prime → ¬ p ∣ N → heckeOperator χ p f = c • f → ‖c‖ ≤ 2

end Langlands
