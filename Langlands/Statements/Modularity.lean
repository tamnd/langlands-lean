/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The statements of modularity over the rationals

This file states the modularity theorems for elliptic curves over $\mathbb{Q}$ and two related statements about the coefficients of modular forms. These are the rows of 6.2.2 of the spec that use $q$-expansions. Each statement is a `def` of type `Prop`. A theorem that is published but not yet formalized is a `def`, never an axiom.

* `Langlands.ModularityEllipticQ`: for each elliptic curve $E$ over $\mathbb{Q}$ there is a cusp form $f$ of weight 2 on $\Gamma_0(N)$ with $a_n(f) = a_n(E)$ for every $n \ge 1$, so that $L(f, s) = L(E, s)$. This is the theorem of Breuil, Conrad, Diamond and Taylor.
* `Langlands.ModularitySemistableQ`: the same statement for the semistable curves. This is the theorem of Wiles and Taylor-Wiles.
* `Langlands.HasseWeilEllipticQ`: the completed L-function of $E$ continues to an entire function with a functional equation $\Lambda(2 - s) = \pm \Lambda(s)$.
* `Langlands.RamanujanPeterssonHolomorphic`: for a normalized Hecke eigenform of weight $k$ on $\Gamma_0(N)$ and a prime $p \nmid N$, $|a_p| \le 2 p^{(k-1)/2}$. This is the theorem of Deligne, and of Deligne and Serre for $k = 1$.
* `Langlands.SatoTate`: for an elliptic curve over $\mathbb{Q}$ without complex multiplication, the angles $\theta_p$ with $a_p = 2 \sqrt{p} \cos \theta_p$ are equidistributed for the measure $\frac{2}{\pi} \sin^2 \theta \, d\theta$ on $[0, \pi]$. This is the theorem of Barnet-Lamb, Geraghty, Harris and Taylor.

## Implementation notes

The coefficients $a_n(E)$ are those of `WeierstrassCurve.LFunction` in Mathlib. This is the Euler product of the local factors of a minimal model at each prime, so it includes the factors at the primes of bad reduction. The statement `ModularityEllipticQ` asks for equality of all the coefficients, not only of almost all of them. A cusp form with these coefficients is automatically a normalized eigenform of all the Hecke operators, and it is the newform of level the conductor of $E$.

Mathlib does not have Hecke operators on modular forms yet. The structure `IsNormalizedEigenform` uses the equivalent conditions on the $q$-expansion: $a_1 = 1$, the coefficients are multiplicative, and they satisfy the recursion of the Euler factor at each prime. For a cusp form on $\Gamma_0(N)$ these conditions hold if and only if the form is an eigenvector of each $T_n$ with $a_1 = 1$.

The statement `HasseWeilEllipticQ` asks for some level $N \ge 1$ in the gamma factor. The functional equation determines $N$, and $N$ is the conductor of $E$. The definition of the conductor is not needed for the statement.

An elliptic curve over $\mathbb{Q}$ has complex multiplication if and only if its $j$-invariant is one of 13 rational numbers, one for each imaginary quadratic order of class number one. The predicate `HasCMOverQ` uses this list. This is a theorem of the theory of complex multiplication. When Mathlib has the endomorphism ring of an elliptic curve, a fidelity file will compare the list with the definition by endomorphisms.

## References

* C. Breuil, B. Conrad, F. Diamond and R. Taylor, On the modularity of elliptic curves over Q, J. Amer. Math. Soc. 14 (2001).
* A. Wiles, Modular elliptic curves and Fermat's last theorem, Ann. of Math. 141 (1995).
* P. Deligne, La conjecture de Weil. I, Publ. Math. IHES 43 (1974).
* T. Barnet-Lamb, D. Geraghty, M. Harris and R. Taylor, A family of Calabi-Yau varieties and potential automorphy II, Publ. RIMS 47 (2011).
* J. Silverman, The arithmetic of elliptic curves, second edition, 2009.
-/

namespace Langlands

open Filter Topology Real IsDedekindDomain NumberField
open scoped MatrixGroups

/-- The $q$-expansion of a cusp form on $\Gamma_0(N)$, at the cusp $\infty$ with width 1. -/
noncomputable def qCoeff {N : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

/-- A cusp form of weight $k$ on $\Gamma_0(N)$ is a normalized Hecke eigenform if its $q$-expansion has $a_1 = 1$, is multiplicative, and satisfies the recursion of the Euler factor at each prime. These are the conditions for an eigenvector of every Hecke operator $T_n$ with trivial character. -/
structure IsNormalizedEigenform {N : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : Prop where
  one : qCoeff f 1 = 1
  mul : ∀ m n : ℕ, m.Coprime n → qCoeff f (m * n) = qCoeff f m * qCoeff f n
  good : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * qCoeff f (p ^ r)
  bad : ∀ p r : ℕ, p.Prime → p ∣ N → qCoeff f (p ^ (r + 1)) = qCoeff f p * qCoeff f (p ^ r)

/-- **Modularity of elliptic curves over $\mathbb{Q}$** (Breuil, Conrad, Diamond and Taylor). Each elliptic curve $E$ over $\mathbb{Q}$ has a cusp form of weight 2 on $\Gamma_0(N)$ for some $N \ge 1$ whose $q$-expansion coefficients are the coefficients of $L(E, s)$. -/
def ModularityEllipticQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E.LFunction n : ℂ)

/-- An elliptic curve over $\mathbb{Q}$ is semistable if a minimal model at each prime has good or multiplicative reduction, that is, no prime has additive reduction. -/
def IsSemistable (E : WeierstrassCurve ℚ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ),
    ¬ ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasAdditiveReduction
      (v.adicCompletionIntegers ℚ)

/-- **Modularity of semistable elliptic curves over $\mathbb{Q}$** (Wiles, Taylor-Wiles). This is the case of `ModularityEllipticQ` that proves Fermat's last theorem. -/
def ModularitySemistableQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsSemistable E →
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      0 < N ∧ ∀ n : ℕ, 1 ≤ n → qCoeff f n = (E.LFunction n : ℂ)

/-- **The Hasse-Weil conjecture for elliptic curves over $\mathbb{Q}$**. The completed L-function $\Lambda(E, s) = N^{s/2} (2\pi)^{-s} \Gamma(s) L(E, s)$, defined for $\mathrm{Re}(s) > 3/2$, continues to an entire function with $\Lambda(E, 2 - s) = \varepsilon \Lambda(E, s)$ and $\varepsilon = \pm 1$. It follows from `ModularityEllipticQ` and the theory of Hecke. -/
def HasseWeilEllipticQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ (N : ℕ) (ε : ℤ) (Λ : ℂ → ℂ), 0 < N ∧ (ε = 1 ∨ ε = -1) ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        Λ s = (N : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Complex.Gamma s * E.LSeries s) ∧
      ∀ s : ℂ, Λ (2 - s) = ε * Λ s

/-- **The Ramanujan-Petersson conjecture for holomorphic forms** (Deligne; Deligne and Serre for weight 1). For a normalized Hecke eigenform of weight $k$ on $\Gamma_0(N)$ and a prime $p \nmid N$, $|a_p| \le 2 p^{(k-1)/2}$. -/
def RamanujanPeterssonHolomorphic : Prop :=
  ∀ (N : ℕ) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k),
    0 < N → IsNormalizedEigenform f → ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ‖qCoeff f p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)

/-- The 13 rational $j$-invariants of the elliptic curves over $\mathbb{Q}$ with complex multiplication, one for each imaginary quadratic order of class number one, of discriminant $-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163$. -/
def cmJInvariants : Set ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000,
    -147197952000, -262537412640768000}

/-- An elliptic curve over $\mathbb{Q}$ has complex multiplication over $\overline{\mathbb{Q}}$ if and only if its $j$-invariant is in `cmJInvariants`. -/
def HasCMOverQ (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ cmJInvariants

/-- The Sato-Tate angle $\theta_p \in [0, \pi]$ of $E$ at $p$, with $a_p = 2 \sqrt{p} \cos \theta_p$. By the Hasse bound the argument of $\arccos$ is in $[-1, 1]$ at each prime of good reduction. -/
noncomputable def satoTateAngle (E : WeierstrassCurve ℚ) (p : ℕ) : ℝ :=
  Real.arccos ((E.LFunction p : ℝ) / (2 * Real.sqrt p))

/-- **The Sato-Tate conjecture** (Barnet-Lamb, Geraghty, Harris and Taylor). For an elliptic curve over $\mathbb{Q}$ without complex multiplication and $0 \le \alpha \le \beta \le \pi$, the proportion of the primes $p \le x$ with $\theta_p \in [\alpha, \beta]$ tends to $\frac{2}{\pi} \int_\alpha^\beta \sin^2 \theta \, d\theta$. The finitely many primes of bad reduction do not change the limit. -/
def SatoTate : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ¬ HasCMOverQ E →
    ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ π →
      Tendsto
        (fun x : ℕ =>
          (Nat.card {p : ℕ // p.Prime ∧ p ≤ x ∧ satoTateAngle E p ∈ Set.Icc α β} : ℝ) /
            Nat.card {p : ℕ // p.Prime ∧ p ≤ x})
        atTop (𝓝 ((2 / π) * ∫ θ in α..β, Real.sin θ ^ 2))

end Langlands
