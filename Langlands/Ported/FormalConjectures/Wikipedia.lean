/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Statements of formal-conjectures

Ported from google-deepmind/formal-conjectures at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53, from the files `FormalConjectures/Wikipedia/ModularityConjecture.lean`, `SatoTateConjecture.lean`, `RamanujanTau.lean` and `HasseWeil.lean`.

The changes are these:

* Each `theorem` with `sorry` is a `def` of type `Prop` with the same name and the same statement.
* The namespaces have the prefix `Langlands.Ported.FormalConjectures`.
* The attributes `category` and `AMS`, the `module` header and the test lemmas are removed.
* The coercion of `N : ℕ+` to `ℝ` in `modularFormAn` is written as `((N : ℕ) : ℝ)`. This is the same term.

The definitions are otherwise copied without change. The bridges to the statements of the project are in `Langlands/Bridge/FormalConjectures.lean`.
-/

namespace Langlands.Ported.FormalConjectures

namespace ModularityConjecture

open Complex CongruenceSubgroup ModularFormClass UpperHalfPlane
open scoped Real ModularForm CongruenceSubgroup

/-- The `n`-th Fourier coefficient of a modular form (around the cusp at infinity). -/
noncomputable def modularFormAn (n : ℕ) {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : ℂ :=
  (qExpansion ((N : ℕ) : ℝ) f).coeff n

/-- The reduction of a rational number modulo `p`. -/
def ratRed (q : ℚ) (p : ℕ) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

/-- The set of points on an elliptic curve over `ZMod n`. -/
def setOfPointsModN (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) :=
  {P : ZMod n × ZMod n |
    let ⟨x, y⟩ := P
    y ^ 2 + ratRed E.a₁ n * x * y + ratRed E.a₃ n * y =
      x ^ 3 + ratRed E.a₂ n * x ^ 2 + ratRed E.a₄ n * x + ratRed E.a₆ n}

/-- The trace of Frobenius by point count on the affine curve. -/
noncomputable def WeierstrassCurve.ap (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : ℤ :=
  (p : ℤ) - Cardinal.toNat (Cardinal.mk (setOfPointsModN E p))

/-- Normalized eigenforms, by the conditions on the `q`-expansion coefficients. -/
def IsNormalisedEigenform {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : Prop :=
  modularFormAn 1 f = 1 ∧
  (∀ (m n : ℕ), m.Coprime n → modularFormAn (n * m) f = modularFormAn n f * modularFormAn m f) ∧
  (∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) ≠ 0 →
    modularFormAn (p ^ r) f =
      modularFormAn p f * modularFormAn (p ^ (r - 1)) f - p ^ (k - 1) * modularFormAn (p ^ (r - 2)) f) ∧
  ∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) = 0 → modularFormAn (p ^ r) f = (modularFormAn p f) ^ r

/-- The modularity of one elliptic curve, in the form of formal-conjectures. -/
def modularityConjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ (N : ℕ+) (f : CuspForm (Gamma0 N) 2), IsNormalisedEigenform f ∧
    ∀ (p : ℕ), p.Prime → (N : ZMod p) ≠ 0 → modularFormAn p f = WeierstrassCurve.ap E p

/-- The theorem `modularity_conjecture` of formal-conjectures, as a `Prop`. -/
def modularity_conjecture : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], modularityConjecture E

end ModularityConjecture

namespace SatoTateConjecture

open Real

/-- The thirteen rational CM $j$-invariants. -/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736,
    -12288000, 16581375, -884736000, -147197952000, -262537412640768000}

/-- Complex multiplication by the $j$-invariant. -/
def HasCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ cmJInvariants

/-- The normalized coefficient $a_p(E)/(2\sqrt{p})$. -/
noncomputable def normalisedAp (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : ℝ :=
  (ModularityConjecture.WeierstrassCurve.ap E p : ℝ) / (2 * √p)

/-- The cumulative distribution function of the Sato-Tate measure. -/
noncomputable def satoTateCDF (t : ℝ) : ℝ :=
  (t * √(1 - t ^ 2) + arcsin t) / π + 1 / 2

/-- The mass of $[a, b]$ for the Sato-Tate distribution. -/
noncomputable def satoTateMeasure (a b : ℝ) : ℝ :=
  satoTateCDF b - satoTateCDF a

/-- The number of primes $p < N$ with normalized coefficient in $[a, b]$. -/
noncomputable def primeCountInInterval (E : WeierstrassCurve ℚ) [E.IsElliptic] (a b : ℝ) (N : ℕ) : ℕ :=
  ((Nat.primesBelow N).filter (fun p : ℕ ↦ a ≤ normalisedAp E p ∧ normalisedAp E p ≤ b)).card

/-- The theorem `satoTate_conjecture` of formal-conjectures, as a `Prop`. -/
def satoTate_conjecture : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (_ : ¬ HasCM E) (a b : ℝ) (_ : -1 ≤ a) (_ : a ≤ b) (_ : b ≤ 1),
    Filter.Tendsto
      (fun N : ℕ ↦ (primeCountInInterval E a b N : ℝ) / ((Nat.primesBelow N).card : ℝ))
      Filter.atTop (nhds (satoTateMeasure a b))

end SatoTateConjecture

namespace RamanujanTau

open PowerSeries PowerSeries.WithPiTopology

/-- The discriminant form as a power series. -/
noncomputable def Δ : PowerSeries ℤ := X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24

/-- The Ramanujan $\tau$-function. -/
noncomputable def τ (n : ℕ) : ℤ := PowerSeries.coeff n Δ

/-- The theorem `ramanujan_petersson` of formal-conjectures, as a `Prop`. -/
def ramanujan_petersson : Prop :=
  ∀ p : ℕ, Prime p → abs (τ p) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)

end RamanujanTau

namespace HasseWeil

/-- The $L$-series of `E` has the analytic continuation `L`. -/
def HasAnalyticContinuation {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    (L : ℂ → ℂ) : Prop :=
  (∀ z, AnalyticAt ℂ L z) ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The theorem `exists_hasAnalyticContinuation_rat` of formal-conjectures, as a `Prop`. -/
def exists_hasAnalyticContinuation_rat : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L

end HasseWeil

end Langlands.Ported.FormalConjectures
