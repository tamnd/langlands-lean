/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.PadicGalois

/-!
# The shape of the Breuil-Mézard conjecture for GL(2) over the p-adic numbers

Let $p$ be a prime, let $k$ be a finite field of characteristic $p$ and let $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$ be continuous. Let $\lambda = (\lambda_1 > \lambda_2)$ be a Hodge-Tate type and let $\tau$ be an inertial type, a representation of the inertia group $I_{\mathbb{Q}_p}$ with open kernel that extends to the Weil group. Kisin constructs the quotient $R^\square(\lambda, \tau, \bar\rho)$ of the universal framed deformation ring of $\bar\rho$ whose $\overline{\mathbb{Q}}_p$-points are the potentially semistable lifts of Hodge-Tate type $\lambda$ and inertial type $\tau$. Henniart attaches to $\tau$ a smooth irreducible representation $\sigma(\tau)$ of $GL_2(\mathbb{Z}_p)$, and $\sigma(\lambda, \tau) = \mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} \overline{\mathbb{Q}}_p^2 \otimes \det^{\lambda_2} \otimes \sigma(\tau)$. Let $n_{a,b}(\lambda, \tau)$ be the multiplicity of the Serre weight $\sigma_{a,b} = \mathrm{Sym}^a \otimes \det^b$ (`Langlands.serreWeight`) in the semisimplified reduction of a lattice in $\sigma(\lambda, \tau)$.

The conjecture of Breuil and Mézard says that there are integers $\mu_{a,b}(\bar\rho) \ge 0$, which do not depend on $\lambda$ and $\tau$, such that the Hilbert-Samuel multiplicity of the special fiber is
$$e(R^\square(\lambda, \tau, \bar\rho) \otimes k) = \sum_{0 \le a \le p - 1,\ 0 \le b \le p - 2} n_{a,b}(\lambda, \tau)\, \mu_{a,b}(\bar\rho).$$
Kisin proved it for most $\bar\rho$ with $p > 2$, with the $p$-adic local Langlands correspondence of Colmez and with global methods. Paškūnas gave a local proof, and Hu and Tan completed the remaining cases. There is a variant with potentially crystalline lifts and the representation $\sigma^{cr}(\tau)$.

## Main definitions

* `Langlands.HodgeTateType`: the pairs $(\lambda_1, \lambda_2)$ of integers with $\lambda_1 > \lambda_2$.
* `Langlands.BreuilMezardData`: the interface with the objects that the conjecture uses and that the project does not define: the inertial types, the multiplicities $e(R^\square(\lambda, \tau, \bar\rho) \otimes k)$ and the multiplicities $n_{a,b}(\lambda, \tau)$.
* `Langlands.BreuilMezardGL2Qp`: the shape of the conjecture for this interface.

## The missing vocabulary

The statement needs these notions, which are not in Mathlib or in the project:
* the universal framed deformation ring $R^\square(\bar\rho)$, a complete noetherian local ring that pro-represents the functor `Langlands.FramedLift` on Artinian local rings with residue field $k$;
* the potentially semistable lifts of a given Hodge-Tate type and inertial type, which need the rings of Fontaine, and the quotient $R^\square(\lambda, \tau, \bar\rho)$ of Kisin;
* the Hilbert-Samuel multiplicity of a noetherian local ring;
* the inertial types and the representations $\sigma(\tau)$ of Henniart, with the reduction of a lattice and its semisimplification.

These are the fields of `BreuilMezardData`. The structure is only an interface. It does not construct the fields, and the conditions that make them correct are not in it. Thus `BreuilMezardGL2Qp` is a shape and not a statement. It is true for some choices of the fields, for example for zero multiplicities, so it has no mathematical content until the fields are defined. The specification of the project counts it as a shape and not as a G1 statement.

## References

* C. Breuil and A. Mézard, Multiplicités modulaires et représentations de GL2(Zp) et de Gal(Q̄p/Qp) en l = p, Duke Math. J. 115 (2002).
* M. Kisin, The Fontaine-Mazur conjecture for GL2, J. Amer. Math. Soc. 22 (2009).
* M. Kisin, Potentially semi-stable deformation rings, J. Amer. Math. Soc. 21 (2008).
* V. Paškūnas, On the Breuil-Mézard conjecture, Duke Math. J. 164 (2015).
* Y. Hu and F. Tan, The Breuil-Mézard conjecture for non-scalar split residually reducible representations, Ann. Sci. ENS 48 (2015).
* G. Henniart, Sur l'unicité des types pour GL2, appendix to Breuil and Mézard (2002).
-/

namespace Langlands

/-- A Hodge-Tate type for $GL_2$: a pair $(\lambda_1, \lambda_2)$ of integers with $\lambda_1 > \lambda_2$, the two distinct Hodge-Tate weights. -/
def HodgeTateType : Type :=
  {w : ℤ × ℤ // w.2 < w.1}

/-- The interface for the conjecture of Breuil and Mézard for a residual representation $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$. The representation is data. The inertial types and the two families of multiplicities are fields, since the project does not define them. The interface does not construct them, and the conditions that make them correct are not in it. -/
structure BreuilMezardData (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    where
  /-- The residual representation $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$. -/
  ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k
  /-- The residual representation is continuous: its kernel is open. -/
  isOpen_ker : IsOpen (ρbar.ker : Set (Field.absoluteGaloisGroup ℚ_[p]))
  /-- The inertial types $\tau$: the representations $I_{\mathbb{Q}_p} \to GL_2(\overline{\mathbb{Q}}_p)$ with open kernel that extend to the Weil group of $\mathbb{Q}_p$, up to isomorphism. -/
  InertialType : Type
  /-- The Hilbert-Samuel multiplicity $e(R^\square(\lambda, \tau, \bar\rho) \otimes k)$ of the special fiber of the potentially semistable framed deformation ring of Kisin. It is zero when the ring is zero. -/
  deformationMultiplicity : HodgeTateType → InertialType → ℕ
  /-- The multiplicity $n_{a,b}(\lambda, \tau)$ of the Serre weight $\mathrm{Sym}^a \otimes \det^b$ in the semisimplified reduction of $\sigma(\lambda, \tau) = \mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} \otimes \det^{\lambda_2} \otimes \sigma(\tau)$, where $\sigma(\tau)$ is the type of Henniart. -/
  typeMultiplicity : HodgeTateType → InertialType → ℕ → ℕ → ℕ

/-- **The shape of the Breuil-Mézard conjecture for $GL_2(\mathbb{Q}_p)$** (Breuil and Mézard; proved by Kisin, Paškūnas, Hu and Tan for $p > 2$). There are integers $\mu_{a,b} \ge 0$ for the Serre weights $\mathrm{Sym}^a \otimes \det^b$ with $0 \le a \le p - 1$ and $0 \le b \le p - 2$, that do not depend on the Hodge-Tate type $\lambda$ or on the inertial type $\tau$, such that $e(R^\square(\lambda, \tau, \bar\rho) \otimes k) = \sum_{a,b} n_{a,b}(\lambda, \tau)\, \mu_{a,b}$ for each $\lambda$ and $\tau$.

This is a shape, not a statement: the deformation rings, their multiplicities and the types are fields of `BreuilMezardData`. -/
def BreuilMezardGL2Qp {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
    (D : BreuilMezardData p k) : Prop :=
  ∃ μ : ℕ → ℕ → ℕ, ∀ (hw : HodgeTateType) (τ : D.InertialType),
    D.deformationMultiplicity hw τ =
      ∑ a ∈ Finset.range p, ∑ b ∈ Finset.range (p - 1), D.typeMultiplicity hw τ a b * μ a b

end Langlands
