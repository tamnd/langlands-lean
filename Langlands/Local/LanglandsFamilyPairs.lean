/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Statements.LocalLanglands
import Langlands.Local.GL1LFactor
import Langlands.Local.GL1Epsilon
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The L-factors and ε-factors of pairs in the local Langlands correspondence

Let $K$ be a nonarchimedean local field with residue field of size $q$. The local Langlands correspondence for $GL_n$ is characterized by the L-factors and ε-factors of pairs (Henniart). This file states these conditions. On the Galois side it defines the tensor product $\rho \otimes \rho'$ of Weil-Deligne representations, whose L-factor is `Langlands.WeilDeligneRep.lFactor`, and it takes the ε-factor as a parameter with the properties of Deligne's characterization. On the representation side it defines the ψ-Whittaker model, the generic representations, the zeta integrals of Jacquet, Piatetski-Shapiro and Shalika, the Rankin-Selberg L-factor and the Rankin-Selberg ε-factor with the local functional equation. Then it adds the structure `IsLanglandsFamilyPairs` above `Langlands.IsLanglandsFamily`, and the statement `LocalLanglandsGLFull n`. For $m = m' = 1$ it proves that the factors of pairs are Tate's factors of the product $\chi \chi'$.

## Main definitions

* `Langlands.kronMat`: the Kronecker product $A \otimes B$ of square matrices, indexed by $\mathrm{Fin}(m m')$.
* `Langlands.WeilDeligneRep.tensor`: the tensor product $\rho \otimes \rho' = (r \otimes r', N \otimes 1 + 1 \otimes N')$ of Weil-Deligne representations of dimensions $m$ and $m'$.
* `Langlands.WeilDeligneRep.forgetN`: the Weil-Deligne representation $(r, 0)$.
* `Langlands.WDEpsilonFn`, `Langlands.IsWDEpsilon`: the Galois ε-factor as a parameter, with iso invariance, monomial form, Tate's factor in dimension one and Deligne's formula for the monodromy.
* `Langlands.IsTateEpsilon`: $e$ is the factor in Tate's local functional equation for $\chi$.
* `Langlands.IsWhittakerFunctional`, `Langlands.IsGeneric`, `Langlands.whittakerModel`: ψ-Whittaker functionals, ψ-generic representations and the ψ-Whittaker model.
* `Langlands.quotIntegral`: the integral over $N_m \backslash GL_m(K)$, in the coordinates $\bar{u} \, \mathrm{diag}(t)$.
* `Langlands.rsZeta`: the zeta integral $\Psi(s, W, W'; j)$ for $m < n$.
* `Langlands.rsZetaPhi`: the zeta integral $\Psi(s, W, W', \Phi)$ for $m = n$.
* `Langlands.IsRSLFactor`: $L$ is the Rankin-Selberg L-factor $L(s, \pi \times \pi')$.
* `Langlands.rsFEPairs`: the pairs of zeta integrals in the local functional equation.
* `Langlands.IsRSEpsilonFactor`: $\varepsilon$ is the Rankin-Selberg ε-factor $\varepsilon(s, \pi \times \pi', \psi)$.
* `Langlands.IsLanglandsFamilyPairs`: the conditions of `IsLanglandsFamily`, and the equality of the L-factors and ε-factors of pairs for generic representations.
* `Langlands.LocalLanglandsGLFull`: the existence of a Galois ε-factor and of a family with the conditions of `IsLanglandsFamilyPairs`.

## Main results

* `Langlands.isSemisimple_kronMat`: the Kronecker product of semisimple matrices is semisimple.
* `Langlands.IsLanglandsFamilyPairs.isLanglandsFamily`: `IsLanglandsFamilyPairs` implies `IsLanglandsFamily`.
* `Langlands.LocalLanglandsGLFull.localLanglandsGL`: `LocalLanglandsGLFull n` implies `LocalLanglandsGL n`.
* `Langlands.rsZetaPhi_one`: for $GL_1$ the zeta integral of pairs is $a b Z(\Phi, \chi \chi', s)$.
* `Langlands.isRSLFactor_one`: for $GL_1$ the Rankin-Selberg L-factor of $\chi$ and $\chi'$ is $L(s, \chi \chi')$.
* `Langlands.tensor_wdOfChar`, `Langlands.lFactor_tensor_wdOfChar`: the tensor product of the Weil-Deligne representations of $\chi$ and $\chi'$ is the Weil-Deligne representation of $\chi \chi'$, with L-factor $L(s, \chi \chi')$.
* `Langlands.isRSLFactor_tensor_wdOfChar`: condition 5 for $m = m' = 1$.
* `Langlands.mem_rsFEPairs_one`, `Langlands.zeta_pair_mem_rsFEPairs_one`: for $GL_1$ the pairs of the functional equation of pairs are the pairs $(Z(\varphi, \chi \chi', s), Z(\hat{\varphi}, (\chi \chi')^{-1}, s))$ of Tate's functional equation, up to a constant.
* `Langlands.isTateEpsilon_tensor`: the Galois ε-factor of the tensor product of the Weil-Deligne representations of $\chi$ and $\chi'$ is the factor of Tate's functional equation for $\chi \chi'$.

## Implementation notes

* The Galois ε-factor is a parameter $\varepsilon$ with the conditions of `IsWDEpsilon`. Additivity in exact sequences and inductivity in degree zero are not part of the conditions, because induction of Weil-Deligne representations is not in the library. Thus the conditions do not determine $\varepsilon$ in dimension $m \ge 2$. In dimension one, `IsTateEpsilon` is the property that `Langlands.LocalGL1.localFunctionalEquation_tateEpsilon` in `Langlands.Local.LanglandsFamilyEps` proves for `Langlands.LocalGL1.tateEpsilon`. That module is not built in the main checkout, so this file does not import it.
* The conditions on pairs are stated only for generic representations: $\pi$ is ψ-generic and $\pi'$ is $\psi^{-1}$-generic. The reduction of the factors of non-generic representations to generic ones, by the Langlands classification and the Bernstein-Zelevinsky theory, is not formalized.
* The zeta integrals are Bochner integrals, so they are $0$ when the integrand is not integrable. The conditions use the zeta integrals only for $\mathrm{Re}(s)$ large, where they converge. The functional equation is an identity of the Laurent polynomials $\Psi / L$ in $q^{-s}$, which gives the analytic continuation.
* The integral over $N_m \backslash GL_m(K)$ uses the open subset $\bar{N}_m T_m$ of the quotient, with the measure $d\bar{u} \prod_i |t_i|^{-1} dt_i$. This is a right invariant measure on the quotient, up to a constant.
* The ε-factor of pairs uses the self dual Haar measure for $\psi$. The L-factor does not depend on the Haar measure.

## What is still open

* The convergence of the zeta integrals of Jacquet, Piatetski-Shapiro and Shalika for $\mathrm{Re}(s)$ large, and the existence of $L(s, \pi \times \pi')$ and $\varepsilon(s, \pi \times \pi', \psi)$ for $n \ge 2$.
* The uniqueness of the Galois ε-factor. The ε-factor condition for $GL_1$ and the uniqueness of the generator in `IsZetaGenerator` are proved in `Langlands.Local.LanglandsFamilyPairsEps`.
* The factors of pairs for non-generic representations.

## References

* H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), 367 to 464.
* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in Modular functions of one variable II, Lecture Notes in Math. 349, Springer 1973.
* J. Tate, *Number theoretic background*, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979.
* G. Henniart, *Une caractérisation de la correspondance de Langlands locale pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587 to 602.
-/

namespace Langlands

universe u

open Matrix MeasureTheory
open scoped Kronecker

section Kronecker

variable {m m' : ℕ}

/-- The Kronecker product $A \otimes B$ of square matrices of sizes $m$ and $m'$, with the indices $\mathrm{Fin}\, m \times \mathrm{Fin}\, m'$ identified with $\mathrm{Fin}(m m')$ by `finProdFinEquiv`. -/
noncomputable def kronMat (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    Matrix (Fin (m * m')) (Fin (m * m')) ℂ :=
  reindexAlgEquiv ℂ ℂ finProdFinEquiv (A ⊗ₖ B)

/-- The Kronecker product is multiplicative: $(A A') \otimes (B B') = (A \otimes B)(A' \otimes B')$. -/
theorem kronMat_mul (A A' : Matrix (Fin m) (Fin m) ℂ) (B B' : Matrix (Fin m') (Fin m') ℂ) :
    kronMat (A * A') (B * B') = kronMat A B * kronMat A' B' := by
  rw [kronMat, mul_kronecker_mul, map_mul]
  rfl

/-- The Kronecker product of two identity matrices is the identity matrix. -/
theorem kronMat_one : kronMat (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m') (Fin m') ℂ) = 1 := by
  rw [kronMat, one_kronecker_one, map_one]

/-- The Kronecker product is additive in the first factor. -/
theorem kronMat_add_left (A A' : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat (A + A') B = kronMat A B + kronMat A' B := by
  rw [kronMat, add_kronecker, map_add]
  rfl

/-- The Kronecker product is additive in the second factor. -/
theorem kronMat_add_right (A : Matrix (Fin m) (Fin m) ℂ) (B B' : Matrix (Fin m') (Fin m') ℂ) :
    kronMat A (B + B') = kronMat A B + kronMat A B' := by
  rw [kronMat, kronecker_add, map_add]
  rfl

/-- The Kronecker product is linear in the first factor. -/
theorem kronMat_smul_left (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat (c • A) B = c • kronMat A B := by
  rw [kronMat, smul_kronecker, map_smul]
  rfl

/-- The Kronecker product with a zero first factor is zero. -/
theorem kronMat_zero_left (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat (0 : Matrix (Fin m) (Fin m) ℂ) B = 0 := by
  rw [kronMat, zero_kronecker, map_zero]

/-- The matrices $A \otimes 1$ and $1 \otimes B$ commute. -/
theorem kronMat_mul_comm (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat A 1 * kronMat 1 B = kronMat 1 B * kronMat A 1 := by
  rw [← kronMat_mul, ← kronMat_mul, mul_one, one_mul, one_mul, mul_one]

/-- The Kronecker product as a monoid homomorphism $M_m(\mathbb{C}) \times M_{m'}(\mathbb{C}) \to M_{m m'}(\mathbb{C})$. -/
noncomputable def kronHom (m m' : ℕ) :
    Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m') (Fin m') ℂ →* Matrix (Fin (m * m')) (Fin (m * m')) ℂ where
  toFun p := kronMat p.1 p.2
  map_one' := kronMat_one
  map_mul' _ _ := kronMat_mul _ _ _ _

/-- The algebra homomorphism $A \mapsto A \otimes 1$. -/
noncomputable def kronLeft (m m' : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Fin (m * m')) (Fin (m * m')) ℂ where
  toFun A := kronMat A 1
  map_one' := kronMat_one
  map_mul' A B := by rw [← kronMat_mul, mul_one]
  map_zero' := kronMat_zero_left _
  map_add' A B := kronMat_add_left _ _ _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, kronMat_smul_left, kronMat_one]

/-- The Kronecker product is linear in the second factor. -/
theorem kronMat_smul_right (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat A (c • B) = c • kronMat A B := by
  rw [kronMat, kronecker_smul, map_smul]
  rfl

/-- The Kronecker product with a zero second factor is zero. -/
theorem kronMat_zero_right (A : Matrix (Fin m) (Fin m) ℂ) :
    kronMat A (0 : Matrix (Fin m') (Fin m') ℂ) = 0 := by
  rw [kronMat, kronecker_zero, map_zero]

/-- The factorization $A \otimes B = (A \otimes 1)(1 \otimes B)$. -/
theorem kronMat_eq_mul (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    kronMat A B = kronMat A 1 * kronMat 1 B := by
  rw [← kronMat_mul, mul_one, one_mul]

/-- The algebra homomorphism $B \mapsto 1 \otimes B$. -/
noncomputable def kronRight (m m' : ℕ) :
    Matrix (Fin m') (Fin m') ℂ →ₐ[ℂ] Matrix (Fin (m * m')) (Fin (m * m')) ℂ where
  toFun B := kronMat 1 B
  map_one' := kronMat_one
  map_mul' A B := by rw [← kronMat_mul, mul_one]
  map_zero' := kronMat_zero_right _
  map_add' A B := kronMat_add_right _ _ _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, kronMat_smul_right, kronMat_one]

/-- An algebra homomorphism of matrix algebras sends a semisimple matrix to a semisimple matrix. The minimal polynomial of $A$ is squarefree and it annihilates $\varphi(A)$. -/
theorem isSemisimple_toLin'_algHom {k l : ℕ}
    (φ : Matrix (Fin k) (Fin k) ℂ →ₐ[ℂ] Matrix (Fin l) (Fin l) ℂ) {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    Module.End.IsSemisimple (Matrix.toLin' (φ A)) := by
  set p := minpoly ℂ (Matrix.toLin' A)
  have hp : Squarefree p := hA.minpoly_squarefree
  have h0 : Polynomial.aeval (Matrix.toLin' A) p = 0 := minpoly.aeval ℂ _
  have h1 : Polynomial.aeval A p = 0 := by
    have : Polynomial.aeval (Matrix.toLinAlgEquiv' A) p = Matrix.toLinAlgEquiv' (Polynomial.aeval A p) :=
      Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _) A p
    rw [← map_zero (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _)] at h0
    exact (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _).injective (this.symm.trans h0)
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp ?_
  have e1 : Polynomial.aeval (Matrix.toLinAlgEquiv' (φ A)) p =
      Matrix.toLinAlgEquiv' (φ (Polynomial.aeval A p)) := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply]
  exact e1.trans (by rw [h1, map_zero, map_zero])

/-- The Kronecker product of two semisimple matrices is semisimple, because $A \otimes 1$ and $1 \otimes B$ are semisimple and commute. -/
theorem isSemisimple_kronMat {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin m') (Fin m') ℂ}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) (hB : Module.End.IsSemisimple (Matrix.toLin' B)) :
    Module.End.IsSemisimple (Matrix.toLin' (kronMat A B)) := by
  have e : Matrix.toLin' (kronMat A B) = Matrix.toLin' (kronMat A 1) * Matrix.toLin' (kronMat 1 B) := by
    rw [kronMat_eq_mul]
    exact map_mul (Matrix.toLinAlgEquiv' : Matrix (Fin (m * m')) (Fin (m * m')) ℂ ≃ₐ[ℂ] _) _ _
  rw [e]
  refine Module.End.IsSemisimple.mul_of_commute ?_ (isSemisimple_toLin'_algHom (kronLeft m m') hA)
    (isSemisimple_toLin'_algHom (kronRight m m') hB)
  exact (show Commute (kronMat A 1) (kronMat 1 B) from kronMat_mul_comm A B).map
    (Matrix.toLinAlgEquiv' : Matrix (Fin (m * m')) (Fin (m * m')) ℂ ≃ₐ[ℂ] _)

end Kronecker

namespace WeilDeligneRep

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {m m' : ℕ}

/-- The homomorphism $w \mapsto r(w) \otimes r'(w)$ from $W_K$ to $GL_{m m'}(\mathbb{C})$. -/
noncomputable def tensorR (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    WeilGroup K →* GL (Fin (m * m')) ℂ :=
  (Units.map (kronHom m m')).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp (ρ.r.prod ρ'.r))

/-- The matrix of $(r \otimes r')(w)$ is $r(w) \otimes r'(w)$. -/
theorem tensorR_apply (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    (tensorR ρ ρ' w : Matrix (Fin (m * m')) (Fin (m * m')) ℂ) = kronMat (ρ.r w : Matrix _ _ ℂ) (ρ'.r w) :=
  rfl

/-- The inverse of $(r \otimes r')(w)$ is $r(w)^{-1} \otimes r'(w)^{-1}$. -/
theorem tensorR_inv_apply (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    (((tensorR ρ ρ' w)⁻¹ : GL (Fin (m * m')) ℂ) : Matrix (Fin (m * m')) (Fin (m * m')) ℂ) =
      kronMat (((ρ.r w)⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ) (((ρ'.r w)⁻¹ : GL (Fin m') ℂ) : Matrix _ _ ℂ) :=
  rfl

/-- **The tensor product of Weil-Deligne representations.** For $\rho = (r, N)$ of dimension $m$ and $\rho' = (r', N')$ of dimension $m'$, the tensor product is $\rho \otimes \rho' = (r \otimes r', N \otimes 1 + 1 \otimes N')$ of dimension $m m'$. The monodromy operator is nilpotent because $N \otimes 1$ and $1 \otimes N'$ are nilpotent and commute. -/
noncomputable def tensor (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    WeilDeligneRep K (m * m') where
  r := tensorR ρ ρ'
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := ρ.r.ker ⊓ ρ'.r.ker) (fun w hw => ?_)
      (ρ.isOpen_ker.inter ρ'.isOpen_ker)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hw
    rw [MonoidHom.mem_ker]
    ext1
    rw [tensorR_apply, hw.1, hw.2, Units.val_one, Units.val_one, Units.val_one, kronMat_one]
  N := kronMat ρ.N 1 + kronMat 1 ρ'.N
  isNilpotent := by
    have hc : Commute (kronMat ρ.N (1 : Matrix (Fin m') (Fin m') ℂ)) (kronMat 1 ρ'.N) :=
      kronMat_mul_comm _ _
    exact hc.isNilpotent_add (ρ.isNilpotent.map (kronLeft m m')) (ρ'.isNilpotent.map (kronRight m m'))
  conj w := by
    rw [tensorR_apply, tensorR_inv_apply, mul_add, add_mul, ← kronMat_mul, ← kronMat_mul,
      ← kronMat_mul, ← kronMat_mul, ρ.conj w, ρ'.conj w]
    simp only [mul_one, Units.mul_inv]
    rw [kronMat_smul_left, kronMat_smul_right, smul_add]
  semisimple w := by
    rw [tensorR_apply]
    exact isSemisimple_kronMat (ρ.semisimple w) (ρ'.semisimple w)

/-- The representation of $W_K$ in $\rho \otimes \rho'$ is $w \mapsto r(w) \otimes r'(w)$. -/
theorem tensor_r (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    ((ρ.tensor ρ').r w : Matrix (Fin (m * m')) (Fin (m * m')) ℂ) =
      kronMat (ρ.r w : Matrix _ _ ℂ) (ρ'.r w) :=
  rfl

/-- The monodromy operator of $\rho \otimes \rho'$ is $N \otimes 1 + 1 \otimes N'$. -/
theorem tensor_N (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    (ρ.tensor ρ').N = kronMat ρ.N 1 + kronMat 1 ρ'.N :=
  rfl

/-- The Weil-Deligne representation $(r, 0)$ of a Weil-Deligne representation $(r, N)$. Its L-space is the space $V^I$ of the inertia invariants. -/
noncomputable def forgetN (ρ : WeilDeligneRep K m) : WeilDeligneRep K m where
  r := ρ.r
  isOpen_ker := ρ.isOpen_ker
  N := 0
  isNilpotent := IsNilpotent.zero
  conj w := by simp
  semisimple := ρ.semisimple

end WeilDeligneRep

section Epsilon

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The type of a candidate ε-factor on the Galois side: a function $(\mu, m, \rho, \psi, s) \mapsto \varepsilon(s, \rho, \psi, \mu)$ of a measure $\mu$ on $K$, a Weil-Deligne representation $\rho$ of dimension $m$, an additive character $\psi$ and $s \in \mathbb{C}$. -/
def WDEpsilonFn [MeasurableSpace K] : Type u :=
  Measure K → ∀ m : ℕ, WeilDeligneRep K m → AddChar K ℂ → ℂ → ℂ

/-- The function $e$ is the factor in Tate's local functional equation for the character $\chi$, the measure $\mu$ and the additive character $\psi$: for each locally constant $\varphi$ with compact support and each $s$ in the strip $|\chi(\varpi) q^{-s}| < 1$, $|\chi(\varpi)^{-1} q^{-(1 - s)}| < 1$, $$Z(\hat{\varphi}, \chi^{-1}, 1 - s) L(1 - s, \chi^{-1})^{-1} = e(s) Z(\varphi, \chi, s) L(s, \chi)^{-1}.$$ The file `Langlands/Local/LanglandsFamilyEps.lean` proves this for `Langlands.LocalGL1.tateEpsilon` as `localFunctionalEquation_tateEpsilon`. -/
def IsTateEpsilon [MeasurableSpace K] (μ : Measure K) (χ : Kˣ →* ℂˣ) (ψ : AddChar K ℂ) (e : ℂ → ℂ) :
    Prop :=
  ∀ φ : K → ℂ, IsLocallyConstant φ → HasCompactSupport φ → ∀ s : ℂ,
    ‖(χ (LocalGL1.unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 →
    ‖(χ (LocalGL1.unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 →
      LocalGL1.zeta χ⁻¹ μ (LocalGL1.fourier μ ψ φ) (1 - s) * (LocalGL1.charLFactor K (LocalGL1.unif K) χ⁻¹ (1 - s))⁻¹ =
        e s * (LocalGL1.zeta χ μ φ s * (LocalGL1.charLFactor K (LocalGL1.unif K) χ s)⁻¹)

/-- **The ε-factor on the Galois side, as a parameter.** The function $\varepsilon$ has the following standard properties of the ε-factor of Deligne and Langlands: it depends only on the isomorphism class of $\rho$; it is a monomial $c q^{-k s}$ with $c \neq 0$; in dimension one it is Tate's factor of the character $\det r \circ \mathrm{art}_K$, for each Haar measure and each nontrivial $\psi$; and it satisfies Deligne's formula $\varepsilon(s, \rho, \psi) \det(-q^{-s} \Phi \mid V_N^I) = \varepsilon(s, (r, 0), \psi) \det(-q^{-s} \Phi \mid V^I)$ for the monodromy. The additivity in exact sequences and the inductivity in degree zero are not part of the conditions, so these conditions do not determine $\varepsilon$ in dimension $m \ge 2$. -/
structure IsWDEpsilon [MeasurableSpace K] (art : Kˣ ≃ₜ* WeilGroup.Ab K) (ε : WDEpsilonFn K) : Prop where
  iso : ∀ μ m (ρ ρ' : WeilDeligneRep K m), WDIso.mk ρ = WDIso.mk ρ' → ∀ ψ s, ε μ m ρ ψ s = ε μ m ρ' ψ s
  monomial : ∀ μ m (ρ : WeilDeligneRep K m) ψ, ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, ∀ s,
    ε μ m ρ ψ s = c * ((residueCard K : ℂ) ^ (-s)) ^ k
  dimOne : ∀ (μ : Measure K) [μ.IsAddHaarMeasure] (ρ : WeilDeligneRep K 1) (ψ : AddChar K ℂ) (k : ℤ),
    LocalGL1.IsConductor ψ k → IsTateEpsilon K μ (LocalGL1.charOfWD K art ρ) ψ (ε μ 1 ρ ψ)
  monodromy : ∀ μ m (ρ : WeilDeligneRep K m) ψ s,
    ε μ m ρ ψ s * LinearMap.det (-((residueCard K : ℂ) ^ (-s)) • ρ.frobOnLSpace) =
      ε μ m ρ.forgetN ψ s * LinearMap.det (-((residueCard K : ℂ) ^ (-s)) • ρ.forgetN.frobOnLSpace)

end Epsilon

section Whittaker

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n m : ℕ}

/-- The element $g$ of $GL_n(K)$ is upper triangular with $1$ on the diagonal. -/
def IsUpperUnipotent (g : GL (Fin n) K) : Prop :=
  (∀ i, (g : Matrix (Fin n) (Fin n) K) i i = 1) ∧ ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) K) i j = 0

/-- The character $\psi_N(u) = \psi(u_{1, 2} + u_{2, 3} + \dots + u_{n - 1, n})$ of the upper unipotent subgroup $N_n$, evaluated at $g$. -/
def unipChar (ψ : AddChar K ℂ) (g : GL (Fin n) K) : ℂ :=
  ψ (∑ i : Fin n, if h : i.val + 1 < n then (g : Matrix (Fin n) (Fin n) K) i ⟨i.val + 1, h⟩ else 0)

/-- The linear form $\lambda$ on $\pi$ is a ψ-Whittaker functional: $\lambda(\pi(u) v) = \psi_N(u) \lambda(v)$ for each $u \in N_n$ and each $v$. -/
def IsWhittakerFunctional (π : SmoothRep (GL (Fin n) K)) (ψ : AddChar K ℂ) (l : Module.Dual ℂ π.V) :
    Prop :=
  ∀ u, IsUpperUnipotent u → ∀ v, l (π.ρ u v) = unipChar ψ u * l v

/-- The representation $\pi$ is ψ-generic: it has a nonzero ψ-Whittaker functional. -/
def IsGeneric (π : SmoothRep (GL (Fin n) K)) (ψ : AddChar K ℂ) : Prop :=
  ∃ l : Module.Dual ℂ π.V, l ≠ 0 ∧ IsWhittakerFunctional π ψ l

/-- The ψ-Whittaker functions of $\pi$: the functions $W(g) = \lambda(\pi(g) v)$ for a ψ-Whittaker functional $\lambda$ and a vector $v$. For an irreducible generic $\pi$ the Whittaker functional is unique up to a scalar (Gelfand and Kazhdan, Shalika), so this set is the Whittaker model $\mathcal{W}(\pi, \psi)$. -/
def whittakerModel (π : SmoothRep (GL (Fin n) K)) (ψ : AddChar K ℂ) : Set (GL (Fin n) K → ℂ) :=
  {W | ∃ l, IsWhittakerFunctional π ψ l ∧ ∃ v, W = π.coeff v l}

open scoped Classical in
/-- The extension of a function $W$ on $GL_n(K)$ to $M_n(K)$ by $0$ off $GL_n(K)$. -/
noncomputable def extGL (W : GL (Fin n) K → ℂ) (x : Matrix (Fin n) (Fin n) K) : ℂ :=
  if h : IsUnit x.det then W (Matrix.nonsingInvUnit x h) else 0

/-- The index set $\{(i, j) : j < i\}$ of the entries below the diagonal of an $m \times m$ matrix. -/
def StrictLower (m : ℕ) : Type :=
  {p : Fin m × Fin m // p.2 < p.1}

/-- The index set of the entries below the diagonal is finite. -/
instance (m : ℕ) : Fintype (StrictLower m) :=
  inferInstanceAs (Fintype {p : Fin m × Fin m // p.2 < p.1})

open scoped Classical in
/-- The lower unipotent matrix $\bar{u}$ with entries $u_{i j}$ below the diagonal. -/
def lowerUnip (u : StrictLower m → K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => if i = j then 1 else if h : j < i then u ⟨(i, j), h⟩ else 0

variable [MeasurableSpace K] (μ : Measure K) [SigmaFinite μ]

/-- The integral over $N_m \backslash GL_m(K)$ of a function $F$ that is invariant on the left under $N_m$, in coordinates: $$\int_{N_m \backslash GL_m(K)} F(g) \, dg = \int_{\bar{N}_m} \int_{(K^\times)^m} F(\bar{u} \, \mathrm{diag}(t)) \prod_i |t_i|^{-1} \, dt \, d\bar{u}.$$ The product of the lower unipotent subgroup and the diagonal torus is open in $N_m \backslash GL_m(K)$ with a complement of measure zero, and the formula gives a right invariant measure on the quotient, up to a constant. -/
noncomputable def quotIntegral (F : Matrix (Fin m) (Fin m) K → ℂ) : ℂ :=
  ∫ u : StrictLower m → K, ∫ t : Fin m → K,
    F (lowerUnip u * Matrix.diagonal t) * ∏ i, ((normAbs K (t i) : ℂ))⁻¹
      ∂(Measure.pi fun _ => μ) ∂(Measure.pi fun _ => μ)

/-- The matrix $\begin{pmatrix} g & 0 & 0 \\ x & 1_j & 0 \\ 0 & 0 & 1_{n - m - j} \end{pmatrix}$ of size $n$ for $g$ of size $m$ and $x$ of size $j \times m$. -/
def embedMat (n : ℕ) {m j : ℕ} (g : Matrix (Fin m) (Fin m) K) (x : Fin j → Fin m → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if hb : b.val < m then
      if ha : a.val < m then g ⟨a.val, ha⟩ ⟨b.val, hb⟩
      else if ha' : a.val - m < j then x ⟨a.val - m, ha'⟩ ⟨b.val, hb⟩ else 0
    else if a = b then 1 else 0

/-- **The zeta integral of Jacquet, Piatetski-Shapiro and Shalika for $m < n$.** For functions $F$ on $M_n(K)$ and $F'$ on $M_m(K)$, $$\Psi(s, F, F'; j) = \int_{N_m \backslash GL_m(K)} \int_{M_{j \times m}(K)} F\begin{pmatrix} g & 0 & 0 \\ x & 1_j & 0 \\ 0 & 0 & 1_{n - m - j} \end{pmatrix} dx \, F'(g) |\det g|^{s - (n - m)/2} \, dg.$$ For $F = W$ and $F' = W'$ in the Whittaker models this is $\Psi(s, W, W'; j)$. -/
noncomputable def rsZeta (F : Matrix (Fin n) (Fin n) K → ℂ) (F' : Matrix (Fin m) (Fin m) K → ℂ)
    (j : ℕ) (s : ℂ) : ℂ :=
  quotIntegral μ fun g =>
    (∫ x : Fin j → Fin m → K, F (embedMat n g x) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) *
      F' g * (normAbs K g.det : ℂ) ^ (s - ((n : ℂ) - m) / 2)

/-- The last row $e_n g$ of a matrix $g$ of size $n$, or $0$ if $n = 0$. -/
def lastRow (g : Matrix (Fin n) (Fin n) K) : Fin n → K :=
  fun k => ∑ i : Fin n, if i.val + 1 = n then g i k else 0

/-- **The zeta integral of Jacquet, Piatetski-Shapiro and Shalika for $m = n$.** $$\Psi(s, F, F', \Phi) = \int_{N_n \backslash GL_n(K)} F(g) F'(g) \Phi(e_n g) |\det g|^s \, dg$$ for a function $\Phi$ on $K^n$. -/
noncomputable def rsZetaPhi (F F' : Matrix (Fin n) (Fin n) K → ℂ) (Φ : (Fin n → K) → ℂ) (s : ℂ) : ℂ :=
  quotIntegral μ fun g => F g * F' g * Φ (lastRow g) * (normAbs K g.det : ℂ) ^ s

/-- The Fourier transform $\hat{\Phi}(y) = \int_{K^n} \Phi(x) \psi(\sum_i x_i y_i) \, dx$ on $K^n$, for the product measure $\mu^n$. -/
noncomputable def fourierPi (ψ : AddChar K ℂ) (Φ : (Fin n → K) → ℂ) (y : Fin n → K) : ℂ :=
  ∫ x, Φ x * ψ (∑ i, x i * y i) ∂(Measure.pi fun _ => μ)

/-- A Schwartz-Bruhat function on $K^n$: a locally constant function with compact support. -/
def IsSchwartzPi (Φ : (Fin n → K) → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ

/-- The antidiagonal permutation matrix $w_n$ of size $n$. -/
def antiDiag (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if a.val + b.val + 1 = n then 1 else 0

/-- The matrix $w_{n, m} = \mathrm{diag}(1_m, w_{n - m})$. -/
def wMat (n m : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if a.val < m then (if a = b then 1 else 0)
    else if m ≤ b.val ∧ a.val + b.val + 1 = n + m then 1 else 0

/-- The function $\tilde{F}(g) = F(w_n \, {}^t g^{-1})$. For a Whittaker function $W \in \mathcal{W}(\pi, \psi)$, $\tilde{W}$ is in $\mathcal{W}(\tilde{\pi}, \psi^{-1})$. -/
noncomputable def tildeF (F : Matrix (Fin n) (Fin n) K → ℂ) (g : Matrix (Fin n) (Fin n) K) : ℂ :=
  F (antiDiag n * (g⁻¹)ᵀ)

/-- The right translate $g \mapsto F(g h)$ of a function $F$ on $M_n(K)$. -/
def rightTrans (F : Matrix (Fin n) (Fin n) K → ℂ) (h g : Matrix (Fin n) (Fin n) K) : ℂ :=
  F (g * h)

open scoped Classical in
/-- The zeta integrals that define $L(s, \pi \times \pi')$: for $m < n$ the integrals $\Psi(s, W, W'; 0)$, and for $m = n$ the integrals $\Psi(s, W, W', \Phi)$ for Schwartz-Bruhat $\Phi$, with $W \in \mathcal{W}(\pi, \psi)$ and $W' \in \mathcal{W}(\pi', \psi^{-1})$. For $m > n$ the set is empty. -/
noncomputable def rsZetaSet (π : SmoothRep (GL (Fin n) K)) (π' : SmoothRep (GL (Fin m) K))
    (ψ : AddChar K ℂ) : Set (ℂ → ℂ) :=
  if m < n then
    {Z | ∃ W ∈ whittakerModel π ψ, ∃ W' ∈ whittakerModel π' ψ⁻¹,
      Z = rsZeta μ (extGL W) (extGL W') 0}
  else
    {Z | ∃ (h : m = n), ∃ W ∈ whittakerModel π ψ, ∃ W' ∈ whittakerModel π' ψ⁻¹,
      ∃ Φ : (Fin n → K) → ℂ, IsSchwartzPi Φ ∧
        Z = rsZetaPhi μ (extGL W) (h ▸ extGL W') Φ}

variable (K) in
/-- $L$ is the generator of the family $Z$ of zeta integrals, in the form of `Langlands.IsGJLFactor`. Write $X = q^{-s}$. Then $L(s) = P(X)^{-1}$ for a polynomial $P$ with $P(0) = 1$; each member of $Z$ is $A(X) X^{-k} L(s)$ for $\mathrm{Re}(s)$ large; and $L(s)$ is a finite sum $\sum_i A_i(X) X^{-k} Z_i(s)$ of members of $Z$ for $\mathrm{Re}(s)$ large. -/
def IsZetaGenerator (Z : Set (ℂ → ℂ)) (L : ℂ → ℂ) : Prop :=
  (∃ P : Polynomial ℂ, P.coeff 0 = 1 ∧ ∀ s, L s = (P.eval ((residueCard K : ℂ) ^ (-s)))⁻¹) ∧
  (∀ f ∈ Z, ∃ (A : Polynomial ℂ) (k : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
      f s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k * L s) ∧
  ∃ (j : ℕ) (f : Fin j → ℂ → ℂ) (A : Fin j → Polynomial ℂ) (k : ℕ) (s₀ : ℝ),
    (∀ i, f i ∈ Z) ∧ ∀ s : ℂ, s₀ < s.re →
      L s = ∑ i, (A i).eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k * f i s

/-- **The Rankin-Selberg L-factor.** $L$ is the L-factor $L(s, \pi \times \pi')$ of Jacquet, Piatetski-Shapiro and Shalika: the generator of the zeta integrals of `rsZetaSet`. It does not depend on the choice of the Haar measure $\mu$. -/
def IsRSLFactor (π : SmoothRep (GL (Fin n) K)) (π' : SmoothRep (GL (Fin m) K)) (ψ : AddChar K ℂ)
    (L : ℂ → ℂ) : Prop :=
  IsZetaGenerator K (rsZetaSet μ π π' ψ) L

open scoped Classical in
/-- The pairs of zeta integrals in the local functional equation of Jacquet, Piatetski-Shapiro and Shalika. For $m < n$ and $0 \le j < n - m$ the pair is $(\Psi(s, W, W'; j), \Psi(s, \rho(w_{n, m}) \tilde{W}, \tilde{W}'; n - m - 1 - j))$. For $m = n$ the pair is $(\Psi(s, W, W', \Phi), \Psi(s, \tilde{W}, \tilde{W}', \hat{\Phi}))$. -/
noncomputable def rsFEPairs (π : SmoothRep (GL (Fin n) K)) (π' : SmoothRep (GL (Fin m) K))
    (ψ : AddChar K ℂ) : Set ((ℂ → ℂ) × (ℂ → ℂ)) :=
  if m < n then
    {p | ∃ W ∈ whittakerModel π ψ, ∃ W' ∈ whittakerModel π' ψ⁻¹, ∃ j < n - m,
      p = (rsZeta μ (extGL W) (extGL W') j,
        rsZeta μ (rightTrans (tildeF (extGL W)) (wMat n m)) (tildeF (extGL W')) (n - m - 1 - j))}
  else
    {p | ∃ (h : m = n), ∃ W ∈ whittakerModel π ψ, ∃ W' ∈ whittakerModel π' ψ⁻¹,
      ∃ Φ : (Fin n → K) → ℂ, IsSchwartzPi Φ ∧
        p = (rsZetaPhi μ (extGL W) (h ▸ extGL W') Φ,
          rsZetaPhi μ (tildeF (extGL W)) (tildeF (h ▸ extGL W')) (fourierPi μ ψ Φ))}

variable (K) in
/-- The function $\varepsilon$ is a monomial $c q^{-k s}$ with $c \neq 0$ and $k \in \mathbb{Z}$. -/
def IsMonomialFactor (ε : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, ∀ s, ε s = c * ((residueCard K : ℂ) ^ (-s)) ^ k

/-- **The Rankin-Selberg ε-factor.** $\varepsilon$ is the ε-factor $\varepsilon(s, \pi \times \pi', \psi)$ of Jacquet, Piatetski-Shapiro and Shalika. Let $L = L(s, \pi \times \pi')$ and $\tilde{L} = L(s, \tilde{\pi} \times \tilde{\pi}')$ (for $\psi^{-1}$). Then $\varepsilon$ is a monomial, and for the central character $\omega'$ of $\pi'$ and each pair $(\Psi, \tilde{\Psi})$ of `rsFEPairs`, $$\frac{\tilde{\Psi}(1 - s)}{\tilde{L}(1 - s)} = \omega'(-1)^{n - 1} \varepsilon(s) \frac{\Psi(s)}{L(s)}.$$ The two quotients are Laurent polynomials in $q^{-s}$, so the equation is an identity of Laurent polynomials for all $s$; this is the form of the functional equation after the analytic continuation. -/
def IsRSEpsilonFactor (π : SmoothRep (GL (Fin n) K)) (π' : SmoothRep (GL (Fin m) K))
    (ψ : AddChar K ℂ) (ε : ℂ → ℂ) : Prop :=
  ∃ L Lt : ℂ → ℂ, IsRSLFactor μ π π' ψ L ∧
    IsRSLFactor μ π.contragredient π'.contragredient ψ⁻¹ Lt ∧ IsMonomialFactor K ε ∧
    ∀ ω' : Kˣ →* ℂˣ, π'.HasCentralChar ω' → ∀ p ∈ rsFEPairs μ π π' ψ,
      ∃ (A A' : Polynomial ℂ) (k k' : ℕ) (s₀ s₁ : ℝ),
        (∀ s : ℂ, s₀ < s.re →
          p.1 s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k * L s) ∧
        (∀ s : ℂ, s₁ < s.re →
          p.2 s = A'.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k' * Lt s) ∧
        ∀ s : ℂ, A'.eval ((residueCard K : ℂ) ^ (-(1 - s))) / ((residueCard K : ℂ) ^ (-(1 - s))) ^ k' =
          (ω' (-1) : ℂ) ^ (n - 1) * ε s *
            (A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k)

end Whittaker

section Family

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The Haar measure $\mu$ is self dual for an additive character of conductor exponent $k$: $\mu(\mathcal{O}_K)^2 q^k = 1$. -/
def IsSelfDual [MeasurableSpace K] (μ : Measure K) (k : ℤ) : Prop :=
  μ.real (LocalGL1.ordBall K 0) ^ 2 * (residueCard K : ℝ) ^ k = 1

/-- **The conditions on a family with the factors of pairs.** The conditions of `Langlands.IsLanglandsFamily`, and for $1 \le m' \le m \le n$, each $\pi \in \mathrm{Irr}(GL_m(K))$ that is ψ-generic and each $\pi' \in \mathrm{Irr}(GL_{m'}(K))$ that is $\psi^{-1}$-generic, with $\rho = \mathrm{rec}_m(\pi)$ and $\rho' = \mathrm{rec}_{m'}(\pi')$: condition 5, $L(s, \pi \times \pi') = L(s, \rho \otimes \rho')$, and condition 6, $\varepsilon(s, \pi \times \pi', \psi) = \varepsilon(s, \rho \otimes \rho', \psi)$ for the self dual measure. The conditions are stated only for generic representations. -/
structure IsLanglandsFamilyPairs [MeasurableSpace K] (art : Kˣ ≃ₜ* WeilGroup.Ab K)
    (ε : WDEpsilonFn K) (n : ℕ) (rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m) : Prop
    extends IsLanglandsFamily K art n rec where
  lFactorPair : ∀ m (hm : m ≤ n) m' (hm' : m' ≤ m), 1 ≤ m' →
    ∀ (π : IrrRep (GL (Fin m) K)) (π' : IrrRep (GL (Fin m') K))
      (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m'),
      WDIso.mk ρ = rec m hm (IrrSmooth.mk π) → WDIso.mk ρ' = rec m' (hm'.trans hm) (IrrSmooth.mk π') →
      ∀ (ψ : AddChar K ℂ) (k : ℤ), LocalGL1.IsConductor ψ k → IsGeneric π.1 ψ → IsGeneric π'.1 ψ⁻¹ →
      ∀ (μ : Measure K) [μ.IsAddHaarMeasure] [SigmaFinite μ],
        IsRSLFactor μ π.1 π'.1 ψ (ρ.tensor ρ').lFactor
  epsilonPair : ∀ m (hm : m ≤ n) m' (hm' : m' ≤ m), 1 ≤ m' →
    ∀ (π : IrrRep (GL (Fin m) K)) (π' : IrrRep (GL (Fin m') K))
      (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m'),
      WDIso.mk ρ = rec m hm (IrrSmooth.mk π) → WDIso.mk ρ' = rec m' (hm'.trans hm) (IrrSmooth.mk π') →
      ∀ (ψ : AddChar K ℂ) (k : ℤ), LocalGL1.IsConductor ψ k → IsGeneric π.1 ψ → IsGeneric π'.1 ψ⁻¹ →
      ∀ (μ : Measure K) [μ.IsAddHaarMeasure] [SigmaFinite μ], IsSelfDual K μ k →
        IsRSEpsilonFactor μ π.1 π'.1 ψ (ε μ (m * m') (ρ.tensor ρ') ψ)

/-- A family with the conditions of `IsLanglandsFamilyPairs` has the conditions of `IsLanglandsFamily`. -/
theorem IsLanglandsFamilyPairs.isLanglandsFamily [MeasurableSpace K] {art : Kˣ ≃ₜ* WeilGroup.Ab K}
    {ε : WDEpsilonFn K} {n : ℕ} {rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m}
    (h : IsLanglandsFamilyPairs K art ε n rec) : IsLanglandsFamily K art n rec :=
  h.toIsLanglandsFamily

/-- **The local Langlands correspondence for $GL_n$ with the factors of pairs** (Harris and Taylor, Henniart, Scholze), existence part. For each nonarchimedean local field $K$ and each local Artin map, there is a Galois ε-factor with the properties of `IsWDEpsilon`, and a family $(\mathrm{rec}_m)_{m \le n}$ with the conditions of `IsLanglandsFamilyPairs` for this ε-factor. The conditions on pairs are stated only for generic representations. -/
def LocalLanglandsGLFull (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      letI : MeasurableSpace K := borel K
      ∃ ε : WDEpsilonFn K, IsWDEpsilon K art ε ∧
        ∃ rec : ∀ m ≤ n, IrrSmooth (GL (Fin m) K) ≃ WDIso K m, IsLanglandsFamilyPairs K art ε n rec

/-- `LocalLanglandsGLFull n` implies `LocalLanglandsGL n`. -/
theorem LocalLanglandsGLFull.localLanglandsGL {n : ℕ} (h : LocalLanglandsGLFull.{u} n) :
    LocalLanglandsGL.{u} n := by
  intro K _ _ _ _ art hart
  let : MeasurableSpace K := borel K
  obtain ⟨ε, -, rec, hrec⟩ := h K art hart
  exact ⟨rec, hrec.isLanglandsFamily⟩

end Family

section GL1

open LocalGL1 Filter

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/-- **Tate's local theory as a zeta generator.** Let $Z$ be a family of functions that are multiples $c Z(\varphi, \chi, s)$ of Tate zeta integrals, and that contains each Tate zeta integral $Z(\varphi, \chi, s)$. Then the Tate L-factor $L(s, \chi)$ generates $Z$. The proof is the proof of `Langlands.LocalGL1.isGJLFactor_wdOfChar`. -/
theorem isZetaGenerator_of_zeta (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) (Z : Set (ℂ → ℂ))
    (hZ : ∀ f ∈ Z, ∃ (c : ℂ) (φ : K → ℂ), IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      f = fun s => c * zeta χ μ φ s)
    (hgen : ∀ φ : K → ℂ, IsLocallyConstant φ → HasCompactSupport φ → (fun s => zeta χ μ φ s) ∈ Z) :
    IsZetaGenerator K Z (charLFactor K (unif K) χ) := by
  classical
  have hL : ∀ s, charLFactor K (unif K) χ s =
      if ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 then (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 1 := fun s => rfl
  have hX : ∀ s : ℂ, (residueCard K : ℂ) ^ (-s) ≠ 0 := fun s =>
    Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast residueCard_pos'.ne'))
  have hc0 : (μ.real (ordShell K 0) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (measureReal_ordShell_ne_zero μ)
  refine ⟨?_, ?_, ?_⟩
  · by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · exact ⟨1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X, by simp,
        fun s => by rw [(hL s).trans (ite_eq_left hunr)]; simp⟩
    · exact ⟨1, by simp, fun s => by rw [(hL s).trans (ite_eq_right hunr)]; simp⟩
  · intro f hf
    obtain ⟨c, φ, hφ, hφs, rfl⟩ := hZ f hf
    obtain ⟨A, M, N, hA⟩ := exists_zeta_eq χ μ hχ hφ hφs
    by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · refine ⟨Polynomial.C c * (A * (1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X) +
        Polynomial.C (φ 0 * (μ.real (ordShell K 0) : ℂ) * (χ (unif K) : ℂ) ^ N) *
          Polynomial.X ^ (N + M)), M, zetaBound χ, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_unramified χ μ hunr] at h0
      have h1 := one_sub_ne_zero χ hs'
      have hT : ballZeta χ μ (fun _ => 1) s 0 =
          (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
        rw [← h0, mul_div_cancel_right₀ _ h1]
      simp only
      rw [hA s hs', hT, (hL s).trans (ite_eq_left hunr)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
      have hXs := hX s
      generalize (residueCard K : ℂ) ^ (-s) = X at hXs h1 ⊢
      generalize (χ (unif K) : ℂ) = d at h1 ⊢
      have h1' : 1 - X * d ≠ 0 := by rwa [mul_comm]
      field_simp
      ring
    · simp only [not_forall] at hunr
      obtain ⟨u, hu, hχu⟩ := hunr
      refine ⟨Polynomial.C c * A, M, zetaBound χ, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_ramified χ μ hu hχu] at h0
      have hT : ballZeta χ μ (fun _ => 1) s 0 = 0 :=
        (mul_eq_zero.1 h0).resolve_right (one_sub_ne_zero χ hs')
      have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
      simp only
      rw [hA s hs', hT, (hL s).trans (ite_eq_right hn)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
  · by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
    · have hl0 : IsLocallyConstant ((ordBall K 0).indicator fun _ => (1 : ℂ)) :=
        isLocallyConstant_indicator (isOpen_ordBall 0) (isClosed_ordBall 0)
          (fun _ _ => Eventually.of_forall fun _ => rfl)
      have hs0 : HasCompactSupport ((ordBall K 0).indicator fun _ => (1 : ℂ)) :=
        HasCompactSupport.intro (isCompact_ordBall 0) (fun _ hy => Set.indicator_of_notMem hy _)
      refine ⟨1, fun _ s => zeta χ μ ((ordBall K 0).indicator fun _ => 1) s,
        fun _ => Polynomial.C ((μ.real (ordShell K 0) : ℂ))⁻¹, 0,
        zetaBound χ, fun _ => hgen _ hl0 hs0, fun s hs => ?_⟩
      have hs' := norm_zetaRatio_le χ hs
      have h0 := ballZeta_one_zero χ μ hχ hs'
      rw [shellCoeff_one_of_unramified χ μ hunr] at h0
      have h1 := one_sub_ne_zero χ hs'
      rw [Fin.sum_univ_one]
      simp only
      rw [zeta_indicator_ordBall, (hL s).trans (ite_eq_left hunr)]
      simp only [Polynomial.eval_C, pow_zero, div_one]
      have hT : ballZeta χ μ (fun _ => 1) s 0 =
          (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
        rw [← h0, mul_div_cancel_right₀ _ h1]
      rw [hT]
      field_simp
    · simp only [not_forall] at hunr
      have hl1 : IsLocallyConstant ((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) :=
        isLocallyConstant_indicator (isOpen_ordShell 0) (isClosed_ordShell 0)
          (fun y hy => (eventually_extChar_eq χ hχ hy.1).mono fun z hz => by rw [hz])
      have hs1 : HasCompactSupport ((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) :=
        HasCompactSupport.intro (isCompact_ordShell 0) (fun _ hy => Set.indicator_of_notMem hy _)
      refine ⟨1, fun _ s => zeta χ μ ((ordShell K 0).indicator fun y => (extChar χ y)⁻¹) s,
        fun _ => Polynomial.C ((μ.real (ordShell K 0) : ℂ))⁻¹, 0,
        zetaBound χ, fun _ => hgen _ hl1 hs1, fun s hs => ?_⟩
      obtain ⟨u, hu, hχu⟩ := hunr
      have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
      rw [Fin.sum_univ_one]
      simp only
      rw [zeta_indicator_ordShell, (hL s).trans (ite_eq_right hn)]
      simp only [Polynomial.eval_C, pow_zero, div_one]
      field_simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- In dimension one, if $W(g) = a \chi(\det g)$, then the extension of $W$ to $M_1(K)$ is $x \mapsto a \chi(x)$ with $\chi(0) = 0$. -/
theorem extGL_one (χ : Kˣ →* ℂˣ) (a : ℂ) (W : GL (Fin 1) K → ℂ)
    (hW : ∀ g, W g = a * χ (Matrix.GeneralLinearGroup.det g)) (x : Matrix (Fin 1) (Fin 1) K) :
    extGL W x = a * extChar χ (x 0 0) := by
  classical
  rw [extGL]
  split_ifs with h
  · have h0 : x 0 0 ≠ 0 := by rw [← Matrix.det_fin_one x]; exact h.ne_zero
    rw [hW, extChar_of_ne_zero χ h0]
    congr 3
    ext
    simp only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Units.val_mk0]
    rfl
  · have h0 : x 0 0 = 0 := by
      by_contra h0
      exact h (by rw [Matrix.det_fin_one]; exact isUnit_iff_ne_zero.2 h0)
    rw [h0, extChar_zero, mul_zero]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- In dimension one the lower unipotent matrix is $1$. -/
theorem lowerUnip_one (u : StrictLower 1 → K) : lowerUnip u = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [lowerUnip]

/-- A matrix of size one has no entry below the diagonal. -/
instance : IsEmpty (StrictLower 1) :=
  ⟨fun p => by have := p.2; omega⟩

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- **The zeta integral of pairs in dimension one.** If $F(x) = a \chi(x)$ and $F'(x) = b \chi'(x)$ on $M_1(K) = K$, then $\Psi(s, F, F', \Phi) = a b Z(\Phi, \chi \chi', s)$, the Tate zeta integral of $\chi \chi'$. -/
theorem rsZetaPhi_one_of_eq [SigmaFinite μ] (χ χ' : Kˣ →* ℂˣ) (a b : ℂ)
    (F F' : Matrix (Fin 1) (Fin 1) K → ℂ) (hF : ∀ x, F x = a * extChar χ (x 0 0))
    (hF' : ∀ x, F' x = b * extChar χ' (x 0 0)) (Φ : (Fin 1 → K) → ℂ) (s : ℂ) :
    rsZetaPhi μ F F' Φ s = a * b * zeta (χ * χ') μ (fun y => Φ fun _ => y) s := by
  unfold rsZetaPhi quotIntegral
  simp only [lowerUnip_one, one_mul, Fin.prod_univ_one]
  rw [Measure.pi_of_empty (fun _ => μ) (Function.const _ 0), integral_dirac]
  have hmp := (measurePreserving_funUnique μ (Fin 1)).symm
  refine (hmp.integral_comp' (fun t : Fin 1 → K => F (diagonal t) * F' (diagonal t) *
    Φ (lastRow (diagonal t)) * (normAbs K (diagonal t).det : ℂ) ^ s *
      ((normAbs K (t 0) : ℂ))⁻¹)).symm.trans ?_
  rw [zeta, ← integral_const_mul]
  congr 1
  funext y
  have hdiag : diagonal ((MeasurableEquiv.funUnique (Fin 1) K).symm y) = Matrix.of fun _ _ => y := by
    ext i j
    fin_cases i; fin_cases j
    rfl
  have hrow : lastRow (Matrix.of fun _ _ => y : Matrix (Fin 1) (Fin 1) K) = fun _ => y := by
    funext k
    simp [lastRow]
  have hy0 : (MeasurableEquiv.funUnique (Fin 1) K).symm y 0 = y := rfl
  rw [hdiag, hrow, hy0, hF, hF', Matrix.det_fin_one]
  simp only [Matrix.of_apply]
  rw [zetaFn]
  by_cases hy : y = 0
  · simp [hy, extChar_zero]
  · have hn : (normAbs K y : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      simp only [normAbs, hy, ↓reduceIte]
      exact zpow_ne_zero _ (by exact_mod_cast residueCard_pos'.ne')
    rw [extChar_of_ne_zero χ hy, extChar_of_ne_zero χ' hy, extChar_of_ne_zero (χ * χ') hy,
      Complex.cpow_sub _ _ hn, Complex.cpow_one, MonoidHom.mul_apply, Units.val_mul]
    field_simp

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- For Whittaker functions $W = a \chi \circ \det$ and $W' = b \chi' \circ \det$ of $GL_1(K)$, $\Psi(s, W, W', \Phi) = a b Z(\Phi, \chi \chi', s)$. -/
theorem rsZetaPhi_one [SigmaFinite μ] (χ χ' : Kˣ →* ℂˣ) (a b : ℂ) (W W' : GL (Fin 1) K → ℂ)
    (hW : ∀ g, W g = a * χ (Matrix.GeneralLinearGroup.det g))
    (hW' : ∀ g, W' g = b * χ' (Matrix.GeneralLinearGroup.det g)) (Φ : (Fin 1 → K) → ℂ) (s : ℂ) :
    rsZetaPhi μ (extGL W) (extGL W') Φ s = a * b * zeta (χ * χ') μ (fun y => Φ fun _ => y) s :=
  rsZetaPhi_one_of_eq μ χ χ' a b _ _ (extGL_one χ a W hW) (extGL_one χ' b W' hW') Φ s

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The extension by zero satisfies $\chi(y^{-1}) = \chi^{-1}(y)$, also at $y = 0$. -/
theorem extChar_inv' (χ : Kˣ →* ℂˣ) (y : K) : extChar χ y⁻¹ = extChar χ⁻¹ y := by
  by_cases hy : y = 0
  · simp [hy, extChar_zero]
  · rw [extChar_of_ne_zero χ (inv_ne_zero hy), extChar_of_ne_zero χ⁻¹ hy, MonoidHom.inv_apply]
    congr 1
    rw [← map_inv]
    congr 1
    ext
    simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- In dimension one, if $F(x) = a \chi(x)$, then $\tilde{F}(x) = a \chi^{-1}(x)$. -/
theorem tildeF_one (χ : Kˣ →* ℂˣ) (a : ℂ) (F : Matrix (Fin 1) (Fin 1) K → ℂ)
    (hF : ∀ x, F x = a * extChar χ (x 0 0)) (x : Matrix (Fin 1) (Fin 1) K) :
    tildeF F x = a * extChar χ⁻¹ (x 0 0) := by
  have ha : (antiDiag 1 : Matrix (Fin 1) (Fin 1) K) = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [antiDiag]
  rw [tildeF, ha, one_mul, hF, Matrix.transpose_apply, Matrix.inv_def, Matrix.adjugate_fin_one,
    Matrix.det_fin_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Ring.inverse_eq_inv', extChar_inv']

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K]
  [μ.IsAddHaarMeasure] [μ.Regular] in
/-- In dimension one the Fourier transform on $K^1$ is the Fourier transform on $K$. -/
theorem fourierPi_one [SigmaFinite μ] (ψ : AddChar K ℂ) (Φ : (Fin 1 → K) → ℂ) (y : K) :
    fourierPi μ ψ Φ (fun _ => y) = fourier μ ψ (fun x => Φ fun _ => x) y := by
  unfold fourierPi fourier
  have hmp := (measurePreserving_funUnique μ (Fin 1)).symm
  refine (hmp.integral_comp' (fun t : Fin 1 → K => Φ t * ψ (∑ i, t i * (fun _ => y) i))).symm.trans ?_
  congr 1
  funext x
  simp only [Fin.sum_univ_one]
  rfl

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  [μ.IsAddHaarMeasure] [μ.Regular] in
/-- In dimension one each linear form is a Whittaker functional, because $N_1$ is trivial. -/
theorem isWhittakerFunctional_one (χ : Kˣ →* ℂˣ) (π : SmoothRep (GL (Fin 1) K))
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (ψ : AddChar K ℂ)
    (l : Module.Dual ℂ π.V) : IsWhittakerFunctional π ψ l := by
  intro u hu v
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    ext
    simp [hu.1 0]
  simp [hπ, hdet, unipChar]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  [μ.IsAddHaarMeasure] [μ.Regular] in
/-- A matrix coefficient of a representation of $GL_1(K)$ by $\chi \circ \det$ is $\lambda(v) \chi(\det g)$. -/
theorem coeff_one (χ : Kˣ →* ℂˣ) (π : SmoothRep (GL (Fin 1) K))
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (v : π.V)
    (l : Module.Dual ℂ π.V) (g : GL (Fin 1) K) :
    π.coeff v l g = l v * χ (Matrix.GeneralLinearGroup.det g) := by
  rw [SmoothRep.coeff, hπ, map_smul, smul_eq_mul, mul_comm]

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The product of two smooth characters is smooth. -/
theorem isSmoothChar_mul_pair {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ') :
    IsSmoothChar K (χ * χ') := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ'.ker) (fun x hx => ?_) (hχ.inter hχ')
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, mul_one]

/-- **The L-factor of pairs for $m = m' = 1$.** For representations of $GL_1(K)$ by $\chi \circ \det$ and $\chi' \circ \det$ on nonzero spaces, the Rankin-Selberg L-factor is the Tate L-factor $L(s, \chi \chi')$. -/
theorem isRSLFactor_one [SigmaFinite μ] {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ') (π π' : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V] [Nontrivial π'.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (hπ' : ∀ g v, π'.ρ g v = (χ' (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (ψ : AddChar K ℂ) :
    IsRSLFactor μ π π' ψ (charLFactor K (unif K) (χ * χ')) := by
  classical
  refine isZetaGenerator_of_zeta μ (χ * χ') (isSmoothChar_mul_pair hχ hχ') _ ?_ ?_
  · intro f hf
    simp only [rsZetaSet, lt_self_iff_false, ↓reduceIte] at hf
    obtain ⟨h, W, ⟨l, -, v, rfl⟩, W', ⟨l', -, v', rfl⟩, Φ, hΦ, rfl⟩ := hf
    refine ⟨l v * l' v', fun y => Φ fun _ => y,
      hΦ.1.comp_continuous (continuous_pi fun _ => continuous_id),
      hΦ.2.comp_homeomorph (Homeomorph.funUnique (Fin 1) K).symm, ?_⟩
    funext s
    exact rsZetaPhi_one μ χ χ' _ _ _ _ (coeff_one χ π hπ v l) (coeff_one χ' π' hπ' v' l') Φ s
  · intro φ hφ hφs
    obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
    obtain ⟨v', hv'⟩ := exists_ne (0 : π'.V)
    obtain ⟨l', hl'⟩ := Module.Projective.exists_dual_ne_zero ℂ hv'
    simp only [rsZetaSet, lt_self_iff_false, ↓reduceIte]
    refine ⟨trivial, _, ⟨(l v)⁻¹ • l, isWhittakerFunctional_one χ π hπ ψ _, v, rfl⟩,
      _, ⟨(l' v')⁻¹ • l', isWhittakerFunctional_one χ' π' hπ' ψ⁻¹ _, v', rfl⟩,
      fun x => φ (x 0), ⟨hφ.comp_continuous (continuous_apply 0),
        hφs.comp_homeomorph (Homeomorph.funUnique (Fin 1) K)⟩, ?_⟩
    funext s
    rw [rsZetaPhi_one μ χ χ' _ _ _ _ (coeff_one χ π hπ v _) (coeff_one χ' π' hπ' v' _)]
    simp [hl, hl']

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The tensor product of $(\chi \circ \mathrm{art}_K^{-1}, 0)$ and $(\chi' \circ \mathrm{art}_K^{-1}, 0)$ is $(\chi \chi' \circ \mathrm{art}_K^{-1}, 0)$. -/
theorem tensor_wdOfChar (art : Kˣ ≃ₜ* WeilGroup.Ab K) {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ') :
    ((wdOfChar K art χ hχ).tensor (wdOfChar K art χ' hχ') : WeilDeligneRep K 1) =
      wdOfChar K art (χ * χ') (isSmoothChar_mul_pair hχ hχ') := by
  refine wd_ext K ?_ (by rw [N_eq_zero, N_eq_zero])
  ext w i j
  fin_cases i; fin_cases j
  change kronMat ((wdOfChar K art χ hχ).r w : Matrix (Fin 1) (Fin 1) ℂ) ((wdOfChar K art χ' hχ').r w : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = _
  simp [wdOfChar_r, kronMat, weilChar_apply, unitGL]

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- For a local Artin map, the L-factor of $(\chi \circ \mathrm{art}_K^{-1}, 0) \otimes (\chi' \circ \mathrm{art}_K^{-1}, 0)$ is the Tate L-factor $L(s, \chi \chi')$. -/
theorem lFactor_tensor_wdOfChar {art : Kˣ ≃ₜ* WeilGroup.Ab K} (hart : IsLocalArtinMap K art)
    {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ') :
    ((wdOfChar K art χ hχ).tensor (wdOfChar K art χ' hχ')).lFactor =
      charLFactor K (unif K) (χ * χ') := by
  funext s
  rw [tensor_wdOfChar art hχ hχ']
  exact (charLFactor_eq_lFactor_of_iff K art hart _ _ _ isUniformizer_unif
    (unramified_iff hart _) s).symm

/-- **Condition 5 for $m = m' = 1$.** For a local Artin map, the L-factor of the tensor product of the Weil-Deligne representations of $\chi$ and $\chi'$ is the Rankin-Selberg L-factor of $\chi \circ \det$ and $\chi' \circ \det$. -/
theorem isRSLFactor_tensor_wdOfChar [SigmaFinite μ] {art : Kˣ ≃ₜ* WeilGroup.Ab K}
    (hart : IsLocalArtinMap K art) {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ') (π π' : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V] [Nontrivial π'.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (hπ' : ∀ g v, π'.ρ g v = (χ' (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (ψ : AddChar K ℂ) :
    IsRSLFactor μ π π' ψ ((wdOfChar K art χ hχ).tensor (wdOfChar K art χ' hχ')).lFactor := by
  rw [lFactor_tensor_wdOfChar hart hχ hχ']
  exact isRSLFactor_one μ hχ hχ' π π' hπ hπ' ψ

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- For characters, $\chi^{-1} \chi'^{-1} = (\chi \chi')^{-1}$. -/
theorem inv_mul_inv_char (χ χ' : Kˣ →* ℂˣ) : χ⁻¹ * χ'⁻¹ = (χ * χ')⁻¹ := by
  ext x
  simp [mul_comm]

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- **The functional equation of pairs for $m = m' = 1$ is Tate's.** For representations of $GL_1(K)$ by $\chi \circ \det$ and $\chi' \circ \det$, each pair of `rsFEPairs` is $(c Z(\varphi, \chi \chi', s), c Z(\hat{\varphi}, (\chi \chi')^{-1}, s))$ for a constant $c$ and a locally constant $\varphi$ with compact support. The sign $\omega'(-1)^{n - 1}$ is $1$ for $n = 1$. -/
theorem mem_rsFEPairs_one [SigmaFinite μ] {χ χ' : Kˣ →* ℂˣ} (π π' : SmoothRep (GL (Fin 1) K))
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (hπ' : ∀ g v, π'.ρ g v = (χ' (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (ψ : AddChar K ℂ)
    {p : (ℂ → ℂ) × (ℂ → ℂ)} (hp : p ∈ rsFEPairs μ π π' ψ) :
    ∃ (c : ℂ) (φ : K → ℂ), IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      p = (fun s => c * zeta (χ * χ') μ φ s, fun s => c * zeta (χ * χ')⁻¹ μ (fourier μ ψ φ) s) := by
  classical
  simp only [rsFEPairs, lt_self_iff_false, ↓reduceIte] at hp
  obtain ⟨h, W, ⟨l, -, v, rfl⟩, W', ⟨l', -, v', rfl⟩, Φ, hΦ, rfl⟩ := hp
  refine ⟨l v * l' v', fun y => Φ fun _ => y,
    hΦ.1.comp_continuous (continuous_pi fun _ => continuous_id),
    hΦ.2.comp_homeomorph (Homeomorph.funUnique (Fin 1) K).symm, ?_⟩
  have h1 := extGL_one χ (l v) _ (coeff_one χ π hπ v l)
  have h2 := extGL_one χ' (l' v') _ (coeff_one χ' π' hπ' v' l')
  refine Prod.ext (funext fun s => rsZetaPhi_one_of_eq μ χ χ' _ _ _ _ h1 h2 Φ s)
    (funext fun s => ?_)
  simp only
  rw [rsZetaPhi_one_of_eq μ χ⁻¹ χ'⁻¹ _ _ _ _ (tildeF_one χ _ _ h1) (tildeF_one χ' _ _ h2),
      inv_mul_inv_char]
  congr 2
  funext y
  exact fourierPi_one μ ψ Φ y

omit [μ.IsAddHaarMeasure] [μ.Regular] in
/-- Conversely, on nonzero spaces each pair $(Z(\varphi, \chi \chi', s), Z(\hat{\varphi}, (\chi \chi')^{-1}, s))$ of Tate zeta integrals is in `rsFEPairs`. -/
theorem zeta_pair_mem_rsFEPairs_one [SigmaFinite μ] {χ χ' : Kˣ →* ℂˣ}
    (π π' : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V] [Nontrivial π'.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (hπ' : ∀ g v, π'.ρ g v = (χ' (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (ψ : AddChar K ℂ)
    {φ : K → ℂ} (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    (fun s => zeta (χ * χ') μ φ s, fun s => zeta (χ * χ')⁻¹ μ (fourier μ ψ φ) s) ∈
      rsFEPairs μ π π' ψ := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  obtain ⟨v', hv'⟩ := exists_ne (0 : π'.V)
  obtain ⟨l', hl'⟩ := Module.Projective.exists_dual_ne_zero ℂ hv'
  simp only [rsFEPairs, lt_self_iff_false, ↓reduceIte]
  refine ⟨trivial, _, ⟨(l v)⁻¹ • l, isWhittakerFunctional_one χ π hπ ψ _, v, rfl⟩,
    _, ⟨(l' v')⁻¹ • l', isWhittakerFunctional_one χ' π' hπ' ψ⁻¹ _, v', rfl⟩,
    fun x => φ (x 0), ⟨hφ.comp_continuous (continuous_apply 0),
      hφs.comp_homeomorph (Homeomorph.funUnique (Fin 1) K)⟩, ?_⟩
  have h1 := extGL_one χ _ _ (coeff_one χ π hπ v ((l v)⁻¹ • l))
  have h2 := extGL_one χ' _ _ (coeff_one χ' π' hπ' v' ((l' v')⁻¹ • l'))
  refine Prod.ext (funext fun s => ?_) (funext fun s => ?_)
  · simp only
    rw [rsZetaPhi_one_of_eq μ χ χ' _ _ _ _ h1 h2]
    simp [hl, hl']
  · simp only
    rw [rsZetaPhi_one_of_eq μ χ⁻¹ χ'⁻¹ _ _ _ _ (tildeF_one χ _ _ h1) (tildeF_one χ' _ _ h2),
      inv_mul_inv_char]
    have hf : (fun y => fourierPi μ ψ (fun x : Fin 1 → K => φ (x 0)) fun _ => y) = fourier μ ψ φ := by
      funext y
      exact fourierPi_one μ ψ _ y
    rw [hf]
    simp [hl, hl']

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] [μ.Regular] in
/-- The character $\det r \circ \mathrm{art}_K$ of $(\chi \circ \mathrm{art}_K^{-1}, 0)$ is $\chi$. -/
theorem charOfWD_wdOfChar_eq (art : Kˣ ≃ₜ* WeilGroup.Ab K) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    charOfWD K art (wdOfChar K art χ hχ) = χ := by
  ext x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
  rw [charOfWD_apply K art _ hw]
  simp [WeilDeligneRep.det, wdOfChar_r, det_unitGL, weilChar_apply, hw]

omit [BorelSpace K] [μ.Regular] in
/-- **The Galois ε-factor of pairs for $m = m' = 1$.** For an ε-factor with the properties of `IsWDEpsilon`, the ε-factor of the tensor product of the Weil-Deligne representations of $\chi$ and $\chi'$ is Tate's ε-factor of $\chi \chi'$. -/
theorem isTateEpsilon_tensor {art : Kˣ ≃ₜ* WeilGroup.Ab K} {ε : WDEpsilonFn K}
    (hε : IsWDEpsilon K art ε) {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (hχ' : IsSmoothChar K χ')
    {ψ : AddChar K ℂ} {k : ℤ} (hψ : IsConductor ψ k) :
    IsTateEpsilon K μ (χ * χ') ψ
      (ε μ (1 * 1) ((wdOfChar K art χ hχ).tensor (wdOfChar K art χ' hχ')) ψ) := by
  have h := hε.dimOne μ (wdOfChar K art (χ * χ') (isSmoothChar_mul_pair hχ hχ')) ψ k hψ
  rw [charOfWD_wdOfChar_eq] at h
  have he : ε μ (1 * 1) ((wdOfChar K art χ hχ).tensor (wdOfChar K art χ' hχ')) ψ =
      ε μ 1 (wdOfChar K art (χ * χ') (isSmoothChar_mul_pair hχ hχ')) ψ :=
    congrArg (fun ρ : WeilDeligneRep K 1 => ε μ 1 ρ ψ) (tensor_wdOfChar art hχ hχ')
  rw [he]
  exact h

end GL1

end Langlands
