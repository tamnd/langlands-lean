/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.BreuilMezardSym
import Langlands.Deformation.Framed
import Langlands.Padic.Semistable2
import Langlands.Statements.BreuilMezard

/-!
# The Breuil-Mézard conjecture for GL(2) over the p-adic numbers

This file states the conjecture of Breuil and Mézard for $GL_2(\mathbb{Q}_p)$ with the real objects of the project. It does not replace the shape `Langlands.BreuilMezardGL2Qp` of `Langlands.Statements.BreuilMezard`, which other files use.

Let $p$ be a prime, let $k$ be a finite field of characteristic $p$ and let $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$ be continuous. Let $R$ be a universal framed deformation ring of $\bar\rho$ over $\mathbb{Z}_p$, with universal lift $\rho^u$. For a Hodge-Tate type $\lambda = (\lambda_1 > \lambda_2)$ and an inertial type $\tau$, let $R(\lambda, \tau)$ be the quotient of $R$ cut out by the points whose lifts are potentially semistable with Hodge-Tate weights $\lambda$ and inertial type $\tau$. Let $\sigma(\tau)$ be the type of Henniart, a smooth irreducible representation of $GL_2(\mathbb{Z}_p)$. The conjecture says that there are integers $\mu_{a,b}(\bar\rho)$ such that for all $\lambda$ and $\tau$
$$e(R(\lambda, \tau) / p) = \sum_{0 \le a \le p - 1} \sum_{0 \le b \le p - 2} n_{a,b}(\lambda, \tau) \, \mu_{a,b}(\bar\rho),$$
where $e$ is the Hilbert-Samuel multiplicity and $n_{a,b}(\lambda, \tau)$ is the multiplicity of the Serre weight $\mathrm{Sym}^a k^2 \otimes \det^b$ in the reduction of a stable lattice of $\mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} E^2 \otimes \det^{\lambda_2} \otimes \sigma_E$. Here $\sigma_E$ is a model of $\sigma(\tau)$ over a finite extension $E$ of $\mathbb{Q}_p$.

## Main definitions

* `Langlands.restrictToQp`: a lift $\rho : G_{\mathbb{Q}_p} \to GL_2(E)$ as a representation over $\mathbb{Q}_p$ on $E^2$.
* `Langlands.InertialTypeMap`: an assignment of an inertial type to each lift. It is a parameter of the statement.
* `Langlands.IsPstLift`: the point predicate of $R(\lambda, \tau)$. The lift is continuous, potentially semistable, has Hodge-Tate weights $\lambda$ and has inertial type $\tau$.
* `Langlands.IsModelOf`: a representation $\tau_E$ over $E$ is a model of a complex representation $\sigma$ along an embedding $j : E \to \mathbb{C}$.
* `Langlands.BreuilMezardFullFor`: the conjecture for one residual representation $\bar\rho$, one correspondence `rec` and one map `wd`.
* `Langlands.BreuilMezardGL2QpFull`: the conjecture for all $k$ and $\bar\rho$ and for all correspondences that satisfy `IsLanglandsMap`.

## Main results

* `Langlands.typeMultiplicityOf_one_zero_trivial`: for $\lambda = (1, 0)$ and the trivial type, $n_{a,b}$ is the multiplicity of $\sigma_{a,b}$ in the trivial representation over the residue field.
* `Langlands.typeMultiplicityOf_coeffRed_trivial`: over each coefficient field $E$ of the statement, $n_{0,0}((1, 0), 1) = 1$.
* `Langlands.typeMultiplicityOf_one_zero_trivial_of_ne_zero`: for $a \ne 0$, $n_{a,b}((1, 0), 1) = 0$.
* `Langlands.BreuilMezardFullFor.exists_mu`: if the conjecture holds, then each input whose multiplicities are $1$ at one Serre weight $(a_0, b_0)$ and $0$ at the others gives $e(R(\lambda, \tau) / p) = \mu_{a_0,b_0}(\bar\rho)$.

## Fidelity

These parts are faithful.

* The ring $R$ is a universal framed deformation ring in the sense of `IsUniversalFramedDeformationRing`, over $\Lambda = \mathbb{Z}_p$ with residue field $k$.
* The left side is `specialFiberMultiplicity` with $\varpi = p$. This is the Hilbert-Samuel multiplicity of $R(\lambda, \tau) / p$ at its maximal ideal.
* A point of $R(\lambda, \tau)$ is a lift to a field $E$ that is finite over $\mathbb{Q}_p$, compatible with the structure map from $\mathbb{Z}_p$. The lift must be continuous for the module topology and potentially semistable in the sense of `Padic.IsPotentiallySemistableQp`, that is, semistable on an open subgroup $G_L$ with $B_{st}$ of the project.
* The Hodge-Tate weights are the real `Padic.hodgeTateWeights` of the lift over $\mathbb{Q}_p$. The project convention gives weight $-1$ to the cyclotomic character, and $\sigma(\lambda, \tau)$ uses $\mathrm{Sym}^{\lambda_1 - \lambda_2 - 1} \otimes \det^{\lambda_2}$, which fits weights $\{\lambda_1, \lambda_2\}$ in the convention where the cyclotomic character has weight $1$. So the condition is that the set of weights is $\{-\lambda_1, -\lambda_2\}$. The weights are a set, so the condition does not see multiplicities. Over $\mathbb{Q}_p$ the weights do not depend on the embedding of $E$, and $\lambda_1 > \lambda_2$, so for a lift of dimension $2$ over $E$ each weight has multiplicity $1$.
* The multiplicities $n_{a,b}$ are `typeMultiplicityOf` with the reduction map `coeffRed p E`, for every finite extension $E$ and every model $\tau_E$ of $\sigma(\tau)$ over $E$. They do not depend on the stable lattice, by `serreMultiplicityIndependent`.
* The integers $\mu_{a,b}$ exist before $\lambda$, $\tau$, $E$ and the model are chosen, as in the conjecture.
* The fidelity checks show that the type multiplicities are not forced to be zero, and that the conjecture determines $\mu_{a_0,b_0}$ from each input with $n = \delta_{(a_0,b_0)}$.

These parts are not faithful, or are weaker than the conjecture.

* The inertial type of a lift needs $D_{pst}$ and the Weil-Deligne representation of Fontaine. The project does not have them for $p$-adic representations. So the inertial type of a lift is given by the parameter `wd : InertialTypeMap p`, and the statement is faithful only when `wd` sends a potentially semistable lift to the restriction to inertia of its Weil-Deligne representation, transported to $\mathbb{C}$. For other maps the statement is a different claim. The value of `wd` on lifts that are not potentially semistable has no effect.
* The type $\sigma(\tau)$ is a representation with `IsHenniartType rec τ σ` for a correspondence `rec` with `IsLanglandsMap`. `IsLanglandsMap` does not fix `rec` on the supercuspidal representations, because the project does not have $\varepsilon$-factors. So for supercuspidal types the statement holds for each such `rec`, which is a stronger claim than the conjecture if `rec` is not unique.
* The project does not prove the theorem of Mazur that a universal framed deformation ring exists, or that types of Henniart and models over $E$ exist. If one of them does not exist, the statement is vacuous for that input.
* The ring $R(\lambda, \tau)$ is the quotient by the ideal of elements that vanish at all the points, which is the definition of Kisin when the points are dense. The project does not prove that it is the ring of Kisin, or that it is local and nonzero when it has a point. If it is not local, `specialFiberMultiplicity` is $0$.
* The project does not prove that a potentially semistable representation is de Rham, that $B_{st}^{G_L}$ is a field, or that $n_{a,b}$ does not depend on $E$ and the model. These hold in the mathematics.
* The prime $p = 2$ is included. The conjecture is known for $p > 2$ in most cases, and the statement for $p = 2$ is still the conjecture.

## References

* C. Breuil and A. Mézard, *Multiplicités modulaires et représentations de $GL_2(\mathbb{Z}_p)$ et de $\mathrm{Gal}(\overline{\mathbb{Q}}_p / \mathbb{Q}_p)$ en $\ell = p$*, Duke Math. J. 115 (2002).
* M. Kisin, *Potentially semi-stable deformation rings*, J. Amer. Math. Soc. 21 (2008).
* M. Kisin, *The Fontaine-Mazur conjecture for $GL_2$*, J. Amer. Math. Soc. 22 (2009).
* V. Paškūnas, *On the Breuil-Mézard conjecture*, Duke Math. J. 164 (2015).
* Y. Hu and F. Tan, *The Breuil-Mézard conjecture for non-scalar split residual representations*, Ann. Sci. Éc. Norm. Supér. 48 (2015).
* G. Henniart, appendix to Breuil and Mézard (2002).
-/

namespace Langlands

open ValuativeRel IsLocalRing

section Lifts

variable (p : ℕ) [Fact p.Prime]

/-- The representation $\rho$ of $G_{\mathbb{Q}_p}$ on $E^2$, seen as a representation over $\mathbb{Q}_p$. For $E$ finite over $\mathbb{Q}_p$ this is the $p$-adic representation whose Hodge-Tate weights and potential semistability the statement uses. -/
noncomputable def restrictToQp {E : Type*} [Field E] [Algebra ℚ_[p] E]
    (ρ : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) E) :
    Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) (Fin 2 → E) where
  toFun g := (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)).restrictScalars ℚ_[p]
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- An assignment of an inertial type to each lift $\rho : G_{\mathbb{Q}_p} \to GL_2(E)$. The intended map sends a potentially semistable lift to the restriction to inertia of its Weil-Deligne representation $WD(D_{pst}(\rho))$, transported to $\mathbb{C}$. The project cannot define this map yet, so the statement takes it as a parameter. -/
def InertialTypeMap : Type 1 :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[p] E],
    (Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) E) → InertialType ℚ_[p] 2

variable {p}

/-- The lift $\rho : G_{\mathbb{Q}_p} \to GL_2(E)$ is a point of $R(w, \tau)$. The structure map makes $E$ a finite extension of $\mathbb{Q}_p$, the lift is continuous and potentially semistable, its Hodge-Tate weights are $\{-w_1, -w_2\}$ in the convention of the project, and `wd` gives it the inertial type $\tau$. -/
def IsPstLift (w : ℤ × ℤ) (τ : InertialType ℚ_[p] 2) (wd : InertialTypeMap p) (E : Type)
    [Field E] [Algebra ℤ_[p] E] (ρ : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) E) : Prop :=
  ∃ _ : Algebra ℚ_[p] E, (∀ x : ℤ_[p], algebraMap ℚ_[p] E x = algebraMap ℤ_[p] E x) ∧
    ∃ _ : FiniteDimensional ℚ_[p] E,
      Padic.IsContinuousRep p (restrictToQp p ρ) ∧
      Padic.IsPotentiallySemistableQp (restrictToQp p ρ) ∧
      Padic.hodgeTateWeights (PadicComplexInt p) p (restrictToQp p ρ) = {-w.1, -w.2} ∧
      wd E ρ = τ

end Lifts

section Model

variable {E : Type*} [Field E] {H : Type*} [Group H] [TopologicalSpace H] {W : Type*}
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

/-- The representation $\tau_E$ over $E$ is a model of the complex representation $\sigma$ along the embedding $j : E \to \mathbb{C}$: in a basis of $\tau_E$, the matrices of $\tau_E$ mapped by $j$ give a representation on $\mathbb{C}^n$ that is isomorphic to $\sigma$. -/
def IsModelOf (j : E →+* ℂ) (τE : Representation E H W) (σ : SmoothRep H) : Prop :=
  ∃ e : (Fin (Module.finrank E W) → ℂ) ≃ₗ[ℂ] σ.V, ∀ g v,
    e (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis E W) (Module.finBasis E W)
      (τE g)).map j) v) = σ.ρ g (e v)

end Model

section Statement

variable (p : ℕ) [Fact p.Prime]

/-- The Breuil-Mézard conjecture for one residual representation $\bar\rho$, one correspondence `rec` and one map `wd`. For each universal framed deformation ring $R$ of $\bar\rho$ there are integers $\mu_{a,b}$ such that for each Hodge-Tate type $w$, each inertial type $\tau$ with a type $\sigma$ of Henniart, and each model $\tau_E$ of $\sigma$ over a finite extension $E$ of $\mathbb{Q}_p$, the multiplicity of the special fibre of $R(w, \tau)$ is $\sum_{a < p} \sum_{b < p - 1} n_{a,b}(w, \tau_E) \, \mu_{a,b}$. -/
def BreuilMezardFullFor (k : Type) [Field k] [Algebra ℤ_[p] k]
    (ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k)
    (rec : IrrSmooth (GL (Fin 2) ℚ_[p]) ≃ WDIso ℚ_[p] 2) (wd : InertialTypeMap p) : Prop :=
  ∀ (R : CoeffAlg ℤ_[p] k) (ρu : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) R),
    IsUniversalFramedDeformationRing ρbar R ρu →
    ∃ μ : ℕ → ℕ → ℕ, ∀ (w : HodgeTateType) (τ : InertialType ℚ_[p] 2)
      (σ : SmoothRep (GL (Fin 2) 𝒪[ℚ_[p]])), IsHenniartType rec τ σ →
      ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra ℚ_[p] E] [ValuativeExtension ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
        (W : Type) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
        (τE : Representation E (GL (Fin 2) 𝒪[ℚ_[p]]) W) (j : E →+* ℂ), IsModelOf j τE σ →
        specialFiberMultiplicity R ρu (IsPstLift w.1 τ wd) (p : ℤ_[p]) =
          ∑ a ∈ Finset.range p, ∑ b ∈ Finset.range (p - 1),
            typeMultiplicityOf ℚ_[p] (coeffRed p E) w.1 τE a b * μ a b

/-- The Breuil-Mézard conjecture for $GL_2(\mathbb{Q}_p)$, relative to the map `wd`. It is `BreuilMezardFullFor` for each finite field $k$ of characteristic $p$, each continuous $\bar\rho : G_{\mathbb{Q}_p} \to GL_2(k)$, and each correspondence `rec` that satisfies `IsLanglandsMap` for a local Artin map. The topology on $k$ is discrete, so continuity of $\bar\rho$ is the condition that its kernel is open. -/
def BreuilMezardGL2QpFull (wd : InertialTypeMap p) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k p] [Algebra ℤ_[p] k]
    (ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k),
    IsOpen (ρbar.ker : Set (Field.absoluteGaloisGroup ℚ_[p])) →
    ∀ art : ℚ_[p]ˣ ≃ₜ* WeilGroup.Ab ℚ_[p], IsLocalArtinMap ℚ_[p] art →
      ∀ rec : IrrSmooth (GL (Fin 2) ℚ_[p]) ≃ WDIso ℚ_[p] 2, IsLanglandsMap ℚ_[p] art 2 rec →
        BreuilMezardFullFor p k ρbar rec wd

end Statement

section Fidelity

open MvPolynomial TensorProduct

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*} [Group G]
  {C : Type*} [Field C] [Algebra O C] [IsFractionRing O C]

omit [IsDiscreteValuationRing O] in
/-- The image of $O$ in its fraction field $C$ is a stable lattice of the trivial representation. -/
theorem isStableLattice_range_trivial :
    IsStableLattice (Representation.trivial C G C) (LinearMap.range (Algebra.linearMap O C)) := by
  have hfg : (LinearMap.range (Algebra.linearMap O C)).FG :=
    LinearMap.range_eq_map (Algebra.linearMap O C) ▸ (Module.Finite.fg_top (R := O) (M := O)).map _
  refine ⟨{ toIsLattice := Submodule.IsLattice.of_fg C hfg, span_eq_top := ?_ }, fun g v hv => hv⟩
  rw [eq_top_iff]
  intro x _
  have h1 : (1 : C) ∈ Submodule.span C (LinearMap.range (Algebra.linearMap O C) : Set C) :=
    Submodule.subset_span ⟨1, by simp⟩
  simpa using Submodule.smul_mem _ x h1

/-- The multiplicity $n_{a,b}$ of the trivial representation on $C$ is the multiplicity of the trivial representation on $O$. -/
theorem serreMultiplicity_trivial (θ : G →* GL (Fin 2) (ResidueField O)) (a b : ℕ) :
    serreMultiplicity O (Representation.trivial C G C) θ a b =
      reductionMultiplicity (Representation.trivial O G O) (serreWeightRep θ a b) := by
  rw [serreMultiplicity_eq_latticeSerreMultiplicity _ θ isStableLattice_range_trivial]
  have hinj : Function.Injective (Algebra.linearMap O C) := IsFractionRing.injective O C
  exact reductionMultiplicity_congr (LinearEquiv.ofInjective _ hinj).symm (fun g x => rfl) _

end Fidelity

section FidelityType

open MvPolynomial TensorProduct

variable {K : Type*} [Field K] [ValuativeRel K] {C : Type*} [Field C] [Algebra K C]

/-- For $\lambda = (1, 0)$ and the trivial type, $\mathrm{Sym}^0 C^2 \otimes \det^0 \otimes 1$ is the trivial representation. -/
theorem typeRep_one_zero_trivial (g : GL (Fin 2) 𝒪[K]) :
    typeRep K (1, 0) (Representation.trivial C (GL (Fin 2) 𝒪[K]) C) g = 1 := by
  have h : symDetRep (glIntegersTo (C := C) K) 0 0 g = 1 := by
    rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, symDetRep_natCast]
    exact serreWeight_zero_zero _
  ext x
  simp [typeRep, Representation.tprod_apply, h]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O C]
  [IsFractionRing O C]

/-- The multiplicity $n_{a,b}(\lambda, \tau)$ for $\lambda = (1, 0)$ and the trivial type $\tau = 1$ is the multiplicity of $\sigma_{a,b}$ in the trivial representation over the residue field. -/
theorem typeMultiplicityOf_one_zero_trivial (red : 𝒪[K] →+* ResidueField O) (a b : ℕ) :
    typeMultiplicityOf K red (1, 0) (Representation.trivial C (GL (Fin 2) 𝒪[K]) C) a b =
      reductionMultiplicity (Representation.trivial O (GL (Fin 2) 𝒪[K]) O)
        (serreWeightRep (Matrix.GeneralLinearGroup.map red) a b) := by
  let V := homogeneousSubmodule (Fin 2) C ((1 : ℤ) - 0 - 1).toNat ⊗[C] C
  let := Module.restrictScalars O C V
  have := IsScalarTower.restrictScalars O C V
  let e : V ≃ₗ[C] C := (TensorProduct.rid C _).trans (homogeneousZeroEquiv C)
  refine (serreMultiplicity_congr (ρ' := Representation.trivial C (GL (Fin 2) 𝒪[K]) C) e
    (fun g x => ?_) _ a b).trans (serreMultiplicity_trivial _ a b)
  rw [typeRep_one_zero_trivial]
  rfl

/-- **Fidelity check.** The multiplicity $n_{0,0}((1, 0), 1)$ is $1$, so the type multiplicities in the Breuil-Mézard formula are not all zero. -/
theorem typeMultiplicityOf_one_zero_trivial_zero_zero (red : 𝒪[K] →+* ResidueField O) :
    typeMultiplicityOf K red (1, 0) (Representation.trivial C (GL (Fin 2) 𝒪[K]) C) 0 0 = 1 := by
  rw [typeMultiplicityOf_one_zero_trivial]
  exact reductionMultiplicity_trivial _

/-- **Fidelity check.** For $a \ne 0$ the multiplicity $n_{a,b}((1, 0), 1)$ is $0$. -/
theorem typeMultiplicityOf_one_zero_trivial_of_ne_zero (red : 𝒪[K] →+* ResidueField O) {a : ℕ}
    (ha : a ≠ 0) (b : ℕ) :
    typeMultiplicityOf K red (1, 0) (Representation.trivial C (GL (Fin 2) 𝒪[K]) C) a b = 0 := by
  rw [typeMultiplicityOf_one_zero_trivial]
  exact reductionMultiplicity_trivial_of_ne_zero _ ha b

end FidelityType

section FidelityStatement

variable (p : ℕ) [Fact p.Prime]

/-- **Fidelity check.** Over every coefficient field $E$ of the statement, the multiplicity $n_{0,0}((1, 0), 1)$ of the trivial model is $1$. -/
theorem typeMultiplicityOf_coeffRed_trivial (E : Type*) [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra ℚ_[p] E]
    [ValuativeExtension ℚ_[p] E] :
    typeMultiplicityOf ℚ_[p] (coeffRed p E) (1, 0)
      (Representation.trivial E (GL (Fin 2) 𝒪[ℚ_[p]]) E) 0 0 = 1 :=
  typeMultiplicityOf_one_zero_trivial_zero_zero _

variable {p}

/-- **Fidelity check.** If the conjecture holds, then each input whose multiplicities $n_{a,b}$ are $1$ at $(a_0, b_0)$ and $0$ at the other Serre weights determines $\mu_{a_0,b_0}(\bar\rho)$: it is the multiplicity of the special fibre of the deformation ring of this type. Thus the conjecture is not a statement about a sum of zeros. -/
theorem BreuilMezardFullFor.exists_mu {k : Type} [Field k] [Algebra ℤ_[p] k]
    {ρbar : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) k}
    {rec : IrrSmooth (GL (Fin 2) ℚ_[p]) ≃ WDIso ℚ_[p] 2} {wd : InertialTypeMap p}
    (h : BreuilMezardFullFor p k ρbar rec wd) {R : CoeffAlg ℤ_[p] k}
    {ρu : Field.absoluteGaloisGroup ℚ_[p] →* GL (Fin 2) R}
    (hR : IsUniversalFramedDeformationRing ρbar R ρu) :
    ∃ μ : ℕ → ℕ → ℕ, ∀ (w : HodgeTateType) (τ : InertialType ℚ_[p] 2)
      (σ : SmoothRep (GL (Fin 2) 𝒪[ℚ_[p]])), IsHenniartType rec τ σ →
      ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra ℚ_[p] E] [ValuativeExtension ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
        (W : Type) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
        (τE : Representation E (GL (Fin 2) 𝒪[ℚ_[p]]) W) (j : E →+* ℂ), IsModelOf j τE σ →
        ∀ a₀ b₀, a₀ < p → b₀ < p - 1 →
          (∀ a < p, ∀ b < p - 1, typeMultiplicityOf ℚ_[p] (coeffRed p E) w.1 τE a b =
            if a = a₀ ∧ b = b₀ then 1 else 0) →
          specialFiberMultiplicity R ρu (IsPstLift w.1 τ wd) (p : ℤ_[p]) = μ a₀ b₀ := by
  obtain ⟨μ, hμ⟩ := h R ρu hR
  refine ⟨μ, fun w τ σ hσ E _ _ _ _ _ _ _ W _ _ _ τE j hj a₀ b₀ ha₀ hb₀ hδ => ?_⟩
  rw [hμ w τ σ hσ E W τE j hj]
  have hs : ∀ a ∈ Finset.range p, ∑ b ∈ Finset.range (p - 1),
      typeMultiplicityOf ℚ_[p] (coeffRed p E) w.1 τE a b * μ a b =
        if a = a₀ then μ a₀ b₀ else 0 := by
    intro a ha
    rw [Finset.sum_congr rfl fun b hb => by
      rw [hδ a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb)]]
    by_cases h : a = a₀
    · subst h
      simp [Finset.mem_range.2 hb₀]
    · simp [h]
  rw [Finset.sum_congr rfl hs]
  simp [Finset.mem_range.2 ha₀]

end FidelityStatement

end Langlands
