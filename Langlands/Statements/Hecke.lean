/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.ClassField
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units

/-!
# Hecke's functional equation

This file states Hecke's theorem in the form proved in Tate's thesis: the completed L-function of a Hecke character of a number field has a meromorphic continuation to $\mathbb{C}$ and satisfies $\Lambda(s, \chi) = \varepsilon(s, \chi) \Lambda(1 - s, \chi^{-1})$.

* `Langlands.HeckeCharacter K` is the group of continuous homomorphisms $C_K \to \mathbb{C}^\times$ from the idele class group of $K$. They may have finite or infinite order and need not be unitary.
* `Langlands.HeckeCharacter.finiteComponent` and `Langlands.HeckeCharacter.infiniteComponent` are the local components $\chi_v$, the composites with the maps $K_v^\times \to C_K$.
* `Langlands.HeckeCharacter.IsUnramifiedAt` says that $\chi_v$ is trivial on $\mathcal{O}_v^\times$, and `Langlands.HeckeCharacter.conductor` is the conductor $\mathfrak{f}_\chi = \prod_v \mathfrak{p}_v^{a_v}$, where $a_v$ is the least $m$ such that $\chi_v$ is trivial on $1 + \mathfrak{p}_v^m$ (with $1 + \mathfrak{p}_v^0 = \mathcal{O}_v^\times$).
* `Langlands.HeckeCharacter.finiteLFunction` is the Euler product $\prod_{v \nmid \mathfrak{f}_\chi} (1 - \chi_v(\varpi_v) N(v)^{-s})^{-1}$.
* `Langlands.HeckeCharacter.IsArchimedeanParameter` records the type of $\chi_v$ at an infinite place, and `Langlands.HeckeCharacter.gammaFactor` is the product of the archimedean factors $\Gamma_\mathbb{R}(s + t_v + a_v)$ and $\Gamma_\mathbb{C}(s + t_v + |n_v| / 2)$.
* `Langlands.HeckeFunctionalEquation` is the theorem.
* `Langlands.ArchimedeanParametersExist` says that every Hecke character has archimedean parameters, so that the theorem is not vacuous.

## Implementation notes

The idele group of Mathlib is the group of units of the adele ring, with the topology of the units of a topological ring (induced by $x \mapsto (x, x^{-1})$). This is the restricted product topology. The idele class group has the quotient topology.

The archimedean parameters are data in the statement rather than a definition, to avoid the classification of the continuous characters of $\mathbb{R}^\times$ and $\mathbb{C}^\times$ inside a definition. At a real place they are $a \in \{0, 1\}$ and $t \in \mathbb{C}$ with $\chi_v(x) = \mathrm{sign}(x)^a |x|^t$; at a complex place they are $n \in \mathbb{Z}$ and $t \in \mathbb{C}$ with $\chi_v(z) = (z / |z|)^n |z|_\mathbb{C}^t$, where $|z|_\mathbb{C} = |z|^2$. Both cases are one formula through the embedding $K_v \to \mathbb{C}$ and the multiplicity of the place. These parameters are unique, so the Gamma factor depends only on $\chi$. Their existence is `ArchimedeanParametersExist`, which is stated and not proved here.

The uniformizer $\varpi_v$ is an element of $K$ of valuation one at $v$, chosen once. At an unramified place the value $\chi_v(\varpi_v)$ does not depend on the choice.

## References

* J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in Algebraic number theory (Cassels and Frohlich, eds.), 1967.
* J. Neukirch, Algebraic number theory, chapter VII, section 8.
-/

namespace Langlands

open NumberField IsDedekindDomain

open scoped Classical

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A Hecke character of a number field $K$: a continuous homomorphism from the idele class group of $K$ to $\mathbb{C}^\times$. -/
abbrev HeckeCharacter : Type u :=
  ContinuousMonoidHom (IdeleClassGroup (𝓞 K) K) ℂˣ

/-- The norm of an idele: the product of its normalized local absolute values. -/
noncomputable def ideleNorm (x : IdeleGroup (𝓞 K) K) : ℝ :=
  ‖(x : AdeleRing (𝓞 K) K)‖

namespace HeckeCharacter

variable {K} (χ : HeckeCharacter K)

/-- The local component $\chi_v : K_v^\times \to \mathbb{C}^\times$ at a finite place $v$. -/
noncomputable def finiteComponent (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).comp (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v)

/-- The local component $\chi_v : K_v^\times \to \mathbb{C}^\times$ at an infinite place $v$. -/
noncomputable def infiniteComponent (v : InfinitePlace K) : v.Completionˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).comp (IdeleClassGroup.ofCompletion (𝓞 K) K v)

/-- The character $\chi_v$ is trivial on the group $1 + \mathfrak{p}_v^m$ of units $x$ of $\mathcal{O}_v$ with $v(x - 1) \geq m$. For $m = 0$ this group is $\mathcal{O}_v^\times$. -/
def IsTrivialOnHigherUnits (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) : Prop :=
  ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 →
    Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) →
      χ.finiteComponent v x = 1

/-- The character is unramified at $v$ if $\chi_v$ is trivial on $\mathcal{O}_v^\times$. -/
def IsUnramifiedAt (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  χ.IsTrivialOnHigherUnits v 0

/-- The exponent of the conductor at $v$: the least $m$ such that $\chi_v$ is trivial on $1 + \mathfrak{p}_v^m$. Such an $m$ exists because $\chi$ is continuous (this is not proved here). -/
noncomputable def conductorExponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sInf {m | χ.IsTrivialOnHigherUnits v m}

/-- The conductor $\mathfrak{f}_\chi = \prod_v \mathfrak{p}_v^{a_v}$. The exponent $a_v$ is zero for almost all $v$ because $\chi$ is continuous (this is not proved here). -/
noncomputable def conductor : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ χ.conductorExponent v

end HeckeCharacter

/-- A uniformizer at $v$: an element of $K$ of valuation one at $v$, chosen once. -/
noncomputable def uniformizer (v : HeightOneSpectrum (𝓞 K)) : K :=
  (v.valuation_exists_uniformizer K).choose

theorem uniformizer_ne_zero (v : HeightOneSpectrum (𝓞 K)) : uniformizer K v ≠ 0 := by
  intro h
  have := (v.valuation_exists_uniformizer K).choose_spec
  rw [← uniformizer, h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- The uniformizer as a unit of the completion $K_v$. -/
noncomputable def localUniformizer (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
    (Units.mk0 (uniformizer K v) (uniformizer_ne_zero K v))

namespace HeckeCharacter

variable {K} (χ : HeckeCharacter K)

/-- The local L-factor at a finite place $v$: $(1 - \chi_v(\varpi_v) N(v)^{-s})^{-1}$ if $\chi$ is unramified at $v$, and $1$ otherwise. -/
noncomputable def localFactor (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  if χ.IsUnramifiedAt v then
    (1 - (χ.finiteComponent v (localUniformizer K v) : ℂ) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

/-- The finite Hecke L-function, as the Euler product of the local factors. It converges for $\mathrm{Re}(s) > 1 - \sigma$, where $|\chi| = \|\cdot\|^\sigma$. -/
noncomputable def finiteLFunction (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 K), χ.localFactor v s

/-- The parameters of $\chi_v$ at an infinite place $v$. With $\iota : K_v \to \mathbb{C}$ the embedding of the completion, $\chi_v(x) = (\iota(x) / |\iota(x)|)^n |\iota(x)|^{m_v t}$, where $m_v$ is $1$ at a real place and $2$ at a complex place. At a real place $n$ is $0$ or $1$. -/
structure IsArchimedeanParameter (v : InfinitePlace K) (n : ℤ) (t : ℂ) : Prop where
  /-- At a real place the sign exponent is $0$ or $1$. -/
  isReal : v.IsReal → n = 0 ∨ n = 1
  /-- The formula for $\chi_v$. -/
  eq : ∀ x : v.Completionˣ,
    (χ.infiniteComponent v x : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding v x /
          (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ)) ^ n *
        (‖InfinitePlace.Completion.extensionEmbedding v x‖ : ℂ) ^ ((v.mult : ℂ) * t)

end HeckeCharacter

/-- The archimedean factor of the completed L-function for parameters $(n_v, t_v)$: the product of $\Gamma_\mathbb{R}(s + t_v + n_v)$ over the real places and of $\Gamma_\mathbb{C}(s + t_v + |n_v| / 2)$ over the complex places. -/
noncomputable def gammaFactor (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace K,
    if v.IsReal then Complex.Gammaℝ (s + t v + n v)
    else Complex.Gammaℂ (s + t v + ((|n v| : ℤ) : ℂ) / 2)

namespace HeckeCharacter

variable {K} (χ : HeckeCharacter K)

/-- The completed Hecke L-function $\Lambda(s, \chi) = L_\infty(s, \chi) L(s, \chi)$ for archimedean parameters $(n_v, t_v)$ of $\chi$. -/
noncomputable def completedLFunction (n : InfinitePlace K → ℤ) (t : InfinitePlace K → ℂ) (s : ℂ) :
    ℂ :=
  gammaFactor K n t s * χ.finiteLFunction s

end HeckeCharacter

/-- A sanity check: the trivial character has the archimedean parameters $n = 0$ and $t = 0$ at every infinite place. -/
theorem HeckeCharacter.isArchimedeanParameter_one (v : InfinitePlace K) :
    (1 : HeckeCharacter K).IsArchimedeanParameter v 0 0 :=
  ⟨fun _ => Or.inl rfl, fun x => by simp [HeckeCharacter.infiniteComponent]⟩

/-- A sanity check: the trivial character is unramified at every finite place. -/
theorem HeckeCharacter.isUnramifiedAt_one (v : HeightOneSpectrum (𝓞 K)) :
    (1 : HeckeCharacter K).IsUnramifiedAt v :=
  fun x _ _ => by simp [HeckeCharacter.finiteComponent]

/-- A sanity check: the conductor of the trivial character is the unit ideal. -/
theorem HeckeCharacter.conductor_one : (1 : HeckeCharacter K).conductor = 1 := by
  have h (v : HeightOneSpectrum (𝓞 K)) : (1 : HeckeCharacter K).conductorExponent v = 0 :=
    Nat.sInf_eq_zero.mpr (Or.inl (HeckeCharacter.isUnramifiedAt_one K v))
  simp only [HeckeCharacter.conductor, h, pow_zero]
  exact finprod_one

/-- Every Hecke character has archimedean parameters at every infinite place. This is the classification of the continuous characters of $\mathbb{R}^\times$ and $\mathbb{C}^\times$. It is stated here so that `HeckeFunctionalEquation` is seen not to be vacuous, and it is not proved here. -/
def ArchimedeanParametersExist : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (χ : HeckeCharacter K) (v : InfinitePlace K),
    ∃ (n : ℤ) (t : ℂ), χ.IsArchimedeanParameter v n t

/-- Hecke's theorem, as proved in Tate's thesis. Let $\chi$ be a Hecke character of a number field $K$, with archimedean parameters $(n, t)$, and let $(n', t')$ be archimedean parameters of $\chi^{-1}$. Then there is a real number $\sigma$ with $|\chi| = \|\cdot\|^\sigma$, and there are functions $\Lambda$ and $\Lambda'$, meromorphic on $\mathbb{C}$, that agree with the completed L-functions of $\chi$ and $\chi^{-1}$ on the half planes of convergence of the Euler products, and a complex number $W$ of absolute value one, such that $\Lambda(s) = W (|d_K| N(\mathfrak{f}_\chi))^{1/2 - s - \sigma} \Lambda'(1 - s)$. Moreover $\Lambda$ is entire, unless $\chi = \|\cdot\|^{s_0}$, in which case $\Lambda$ has simple poles at $-s_0$ and $1 - s_0$ and no other poles.

The textbook form is $\Lambda(s, \chi) = \varepsilon(s, \chi) \Lambda(1 - s, \chi^{-1})$ with $\varepsilon(s, \chi) = W(\chi_0) (|d_K| N(\mathfrak{f}_\chi))^{1/2 - s - \sigma}$, where $\chi = \chi_0 \|\cdot\|^\sigma$ and $\chi_0$ is unitary. For unitary $\chi$ one has $\sigma = 0$ and $\chi^{-1} = \bar\chi$, which is the form of Neukirch VII.8.5. The statement differs from the textbook in these points. The archimedean parameters are hypotheses, and their existence is `ArchimedeanParametersExist`. The analytic continuation is a function that is equal to the Euler product on a half plane, rather than a function defined by the theorem. The functional equation is an identity of functions on all of $\mathbb{C}$; at a pole the values of $\Lambda$ and $\Lambda'$ are free, and the identity there is a choice of these values. The root number $W$ is not identified with the product of the local root numbers. -/
def HeckeFunctionalEquation : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (χ : HeckeCharacter K)
    (n n' : InfinitePlace K → ℤ) (t t' : InfinitePlace K → ℂ),
    (∀ v, χ.IsArchimedeanParameter v (n v) (t v)) →
    (∀ v, χ⁻¹.IsArchimedeanParameter v (n' v) (t' v)) →
    ∃ σ : ℝ, (∀ x : IdeleGroup (𝓞 K) K, ‖(χ x : ℂ)‖ = ideleNorm K x ^ σ) ∧
    ∃ (Λ Λ' : ℂ → ℂ) (W : ℂ),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λ' Set.univ ∧
      (∀ s : ℂ, 1 - σ < s.re → Λ s = χ.completedLFunction n t s) ∧
      (∀ s : ℂ, 1 + σ < s.re → Λ' s = χ⁻¹.completedLFunction n' t' s) ∧
      ‖W‖ = 1 ∧
      (∀ s : ℂ, Λ s =
        W * (((|discr K| : ℤ) : ℂ) * (Ideal.absNorm χ.conductor : ℂ)) ^ (1 / 2 - s - σ) *
          Λ' (1 - s)) ∧
      ((∀ s : ℂ, AnalyticAt ℂ Λ s) ∨
        ∃ s₀ : ℂ, (∀ x : IdeleGroup (𝓞 K) K, (χ x : ℂ) = (ideleNorm K x : ℂ) ^ s₀) ∧
          (∀ s : ℂ, s ≠ -s₀ → s ≠ 1 - s₀ → AnalyticAt ℂ Λ s) ∧
          meromorphicOrderAt Λ (-s₀) = -1 ∧ meromorphicOrderAt Λ (1 - s₀) = -1)

end Langlands
