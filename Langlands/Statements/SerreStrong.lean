/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Galois

/-!
# Serre's modularity conjecture, strong form

Let $p$ be a prime and let $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$ be continuous, odd and irreducible. Serre conjectured that $\bar\rho$ comes from a newform of level $N(\bar\rho)$, the Artin conductor of $\bar\rho$ away from $p$, and of weight $k(\bar\rho)$, a weight that depends only on the restriction of $\bar\rho$ to an inertia group at $p$. Khare and Wintenberger proved the conjecture, with Kisin for $p = 2$. The weak form, with some level and some weight, is `Langlands.SerreModularityWeak`.

## Main definitions

* `Langlands.ramificationGroup`: the lower ramification group $G_i = \{\sigma \in \mathrm{Gal}(L/\mathbb{Q}) : \sigma(x) \equiv x \pmod{P^{i+1}} \text{ for all } x \in \mathcal{O}_L\}$ of a prime $P$ of a finite Galois extension $L$ of $\mathbb{Q}$. It is `Ideal.inertia` of $P^{i+1}$.
* `Langlands.invariantsOn`: the subspace $V^H$ of $V = \overline{\mathbb{F}}_p^2$ of the vectors fixed by $\bar\rho(\sigma)$ for each $\sigma \in G_\mathbb{Q}$ whose image in $\mathrm{Gal}(L/\mathbb{Q})$ is in $H$.
* `Langlands.artinExponent`: the exponent $n(P) = \sum_{i \ge 0} \frac{|G_i|}{|G_0|} \dim (V / V^{G_i})$ of the Artin conductor at $P$, for an $L$ through which $\bar\rho$ factors.
* `Langlands.IsArtinConductorAwayFrom`: $N$ is prime to $p$ and $v_q(N) = n(P)$ for each prime $q \ne p$, each $L$ through which $\bar\rho$ factors and each prime $P$ of $L$ over $q$.
* `Langlands.HasTameInertiaType`: the restriction of $\bar\rho$ to the inertia group $I_Q$ at a prime $Q$ of $\bar{\mathbb{Z}}$ over $p$ is $\theta_n^{e_1} \oplus \theta_n^{e_2}$, where $\theta_n$ is the fundamental character of level $n$.
* `Langlands.IsSerreWeightTame`: Serre's recipe for $k(\bar\rho)$ when $\bar\rho|_{I_p}$ is semisimple, that is tamely ramified.
* `Langlands.SerreModularityTame`: the strong form of the conjecture for the $\bar\rho$ that are tamely ramified at $p$. This is a full statement.
* `Langlands.SerreWeightRule`: an interface for the full weight $k(\bar\rho)$, with the condition that it is Serre's weight in the tame case.
* `Langlands.SerreModularity`: the strong form of the conjecture, with the weight as a parameter. This is a shape.

## Main results

* `Langlands.SerreModularity.tame`: the shape gives the full statement in the tame case, for each weight rule.

## The level

The kernel of $\bar\rho$ is open, so $\bar\rho$ factors through $\mathrm{Gal}(L/\mathbb{Q})$ for a finite Galois extension $L$. Let $P$ be a prime of $\mathcal{O}_L$ over $q$ and let $G_i$ be the lower ramification groups of $P$. These are the ramification groups of the completion $L_P / \mathbb{Q}_q$, since $\mathcal{O}_L$ is dense in $\mathcal{O}_{L_P}$. The exponent of the Artin conductor at $q$ is $n(q) = \sum_{i \ge 0} \frac{|G_i|}{|G_0|} \dim (V / V^{G_i})$ (Serre, Local fields, VI, section 2). The groups $G_i$ are trivial for large $i$, so the sum is finite. By the theorem of Artin, $n(q)$ is an integer, and it does not depend on $L$ or on $P$. The statement does not use these theorems: it asks that $v_q(N) = n(P)$ for each choice. Then $N(\bar\rho) = \prod_{q \ne p} q^{n(q)}$.

## The weight

Let $Q$ be a maximal ideal of $\bar{\mathbb{Z}}$ over $p$, with inertia group $I_Q$. Let $\varpi \in \bar{\mathbb{Z}}$ with $\varpi^{p^n - 1} = p$. For $\sigma \in I_Q$, the quotient $\zeta = \sigma(\varpi)/\varpi$ is a root of unity of order dividing $p^n - 1$, and the fundamental character of level $n$ is $\theta_n(\sigma) = \iota(\zeta \bmod Q)$, for a field embedding $\iota : \bar{\mathbb{Z}}/Q \to \overline{\mathbb{F}}_p$. It does not depend on $\varpi$. The character $\theta_1$ is the reduction $\omega$ of the cyclotomic character on $I_Q$. A different $\iota$ changes $\theta_2$ to $\theta_2^p$. The recipe below does not change under this, since it is symmetric in the two exponents.

The restriction $\bar\rho|_{I_Q}$ is semisimple if and only if the wild inertia group acts trivially, because the wild inertia group is a pro-$p$ group. In this case Serre's recipe (Serre 1987, sections 2.2 and 2.3) is:
* level 2: if $\bar\rho|_{I_Q} \cong \theta_2^{a + pb} \oplus \theta_2^{b + pa}$ with $0 \le a < b \le p - 1$, then $k(\bar\rho) = 1 + pa + b$;
* level 1: if $\bar\rho|_{I_Q} \cong \omega^\alpha \oplus \omega^\beta$ with $0 \le \alpha \le \beta \le p - 2$, then $k(\bar\rho) = 1 + p\alpha + \beta$, except that $k(\bar\rho) = p$ for $\alpha = \beta = 0$, the case where $\bar\rho$ is unramified at $p$.

## What is not stated

The weight in the wild case is not defined here. This is the case where $\bar\rho|_{I_Q} \cong \begin{pmatrix} \omega^\beta & * \\ 0 & \omega^\alpha \end{pmatrix}$ is not semisimple (Serre 1987, section 2.4). The recipe there depends on whether $\beta = \alpha + 1$, and then on whether $\bar\rho$ is peu ramifié or très ramifié at $p$. This is a condition on the Kummer extension of $\mathbb{Q}_p^{ur}(\mu_p)$ cut out by the extension class $*$: it is peu ramifié if this extension is generated by $p$-th roots of units. There are more special rules for $p = 2$. For this reason `SerreModularity` takes the weight as a parameter of type `SerreWeightRule`. The structure fixes the weight only in the tame case, so `SerreModularity` is a shape. The statement `SerreModularityTame` is the full strong form for the $\bar\rho$ that are tamely ramified at $p$.

The nebentypus $\varepsilon(\bar\rho)$ is not fixed. It is determined by the conditions at Frobenius: $\theta(\chi(q)) q^{k-1} = \det \bar\rho(\mathrm{Frob}_q)$ for almost all $q$. As in `Langlands.SerreModularityWeak`, the form is a normalized eigenform of level $N$. By the theorem of Carayol and Livné, the level of a newform whose representation reduces to $\bar\rho$ is divisible by $N(\bar\rho)$, so an eigenform of level $N(\bar\rho)$ has the eigenvalues of a newform of level exactly $N(\bar\rho)$.

## References

* J.-P. Serre, Sur les représentations modulaires de degré 2 de Gal(Q̄/Q), Duke Math. J. 54 (1987), sections 1 to 3.
* J.-P. Serre, Local fields, chapters IV and VI.
* B. Edixhoven, The weight in Serre's conjectures on modular forms, Invent. Math. 109 (1992).
* C. Khare and J.-P. Wintenberger, Serre's modularity conjecture (I) and (II), Invent. Math. 178 (2009).
* M. Kisin, Modularity of 2-adic Barsotti-Tate representations, Invent. Math. 178 (2009).
* H. Carayol, Sur les représentations l-adiques associées aux formes modulaires de Hilbert, Ann. Sci. ENS 19 (1986), and R. Livné, On the conductors of mod l Galois representations coming from modular forms, J. Number Theory 31 (1989).
-/

namespace Langlands

open NumberField CongruenceSubgroup

open scoped MatrixGroups

/-- The residual coefficient field $\overline{\mathbb{F}}_p$. -/
local notation "𝔽bar" p => AlgebraicClosure (ZMod p)

/-! ### The Artin conductor away from p -/

section Conductor

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

/-- The lower ramification group $G_i = \{\sigma : \sigma(x) \equiv x \pmod{P^{i+1}} \text{ for all } x \in \mathcal{O}_L\}$ of a prime $P$ of $\mathcal{O}_L$. For $i = 0$ it is the inertia group of $P$. -/
noncomputable def ramificationGroup (P : Ideal (𝓞 L)) (i : ℕ) : Subgroup Gal(L/ℚ) :=
  (P ^ (i + 1)).inertia Gal(L/ℚ)

variable [IsGalois ℚ L] {p : ℕ} [Fact p.Prime]

/-- The subspace $V^H$ of $V = \overline{\mathbb{F}}_p^2$ of the vectors that are fixed by $\bar\rho(\sigma)$ for each $\sigma \in G_\mathbb{Q}$ whose restriction to $L$ is in $H$. If $\bar\rho$ factors through $\mathrm{Gal}(L/\mathbb{Q})$, this is the space of the invariants of $H$. -/
noncomputable def invariantsOn
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)) (H : Subgroup Gal(L/ℚ)) :
    Submodule (𝔽bar p) (Fin 2 → 𝔽bar p) :=
  ⨅ (σ : Field.absoluteGaloisGroup ℚ) (_ : AlgEquiv.restrictNormalHom L σ ∈ H),
    LinearMap.ker (Matrix.toLin' (ρ σ : Matrix (Fin 2) (Fin 2) (𝔽bar p)) - LinearMap.id)

/-- The exponent $n(P) = \sum_{i \ge 0} \frac{|G_i|}{|G_0|} \dim (V / V^{G_i})$ of the Artin conductor of $\bar\rho$ at a prime $P$ of $\mathcal{O}_L$, where $G_i$ are the lower ramification groups of $P$. The sum is finite, since $G_i$ is trivial for large $i$. -/
noncomputable def artinExponent
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)) (P : Ideal (𝓞 L)) : ℚ :=
  ∑ᶠ i : ℕ, ((Nat.card (ramificationGroup L P i) : ℚ) / Nat.card (ramificationGroup L P 0)) *
    (2 - Module.finrank (𝔽bar p) (invariantsOn L ρ (ramificationGroup L P i)) : ℚ)

end Conductor

/-- The number $N$ is the Artin conductor of $\bar\rho$ away from $p$: it is prime to $p$, and $v_q(N) = n(P)$ for each prime $q \ne p$, each finite Galois extension $L$ of $\mathbb{Q}$ such that $\bar\rho$ is trivial on $G_L$, and each maximal ideal $P$ of $\mathcal{O}_L$ over $q$. -/
def IsArtinConductorAwayFrom (p : ℕ) [Fact p.Prime]
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)) (N : ℕ) : Prop :=
  ¬ p ∣ N ∧
    ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L],
        (∀ σ : Field.absoluteGaloisGroup ℚ,
          (∀ x : L, σ • (x : AlgebraicClosure ℚ) = x) → ρ σ = 1) →
        ∀ P : Ideal (𝓞 L), P.IsMaximal → P.LiesOver (Ideal.span {(q : ℤ)}) →
          (padicValNat q N : ℚ) = artinExponent L ρ P

/-! ### Serre's weight in the tame case -/

/-- The restriction of $\bar\rho$ to the inertia group $I_Q$ is $\theta_n^{e_1} \oplus \theta_n^{e_2}$, where $\theta_n$ is the fundamental character of level $n$. There are an embedding $\iota : \bar{\mathbb{Z}}/Q \to \overline{\mathbb{F}}_p$, an element $\varpi$ with $\varpi^{p^n - 1} = p$ and a matrix $g$ such that $g \bar\rho(\sigma) g^{-1} = \mathrm{diag}(\iota(\bar\zeta)^{e_1}, \iota(\bar\zeta)^{e_2})$ for each $\sigma \in I_Q$, where $\zeta = \sigma(\varpi)/\varpi$. -/
def HasTameInertiaType (p : ℕ) [Fact p.Prime] (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p))
    (Q : Ideal AlgebraicIntegers) (n e₁ e₂ : ℕ) : Prop :=
  ∃ (ι : AlgebraicIntegers ⧸ Q →+* 𝔽bar p) (ϖ : AlgebraicIntegers) (g : GL (Fin 2) (𝔽bar p)),
    ϖ ^ (p ^ n - 1) = (p : AlgebraicIntegers) ∧
    ∀ σ ∈ Q.inertia (Field.absoluteGaloisGroup ℚ), ∀ ζ : AlgebraicIntegers, σ • ϖ = ζ * ϖ →
      ((g * ρ σ * g⁻¹ : GL (Fin 2) (𝔽bar p)) : Matrix (Fin 2) (Fin 2) (𝔽bar p)) =
        Matrix.diagonal ![ι (Ideal.Quotient.mk Q ζ) ^ e₁, ι (Ideal.Quotient.mk Q ζ) ^ e₂]

/-- Serre's weight $k(\bar\rho) = k$ in the tame case (Serre 1987, sections 2.2 and 2.3). For a maximal ideal $Q$ of $\bar{\mathbb{Z}}$ over $p$, either $\bar\rho|_{I_Q} \cong \theta_2^{a + pb} \oplus \theta_2^{b + pa}$ with $0 \le a < b \le p - 1$ and $k = 1 + pa + b$, or $\bar\rho|_{I_Q} \cong \omega^\alpha \oplus \omega^\beta$ with $0 \le \alpha \le \beta \le p - 2$ and $k = 1 + p\alpha + \beta$, where $k = p$ if $\alpha = \beta = 0$. -/
def IsSerreWeightTame (p : ℕ) [Fact p.Prime] (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p))
    (k : ℕ) : Prop :=
  ∃ Q : Ideal AlgebraicIntegers, Q.IsMaximal ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧
    ((∃ a b : ℕ, a < b ∧ b ≤ p - 1 ∧ HasTameInertiaType p ρ Q 2 (a + p * b) (b + p * a) ∧
        k = 1 + p * a + b) ∨
      (∃ α β : ℕ, α ≤ β ∧ β ≤ p - 2 ∧ HasTameInertiaType p ρ Q 1 α β ∧
        k = if β = 0 then p else 1 + p * α + β))

/-! ### The statements -/

/-- The representation $\bar\rho$ is the reduction of the eigenform $f$ of weight $k$ and character $\chi$ through $\theta : \mathbb{Z}[a_n(f), \chi] \to \overline{\mathbb{F}}_p$: $\mathrm{tr}\, \bar\rho(\sigma) = \theta(a_q(f))$ and $\det \bar\rho(\sigma) = \theta(\chi(q)) q^{k-1}$ for each arithmetic Frobenius $\sigma$ at a prime $q \nmid Np$. This is the conclusion of `Langlands.SerreModularityWeak`. -/
def IsReductionOf (p : ℕ) [Fact p.Prime] (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p))
    {N : ℕ} {k : ℤ} (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (θ : coeffRing f χ →+* 𝔽bar p) :
    Prop :=
  ∀ q : ℕ, q.Prime → ¬ q ∣ N * p → ∀ σ, IsFrobeniusAt q σ →
    (ρ σ : Matrix (Fin 2) (Fin 2) (𝔽bar p)).trace =
      θ ⟨qCoeffGamma1 f q, qCoeffGamma1_mem_coeffRing f χ q⟩ ∧
    (ρ σ : Matrix (Fin 2) (Fin 2) (𝔽bar p)).det =
      θ ⟨χ (q : ZMod N), character_mem_coeffRing f χ q⟩ * (q : 𝔽bar p) ^ (k - 1)

/-- **Serre's modularity conjecture, strong form, tame case** (Khare and Wintenberger, with Kisin for $p = 2$). Let $p$ be a prime and let $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$ be continuous, irreducible and odd. Let $N = N(\bar\rho)$ be the Artin conductor of $\bar\rho$ away from $p$. Assume that $\bar\rho$ is tamely ramified at $p$, with Serre weight $k = k(\bar\rho)$ given by `IsSerreWeightTame`. Then there are a character $\chi$ modulo $N$, a normalized eigenform $f$ of weight $k$ on $\Gamma_1(N)$ with character $\chi$ and a ring homomorphism $\theta : \mathbb{Z}[a_n(f), \chi] \to \overline{\mathbb{F}}_p$ such that $\bar\rho$ is the reduction of $f$ through $\theta$.

This is a full statement, for the $\bar\rho$ that are tamely ramified at $p$. -/
def SerreModularityTame : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)),
    IsOpen (ρ.ker : Set (Field.absoluteGaloisGroup ℚ)) → IsIrreducibleRep ρ → IsOddRep ρ →
    ∀ N k : ℕ, IsArtinConductorAwayFrom p ρ N → IsSerreWeightTame p ρ k →
      ∃ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
        (θ : coeffRing f χ →+* 𝔽bar p),
        IsNormalizedEigenformWithCharacter f χ ∧ IsReductionOf p ρ χ f θ

/-- An interface for Serre's weight $k(\bar\rho)$ in all cases. The weight in the wild case (Serre 1987, section 2.4, with the distinction between peu ramifié and très ramifié) is not defined in the project, so it is a field. The structure asks only that the weight is the one of `IsSerreWeightTame` in the tame case. -/
structure SerreWeightRule where
  /-- The weight $k(\bar\rho)$. -/
  weight : ∀ (p : ℕ) [Fact p.Prime], (Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)) → ℕ
  /-- In the tame case the weight is Serre's weight. -/
  tame : ∀ (p : ℕ) [Fact p.Prime] (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p))
    (k : ℕ), IsSerreWeightTame p ρ k → weight p ρ = k

/-- **The shape of Serre's modularity conjecture, strong form** (Khare and Wintenberger, with Kisin for $p = 2$). Let $\bar\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{F}}_p)$ be continuous, irreducible and odd, and let $N = N(\bar\rho)$ be its Artin conductor away from $p$. Then there are a character $\chi$ modulo $N$, a normalized eigenform $f$ of weight $k(\bar\rho)$ on $\Gamma_1(N)$ with character $\chi$ and a ring homomorphism $\theta : \mathbb{Z}[a_n(f), \chi] \to \overline{\mathbb{F}}_p$ such that $\bar\rho$ is the reduction of $f$ through $\theta$. The weight $k(\bar\rho)$ is the field `weight` of the parameter `w`.

This is a shape, not a statement: the weight in the wild case is a parameter. With the weight of Serre 1987, section 2, as the parameter, it is the strong form of the conjecture. -/
def SerreModularity (w : SerreWeightRule) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (𝔽bar p)),
    IsOpen (ρ.ker : Set (Field.absoluteGaloisGroup ℚ)) → IsIrreducibleRep ρ → IsOddRep ρ →
    ∀ N : ℕ, IsArtinConductorAwayFrom p ρ N →
      ∃ (χ : DirichletCharacter ℂ N)
        (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (w.weight p ρ))
        (θ : coeffRing f χ →+* 𝔽bar p),
        IsNormalizedEigenformWithCharacter f χ ∧ IsReductionOf p ρ χ f θ

/-- For each weight rule, the shape `SerreModularity` gives the full statement `SerreModularityTame` in the tame case. -/
theorem SerreModularity.tame (w : SerreWeightRule) (h : SerreModularity w) :
    SerreModularityTame := by
  intro p _ ρ hker hirr hodd N k hN hk
  obtain rfl := w.tame p ρ k hk
  exact h p ρ hker hirr hodd N hN

end Langlands
