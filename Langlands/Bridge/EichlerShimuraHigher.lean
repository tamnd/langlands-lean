/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Galois.Profinite
import Langlands.Bridge.AnthropicES
import Langlands.Galois.PseudoCharacter

/-!
# Eichler, Shimura and Deligne for each weight from the weight 2 case, by congruences

This file proves `Langlands.EichlerShimuraDeligne`, the existence of the $\ell$-adic Galois representations of the normalized eigenforms of weight $k \ge 2$, from its weight 2 case `Langlands.Bridge.EichlerShimuraWeightTwo` and four published theorems that enter as named hypotheses. The route is the congruence and pseudo-character argument of Wiles and Taylor.

Let $f$ be a normalized eigenform of weight $k \ge 2$ and level $N$ with character $\chi$, let $\ell$ be a prime and let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$. For each $n$ the theorem of Shimura and Hida gives a ring homomorphism from the Hecke algebra of weight 2 and level $N \ell^m$ to $\mathcal{O}/\ell^n$ that sends $T_a$ to $a_a(f)$ and $d \langle d \rangle$ to $\chi(d) d^{k-1}$. Through the decomposition of the Hecke algebra by the eigenforms $g_1, \dots, g_r$ of weight 2, this homomorphism is $T \mapsto \sum_i c_i \lambda_T(g_i)$ modulo $\ell^n$ (`WeightTwoCongruence`). The weight 2 case gives representations $\rho_i$ for the $g_i$. The functions $T_n = \sum_i c_i \operatorname{tr} \rho_i$ and $D_n = \sum_i c_i \det \rho_i$ are continuous, and they are pseudo-characters of dimension 2 modulo $\ell^n$: at the Frobenius elements this follows from the Hecke relations of the $g_i$ and of $f$, and the Frobenius elements are dense (`FrobeniusDense`). The functions $T_n$ converge uniformly to a continuous pseudo-character $(T, D)$ with values in a finite extension of $\mathbb{Q}_\ell$ (`CoefficientField`), with $T(\mathrm{Frob}_p) = \iota^{-1}(a_p(f))$ and $D(\mathrm{Frob}_p) = \iota^{-1}(\chi(p) p^{k-1})$. The theorem of Taylor (`PseudoCharTwoRepresentation`) gives the representation.

## Main definitions

* `Langlands.Bridge.FrobeniusDense`: the Frobenius elements at the primes $p \nmid M$ are dense in $G_\mathbb{Q}$. This is a consequence of the theorem of Chebotarev.
* `Langlands.Bridge.WeightTwoCongruence`: the congruence modulo $\ell^n$ between the Hecke eigenvalues of $f$ and the Hecke algebra of weight 2 and level $N \ell^m$, in the form of a combination of eigenforms of weight 2. This is the theorem of Shimura and Hida.
* `Langlands.Bridge.CoefficientField`: the values $\iota^{-1}(a_p(f))$ and $\iota^{-1}(\chi(p) p^{k-1})$ lie in a finite extension of $\mathbb{Q}_\ell$.
* `Langlands.Bridge.PseudoCharTwoRepresentation`: a continuous pseudo-character of dimension 2 of $G_\mathbb{Q}$ with values in a finite extension of $\mathbb{Q}_\ell$ is the trace and the determinant of a continuous semisimple representation over $\overline{\mathbb{Q}}_\ell$. This is the theorem of Taylor.

## Main results

* `Langlands.Bridge.norm_mul_sub_mul_le`: $\|xy - ab\| \le \varepsilon (2B + 1)$ if $\|x - a\|, \|y - b\| \le \varepsilon \le 1$ and $\|a\|, \|b\| \le B$.
* `Langlands.Bridge.exists_approx_weightTwo`: the pseudo-characters modulo $\ell^n$ that the weight 2 representations and the congruence give, with their properties.
* `Langlands.Bridge.eichlerShimuraDeligne_of_congruence`: `EichlerShimuraWeightTwo`, `WeightTwoCongruence`, `CoefficientField`, `FrobeniusDense` and `PseudoCharTwoRepresentation` give `EichlerShimuraDeligne`.

## A remark on the congruence

The congruence is not a congruence of $f$ with a single eigenform of weight 2 for each $n$. Such a congruence is false for $k > 2$ and $n$ large. If $g$ is an eigenform of weight 2 and level $N \ell^m$ with character $\psi$ and $a_q(g) \equiv a_q(f)$ modulo $\ell^n$ for all $q \nmid N \ell$, then the determinants of the representations give $\psi(q) q \equiv \chi(q) q^{k-1}$ modulo $\ell^n$. For $q \equiv 1 \pmod N$ and $q \equiv 1 + \ell \pmod{\ell^2}$ this asks that the root of unity $\psi(q)$ is within $\ell^{-n}$ of $q^{k-2}$, while $|q^{k-2} - 1| = |k - 2|_\ell\, \ell^{-1}$ and each root of unity $\zeta \ne 1$ of $\ell$-power order has $|\zeta - 1| > \ell^{-1}$ (for $\ell$ odd). The correct statement is about the Hecke algebra, in which $\langle d \rangle$ acts modulo $\ell^n$ by $\chi(d) d^{k-2}$, a value that is not a root of unity. Through the eigenforms this is a linear combination $\sum_i c_i \lambda_T(g_i)$, as in `WeightTwoCongruence`.

## References

* G. Shimura, Introduction to the arithmetic theory of automorphic functions, 1971, Theorem 3.52.
* H. Hida, Elementary theory of L-functions and Eisenstein series, LMS Student Texts 26, 1993, Chapter 7.
* H. Hida, Galois representations into $GL_2(\mathbb{Z}_p[[X]])$ attached to ordinary cusp forms, Invent. Math. 85 (1986), Section 1.
* A. Wiles, On ordinary $\lambda$-adic representations associated to modular forms, Invent. Math. 94 (1988), Section 2.
* R. Taylor, Galois representations associated to Siegel modular forms of low weight, Duke Math. J. 63 (1991), Section 1.
* G. Chenevier, The p-adic analytic space of pseudocharacters of a profinite group and pseudorepresentations over arbitrary rings, LMS Lecture Note Series 414 (2014), Lemma 7.7 and Theorem 2.12.
* J.-P. Serre, Abelian l-adic representations and elliptic curves, 1968, Chapter I, Section 2.2.
* J. Neukirch, Algebraic number theory, Chapter VII, Theorem 13.4.
-/

noncomputable section

namespace Langlands.Bridge

open Langlands.Galois CongruenceSubgroup Filter Topology

open scoped MatrixGroups ModularForm

/-- **The density of the Frobenius elements** (Chebotarev). For each $M \ge 1$, the set of the arithmetic Frobenius elements at the primes $p \nmid M$ is dense in $G_\mathbb{Q}$ with the Krull topology. A basic open set is a coset $\tau H$ of the subgroup $H$ that fixes a finite Galois extension $L$ of $\mathbb{Q}$, and the theorem of Chebotarev gives infinitely many primes $p$ with a prime of $L$ over $p$ whose Frobenius is $\tau|_L$. Reference: Neukirch, Algebraic number theory, Chapter VII, Theorem 13.4; Serre, Abelian l-adic representations, Chapter I, Section 2.2, Corollary 2 to the theorem of Chebotarev. -/
def FrobeniusDense : Prop :=
  ∀ M : ℕ, 0 < M →
    Dense {σ : Field.absoluteGaloisGroup ℚ | ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ IsFrobeniusAt p σ}

/-- **The congruence with the Hecke algebra of weight 2** (Shimura, Hida). Let $f$ be a normalized eigenform of weight $k \ge 2$ on $\Gamma_1(N)$ with character $\chi$, let $\ell$ be a prime, let $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ and let $n \ge 0$. Then there are $m$, normalized eigenforms $g_1, \dots, g_r$ of weight 2 on $\Gamma_1(N \ell^m)$ with characters $\psi_i$, and $c_1, \dots, c_r \in \mathbb{C}$ such that for all $a, d \ge 1$ prime to $N \ell$, $\sum_i c_i\, \psi_i(d)\, d\, a_a(g_i) \equiv \chi(d)\, d^{k-1}\, a_a(f)$ modulo $\ell^n$, that is $\|\iota^{-1}(\text{difference})\| \le \ell^{-n}$.

The left side is the eigenvalue of the Hecke operator $d \langle d \rangle T_a$ of weight 2 on the form $\sum_i c_i g_i$, and these operators span the Hecke algebra away from $N \ell$. The theorem of Shimura and Hida gives a ring homomorphism $\theta$ from the Hecke algebra of weight 2 and level $N \ell^m$ (for $m \ge n$) to $\mathcal{O}/\ell^n$, with $\theta(T_a) = a_a(f)$ and $\theta(\langle d \rangle) = \chi(d) d^{k-2}$. It comes from the Hecke equivariant embedding of $H^1(\Gamma_1(N), \mathrm{Sym}^{k-2}(\mathcal{O}/\ell^n))$ into $H^1(\Gamma_1(N \ell^m), \mathcal{O}/\ell^n)$ with the twist $d^{k-2}$ (Shapiro's lemma), and from the theorem of Eichler and Shimura in weight 2. The Hecke algebra is semisimple away from the level, so a homomorphism to $\mathcal{O}/\ell^n$, lifted to $\mathcal{O}$ on a $\mathbb{Z}_\ell$-basis and extended linearly, is a linear combination of the eigenvalue maps of the eigenforms. Reference: Hida, Elementary theory of L-functions and Eisenstein series, Chapter 7, Section 7.2; Hida, Invent. Math. 85 (1986), Section 1; Taylor, Duke Math. J. 63 (1991), Section 1. -/
def WeightTwoCongruence : Prop :=
  ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    0 < N → 2 ≤ k → IsNormalizedEigenformWithCharacter f χ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ) (n : ℕ),
      ∃ (m r : ℕ) (g : Fin r → CuspForm (Gamma1 (N * ℓ ^ m) : Subgroup (GL (Fin 2) ℝ)) 2)
        (ψ : Fin r → DirichletCharacter ℂ (N * ℓ ^ m)) (c : Fin r → ℂ),
        (∀ i, IsNormalizedEigenformWithCharacter (g i) (ψ i)) ∧
        ∀ a d : ℕ, a.Coprime (N * ℓ) → d.Coprime (N * ℓ) →
          ‖ι.symm (∑ i, c i * (ψ i (d : ZMod (N * ℓ ^ m)) * (d : ℂ) * qCoeffGamma1 (g i) a)) -
            ι.symm (χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * qCoeffGamma1 f a)‖ ≤ (ℓ : ℝ)⁻¹ ^ n

/-- **The field of coefficients is finite over $\mathbb{Q}_\ell$** (Shimura). For a normalized eigenform $f$ of weight $k \ge 2$ on $\Gamma_1(N)$ with character $\chi$, a prime $\ell$ and $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$, there is a finite dimensional $\mathbb{Q}_\ell$-subspace $E$ of $\overline{\mathbb{Q}}_\ell$ that contains $\iota^{-1}(a_p(f))$ and $\iota^{-1}(\chi(p) p^{k-1})$ for each prime $p \nmid N \ell$. The coefficients $a_n(f)$ and the values of $\chi$ generate a number field $K$, and one takes for $E$ the field $\mathbb{Q}_\ell \cdot \iota^{-1}(K)$. Reference: Shimura, Introduction to the arithmetic theory of automorphic functions, Theorem 3.52; Diamond and Shurman, A first course in modular forms, Section 6.5. -/
def CoefficientField : Prop :=
  ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    0 < N → 2 ≤ k → IsNormalizedEigenformWithCharacter f χ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ ≃+* ℂ),
      ∃ E : Submodule ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
          ι.symm (qCoeffGamma1 f p) ∈ E ∧ ι.symm (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) ∈ E

/-- **Pseudo-characters of dimension 2 come from representations** (Taylor; Rouquier, Nyssen, Chenevier). Let $(t, d)$ be a continuous pseudo-character of dimension 2 of $G_\mathbb{Q}$ with values in $\overline{\mathbb{Q}}_\ell$, such that $t$ takes values in a finite dimensional $\mathbb{Q}_\ell$-subspace. Then there is a continuous representation $\rho : G_\mathbb{Q} \to GL_2(\overline{\mathbb{Q}}_\ell)$ with $\operatorname{tr} \rho = t$ and $\det \rho = d$, and $\rho(h) = 1$ for each $h$ with $t(gh) = t(g)$ for all $g$.

The representation is the semisimple representation with trace $t$. The last property holds for a semisimple representation in characteristic 0: if $t(gh) = t(g)$ for all $g$, then $\rho(h) - 1$ is orthogonal for the trace form to the algebra spanned by $\rho(G)$, and the trace form on a semisimple algebra in characteristic 0 is nondegenerate. Reference: Taylor, Galois representations associated to Siegel modular forms of low weight, Duke Math. J. 63 (1991), Section 1, Theorem 1; Chenevier, LMS Lecture Note Series 414 (2014), Lemma 7.7 (the pairs $(t, d)$ of dimension 2) and Theorem 2.12 (the representation over an algebraically closed field). -/
def PseudoCharTwoRepresentation : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (t d : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ)
    (E : Submodule ℚ_[ℓ] (PadicAlgCl ℓ)), FiniteDimensional ℚ_[ℓ] E → (∀ g, t g ∈ E) →
    Continuous t → Continuous d → IsPseudoCharTwo t d →
    ∃ ρ : Field.absoluteGaloisGroup ℚ →* GL (Fin 2) (PadicAlgCl ℓ), Continuous ρ ∧
      (∀ g, (ρ g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).trace = t g) ∧
      (∀ g, (ρ g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).det = d g) ∧
      ∀ h, (∀ g, t (g * h) = t g) → ρ h = 1

/-- If $\|x - a\| \le \varepsilon$ and $\|y - b\| \le \varepsilon$ with $0 \le \varepsilon \le 1$, and $\|a\|, \|b\| \le B$, then $\|xy - ab\| \le \varepsilon (2B + 1)$. -/
theorem norm_mul_sub_mul_le {R : Type*} [NormedRing R] {x y a b : R} {ε B : ℝ}
    (hx : ‖x - a‖ ≤ ε) (hy : ‖y - b‖ ≤ ε) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hε : ε ≤ 1)
    (hε0 : 0 ≤ ε) : ‖x * y - a * b‖ ≤ ε * (2 * B + 1) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans ha
  have e : x * y - a * b = (x - a) * (y - b) + a * (y - b) + (x - a) * b := by noncomm_ring
  rw [e]
  calc _ ≤ ‖(x - a) * (y - b)‖ + ‖a * (y - b)‖ + ‖(x - a) * b‖ := norm_add₃_le
    _ ≤ ‖x - a‖ * ‖y - b‖ + ‖a‖ * ‖y - b‖ + ‖x - a‖ * ‖b‖ := by
        gcongr <;> exact norm_mul_le _ _
    _ ≤ ε * ε + B * ε + ε * B := by gcongr
    _ ≤ ε * (2 * B + 1) := by nlinarith

/-- A prime $p \nmid N \ell$ does not divide $N \ell^m \ell$. -/
theorem not_dvd_mul_pow_mul {N ℓ m p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N * ℓ) :
    ¬ p ∣ N * ℓ ^ m * ℓ := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact h (dvd_mul_of_dvd_left h2 _)
    · exact h (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h2) _)
  · exact h (dvd_mul_of_dvd_right h1 _)

/-- **The pseudo-characters modulo $\ell^n$.** Let $f$ be a normalized eigenform of weight $k \ge 2$ on $\Gamma_1(N)$ with character $\chi$, let $\ell$ be a prime, $\iota : \overline{\mathbb{Q}}_\ell \cong \mathbb{C}$ and $n \ge 0$, and write $\varepsilon = \ell^{-n}$. From `EichlerShimuraWeightTwo` and `WeightTwoCongruence` there are continuous functions $T, D : G_\mathbb{Q} \to \overline{\mathbb{Q}}_\ell$ and $P, Q, R : G_\mathbb{Q} \times G_\mathbb{Q} \to \overline{\mathbb{Q}}_\ell$ with these properties: $T(gh) = T(hg)$, $Q(g, g^{-1} h) - P(g, h) + T(gh) = 0$, $D(gh) = R(g, h)$, $T(1) = 2 D(1)$, $\|D(1) - 1\| \le \varepsilon$, $T(g\sigma) = T(g)$ for $\sigma$ in an inertia group at $p \nmid N \ell$, and at Frobenius elements $\sigma, \sigma'$ at primes $p, p' \nmid N \ell$ the values $T(\sigma)$, $D(\sigma)$, $P(\sigma, \sigma')$, $Q(\sigma, \sigma')$, $R(\sigma, \sigma')$ are within $\varepsilon$ (within $2 \varepsilon$ for $P$) of $a_p$, $\chi(p) p^{k-1}$, $a_p a_{p'}$, $\chi(p) p^{k-1} a_{p'}$ and $\chi(p) p^{k-1} \chi(p') p'^{k-1}$, through $\iota^{-1}$. One takes $T = \sum_i c_i \operatorname{tr} \rho_i$, $D = \sum_i c_i \det \rho_i$, $P(g, h) = \sum_i c_i \operatorname{tr} \rho_i(g) \operatorname{tr} \rho_i(h)$, $Q(g, h) = \sum_i c_i \det \rho_i(g) \operatorname{tr} \rho_i(h)$ and $R(g, h) = \sum_i c_i \det \rho_i(g) \det \rho_i(h)$. -/
theorem exists_approx_weightTwo (h2 : EichlerShimuraWeightTwo) (hcong : WeightTwoCongruence)
    {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N}
    {f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k} (hN : 0 < N) (hk : 2 ≤ k)
    (hf : IsNormalizedEigenformWithCharacter f χ) (ℓ : ℕ) [Fact ℓ.Prime]
    (ι : PadicAlgCl ℓ ≃+* ℂ) (n : ℕ) :
    ∃ (T D : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ)
      (P Q R : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ),
      Continuous T ∧ Continuous D ∧
      Continuous (fun x : Field.absoluteGaloisGroup ℚ × Field.absoluteGaloisGroup ℚ =>
        P x.1 x.2) ∧
      Continuous (fun x : Field.absoluteGaloisGroup ℚ × Field.absoluteGaloisGroup ℚ =>
        Q x.1 x.2) ∧
      Continuous (fun x : Field.absoluteGaloisGroup ℚ × Field.absoluteGaloisGroup ℚ =>
        R x.1 x.2) ∧
      (∀ g h, T (g * h) = T (h * g)) ∧
      (∀ g h, Q g (g⁻¹ * h) - P g h + T (g * h) = 0) ∧
      (∀ g h, D (g * h) = R g h) ∧
      T 1 = 2 * D 1 ∧ ‖D 1 - 1‖ ≤ (ℓ : ℝ)⁻¹ ^ n ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ Q' : Ideal AlgebraicIntegers, Q'.IsMaximal →
        Q'.LiesOver (Ideal.span {(p : ℤ)}) →
        ∀ σ ∈ Q'.inertia (Field.absoluteGaloisGroup ℚ), ∀ g, T (g * σ) = T g) ∧
      (∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
        ‖T σ - ι.symm (qCoeffGamma1 f p)‖ ≤ (ℓ : ℝ)⁻¹ ^ n ∧
        ‖D σ - ι.symm (χ (p : ZMod N) * (p : ℂ) ^ (k - 1))‖ ≤ (ℓ : ℝ)⁻¹ ^ n) ∧
      ∀ (p p' : ℕ) σ σ', p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
        p'.Prime → ¬ p' ∣ N * ℓ → IsFrobeniusAt p' σ' →
        ‖P σ σ' - ι.symm (qCoeffGamma1 f p * qCoeffGamma1 f p')‖ ≤ 2 * (ℓ : ℝ)⁻¹ ^ n ∧
        ‖Q σ σ' - ι.symm (χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * qCoeffGamma1 f p')‖ ≤
          (ℓ : ℝ)⁻¹ ^ n ∧
        ‖R σ σ' - ι.symm (χ (p : ZMod N) * (p : ℂ) ^ (k - 1) *
          (χ (p' : ZMod N) * (p' : ℂ) ^ (k - 1)))‖ ≤ (ℓ : ℝ)⁻¹ ^ n := by
  obtain ⟨m, r, g, ψ, c, hg, hc⟩ := hcong N k χ f hN hk hf ℓ ι n
  have hM : 0 < N * ℓ ^ m := Nat.mul_pos hN (pow_pos (Fact.out : ℓ.Prime).pos m)
  choose ρ hρc hρp using fun i => h2 (N * ℓ ^ m) (ψ i) (g i) hM (hg i) ℓ ι
  set j := ι.symm with hj
  set ε : ℝ := (ℓ : ℝ)⁻¹ ^ n with hε
  let tr : Fin r → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ :=
    fun i x => (ρ i x : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).trace
  let dt : Fin r → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ :=
    fun i x => (ρ i x : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).det
  have htrc : ∀ i, Continuous (tr i) := fun i =>
    (Units.continuous_val.comp (hρc i)).matrix_trace
  have hdtc : ∀ i, Continuous (dt i) := fun i =>
    (Units.continuous_val.comp (hρc i)).matrix_det
  have hcop : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → p.Coprime (N * ℓ) :=
    fun p hp h => (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hfrob : ∀ i (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      tr i σ = j (qCoeffGamma1 (g i) p) ∧
        dt i σ = j (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ)) := by
    intro i p σ hp hpN hσ
    obtain ⟨h1, h2'⟩ := (hρp i p hp (not_dvd_mul_pow_mul hp hpN)).2 σ hσ
    refine ⟨?_, ?_⟩
    · rw [← h1]
      exact (ι.symm_apply_apply _).symm
    · have e : ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) =
          ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) ^ ((2 : ℤ) - 1) := by norm_num
      rw [e, ← h2']
      exact (ι.symm_apply_apply _).symm
  let T : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ := fun x => ∑ i, j (c i) * tr i x
  let D : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ := fun x => ∑ i, j (c i) * dt i x
  let P : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ :=
    fun x y => ∑ i, j (c i) * tr i x * tr i y
  let Q : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ :=
    fun x y => ∑ i, j (c i) * dt i x * tr i y
  let R : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ :=
    fun x y => ∑ i, j (c i) * dt i x * dt i y
  -- The values at Frobenius elements, as images of complex numbers.
  have hTσ : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      T σ = j (∑ i, c i * qCoeffGamma1 (g i) p) := by
    intro p σ hp hpN hσ
    simp only [T, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [(hfrob i p σ hp hpN hσ).1]
  have hDσ : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      D σ = j (∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ))) := by
    intro p σ hp hpN hσ
    simp only [D, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [(hfrob i p σ hp hpN hσ).2, map_mul]
  have hPσ : ∀ (p p' : ℕ) σ σ', p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      p'.Prime → ¬ p' ∣ N * ℓ → IsFrobeniusAt p' σ' →
      P σ σ' = j (∑ i, c i * (qCoeffGamma1 (g i) p * qCoeffGamma1 (g i) p')) := by
    intro p p' σ σ' hp hpN hσ hp' hpN' hσ'
    simp only [P, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hfrob i p σ hp hpN hσ).1, (hfrob i p' σ' hp' hpN' hσ').1, mul_assoc]
  have hQσ : ∀ (p p' : ℕ) σ σ', p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      p'.Prime → ¬ p' ∣ N * ℓ → IsFrobeniusAt p' σ' →
      Q σ σ' = j (∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) *
        qCoeffGamma1 (g i) p')) := by
    intro p p' σ σ' hp hpN hσ hp' hpN' hσ'
    simp only [Q, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hfrob i p σ hp hpN hσ).2, (hfrob i p' σ' hp' hpN' hσ').1, map_mul, mul_assoc]
  have hRσ : ∀ (p p' : ℕ) σ σ', p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      p'.Prime → ¬ p' ∣ N * ℓ → IsFrobeniusAt p' σ' →
      R σ σ' = j (∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) *
        (ψ i (p' : ZMod (N * ℓ ^ m)) * (p' : ℂ)))) := by
    intro p p' σ σ' hp hpN hσ hp' hpN' hσ'
    simp only [R, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hfrob i p σ hp hpN hσ).2, (hfrob i p' σ' hp' hpN' hσ').2, map_mul, map_mul, mul_assoc]
  -- The congruences, with the trivial values of the characters at 1.
  have hc1 : ∀ a : ℕ, a.Coprime (N * ℓ) →
      ‖j (∑ i, c i * qCoeffGamma1 (g i) a) - j (qCoeffGamma1 f a)‖ ≤ ε := by
    intro a ha
    have h := hc a 1 ha (Nat.coprime_one_left _)
    simpa using h
  have hcd : ∀ d : ℕ, d.Coprime (N * ℓ) →
      ‖j (∑ i, c i * (ψ i (d : ZMod (N * ℓ ^ m)) * (d : ℂ))) -
        j (χ (d : ZMod N) * (d : ℂ) ^ (k - 1))‖ ≤ ε := by
    intro d hd
    have h := hc 1 d (Nat.coprime_one_left _) hd
    simpa [(hg _).one, hf.one] using h
  refine ⟨T, D, P, Q, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul (htrc i)
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul (hdtc i)
  · exact continuous_finsetSum _ fun i _ =>
      (continuous_const.mul ((htrc i).comp continuous_fst)).mul ((htrc i).comp continuous_snd)
  · exact continuous_finsetSum _ fun i _ =>
      (continuous_const.mul ((hdtc i).comp continuous_fst)).mul ((htrc i).comp continuous_snd)
  · exact continuous_finsetSum _ fun i _ =>
      (continuous_const.mul ((hdtc i).comp continuous_fst)).mul ((hdtc i).comp continuous_snd)
  · intro x y
    exact Finset.sum_congr rfl fun i _ => by
      simp only [tr]
      rw [(isPseudoCharTwo_trace_det (ρ i)).comm x y]
  · intro x y
    simp only [Q, P, T, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h := (isPseudoCharTwo_trace_det (ρ i)).rel x y
    simp only [tr, dt]
    linear_combination j (c i) * h
  · intro x y
    exact Finset.sum_congr rfl fun i _ => by
      simp only [dt]; rw [(isPseudoCharTwo_trace_det (ρ i)).det_mul x y, mul_assoc]
  · simp only [T, D, tr, dt, map_one, Units.val_one, Matrix.trace_one, Matrix.det_one,
      Fintype.card_fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · have h := hc1 1 (Nat.coprime_one_left _)
    simp only [(hg _).one, hf.one, mul_one, map_one] at h
    simpa [D, dt, map_sum] using h
  · intro p hp hpN Q' hQ' hlies σ hσ x
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hρp i p hp (not_dvd_mul_pow_mul hp hpN)).1 Q' hQ' hlies σ hσ
    simp only [tr, map_mul, h1, mul_one]
  · intro p σ hp hpN hσ
    refine ⟨?_, ?_⟩
    · rw [hTσ p σ hp hpN hσ]
      exact hc1 p (hcop p hp hpN)
    · rw [hDσ p σ hp hpN hσ]
      exact hcd p (hcop p hp hpN)
  · intro p p' σ σ' hp hpN hσ hp' hpN' hσ'
    refine ⟨?_, ?_, ?_⟩
    · rw [hPσ p p' σ σ' hp hpN hσ hp' hpN' hσ']
      rcases eq_or_ne p p' with rfl | hne
      · -- The case $p = p'$: $a_p^2 = a_{p^2} + \psi(p) p$.
        have hrec : ∀ i, qCoeffGamma1 (g i) p * qCoeffGamma1 (g i) p =
            qCoeffGamma1 (g i) (p ^ 2) + ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) := by
          intro i
          have h := (hg i).prime_pow p 0 hp
          simp only [zero_add, pow_one, pow_zero, (hg i).one, mul_one] at h
          rw [h]
          norm_num
        have hrecf : qCoeffGamma1 f p * qCoeffGamma1 f p =
            qCoeffGamma1 f (p ^ 2) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) := by
          have h := hf.prime_pow p 0 hp
          simp only [zero_add, pow_one, pow_zero, hf.one, mul_one] at h
          rw [h]
          ring
        have hsum : ∑ i, c i * (qCoeffGamma1 (g i) p * qCoeffGamma1 (g i) p) =
            ∑ i, c i * qCoeffGamma1 (g i) (p ^ 2) +
              ∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [hrec i]; ring
        have e : j (∑ i, c i * (qCoeffGamma1 (g i) p * qCoeffGamma1 (g i) p)) -
            j (qCoeffGamma1 f p * qCoeffGamma1 f p) =
            (j (∑ i, c i * qCoeffGamma1 (g i) (p ^ 2)) - j (qCoeffGamma1 f (p ^ 2))) +
            (j (∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ))) -
              j (χ (p : ZMod N) * (p : ℂ) ^ (k - 1))) := by
          rw [hsum, hrecf, map_add, map_add]
          ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have h1 := hc1 (p ^ 2) (Nat.Coprime.pow_left 2 (hcop p hp hpN))
        have h2' := hcd p (hcop p hp hpN)
        linarith
      · have hpp : p.Coprime p' := (Nat.coprime_primes hp hp').2 hne
        have hsum : ∑ i, c i * (qCoeffGamma1 (g i) p * qCoeffGamma1 (g i) p') =
            ∑ i, c i * qCoeffGamma1 (g i) (p * p') :=
          Finset.sum_congr rfl fun i _ => by rw [(hg i).mul p p' hpp]
        rw [hsum, ← hf.mul p p' hpp]
        have h1 := hc1 (p * p') (Nat.Coprime.mul_left (hcop p hp hpN) (hcop p' hp' hpN'))
        have hε0 : 0 ≤ ε := by positivity
        linarith
    · rw [hQσ p p' σ σ' hp hpN hσ hp' hpN' hσ']
      exact hc p' p (hcop p' hp' hpN') (hcop p hp hpN)
    · rw [hRσ p p' σ σ' hp hpN hσ hp' hpN' hσ']
      have h := hcd (p * p') (Nat.Coprime.mul_left (hcop p hp hpN) (hcop p' hp' hpN'))
      have e1 : ∑ i, c i * (ψ i (p : ZMod (N * ℓ ^ m)) * (p : ℂ) *
          (ψ i (p' : ZMod (N * ℓ ^ m)) * (p' : ℂ))) =
          ∑ i, c i * (ψ i ((p * p' : ℕ) : ZMod (N * ℓ ^ m)) * ((p * p' : ℕ) : ℂ)) :=
        Finset.sum_congr rfl fun i _ => by push_cast; rw [map_mul]; ring
      have e2 : χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (χ (p' : ZMod N) * (p' : ℂ) ^ (k - 1)) =
          χ ((p * p' : ℕ) : ZMod N) * ((p * p' : ℕ) : ℂ) ^ (k - 1) := by
        push_cast
        rw [map_mul, mul_zpow]
        ring
      rw [e1, e2]
      exact h

/-- **Eichler, Shimura and Deligne for each weight $k \ge 2$, by congruences**, `proved-mod` the weight 2 case `EichlerShimuraWeightTwo` and the published theorems `WeightTwoCongruence` (Shimura, Hida), `CoefficientField` (Shimura), `FrobeniusDense` (Chebotarev) and `PseudoCharTwoRepresentation` (Taylor). This is the full statement `Langlands.EichlerShimuraDeligne`. -/
theorem eichlerShimuraDeligne_of_congruence (h2 : EichlerShimuraWeightTwo)
    (hcong : WeightTwoCongruence) (hE : CoefficientField) (hdense : FrobeniusDense)
    (hTay : PseudoCharTwoRepresentation) : EichlerShimuraDeligne := by
  intro N k χ f hN hk hf ℓ _ ι
  set j := ι.symm with hj
  obtain ⟨E, hEfin, hEmem⟩ := hE N k χ f hN hk hf ℓ ι
  have hEc : IsComplete (E : Set (PadicAlgCl ℓ)) := Submodule.complete_of_finiteDimensional E
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hinv0 : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have hinv1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hℓ
  set δ : ℕ → ℝ := fun n => (ℓ : ℝ)⁻¹ ^ n with hδdef
  have hδ0 : ∀ n, 0 < δ n := fun n => pow_pos (inv_pos.2 (by linarith)) n
  have hδanti : Antitone δ := fun a b hab => pow_le_pow_of_le_one hinv0 hinv1.le hab
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hinv0 hinv1
  have hδ1 : ∀ n, δ n ≤ 1 := fun n => pow_le_one₀ hinv0 hinv1.le
  choose T D P Q R hTc hDc hPc hQc hRc hcomm hrel hDR hT1 hD1 hunr hfr1 hfr2 using
    fun n => exists_approx_weightTwo h2 hcong hN hk hf ℓ ι n
  set S := {σ : Field.absoluteGaloisGroup ℚ | ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧
    IsFrobeniusAt p σ} with hSdef
  have hS : Dense S := hdense (N * ℓ) (Nat.mul_pos hN (Fact.out : ℓ.Prime).pos)
  classical
  let vT : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ := fun σ =>
    if h : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p σ then
      j (qCoeffGamma1 f h.choose) else 0
  let vD : Field.absoluteGaloisGroup ℚ → PadicAlgCl ℓ := fun σ =>
    if h : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p σ then
      j (χ (h.choose : ZMod N) * (h.choose : ℂ) ^ (k - 1)) else 0
  obtain ⟨T', hTc', hTE, hTb, hTu⟩ := exists_continuous_limit_of_dense hS hEc vT
    (fun s hs => by
      have hs' : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p s := hs
      simp only [vT, dite_eq_left_of_eq_true (eq_true hs')]
      obtain ⟨hp, hpN, -⟩ := hs.choose_spec
      exact (hEmem _ hp hpN).1)
    T hTc δ hδ0 hδanti hδt (fun n s hs => by
      have hs' : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p s := hs
      simp only [vT, dite_eq_left_of_eq_true (eq_true hs')]
      obtain ⟨hp, hpN, hσ⟩ := hs.choose_spec
      rw [dist_eq_norm]
      exact (hfr1 n _ s hp hpN hσ).1)
  obtain ⟨D', hDc', -, hDb, hDu⟩ := exists_continuous_limit_of_dense hS hEc vD
    (fun s hs => by
      have hs' : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p s := hs
      simp only [vD, dite_eq_left_of_eq_true (eq_true hs')]
      obtain ⟨hp, hpN, -⟩ := hs.choose_spec
      exact (hEmem _ hp hpN).2)
    D hDc δ hδ0 hδanti hδt (fun n s hs => by
      have hs' : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N * ℓ ∧ IsFrobeniusAt p s := hs
      simp only [vD, dite_eq_left_of_eq_true (eq_true hs')]
      obtain ⟨hp, hpN, hσ⟩ := hs.choose_spec
      rw [dist_eq_norm]
      exact (hfr1 n _ s hp hpN hσ).2)
  have hTfrob : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      T' σ = j (qCoeffGamma1 f p) := fun p σ hp hpN hσ =>
    hTu σ _ fun n => by rw [dist_eq_norm]; exact (hfr1 n p σ hp hpN hσ).1
  have hDfrob : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      D' σ = j (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) := fun p σ hp hpN hσ =>
    hDu σ _ fun n => by rw [dist_eq_norm]; exact (hfr1 n p σ hp hpN hσ).2
  have hTt : ∀ g, Tendsto (fun n => T n g) atTop (𝓝 (T' g)) := fun g =>
    tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun _ => dist_nonneg) (fun n => hTb n g) hδt)
  have hDt : ∀ g, Tendsto (fun n => D n g) atTop (𝓝 (D' g)) := fun g =>
    tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun _ => dist_nonneg) (fun n => hDb n g) hδt)
  -- A bound for the limits on the compact group.
  have : CompactSpace (Field.absoluteGaloisGroup ℚ) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  obtain ⟨B1, hB1⟩ := isCompact_univ.exists_bound_of_continuousOn hTc'.continuousOn
  obtain ⟨B2, hB2⟩ := isCompact_univ.exists_bound_of_continuousOn hDc'.continuousOn
  set B := max B1 B2 with hBdef
  have hBa : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      ‖j (qCoeffGamma1 f p)‖ ≤ B := fun p σ hp hpN hσ => by
    rw [← hTfrob p σ hp hpN hσ]
    exact (hB1 σ (Set.mem_univ _)).trans (le_max_left _ _)
  have hBd : ∀ (p : ℕ) σ, p.Prime → ¬ p ∣ N * ℓ → IsFrobeniusAt p σ →
      ‖j (χ (p : ZMod N) * (p : ℂ) ^ (k - 1))‖ ≤ B := fun p σ hp hpN hσ => by
    rw [← hDfrob p σ hp hpN hσ]
    exact (hB2 σ (Set.mem_univ _)).trans (le_max_right _ _)
  set η : ℕ → ℝ := fun n => δ n * (2 * B + 3) with hηdef
  -- The approximate multiplicativity, first at Frobenius elements, then everywhere.
  have hPall : ∀ n x y, ‖P n x y - T n x * T n y‖ ≤ η n := by
    intro n x y
    refine norm_le_of_dense (f := fun z : Field.absoluteGaloisGroup ℚ ×
      Field.absoluteGaloisGroup ℚ => P n z.1 z.2 - T n z.1 * T n z.2)
      ((hPc n).sub (((hTc n).comp continuous_fst).mul ((hTc n).comp continuous_snd)))
      (hS.prod hS) (fun z hz => ?_) (x, y)
    obtain ⟨⟨p, hp, hpN, hσ⟩, ⟨p', hp', hpN', hσ'⟩⟩ := hz
    have h3 := (hfr2 n p p' z.1 z.2 hp hpN hσ hp' hpN' hσ').1
    have h4 := norm_mul_sub_mul_le (hfr1 n p z.1 hp hpN hσ).1 (hfr1 n p' z.2 hp' hpN' hσ').1
      (hBa p z.1 hp hpN hσ) (hBa p' z.2 hp' hpN' hσ') (hδ1 n) (hδ0 n).le
    rw [map_mul] at h3
    have := norm_sub_le_norm_sub_add_norm_sub (P n z.1 z.2) (j (qCoeffGamma1 f p) *
      j (qCoeffGamma1 f p')) (T n z.1 * T n z.2)
    rw [norm_sub_rev (j _ * j _)] at this
    simp only [hηdef]
    change ‖P n z.1 z.2 - T n z.1 * T n z.2‖ ≤ δ n * (2 * B + 3)
    have : δ n * (2 * B + 3) = 2 * δ n + δ n * (2 * B + 1) := by ring
    linarith
  have hQall : ∀ n x y, ‖Q n x y - D n x * T n y‖ ≤ η n := by
    intro n x y
    refine norm_le_of_dense (f := fun z : Field.absoluteGaloisGroup ℚ ×
      Field.absoluteGaloisGroup ℚ => Q n z.1 z.2 - D n z.1 * T n z.2)
      ((hQc n).sub (((hDc n).comp continuous_fst).mul ((hTc n).comp continuous_snd)))
      (hS.prod hS) (fun z hz => ?_) (x, y)
    obtain ⟨⟨p, hp, hpN, hσ⟩, ⟨p', hp', hpN', hσ'⟩⟩ := hz
    have h3 := (hfr2 n p p' z.1 z.2 hp hpN hσ hp' hpN' hσ').2.1
    have h4 := norm_mul_sub_mul_le (hfr1 n p z.1 hp hpN hσ).2 (hfr1 n p' z.2 hp' hpN' hσ').1
      (hBd p z.1 hp hpN hσ) (hBa p' z.2 hp' hpN' hσ') (hδ1 n) (hδ0 n).le
    rw [map_mul] at h3
    have := norm_sub_le_norm_sub_add_norm_sub (Q n z.1 z.2)
      (j (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * j (qCoeffGamma1 f p')) (D n z.1 * T n z.2)
    rw [norm_sub_rev (j _ * j _)] at this
    change ‖Q n z.1 z.2 - D n z.1 * T n z.2‖ ≤ δ n * (2 * B + 3)
    have : δ n * (2 * B + 3) = 2 * δ n + δ n * (2 * B + 1) := by ring
    linarith [(hδ0 n).le]
  have hRall : ∀ n x y, ‖R n x y - D n x * D n y‖ ≤ η n := by
    intro n x y
    refine norm_le_of_dense (f := fun z : Field.absoluteGaloisGroup ℚ ×
      Field.absoluteGaloisGroup ℚ => R n z.1 z.2 - D n z.1 * D n z.2)
      ((hRc n).sub (((hDc n).comp continuous_fst).mul ((hDc n).comp continuous_snd)))
      (hS.prod hS) (fun z hz => ?_) (x, y)
    obtain ⟨⟨p, hp, hpN, hσ⟩, ⟨p', hp', hpN', hσ'⟩⟩ := hz
    have h3 := (hfr2 n p p' z.1 z.2 hp hpN hσ hp' hpN' hσ').2.2
    have h4 := norm_mul_sub_mul_le (hfr1 n p z.1 hp hpN hσ).2 (hfr1 n p' z.2 hp' hpN' hσ').2
      (hBd p z.1 hp hpN hσ) (hBd p' z.2 hp' hpN' hσ') (hδ1 n) (hδ0 n).le
    rw [map_mul] at h3
    have := norm_sub_le_norm_sub_add_norm_sub (R n z.1 z.2)
      (j (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * j (χ (p' : ZMod N) * (p' : ℂ) ^ (k - 1)))
      (D n z.1 * D n z.2)
    rw [norm_sub_rev (j _ * j _)] at this
    change ‖R n z.1 z.2 - D n z.1 * D n z.2‖ ≤ δ n * (2 * B + 3)
    have : δ n * (2 * B + 3) = 2 * δ n + δ n * (2 * B + 1) := by ring
    linarith [(hδ0 n).le]
  have hBnn : 0 ≤ B := (norm_nonneg _).trans ((hB1 1 (Set.mem_univ _)).trans (le_max_left _ _))
  have hη0 : ∀ n, 0 ≤ η n := fun n => mul_nonneg (hδ0 n).le (by linarith)
  -- The limit is a pseudo-character.
  have hpc : IsPseudoCharTwo T' D' := by
    refine IsPseudoCharTwo.of_approx (ε := fun n => 2 * η n + 2 * δ n) ?_ hTt hDt
      (fun n => ?_) (fun n x y => ?_) (fun n => ?_) (fun n x y => ?_) (fun n x y => ?_)
    · have h := ((hδt.mul_const (2 * B + 3)).const_mul 2).add (hδt.const_mul 2)
      simpa [hηdef] using h
    · rw [hT1 n]
      have e : 2 * D n 1 - 2 = (D n 1 - 1) + (D n 1 - 1) := by ring
      rw [e]
      have := hD1 n
      have := norm_add_le (D n 1 - 1) (D n 1 - 1)
      linarith [hη0 n]
    · rw [hcomm n x y, sub_self, norm_zero]
      linarith [hη0 n, hδ0 n]
    · have := hD1 n
      linarith [hη0 n, hδ0 n]
    · rw [hDR n x y]
      have := hRall n x y
      linarith [hη0 n, hδ0 n]
    · have e : D n x * T n (x⁻¹ * y) - T n x * T n y + T n (x * y) =
          -(Q n x (x⁻¹ * y) - D n x * T n (x⁻¹ * y)) + (P n x y - T n x * T n y) +
            (Q n x (x⁻¹ * y) - P n x y + T n (x * y)) := by ring
      rw [e, hrel n x y, add_zero]
      have h1 := norm_add_le (-(Q n x (x⁻¹ * y) - D n x * T n (x⁻¹ * y)))
        (P n x y - T n x * T n y)
      rw [norm_neg] at h1
      have := hQall n x (x⁻¹ * y)
      have := hPall n x y
      linarith [hδ0 n]
  obtain ⟨ρ, hρc, hρtr, hρdet, hρker⟩ := hTay ℓ T' D' E hEfin hTE hTc' hDc' hpc
  refine ⟨ρ, hρc, fun p hp hpN => ⟨fun Q' hQ' hlies σ hσ => hρker σ fun x => ?_,
    fun σ hσ => ⟨?_, ?_⟩⟩⟩
  · exact tendsto_nhds_unique (hTt (x * σ))
      ((hTt x).congr fun n => (hunr n p hp hpN Q' hQ' hlies σ hσ x).symm)
  · rw [hρtr, hTfrob p σ hp hpN hσ]
    exact ι.apply_symm_apply _
  · rw [hρdet, hDfrob p σ hp hpN hσ]
    exact ι.apply_symm_apply _

end Langlands.Bridge
