/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.Automorphic
import Langlands.Statements.Galois

/-!
# Global statements for $GL_n$: Ramanujan, functoriality, symmetric powers and base change

This file states four global results and conjectures for cusp forms on $GL_n$ over a number field. Each one is a condition on the Satake parameters at the unramified places, with the vocabulary of `Langlands.Statements.Automorphic`.

* `Langlands.RamanujanGL n K` is the generalized Ramanujan conjecture at the unramified places: a cusp form on $GL_n$ over $K$ with a unitary central character has Satake parameters of absolute value $1$ at each place where it is spherical. It is a conjecture for $n \ge 2$. For $n = 1$ it is proved here as `Langlands.ramanujanGL_one`.
* `Langlands.FunctorialityGL n m r` is Langlands functoriality for an algebraic representation $r : GL_n(\mathbb{C}) \to GL_m(\mathbb{C})$: each cuspidal Hecke eigenform $\pi$ on $GL_n$ has a lift $\Pi$ to $GL_m$, an isobaric sum of cuspidal representations, with $\mathrm{Sat}(\Pi_v) = r(\mathrm{Sat}(\pi_v))$ at almost all places. It is a conjecture. The case $r = \mathrm{id}$ is proved here as `Langlands.functorialityGL_id`.
* `Langlands.SymPowerFunctoriality` is the theorem of Newton and Thorne: for a normalized eigenform $f$ of weight $k \ge 2$ without complex multiplication and each $n \ge 1$, there is a cusp form on $GL_{n+1}$ over $\mathbb{Q}$ whose Satake parameters at each $p \nmid N$ are $\alpha_p^{n-j} \beta_p^j$ for $0 \le j \le n$, where $\alpha_p, \beta_p$ are the unitary Satake parameters of $f$.
* `Langlands.BaseChangeCyclic` is the theorem of Arthur and Clozel: for a cyclic extension $L / K$ of prime degree, each cuspidal Hecke eigenform $\pi$ on $GL_n$ over $K$ has a base change $\Pi$ to $L$, an isobaric sum, with $\mathrm{Sat}(\Pi_w) = \{\alpha^{f} : \alpha \in \mathrm{Sat}(\pi_v)\}$ at almost all places $v$ and the places $w \mid v$ of residue degree $f$.

## Implementation notes

The statements use the Hecke eigensystems of cusp forms in place of cuspidal automorphic representations. The implementation notes of `Langlands.Statements.Automorphic` explain why this gives the same eigensystems. A Hecke eigenform at almost all places generates one cuspidal automorphic representation, by strong multiplicity one.

The textbook forms are statements about the local components at all places, through the local Langlands correspondence for $GL_n$. These statements are only about the unramified places, where the local correspondence is the Satake parameter. At these places they say the same as the textbook forms. Functoriality and base change are statements about almost all places, which is the weak form in the sense of Langlands. For base change this weak form determines $\Pi$, by strong multiplicity one for isobaric representations of Jacquet and Shalika.

A lift to $GL_m$ need not be cuspidal. It is an isobaric sum $\Pi_1 \boxplus \cdots \boxplus \Pi_k$ of cuspidal representations, and its Satake parameters are the union of those of the $\Pi_j$. The structure `Langlands.IsobaricCuspData` records the summands as cusp forms.

These rows of the plan are not stated in this file.

* The reciprocity conjecture for $GL_n$ and the construction of Galois representations from regular algebraic cuspidal representations are in `Langlands.Statements.Reciprocity`, which has the vocabulary for the infinitesimal character at the infinite places. The Hodge-Tate and de Rham conditions on the Galois side need $p$-adic Hodge theory, which Mathlib does not have. A form with only the algebraicity of the Satake parameters would be a different and stronger statement, so it is not given.
* Reciprocity for $GL_n$ over a function field (Drinfeld for $n = 2$, L. Lafforgue in general) needs the adele ring of a global function field, with its places at infinity. Mathlib has the finite adeles of a Dedekind domain, but not the full adele ring of a function field.
* The global Jacquet-Langlands correspondence needs automorphic forms on the units of a quaternion algebra and the discrete series at the ramified places.

## References

* R. P. Langlands, Problems in the theory of automorphic forms, in Lectures in modern analysis and applications III, Lecture Notes in Math. 170, 1970.
* P. Sarnak, Notes on the generalized Ramanujan conjectures, in Harmonic analysis, the trace formula, and Shimura varieties, Clay Math. Proc. 4, 2005.
* J. Arthur and L. Clozel, Simple algebras, base change, and the advanced theory of the trace formula, Ann. of Math. Stud. 120, 1989.
* J. Newton and J. A. Thorne, Symmetric power functoriality for holomorphic modular forms, Publ. Math. IHES 134 (2021), and II, Publ. Math. IHES 134 (2021).
* K. Ribet, Galois representations attached to eigenforms with Nebentypus, in Modular functions of one variable V, Lecture Notes in Math. 601, 1977.
* H. Jacquet and J. Shalika, On Euler products and the classification of automorphic forms II, Amer. J. Math. 103 (1981).
-/

namespace Langlands

open NumberField IsDedekindDomain CongruenceSubgroup

open scoped MatrixGroups ModularForm

universe u

/-! ### The Ramanujan conjecture -/

/-- **The generalized Ramanujan conjecture for $GL_n$ at the unramified places.** Let $\varphi$ be a nonzero bounded cusp form on $GL_n$ over $K$. A nonzero bounded cusp form has a unitary central character, and each unitary cuspidal automorphic representation has bounded vectors. So these $\varphi$ give all the unitary cuspidal automorphic representations $\pi$. The eigensystem of $\varphi$ at $v$ is the eigensystem of $\pi_v$ for each $\pi$ in which $\varphi$ has a nonzero component. Let $v$ be a finite place where $\varphi$ is spherical and a Hecke eigenvector. Then each Satake parameter $\alpha$ of $\varphi$ at $v$ has $|\alpha| = 1$. In other words, $\pi_v$ is tempered. The cuspidal condition uses the invariant probability measure on $(\mathbb{A}_K/K)^{n \times n}$. This measure exists because $\mathbb{A}_K/K$ is compact, but Mathlib does not have this fact yet.

The textbook form says that $\pi_v$ is tempered at every place $v$, including the ramified and the infinite places. This statement is only about the finite places where $\pi$ is unramified. It is a theorem for $n = 1$ (see `Langlands.ramanujanGL_one`), and for $n = 2$, $K$ totally real and $\pi$ holomorphic of weights at least $2$ (Deligne, Blasius). It is open in general, for example for Maass forms on $GL_2$ over $\mathbb{Q}$. -/
def RamanujanGL (n : ℕ) (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (N : 𝓞 K) (φ : AdelicGL K n → ℂ), IsCuspForm N φ → φ ≠ 0 →
    (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (ev : ℕ → ℂ), IsHeckeEigenAt φ v ev →
      ∀ α ∈ satake n v ev, ‖α‖ = 1

/-! ### Functoriality -/

/-- **Langlands functoriality for $GL_n \to GL_m$.** Let $r : GL_n(\mathbb{C}) \to GL_m(\mathbb{C})$ be an algebraic representation of the dual group. Let $\varphi$ be a nonzero cusp form on $GL_n$ over a number field $K$ that is a Hecke eigenform at almost all places. Then there is an isobaric sum $\Pi$ of cuspidal representations of $GL_m(\mathbb{A}_K)$ and a finite set $S$ of places with this property. At each finite place $v \notin S$ where $\varphi$ has Hecke eigenvalues with Satake parameters $\alpha_1, \ldots, \alpha_n$, the Satake parameters of $\Pi_v$ are the eigenvalues of $r(\mathrm{diag}(\alpha_1, \ldots, \alpha_n))$, with multiplicity.

This is the weak form of the conjecture of Langlands, in the sense of the unramified places. The textbook form allows an $L$-homomorphism ${}^L GL_n \to {}^L GL_m$, that is, a representation of $GL_n(\mathbb{C}) \times W_K$. This statement is for the representations that are trivial on the Weil group $W_K$. A general $L$-homomorphism is a sum of products $r_i \otimes \sigma_i$, with $\sigma_i$ an irreducible representation of $W_K$. When each $\sigma_i$ is a character, its transfer is a twist of the transfer for $r_i$ by the corresponding Hecke character. When some $\sigma_i$ has dimension at least $2$, the statement does not cover it. This case contains the strong Artin conjecture. The summands of the lift are cusp forms with any central character, so they can be twists of unitary cuspidal representations by $|\det|^s$. The conjecture is open in general. Known cases include $r = \mathrm{Sym}^2$, $\mathrm{Sym}^3$, $\mathrm{Sym}^4$ for $n = 2$ (Gelbart and Jacquet, Kim and Shahidi, Kim) and $r = \wedge^2$ for $n = 4$ (Kim). The case $r = \mathrm{id}$ is `Langlands.functorialityGL_id`. -/
def FunctorialityGL (n m : ℕ) (r : GL (Fin n) ℂ →* GL (Fin m) ℂ) : Prop :=
  IsAlgebraicRep r →
  ∀ (K : Type u) [Field K] [NumberField K] (N : 𝓞 K) (φ : AdelicGL K n → ℂ),
    IsCuspForm N φ → φ ≠ 0 → IsHeckeEigenform φ →
    ∃ (D : IsobaricCuspData K m) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite ∧
      ∀ v ∉ S, ∀ ev : ℕ → ℂ, IsHeckeEigenAt φ v ev →
        ∀ α : Fin n → ℂˣ, Finset.univ.val.map (fun j ↦ (α j : ℂ)) = satake n v ev →
          D.HasSatakeAt v (r (diagonalGL α) : Matrix (Fin m) (Fin m) ℂ).charpoly.roots

/-! ### Symmetric power functoriality -/

/-- A cusp form $f$ on $\Gamma_1(N)$ has complex multiplication if there is a nontrivial Dirichlet character $\varepsilon$ modulo some $M \ge 1$ with $\varepsilon(p) a_p(f) = a_p(f)$ for each prime $p \nmid NM$. For a normalized eigenform this is the definition of Ribet. The character $\varepsilon$ is then the quadratic character of an imaginary quadratic field, and $a_p(f) = 0$ at the primes that are inert in this field. -/
def HasComplexMultiplication {N : ℕ} {k : ℤ}
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) : Prop :=
  ∃ (M : ℕ) (ε : DirichletCharacter ℂ M), 0 < M ∧ ε ≠ 1 ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N * M → ε (p : ZMod M) * qCoeffGamma1 f p = qCoeffGamma1 f p

/-- The Satake parameters of $\mathrm{Sym}^n$ of $\{\alpha, \beta\}$: the multiset $\{\alpha^{n-j} \beta^j : 0 \le j \le n\}$. -/
def symPowerParameters (n : ℕ) (α β : ℂ) : Multiset ℂ :=
  (Multiset.range (n + 1)).map fun j ↦ α ^ (n - j) * β ^ j

/-- **Symmetric power functoriality for holomorphic modular forms** (Newton and Thorne). Let $f$ be a normalized eigenform of weight $k \ge 2$ on $\Gamma_1(N)$ with character $\chi$, without complex multiplication. Let $n \ge 1$. Then there is a nonzero cusp form $\varphi$ on $GL_{n+1}$ over $\mathbb{Q}$ with this property. At each prime $p \nmid N$, $\varphi$ is a Hecke eigenvector at $p$, and its Satake parameters are $\alpha^{n-j} \beta^j$ for $0 \le j \le n$, where $\alpha + \beta = a_p(f) p^{-(k-1)/2}$ and $\alpha \beta = \chi(p)$.

The textbook form says that the symmetric power lift $\mathrm{Sym}^n \pi_f$ is a cuspidal automorphic representation of $GL_{n+1}(\mathbb{A}_\mathbb{Q})$, with local components given by the local Langlands correspondence at every place. This statement is only about the primes $p \nmid N$, where $\pi_f$ is unramified and $\alpha, \beta$ are its Satake parameters. The form $\varphi$ is a vector in $\mathrm{Sym}^n \pi_f$ that is spherical at these primes. The statement asks for a cusp form and not for a cuspidal representation, but a nonzero Hecke eigenform at almost all places generates a cuspidal representation, by strong multiplicity one. The theorem of Newton and Thorne is for newforms. A normalized eigenform has the Hecke eigenvalues of a newform at the primes $p \nmid N$, so the statement is the same. The pair $\{\alpha, \beta\}$ depends on the normalization of the Satake parameter of $\pi_f$ only up to the replacement by $\{\alpha^{-1}, \beta^{-1}\}$, which gives the contragredient of $\mathrm{Sym}^n \pi_f$, again a cusp form. -/
def SymPowerFunctoriality : Prop :=
  ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    0 < N → 2 ≤ k → IsNormalizedEigenformWithCharacter f χ → ¬ HasComplexMultiplication f →
    ∀ n : ℕ, 1 ≤ n →
      ∃ (L : 𝓞 ℚ) (φ : AdelicGL ℚ (n + 1) → ℂ), IsCuspForm L φ ∧ φ ≠ 0 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ Ideal.absNorm v.asIdeal ∣ N →
          ∃ ev : ℕ → ℂ, IsHeckeEigenAt φ v ev ∧
            ∀ α β : ℂ,
              α + β = qCoeffGamma1 f (Ideal.absNorm v.asIdeal) *
                (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) →
              α * β = χ (Ideal.absNorm v.asIdeal : ZMod N) →
              satake (n + 1) v ev = symPowerParameters n α β

/-! ### Cyclic base change -/

/-- **Cyclic base change for $GL_n$** (Arthur and Clozel). Let $L / K$ be a cyclic extension of number fields of prime degree. Let $\varphi$ be a nonzero cusp form on $GL_n$ over $K$ that is a Hecke eigenform at almost all places. Then there is an isobaric sum $\Pi$ of cuspidal representations of $GL_n(\mathbb{A}_L)$ and a finite set $S$ of places of $K$ with this property. Let $v \notin S$ be a finite place where $\varphi$ has Hecke eigenvalues with Satake parameters $\alpha_1, \ldots, \alpha_n$, and let $w$ be a place of $L$ over $v$ with residue degree $f$. Then the Satake parameters of $\Pi_w$ are $\alpha_1^f, \ldots, \alpha_n^f$.

The textbook form also describes $\Pi$: it is cuspidal unless $\pi \cong \pi \otimes (\eta \circ \det)$ for a character $\eta$ of $K^\times \backslash \mathbb{A}_K^\times$ attached to $L / K$, and its local components are the local base changes at every place. This statement is the weak form at the unramified places. The relation $\alpha \mapsto \alpha^f$ is the restriction of the Langlands parameter from $W_{K_v}$ to $W_{L_w}$, since the Frobenius of $L_w$ is the $f$-th power of the Frobenius of $K_v$. For a cyclic extension of any degree, the theorem follows by induction over a chain of extensions of prime degree. -/
def BaseChangeCyclic : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L],
    IsGalois K L → IsCyclic (L ≃ₐ[K] L) → (Module.finrank K L).Prime →
    ∀ (n : ℕ) (N : 𝓞 K) (φ : AdelicGL K n → ℂ), IsCuspForm N φ → φ ≠ 0 → IsHeckeEigenform φ →
      ∃ (D : IsobaricCuspData L n) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite ∧
        ∀ v ∉ S, ∀ ev : ℕ → ℂ, IsHeckeEigenAt φ v ev →
          ∀ w : HeightOneSpectrum (𝓞 L),
            w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal →
            D.HasSatakeAt w ((satake n v ev).map (· ^ w.asIdeal.inertiaDeg (𝓞 K)))

/-! ### Sanity checks -/

/-- If right translation by $s$ multiplies a nonzero bounded function by $b$, then $|b| \le 1$. -/
theorem norm_le_one_of_translate {G : Type*} [Group G] (φ : G → ℂ) (s : G) (b : ℂ)
    (h : ∀ g, φ (g * s) = b * φ g) (C : ℝ) (hC : ∀ g, ‖φ g‖ ≤ C) (g₀ : G) (h₀ : φ g₀ ≠ 0) :
    ‖b‖ ≤ 1 := by
  have hk (k : ℕ) : φ (g₀ * s ^ k) = b ^ k * φ g₀ := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, h, ih]; ring
  by_contra hb
  push Not at hb
  have hpos : 0 < ‖φ g₀‖ := norm_pos_iff.2 h₀
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (C / ‖φ g₀‖) hb
  have := hC (g₀ * s ^ k)
  rw [hk, norm_mul, norm_pow] at this
  rw [div_lt_iff₀ hpos] at hk'
  linarith

/-- **The Ramanujan conjecture for $GL_1$.** For $n = 1$ the operator $T_{v,1}$ is a right translation, the Satake parameter is its eigenvalue, and a bounded nonzero eigenvector of a translation has an eigenvalue of absolute value $1$. -/
theorem ramanujanGL_one (K : Type u) [Field K] [NumberField K] : RamanujanGL 1 K := by
  intro N φ _ hφ ⟨C, hC⟩ v ev hev α hα
  rw [satake_one, Multiset.mem_singleton] at hα
  subst hα
  obtain ⟨t, ht⟩ := exists_adelicHeckeOperator_one_eq (K := K) v
  have h (g : AdelicGL K 1) : φ (g * t) = ev 1 * φ g := by
    have := ht φ g
    rw [hev.2 1 le_rfl le_rfl] at this
    simpa using this.symm
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hφ (funext h')
  have hne : ev 1 ≠ 0 := by
    intro h0
    apply hg₀
    have := h (g₀ * t⁻¹)
    rwa [inv_mul_cancel_right, h0, zero_mul] at this
  have h' (g : AdelicGL K 1) : φ (g * t⁻¹) = (ev 1)⁻¹ * φ g := by
    have := h (g * t⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have h₁ := norm_le_one_of_translate φ t (ev 1) h C hC g₀ hg₀
  have h₂ := norm_le_one_of_translate φ t⁻¹ (ev 1)⁻¹ h' C hC g₀ hg₀
  rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 hne)] at h₂
  exact le_antisymm h₁ h₂

theorem isAlgebraicRep_id (n : ℕ) : IsAlgebraicRep (MonoidHom.id (GL (Fin n) ℂ)) :=
  ⟨fun i j ↦ MvPolynomial.X (some (i, j)), fun g i j ↦ by simp⟩

/-- **Functoriality for the identity.** For $r = \mathrm{id}$ the lift of $\varphi$ is $\varphi$ itself. The proof computes the eigenvalues of a diagonal matrix as the roots of its characteristic polynomial. -/
theorem functorialityGL_id (n : ℕ) : FunctorialityGL.{u} n n (MonoidHom.id _) := by
  intro _ K _ _ N φ hφ hne _
  refine ⟨⟨1, fun _ ↦ n, fun _ ↦ N, fun _ ↦ φ, fun _ ↦ hφ, fun _ ↦ hne, by simp⟩, ∅,
    Set.finite_empty, fun v _ ev hev α hα ↦ ⟨fun _ ↦ ev, fun _ ↦ hev, ?_⟩⟩
  have hd : ((MonoidHom.id (GL (Fin n) ℂ) (diagonalGL α) : GL (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal fun j ↦ (α j : ℂ) := rfl
  have hm : Finset.univ.val.map (fun j ↦ Polynomial.X - Polynomial.C (α j : ℂ)) =
      (Finset.univ.val.map fun j ↦ (α j : ℂ)).map fun a ↦ Polynomial.X - Polynomial.C a := by
    rw [Multiset.map_map]
    rfl
  rw [hd, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, hm,
    Polynomial.roots_multiset_prod_X_sub_C, hα]
  simp

end Langlands
