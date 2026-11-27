/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.LanglandsFamilyPairs
import Langlands.Local.LanglandsFamilyEps
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The ε-factors of pairs for $GL_1$, additivity and the uniqueness of L-factors

Let $K$ be a nonarchimedean local field with residue field of size $q$. This file continues `Langlands.Local.LanglandsFamilyPairs`. It links the condition `Langlands.IsTateEpsilon` to the concrete Tate ε-factor of `Langlands.Local.LanglandsFamilyEps`, so that a concrete ε-factor exists in dimension one. It proves the condition `Langlands.IsRSEpsilonFactor` for $GL_1 \times GL_1$ with the Tate ε-factor of $\chi \chi'$. It defines the direct sum of Weil-Deligne representations and the additive Galois ε-factor. It proves that the generator of a family of zeta integrals is unique.

## Main definitions

* `Langlands.blockMat`, `Langlands.blockHom`: the block diagonal matrix $\mathrm{diag}(A, B)$, indexed by $\mathrm{Fin}(m + m')$, and the algebra homomorphism $(A, B) \mapsto \mathrm{diag}(A, B)$.
* `Langlands.WeilDeligneRep.directSum`: the direct sum $\rho \oplus \rho' = (\mathrm{diag}(r, r'), \mathrm{diag}(N, N'))$ of Weil-Deligne representations of dimensions $m$ and $m'$.
* `Langlands.IsWDEpsilonAdditive`: the conditions of `IsWDEpsilon` and the additivity $\varepsilon(s, \rho \oplus \rho', \psi) = \varepsilon(s, \rho, \psi) \varepsilon(s, \rho', \psi)$.

## Main results

* `Langlands.isSemisimple_blockMat`: the block diagonal matrix of semisimple matrices is semisimple.
* `Langlands.LocalGL1.isTateEpsilon_tateEpsilon`: the concrete Tate ε-factor `tateEpsilon` satisfies `IsTateEpsilon`.
* `Langlands.LocalGL1.isTateEpsilon_wdEpsilon`: in dimension one, `wdEpsilon` satisfies `IsTateEpsilon` for the character $\det r \circ \mathrm{art}_K$.
* `Langlands.LocalGL1.tateEpsilon_monomial`: the Tate ε-factor is a monomial $c (q^{-s})^k$ with $c \neq 0$.
* `Langlands.LocalGL1.zeta_eq_laurent_of_lt`: $Z(\varphi, \chi, s) = A(q^{-s}) q^{k s} L(s, \chi)$ on the half-plane $|\chi(\varpi) q^{-s}| < 1$.
* `Langlands.LocalGL1.fourier_isSchwartzBruhat`: the Fourier transform of a Schwartz-Bruhat function is a Schwartz-Bruhat function.
* `Langlands.contragredient_one_apply`, `Langlands.nontrivial_contragredient_one`: the contragredient of $\chi \circ \det$ on $GL_1(K)$ is $\chi^{-1} \circ \det$ on a nonzero space.
* `Langlands.isRSEpsilonFactor_one`: the Rankin-Selberg ε-factor of $\chi \circ \det$ and $\chi' \circ \det$ is the Tate ε-factor $\varepsilon(s, \chi \chi', \psi)$.
* `Langlands.IsZetaGenerator.unique`: two generators of the same family of zeta integrals are equal.

## Implementation notes

* The Laurent form of `zeta_eq_laurent_of_lt` holds on the half-plane $\mathrm{Re}(s) > \log_q |\chi(\varpi)|$. The Laurent form of `Langlands.LocalGL1.exists_zeta_eq` holds only for $|\chi(\varpi) q^{1 - s}| \le 1$, and this region does not meet the strip of Tate's functional equation. The proof here uses the sharp lemmas of `Langlands.Local.GL1Epsilon`.
* The meromorphic continuation of the zeta integrals is not necessary. On the strip $a < \mathrm{Re}(s) < a + 1$, with $a = \log_q |\chi \chi'(\varpi)|$, Tate's functional equation and the two Laurent forms give the identity of Laurent polynomials. Both sides are entire functions of $s$, so the identity holds for all $s$ by `eq_of_differentiable_of_eqOn_strip`.
* The Haar measure is regular and σ-finite by the instances of the library, because $K$ is second countable and locally compact. Thus `isRSEpsilonFactor_one` needs only `IsAddHaarMeasure`.
* The direct sum uses `Matrix.fromBlocks` and the reindexing by `finSumFinEquiv`. The proofs copy the pattern of the tensor product in `Langlands.Local.LanglandsFamilyPairs`.

## What is still open

* The inductivity in degree zero of the Galois ε-factor. It needs the induction of Weil-Deligne representations from $W_L$ to $W_K$ for a finite extension $L / K$, and the restriction of the Artin map, which are not in the library. For this reason `IsWDEpsilonAdditive` contains only the additivity on direct sums.
* A concrete ε-factor with the conditions of `IsWDEpsilon` or `IsWDEpsilonAdditive` in each dimension, and the uniqueness of the Galois ε-factor.
* The Rankin-Selberg ε-factor for $n \ge 2$.

## References

* J. Tate, *Number theoretic background*, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979.
* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in Modular functions of one variable II, Lecture Notes in Math. 349, Springer 1973.
* H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), 367 to 464.
-/

namespace Langlands

universe u

open Matrix MeasureTheory

section Block

variable {m m' : ℕ}

/-- The block diagonal matrix $\begin{pmatrix} A & 0 \\ 0 & B \end{pmatrix}$ of size $m + m'$, indexed by $\mathrm{Fin}(m + m')$. -/
noncomputable def blockMat (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    Matrix (Fin (m + m')) (Fin (m + m')) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

/-- The block diagonal matrices multiply blockwise. -/
theorem blockMat_mul (A A' : Matrix (Fin m) (Fin m) ℂ) (B B' : Matrix (Fin m') (Fin m') ℂ) :
    blockMat (A * A') (B * B') = blockMat A B * blockMat A' B' := by
  rw [blockMat, blockMat, blockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

/-- The block diagonal matrix of two identity matrices is the identity matrix. -/
theorem blockMat_one : blockMat (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m') (Fin m') ℂ) = 1 := by
  rw [blockMat, ← map_one (Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv : Fin m ⊕ Fin m' ≃ _)),
    ← Matrix.fromBlocks_one]

/-- The block diagonal matrices add blockwise. -/
theorem blockMat_add (A A' : Matrix (Fin m) (Fin m) ℂ) (B B' : Matrix (Fin m') (Fin m') ℂ) :
    blockMat (A + A') (B + B') = blockMat A B + blockMat A' B' := by
  rw [blockMat, blockMat, blockMat, ← map_add, Matrix.fromBlocks_add]
  simp

/-- A scalar multiple of a block diagonal matrix is the block diagonal matrix of the scalar multiples. -/
theorem blockMat_smul (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m') (Fin m') ℂ) :
    blockMat (c • A) (c • B) = c • blockMat A B := by
  rw [blockMat, blockMat, ← map_smul, Matrix.fromBlocks_smul]
  simp

/-- The block diagonal matrix of two zero matrices is the zero matrix. -/
theorem blockMat_zero : blockMat (0 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m') (Fin m') ℂ) = 0 := by
  simpa using blockMat_smul (0 : ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m') (Fin m') ℂ)

variable (m m') in
/-- The algebra homomorphism $(A, B) \mapsto \mathrm{diag}(A, B)$ from $M_m(\mathbb{C}) \times M_{m'}(\mathbb{C})$ to $M_{m + m'}(\mathbb{C})$. -/
noncomputable def blockHom :
    (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m') (Fin m') ℂ) →ₐ[ℂ]
      Matrix (Fin (m + m')) (Fin (m + m')) ℂ where
  toFun p := blockMat p.1 p.2
  map_one' := blockMat_one
  map_mul' p p' := blockMat_mul _ _ _ _
  map_zero' := blockMat_zero
  map_add' p p' := blockMat_add _ _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change blockMat (c • 1) (c • 1) = _
    rw [blockMat_smul, blockMat_one]

/-- The value of `blockHom` at $(A, B)$ is the block diagonal matrix of $A$ and $B$. -/
theorem blockHom_apply (p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m') (Fin m') ℂ) :
    blockHom m m' p = blockMat p.1 p.2 := rfl

/-- If the minimal polynomial of the linear map of a matrix $A$ divides $p$, then $p(A) = 0$. -/
theorem aeval_toLin'_eq_zero {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} {p : Polynomial ℂ}
    (hp : minpoly ℂ (Matrix.toLin' A) ∣ p) : Polynomial.aeval A p = 0 := by
  have h0 : Polynomial.aeval (Matrix.toLin' A) p = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval ℂ _)
  have : Polynomial.aeval (Matrix.toLinAlgEquiv' A) p = Matrix.toLinAlgEquiv' (Polynomial.aeval A p) :=
    Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _) A p
  rw [← map_zero (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _)] at h0
  exact (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _).injective (this.symm.trans h0)

/-- The block diagonal matrix of two semisimple matrices is semisimple. The radical of the product of the two minimal polynomials is squarefree and it kills the block diagonal matrix. -/
theorem isSemisimple_blockMat {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin m') (Fin m') ℂ}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) (hB : Module.End.IsSemisimple (Matrix.toLin' B)) :
    Module.End.IsSemisimple (Matrix.toLin' (blockMat A B)) := by
  classical
  set pA := minpoly ℂ (Matrix.toLin' A)
  set pB := minpoly ℂ (Matrix.toLin' B)
  have hpA : pA ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have hpB : pB ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  set P := UniqueFactorizationMonoid.radical (pA * pB)
  have hAP : pA ∣ P := (UniqueFactorizationMonoid.dvd_radical_iff hA.minpoly_squarefree.isRadical
    (mul_ne_zero hpA hpB)).2 (dvd_mul_right _ _)
  have hBP : pB ∣ P := (UniqueFactorizationMonoid.dvd_radical_iff hB.minpoly_squarefree.isRadical
    (mul_ne_zero hpA hpB)).2 (dvd_mul_left _ _)
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := P)
    UniqueFactorizationMonoid.squarefree_radical ?_
  have h1 : Polynomial.aeval (A, B) P = 0 := by
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Matrix (Fin m) (Fin m) ℂ)
        (Matrix (Fin m') (Fin m') ℂ)) (A, B) P
      rw [AlgHom.fst_apply, AlgHom.fst_apply] at this
      change (Polynomial.aeval (A, B) P).1 = 0
      rw [← this]
      exact aeval_toLin'_eq_zero hAP
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Matrix (Fin m) (Fin m) ℂ)
        (Matrix (Fin m') (Fin m') ℂ)) (A, B) P
      rw [AlgHom.snd_apply, AlgHom.snd_apply] at this
      change (Polynomial.aeval (A, B) P).2 = 0
      rw [← this]
      exact aeval_toLin'_eq_zero hBP
  have e1 : Polynomial.aeval (Matrix.toLinAlgEquiv' (blockHom m m' (A, B))) P =
      Matrix.toLinAlgEquiv' (blockHom m m' (Polynomial.aeval (A, B) P)) := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply]
  exact e1.trans (by rw [h1, map_zero, map_zero])

end Block

namespace WeilDeligneRep

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {m m' : ℕ}

/-- The homomorphism $w \mapsto \mathrm{diag}(r(w), r'(w))$ from $W_K$ to $GL_{m + m'}(\mathbb{C})$. -/
noncomputable def directSumR (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    WeilGroup K →* GL (Fin (m + m')) ℂ :=
  (Units.map (blockHom m m').toMonoidHom).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp (ρ.r.prod ρ'.r))

/-- The matrix of $(r \oplus r')(w)$ is $\mathrm{diag}(r(w), r'(w))$. -/
theorem directSumR_apply (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    (directSumR ρ ρ' w : Matrix (Fin (m + m')) (Fin (m + m')) ℂ) =
      blockMat (ρ.r w : Matrix _ _ ℂ) (ρ'.r w) :=
  rfl

/-- The inverse of $(r \oplus r')(w)$ is $\mathrm{diag}(r(w)^{-1}, r'(w)^{-1})$. -/
theorem directSumR_inv_apply (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    (((directSumR ρ ρ' w)⁻¹ : GL (Fin (m + m')) ℂ) : Matrix (Fin (m + m')) (Fin (m + m')) ℂ) =
      blockMat (((ρ.r w)⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ) (((ρ'.r w)⁻¹ : GL (Fin m') ℂ) : Matrix _ _ ℂ) :=
  rfl

/-- **The direct sum of Weil-Deligne representations.** For $\rho = (r, N)$ of dimension $m$ and $\rho' = (r', N')$ of dimension $m'$, the direct sum is $\rho \oplus \rho' = (\mathrm{diag}(r, r'), \mathrm{diag}(N, N'))$ of dimension $m + m'$. -/
noncomputable def directSum (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    WeilDeligneRep K (m + m') where
  r := directSumR ρ ρ'
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := ρ.r.ker ⊓ ρ'.r.ker) (fun w hw => ?_)
      (ρ.isOpen_ker.inter ρ'.isOpen_ker)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hw
    rw [MonoidHom.mem_ker]
    ext1
    rw [directSumR_apply, hw.1, hw.2, Units.val_one, Units.val_one, Units.val_one, blockMat_one]
  N := blockMat ρ.N ρ'.N
  isNilpotent := by
    obtain ⟨a, ha⟩ := ρ.isNilpotent
    obtain ⟨b, hb⟩ := ρ'.isNilpotent
    have h : IsNilpotent ((ρ.N, ρ'.N) : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m') (Fin m') ℂ) :=
      ⟨a + b, Prod.ext (by simp [pow_add, ha]) (by simp [pow_add, hb])⟩
    exact h.map (blockHom m m')
  conj w := by
    rw [directSumR_apply, directSumR_inv_apply, ← blockMat_mul, ← blockMat_mul, ρ.conj w, ρ'.conj w,
      blockMat_smul]
  semisimple w := by
    rw [directSumR_apply]
    exact isSemisimple_blockMat (ρ.semisimple w) (ρ'.semisimple w)

/-- The representation of $W_K$ in $\rho \oplus \rho'$ is $w \mapsto \mathrm{diag}(r(w), r'(w))$. -/
theorem directSum_r (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') (w : WeilGroup K) :
    ((ρ.directSum ρ').r w : Matrix (Fin (m + m')) (Fin (m + m')) ℂ) =
      blockMat (ρ.r w : Matrix _ _ ℂ) (ρ'.r w) :=
  rfl

/-- The monodromy operator of $\rho \oplus \rho'$ is $\mathrm{diag}(N, N')$. -/
theorem directSum_N (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') :
    (ρ.directSum ρ').N = blockMat ρ.N ρ'.N :=
  rfl

end WeilDeligneRep

section Additive

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The additive Galois ε-factor.** The conditions of `IsWDEpsilon`, and the additivity on direct sums: $\varepsilon(s, \rho \oplus \rho', \psi) = \varepsilon(s, \rho, \psi) \varepsilon(s, \rho', \psi)$. The inductivity in degree zero is not part of the conditions, because the induction of Weil-Deligne representations from $W_L$ for a finite extension $L / K$ is not in the library. -/
structure IsWDEpsilonAdditive [MeasurableSpace K] (art : Kˣ ≃ₜ* WeilGroup.Ab K) (ε : WDEpsilonFn K) : Prop
    extends IsWDEpsilon K art ε where
  additive : ∀ μ m m' (ρ : WeilDeligneRep K m) (ρ' : WeilDeligneRep K m') ψ s,
    ε μ (m + m') (ρ.directSum ρ') ψ s = ε μ m ρ ψ s * ε μ m' ρ' ψ s

end Additive

section Unique

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- If $L$ and $L'$ generate the same family $Z$, then $L' = R(X) X^{-N} L$ for $\mathrm{Re}(s)$ large, with $X = q^{-s}$, a polynomial $R$ and $N \ge 0$. -/
theorem IsZetaGenerator.exists_ratio {Z : Set (ℂ → ℂ)} {L L' : ℂ → ℂ} (hL : IsZetaGenerator K Z L)
    (hL' : IsZetaGenerator K Z L') :
    ∃ (R : Polynomial ℂ) (N : ℕ) (s₀ : ℝ), ∀ s : ℂ, s₀ < s.re →
      L' s = R.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ N * L s := by
  obtain ⟨-, hZ, -⟩ := hL
  obtain ⟨-, -, j, f, A, k, s₀, hf, hsum⟩ := hL'
  choose B kB sB hB using fun i => hZ (f i) (hf i)
  set T := ∑ i, kB i
  have hkT : ∀ i, kB i ≤ T := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set s₁ := |s₀| + ∑ i, |sB i|
  have hs₀ : s₀ ≤ s₁ := (le_abs_self _).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  have hsB : ∀ i, sB i ≤ s₁ := fun i => (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |sB i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (abs_nonneg _)))
  refine ⟨∑ i, A i * (B i * Polynomial.X ^ (T - kB i)), k + T, s₁, fun s hs => ?_⟩
  have hx : (residueCard K : ℂ) ^ (-s) ≠ 0 := LocalGL1.cpow_neg_ne_zero s
  rw [hsum s (lt_of_le_of_lt hs₀ hs), Polynomial.eval_finsetSum, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hB i s (lt_of_le_of_lt (hsB i) hs)]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  generalize (residueCard K : ℂ) ^ (-s) = x at hx ⊢
  have hp : x ^ T = x ^ (T - kB i) * x ^ kB i := by rw [← pow_add, Nat.sub_add_cancel (hkT i)]
  rw [pow_add, hp]
  field_simp

/-- Two polynomials that agree at $q^{-t}$ for each real $t > s_0$ are equal. -/
theorem eq_of_eval_qpow {P Q : Polynomial ℂ} {s₀ : ℝ}
    (h : ∀ t : ℝ, s₀ < t → P.eval ((residueCard K : ℂ) ^ (-(t : ℂ))) = Q.eval ((residueCard K : ℂ) ^ (-(t : ℂ)))) :
    P = Q := by
  refine Polynomial.eq_of_infinite_eval_eq P Q ?_
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast LocalGL1.one_lt_residueCard (K := K)
  have hinj : Set.InjOn (fun t : ℝ => (residueCard K : ℂ) ^ (-(t : ℂ))) (Set.Ioi s₀) := by
    intro t _ t' _ htt
    have e : ∀ u : ℝ, (residueCard K : ℂ) ^ (-(u : ℂ)) = (((residueCard K : ℝ) ^ (-u) : ℝ) : ℂ) := by
      intro u
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl
    simp only [e, Complex.ofReal_inj] at htt
    have h1 := (Real.rpow_le_rpow_left_iff hq).1 htt.le
    have h2 := (Real.rpow_le_rpow_left_iff hq).1 htt.ge
    linarith
  exact ((Set.Ioi_infinite s₀).image hinj).mono (by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht)

/-- **The generator of a family of zeta integrals is unique.** If $L$ and $L'$ generate the same family $Z$ in the sense of `IsZetaGenerator`, then $L = L'$. The proof shows $X^N P = R P'$ as polynomials. Since $P'(0) = 1$, the polynomial $P'$ is prime to $X^N$, so $P' \mid P$. In the same way $P \mid P'$, and $P = P'$ because $P(0) = P'(0) = 1$. -/
theorem IsZetaGenerator.unique {Z : Set (ℂ → ℂ)} {L L' : ℂ → ℂ} (hL : IsZetaGenerator K Z L)
    (hL' : IsZetaGenerator K Z L') : L = L' := by
  obtain ⟨R, N, s₀, hR⟩ := hL.exists_ratio hL'
  obtain ⟨R', N', s₁, hR'⟩ := hL'.exists_ratio hL
  obtain ⟨P, hP0, hP⟩ := hL.1
  obtain ⟨P', hP0', hP'⟩ := hL'.1
  have key : ∀ {P P' R : Polynomial ℂ} {N : ℕ} {s₀ : ℝ} {L L' : ℂ → ℂ}, P.coeff 0 = 1 → P'.coeff 0 = 1 →
      (∀ s, L s = (P.eval ((residueCard K : ℂ) ^ (-s)))⁻¹) →
      (∀ s, L' s = (P'.eval ((residueCard K : ℂ) ^ (-s)))⁻¹) →
      (∀ s : ℂ, s₀ < s.re →
        L' s = R.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ N * L s) →
      P' ∣ P := by
    intro P P' R N s₀ L L' hP0 hP0' hP hP' hR
    have hP'0 : P' ≠ 0 := fun h => by simp [h] at hP0'
    have hPP : P * P' ≠ 0 := mul_ne_zero (fun h => by simp [h] at hP0) hP'0
    have hpoly : Polynomial.X ^ N * P = R * P' := by
      refine mul_right_cancel₀ hPP (eq_of_eval_qpow (K := K) (s₀ := s₀) fun t ht => ?_)
      have h := hR t (by simpa using ht)
      rw [hP, hP'] at h
      have hx : (residueCard K : ℂ) ^ (-(t : ℂ)) ≠ 0 := LocalGL1.cpow_neg_ne_zero _
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      generalize (residueCard K : ℂ) ^ (-(t : ℂ)) = x at h hx ⊢
      by_cases ha : P.eval x = 0
      · simp [ha]
      by_cases hb : P'.eval x = 0
      · simp [hb]
      have e : x ^ N * P.eval x = R.eval x * P'.eval x := by
        field_simp at h
        linear_combination h
      rw [e]
    have hX : ¬ Polynomial.X ∣ P' := by
      rw [Polynomial.X_dvd_iff, hP0']
      exact one_ne_zero
    have hcop : IsCoprime P' (Polynomial.X ^ N) :=
      ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 hX).pow_left.symm
    exact hcop.dvd_of_dvd_mul_left ⟨R, by rw [hpoly, mul_comm]⟩
  have h1 : P' ∣ P := key hP0 hP0' hP hP' hR
  have h2 : P ∣ P' := key hP0' hP0 hP' hP hR'
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h2 h1
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hc := congrArg (fun p => Polynomial.coeff p 0) hu
  simp only [Polynomial.mul_coeff_zero, hP0, hP0', ← hr, Polynomial.coeff_C_zero, one_mul] at hc
  rw [← hr, hc, map_one, mul_one] at hu
  funext s
  rw [hP, hP', hu]

end Unique


section Contragredient

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- If $GL_1(K)$ acts on $V$ by $\chi \circ \det$, then it acts on the contragredient by $\chi^{-1} \circ \det$. -/
theorem contragredient_one_apply {χ : Kˣ →* ℂˣ} (π : SmoothRep (GL (Fin 1) K))
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) (g : GL (Fin 1) K)
    (l : π.contragredient.V) :
    π.contragredient.ρ g l = ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • l := by
  let l' : smoothVectors π.ρ.dual := l
  change (π.ρ.dual.subrepresentation _ (smoothVectors_stable _)) g l' =
    ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • l'
  apply Subtype.ext
  refine LinearMap.ext fun v => ?_
  change (π.ρ.dual g l'.1) v = ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * l'.1 v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hπ, map_smul,
    map_inv, MonoidHom.inv_apply, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val]

/-- If $GL_1(K)$ acts on a nonzero space $V$ by $\chi \circ \det$, then the contragredient is not zero. Each linear form is smooth, because its stabilizer contains the stabilizer of a nonzero vector. -/
theorem nontrivial_contragredient_one {χ : Kˣ →* ℂˣ} (π : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) :
    Nontrivial π.contragredient.V := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  have hsm : l ∈ smoothVectors π.ρ.dual := by
    refine Subgroup.isOpen_mono (H₁ := vecStabilizer π.ρ v) (fun g hg => ?_) (π.smooth v)
    rw [mem_vecStabilizer, hπ] at hg
    have h1 : (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = 1 := by
      have : ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) - 1) • v = 0 := by
        rw [sub_smul, hg, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hv)
    rw [mem_vecStabilizer]
    refine LinearMap.ext fun u => ?_
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hπ, map_smul,
      map_inv, map_inv, Units.val_inv_eq_inv_val, h1, inv_one, one_smul]
  refine ⟨⟨(⟨l, hsm⟩ : smoothVectors π.ρ.dual), (0 : smoothVectors π.ρ.dual), fun h => hl ?_⟩⟩
  have := congrArg (fun w : smoothVectors π.ρ.dual => w.1 v) h
  simpa using this

end Contragredient

namespace LocalGL1

section TateLink

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

omit [MeasurableSpace K] [BorelSpace K] in
open Classical in
/-- The function `lFactorInv` is the inverse $L(s, \chi)^{-1}$ of the Tate L-factor `charLFactor`. -/
theorem lFactorInv_eq (χ : Kˣ →* ℂˣ) (s : ℂ) :
    lFactorInv χ s = (charLFactor K (unif K) χ s)⁻¹ := by
  unfold lFactorInv charLFactor IsUnramifiedChar
  split_ifs <;> simp

/-- **The concrete Tate ε-factor satisfies `IsTateEpsilon`.** For a smooth character $\chi$ and an additive character $\psi$ of conductor exponent $n$, the factor `tateEpsilon` of `Langlands.Local.LanglandsFamilyEps` is the factor of Tate's local functional equation. The regularity of the Haar measure follows from the instances of the library. -/
theorem isTateEpsilon_tateEpsilon (μ : Measure K) [μ.IsAddHaarMeasure]
    {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) :
    IsTateEpsilon K μ χ ψ (tateEpsilon μ χ ψ n) := by
  intro φ hφ hφs s hs hs'
  have h := localFunctionalEquation_tateEpsilon μ hχ hψ hφ hφs hs hs'
  rwa [lFactorInv_eq, lFactorInv_eq] at h

/-- The Tate ε-factor is a monomial $c (q^{-s})^k$ with $c \neq 0$. -/
theorem tateEpsilon_monomial (μ : Measure K) [μ.IsAddHaarMeasure] {χ : Kˣ →* ℂˣ}
    (hχ : IsSmoothChar K χ) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, ∀ s, tateEpsilon μ χ ψ n s = c * ((residueCard K : ℂ) ^ (-s)) ^ k := by
  by_cases hu : IsUnramifiedChar χ
  · obtain ⟨c, hc, h⟩ := epsilonUnramified_eq χ μ n
    exact ⟨c, hc, n, fun s => by simp only [tateEpsilon, hu, ↓reduceIte]; exact h s⟩
  · refine ⟨gaussInt χ μ ψ (-n - conductorExp χ),
      gaussInt_ne_zero μ hχ (isRamifiedConductor_conductorExp hχ hu) hψ.continuous hψ,
      (conductorExp χ : ℤ) + n, fun s => ?_⟩
    simp only [tateEpsilon, hu, ↓reduceIte]
    rfl

variable (K) in
/-- In dimension one, the ε-factor `wdEpsilon` of a Weil-Deligne representation $\rho$ is the factor of Tate's local functional equation for $\det r \circ \mathrm{art}_K$. This is the condition `dimOne` of `IsWDEpsilon` for `wdEpsilon`. -/
theorem isTateEpsilon_wdEpsilon (art : Kˣ ≃ₜ* WeilGroup.Ab K) (μ : Measure K) [μ.IsAddHaarMeasure]
    (ρ : WeilDeligneRep K 1) {ψ : AddChar K ℂ} {n : ℤ} (hψ : IsConductor ψ n) :
    IsTateEpsilon K μ (charOfWD K art ρ) ψ (wdEpsilon K art μ ρ ψ n) :=
  isTateEpsilon_tateEpsilon μ (isSmoothChar_charOfWD K art ρ) hψ

end TateLink

section SharpZeta

open Filter Topology

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- The expansion of $T_m$ in $n$ shells, for $|\chi(\varpi) q^{-s}| < 1$. -/
theorem ballZeta_eq_add_of_lt (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1)
    {φ : K → ℂ} (hφm : AEStronglyMeasurable φ μ) {C : ℝ} (hφC : ∀ y, ‖φ y‖ ≤ C) (m : ℤ) (n : ℕ) :
    ballZeta χ μ φ s m = ballZeta χ μ φ s (m + n) + ∑ j ∈ Finset.range n,
      shellCoeff χ μ φ (m + j) * ((residueCard K : ℂ) ^ (-s) * residueCard K) ^ (m + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, ballZeta_eq_succ_of_lt χ μ hχ hs hφm hφC (m + n), Finset.sum_range_succ]
    push_cast
    ring_nf

/-- **Tate's local computation on the sharp half-plane.** For a Schwartz-Bruhat function $\varphi$ there are a polynomial $A$ and $M, N \ge 0$ with $Z(\varphi, \chi, s) = A(X) X^{-M} + \varphi(0) (\chi(\varpi) X)^N T_0(s)$, where $X = q^{-s}$, for each $s$ with $|\chi(\varpi) q^{-s}| < 1$. -/
theorem exists_zeta_eq_of_lt (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {φ : K → ℂ}
    (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    ∃ (A : Polynomial ℂ) (M N : ℕ), ∀ s : ℂ, ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 →
      zeta χ μ φ s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ M +
        φ 0 * ((χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
          ballZeta χ μ (fun _ => 1) s 0 := by
  obtain ⟨N, hN⟩ := exists_nat_eq_of_isLocallyConstant hφ
  obtain ⟨M, hM⟩ := exists_nat_tsupport_subset hφs
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  have hφm : AEStronglyMeasurable φ μ := hφ.continuous.aestronglyMeasurable
  refine ⟨∑ j ∈ Finset.range (M + N), Polynomial.C (shellCoeff χ μ φ (-(M : ℤ) + j) *
    (residueCard K : ℂ) ^ (-(M : ℤ) + j)) * Polynomial.X ^ j, M, N, fun s hs => ?_⟩
  have hX : (residueCard K : ℂ) ^ (-s) ≠ 0 := cpow_neg_ne_zero s
  have h1 : zeta χ μ φ s = ballZeta χ μ φ s (-(M : ℤ)) := by
    unfold zeta ballZeta
    congr 1
    funext y
    by_cases hy : y ∈ ordBall K (-(M : ℤ))
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (fun h => hy (hM h)),
        zero_mul]
  have h2 : ballZeta χ μ φ s N = φ 0 * ballZeta χ μ (fun _ => 1) s N := by
    unfold ballZeta
    rw [← integral_const_mul]
    congr 1
    funext y
    by_cases hy : y ∈ ordBall K N
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hN y hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [h1, ballZeta_eq_add_of_lt μ χ hχ hs hφm hC (-(M : ℤ)) (M + N),
    show -(M : ℤ) + ((M + N : ℕ) : ℤ) = (N : ℤ) by push_cast; ring, h2, ballZeta_one_nat,
    Polynomial.eval_finsetSum, Finset.sum_div]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_zpow, zpow_add₀ hX, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp
  · ring

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- If $|\chi(\varpi) q^{-s}| < 1$, then $1 - \chi(\varpi) q^{-s} \neq 0$. -/
theorem one_sub_ne_zero_of_lt (χ : Kˣ →* ℂˣ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) :
    1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  intro h
  rw [← sub_eq_zero.1 h, norm_one] at hs
  exact lt_irrefl _ hs

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
open Classical in
/-- If $|\chi(\varpi) q^{-s}| < 1$, then $L(s, \chi) \neq 0$. -/
theorem charLFactor_ne_zero_of_lt (χ : Kˣ →* ℂˣ) {s : ℂ}
    (hs : ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1) :
    charLFactor K (unif K) χ s ≠ 0 := by
  unfold charLFactor
  split_ifs
  · exact inv_ne_zero (one_sub_ne_zero_of_lt χ hs)
  · exact one_ne_zero

/-- **The Laurent form of a Tate zeta integral.** For a Schwartz-Bruhat function $\varphi$ there are a polynomial $A$ and $k \ge 0$ with $Z(\varphi, \chi, s) = A(X) X^{-k} L(s, \chi)$, where $X = q^{-s}$, for each $s$ with $|\chi(\varpi) q^{-s}| < 1$. -/
theorem zeta_eq_laurent_of_lt (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) {φ : K → ℂ}
    (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    ∃ (A : Polynomial ℂ) (k : ℕ), ∀ s : ℂ, ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 →
      zeta χ μ φ s = A.eval ((residueCard K : ℂ) ^ (-s)) / ((residueCard K : ℂ) ^ (-s)) ^ k *
        charLFactor K (unif K) χ s := by
  classical
  have hL : ∀ s, charLFactor K (unif K) χ s =
      if ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 then (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 1 := fun s => rfl
  obtain ⟨A, M, N, hA⟩ := exists_zeta_eq_of_lt μ χ hχ hφ hφs
  by_cases hunr : ∀ x : Kˣ, normAbs K x = 1 → χ x = 1
  · refine ⟨A * (1 - Polynomial.C (χ (unif K) : ℂ) * Polynomial.X) +
      Polynomial.C (φ 0 * (μ.real (ordShell K 0) : ℂ) * (χ (unif K) : ℂ) ^ N) *
        Polynomial.X ^ (N + M), M, fun s hs => ?_⟩
    have h0 := ballZeta_one_zero_of_lt χ μ hχ hs
    rw [shellCoeff_one_of_unramified χ μ hunr] at h0
    have h1 := one_sub_ne_zero_of_lt χ hs
    have hT : ballZeta χ μ (fun _ => 1) s 0 =
        (μ.real (ordShell K 0) : ℂ) / (1 - (χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)) := by
      rw [← h0, mul_div_cancel_right₀ _ h1]
    rw [hA s hs, hT, (hL s).trans (ite_eq_left hunr)]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
    have hXs : (residueCard K : ℂ) ^ (-s) ≠ 0 := cpow_neg_ne_zero s
    generalize (residueCard K : ℂ) ^ (-s) = X at hXs h1 ⊢
    generalize (χ (unif K) : ℂ) = d at h1 ⊢
    have h1' : 1 - X * d ≠ 0 := by rwa [mul_comm]
    field_simp
    ring
  · simp only [not_forall] at hunr
    obtain ⟨u, hu, hχu⟩ := hunr
    refine ⟨A, M, fun s hs => ?_⟩
    have h0 := ballZeta_one_zero_of_lt χ μ hχ hs
    rw [shellCoeff_one_of_ramified χ μ hu hχu] at h0
    have hT : ballZeta χ μ (fun _ => 1) s 0 = 0 :=
      (mul_eq_zero.1 h0).resolve_right (one_sub_ne_zero_of_lt χ hs)
    have hn : ¬ ∀ x : Kˣ, normAbs K x = 1 → χ x = 1 := fun h => hχu (h u hu)
    rw [hA s hs, hT, (hL s).trans (ite_eq_right hn)]
    ring

omit [MeasurableSpace K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- If $\mathrm{Re}(s) > \log_q |\chi(\varpi)|$, then $|\chi(\varpi) q^{-s}| < 1$. -/
theorem norm_lt_one_of_logb_lt (χ : Kˣ →* ℂˣ) {s : ℂ}
    (hs : Real.logb (residueCard K) ‖(χ (unif K) : ℂ)‖ < s.re) :
    ‖(χ (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := by
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast one_lt_residueCard
  have hq0 : (0 : ℝ) < residueCard K := by linarith
  have hc : 0 < ‖(χ (unif K) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos residueCard_pos', Complex.neg_re]
  conv_lhs => rw [← Real.rpow_logb hq0 hq.ne' hc]
  rw [← Real.rpow_add hq0]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

/-- The Fourier transform of a Schwartz-Bruhat function is a Schwartz-Bruhat function, for an additive character with a conductor exponent. -/
theorem fourier_isSchwartzBruhat {ψ : AddChar K ℂ} {n : ℤ}
    (hψ : IsConductor ψ n) {φ : K → ℂ} (hφ : IsLocallyConstant φ) (hφs : HasCompactSupport φ) :
    IsLocallyConstant (fourier μ ψ φ) ∧ HasCompactSupport (fourier μ ψ φ) := by
  obtain ⟨N, T, hT⟩ := exists_eq_sum_ballIndicator hφ hφs
  have hφe : φ = fun x => ∑ b ∈ T, φ b * ballIndicator b N x := funext hT
  have hbb : ∀ b ∈ T, IsBallBounded μ (ballIndicator b N) := fun b _ =>
    isBallBounded_of_isLocallyConstant μ (isLocallyConstant_ballIndicator b N)
      (hasCompactSupport_ballIndicator b N)
  have hF : fourier μ ψ φ = fun ξ => ∑ b ∈ T, φ b *
      (ψ (b * ξ) * (ordBall K (-n - N)).indicator (fun _ => (μ.real (ordBall K N) : ℂ)) ξ) := by
    conv_lhs => rw [hφe]
    rw [fourier_sum μ hψ.continuous T _ _ hbb]
    funext ξ
    simp only [fourier_ballIndicator μ hψ]
  have hind : IsLocallyConstant
      ((ordBall K (-n - N)).indicator (fun _ => (μ.real (ordBall K N) : ℂ))) :=
    isLocallyConstant_indicator (isOpen_ordBall _) (isClosed_ordBall _)
      (fun _ _ => Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨?_, ?_⟩
  · rw [hF, IsLocallyConstant.iff_eventually_eq]
    intro ξ
    have hb : ∀ b ∈ T, ∀ᶠ η in 𝓝 ξ, ψ (b * η) = ψ (b * ξ) := fun b _ =>
      (hψ.isLocallyConstant.comp_continuous (continuous_const.mul continuous_id)).eventually_eq ξ
    filter_upwards [(Filter.eventually_all_finset T).2 hb, hind.eventually_eq ξ] with η h1 h2
    exact Finset.sum_congr rfl fun b hbT => by rw [h1 b hbT, h2]
  · refine HasCompactSupport.intro (isCompact_ordBall (-n - N)) fun ξ hξ => ?_
    rw [hF]
    exact Finset.sum_eq_zero fun b _ => by rw [Set.indicator_of_notMem hξ, mul_zero, mul_zero]

end SharpZeta

end LocalGL1

section PairsOne

open LocalGL1 Filter Topology

/-- **The identity theorem on a strip.** Two entire functions that agree on the strip $a < \mathrm{Re}(s) < b$ are equal. -/
theorem eq_of_differentiable_of_eqOn_strip {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) {a b : ℝ} (hab : a < b)
    (h : ∀ s : ℂ, a < s.re → s.re < b → F s = G s) : F = G := by
  set U : Set ℂ := {s | a < s.re} ∩ {s | s.re < b}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  set z₀ : ℂ := (((a + b) / 2 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ U := by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq, z₀, Complex.ofReal_re] <;> linarith
  have hH : AnalyticOnNhd ℂ (F - G) Set.univ :=
    (hF.sub hG).differentiableOn.analyticOnNhd isOpen_univ
  have hev : (F - G) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hU.mem_nhds hz₀] with s hs
    simp [h s hs.1 hs.2]
  have := hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) hev
  funext s
  exact sub_eq_zero.1 (this (Set.mem_univ s))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The function $s \mapsto A(q^{f(s)}) (q^{f(s)})^{-k}$ is entire for an entire function $f$. -/
theorem differentiable_laurent (A : Polynomial ℂ) (k : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun s => A.eval ((residueCard K : ℂ) ^ (f s)) / ((residueCard K : ℂ) ^ (f s)) ^ k := by
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast (residueCard_pos' (K := K)).ne'
  have hX : Differentiable ℂ fun s => (residueCard K : ℂ) ^ (f s) := Differentiable.const_cpow hf (Or.inl hq)
  refine ((Polynomial.differentiable A).comp hX).div (hX.pow k) fun s => ?_
  exact pow_ne_zero _ (Complex.cpow_ne_zero_iff.2 (Or.inl hq))

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- **The ε-factor of pairs for $m = m' = 1$.** For representations of $GL_1(K)$ by $\chi \circ \det$ and $\chi' \circ \det$ on nonzero spaces and an additive character $\psi$ of conductor exponent $k$, the Tate ε-factor $\varepsilon(s, \chi \chi', \psi)$ is the Rankin-Selberg ε-factor. The functional equation of Laurent polynomials holds on the strip of Tate's functional equation, so it holds for all $s$ by the identity theorem. -/
theorem isRSEpsilonFactor_one {χ χ' : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ') (π π' : SmoothRep (GL (Fin 1) K)) [Nontrivial π.V] [Nontrivial π'.V]
    (hπ : ∀ g v, π.ρ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v)
    (hπ' : ∀ g v, π'.ρ g v = (χ' (Matrix.GeneralLinearGroup.det g) : ℂ) • v) {ψ : AddChar K ℂ}
    {k : ℤ} (hψ : IsConductor ψ k) :
    IsRSEpsilonFactor μ π π' ψ (tateEpsilon μ (χ * χ') ψ k) := by
  set η := χ * χ' with hηdef
  have hη : IsSmoothChar K η := isSmoothChar_mul hχ hχ'
  have := nontrivial_contragredient_one π hπ
  have := nontrivial_contragredient_one π' hπ'
  refine ⟨charLFactor K (unif K) η, charLFactor K (unif K) η⁻¹,
    isRSLFactor_one μ hχ hχ' π π' hπ hπ' ψ, ?_, tateEpsilon_monomial μ hη hψ, ?_⟩
  · have := isRSLFactor_one μ (isSmoothChar_inv χ hχ) (isSmoothChar_inv χ' hχ') π.contragredient
      π'.contragredient (contragredient_one_apply π hπ) (contragredient_one_apply π' hπ') ψ⁻¹
    rwa [inv_mul_inv_char] at this
  intro ω' _ p hp
  obtain ⟨c, φ, hφ, hφs, rfl⟩ := mem_rsFEPairs_one μ π π' hπ hπ' ψ hp
  obtain ⟨hf1, hf2⟩ := fourier_isSchwartzBruhat μ hψ hφ hφs
  obtain ⟨A0, k0, h0⟩ := zeta_eq_laurent_of_lt μ η hη hφ hφs
  obtain ⟨A1, k1, h1⟩ := zeta_eq_laurent_of_lt μ η⁻¹ (isSmoothChar_inv η hη) hf1 hf2
  set a := Real.logb (residueCard K) ‖(η (unif K) : ℂ)‖
  have ha1 : Real.logb (residueCard K) ‖((η⁻¹ (unif K) : ℂˣ) : ℂ)‖ = -a := by
    rw [inv_apply_coe, norm_inv, Real.logb_inv]
  refine ⟨Polynomial.C c * A0, Polynomial.C c * A1, k0, k1, a, -a, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · simp only
    rw [h0 s (norm_lt_one_of_logb_lt η hs), Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · simp only
    rw [h1 s (norm_lt_one_of_logb_lt η⁻¹ (by rw [ha1]; exact hs)), Polynomial.eval_mul,
      Polynomial.eval_C]
    ring
  obtain ⟨cε, -, kε, hε⟩ := tateEpsilon_monomial μ hη hψ
  have hq : (residueCard K : ℂ) ≠ 0 := by exact_mod_cast (residueCard_pos' (K := K)).ne'
  have key := eq_of_differentiable_of_eqOn_strip
    (F := fun s => (Polynomial.C c * A1).eval ((residueCard K : ℂ) ^ (-(1 - s))) /
      ((residueCard K : ℂ) ^ (-(1 - s))) ^ k1)
    (G := fun s => tateEpsilon μ η ψ k s * ((Polynomial.C c * A0).eval ((residueCard K : ℂ) ^ (-s)) /
      ((residueCard K : ℂ) ^ (-s)) ^ k0))
    (differentiable_laurent _ _ ((differentiable_const (1 : ℂ)).sub differentiable_id).neg) ?_
    (lt_add_one a) ?_
  · intro s
    have := congrFun key s
    rw [this]
    simp
  · have hε' : tateEpsilon μ η ψ k = fun s => cε * ((residueCard K : ℂ) ^ (-s)) ^ kε := funext hε
    rw [hε']
    have hX : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
      Differentiable.const_cpow differentiable_id.neg (Or.inl hq)
    exact ((differentiable_const _).mul (Differentiable.zpow hX (Or.inl fun s => cpow_neg_ne_zero s))).mul
      (differentiable_laurent _ _ differentiable_id.neg)
  · intro s hs hs'
    have hs1 : ‖(η (unif K) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := norm_lt_one_of_logb_lt η hs
    have hs2 : ‖((η⁻¹ (unif K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 :=
      norm_lt_one_of_logb_lt η⁻¹ (by rw [ha1, Complex.sub_re, Complex.one_re]; linarith)
    have hs2' : ‖(η (unif K) : ℂ)⁻¹ * (residueCard K : ℂ) ^ (-(1 - s))‖ < 1 := by
      rwa [inv_apply_coe] at hs2
    have FE := isTateEpsilon_tateEpsilon μ hη hψ φ hφ hφs s hs1 hs2'
    rw [h0 s hs1, h1 (1 - s) hs2, mul_inv_cancel_right₀ (charLFactor_ne_zero_of_lt η⁻¹ hs2),
      mul_inv_cancel_right₀ (charLFactor_ne_zero_of_lt η hs1)] at FE
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_div_assoc, FE, mul_div_assoc]
    ring

end PairsOne

end Langlands
