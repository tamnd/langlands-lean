/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.JacquetPrincipal

/-!
# Subrepresentations of the principal series of $GL_2$

Let $K$ be a nonarchimedean local field, let $B = TN$ be the upper triangular Borel subgroup of $G = GL_2(K)$, and let $\chi_1, \chi_2$ be smooth characters of $K^\times$. Let $V = \mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ be the unnormalized principal series. This file proves that each nonzero $G$-stable subspace $W$ of $V$ has a nonzero Jacquet module $W_N$, and that $W_N$ maps onto the character $\chi_1 \otimes \chi_2$ of $T$. It gives Frobenius reciprocity in the form $\mathrm{Hom}_G(\pi, \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)) \cong \mathrm{Hom}_T(\pi_N, \alpha_1 \otimes \alpha_2)$. With the composition series of $V_N$, this shows that a nonzero map of representations of $G$ between two principal series exists only for the two expected pairs of characters. These are the first steps of the irreducibility criterion of Bushnell and Henniart, chapter 3, section 9. The criterion itself is not proved here: see the open parts below.

## Main definitions

* `Langlands.SmoothRep.subIncl`, `Langlands.SmoothRep.quotientMk`: the inclusion of a $G$-stable subspace and the map to the quotient, as maps of representations.
* `Langlands.SmoothRep.borelHomEquiv`: the maps of representations of $B$ from $\pi$ to $\alpha_1 \otimes \alpha_2$ are the $N$-invariant maps of representations of $T$.
* `Langlands.SmoothRep.jacquetFrobenius`: Frobenius reciprocity $\mathrm{Hom}_G(\pi, \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)) \cong \mathrm{Hom}_T(\pi_N, \alpha_1 \otimes \alpha_2)$.
* `Langlands.GL2.diagTorus`: the diagonal matrix $\mathrm{diag}(a, d)$ as an element of $T$.
* `Langlands.principalSeriesSubJacquetEval`: the map $W_N \to \chi_1 \otimes \chi_2$, $[f] \mapsto f(1)$, for a $G$-stable subspace $W$.

## Main results

* `Langlands.GL2.borel_eq_torus_mul_unipotent`: each $b \in B$ is $t n$ with $t \in T$ and $n \in N$.
* `Langlands.GL2.torusChar_inj`: the character $\alpha_1 \otimes \alpha_2$ of $T$ determines $\alpha_1$ and $\alpha_2$.
* `Langlands.principalSeriesInd_not_le_jacquetKer`: a nonzero $G$-stable subspace $W$ of $V$ is not contained in $V(N)$.
* `Langlands.principalSeriesSubJacquetEval_surjective`, `Langlands.principalSeriesInd_sub_jacquet_nontrivial`: for such $W$, the Jacquet module $W_N$ maps onto $\chi_1 \otimes \chi_2$, so $W_N \neq 0$.
* `Langlands.principalSeriesJacquet_exists_basis`: a basis $x_0, y_1$ of $V_N$, where $y_1$ spans the image of $(V_w)_N$.
* `Langlands.principalSeriesJacquet_hom_eq`: a nonzero map of representations of $T$ from $V_N$ to a character $\theta$ exists only if $\theta$ is $\chi_1 \otimes \chi_2$ or `Langlands.bigCellChar`.
* `Langlands.principalSeriesInd_hom_eq`: a nonzero map of representations of $G$ from $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ to $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ exists only if $\alpha_1 \otimes \alpha_2$ is $\chi_1 \otimes \chi_2$ or `Langlands.bigCellChar`.
* `Langlands.principalSeriesInd_quotient_jacquet_iso`: if $W \neq 0$ is $G$-stable and $(V / W)_N \neq 0$, then $(V / W)_N$ is the character `Langlands.bigCellChar`.
* `Langlands.principalSeriesInd_exists_hom_of_quotient`: in this case there is a nonzero map of representations of $G$ from $V$ to $\mathrm{Ind}_B^G(\chi_2|\cdot| \otimes \chi_1|\cdot|^{-1})$ that vanishes on $W$.
* `Langlands.normPrincipalSeries_sub_jacquet_nontrivial`, `Langlands.normPrincipalSeries_sub_jacquet_exists_surjective`: the same results on $W_N$ for the normalized principal series.
* `Langlands.normPrincipalSeries_hom_eq`: a nonzero map of representations of $G$ from the normalized principal series of $(\chi_1, \chi_2)$ to that of $(\chi_1', \chi_2')$ exists only if $(\chi_1', \chi_2')$ is $(\chi_1, \chi_2)$ or $(\chi_2, \chi_1)$.
* `Langlands.normPrincipalSeries_exists_hom_of_quotient`: if $W \neq 0$ is a $G$-stable subspace of the normalized principal series of $(\chi_1, \chi_2)$ and the quotient $Q$ has $Q_N \neq 0$, then there is a nonzero map of representations of $G$ to the normalized principal series of $(\chi_2, \chi_1)$ that vanishes on $W$.

## Proof

Let $W \neq 0$ be $G$-stable. If $f \in W$ is not zero, then $f(g) \neq 0$ for some $g$, and $g \cdot f \in W$ has value $f(g)$ at $1$. The map $V_N \to \chi_1 \otimes \chi_2$, $[f] \mapsto f(1)$, vanishes on $V(N)$, so $W \not\le V(N)$ and $W_N$ maps onto $\chi_1 \otimes \chi_2$. Frobenius reciprocity for $B$ with Jacquet's description of $N$-invariant maps gives `Langlands.SmoothRep.jacquetFrobenius`. The Jacquet module $V_N$ has the basis $x_0, y_1$, where $T$ acts on $y_1$ by `Langlands.bigCellChar` and on $x_0$ by $\chi_1 \otimes \chi_2$ modulo $y_1$. Thus a nonzero map $\varphi : V_N \to \theta$ gives $\theta = $ `Langlands.bigCellChar` if $\varphi(y_1) \neq 0$, and $\theta = \chi_1 \otimes \chi_2$ if $\varphi(y_1) = 0$. For the quotient $Q = V / W$, a function $f \in W$ with $f(1) \neq 0$ shows that the image of $x_0$ in $Q_N$ is a multiple of the image of $y_1$. Thus $Q_N$ is spanned by the image of $y_1$. In the normalized form, `Langlands.bigCellChar` of $(\chi_1|\cdot|^{1/2}, \chi_2|\cdot|^{-1/2})$ is the character $\chi_2|\cdot|^{1/2} \otimes \chi_1|\cdot|^{-1/2}$, because $|\cdot|^{-1/2}|\cdot| = |\cdot|^{1/2}$.

## Open parts

The irreducibility criterion of Bushnell and Henniart, chapter 3, section 9, is not proved in this file. It states that the normalized principal series of $(\chi_1, \chi_2)$ is irreducible if $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$. The results of this file reduce it to the two statements below. The module `Langlands.Smooth.IrreducibilityCriterion` proves the criterion, and both statements follow from it.

* A nonzero quotient $Q$ of the normalized principal series has $Q_N \neq 0$. This needs the duality $(\mathrm{Ind}_B^G \chi)^\vee \cong \mathrm{Ind}_B^G(\chi^{-1})$ of normalized induction and the exactness of the Jacquet functor on contragredients, or an equal argument with the Hecke algebra. These are not in the library.
* If $\chi_1 \chi_2^{-1} \neq |\cdot|^{\pm 1}$, each nonzero map of representations of $G$ from the normalized principal series of $(\chi_1, \chi_2)$ to that of $(\chi_2, \chi_1)$ is injective. This needs the intertwining operator $M(w)$ and its composition $M(w^{-1}) M(w)$, which are not in the library.

With these two statements, a proper nonzero $G$-stable subspace $W$ gives a nonzero map that vanishes on $W$ by `Langlands.normPrincipalSeries_exists_hom_of_quotient`, and this contradicts the injectivity. The description of the reducible case is still open.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, chapter 3, section 9.
* W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive groups*.
-/

universe u

open Representation Matrix

namespace Langlands

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- The inclusion $W \to V$ of a subrepresentation, as a map of representations. -/
def subIncl (π : SmoothRep G) (W : Submodule ℂ π.V) (hW : IsStableSubspace π.ρ W) :
    IntertwiningMap (π.sub W hW).ρ π.ρ where
  toLinearMap := W.subtype
  isIntertwining' _ := rfl

/-- The quotient map $V \to V / W$, as a map of representations. -/
def quotientMk (π : SmoothRep G) (W : Submodule ℂ π.V) (hW : IsStableSubspace π.ρ W) :
    IntertwiningMap π.ρ (π.quotient W hW).ρ where
  toLinearMap := W.mkQ
  isIntertwining' _ := rfl

/-- The quotient map $V \to V / W$ is onto. -/
theorem quotientMk_surjective (π : SmoothRep G) (W : Submodule ℂ π.V)
    (hW : IsStableSubspace π.ρ W) : Function.Surjective (π.quotientMk W hW) :=
  Submodule.mkQ_surjective W

/-- A nonzero map of representations between two characters exists only if the characters are equal. -/
theorem charRep_eq_of_ne_zero {θ θ' : G →* ℂˣ} {hθ : IsOpen (θ.ker : Set G)}
    {hθ' : IsOpen (θ'.ker : Set G)} (f : IntertwiningMap (charRep θ hθ).ρ (charRep θ' hθ').ρ)
    (hf : f ≠ 0) : θ = θ' := by
  let e : (charRep θ hθ).V := ULift.up 1
  have hne : f e ≠ 0 := by
    intro h
    refine hf (IntertwiningMap.ext (LinearMap.ext fun c => ?_))
    obtain ⟨c⟩ := c
    have hc : (ULift.up c : (charRep θ hθ).V) = c • e :=
      ULift.ext (by
        change c = c * 1
        rw [mul_one])
    have h' := map_smul f c e
    rw [← hc, h, smul_zero] at h'
    exact h'
  ext g
  have h1 := IntertwiningMap.isIntertwining _ _ f g e
  have h2 : f ((charRep θ hθ).ρ g e) = (θ g : ℂ) • f e := map_smul f (θ g : ℂ) e
  have h3 : (charRep θ' hθ').ρ g (f e) = (θ' g : ℂ) • f e := rfl
  rw [h2, h3] at h1
  exact smul_left_injective ℂ hne h1

end SmoothRep

end General

section Borel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The torus $T$ normalizes $N$. -/
theorem torus_le_normalizer_unipotent :
    torus K ≤ Subgroup.normalizer (unipotent K : Set (GL (Fin 2) K)) :=
  torus_le_borel.trans borel_le_normalizer_unipotent

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Each $b \in B$ is a product $b = t n$ with $t \in T$ and $n \in N$: $t = b \, n(-x/a)$ and $n = n(x/a)$ for $b = \begin{pmatrix} a & x \\ 0 & d \end{pmatrix}$. -/
theorem borel_eq_torus_mul_unipotent (b : borel K) :
    ∃ t : torus K, ∃ n ∈ unipotent K, (b : GL (Fin 2) K) = t * n := by
  have hb := b.2
  rw [mem_borel] at hb
  have ha := val_zero_zero_ne_zero b.2
  set y : K := b.1.1 0 1 / b.1.1 0 0
  have ht : (b : GL (Fin 2) K) * unip (-y) ∈ torus K := by
    rw [mem_torus]
    simp only [Units.val_mul, unip_val, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hb, y]
    field_simp
    ring
  refine ⟨⟨_, ht⟩, unip y, unip_mem y, ?_⟩
  change (b : GL (Fin 2) K) = (b : GL (Fin 2) K) * unip (-y) * unip y
  rw [mul_assoc, ← unip_add, neg_add_cancel, unip_zero, mul_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The character $\alpha_1 \otimes \alpha_2$ of $B$ at $b = tn$ is the character $\alpha_1 \otimes \alpha_2$ of $T$ at $t$. -/
theorem borelChar_eq_torusChar (α₁ α₂ : Kˣ →* ℂˣ) (b : borel K) (t : torus K) {n : GL (Fin 2) K}
    (hn : n ∈ unipotent K) (hb : (b : GL (Fin 2) K) = t * n) :
    borelChar α₁ α₂ b = torusChar α₁ α₂ t := by
  have : b = ⟨t, torus_le_borel t.2⟩ * ⟨n, unipotent_le_borel hn⟩ := Subtype.ext hb
  rw [this, map_mul, borelChar_unipotent α₁ α₂ ⟨n, unipotent_le_borel hn⟩ hn, mul_one]
  rfl

end GL2

end Borel

section FrobeniusJacquet

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

namespace SmoothRep

/-- A map of representations of $B$ from $\pi|_B$ to the character $\alpha_1 \otimes \alpha_2$ of $B$ is the same as a map of representations of $T$ from $\pi|_T$ to $\alpha_1 \otimes \alpha_2$ that is invariant under $N$, since $B = TN$ and the character is trivial on $N$. -/
noncomputable def borelHomEquiv (π : SmoothRep (GL (Fin 2) K)) {α₁ α₂ : Kˣ →* ℂˣ}
    (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂) :
    IntertwiningMap (π.ρ.comp (GL2.borel K).subtype)
        (charRep (borelChar α₁ α₂) (isOpen_ker_borelChar hα₁ hα₂)).ρ ≃ₗ[ℂ]
      π.nInvariantHom (unipotent K) (torus K)
        (charRep (torusChar α₁ α₂) (isOpen_ker_torusChar hα₁ hα₂)) where
  toFun F :=
    ⟨{ toLinearMap := F.toLinearMap
       isIntertwining' := fun t => by
        ext v
        exact IntertwiningMap.isIntertwining _ _ F ⟨t, torus_le_borel t.2⟩ v },
      fun n hn v => by
        have h := IntertwiningMap.isIntertwining _ _ F ⟨n, unipotent_le_borel hn⟩ v
        change F (π.ρ n v) = F v
        refine h.trans ?_
        change ((borelChar α₁ α₂ ⟨n, unipotent_le_borel hn⟩ : ℂˣ) : ℂ) • F v = F v
        rw [borelChar_unipotent α₁ α₂ _ hn, Units.val_one, one_smul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    { toLinearMap := f.1.toLinearMap
      isIntertwining' := fun b => by
        ext v
        obtain ⟨t, n, hn, hb⟩ := borel_eq_torus_mul_unipotent b
        change f.1 (π.ρ b v) = ((borelChar α₁ α₂ b : ℂˣ) : ℂ) • f.1 v
        rw [hb, map_mul, Module.End.mul_apply, borelChar_eq_torusChar α₁ α₂ b t hn hb]
        refine (IntertwiningMap.isIntertwining _ _ f.1 t (π.ρ n v)).trans ?_
        change ((torusChar α₁ α₂ t : ℂˣ) : ℂ) • f.1 (π.ρ n v) = _
        rw [f.2 n hn v] }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Frobenius reciprocity for the principal series, in the form with the Jacquet module: $\mathrm{Hom}_G(\pi, \mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)) \cong \mathrm{Hom}_T(\pi_N, \alpha_1 \otimes \alpha_2)$. It is the composite of `Langlands.SmoothRep.frobenius`, `Langlands.SmoothRep.borelHomEquiv` and `Langlands.SmoothRep.jacquetEquiv`. -/
noncomputable def jacquetFrobenius (π : SmoothRep (GL (Fin 2) K)) {α₁ α₂ : Kˣ →* ℂˣ}
    (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂) :
    IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ ≃ₗ[ℂ]
      IntertwiningMap (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).ρ
        (charRep (torusChar α₁ α₂) (isOpen_ker_torusChar hα₁ hα₂)).ρ :=
  (π.frobenius (GL2.borel K) _).trans ((π.borelHomEquiv hα₁ hα₂).trans
    (π.jacquetEquiv (unipotent K) (torus K) torus_le_normalizer_unipotent _).symm)

/-- The map of Jacquet modules that `jacquetFrobenius` gives sends the class of $v$ to $\Phi(v)(1)$. -/
theorem jacquetFrobenius_apply (π : SmoothRep (GL (Fin 2) K)) {α₁ α₂ : Kˣ →* ℂˣ}
    (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂)
    (Φ : IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ) (v : π.V) :
    π.jacquetFrobenius hα₁ hα₂ Φ (π.jacquetMk _ _ torus_le_normalizer_unipotent v) =
      ind.toFun (Φ v) 1 :=
  rfl

/-- The inverse of `jacquetFrobenius` sends $\varphi$ to $v \mapsto (g \mapsto \varphi(\overline{\pi(g) v}))$. -/
theorem jacquetFrobenius_symm_apply (π : SmoothRep (GL (Fin 2) K)) {α₁ α₂ : Kˣ →* ℂˣ}
    (hα₁ : IsSmoothChar K α₁) (hα₂ : IsSmoothChar K α₂)
    (φ : IntertwiningMap (π.jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).ρ
      (charRep (torusChar α₁ α₂) (isOpen_ker_torusChar hα₁ hα₂)).ρ) (v : π.V)
    (g : GL (Fin 2) K) :
    ind.toFun ((π.jacquetFrobenius hα₁ hα₂).symm φ v) g =
      φ (π.jacquetMk _ _ torus_le_normalizer_unipotent (π.ρ g v)) :=
  rfl

end SmoothRep

end FrobeniusJacquet

section Diagonal

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace GL2

variable (K) in
/-- The diagonal matrix $\mathrm{diag}(a, d)$ of $T$. -/
noncomputable def diagTorus (a d : Kˣ) : torus K :=
  ⟨⟨!![(a : K), 0; 0, (d : K)], !![((a⁻¹ : Kˣ) : K), 0; 0, ((d⁻¹ : Kˣ) : K)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩,
    by rw [mem_torus]; simp⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The value of $\alpha_1 \otimes \alpha_2$ at $\mathrm{diag}(a, d)$ is $\alpha_1(a)\alpha_2(d)$. -/
theorem torusChar_diagTorus (α₁ α₂ : Kˣ →* ℂˣ) (a d : Kˣ) :
    torusChar α₁ α₂ (diagTorus K a d) = α₁ a * α₂ d := by
  change α₁ (diagFst _) * α₂ (diagSnd _) = _
  congr 2
  · exact Units.ext (by simp [val_diagFst, diagTorus])
  · exact Units.ext (by simp [val_diagSnd, diagTorus])

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Two characters $\alpha_1 \otimes \alpha_2$ and $\beta_1 \otimes \beta_2$ of $T$ are equal exactly when $\alpha_1 = \beta_1$ and $\alpha_2 = \beta_2$. -/
theorem torusChar_inj {α₁ α₂ β₁ β₂ : Kˣ →* ℂˣ} :
    torusChar α₁ α₂ = torusChar β₁ β₂ ↔ α₁ = β₁ ∧ α₂ = β₂ := by
  constructor
  · intro h
    refine ⟨MonoidHom.ext fun a => ?_, MonoidHom.ext fun d => ?_⟩
    · have := DFunLike.congr_fun h (diagTorus K a 1)
      rwa [torusChar_diagTorus, torusChar_diagTorus, map_one, map_one, mul_one, mul_one] at this
    · have := DFunLike.congr_fun h (diagTorus K 1 d)
      rwa [torusChar_diagTorus, torusChar_diagTorus, map_one, map_one, one_mul, one_mul] at this
  · rintro ⟨rfl, rfl⟩
    rfl

end GL2

end Diagonal

section Subrepresentations

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

/-- A nonzero $G$-stable subspace $W$ of the principal series contains a function $f$ with $f(1) \neq 0$: if $f(g) \neq 0$, then the translate $g \cdot f \in W$ has the value $f(g)$ at $1$. -/
theorem principalSeriesInd_exists_mem_ne_zero {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥) :
    ∃ f ∈ W, SmoothRep.ind.toFun f 1 ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have h : SmoothRep.ind.toFun f ≠ 0 := fun h =>
    hf0 (SmoothRep.ind.toFun_injective (h.trans rfl))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h
  refine ⟨(Ψ).ρ g f, hW g hf, ?_⟩
  change SmoothRep.ind.toFun f (1 * g) ≠ 0
  rwa [one_mul]

/-- Each vector $f$ of $V(N)$ has $f(1) = 0$, since evaluation at $1$ is invariant under $N$. -/
theorem principalSeriesInd_eval_eq_zero_of_mem {f : (Ψ).V}
    (hf : f ∈ (Ψ).jacquetKer (unipotent K)) : SmoothRep.ind.toFun f 1 = 0 := by
  have h := congrArg (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂)
    (((Ψ).jacquetMk_eq_zero_iff torus_le_normalizer_unipotent f).2 hf)
  exact h.trans (map_zero _)

/-- A nonzero $G$-stable subspace $W$ of the principal series is not contained in $V(N)$. -/
theorem principalSeriesInd_not_le_jacquetKer {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥) : ¬ W ≤ (Ψ).jacquetKer (unipotent K) := by
  intro h
  obtain ⟨f, hf, hf1⟩ := principalSeriesInd_exists_mem_ne_zero hW hW0
  exact hf1 (principalSeriesInd_eval_eq_zero_of_mem (h hf))

/-- The map $W_N \to \chi_1 \otimes \chi_2$ of representations of $T$, for a $G$-stable subspace $W$ of the principal series: the composite of $W_N \to V_N$ and the evaluation at $1$. -/
noncomputable def principalSeriesSubJacquetEval (W : Submodule ℂ (Ψ).V)
    (hW : IsStableSubspace (Ψ).ρ W) :
    IntertwiningMap (((Ψ).sub W hW).jacquet (unipotent K) (torus K)
        torus_le_normalizer_unipotent).ρ
      (SmoothRep.charRep (torusChar χ₁ χ₂) (isOpen_ker_torusChar hχ₁ hχ₂)).ρ :=
  (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂).comp
    (SmoothRep.jacquetMap torus_le_normalizer_unipotent ((Ψ).subIncl W hW))

/-- The map `principalSeriesSubJacquetEval` sends the class of $f \in W$ to $f(1)$. -/
theorem principalSeriesSubJacquetEval_mk (W : Submodule ℂ (Ψ).V)
    (hW : IsStableSubspace (Ψ).ρ W) (f : W) :
    principalSeriesSubJacquetEval W hW
        (((Ψ).sub W hW).jacquetMk _ _ torus_le_normalizer_unipotent f) =
      SmoothRep.ind.toFun (f : (Ψ).V) 1 :=
  rfl

/-- For a nonzero $G$-stable subspace $W$ of the principal series, the Jacquet module $W_N$ maps onto the character $\chi_1 \otimes \chi_2$ of $T$. Thus $W_N \neq 0$, and $\chi_1 \otimes \chi_2$ is a quotient of $W_N$. -/
theorem principalSeriesSubJacquetEval_surjective {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥) :
    Function.Surjective (principalSeriesSubJacquetEval W hW) := by
  obtain ⟨f, hf, hf1⟩ := principalSeriesInd_exists_mem_ne_zero hW hW0
  set c : ℂ := (SmoothRep.ind.toFun f 1).down
  have hc : c ≠ 0 := fun h => hf1 (ULift.ext h)
  intro y
  refine ⟨(y.down / c) • ((Ψ).sub W hW).jacquetMk _ _ torus_le_normalizer_unipotent ⟨f, hf⟩, ?_⟩
  rw [map_smul, principalSeriesSubJacquetEval_mk]
  apply ULift.ext
  change y.down / c * c = y.down
  field_simp

/-- The Jacquet module $W_N$ of a nonzero $G$-stable subspace $W$ of the principal series is not zero. -/
theorem principalSeriesInd_sub_jacquet_nontrivial {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥) :
    Nontrivial (((Ψ).sub W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V := by
  obtain ⟨x, hx⟩ := principalSeriesSubJacquetEval_surjective hW hW0 (ULift.up 1)
  refine ⟨⟨x, 0, fun h => ?_⟩⟩
  rw [h, map_zero] at hx
  exact one_ne_zero (congrArg ULift.down hx).symm

end Subrepresentations

section JacquetCharacters

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

local notation "ΨN" => principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂

local notation "ev" => principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂

/-- A basis of the Jacquet module $V_N$ of the principal series: a vector $x_0$ with $x_0(1) = 1$ under the evaluation, and a nonzero vector $y_1$ in the image of $(V_w)_N$, on which $T$ acts by the character `bigCellChar`. Each vector of $V_N$ is $x(1) x_0 + c y_1$ for some $c$. -/
theorem principalSeriesJacquet_exists_basis :
    ∃ x₀ y₁ : (ΨN).V, ev x₀ = ULift.up 1 ∧ y₁ ≠ 0 ∧ ev y₁ = 0 ∧
      (∀ t, (ΨN).ρ t y₁ = (bigCellChar χ₁ χ₂ t : ℂ) • y₁) ∧
      ∀ x, ∃ c : ℂ, x = (ev x).down • x₀ + c • y₁ := by
  obtain ⟨e, he⟩ := bigCellJacquet_iso (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
  let e' : (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).V ≃ₗ[ℂ] ULift.{u} ℂ := e
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, e' y₀ = ULift.up 1 := ⟨_, e'.apply_symm_apply _⟩
  obtain ⟨x₀, hx₀⟩ := principalSeriesJacquetEval_surjective hχ₁ hχ₂ (ULift.up 1)
  set ι := bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂
  have hy : ∀ y, y = (e' y).down • y₀ := by
    intro y
    apply e'.injective
    rw [map_smul, hy₀]
    apply ULift.ext
    change (e' y).down = (e' y).down * 1
    rw [mul_one]
  refine ⟨x₀, ι y₀, hx₀, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : y₀ = 0 := bigCellJacquetIncl_injective (h.trans (map_zero ι).symm)
    have h2 := congrArg e' h0
    rw [hy₀, map_zero] at h2
    exact one_ne_zero (congrArg ULift.down h2)
  · exact (bigCellJacquetIncl_exact (ι y₀)).2 ⟨y₀, rfl⟩
  · intro t
    have h1 : (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).ρ t y₀ = (bigCellChar χ₁ χ₂ t : ℂ) • y₀ := by
      apply e'.injective
      rw [map_smul]
      exact he t y₀
    rw [← IntertwiningMap.isIntertwining _ _ ι t y₀, h1, map_smul]
  · intro x
    have hk : ev (x - (ev x).down • x₀) = 0 := by
      rw [map_sub, map_smul, hx₀]
      apply ULift.ext
      change (ev x).down - (ev x).down * 1 = 0
      ring
    obtain ⟨y, hy'⟩ := (bigCellJacquetIncl_exact _).1 hk
    refine ⟨(e' y).down, ?_⟩
    rw [← map_smul ι, ← hy y, hy']
    abel

/-- The value of the evaluation at $t \cdot x_0$ is $\chi_1 \otimes \chi_2(t)$ times its value at $x_0$. -/
theorem principalSeriesJacquetEval_ρ (t : torus K) (x : (ΨN).V) :
    (ev ((ΨN).ρ t x)).down = (torusChar χ₁ χ₂ t : ℂ) * (ev x).down := by
  rw [IntertwiningMap.isIntertwining _ _ ev t x]
  rfl

/-- If $\varphi$ is a map of representations of $T$ to the character $\theta$, and $\varphi(t v) = c \varphi(v) \neq 0$, then $\theta(t) = c$. -/
theorem charRep_val_eq_of_map {V : Type u} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (torus K) V} {θ : torus K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (torus K))}
    (φ : IntertwiningMap ρ (SmoothRep.charRep θ hθ).ρ) (t : torus K) (v : V) (c : ℂ)
    (hv : φ v ≠ 0) (h : φ (ρ t v) = c • φ v) : (θ t : ℂ) = c := by
  have h' : φ (ρ t v) = (θ t : ℂ) • φ v := IntertwiningMap.isIntertwining _ _ φ t v
  exact smul_left_injective ℂ hv (h'.symm.trans h)

/-- A nonzero map of representations of $T$ from the Jacquet module $V_N$ of the principal series to a character $\theta$ exists only if $\theta$ is $\chi_1 \otimes \chi_2$ or the character `bigCellChar` $\mathrm{diag}(a, d) \mapsto \chi_2(a)|a| \chi_1(d)|d|^{-1}$. -/
theorem principalSeriesJacquet_hom_eq {θ : torus K →* ℂˣ} {hθ : IsOpen (θ.ker : Set (torus K))}
    (φ : IntertwiningMap (ΨN).ρ (SmoothRep.charRep θ hθ).ρ) (hφ : φ ≠ 0) :
    θ = torusChar χ₁ χ₂ ∨ θ = bigCellChar χ₁ χ₂ := by
  obtain ⟨x₀, y₁, hx₀, -, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
  by_cases h : φ y₁ = 0
  · left
    have hφx : ∀ x, φ x = (ev x).down • φ x₀ := by
      intro x
      obtain ⟨c, hc⟩ := hspan x
      conv_lhs => rw [hc]
      rw [map_add, map_smul, map_smul, h, smul_zero, add_zero]
    have hx0 : φ x₀ ≠ 0 := by
      intro h0
      refine hφ (IntertwiningMap.ext (LinearMap.ext fun x => ?_))
      have := hφx x
      rw [h0, smul_zero] at this
      exact this
    refine MonoidHom.ext fun t => Units.ext ?_
    refine charRep_val_eq_of_map φ t x₀ _ hx0 ?_
    rw [hφx, principalSeriesJacquetEval_ρ, hx₀]
    change ((torusChar χ₁ χ₂ t : ℂ) * 1) • φ x₀ = _
    rw [mul_one]
  · right
    refine MonoidHom.ext fun t => Units.ext ?_
    refine charRep_val_eq_of_map φ t y₁ _ h ?_
    rw [hρy, map_smul]

/-- A nonzero map of representations of $G$ from $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ to $\mathrm{Ind}_B^G(\alpha_1 \otimes \alpha_2)$ exists only if $\alpha_1 \otimes \alpha_2$ is $\chi_1 \otimes \chi_2$ or `bigCellChar`. This is Frobenius reciprocity `Langlands.SmoothRep.jacquetFrobenius` with the composition series of $V_N$. -/
theorem principalSeriesInd_hom_eq {α₁ α₂ : Kˣ →* ℂˣ} {hα₁ : IsSmoothChar K α₁}
    {hα₂ : IsSmoothChar K α₂} (Φ : IntertwiningMap (Ψ).ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ)
    (hΦ : Φ ≠ 0) : torusChar α₁ α₂ = torusChar χ₁ χ₂ ∨ torusChar α₁ α₂ = bigCellChar χ₁ χ₂ :=
  principalSeriesJacquet_hom_eq ((Ψ).jacquetFrobenius hα₁ hα₂ Φ)
    ((LinearEquiv.map_ne_zero_iff _).2 hΦ)

/-- Let $W$ be a nonzero $G$-stable subspace of the principal series with quotient $Q = V / W$. If $Q_N \neq 0$, then $Q_N$ is the character `bigCellChar` of $T$. Since $W$ contains a function $f$ with $f(1) \neq 0$, the image of $x_0$ in $Q_N$ is a multiple of the image of $y_1$. -/
theorem principalSeriesInd_quotient_jacquet_iso {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥)
    (hQ : Nontrivial (((Ψ).quotient W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V) :
    (((Ψ).quotient W hW).jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent).Iso
      (SmoothRep.charRep (bigCellChar χ₁ χ₂) (isOpen_ker_bigCellChar hχ₁ hχ₂)) := by
  set QN := ((Ψ).quotient W hW).jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent
  let p : IntertwiningMap (ΨN).ρ QN.ρ :=
    SmoothRep.jacquetMap torus_le_normalizer_unipotent ((Ψ).quotientMk W hW)
  have hp : Function.Surjective p :=
    SmoothRep.jacquetMap_surjective _ _ ((Ψ).quotientMk_surjective W hW)
  obtain ⟨x₀, y₁, hx₀, -, -, hρy, hspan⟩ := principalSeriesJacquet_exists_basis
    (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
  obtain ⟨f, hf, hf1⟩ := principalSeriesInd_exists_mem_ne_zero hW hW0
  set c : ℂ := (SmoothRep.ind.toFun f 1).down
  have hc : c ≠ 0 := fun h => hf1 (ULift.ext h)
  let xf : (ΨN).V := (Ψ).jacquetMk _ _ torus_le_normalizer_unipotent f
  obtain ⟨d, hd⟩ := hspan xf
  have hq : (Ψ).quotientMk W hW f = 0 := (Submodule.Quotient.mk_eq_zero W).2 hf
  have hpf : p xf = 0 := by
    change ((Ψ).quotient W hW).jacquetMk _ _ torus_le_normalizer_unipotent
      ((Ψ).quotientMk W hW f) = 0
    rw [hq, map_zero]
  rw [hd, map_add, map_smul, map_smul] at hpf
  have hx : p x₀ = (-d / c) • p y₁ := by
    have hc' : (ev xf).down = c := rfl
    rw [hc'] at hpf
    have h3 : c • p x₀ = -(d • p y₁) := eq_neg_of_add_eq_zero_left hpf
    calc p x₀ = c⁻¹ • (c • p x₀) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (-d / c) • p y₁ := by
        rw [h3, smul_neg, smul_smul, ← neg_smul]
        congr 1
        ring
  have hall : ∀ z : QN.V, ∃ a : ℂ, z = a • p y₁ := by
    intro z
    obtain ⟨x, rfl⟩ := hp z
    obtain ⟨b, hb⟩ := hspan x
    refine ⟨(ev x).down * (-d / c) + b, ?_⟩
    rw [hb, map_add, map_smul, map_smul, hx, smul_smul, add_smul, ← hb]
  have hy0 : p y₁ ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := exists_ne (0 : QN.V)
    obtain ⟨a, rfl⟩ := hall z
    rw [h0, smul_zero] at hz
    exact hz rfl
  let L : ULift.{u} ℂ →ₗ[ℂ] QN.V :=
    LinearMap.toSpanSingleton ℂ _ (p y₁) ∘ₗ ULift.moduleEquiv.toLinearMap
  have hL : ∀ a : ULift.{u} ℂ, L a = a.down • p y₁ := fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, hL, smul_eq_zero] at ha
    rcases ha with ha | ha
    · exact ULift.ext ha
    · exact absurd ha hy0
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨a, rfl⟩ := hall z
    exact ⟨ULift.up a, rfl⟩
  have hρ : ∀ t : torus K, QN.ρ t (p y₁) = (bigCellChar χ₁ χ₂ t : ℂ) • p y₁ := by
    intro t
    rw [← IntertwiningMap.isIntertwining _ _ p t y₁, hρy, map_smul]
  refine SmoothRep.Iso.symm ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun t a => ?_⟩
  obtain ⟨a⟩ := a
  change ((bigCellChar χ₁ χ₂ t : ℂ) * a) • p y₁ = QN.ρ t (a • p y₁)
  rw [map_smul, hρ, smul_smul, mul_comm]

/-- Let $W$ be a nonzero $G$-stable subspace of the principal series $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ with quotient $Q$. If $Q_N \neq 0$, then there is a nonzero map of representations of $G$ from $\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ to $\mathrm{Ind}_B^G(\beta_1 \otimes \beta_2)$ that vanishes on $W$, for $\beta_1 = \chi_2 |\cdot|$ and $\beta_2 = \chi_1 |\cdot|^{-1}$. It comes from $Q_N \cong$ `bigCellChar` and Frobenius reciprocity. -/
theorem principalSeriesInd_exists_hom_of_quotient {W : Submodule ℂ (Ψ).V}
    (hW : IsStableSubspace (Ψ).ρ W) (hW0 : W ≠ ⊥)
    (hQ : Nontrivial (((Ψ).quotient W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V)
    {β₁ β₂ : Kˣ →* ℂˣ} (hβ₁ : IsSmoothChar K β₁) (hβ₂ : IsSmoothChar K β₂)
    (h₁ : β₁ = χ₂ * absChar K) (h₂ : β₂ = χ₁ * (absChar K)⁻¹) :
    ∃ Φ : IntertwiningMap (Ψ).ρ (principalSeriesInd β₁ β₂ hβ₁ hβ₂).ρ,
      Φ ≠ 0 ∧ ∀ f ∈ W, Φ f = 0 := by
  subst h₁ h₂
  set QN := ((Ψ).quotient W hW).jacquet (unipotent K) (torus K) torus_le_normalizer_unipotent
  obtain ⟨e, he⟩ := principalSeriesInd_quotient_jacquet_iso hW hW0 hQ
  let lam : IntertwiningMap QN.ρ
      (SmoothRep.charRep (torusChar (χ₂ * absChar K) (χ₁ * (absChar K)⁻¹))
        (isOpen_ker_torusChar hβ₁ hβ₂)).ρ :=
    ⟨e.toLinearMap, fun t => LinearMap.ext (he t)⟩
  set p := SmoothRep.jacquetMap torus_le_normalizer_unipotent ((Ψ).quotientMk W hW)
  have hp : Function.Surjective p :=
    SmoothRep.jacquetMap_surjective _ _ ((Ψ).quotientMk_surjective W hW)
  set φ := lam.comp p
  refine ⟨((Ψ).jacquetFrobenius hβ₁ hβ₂).symm φ, ?_, fun f hf => ?_⟩
  · refine (LinearEquiv.map_ne_zero_iff _).2 fun h0 => ?_
    obtain ⟨z, hz⟩ := exists_ne (0 : QN.V)
    obtain ⟨x, rfl⟩ := hp z
    have h1 : φ x = 0 := by rw [h0]; rfl
    exact hz (e.injective (h1.trans (map_zero e).symm))
  · refine SmoothRep.ind.toFun_injective (funext fun g => ?_)
    rw [SmoothRep.jacquetFrobenius_symm_apply]
    have hq : (Ψ).quotientMk W hW ((Ψ).ρ g f) = 0 := (Submodule.Quotient.mk_eq_zero W).2 (hW g hf)
    change e (((Ψ).quotient W hW).jacquetMk _ _ torus_le_normalizer_unipotent
      ((Ψ).quotientMk W hW ((Ψ).ρ g f))) = 0
    rw [hq, map_zero, map_zero]

end JacquetCharacters

section Normalized

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open GL2

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Π" => normPrincipalSeries χ₁ χ₂ hχ₁ hχ₂

/-- The identity $\chi |\cdot|^{-1/2} |\cdot| = \chi |\cdot|^{1/2}$ of characters of $K^\times$. -/
theorem mul_sqrtAbsChar_inv_mul_absChar (χ : Kˣ →* ℂˣ) :
    χ * (sqrtAbsChar K)⁻¹ * absChar K = χ * sqrtAbsChar K := by
  rw [← sqrtAbsChar_sq]
  ext x
  simp [pow_two]

/-- The identity $\chi |\cdot|^{1/2} |\cdot|^{-1} = \chi |\cdot|^{-1/2}$ of characters of $K^\times$. -/
theorem mul_sqrtAbsChar_mul_absChar_inv (χ : Kˣ →* ℂˣ) :
    χ * sqrtAbsChar K * (absChar K)⁻¹ = χ * (sqrtAbsChar K)⁻¹ := by
  rw [← sqrtAbsChar_sq]
  ext x
  simp [pow_two]

/-- Each nonzero $G$-stable subspace $W$ of the normalized principal series has a nonzero Jacquet module $W_N$. -/
theorem normPrincipalSeries_sub_jacquet_nontrivial {W : Submodule ℂ (Π).V}
    (hW : IsStableSubspace (Π).ρ W) (hW0 : W ≠ ⊥) :
    Nontrivial (((Π).sub W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V := by
  have key : ∀ π : SmoothRep (GL (Fin 2) K), π = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) → ∀ (W : Submodule ℂ π.V)
      (hW : IsStableSubspace π.ρ W), W ≠ ⊥ →
      Nontrivial ((π.sub W hW).jacquet (unipotent K) (torus K)
        torus_le_normalizer_unipotent).V := by
    intro π hπ
    subst hπ
    exact fun W hW hW0 => principalSeriesInd_sub_jacquet_nontrivial hW hW0
  exact key _ (normPrincipalSeries_eq hχ₁ hχ₂) W hW hW0

/-- Each nonzero $G$-stable subspace $W$ of the normalized principal series has a Jacquet module $W_N$ that maps onto the character $\chi_1|\cdot|^{1/2} \otimes \chi_2|\cdot|^{-1/2}$ of $T$. -/
theorem normPrincipalSeries_sub_jacquet_exists_surjective {W : Submodule ℂ (Π).V}
    (hW : IsStableSubspace (Π).ρ W) (hW0 : W ≠ ⊥) :
    ∃ φ : IntertwiningMap (((Π).sub W hW).jacquet (unipotent K) (torus K)
        torus_le_normalizer_unipotent).ρ
      (SmoothRep.charRep (torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹))
        (isOpen_ker_torusChar (hχ₁.mul isSmoothChar_sqrtAbsChar)
          (hχ₂.mul isSmoothChar_sqrtAbsChar.inv))).ρ,
      Function.Surjective φ := by
  have key : ∀ π : SmoothRep (GL (Fin 2) K), π = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) → ∀ (W : Submodule ℂ π.V)
      (hW : IsStableSubspace π.ρ W), W ≠ ⊥ →
      ∃ φ : IntertwiningMap ((π.sub W hW).jacquet (unipotent K) (torus K)
          torus_le_normalizer_unipotent).ρ
        (SmoothRep.charRep (torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹))
          (isOpen_ker_torusChar (hχ₁.mul isSmoothChar_sqrtAbsChar)
            (hχ₂.mul isSmoothChar_sqrtAbsChar.inv))).ρ,
        Function.Surjective φ := by
    intro π hπ
    subst hπ
    exact fun W hW hW0 => ⟨_, principalSeriesSubJacquetEval_surjective hW hW0⟩
  exact key _ (normPrincipalSeries_eq hχ₁ hχ₂) W hW hW0

/-- A nonzero map of representations of $G$ from the normalized principal series of $(\chi_1, \chi_2)$ to that of $(\chi_1', \chi_2')$ exists only if $(\chi_1', \chi_2')$ is $(\chi_1, \chi_2)$ or $(\chi_2, \chi_1)$. -/
theorem normPrincipalSeries_hom_eq {χ₁' χ₂' : Kˣ →* ℂˣ} {hχ₁' : IsSmoothChar K χ₁'}
    {hχ₂' : IsSmoothChar K χ₂'}
    (Φ : IntertwiningMap (Π).ρ (normPrincipalSeries χ₁' χ₂' hχ₁' hχ₂').ρ) (hΦ : Φ ≠ 0) :
    (χ₁' = χ₁ ∧ χ₂' = χ₂) ∨ (χ₁' = χ₂ ∧ χ₂' = χ₁) := by
  have key : ∀ π σ : SmoothRep (GL (Fin 2) K), π = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) → σ = principalSeriesInd (χ₁' * sqrtAbsChar K)
      (χ₂' * (sqrtAbsChar K)⁻¹) (hχ₁'.mul isSmoothChar_sqrtAbsChar)
      (hχ₂'.mul isSmoothChar_sqrtAbsChar.inv) → ∀ Φ : IntertwiningMap π.ρ σ.ρ, Φ ≠ 0 →
      torusChar (χ₁' * sqrtAbsChar K) (χ₂' * (sqrtAbsChar K)⁻¹) =
          torusChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹) ∨
        torusChar (χ₁' * sqrtAbsChar K) (χ₂' * (sqrtAbsChar K)⁻¹) =
          bigCellChar (χ₁ * sqrtAbsChar K) (χ₂ * (sqrtAbsChar K)⁻¹) := by
    intro π σ hπ hσ
    subst hπ hσ
    exact fun Φ hΦ => principalSeriesInd_hom_eq Φ hΦ
  rcases key _ _ (normPrincipalSeries_eq hχ₁ hχ₂) (normPrincipalSeries_eq hχ₁' hχ₂') Φ hΦ with
    h | h
  · obtain ⟨h1, h2⟩ := torusChar_inj.1 h
    exact Or.inl ⟨mul_right_cancel h1, mul_right_cancel h2⟩
  · rw [bigCellChar, mul_sqrtAbsChar_inv_mul_absChar, mul_sqrtAbsChar_mul_absChar_inv] at h
    obtain ⟨h1, h2⟩ := torusChar_inj.1 h
    exact Or.inr ⟨mul_right_cancel h1, mul_right_cancel h2⟩

/-- Let $W$ be a nonzero $G$-stable subspace of the normalized principal series of $(\chi_1, \chi_2)$, with quotient $Q$. If $Q_N \neq 0$, then there is a nonzero map of representations of $G$ to the normalized principal series of $(\chi_2, \chi_1)$ that vanishes on $W$. -/
theorem normPrincipalSeries_exists_hom_of_quotient {W : Submodule ℂ (Π).V}
    (hW : IsStableSubspace (Π).ρ W) (hW0 : W ≠ ⊥)
    (hQ : Nontrivial (((Π).quotient W hW).jacquet (unipotent K) (torus K)
      torus_le_normalizer_unipotent).V) :
    ∃ Φ : IntertwiningMap (Π).ρ (normPrincipalSeries χ₂ χ₁ hχ₂ hχ₁).ρ,
      Φ ≠ 0 ∧ ∀ f ∈ W, Φ f = 0 := by
  have key : ∀ π σ : SmoothRep (GL (Fin 2) K), π = principalSeriesInd (χ₁ * sqrtAbsChar K)
      (χ₂ * (sqrtAbsChar K)⁻¹) (hχ₁.mul isSmoothChar_sqrtAbsChar)
      (hχ₂.mul isSmoothChar_sqrtAbsChar.inv) → σ = principalSeriesInd (χ₂ * sqrtAbsChar K)
      (χ₁ * (sqrtAbsChar K)⁻¹) (hχ₂.mul isSmoothChar_sqrtAbsChar)
      (hχ₁.mul isSmoothChar_sqrtAbsChar.inv) → ∀ (W : Submodule ℂ π.V)
      (hW : IsStableSubspace π.ρ W), W ≠ ⊥ →
      Nontrivial ((π.quotient W hW).jacquet (unipotent K) (torus K)
        torus_le_normalizer_unipotent).V →
      ∃ Φ : IntertwiningMap π.ρ σ.ρ, Φ ≠ 0 ∧ ∀ f ∈ W, Φ f = 0 := by
    intro π σ hπ hσ
    subst hπ hσ
    intro W hW hW0 hQ
    refine principalSeriesInd_exists_hom_of_quotient hW hW0 hQ _ _ ?_ ?_
    · rw [mul_sqrtAbsChar_inv_mul_absChar]
    · rw [mul_sqrtAbsChar_mul_absChar_inv]
  exact key _ _ (normPrincipalSeries_eq hχ₁ hχ₂) (normPrincipalSeries_eq hχ₂ hχ₁) W hW hW0 hQ

end Normalized

end Langlands
