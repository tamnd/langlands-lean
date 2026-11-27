/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.CuspidalTypes

/-!
# The irreducibility criterion for compact induction

Let $G$ be a topological group, $J$ an open subgroup of $G$ and $\Lambda$ a character of $J$ with open kernel. Let $Z$ be a subgroup of the centre of $G$, for example the centre itself, and assume that $J$ is compact modulo $Z$ in the following form: for each open subgroup $U$ of $J$ the subgroup $(Z \cap J) U$ has finite index in $J$. Below, $Z U$ means $(Z \cap J) U$. This file proves the irreducibility criterion of BH 11.4: if each $g \in G$ that intertwines $\Lambda$ lies in $J$, then $c\text{-}\mathrm{Ind}_J^G \Lambda$ is irreducible.

The proof has three steps. The file `Langlands/Local/CuspidalTypes.lean` gives the second step. First, each nonzero stable subspace $W$ contains a nonzero vector on which $J$ acts by $\Lambda$. For this, translate a nonzero $f \in W$ so that $f(1) \neq 0$, let $U$ be the open subgroup of $J$ of the elements that fix $f$ and lie in the kernel of $\Lambda$, and put $$\varphi = \sum_{j \in J / Z U} \Lambda(j)^{-1} \pi(j) f.$$ The terms do not depend on the representatives, because $Z$ acts on $c\text{-}\mathrm{Ind}_J^G \Lambda$ by $\Lambda$. Then $\pi(j) \varphi = \Lambda(j) \varphi$ and $\varphi(1) = [J : Z U] f(1) \neq 0$. Second, if the intertwining of $\Lambda$ is $J$, then $\varphi$ is a nonzero multiple of the vector `cIndBasic`, which is $\Lambda$ on $J$ and $0$ outside $J$. So `cIndBasic` lies in $W$. Third, each $f$ is the finite sum $\sum_s f(s) \pi(s^{-1}) \, \mathtt{cIndBasic}$ over representatives $s$ of the cosets $J s$ in the support of $f$. So the translates of `cIndBasic` span $c\text{-}\mathrm{Ind}_J^G \Lambda$, and $W$ is everything.

## Main definitions

* `Langlands.IsCompactModCenter`: for each open subgroup $U$ of $J$, the subgroup $(Z \cap J) U$ has finite index in $J$.
* `Langlands.lambdaStab`: the subgroup of the $j \in J$ with $\pi(j) f = \Lambda(j) f$.
* `Langlands.cInd.toFunLin`: the evaluation $f \mapsto f(x)$, as a linear form on $c\text{-}\mathrm{Ind}_J^G \Lambda$.

## Main results

* `Langlands.cInd.ρ_center`: a central element $z \in J$ acts on $c\text{-}\mathrm{Ind}_J^G \Lambda$ by $\Lambda(z)$.
* `Langlands.exists_isotypic_of_ne_zero`: a nonzero vector $f$ gives a nonzero vector $\varphi$, in the span of the translates of $f$, on which $J$ acts by $\Lambda$.
* `Langlands.exists_isotypic_mem`: each nonzero stable subspace contains a nonzero vector on which $J$ acts by $\Lambda$.
* `Langlands.eq_sum_translate_cIndBasic`: each $f$ is a finite sum $\sum_{s \in T} f(s) \pi(s^{-1}) \, \mathtt{cIndBasic}$.
* `Langlands.span_translate_cIndBasic`: the translates of `cIndBasic` span $c\text{-}\mathrm{Ind}_J^G \Lambda$.
* `Langlands.isIrreducible_cInd`: if the intertwining of $\Lambda$ is $J$, then $c\text{-}\mathrm{Ind}_J^G \Lambda$ is irreducible (BH 11.4).

## Implementation notes

The group $Z$ is any subgroup of the centre of $G$, and only $Z \cap J$ is used. An example is the centre $F^\times$ of $GL_2(F)$. The condition `IsCompactModCenter` is stated with the open subgroups of $J$ for the topology of a subspace. For $J$ open and compact modulo $Z$ it holds, because the image of $U$ in $J / Z$ is an open subgroup of a compact group. The averaging is a sum over the finite type $J / ((Z \cap J) \sqcup U)$ of left cosets. The decomposition of the third step does not use that the vectors are smooth.

## Still open

* The proof that `IsCompactModCenter` holds for the group $J_\alpha = E^\times U^m_{\mathfrak{A}}$ of `Langlands/Local/CuspidalTypes.lean` and $Z = F^\times$. This needs that $J_\alpha / F^\times U$ is finite for each open subgroup $U$, that is, that $E^\times / F^\times U^0_E$ is finite and that $U^m_{\mathfrak{A}}$ is compact. With this and the computation $I_G(\Lambda) = J_\alpha$ of BH §15, the main result gives the irreducibility of `Langlands.LocalGL2.cuspInd`.
* The supercuspidality of $c\text{-}\mathrm{Ind}_J^G \Lambda$ (BH 11.4, second part), which uses that its matrix coefficients have compact support modulo the centre.
* The converse direction and the comparison of two induced representations (BH 11.5): $\mathrm{Hom}_G(c\text{-}\mathrm{Ind}_J^G \Lambda, c\text{-}\mathrm{Ind}_{J'}^G \Lambda')$ is not zero exactly when some $g \in G$ intertwines $\Lambda$ with $\Lambda'$. This needs the Mackey formula for the Hecke algebra of bi-equivariant functions.

## References

* C. J. Bushnell, G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §11.
-/

namespace Langlands

universe w

open SmoothRep

section CIndIrreducible

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (J : Subgroup G) (Λ : J →* ℂˣ)

/-- The group $J$ is compact modulo $Z$ in the following form: for each open subgroup $U$ of $J$, the subgroup $(Z \cap J) U$ has finite index in $J$. For an open subgroup $J$ that is compact modulo $Z$ this holds, because the image of $U$ in $J / Z$ is open. -/
def IsCompactModCenter (Z : Subgroup G) : Prop :=
  ∀ U : Subgroup J, IsOpen (U : Set J) → (Z.subgroupOf J ⊔ U).FiniteIndex

/-- The evaluation $f \mapsto f(x)$ at a point $x \in G$, as a linear form on $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
def cInd.toFunLin (x : G) : (cInd J Λ).V →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (cIndSpace J Λ).subtype

variable {J Λ}

/-- The linear form `cInd.toFunLin` is the evaluation of the function of a vector. -/
theorem cInd.toFunLin_apply (x : G) (f : (cInd J Λ).V) :
    cInd.toFunLin J Λ x f = cInd.toFun f x :=
  rfl

/-- The function of a finite sum of vectors is the sum of the functions. -/
theorem cInd.toFun_sum {ι : Type*} (s : Finset ι) (F : ι → (cInd J Λ).V) (x : G) :
    cInd.toFun (∑ i ∈ s, F i) x = ∑ i ∈ s, cInd.toFun (F i) x :=
  map_sum (cInd.toFunLin J Λ x) F s

/-- The function of $c f$ is $c$ times the function of $f$. -/
theorem cInd.toFun_smul (c : ℂ) (f : (cInd J Λ).V) (x : G) :
    cInd.toFun (c • f) x = c * cInd.toFun f x :=
  rfl

/-- A central element $z \in J$ acts on $c\text{-}\mathrm{Ind}_J^G \Lambda$ by the scalar $\Lambda(z)$. -/
theorem cInd.ρ_center {z : G} (hz : z ∈ Subgroup.center G) (hzJ : z ∈ J)
    (f : (cInd J Λ).V) : (cInd J Λ).ρ z f = (Λ ⟨z, hzJ⟩ : ℂ) • f := by
  refine cInd.ext fun x => ?_
  rw [cInd.toFun_ρ, Subgroup.mem_center_iff.1 hz x]
  exact cInd.toFun_mul_left f ⟨z, hzJ⟩ x

variable (Λ) in
/-- For a vector $f$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$, the subgroup of the $j \in J$ with $\pi(j) f = \Lambda(j) f$. -/
def lambdaStab (f : (cInd J Λ).V) : Subgroup J where
  carrier := {j | (cInd J Λ).ρ j f = (Λ j : ℂ) • f}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, (cInd J Λ).ρ.map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul,
      Λ.map_mul, Units.val_mul, mul_comm]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have h := congrArg ((cInd J Λ).ρ (a⁻¹ : J)) ha
    rw [← Module.End.mul_apply, ← (cInd J Λ).ρ.map_mul, InvMemClass.coe_inv, inv_mul_cancel,
      (cInd J Λ).ρ.map_one, Module.End.one_apply, map_smul] at h
    rw [InvMemClass.coe_inv]
    conv_rhs => rw [h]
    rw [smul_smul, Λ.map_inv, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Λ a).ne_zero, one_smul]

/-- Membership in `lambdaStab`. -/
theorem mem_lambdaStab {f : (cInd J Λ).V} {j : J} :
    j ∈ lambdaStab Λ f ↔ (cInd J Λ).ρ j f = (Λ j : ℂ) • f :=
  Iff.rfl

/-- Let $Z$ be a subgroup of the centre of $G$, assume that $J$ is compact modulo $Z$ and that $\Lambda$ has open kernel. Then for each vector $f \neq 0$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ there is a vector $\varphi \neq 0$ in the span of the translates of $f$ with $\pi(j) \varphi = \Lambda(j) \varphi$ for each $j \in J$. The vector $\varphi$ is the average of $\Lambda(j)^{-1} \pi(j g) f$ over $j \in J / Z U$, where $f(g) \neq 0$ and $U$ is the open subgroup of $J$ of the elements that fix $\pi(g) f$ and lie in the kernel of $\Lambda$. -/
theorem exists_isotypic_of_ne_zero {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hc : IsCompactModCenter J Z) (hΛ : IsOpen (Λ.ker : Set J)) {f : (cInd J Λ).V} (hf : f ≠ 0) :
    ∃ φ ∈ Submodule.span ℂ (Set.range fun g => (cInd J Λ).ρ g f), φ ≠ 0 ∧
      ∀ j : J, (cInd J Λ).ρ j φ = (Λ j : ℂ) • φ := by
  classical
  -- A translate `f₁` of `f` with `f₁(1) ≠ 0`.
  obtain ⟨g, hg⟩ : ∃ g, cInd.toFun f g ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (cInd.ext fun x => h x)
  set f₁ := (cInd J Λ).ρ g f with hf₁
  have hf₁1 : cInd.toFun f₁ 1 ≠ 0 := by
    rw [hf₁, cInd.toFun_ρ, one_mul]
    exact hg
  -- The open subgroup `U` and the subgroup `H = Z U` of finite index.
  let U : Subgroup J := (vecStabilizer (cInd J Λ).ρ f₁).comap J.subtype ⊓ Λ.ker
  have hU : IsOpen (U : Set J) := by
    refine IsOpen.inter ?_ hΛ
    exact ((cInd J Λ).smooth f₁).preimage continuous_subtype_val
  let H : Subgroup J := Z.subgroupOf J ⊔ U
  have : H.FiniteIndex := hc U hU
  let : Fintype (J ⧸ H) := Fintype.ofFinite _
  have hH : H ≤ lambdaStab Λ f₁ := by
    refine sup_le (fun z hz => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_subgroupOf] at hz
      rw [mem_lambdaStab, cInd.ρ_center (hZc hz) z.2]
    · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      rw [Subgroup.mem_comap, mem_vecStabilizer] at hu1
      rw [mem_lambdaStab, MonoidHom.mem_ker.1 hu2, Units.val_one, one_smul]
      exact hu1
  -- The terms of the average, as a function on `J ⧸ H`.
  let T : J → (cInd J Λ).V := fun j => ((Λ j)⁻¹ : ℂ) • (cInd J Λ).ρ j f₁
  have hT : ∀ a b : J, a⁻¹ * b ∈ H → T a = T b := by
    intro a b hab
    have hb : b = a * (a⁻¹ * b) := by group
    have h := hH hab
    rw [mem_lambdaStab] at h
    simp only [T]
    have ha : (Λ a : ℂ) ≠ 0 := (Λ a).ne_zero
    have hc : (Λ (a⁻¹ * b) : ℂ) ≠ 0 := (Λ _).ne_zero
    rw [hb, Subgroup.coe_mul, (cInd J Λ).ρ.map_mul, Module.End.mul_apply, h, map_smul, smul_smul,
      Λ.map_mul, Units.val_mul]
    congr 1
    field_simp
  let Φ : J ⧸ H → (cInd J Λ).V :=
    Quotient.lift T fun a b hab => hT a b (QuotientGroup.leftRel_apply.1 hab)
  have hΦ : ∀ j : J, Φ (j : J ⧸ H) = T j := fun _ => rfl
  refine ⟨∑ q, Φ q, Submodule.sum_mem _ fun q _ => ?_, ?_, fun j => ?_⟩
  · induction q using QuotientGroup.induction_on with
    | H j =>
      rw [hΦ]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j * g, ?_⟩)
      simp only [hf₁, map_mul, Module.End.mul_apply]
  · intro h0
    have h1 := congrArg (cInd.toFunLin J Λ 1) h0
    rw [map_sum, map_zero] at h1
    have h2 : ∀ q, cInd.toFunLin J Λ 1 (Φ q) = cInd.toFun f₁ 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H j =>
        rw [hΦ, map_smul, cInd.toFunLin_apply, cInd.toFun_ρ, one_mul,
          ← mul_one (j : G), cInd.toFun_mul_left, smul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (Λ j).ne_zero, one_mul]
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have hcard : (Fintype.card (J ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact mul_ne_zero hcard hf₁1 h1
  · have h3 : ∀ q, (cInd J Λ).ρ j (Φ q) = (Λ j : ℂ) • Φ (j • q) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a =>
        rw [hΦ, MulAction.Quotient.smul_mk, hΦ]
        have hj : (Λ j : ℂ) ≠ 0 := (Λ j).ne_zero
        have ha : (Λ a : ℂ) ≠ 0 := (Λ a).ne_zero
        simp only [T, map_smul, smul_eq_mul, Subgroup.coe_mul, (cInd J Λ).ρ.map_mul, Λ.map_mul,
          Units.val_mul, Module.End.mul_apply, smul_smul]
        congr 1
        field_simp
    rw [map_sum, Finset.smul_sum]
    simp only [h3]
    exact Fintype.sum_equiv (MulAction.toPerm j) _ _ fun _ => rfl

/-- Under the hypotheses of `exists_isotypic_of_ne_zero`, each nonzero stable subspace $W$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ contains a nonzero vector on which $J$ acts by $\Lambda$. -/
theorem exists_isotypic_mem {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hc : IsCompactModCenter J Z) (hΛ : IsOpen (Λ.ker : Set J))
    {W : Submodule ℂ (cInd J Λ).V} (hW : IsStableSubspace (cInd J Λ).ρ W) (hW0 : W ≠ ⊥) :
    ∃ φ ∈ W, φ ≠ 0 ∧ ∀ j : J, (cInd J Λ).ρ j φ = (Λ j : ℂ) • φ := by
  obtain ⟨f, hfW, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨φ, hφ, hφ0, hφJ⟩ := exists_isotypic_of_ne_zero hZc hc hΛ hf
  refine ⟨φ, Submodule.span_le.2 ?_ hφ, hφ0, hφJ⟩
  rintro _ ⟨g, rfl⟩
  exact hW g hfW

variable (J Λ) in
/-- Let $J$ be open and $\Lambda$ a character with open kernel. Each vector $f$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$ is a finite sum $\sum_{s \in T} f(s) \pi(s^{-1}) \, \mathtt{cIndBasic}$, where the elements of $T$ lie in distinct cosets $J s$. The vector $\pi(s^{-1}) \, \mathtt{cIndBasic}$ is supported on $J s$ and has the value $\Lambda(j)$ at $j s$. -/
theorem eq_sum_translate_cIndBasic (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))
    (f : (cInd J Λ).V) : ∃ T : Finset G,
      f = ∑ s ∈ T, cInd.toFun f s • (cInd J Λ).ρ s⁻¹ (cIndBasic J Λ hJ hΛ) := by
  classical
  obtain ⟨S, hS⟩ := (show cIndSpace J Λ from f).2.2.2
  let r : G → Quotient (QuotientGroup.rightRel J) := Quotient.mk _
  refine ⟨S.image fun s => (r s).out, cInd.ext fun x => ?_⟩
  simp only [cInd.toFun_sum, cInd.toFun_smul, cInd.toFun_ρ, cInd.toFun_cIndBasic]
  -- Two elements of the image lie in the same coset only if they are equal.
  have hT : ∀ s ∈ S.image (fun s => (r s).out), ∀ t ∈ S.image (fun s => (r s).out),
      x * s⁻¹ ∈ J → x * t⁻¹ ∈ J → s = t := by
    intro s hs t ht hxs hxt
    obtain ⟨s₀, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.1 ht
    have e : r (r s₀).out = r (r t₀).out := by
      refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
      have := J.mul_mem (J.inv_mem hxt) hxs
      simpa [mul_assoc] using this
    simp only [r, Quotient.out_eq] at e
    exact congrArg Quotient.out e
  by_cases hx : ∃ s ∈ S.image (fun s => (r s).out), x * s⁻¹ ∈ J
  · obtain ⟨s, hs, hxs⟩ := hx
    rw [Finset.sum_eq_single_of_mem s hs fun t ht hts => ?_]
    · rw [cIndBasicFun_of_mem J Λ hxs, mul_comm, ← cInd.toFun_mul_left]
      simp
    · rw [cIndBasicFun_of_not_mem J Λ fun hxt => hts (hT t ht s hs hxt hxs), mul_zero]
  · push Not at hx
    rw [Finset.sum_eq_zero fun t ht => by rw [cIndBasicFun_of_not_mem J Λ (hx t ht), mul_zero]]
    by_contra h0
    obtain ⟨s₀, hs₀, hxs₀⟩ := hS x h0
    refine hx (r s₀).out (Finset.mem_image_of_mem _ hs₀) ?_
    have e : r (r s₀).out = r s₀ := Quotient.out_eq _
    have h := QuotientGroup.rightRel_apply.1 (Quotient.exact e)
    have := J.mul_mem hxs₀ h
    simpa [mul_assoc] using this

variable (J Λ) in
/-- Let $J$ be open and $\Lambda$ a character with open kernel. The translates $\pi(g) \, \mathtt{cIndBasic}$ span $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
theorem span_translate_cIndBasic (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    Submodule.span ℂ (Set.range fun g => (cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ)) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨T, hT⟩ := eq_sum_translate_cIndBasic J Λ hJ hΛ f
  rw [hT]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s⁻¹, rfl⟩)

variable (J Λ) in
/-- The irreducibility criterion (BH 11.4). Let $J$ be an open subgroup of $G$ and $\Lambda$ a character of $J$ with open kernel. Let $Z$ be a subgroup of the centre of $G$, and assume that $J$ is compact modulo $Z$ in the form `IsCompactModCenter`. If each $g \in G$ that intertwines $\Lambda$ lies in $J$, then $c\text{-}\mathrm{Ind}_J^G \Lambda$ is irreducible. -/
theorem isIrreducible_cInd (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))
    {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G) (hc : IsCompactModCenter J Z)
    (hI : ∀ g, Intertwines J Λ g → g ∈ J) : (cInd J Λ).IsIrreducible := by
  refine ⟨nontrivial_cInd J Λ hJ hΛ, fun W hW => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  refine Or.inr ?_
  obtain ⟨φ, hφW, hφ0, hφJ⟩ := exists_isotypic_mem hZc hc hΛ hW hW0
  have hφ := eq_smul_cIndBasic_of_isotypic J Λ hJ hΛ hI φ hφJ
  set c := cInd.toFun φ 1 with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hφ
    exact hφ0 hφ
  have hb : cIndBasic J Λ hJ hΛ ∈ W := by
    have := W.smul_mem c⁻¹ hφW
    rwa [hφ, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  rw [eq_top_iff, ← span_translate_cIndBasic J Λ hJ hΛ, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact hW g hb

end CIndIrreducible

end Langlands
