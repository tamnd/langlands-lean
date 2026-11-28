/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.CIndSupercuspidal
import Langlands.Smooth.CuspidalCoefficients
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Compact induction from a type is admissible

Let $K$ be a nonarchimedean local field, $G = GL_2(K)$, $K_0 = GL_2(\mathcal{O}_K)$ and $N$ the upper unipotent subgroup with elements $n(y)$. Let $J$ be an open subgroup of $G$ that is compact modulo the centre $Z$, and $\Lambda$ a character of $J$ with open kernel. Assume that each element of $G$ that intertwines $\Lambda$ lies in $J$. This file proves that $\pi = c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible, without the named input `Langlands.LocalGL2.CompactCoeffAdmissible`. Then `Langlands.LocalGL2.CIndSupercuspidal` follows with no input.

## Main definitions

* `Langlands.charTerm`: the function $h \mapsto \theta(h) f(h^{-1})$ on a subgroup $H$, for a character $\theta$ of $H$ and a vector $f$ of $\pi$.
* `Langlands.charForm`: the linear form $f \mapsto \sum_{h \in H / (J \cap H)} \theta(h) f(h^{-1})$ on $\pi$.
* `Langlands.charFormHom`: the same form as an $H$-map from $\pi$ to the character $\theta$.
* `Langlands.LocalGL2.conjBorel`: the conjugate $g B g^{-1}$ of the Borel subgroup.
* `Langlands.LocalGL2.conjDiag`: the map $h \mapsto$ the diagonal of $g^{-1} h g$ on $g B g^{-1}$.

## Main results

* `Langlands.exists_monoidHom_extend`: a character of a subgroup of a commutative group extends to the whole group, because $\mathbb{C}^\times$ is divisible.
* `Langlands.charForm_ρ`, `Langlands.charForm_cIndBasic`: the form `charForm` is $H$-equivariant for $\theta$, and its value at $f_0$ is $1$.
* `Langlands.isAdmissible_cInd_of_isAdmissible_ind`: if $\theta$ agrees with $\Lambda$ on $J \cap H$ and $\mathrm{Ind}_H^G \theta$ is admissible, then $\pi$ is admissible.
* `Langlands.trivialOnConj_of_mem_fixedVectors`: if $f \in V^U$ and $f(x) \neq 0$, then $\Lambda$ is trivial on $J \cap x U x^{-1}$.
* `Langlands.LocalGL2.val_conjDiag`, `Langlands.LocalGL2.eq_conj_unip_of_conjDiag_eq_one`: the map `conjDiag` gives the diagonal of $g^{-1} h g$, and its kernel is $g N g^{-1}$.
* `Langlands.LocalGL2.exists_open_conj_le`: an open subgroup $K'$ contains $\rho^{-1} K'' \rho$ for each $\rho \in K_0$, for an open subgroup $K''$.
* `Langlands.LocalGL2.exists_le_valuation_of_trivialOnConj`: if $\Lambda$ is not trivial on $J \cap g N g^{-1}$ for each $g \in K_0$, then `TrivialOnConj J Λ K' (σ * diag(a, d) * ρ)` with $\sigma, \rho \in K_0$ gives $\varepsilon \le v(d/a)$ for a fixed $\varepsilon \neq 0$.
* `Langlands.LocalGL2.exists_isCompact_of_trivialOnConj`: in the same case, the elements $h$ with `TrivialOnConj J Λ K' h` lie in $C Z$ for a compact set $C$.
* `Langlands.LocalGL2.finiteDimensional_fixedVectors_of_forall`: in the same case, $V^U$ has finite dimension for each open subgroup $U$.
* `Langlands.LocalGL2.isAdmissible_cInd_of_conj`: if $\Lambda$ is trivial on $J \cap g_0 N g_0^{-1}$ for some $g_0$, then $\pi$ is admissible.
* `Langlands.LocalGL2.isAdmissible_cInd_of_intertwining`: $c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible.
* `Langlands.LocalGL2.cIndSupercuspidal`: `Langlands.LocalGL2.CIndSupercuspidal K` holds.

## Proof

There are two cases.

First, assume that for each $g \in K_0$ there is $y$ with $g n(y) g^{-1} \in J$ and $\Lambda(g n(y) g^{-1}) \neq 1$. Let $U$ be open. If $f \in V^U$ and $f(h) \neq 0$, then $\Lambda$ is trivial on $J \cap h U h^{-1}$. Write $h = \sigma \, \mathrm{diag}(a, d) \, \rho$ with $\sigma, \rho \in K_0$ (Cartan). For $x = \sigma n(y) \sigma^{-1}$ we have $h^{-1} x h = \rho^{-1} n(d y / a) \rho$. This element is not in $U$, so $v(d y / a)$ is not small. The element $y$ depends only on a coset of $\sigma$ modulo an open subgroup of $\ker \Lambda$, so there are finitely many $y$, and $v(d/a) \ge \varepsilon$. The Weyl element gives $v(a/d) \ge \varepsilon$. Thus $h \in C Z$ for a compact set $C$, and $Z \subseteq J$. Cover $C$ by finitely many cosets $t U$. Then $f$ is determined by the finitely many values $f(t)$.

Second, assume that $\Lambda$ is trivial on $J \cap g_0 N g_0^{-1}$. Let $H = g_0 B g_0^{-1}$. On $J \cap H$, the character $\Lambda$ factors through the diagonal map $H \to K^\times \times K^\times$. Extend it to a character of $K^\times \times K^\times$, and let $\theta$ be the composite on $H$. The form $f \mapsto \sum_{h \in H / (J \cap H)} \theta(h) f(h^{-1})$ is $H$-equivariant and is $1$ at $f_0$. Frobenius reciprocity gives a nonzero map $\pi \to \mathrm{Ind}_H^G \theta$. It is injective, because $\pi$ is irreducible (`Langlands.isIrreducible_cInd`). The induced representation is admissible, because $G = H g_0 K_0$ (Iwasawa).

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§10 and 11.
-/

namespace Langlands

universe w

open SmoothRep Representation

section Extension

/-- Each power map $z \mapsto z^n$ of $\mathbb{C}^\times$ with $n \neq 0$ is surjective: $z = \exp(\log x / n)$ is a root of $x$. -/
theorem zpow_surjective_units_complex {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective fun z : ℂˣ => z ^ n := by
  intro x
  refine ⟨Units.mk0 (Complex.exp (Complex.log x / n)) (Complex.exp_ne_zero _), Units.ext ?_⟩
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
    mul_div_cancel₀ _ (Int.cast_ne_zero.2 hn), Complex.exp_log x.ne_zero]

/-- **Extension of characters.** Let $B$ be a subgroup of a commutative group $A$. Each character of $B$ extends to a character of $A$, because $\mathbb{C}^\times$ is divisible and thus an injective abelian group. -/
theorem exists_monoidHom_extend {A : Type*} [CommGroup A] (B : Subgroup A) (χ : B →* ℂˣ) :
    ∃ χ' : A →* ℂˣ, ∀ b : B, χ' b = χ b := by
  let : DivisibleBy (Additive ℂˣ) ℤ := divisibleByOfSMulRightSurj (A := Additive ℂˣ) (α := ℤ)
    fun {n} hn x => by
      obtain ⟨y, hy⟩ := zpow_surjective_units_complex hn (Additive.toMul x)
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive B.subtype) (fun a b hab => Subtype.ext hab) (MonoidHom.toAdditive χ)
  exact ⟨MonoidHom.toAdditive.symm h, fun b => DFunLike.congr_fun hh (Additive.ofMul b)⟩

end Extension

section Frobenius

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {J : Subgroup G} {Λ : J →* ℂˣ} {H : Subgroup G} {θ : H →* ℂˣ}

variable (J Λ θ) in
/-- The function $h \mapsto \theta(h) f(h^{-1})$ on $H$, for a vector $f$ of $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
noncomputable def charTerm (f : (cInd J Λ).V) (h : H) : ℂ :=
  (θ h : ℂ) * cInd.toFun f (h : G)⁻¹

/-- If $\theta$ agrees with $\Lambda$ on $J \cap H$, then `charTerm` is invariant on the right under $J \cap H$. -/
theorem charTerm_mul_right (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩)
    (f : (cInd J Λ).V) (h l : H) (hl : (l : G) ∈ J) :
    charTerm J Λ θ f (h * l) = charTerm J Λ θ f h := by
  have e : ((h * l : H) : G)⁻¹ = (((⟨l, hl⟩ : J)⁻¹ : J) : G) * (h : G)⁻¹ := by
    rw [Subgroup.coe_mul, mul_inv_rev]
    rfl
  have hne : (Λ ⟨l, hl⟩ : ℂ) ≠ 0 := Units.ne_zero _
  unfold charTerm
  rw [e, cInd.toFun_mul_left, map_mul, hθ l hl, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

variable (J Λ θ) in
/-- The function `charTerm` at a representative of a coset in $H / (J \cap H)$. -/
noncomputable def charTermQ (f : (cInd J Λ).V) (q : H ⧸ J.subgroupOf H) : ℂ :=
  charTerm J Λ θ f q.out

/-- The value of `charTermQ` at the coset of $h$ is the value of `charTerm` at $h$. -/
theorem charTermQ_mk (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩)
    (f : (cInd J Λ).V) (h : H) :
    charTermQ J Λ θ f (h : H ⧸ J.subgroupOf H) = charTerm J Λ θ f h := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) h
  unfold charTermQ
  rw [hl]
  exact charTerm_mul_right hθ f h l (Subgroup.mem_subgroupOf.1 l.2)

/-- The function `charTermQ` has finite support. For each $s$ in the finite set of `cIndSpace`, at most one coset $q$ has $q^{-1} s^{-1} \in J$. -/
theorem charTermQ_finite (f : (cInd J Λ).V) :
    (Function.support (charTermQ J Λ θ f)).Finite := by
  obtain ⟨S, hS⟩ := (show cIndSpace J Λ from f).2.2.2
  have hsub : Function.support (charTermQ J Λ θ f) ⊆
      ⋃ s ∈ (S : Set G), {q : H ⧸ J.subgroupOf H | ((q.out : H) : G)⁻¹ * s⁻¹ ∈ J} := by
    intro q hq
    have h1 : cInd.toFun f ((q.out : H) : G)⁻¹ ≠ 0 := by
      rw [Function.mem_support] at hq
      unfold charTermQ charTerm at hq
      exact right_ne_zero_of_mul hq
    obtain ⟨s, hs, hsJ⟩ := hS _ h1
    exact Set.mem_biUnion hs hsJ
  refine (S.finite_toSet.biUnion fun s _ => Set.Subsingleton.finite ?_).subset hsub
  intro q hq q' hq'
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have := J.mul_mem hq (J.inv_mem hq')
  convert this using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
  group

variable (J Λ θ) in
/-- The linear form $f \mapsto \sum_{h \in H / (J \cap H)} \theta(h) f(h^{-1})$ on $c\text{-}\mathrm{Ind}_J^G \Lambda$. The sum is finite by `Langlands.charTermQ_finite`. -/
noncomputable def charForm : (cInd J Λ).V →ₗ[ℂ] ℂ where
  toFun f := ∑ᶠ q, charTermQ J Λ θ f q
  map_add' f f' := by
    rw [← finsum_add_distrib (charTermQ_finite f) (charTermQ_finite f')]
    refine finsum_congr fun q => ?_
    unfold charTermQ charTerm
    rw [← mul_add]
    rfl
  map_smul' c f := by
    rw [RingHom.id_apply, smul_eq_mul, mul_finsum]
    refine finsum_congr fun q => ?_
    unfold charTermQ charTerm
    rw [cInd.toFun_smul]
    ring

/-- The form `charForm` is $H$-equivariant for $\theta$: $\ell(\pi(h_0) f) = \theta(h_0) \ell(f)$. -/
theorem charForm_ρ (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩) (h₀ : H)
    (f : (cInd J Λ).V) :
    charForm J Λ θ ((cInd J Λ).ρ h₀ f) = θ h₀ * charForm J Λ θ f := by
  have key : ∀ q, charTermQ J Λ θ ((cInd J Λ).ρ h₀ f) q =
      θ h₀ * charTermQ J Λ θ f (h₀⁻¹ • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H h =>
      have e : (h₀⁻¹ • (h : H ⧸ J.subgroupOf H)) = ((h₀⁻¹ * h : H) : H ⧸ J.subgroupOf H) := rfl
      rw [e, charTermQ_mk hθ, charTermQ_mk hθ]
      unfold charTerm
      have hne : (θ h₀ : ℂ) ≠ 0 := Units.ne_zero _
      rw [cInd.toFun_ρ, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
      field_simp
  change ∑ᶠ q, charTermQ J Λ θ ((cInd J Λ).ρ h₀ f) q = θ h₀ * ∑ᶠ q, charTermQ J Λ θ f q
  rw [finsum_congr key, mul_finsum]
  exact finsum_comp_equiv (MulAction.toPerm h₀⁻¹) (f := fun q => θ h₀ * charTermQ J Λ θ f q)

/-- The value of `charForm` at the vector $f_0$ is $1$. Only the trivial coset contributes. -/
theorem charForm_cIndBasic (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩)
    (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    charForm J Λ θ (cIndBasic J Λ hJ hΛ) = 1 := by
  change ∑ᶠ q, charTermQ J Λ θ (cIndBasic J Λ hJ hΛ) q = 1
  rw [finsum_eq_single _ ((1 : H) : H ⧸ J.subgroupOf H), charTermQ_mk hθ]
  · unfold charTerm
    rw [cInd.toFun_cIndBasic, OneMemClass.coe_one, inv_one, cIndBasicFun_of_mem J Λ J.one_mem]
    have e : (⟨1, J.one_mem⟩ : J) = 1 := rfl
    rw [e, map_one, map_one, Units.val_one, one_mul]
  · intro q hq
    unfold charTermQ charTerm
    rw [cInd.toFun_cIndBasic, cIndBasicFun_of_not_mem J Λ, mul_zero]
    intro hmem
    apply hq
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmem

variable (J Λ) in
/-- The form `charForm` as an $H$-map from $c\text{-}\mathrm{Ind}_J^G \Lambda$ to the character $\theta$, when $\theta$ agrees with $\Lambda$ on $J \cap H$. -/
noncomputable def charFormHom (hθo : IsOpen (θ.ker : Set H))
    (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩) :
    IntertwiningMap ((cInd J Λ).ρ.comp H.subtype) (charRep θ hθo).ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm.toLinearMap ∘ₗ charForm J Λ θ) fun h f => by
      refine ULift.ext ?_
      change charForm J Λ θ ((cInd J Λ).ρ h f) = (θ h : ℂ) * charForm J Λ θ f
      exact charForm_ρ hθ h f

/-- **Admissibility from an embedding into an induced representation.** Let $J$ be open, compact modulo a central subgroup $Z$, and $\Lambda$ a character of $J$ with open kernel whose intertwining is $J$. Let $\theta$ be a character with open kernel of a subgroup $H$ that agrees with $\Lambda$ on $J \cap H$. If $\mathrm{Ind}_H^G \theta$ is admissible, then $c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible. The map from Frobenius reciprocity is nonzero at $f_0$, so it is injective because $c\text{-}\mathrm{Ind}_J^G \Lambda$ is irreducible. -/
theorem isAdmissible_cInd_of_isAdmissible_ind (hJ : IsOpen (J : Set G))
    (hΛ : IsOpen (Λ.ker : Set J)) {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hc : IsCompactModCenter J Z) (hI : ∀ g, Intertwines J Λ g → g ∈ J)
    (hθo : IsOpen (θ.ker : Set H)) (hθ : ∀ (h : H) (hh : (h : G) ∈ J), θ h = Λ ⟨h, hh⟩)
    (hadm : (ind H (charRep θ hθo)).IsAdmissible) : (cInd J Λ).IsAdmissible := by
  set Φ := ((cInd J Λ).frobenius H (charRep θ hθo)).symm (charFormHom J Λ hθo hθ) with hΦ
  have hΦ1 : ind.toFun (Φ (cIndBasic J Λ hJ hΛ)) 1 = ULift.up 1 := by
    rw [hΦ, frobenius_symm_apply, map_one, Module.End.one_apply]
    change ULift.up (charForm J Λ θ (cIndBasic J Λ hJ hΛ)) = _
    rw [charForm_cIndBasic hθ]
  have hW : IsStableSubspace (cInd J Λ).ρ (LinearMap.ker Φ.toLinearMap) := fun g v hv => by
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    rw [LinearMap.mem_ker] at hv
    change Φ ((cInd J Λ).ρ g v) = 0
    change Φ v = 0 at hv
    rw [IntertwiningMap.isIntertwining _ _ Φ, hv, map_zero]
  have hinj : Function.Injective Φ := by
    rcases (isIrreducible_cInd J Λ hJ hΛ hZc hc hI).2 _ hW with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      have h0 : Φ (cIndBasic J Λ hJ hΛ) = 0 := by
        have : cIndBasic J Λ hJ hΛ ∈ LinearMap.ker Φ.toLinearMap := by
          rw [h]
          exact Submodule.mem_top
        exact this
      rw [h0] at hΦ1
      exact one_ne_zero (congrArg ULift.down hΦ1).symm
  intro U hU
  have := hadm U hU
  let r : fixedVectors (cInd J Λ).ρ U →ₗ[ℂ] fixedVectors (ind H (charRep θ hθo)).ρ U :=
    Φ.toLinearMap.restrict fun v hv g hg => by
      change (ind H (charRep θ hθo)).ρ g (Φ v) = Φ v
      rw [← IntertwiningMap.isIntertwining _ _ Φ, hv g hg]
  exact FiniteDimensional.of_injective r fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))

end Frobenius

section Fixed

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {J : Subgroup G} {Λ : J →* ℂˣ}

/-- Let $f$ be a vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ fixed by $U$. If $f(x) \neq 0$, then $\Lambda$ is trivial on $J \cap x U x^{-1}$: for $j \in J$ with $x^{-1} j x \in U$ we have $\Lambda(j) f(x) = f(j x) = f(x)$. -/
theorem trivialOnConj_of_mem_fixedVectors {U : Subgroup G} {f : (cInd J Λ).V}
    (hf : f ∈ fixedVectors (cInd J Λ).ρ U) {x : G} (hx : cInd.toFun f x ≠ 0) :
    TrivialOnConj J Λ U x := by
  intro j hj
  have h1 := cInd.toFun_mul_left f j x
  have h2 : cInd.toFun f (j * x) = cInd.toFun f x := by
    have := congrArg (fun v => cInd.toFun v x) (hf _ hj)
    simp only [cInd.toFun_ρ] at this
    calc cInd.toFun f (j * x) = cInd.toFun f (x * (x⁻¹ * j * x)) := by congr 1; group
      _ = _ := this
  rw [h2] at h1
  exact Units.ext (mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm))

end Fixed

end Langlands

namespace Langlands.LocalGL2

universe u

open SmoothRep Representation Matrix ValuativeRel GL2

section Admissible

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {J : Subgroup (GL (Fin 2) K)} {Λ : J →* ℂˣ}

variable (K) in
/-- The conjugate $g B g^{-1}$ of the Borel subgroup $B$ of upper triangular matrices. -/
def conjBorel (g : GL (Fin 2) K) : Subgroup (GL (Fin 2) K) :=
  (GL2.borel K).comap (MulAut.conj g⁻¹).toMonoidHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element $h$ is in $g B g^{-1}$ exactly when $g^{-1} h g \in B$. -/
theorem mem_conjBorel {g h : GL (Fin 2) K} : h ∈ conjBorel K g ↔ g⁻¹ * h * g ∈ GL2.borel K := by
  rw [conjBorel, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

variable (K) in
/-- The homomorphism from $g B g^{-1}$ to $K^\times \times K^\times$ that sends $h$ to the diagonal of $g^{-1} h g$. -/
noncomputable def conjDiag (g : GL (Fin 2) K) : conjBorel K g →* Kˣ × Kˣ :=
  (diagFst.prod diagSnd).comp ((MulAut.conj g⁻¹).toMonoidHom.subgroupComap (GL2.borel K))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The two entries of `conjDiag K g h` are the diagonal entries of $g^{-1} h g$. -/
theorem val_conjDiag {g : GL (Fin 2) K} (h : conjBorel K g) :
    ((conjDiag K g h).1 : K) = (g⁻¹ * h * g).1 0 0 ∧
      ((conjDiag K g h).2 : K) = (g⁻¹ * h * g).1 1 1 := by
  have e : (MulAut.conj g⁻¹) (h : GL (Fin 2) K) = g⁻¹ * h * g := by
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨?_, ?_⟩
  · change ((diagFst _ : Kˣ) : K) = _
    rw [val_diagFst]
    exact congrArg (fun X : GL (Fin 2) K => X.1 0 0) e
  · change ((diagSnd _ : Kˣ) : K) = _
    rw [val_diagSnd]
    exact congrArg (fun X : GL (Fin 2) K => X.1 1 1) e

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The kernel of `conjDiag` is $g N g^{-1}$: if the diagonal of $g^{-1} h g$ is $(1, 1)$, then $h = g n(y) g^{-1}$. -/
theorem eq_conj_unip_of_conjDiag_eq_one {g : GL (Fin 2) K} {h : conjBorel K g}
    (hh : conjDiag K g h = 1) :
    (h : GL (Fin 2) K) = g * unip ((g⁻¹ * h * g).1 0 1) * g⁻¹ := by
  have h1 : (g⁻¹ * h * g).1 0 0 = 1 := by
    have := congrArg (fun p : Kˣ × Kˣ => (p.1 : K)) hh
    rw [(val_conjDiag h).1] at this
    simpa using this
  have h2 : (g⁻¹ * h * g).1 1 1 = 1 := by
    have := congrArg (fun p : Kˣ × Kˣ => (p.2 : K)) hh
    rw [(val_conjDiag h).2] at this
    simpa using this
  have hmem : g⁻¹ * h * g ∈ unipotent K := ⟨mem_conjBorel.1 h.2, h1, h2⟩
  have e := eq_unip hmem
  calc (h : GL (Fin 2) K) = g * (g⁻¹ * h * g) * g⁻¹ := by group
    _ = _ := by conv_lhs => rw [e]

/-- **The second case.** Assume that $\Lambda$ is trivial on $J \cap g_0 N g_0^{-1}$. Then $c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible. The character $\Lambda$ on $J \cap g_0 B g_0^{-1}$ factors through the diagonal, and an extension $\theta$ to $g_0 B g_0^{-1}$ gives an embedding into the admissible representation $\mathrm{Ind}_{g_0 B g_0^{-1}}^G \theta$. -/
theorem isAdmissible_cInd_of_conj (hJ : IsOpen (J : Set (GL (Fin 2) K)))
    (hΛ : IsOpen (Λ.ker : Set J)) (hc : IsCompactModCenter J (scalarGL K 2).range)
    (hI : ∀ g, Intertwines J Λ g → g ∈ J) {g₀ : GL (Fin 2) K}
    (hg₀ : ∀ y (hy : g₀ * unip y * g₀⁻¹ ∈ J), Λ ⟨_, hy⟩ = 1) : (cInd J Λ).IsAdmissible := by
  classical
  let H := conjBorel K g₀
  let p := conjDiag K g₀
  let L := J.subgroupOf H
  let ι : L →* J :=
    { toFun := fun l => ⟨l.1.1, l.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : L →* Kˣ × Kˣ := p.comp L.subtype
  have hle : φ.ker ≤ (Λ.comp ι).ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have e := eq_conj_unip_of_conjDiag_eq_one (h := l.1) hl
    have hmem : g₀ * unip ((g₀⁻¹ * (l.1 : GL (Fin 2) K) * g₀).1 0 1) * g₀⁻¹ ∈ J := by
      rw [← e]
      exact l.2
    have : ι l = ⟨_, hmem⟩ := Subtype.ext e
    rw [MonoidHom.comp_apply, this]
    exact hg₀ _ _
  let χ₀ : φ.range →* ℂˣ := (QuotientGroup.lift φ.ker (Λ.comp ι) hle).comp
    (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hχ₀ : ∀ l : L, χ₀ ⟨φ l, l, rfl⟩ = Λ (ι l) := by
    intro l
    have : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ l, l, rfl⟩ = (l : L ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]
  obtain ⟨χ, hχ⟩ := exists_monoidHom_extend φ.range χ₀
  let θ : H →* ℂˣ := χ.comp p
  have hθ : ∀ (h : H) (hh : (h : GL (Fin 2) K) ∈ J), θ h = Λ ⟨h, hh⟩ := by
    intro h hh
    have := hχ ⟨φ ⟨h, hh⟩, ⟨h, hh⟩, rfl⟩
    rw [hχ₀] at this
    exact this
  have hθo : IsOpen (θ.ker : Set H) := by
    have hN : IsOpen ((Λ.ker.map J.subtype : Subgroup (GL (Fin 2) K)) : Set (GL (Fin 2) K)) := by
      rw [Subgroup.coe_map]
      exact hJ.isOpenMap_subtype_val _ hΛ
    refine Subgroup.isOpen_mono (H₁ := (Λ.ker.map J.subtype).subgroupOf H) ?_
      (hN.preimage continuous_subtype_val)
    intro h hh
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hh
    obtain ⟨k, hk, hkh⟩ := hh
    have hhJ : (h : GL (Fin 2) K) ∈ J := by
      rw [← hkh]
      exact k.2
    rw [MonoidHom.mem_ker, hθ h hhJ]
    have : (⟨h, hhJ⟩ : J) = k := Subtype.ext hkh.symm
    rw [this]
    exact hk
  have : FiniteDimensional ℂ (charRep θ hθo).V := inferInstanceAs (FiniteDimensional ℂ (ULift.{u} ℂ))
  refine Langlands.isAdmissible_cInd_of_isAdmissible_ind hJ hΛ range_scalarGL_le_center hc hI
    hθo hθ ?_
  refine ind_isAdmissible (C := (fun k => g₀ * k) '' (maxCompact K : Set (GL (Fin 2) K)))
    (isCompact_maxCompact.image (continuous_const.mul continuous_id)) fun g => ?_
  obtain ⟨b, hb, k, hk, e⟩ := iwasawa (g₀⁻¹ * g)
  refine ⟨⟨g₀ * b * g₀⁻¹, mem_conjBorel.2 (by simpa [mul_assoc] using hb)⟩, g₀ * k, ⟨k, hk, rfl⟩,
    ?_⟩
  change g = g₀ * b * g₀⁻¹ * (g₀ * k)
  calc g = g₀ * (g₀⁻¹ * g) := by group
    _ = _ := by rw [e]; group

omit [IsNonarchimedeanLocalField K] in
/-- Let $K'$ be an open subgroup. There is an open subgroup $K''$ with $\rho^{-1} x \rho \in K'$ for each $\rho \in K_0$ and $x \in K''$. It is the intersection of the conjugates of $K' \cap K_0$ by finitely many coset representatives of $K_0 / (K' \cap K_0)$. -/
theorem exists_open_conj_le [IsNonarchimedeanLocalField K] {K' : Subgroup (GL (Fin 2) K)}
    (hK' : IsOpen (K' : Set (GL (Fin 2) K))) :
    ∃ K'' : Subgroup (GL (Fin 2) K), IsOpen (K'' : Set (GL (Fin 2) K)) ∧
      ∀ ρ ∈ maxCompact K, ∀ x ∈ K'', ρ⁻¹ * x * ρ ∈ K' := by
  classical
  have : CompactSpace (maxCompact K) := isCompact_iff_compactSpace.mp isCompact_maxCompact
  have hK₁ : IsOpen ((K' ⊓ maxCompact K : Subgroup (GL (Fin 2) K)) : Set (GL (Fin 2) K)) := by
    rw [Subgroup.coe_inf]
    exact hK'.inter isOpen_maxCompact
  let K₁ : Subgroup (maxCompact K) := (K' ⊓ maxCompact K).subgroupOf (maxCompact K)
  have : Finite (maxCompact K ⧸ K₁) :=
    Subgroup.quotient_finite_of_isOpen K₁ (hK₁.preimage continuous_subtype_val)
  refine ⟨⨅ q : maxCompact K ⧸ K₁, (K' ⊓ maxCompact K).comap
    (MulAut.conj ((q.out : maxCompact K) : GL (Fin 2) K)⁻¹).toMonoidHom, ?_,
    fun ρ hρ x hx => ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => isOpen_comap_conj hK₁ _
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ (⟨ρ, hρ⟩ : maxCompact K)
    have h1 := (Subgroup.mem_iInf.1 hx) ((⟨ρ, hρ⟩ : maxCompact K) : maxCompact K ⧸ K₁)
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hk] at h1
    have hkm : ((k : maxCompact K) : GL (Fin 2) K) ∈ K' ⊓ maxCompact K := k.2
    have e : ρ⁻¹ * x * ρ = ((k : maxCompact K) : GL (Fin 2) K) *
        ((((⟨ρ, hρ⟩ : maxCompact K) * k : maxCompact K) : GL (Fin 2) K)⁻¹ * x *
          (((⟨ρ, hρ⟩ : maxCompact K) * k : maxCompact K) : GL (Fin 2) K)) *
        ((k : maxCompact K) : GL (Fin 2) K)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact (Subgroup.mem_inf.1 ((K' ⊓ maxCompact K).mul_mem ((K' ⊓ maxCompact K).mul_mem hkm h1)
      ((K' ⊓ maxCompact K).inv_mem hkm))).1

/-- **The first case, a bound on the torus.** Assume that for each $g \in K_0$ there is $y$ with $g n(y) g^{-1} \in J$ and $\Lambda(g n(y) g^{-1}) \neq 1$. Let $K'$ be open. Then there is $\varepsilon \neq 0$ such that `TrivialOnConj J Λ K' (σ * diag(a, d) * ρ)` with $\sigma, \rho \in K_0$ gives $\varepsilon \le v(d/a)$. -/
theorem exists_le_valuation_of_trivialOnConj (hJ : IsOpen (J : Set (GL (Fin 2) K)))
    (hΛ : IsOpen (Λ.ker : Set J)) {K' : Subgroup (GL (Fin 2) K)}
    (hK' : IsOpen (K' : Set (GL (Fin 2) K)))
    (h1 : ∀ g ∈ maxCompact K, ∃ y, ∃ hy : g * unip y * g⁻¹ ∈ J, Λ ⟨_, hy⟩ ≠ 1) :
    ∃ ε : ValueGroupWithZero K, ε ≠ 0 ∧ ∀ σ ∈ maxCompact K, ∀ ρ ∈ maxCompact K, ∀ a d : Kˣ,
      TrivialOnConj J Λ K' (σ * ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) * ρ) →
        ε ≤ valuation K ((d : K) / a) := by
  classical
  obtain ⟨K'', hK''o, hK''⟩ := exists_open_conj_le hK'
  have hO : IsOpen (unip ⁻¹' (K'' : Set (GL (Fin 2) K))) :=
    continuous_unip.isOpen_preimage _ hK''o
  have hO0 : (0 : K) ∈ unip ⁻¹' (K'' : Set (GL (Fin 2) K)) := by
    rw [Set.mem_preimage, unip_zero]
    exact K''.one_mem
  obtain ⟨δ, hδ⟩ := IsValuativeTopology.mem_nhds_iff'.1 (hO.mem_nhds hO0)
  have : CompactSpace (maxCompact K) := isCompact_iff_compactSpace.mp isCompact_maxCompact
  have hN₀ : IsOpen ((Λ.ker.map J.subtype : Subgroup (GL (Fin 2) K)) : Set (GL (Fin 2) K)) := by
    rw [Subgroup.coe_map]
    exact hJ.isOpenMap_subtype_val _ hΛ
  let S : Subgroup (maxCompact K) := (Λ.ker.map J.subtype).subgroupOf (maxCompact K)
  have : Finite (maxCompact K ⧸ S) :=
    Subgroup.quotient_finite_of_isOpen S (hN₀.preimage continuous_subtype_val)
  have hy := fun q : maxCompact K ⧸ S =>
    h1 ((q.out : maxCompact K) : GL (Fin 2) K)⁻¹ ((maxCompact K).inv_mem q.out.2)
  choose y hyJ hyΛ using hy
  have hy0 : ∀ q, y q ≠ 0 := by
    intro q h0
    apply hyΛ q
    have : (⟨_, hyJ q⟩ : J) = 1 := Subtype.ext (by simp [h0, unip_zero])
    rw [this, map_one]
  let ε : maxCompact K ⧸ S → ValueGroupWithZero K := fun q =>
    (δ : ValueGroupWithZero K) * (valuation K (y q))⁻¹
  obtain ⟨q₀, hq₀⟩ := Finite.exists_min ε
  refine ⟨ε q₀, mul_ne_zero δ.ne_zero (inv_ne_zero ((map_ne_zero _).2 (hy0 q₀))),
    fun σ hσ ρ hρ a d htriv => ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨σ⁻¹, (maxCompact K).inv_mem hσ⟩ : maxCompact K)
  set q : maxCompact K ⧸ S := ((⟨σ⁻¹, (maxCompact K).inv_mem hσ⟩ : maxCompact K) : maxCompact K ⧸ S)
    with hq
  refine (hq₀ q).trans ?_
  have hsN : ((s : maxCompact K) : GL (Fin 2) K) ∈ Λ.ker.map J.subtype := s.2
  obtain ⟨j₀, hj₀, hj₀s⟩ := Subgroup.mem_map.1 hsN
  have hj₀s' : (j₀ : GL (Fin 2) K) = ((s : maxCompact K) : GL (Fin 2) K) := hj₀s
  have hoσ : ((q.out : maxCompact K) : GL (Fin 2) K) = σ⁻¹ * ((s : maxCompact K) : GL (Fin 2) K) := by
    rw [hs]
    rfl
  let x : J := ⟨_, hyJ q⟩
  let j : J := j₀ * x * j₀⁻¹
  have hj : Λ j ≠ 1 := by
    simp only [j, map_mul, map_inv, MonoidHom.mem_ker.1 hj₀, one_mul, inv_one, mul_one]
    exact hyΛ q
  have hjv : (j : GL (Fin 2) K) = σ * unip (y q) * σ⁻¹ := by
    simp only [j, x, Subgroup.coe_mul, InvMemClass.coe_inv, hj₀s']
    rw [show ((s : maxCompact K) : GL (Fin 2) K) = σ * ((q.out : maxCompact K) : GL (Fin 2) K) by
      rw [hoσ]; group]
    group
  set D : GL (Fin 2) K := ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) with hDdef
  have hD : D * unip ((d : K) * y q / a) = unip (y q) * D := by
    rw [hDdef, diagTorusHom_mul_unip]
    congr 2
    field_simp
  have hconj : (σ * D * ρ)⁻¹ * j * (σ * D * ρ) = ρ⁻¹ * unip ((d : K) * y q / a) * ρ := by
    rw [hjv]
    calc (σ * D * ρ)⁻¹ * (σ * unip (y q) * σ⁻¹) * (σ * D * ρ) =
        ρ⁻¹ * (D⁻¹ * (unip (y q) * D)) * ρ := by group
      _ = _ := by rw [← hD]; group
  have hval : (δ : ValueGroupWithZero K) ≤ valuation K ((d : K) * y q / a) := by
    by_contra hlt
    push Not at hlt
    have hmem : unip ((d : K) * y q / a) ∈ K'' :=
      hδ (show valuation K (_ - 0) < δ by rw [sub_zero]; exact hlt)
    have hK'm := hK'' ρ hρ _ hmem
    rw [← hconj] at hK'm
    exact hj (htriv j hK'm)
  rw [mul_div_right_comm, map_mul] at hval
  exact (mul_inv_le_iff₀ (zero_lt_iff.2 ((map_ne_zero _).2 (hy0 q)))).2 hval

/-- **The first case, compact support modulo the centre.** Under the hypothesis of `exists_le_valuation_of_trivialOnConj`, there is a compact set $C$ such that each $h$ with `TrivialOnConj J Λ K' h` is $c z$ with $c \in C$ and $z$ scalar. The Cartan decomposition and the Weyl element give $\varepsilon \le v(a/d)$ and $\varepsilon \le v(d/a)$. -/
theorem exists_isCompact_of_trivialOnConj (hJ : IsOpen (J : Set (GL (Fin 2) K)))
    (hΛ : IsOpen (Λ.ker : Set J)) {K' : Subgroup (GL (Fin 2) K)}
    (hK' : IsOpen (K' : Set (GL (Fin 2) K)))
    (h1 : ∀ g ∈ maxCompact K, ∃ y, ∃ hy : g * unip y * g⁻¹ ∈ J, Λ ⟨_, hy⟩ ≠ 1) :
    ∃ C : Set (GL (Fin 2) K), IsCompact C ∧
      ∀ g, TrivialOnConj J Λ K' g → ∃ c ∈ C, ∃ z : Kˣ, g = c * scalarGL K 2 z := by
  classical
  obtain ⟨ε₀, hε0, hε⟩ := exists_le_valuation_of_trivialOnConj hJ hΛ hK' h1
  have hKc := isCompact_maxCompact (K := K)
  obtain ⟨e, he⟩ := valuation_surjective ε₀
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hε0 (by simpa using he.symm)
  obtain ⟨n, hn⟩ := exists_valuation_eq_zpow he0
  rw [he] at hn
  obtain ⟨c, hcϖ⟩ := valuation_surjective (uniformizer K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (uniformizer_ne_zero (R := K)) (by simpa using hcϖ.symm)
  set ϖ : Kˣ := Units.mk0 c hc0
  let D : ℤ → GL (Fin 2) K := fun k => ((diagTorusHom (ϖ ^ k, 1) : torus K) : GL (Fin 2) K)
  refine ⟨⋃ k ∈ Finset.Icc (-n) n,
    (fun p : GL (Fin 2) K × GL (Fin 2) K => p.1 * D k * p.2) '' (maxCompact K ×ˢ maxCompact K),
    (Finset.Icc (-n) n).isCompact_biUnion fun k _ => (hKc.prod hKc).image
      ((continuous_fst.mul continuous_const).mul continuous_snd), fun g hg => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, a, d, rfl⟩ := cartan g
  have hw := weyl_mem_maxCompact (K := K)
  have h₂ := hε k₁ hk₁ k₂ hk₂ a d hg
  have hww : ∀ X : GL (Fin 2) K, weyl * (weyl * X) = X := fun X => by
    rw [← mul_assoc, weyl_mul_weyl, one_mul]
  have hg' : TrivialOnConj J Λ K' ((k₁ * weyl) * ((diagTorusHom (d, a) : torus K) :
      GL (Fin 2) K) * (weyl * k₂)) := by
    rw [← weyl_mul_diagTorusHom_mul_weyl a d]
    simp only [mul_assoc, hww]
    simpa only [mul_assoc] using hg
  have h₁ := hε _ ((maxCompact K).mul_mem hk₁ hw) _ ((maxCompact K).mul_mem hw hk₂) d a hg'
  rw [hn] at h₁ h₂
  have had : (a : K) / d ≠ 0 := div_ne_zero a.ne_zero d.ne_zero
  obtain ⟨k, hk⟩ := exists_valuation_eq_zpow had
  rw [hk, uniformizer_zpow_le_iff] at h₁
  rw [← inv_div, map_inv₀, hk, ← _root_.zpow_neg, uniformizer_zpow_le_iff] at h₂
  have hϖ : valuation K (ϖ : K) = uniformizer K := hcϖ
  let u : Kˣ := a * d⁻¹ * (ϖ ^ k)⁻¹
  have hu : valuation K (u : K) = 1 := by
    have : (u : K) = (a : K) / d * ((ϖ : K) ^ k)⁻¹ := by
      simp [u, div_eq_mul_inv, Units.val_zpow_eq_zpow_val]
    rw [this, map_mul, map_inv₀, map_zpow₀, hk, hϖ,
      mul_inv_cancel₀ (zpow_ne_zero _ uniformizer_ne_zero)]
  have hdec : ((diagTorusHom (a, d) : torus K) : GL (Fin 2) K) =
      D k * ((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * scalarGL K 2 d := by
    rw [← diagTorusHom_self]
    simp only [D, ← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    congr 3
    refine Units.ext ?_
    simp only [u, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨k₁ * D k * (((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * k₂),
    Set.mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      ⟨(k₁, ((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) * k₂),
        ⟨hk₁, (maxCompact K).mul_mem (diagTorusHom_mem_maxCompact hu (by simp)) hk₂⟩, rfl⟩⟩,
    d, ?_⟩
  rw [hdec]
  simp only [mul_assoc, scalarGL_mul_comm d k₂]

/-- **The first case.** Assume that $Z \subseteq J$ and that for each $g \in K_0$ there is $y$ with $g n(y) g^{-1} \in J$ and $\Lambda(g n(y) g^{-1}) \neq 1$. Then $V^U$ has finite dimension for each open subgroup $U$, where $V = c\text{-}\mathrm{Ind}_J^G \Lambda$. A vector of $V^U$ is determined by its values on a finite set $T$ with $C \subseteq T U$. -/
theorem finiteDimensional_fixedVectors_of_forall (hJ : IsOpen (J : Set (GL (Fin 2) K)))
    (hΛ : IsOpen (Λ.ker : Set J)) (hZ : (scalarGL K 2).range ≤ J)
    (h1 : ∀ g ∈ maxCompact K, ∃ y, ∃ hy : g * unip y * g⁻¹ ∈ J, Λ ⟨_, hy⟩ ≠ 1)
    {U : Subgroup (GL (Fin 2) K)} (hU : IsOpen (U : Set (GL (Fin 2) K))) :
    FiniteDimensional ℂ (fixedVectors (cInd J Λ).ρ U) := by
  obtain ⟨C, hC, hCm⟩ := exists_isCompact_of_trivialOnConj hJ hΛ hU h1
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (U : Set _))
    (fun x _ => ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds
      (by simp [U.one_mem]))
  let φ : fixedVectors (cInd J Λ).ρ U →ₗ[ℂ] (t → ℂ) :=
    { toFun := fun f x => cInd.toFun f.1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective φ ((injective_iff_map_eq_zero φ).2 fun f hf => ?_)
  refine Subtype.ext (cInd.ext fun x => ?_)
  change cInd.toFun f.1 x = 0
  by_contra hx
  obtain ⟨c, hc, z, rfl⟩ := hCm x (trivialOnConj_of_mem_fixedVectors f.2 hx)
  obtain ⟨t₀, ht₀, hct⟩ := Set.mem_iUnion₂.1 (ht hc)
  have hu : t₀⁻¹ * c ∈ U := hct
  apply hx
  have hz : scalarGL K 2 z ∈ J := hZ ⟨z, rfl⟩
  have e : c * scalarGL K 2 z = ((⟨_, hz⟩ : J) : GL (Fin 2) K) * (t₀ * (t₀⁻¹ * c)) := by
    rw [mul_inv_cancel_left]
    exact (scalarGL_mul_comm z c).symm
  rw [e, cInd.toFun_mul_left]
  have hfix := congrArg (fun v => cInd.toFun v t₀) (f.2 _ hu)
  simp only [cInd.toFun_ρ] at hfix
  rw [hfix]
  have h0 := congrFun hf ⟨t₀, ht₀⟩
  change cInd.toFun f.1 t₀ = 0 at h0
  rw [h0, mul_zero]

/-- **Compact induction from a type is admissible** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 11.4, with 10.1). Let $J$ be an open subgroup of $GL_2(K)$ that is compact modulo the centre and $\Lambda$ a character of $J$ with open kernel. If each element that intertwines $\Lambda$ lies in $J$, then $c\text{-}\mathrm{Ind}_J^{GL_2(K)} \Lambda$ is admissible. -/
theorem isAdmissible_cInd_of_intertwining (hJ : IsOpen (J : Set (GL (Fin 2) K)))
    (hΛ : IsOpen (Λ.ker : Set J)) (hc : IsCompactModCenter J (scalarGL K 2).range)
    (hI : ∀ g, Intertwines J Λ g → g ∈ J) : (cInd J Λ).IsAdmissible := by
  by_cases h1 : ∀ g ∈ maxCompact K, ∃ y, ∃ hy : g * unip y * g⁻¹ ∈ J, Λ ⟨_, hy⟩ ≠ 1
  · exact fun U hU => finiteDimensional_fixedVectors_of_forall hJ hΛ
      (le_of_forall_intertwines range_scalarGL_le_center hI) h1 hU
  · push Not at h1
    obtain ⟨g₀, -, hg₀⟩ := h1
    exact isAdmissible_cInd_of_conj hJ hΛ hc hI hg₀

variable (K) in
/-- **Compact induction from a type is supercuspidal** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 11.4). The statement `Langlands.LocalGL2.CIndSupercuspidal K` holds with no input. -/
theorem cIndSupercuspidal : CIndSupercuspidal K := fun _ _ hJ hΛ hc hI =>
  ⟨isAdmissible_cInd_of_intertwining hJ hΛ hc hI,
    Langlands.LocalGL2.isSupercuspidal_cInd_of_isAdmissible hJ hΛ hc
      (isAdmissible_cInd_of_intertwining hJ hΛ hc hI)⟩

end Admissible

end Langlands.LocalGL2
