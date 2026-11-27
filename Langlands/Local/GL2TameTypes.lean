/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2Reduction
import Langlands.Local.JGroupCompact
import Langlands.Local.IntertwiningNormalizer
import Langlands.Local.AdaptedUnramified

/-!
# Cuspidal types and the tame parametrization

Let $K$ be a nonarchimedean local field with residue characteristic $p \ne 2$. This file reduces `Langlands.LocalGL2.TameParametrizationGL2` to finer published theorems on cuspidal types, and it proves the parts that the cuspidal types of this project give.

A cuspidal type datum for an admissible pair $(L/K, \xi)$ is a factorization $\xi = \xi_0 \otimes \chi_L$ with $\xi_0$ minimal of odd level $n$, together with a character $\psi$ of level one, an adapted basis of $L$, an element $\alpha \in L$ for $\xi_0$, and the cuspidal type $\Lambda_0$ of $J_\alpha = L^\times U^{[(n+1)/2]}_{\mathfrak{A}}$. Its representation is $c\text{-}\mathrm{Ind}_{J_\alpha}^{GL_2(K)} \Lambda$ with $\Lambda = \Lambda_0 \cdot (\chi \circ \det)$. A pair is covered when it is isomorphic to a pair with a datum. The representation of a datum is irreducible, it has central character $\xi|_{K^\times}$, and its twist by $\chi' \circ \det$ is the representation of a datum for $\xi \otimes \chi'_L$. These facts are proved here. Each ramified pair, and each pair whose minimal part has odd level, is covered, once a character $\psi$ of level one is given.

## Main definitions

* `Langlands.LocalGL2.TameDatum`: a cuspidal type datum for $(L/K, \xi)$, with its group `TameDatum.J` and its representation `TameDatum.rep`.
* `Langlands.LocalGL2.TameDatum.twist`: the twist of a datum by a smooth character of $K^\times$.
* `Langlands.LocalGL2.Covered`: the pairs that are isomorphic to a pair with a datum.
* `Langlands.LocalGL2.CIndSupercuspidal`: compact induction from a type is admissible and supercuspidal (BH 11.4).
* `Langlands.LocalGL2.TypeRepInjective`: isomorphic type representations come from isomorphic pairs (BH 15.6, 20.2).
* `Langlands.LocalGL2.TypeRepIndependent`: the type representation does not depend on the choices (BH §19, with 15.6).
* `Langlands.LocalGL2.TypeRepContragredient`: the contragredient of the representation for $\xi$ is the representation for $\xi^{-1}$ (BH 19.4).
* `Langlands.LocalGL2.UncoveredConstruction`, `Langlands.LocalGL2.UncoveredInjective`, `Langlands.LocalGL2.Exhaustion`: properties of a map $\sigma$ on the pairs that are not covered (BH 19.1 and 19.3, BH 20.2, BH 15.5 and 15.8).
* `Langlands.LocalGL2.UncoveredParametrization`: there is a map $\sigma$ with these three properties.
* `Langlands.LocalGL2.TameTypeInputs`: the five inputs above.
* `Langlands.LocalGL2.typeParam`: the map $P \mapsto \pi_P$.

## Main results

* `Langlands.iso_twist_cInd`: $(c\text{-}\mathrm{Ind}_J^G \Lambda) \otimes \theta \cong c\text{-}\mathrm{Ind}_J^G (\Lambda \cdot \theta|_J)$.
* `Langlands.LocalGL2.IsMinimal.isMinimalElt_unram`: for an unramified minimal pair, each $\alpha$ for $\xi$ is a minimal element.
* `Langlands.LocalGL2.TameDatum.isIrreducible`: the representation of a datum is irreducible.
* `Langlands.LocalGL2.TameDatum.hasCentralChar`: its central character is $\xi|_{K^\times}$.
* `Langlands.LocalGL2.TameDatum.iso_twist`: its twist by $\chi \circ \det$ is the representation of the twisted datum.
* `Langlands.LocalGL2.nonempty_tameDatum_of_isMinimal`: a minimal character of odd level has a datum.
* `Langlands.LocalGL2.covered_of_isTotallyRamifiedExt`, `Langlands.LocalGL2.covered_of_odd_level`: the ramified pairs and the pairs of odd minimal level are covered.
* `Langlands.LocalGL2.tameParametrizationGL2_of_inputs`: `Langlands.LocalGL2.TameTypeInputs` gives `Langlands.LocalGL2.TameParametrizationGL2`.
* `Langlands.LocalGL2.gl2OddInputs_of_tameTypeInputs`: it gives the field `tame` of `Langlands.LocalGL2.GL2OddInputs`.

## Implementation notes

The map $\pi_P$ is the class of the representation of a chosen datum when $P$ is covered, and $\sigma(P)$ otherwise. The proof of each clause of `Langlands.LocalGL2.TameParametrizationGL2` splits into these two cases. For covered pairs, the central character and the twist rule are proved here, and the other clauses use the named inputs. The pairs that are not covered are closed under twists and inverses, so $\sigma$ handles them alone. The inputs on $\sigma$ are properties of one map, because the representations for these pairs are not constructed here. Each input holds for the map $\sigma(P) = \pi_\xi$ of Bushnell and Henniart.

## Still open

* The construction of the representations for the pairs of level zero (BH 19.1) and for the unramified pairs whose minimal part has even level, with the Heisenberg types (BH 19.3). This would remove `Langlands.LocalGL2.UncoveredConstruction`.
* Proofs of `Langlands.LocalGL2.CIndSupercuspidal`, `Langlands.LocalGL2.TypeRepInjective`, `Langlands.LocalGL2.TypeRepIndependent`, `Langlands.LocalGL2.TypeRepContragredient`, `Langlands.LocalGL2.UncoveredInjective` and `Langlands.LocalGL2.Exhaustion`.
* The existence of a character of $K$ of level one. The coverage results take it as a hypothesis.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), chapters 3 and 4, §§10 to 20.
-/

namespace Langlands

universe w

open SmoothRep

section TwistInduction

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Isomorphic representations have isomorphic twists. -/
theorem SmoothRep.Iso.twist {π π' : SmoothRep G} (h : π.Iso π') (θ : G →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set G)) : (π.twist θ hθ).Iso (π'.twist θ hθ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g v => ?_⟩
  change e ((θ g : ℂ) • π.ρ g v) = (θ g : ℂ) • π'.ρ g (e v)
  rw [map_smul]
  exact congrArg ((θ g : ℂ) • ·) (he g v)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The kernel of $\theta^{-1}$ is the kernel of $\theta$. -/
theorem ker_inv_char (θ : G →* ℂˣ) : (θ⁻¹).ker = θ.ker := by
  ext x
  simp [MonoidHom.mem_ker]

variable {J : Subgroup G} {Λ Λ' : J →* ℂˣ}

/-- The map $f \mapsto \theta f$ from $c\text{-}\mathrm{Ind}_J^G \Lambda$ to $c\text{-}\mathrm{Ind}_J^G \Lambda'$, for a character $\theta$ of $G$ with open kernel and $\Lambda' = \Lambda \cdot \theta|_J$. -/
noncomputable def cIndMulChar (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G))
    (h : ∀ j : J, Λ' j = Λ j * θ j) : (cInd J Λ).V →ₗ[ℂ] (cInd J Λ').V where
  toFun f := ⟨fun x => (θ x : ℂ) * cInd.toFun f x, by
    obtain ⟨h1, ⟨U, hU, hfU⟩, S, hS⟩ := (show cIndSpace J Λ from f).2
    refine ⟨fun j g => ?_, ⟨U ⊓ θ.ker, by rw [Subgroup.coe_inf]; exact hU.inter hθ,
      fun g u hu => ?_⟩, S, fun g hg => hS g ?_⟩
    · have := h1 j g
      change (θ (j * g) : ℂ) * cInd.toFun f (j * g) = (Λ' j : ℂ) * ((θ g : ℂ) * cInd.toFun f g)
      change _ * (show cIndSpace J Λ from f).1 (j * g) = _ * (_ * (show cIndSpace J Λ from f).1 g)
      rw [this, h, map_mul, Units.val_mul, Units.val_mul]
      ring
    · rw [Subgroup.mem_inf, MonoidHom.mem_ker] at hu
      change (θ (g * u) : ℂ) * (show cIndSpace J Λ from f).1 (g * u) =
        (θ g : ℂ) * (show cIndSpace J Λ from f).1 g
      rw [hfU g u hu.1, map_mul, hu.2, mul_one]
    · intro h0
      apply hg
      change (θ g : ℂ) * (show cIndSpace J Λ from f).1 g = 0
      rw [h0, mul_zero]⟩
  map_add' f f' := by
    refine cInd.ext fun x => ?_
    change (θ x : ℂ) * (cInd.toFun f x + cInd.toFun f' x) =
      (θ x : ℂ) * cInd.toFun f x + (θ x : ℂ) * cInd.toFun f' x
    ring
  map_smul' c f := by
    refine cInd.ext fun x => ?_
    change (θ x : ℂ) * (c * cInd.toFun f x) = c * ((θ x : ℂ) * cInd.toFun f x)
    ring

/-- The function of $\theta f$ is $x \mapsto \theta(x) f(x)$. -/
theorem cInd.toFun_cIndMulChar (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G))
    (h : ∀ j : J, Λ' j = Λ j * θ j) (f : (cInd J Λ).V) (x : G) :
    cInd.toFun (cIndMulChar θ hθ h f) x = (θ x : ℂ) * cInd.toFun f x :=
  rfl

/-- **Twists of a compact induction.** Let $\theta$ be a character of $G$ with open kernel and let $\Lambda'(j) = \Lambda(j) \theta(j)$ on $J$. Then $(c\text{-}\mathrm{Ind}_J^G \Lambda) \otimes \theta \cong c\text{-}\mathrm{Ind}_J^G \Lambda'$, by $f \mapsto \theta f$. -/
theorem iso_twist_cInd (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G))
    (h : ∀ j : J, Λ' j = Λ j * θ j) : ((cInd J Λ).twist θ hθ).Iso (cInd J Λ') := by
  have hθ' : IsOpen ((θ⁻¹).ker : Set G) := by rw [ker_inv_char]; exact hθ
  have h' : ∀ j : J, Λ j = Λ' j * θ⁻¹ j := fun j => by
    rw [h, MonoidHom.inv_apply, mul_inv_cancel_right]
  have hinv : ∀ x, (θ⁻¹ x : ℂ) * (θ x : ℂ) = 1 := fun x => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have hinv' : ∀ x, (θ x : ℂ) * (θ⁻¹ x : ℂ) = 1 := fun x => by rw [mul_comm, hinv]
  let e : (cInd J Λ).V ≃ₗ[ℂ] (cInd J Λ').V :=
    { cIndMulChar θ hθ h with
      invFun := cIndMulChar θ⁻¹ hθ' h'
      left_inv := fun f => cInd.ext fun x => by
        change (θ⁻¹ x : ℂ) * ((θ x : ℂ) * cInd.toFun f x) = cInd.toFun f x
        rw [← mul_assoc, hinv, one_mul]
      right_inv := fun f => cInd.ext fun x => by
        change (θ x : ℂ) * ((θ⁻¹ x : ℂ) * cInd.toFun f x) = cInd.toFun f x
        rw [← mul_assoc, hinv', one_mul] }
  refine ⟨e, fun g f => cInd.ext fun x => ?_⟩
  change (θ x : ℂ) * ((θ g : ℂ) * cInd.toFun f (x * g)) = (θ (x * g) : ℂ) * cInd.toFun f (x * g)
  rw [map_mul, Units.val_mul]
  ring

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If $\Lambda' = \Lambda \cdot \theta|_J$ and $\theta$ is a character of $G$, then each element that intertwines $\Lambda'$ intertwines $\Lambda$. The reason is $\theta(g x g^{-1}) = \theta(x)$. -/
theorem Intertwines.of_mul_char {θ : G →* ℂˣ} (h : ∀ j : J, Λ' j = Λ j * θ j) {g : G}
    (hg : Intertwines J Λ' g) : Intertwines J Λ g := by
  intro x hx
  have e := hg x hx
  rw [h, h] at e
  have hc : θ (g * x * g⁻¹) = θ x := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [hc] at e
  exact mul_right_cancel e

/-- If $\Lambda$ and $\theta$ have open kernels, then $\Lambda' = \Lambda \cdot \theta|_J$ has an open kernel. -/
theorem isOpen_ker_of_mul_char {θ : G →* ℂˣ} (h : ∀ j : J, Λ' j = Λ j * θ j)
    (hΛ : IsOpen (Λ.ker : Set J)) (hθ : IsOpen (θ.ker : Set G)) : IsOpen (Λ'.ker : Set J) := by
  refine Subgroup.isOpen_mono (H₁ := Λ.ker ⊓ θ.ker.subgroupOf J) ?_ ?_
  · intro j hj
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hj
    rw [MonoidHom.mem_ker, h, hj.1, hj.2, mul_one]
  · rw [Subgroup.coe_inf, Subgroup.coe_subgroupOf]
    exact hΛ.inter (hθ.preimage continuous_subtype_val)

end TwistInduction

/-- An isomorphism carries a central character: if $\pi \cong \pi'$ and $\pi'$ has central character $\omega$, then $\pi$ has central character $\omega$. -/
theorem SmoothRep.HasCentralChar.of_iso {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {π π' : SmoothRep (GL (Fin 2) K)} (h : π.Iso π')
    {ω : Kˣ →* ℂˣ} (hω : π'.HasCentralChar ω) : π.HasCentralChar ω := by
  obtain ⟨e, he⟩ := h
  intro a v
  apply e.injective
  rw [he, hω, map_smul]

end Langlands

namespace Langlands.LocalGL2

universe u v

open Langlands.WeilGroup Langlands.WeilGroup.FiniteExt ValuativeRel Matrix LocalGL1 ChainOrder

section MinimalElement

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [Valuation.HasExtension (valuation F) (valuation E)]
  [Algebra.IsQuadraticExtension F E]

/-- **The element $\alpha$ of an unramified minimal pair is minimal** (BH §13.4 and §19). Let $E/F$ be unramified, let $2 \ne 0$ in $k_F$, let $\psi$ have level one, and let $(E/F, \xi)$ be a minimal pair of level $n \ge 1$. If $\mathrm{ord}_E(\alpha) = -n$ and $\xi(1 + y) = \psi(\mathrm{tr}_{E/F}(\alpha y))$ for each $y \in \mathfrak{p}^{[n/2]+1}_E$, then $\alpha \notin F + \mathfrak{p}^{1-n}_E$. If $\alpha - a \in \mathfrak{p}^{1-n}_E$ with $a \in F$, then $\xi(u) = \psi(a (N_{E/F}(u) - 1))$ on $U^n_E$, so $\xi$ on $U^n_E$ factors through $N_{E/F}$. -/
theorem IsMinimal.isMinimalElt_unram (h2 : (2 : 𝓀[F]) ≠ 0) (hu : IsUnramifiedExt F E)
    {ψ : AddChar F ℂ} (hψ : IsConductor ψ (-1)) {ξ : Eˣ →* ℂˣ} (hξ : IsMinimal F E ξ)
    (hn : 1 ≤ level ξ) {α : E} (hα0 : α ≠ 0) (hord : ord E α = -(level ξ : ℤ))
    (hαξ : ∀ y ∈ ordBall E ((level ξ / 2 + 1 : ℕ) : ℤ), ∀ u : Eˣ, (u : E) = 1 + y →
      (ξ u : ℂ) = ψ (Algebra.trace F E (α * y))) :
    IsMinimalElt F (level ξ) α := by
  have := isSeparable_of_two_ne_zero F E (two_ne_zero_of_residue h2)
  set n := level ξ with hndef
  have hαb : α ∈ ordBall E (-(n : ℤ)) := mem_ordBall_of_le hα0 hord.ge
  refine ⟨hαb, fun a hb => ?_⟩
  have haE : algebraMap F E a ∈ ordBall E (-(n : ℤ)) := by
    have e : algebraMap F E a = α + -(α - algebraMap F E a) := by ring
    rw [e]
    exact add_mem_ordBall hαb (neg_mem_ordBall (ordBall_anti (by omega) hb))
  have ha : a ∈ ordBall F (-(n : ℤ)) := (algebraMap_mem_ordBall_iff hu a _).1 haE
  obtain ⟨φ₀, hφ₀⟩ := exists_psiChar_unitFilt hψ hn ha
  obtain ⟨φ, hφ⟩ := exists_extend_char _ φ₀
  apply hξ.not_factor_level
  refine ⟨φ, fun u hu' => ?_⟩
  have he : ramIdx F E = 1 := isUnramifiedExt_iff_ramIdx.1 hu
  have hN : normUnits F E u ∈ unitFilt F n :=
    normUnits_mem_unitFilt_of_lt hu' (by rw [he]; omega)
  have h1 := hφ ⟨_, hN⟩
  rw [hφ₀] at h1
  simp only at h1
  rw [h1]
  set y : E := (u : E) - 1 with hy
  have hyb : y ∈ ordBall E ((n / 2 + 1 : ℕ) : ℤ) := ordBall_anti (by push_cast; omega) hu'.2
  have h3 := hαξ y hyb u (by rw [hy]; ring)
  have h5 : ψ (Algebra.trace F E ((α - algebraMap F E a) * y)) = 1 := by
    refine hψ.trivial _ ?_
    simp only [neg_neg]
    exact trace_mem_ordBall_one (mem_ordBall_congr (by ring) (mul_mem_ordBall_add hb hu'.2))
  have h6 : ψ (Algebra.trace F E (α * y)) = ψ (Algebra.trace F E (algebraMap F E a * y)) := by
    have e : α * y = algebraMap F E a * y + (α - algebraMap F E a) * y := by ring
    rw [e, map_add, AddChar.map_add_eq_mul, h5, mul_one]
  rw [h6] at h3
  apply Units.ext
  rw [h3, psiUnit, Units.val_mk0]
  have hnorm : algebraMap F E (Algebra.norm F (u : E) - 1) =
      algebraMap F E (Algebra.trace F E y + Algebra.norm F y) := by
    rw [map_sub, map_one, map_add, algebraMap_norm_eq_mul, algebraMap_trace_eq_add,
      algebraMap_norm_eq_mul, show (u : E) = 1 + y by rw [hy]; ring, map_add, map_one]
    ring
  have hnorm' := (algebraMap F E).injective hnorm
  rw [val_normUnits, hnorm', mul_add, AddChar.map_add_eq_mul]
  have h4 : ψ (a * Algebra.norm F y) = 1 := by
    refine hψ.trivial _ ?_
    simp only [neg_neg]
    rw [← algebraMap_mem_ordBall_iff hu, map_mul, algebraMap_norm_eq_mul]
    have hσ : galConj F E y ∈ ordBall E n := (map_mem_ordBall_iff _ _ _).2 hu'.2
    refine ordBall_anti ?_ (mul_mem_ordBall_add haE (mul_mem_ordBall_add hu'.2 hσ))
    omega
  rw [h4, mul_one, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

end MinimalElement

section Datum

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **A cuspidal type datum for $(L/K, \xi)$** (BH §15 and §19). It consists of a character $\psi$ of $K$ of level one, an adapted basis $v$ of $L$ for a chain order $\mathfrak{A}$, a minimal character $\xi_0$ of $L^\times$ of odd level $n$, a minimal element $\alpha \in L$ of level $n$ with $\xi_0(1 + y) = \psi(\mathrm{tr}(\alpha y))$ near $1$, the cuspidal type $\Lambda_0$ of $J_\alpha = L^\times U^{[(n+1)/2]}_{\mathfrak{A}}$ for $(\alpha, \xi_0)$, and a smooth character $\chi$ of $K^\times$ with $\xi = \xi_0 \otimes \chi_L$. The character of the datum is $\Lambda = \Lambda_0 \cdot (\chi \circ \det)$. -/
structure TameDatum (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsQuadraticExtension K L]
    (ξ : Lˣ →* ℂˣ) : Type u where
  /-- The additive character of level one. -/
  ψ : AddChar K ℂ
  /-- The character $\psi$ has level one. -/
  hψ : IsConductor ψ (-1)
  /-- The chain order. -/
  A : ChainOrder
  /-- The basis of $L$ over $K$. -/
  v : Module.Basis (Fin 2) K L
  /-- The basis is adapted to the chain order. -/
  hv : IsAdapted A v
  /-- The minimal character. -/
  ξ₀ : Lˣ →* ℂˣ
  /-- The element $\alpha$. -/
  α : L
  /-- The matrix of $\alpha$ lies in $\mathfrak{P}^{-n}_{\mathfrak{A}}$. -/
  hα : Algebra.leftMulMatrix v α ∈ radPow K A (-(level ξ₀ : ℤ))
  /-- The cuspidal type of $\xi_0$. -/
  Λ₀ : jGroup v hv ((level ξ₀ + 1) / 2) →* ℂˣ
  /-- The twisting character. -/
  χ : Kˣ →* ℂˣ
  /-- The character $\Lambda_0 \cdot (\chi \circ \det)$. -/
  Λ : jGroup v hv ((level ξ₀ + 1) / 2) →* ℂˣ
  /-- The character $\xi_0$ is minimal. -/
  minimal : IsMinimal K L ξ₀
  /-- The level of $\xi_0$ is odd. -/
  odd : Odd (level ξ₀)
  /-- The element $\alpha$ is minimal. -/
  minElt : IsMinimalElt K (level ξ₀) α
  /-- The character $\Lambda_0$ is a cuspidal type for $(\alpha, \xi_0)$. -/
  mem : Λ₀ ∈ cuspTypes hv ψ hψ (level ξ₀) α hα ξ₀
  /-- The character $\chi$ is smooth. -/
  smooth : IsSmoothChar K χ
  /-- The equation $\xi = \xi_0 \otimes \chi_L$. -/
  eq : ξ = twistChar K L ξ₀ χ
  /-- The equation $\Lambda = \Lambda_0 \cdot (\chi \circ \det)$. -/
  mul : ∀ x, Λ x = Λ₀ x * detChar K 2 χ (x : GL (Fin 2) K)

variable {K}

namespace TameDatum

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  {ξ : Lˣ →* ℂˣ}

/-- The group $J_\alpha = L^\times U^{[(n+1)/2]}_{\mathfrak{A}}$ of a datum. -/
noncomputable abbrev J (D : TameDatum K L ξ) : Subgroup (GL (Fin 2) K) :=
  jGroup D.v D.hv ((level D.ξ₀ + 1) / 2)

/-- The representation $\pi_D = c\text{-}\mathrm{Ind}_{J_\alpha}^{GL_2(K)} \Lambda$ of a datum. It is isomorphic to $(c\text{-}\mathrm{Ind}_{J_\alpha}^{GL_2(K)} \Lambda_0) \otimes (\chi \circ \det)$. -/
noncomputable abbrev rep (D : TameDatum K L ξ) : SmoothRep (GL (Fin 2) K) :=
  SmoothRep.cInd D.J D.Λ

/-- The level $n$ of $\xi_0$ is at least $1$. -/
theorem one_le_level (D : TameDatum K L ξ) : 1 ≤ level D.ξ₀ := by
  obtain ⟨k, hk⟩ := D.odd
  omega

/-- The character $\Lambda$ of a datum has an open kernel. -/
theorem isOpen_ker (D : TameDatum K L ξ) : IsOpen (D.Λ.ker : Set D.J) :=
  isOpen_ker_of_mul_char D.mul
    (IsTypeChar.isOpen_ker D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ (hm := by omega) D.mem)
    (isOpen_ker_detChar K 2 D.χ D.smooth)

/-- Each element of $GL_2(K)$ that intertwines $\Lambda$ lies in $J_\alpha$ (BH §15.1). -/
theorem mem_of_intertwines (D : TameDatum K L ξ) (g : GL (Fin 2) K)
    (hg : Intertwines D.J D.Λ g) : g ∈ D.J :=
  mem_jGroup_of_intertwines_cuspType_of_isMinimalElt D.ψ D.hψ D.hα D.ξ₀ D.hv D.minElt
    D.one_le_level D.mem g (hg.of_mul_char D.mul)

/-- **The representation of a datum is irreducible** (BH 11.4 and §15). -/
theorem isIrreducible (D : TameDatum K L ξ) : D.rep.IsIrreducible :=
  isIrreducible_cInd _ D.Λ (isOpen_jGroup D.hv _) D.isOpen_ker range_scalarGL_le_center
    (isCompactModCenter_jGroup D.hv _) D.mem_of_intertwines

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The norm of $c \in K^\times$ is $c^2 = \det(c \cdot 1)$. -/
theorem det_scalarGL_eq_normUnits (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (scalarGL K 2 c) =
      normUnits K L (Units.map (algebraMap K L).toMonoidHom c) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_normUnits]
  simp [scalarGL, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
    pow_two]

/-- **The central character of the representation of a datum** is $\xi|_{K^\times}$. -/
theorem hasCentralChar (D : TameDatum K L ξ) :
    D.rep.HasCentralChar (ξ.comp (Units.map (algebraMap K L).toMonoidHom)) := by
  intro c (f : (SmoothRep.cInd D.J D.Λ).V)
  have hz := scalarGL_mem_jGroup D.hv ((level D.ξ₀ + 1) / 2) c
  have hmem : IsTypeChar D.hv D.ψ D.hψ _ D.α D.hα D.ξ₀ ((level D.ξ₀ + 1) / 2) (by omega) D.Λ₀ :=
    D.mem
  have h1 : D.Λ₀ ⟨scalarGL K 2 c, hz⟩ = D.ξ₀ (Units.map (algebraMap K L).toMonoidHom c) := by
    rw [← hmem.2]
    congr 1
    exact Subtype.ext (embGL_algebraMap c).symm
  have h2 := DFunLike.congr_fun D.eq (Units.map (algebraMap K L).toMonoidHom c)
  rw [cInd.ρ_center (scalarGL_mem_center c) hz, D.mul, h1, MonoidHom.comp_apply, h2,
    twistChar_apply]
  simp only [detChar, MonoidHom.comp_apply]
  rw [det_scalarGL_eq_normUnits (L := L)]

/-- The twist of a datum by a smooth character $\chi$ of $K^\times$: a datum for $\xi \otimes \chi_L$, with the character $\Lambda \cdot (\chi \circ \det)$. -/
noncomputable def twist (D : TameDatum K L ξ) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    TameDatum K L (twistChar K L ξ χ) where
  ψ := D.ψ
  hψ := D.hψ
  A := D.A
  v := D.v
  hv := D.hv
  ξ₀ := D.ξ₀
  α := D.α
  hα := D.hα
  Λ₀ := D.Λ₀
  χ := D.χ * χ
  Λ := D.Λ * (detChar K 2 χ).comp D.J.subtype
  minimal := D.minimal
  odd := D.odd
  minElt := D.minElt
  mem := D.mem
  smooth := LocalGL1.isSmoothChar_mul D.smooth hχ
  eq := by
    rw [← twistChar_twistChar]
    exact congrArg (twistChar K L · χ) D.eq
  mul x := by
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, D.mul, detChar, Subgroup.coe_subtype,
      mul_assoc]

/-- **Twisting a datum** (BH §19): $\pi_D \otimes (\chi \circ \det) \cong \pi_{D \otimes \chi}$. -/
theorem iso_twist (D : TameDatum K L ξ) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    (D.rep.twist (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ)).Iso (D.twist χ hχ).rep :=
  iso_twist_cInd _ _ fun _ => rfl

end TameDatum

end Datum

section Existence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Minimal pairs of odd level have a datum** (BH §15 and §19). Let $2 \ne 0$ in $k_K$, and let $\psi$ be a character of $K$ of level one. If $\xi$ is a minimal character of $L^\times$ of odd level, then there is a cuspidal type datum for $(L/K, \xi)$, with $\chi = 1$. -/
theorem nonempty_tameDatum_of_isMinimal (h2 : (2 : 𝓀[K]) ≠ 0) {ψ : AddChar K ℂ}
    (hψ : IsConductor ψ (-1)) {L : IntermediateField K (AlgebraicClosure K)}
    [Algebra.IsQuadraticExtension K L] {ξ : Lˣ →* ℂˣ} (hξ : IsMinimal K L ξ)
    (hodd : Odd (level ξ)) : Nonempty (TameDatum K L ξ) := by
  have := isSeparable_of_two_ne_zero K L (two_ne_zero_of_residue h2)
  have hn : 1 ≤ level ξ := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨α, hα0, hord, hαξ⟩ := hξ.admissible.exists_alpha h2 hψ hn
  have hcomp : IsCompatible ψ (level ξ) α ξ := fun y hy =>
    hαξ _ (mem_unitFilt.1 hy).2 y (by ring)
  rcases isUnramifiedExt_or_isTotallyRamifiedExt (F := K) (E := L) with hu | hr
  · have hα := (isSimpleStratum_unramBasis hu hn hord
      (hξ.alpha_not_mem h2 hu hψ hn (mem_ordBall_of_le hα0 hord.ge) hαξ)).mem
    obtain ⟨Λ₀, hΛ₀, -⟩ :=
      (existsUnique_mem_cuspTypes_iff (isAdapted_unramBasis hu) ψ hψ _ α hα ξ hodd).2 hcomp
    exact ⟨⟨ψ, hψ, maximal, unramBasis K L hu, isAdapted_unramBasis hu, ξ, α, hα, Λ₀, 1, Λ₀, hξ,
      hodd, hξ.isMinimalElt_unram h2 hu hψ hn hα0 hord hαξ, hΛ₀, isSmoothChar_one',
      (twistChar_one ξ).symm, fun x => by simp [detChar]⟩⟩
  · have hα := (isSimpleStratum_ramBasis hr hn hodd hord).mem
    obtain ⟨Λ₀, hΛ₀, -⟩ :=
      (existsUnique_mem_cuspTypes_iff (isAdapted_ramBasis hr) ψ hψ _ α hα ξ hodd).2 hcomp
    exact ⟨⟨ψ, hψ, iwahori, ramBasis K L hr, isAdapted_ramBasis hr, ξ, α, hα, Λ₀, 1, Λ₀, hξ,
      hodd, isMinimalElt_of_ramified hr hodd hα0 hord, hΛ₀, isSmoothChar_one',
      (twistChar_one ξ).symm, fun x => by simp [detChar]⟩⟩

end Existence

section Pairs

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace TamePair

/-- Each pair is isomorphic to itself. -/
theorem Iso.refl (P : TamePair K) : P.Iso P :=
  (TamePair.setoid (K := K)).iseqv.refl P

/-- The isomorphism of pairs is symmetric. -/
theorem Iso.symm {P Q : TamePair K} (h : P.Iso Q) : Q.Iso P :=
  (TamePair.setoid (K := K)).iseqv.symm h

/-- The isomorphism of pairs is transitive. -/
theorem Iso.trans {P Q R : TamePair K} (h : P.Iso Q) (h' : Q.Iso R) : P.Iso R :=
  (TamePair.setoid (K := K)).iseqv.trans h h'

/-- Isomorphic pairs have isomorphic twists (BH 18.2). -/
theorem Iso.twist {P Q : TamePair K} (h : P.Iso Q) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    (P.twist χ hχ).Iso (Q.twist χ hχ) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, MonoidHom.ext fun (x : P.Lˣ) => ?_⟩
  change twistChar K P.L P.ξ χ x = twistChar K Q.L Q.ξ χ (unitsMap j x)
  rw [twistChar_apply, twistChar_apply, hj, MonoidHom.comp_apply]
  congr 2
  exact (DFunLike.congr_fun (normUnits_comp_unitsMap j) x).symm

/-- Isomorphic pairs have isomorphic inverses. -/
theorem Iso.inv {P Q : TamePair K} (h : P.Iso Q) : P.inv.Iso Q.inv := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, MonoidHom.ext fun (x : P.Lˣ) => ?_⟩
  change P.ξ⁻¹ x = Q.ξ⁻¹ (unitsMap j x)
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hj, MonoidHom.comp_apply]

/-- Isomorphic pairs have the same restriction $\xi|_{K^\times}$. -/
theorem Iso.comp_algebraMap {P Q : TamePair K} (h : P.Iso Q) :
    P.ξ.comp (Units.map (algebraMap K P.L).toMonoidHom) =
      Q.ξ.comp (Units.map (algebraMap K Q.L).toMonoidHom) := by
  obtain ⟨j, hj⟩ := h
  refine MonoidHom.ext fun c => ?_
  rw [MonoidHom.comp_apply, hj, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact congrArg Q.ξ (Units.ext (j.commutes c))

/-- The twist by $\chi$ and then by $\chi^{-1}$ gives back the pair. -/
theorem twist_twist_inv (P : TamePair K) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (hχ' : IsSmoothChar K χ⁻¹) : ((P.twist χ hχ).twist χ⁻¹ hχ').Iso P := by
  refine ⟨AlgEquiv.refl, MonoidHom.ext fun (x : P.Lˣ) => ?_⟩
  change twistChar K P.L (twistChar K P.L P.ξ χ) χ⁻¹ x = P.ξ (unitsMap (AlgEquiv.refl : P.L ≃ₐ[K] P.L) x)
  rw [twistChar_twistChar, twistChar_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
    mul_inv_cancel, mul_one]
  exact congrArg P.ξ (Units.ext rfl)

/-- The inverse of the inverse gives back the pair. -/
theorem inv_inv (P : TamePair K) : P.inv.inv.Iso P := by
  refine ⟨AlgEquiv.refl, MonoidHom.ext fun (x : P.Lˣ) => ?_⟩
  change (P.ξ⁻¹)⁻¹ x = P.ξ (unitsMap (AlgEquiv.refl : P.L ≃ₐ[K] P.L) x)
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, _root_.inv_inv]
  exact congrArg P.ξ (Units.ext rfl)

end TamePair

variable (K) in
/-- A pair is covered when it is isomorphic to a pair with a cuspidal type datum. -/
def Covered (P : TamePair K) : Prop :=
  ∃ Q : TamePair K, Q.Iso P ∧ Nonempty (TameDatum K Q.L Q.ξ)

/-- A pair with a datum is covered. -/
theorem covered_of_datum {P : TamePair K} (D : TameDatum K P.L P.ξ) : Covered K P :=
  ⟨P, TamePair.Iso.refl P, ⟨D⟩⟩

/-- A pair that is isomorphic to a covered pair is covered. -/
theorem Covered.of_iso {P Q : TamePair K} (h : Covered K P) (hPQ : P.Iso Q) : Covered K Q := by
  obtain ⟨R, hR, hD⟩ := h
  exact ⟨R, hR.trans hPQ, hD⟩

/-- **Pairs that are twists of minimal pairs of odd level are covered** (BH §19). -/
theorem covered_of_isMinimal (h2 : (2 : 𝓀[K]) ≠ 0) {ψ : AddChar K ℂ} (hψ : IsConductor ψ (-1))
    (P : TamePair K) {ξ₀ : P.Lˣ →* ℂˣ} (hξ : IsMinimal K P.L ξ₀) (hodd : Odd (level ξ₀))
    {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) (heq : P.ξ = twistChar K P.L ξ₀ χ) : Covered K P := by
  obtain ⟨D⟩ := nonempty_tameDatum_of_isMinimal h2 hψ hξ hodd
  have D' := D.twist χ hχ
  rw [← heq] at D'
  exact covered_of_datum D'

/-- **Ramified pairs are covered** (BH §19). Let $2 \ne 0$ in $k_K$ and let $\psi$ be a character of $K$ of level one. Each pair $(L/K, \xi)$ with $L/K$ totally ramified is covered. -/
theorem covered_of_isTotallyRamifiedExt (h2 : (2 : 𝓀[K]) ≠ 0) {ψ : AddChar K ℂ}
    (hψ : IsConductor ψ (-1)) (P : TamePair K) (hr : IsTotallyRamifiedExt K P.L) :
    Covered K P := by
  obtain ⟨ξ₀, hξ, χ, hχ, heq⟩ := P.adm.exists_isMinimal_twistChar
  exact covered_of_isMinimal h2 hψ P hξ (hξ.odd_level (Or.inl h2) hr) hχ heq

/-- **Unramified pairs of odd level are covered** (BH §19). Let $2 \ne 0$ in $k_K$ and let $\psi$ be a character of $K$ of level one. A pair $(L/K, \xi)$ with $\xi = \xi_0 \otimes \chi_L$ for a minimal $\xi_0$ of odd level is covered. With `covered_of_isTotallyRamifiedExt`, only the unramified pairs whose minimal part has even level, or level zero, can fail to be covered. -/
theorem covered_of_odd_level (h2 : (2 : 𝓀[K]) ≠ 0) {ψ : AddChar K ℂ} (hψ : IsConductor ψ (-1))
    (P : TamePair K) (h : ∃ ξ₀ : P.Lˣ →* ℂˣ, IsMinimal K P.L ξ₀ ∧ Odd (level ξ₀) ∧
      ∃ χ : Kˣ →* ℂˣ, IsSmoothChar K χ ∧ P.ξ = twistChar K P.L ξ₀ χ) : Covered K P := by
  obtain ⟨ξ₀, hξ, hodd, χ, hχ, heq⟩ := h
  exact covered_of_isMinimal h2 hψ P hξ hodd hχ heq

end Pairs

section Inputs

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Compact induction from a type is supercuspidal** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 11.4, with 10.1 for admissibility). Let $J$ be an open subgroup of $GL_2(K)$ that is compact modulo the centre, and $\Lambda$ a character of $J$ with open kernel. If each element that intertwines $\Lambda$ lies in $J$, then $c\text{-}\mathrm{Ind}_J^{GL_2(K)} \Lambda$ is admissible and supercuspidal. Its irreducibility is proved in `Langlands.isIrreducible_cInd`. -/
def CIndSupercuspidal : Prop :=
  ∀ (J : Subgroup (GL (Fin 2) K)) (Λ : J →* ℂˣ), IsOpen (J : Set (GL (Fin 2) K)) →
    IsOpen (Λ.ker : Set J) → IsCompactModCenter J (scalarGL K 2).range →
    (∀ g, Intertwines J Λ g → g ∈ J) →
    (SmoothRep.cInd J Λ).IsAdmissible ∧ (SmoothRep.cInd J Λ).IsSupercuspidal (scalarGL K 2)

/-- **Cuspidal types determine the pair** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 15.6 and 20.2). Let $p \ne 2$. If the representations of a datum for $(L/K, \xi)$ and of a datum for $(L'/K, \xi')$ are isomorphic, then the pairs are $K$-isomorphic. -/
def TypeRepInjective : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ),
    D.rep.Iso D'.rep → P.Iso Q

/-- **The representation does not depend on the choices** (Bushnell and Henniart, The local Langlands conjecture for GL(2), §19, the definition of $\pi_\xi$; the proof uses 15.6). Let $p \ne 2$. For $K$-isomorphic pairs, the representations of any two data are isomorphic. The choices are $\psi$, $\alpha$, the adapted basis, and the factorization $\xi = \xi_0 \otimes \chi_L$. -/
def TypeRepIndependent : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P Q : TamePair K) (D : TameDatum K P.L P.ξ) (D' : TameDatum K Q.L Q.ξ),
    P.Iso Q → D.rep.Iso D'.rep

/-- **The contragredient of a type representation** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 19.4). Let $p \ne 2$. If $\pi$ is isomorphic to the representation of a datum for $(L/K, \xi)$, then each representation isomorphic to the contragredient of $\pi$ is isomorphic to the representation of a datum for $(L/K, \xi^{-1})$. -/
def TypeRepContragredient : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∀ (P : TamePair K) (D : TameDatum K P.L P.ξ)
    (π π' : SmoothRep (GL (Fin 2) K)), π.Iso D.rep → π'.Iso π.contragredient →
      ∃ D' : TameDatum K P.inv.L P.inv.ξ, π'.Iso D'.rep

/-- **The construction for the pairs that are not covered** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 19.1 and 19.3), as a property of a map $\sigma$. For each pair $P$ that is not covered, $\sigma(P)$ is supercuspidal, has central character $\xi|_{K^\times}$, and satisfies the twist and contragredient rules of `Langlands.LocalGL2.TameParametrizationGL2`. -/
def UncoveredConstruction (σ : TamePair K → IrrSmooth (GL (Fin 2) K)) : Prop :=
  ∀ P : TamePair K, ¬ Covered K P →
    σ P ∈ scClasses K ∧
    (∀ π : IrrRep (GL (Fin 2) K), IrrSmooth.mk π = σ P →
      π.1.HasCentralChar (P.ξ.comp (Units.map (algebraMap K P.L).toMonoidHom))) ∧
    (∀ (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) y,
      IrrSmooth.IsTwist y (σ P) (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ) →
        y = σ (P.twist χ hχ)) ∧
    ∀ y, IrrSmooth.IsContragredient y (σ P) → y = σ P.inv

/-- **Injectivity for the pairs that are not covered** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 20.2), as a property of a map $\sigma$. On the pairs that are not covered, $\sigma(P) = \sigma(Q)$ exactly when $P \cong Q$, and no representation in a class $\sigma(P)$ is isomorphic to the representation of a datum. -/
def UncoveredInjective (σ : TamePair K → IrrSmooth (GL (Fin 2) K)) : Prop :=
  (∀ P Q : TamePair K, ¬ Covered K P → ¬ Covered K Q → (σ P = σ Q ↔ P.Iso Q)) ∧
  ∀ P : TamePair K, ¬ Covered K P → ∀ π : IrrRep (GL (Fin 2) K), IrrSmooth.mk π = σ P →
    ∀ (Q : TamePair K) (D : TameDatum K Q.L Q.ξ), ¬ π.1.Iso D.rep

/-- **Exhaustion** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 15.5 and 15.8), as a property of a map $\sigma$. Each irreducible supercuspidal representation is isomorphic to the representation of a datum, or lies in a class $\sigma(P)$ for a pair $P$ that is not covered. -/
def Exhaustion (σ : TamePair K → IrrSmooth (GL (Fin 2) K)) : Prop :=
  ∀ π : IrrRep (GL (Fin 2) K), π.1.IsSupercuspidal (scalarGL K 2) →
    (∃ (Q : TamePair K) (D : TameDatum K Q.L Q.ξ), π.1.Iso D.rep) ∨
      ∃ P : TamePair K, ¬ Covered K P ∧ σ P = IrrSmooth.mk π

/-- **The pairs that are not covered** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 15.5, 15.8, 19.1, 19.3 and 20.2). Let $p \ne 2$. There is a map $\sigma$ with `UncoveredConstruction`, `UncoveredInjective` and `Exhaustion`: in Bushnell and Henniart, $\sigma(P) = \pi_\xi$. -/
def UncoveredParametrization : Prop :=
  (2 : 𝓀[K]) ≠ 0 → ∃ σ : TamePair K → IrrSmooth (GL (Fin 2) K),
    UncoveredConstruction K σ ∧ UncoveredInjective K σ ∧ Exhaustion K σ

/-- The published theorems on cuspidal types that the proof of `Langlands.LocalGL2.TameParametrizationGL2` uses. -/
structure TameTypeInputs : Prop where
  /-- Compact induction from a type is supercuspidal. -/
  supercuspidal : CIndSupercuspidal K
  /-- Cuspidal types determine the pair. -/
  injective : TypeRepInjective K
  /-- The representation does not depend on the choices. -/
  independent : TypeRepIndependent K
  /-- The contragredient of a type representation. -/
  contragredient : TypeRepContragredient K
  /-- The pairs that are not covered. -/
  uncovered : UncoveredParametrization K

variable {K}

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Two irreducible representations have the same class exactly when they are isomorphic. -/
theorem mk_eq_mk_iff_iso {π π' : IrrRep (GL (Fin 2) K)} :
    IrrSmooth.mk π = IrrSmooth.mk π' ↔ π.1.Iso π'.1 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

namespace TameDatum

variable {L : IntermediateField K (AlgebraicClosure K)} [Algebra.IsQuadraticExtension K L]
  {ξ : Lˣ →* ℂˣ}

/-- The representation of a datum is admissible and supercuspidal, given `CIndSupercuspidal`. -/
theorem isAdmissible_and_isSupercuspidal (hsc : CIndSupercuspidal K) (D : TameDatum K L ξ) :
    D.rep.IsAdmissible ∧ D.rep.IsSupercuspidal (scalarGL K 2) :=
  hsc D.J D.Λ (isOpen_jGroup D.hv _) D.isOpen_ker (isCompactModCenter_jGroup D.hv _)
    D.mem_of_intertwines

/-- The representation of a datum as an irreducible admissible representation. -/
noncomputable def irrRep (hsc : CIndSupercuspidal K) (D : TameDatum K L ξ) :
    IrrRep (GL (Fin 2) K) :=
  ⟨D.rep, D.isIrreducible, (D.isAdmissible_and_isSupercuspidal hsc).1⟩

end TameDatum

/-- A chosen pair with a datum that is isomorphic to a covered pair. -/
noncomputable def Covered.pair {P : TamePair K} (h : Covered K P) : TamePair K :=
  h.choose

/-- The chosen pair is isomorphic to the covered pair. -/
theorem Covered.pair_iso {P : TamePair K} (h : Covered K P) : h.pair.Iso P :=
  h.choose_spec.1

/-- A chosen datum for the chosen pair. -/
noncomputable def Covered.datum {P : TamePair K} (h : Covered K P) :
    TameDatum K h.pair.L h.pair.ξ :=
  h.choose_spec.2.some

open Classical in
/-- The map $P \mapsto \pi_P$: the class of $c\text{-}\mathrm{Ind}_{J}^{GL_2(K)} \Lambda$ for a chosen datum when $P$ is covered, and $\sigma(P)$ otherwise. -/
noncomputable def typeParam (hsc : CIndSupercuspidal K) (σ : TamePair K → IrrSmooth (GL (Fin 2) K))
    (P : TamePair K) : IrrSmooth (GL (Fin 2) K) :=
  if h : Covered K P then IrrSmooth.mk (h.datum.irrRep hsc) else σ P

variable {hsc : CIndSupercuspidal K} {σ : TamePair K → IrrSmooth (GL (Fin 2) K)}

/-- The value of `typeParam` at a covered pair. -/
theorem typeParam_of_covered {P : TamePair K} (h : Covered K P) :
    typeParam hsc σ P = IrrSmooth.mk (h.datum.irrRep hsc) := by
  simp [typeParam, h]

/-- The value of `typeParam` at a pair that is not covered. -/
theorem typeParam_of_not_covered {P : TamePair K} (h : ¬ Covered K P) :
    typeParam hsc σ P = σ P := by
  simp [typeParam, h]

/-- For a covered pair $P$, a representation lies in the class $\pi_P$ exactly when it is isomorphic to the representation of a datum for a pair isomorphic to $P$. -/
theorem mk_eq_typeParam_iff (hind : TypeRepIndependent K) (h2 : (2 : 𝓀[K]) ≠ 0)
    {P : TamePair K} (hc : Covered K P) (π : IrrRep (GL (Fin 2) K)) :
    IrrSmooth.mk π = typeParam hsc σ P ↔
      ∃ (Q : TamePair K) (D : TameDatum K Q.L Q.ξ), Q.Iso P ∧ π.1.Iso D.rep := by
  rw [typeParam_of_covered hc, mk_eq_mk_iff_iso]
  constructor
  · intro h
    exact ⟨hc.pair, hc.datum, hc.pair_iso, h⟩
  · rintro ⟨Q, D, hQ, hπ⟩
    exact hπ.trans (hind h2 Q hc.pair D hc.datum (hQ.trans hc.pair_iso.symm))

/-- A twist of a pair that is not covered is not covered. -/
theorem not_covered_twist {P : TamePair K} (hP : ¬ Covered K P) (χ : Kˣ →* ℂˣ)
    (hχ : IsSmoothChar K χ) : ¬ Covered K (P.twist χ hχ) := by
  rintro ⟨Q, hQ, ⟨D⟩⟩
  have hχ' := isSmoothChar_inv hχ
  exact hP ⟨Q.twist χ⁻¹ hχ', (hQ.twist χ⁻¹ hχ').trans (P.twist_twist_inv χ hχ hχ'),
    ⟨D.twist χ⁻¹ hχ'⟩⟩

/-- The inverse of a pair that is not covered is not covered, given `TypeRepContragredient`. -/
theorem not_covered_inv (hcon : TypeRepContragredient K) (h2 : (2 : 𝓀[K]) ≠ 0)
    {P : TamePair K} (hP : ¬ Covered K P) : ¬ Covered K P.inv := by
  rintro ⟨Q, hQ, ⟨D⟩⟩
  obtain ⟨D', -⟩ := hcon h2 Q D D.rep D.rep.contragredient (SmoothRep.Iso.refl _)
    (SmoothRep.Iso.refl _)
  exact hP ⟨Q.inv, hQ.inv.trans P.inv_inv, ⟨D'⟩⟩

/-- **The tame parametrization from cuspidal types** (Bushnell and Henniart, The local Langlands conjecture for GL(2), §§15 to 20). The published theorems in `Langlands.LocalGL2.TameTypeInputs` give `Langlands.LocalGL2.TameParametrizationGL2`, with $\pi_\xi = c\text{-}\mathrm{Ind}_{J}^{GL_2(K)} \Lambda$ for each covered pair. -/
theorem tameParametrizationGL2_of_inputs (I : TameTypeInputs K) : TameParametrizationGL2 K := by
  intro h2
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := I.uncovered h2
  have hsc := I.supercuspidal
  have key : ∀ {P : TamePair K} (hc : Covered K P) (π : IrrRep (GL (Fin 2) K)),
      IrrSmooth.mk π = typeParam hsc σ P ↔
        ∃ (Q : TamePair K) (D : TameDatum K Q.L Q.ξ), Q.Iso P ∧ π.1.Iso D.rep :=
    fun hc π => mk_eq_typeParam_iff I.independent h2 hc π
  refine ⟨typeParam hsc σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    by_cases hc : Covered K P
    · rw [typeParam_of_covered hc]
      exact ⟨_, rfl, (hc.datum.isAdmissible_and_isSupercuspidal hsc).2⟩
    · rw [typeParam_of_not_covered hc]
      exact (hσ1 P hc).1
  · rintro x ⟨π, rfl, hπ⟩
    rcases hσ3 π hπ with ⟨Q, D, hD⟩ | ⟨P, hP, hσP⟩
    · exact ⟨Q, ((key (covered_of_datum D) π).2 ⟨Q, D, TamePair.Iso.refl Q, hD⟩).symm⟩
    · exact ⟨P, (typeParam_of_not_covered hP).trans hσP⟩
  · intro P Q
    by_cases hP : Covered K P <;> by_cases hQ : Covered K Q
    · constructor
      · intro h
        obtain ⟨Q', D', hQ', hiso⟩ :=
          (key hQ (hP.datum.irrRep hsc)).1 ((typeParam_of_covered hP).symm.trans h)
        exact hP.pair_iso.symm.trans ((I.injective h2 _ _ hP.datum D' hiso).trans hQ')
      · intro h
        rw [typeParam_of_covered hP]
        exact (key hQ _).2 ⟨hP.pair, hP.datum, hP.pair_iso.trans h, SmoothRep.Iso.refl _⟩
    · constructor
      · intro h
        exact (hσ2.2 Q hQ (hP.datum.irrRep hsc)
          ((typeParam_of_covered hP).symm.trans (h.trans (typeParam_of_not_covered hQ)))
          hP.pair hP.datum (SmoothRep.Iso.refl _)).elim
      · intro h
        exact absurd (hP.of_iso h) hQ
    · constructor
      · intro h
        exact (hσ2.2 P hP (hQ.datum.irrRep hsc)
          ((typeParam_of_covered hQ).symm.trans (h.symm.trans (typeParam_of_not_covered hP)))
          hQ.pair hQ.datum (SmoothRep.Iso.refl _)).elim
      · intro h
        exact absurd (hQ.of_iso h.symm) hP
    · rw [typeParam_of_not_covered hP, typeParam_of_not_covered hQ]
      exact hσ2.1 P Q hP hQ
  · intro P π hπ
    by_cases hc : Covered K P
    · obtain ⟨Q, D, hQ, hiso⟩ := (key hc π).1 hπ
      have hD := D.hasCentralChar
      rw [hQ.comp_algebraMap] at hD
      exact SmoothRep.HasCentralChar.of_iso hiso hD
    · exact (hσ1 P hc).2.1 π (hπ.trans (typeParam_of_not_covered hc))
  · rintro P χ hχ y ⟨π, π', hπ, hπ', hiso⟩
    by_cases hc : Covered K P
    · obtain ⟨Q, D, hQ, hD⟩ := (key hc π).1 hπ
      have hc' : Covered K (P.twist χ hχ) := ⟨Q.twist χ hχ, hQ.twist χ hχ, ⟨D.twist χ hχ⟩⟩
      rw [← hπ']
      exact (key hc' π').2 ⟨Q.twist χ hχ, D.twist χ hχ, hQ.twist χ hχ,
        hiso.trans ((hD.twist _ _).trans (D.iso_twist χ hχ))⟩
    · rw [typeParam_of_not_covered (not_covered_twist hc χ hχ)]
      exact (hσ1 P hc).2.2.1 χ hχ y ⟨π, π', hπ.trans (typeParam_of_not_covered hc), hπ', hiso⟩
  · rintro P y ⟨π, π', hπ, hπ', hiso⟩
    by_cases hc : Covered K P
    · obtain ⟨Q, D, hQ, hD⟩ := (key hc π).1 hπ
      obtain ⟨D', hD'⟩ := I.contragredient h2 Q D π.1 π'.1 hD hiso
      have hc' : Covered K P.inv := ⟨Q.inv, hQ.inv, ⟨D'⟩⟩
      rw [← hπ']
      exact (key hc' π').2 ⟨Q.inv, D', hQ.inv, hD'⟩
    · rw [typeParam_of_not_covered (not_covered_inv I.contragredient h2 hc)]
      exact (hσ1 P hc).2.2.2 y ⟨π, π', hπ.trans (typeParam_of_not_covered hc), hπ', hiso⟩

/-- **The field `tame` of `Langlands.LocalGL2.GL2OddInputs`** comes from `Langlands.LocalGL2.TameTypeInputs`: the inputs on cuspidal types and the other five inputs give `Langlands.LocalGL2.GL2OddInputs`. -/
theorem gl2OddInputs_of_tameTypeInputs (art : Kˣ ≃ₜ* WeilGroup.Ab K) (I : TameTypeInputs K)
    (hartin : ArtinCompat K) (hgal : GaloisTameParametrization K) (hrect : Rectifier K)
    (hL : SupercuspidalLFactor K) (hns : NonSupercuspidalLLC K art) : GL2OddInputs K art :=
  ⟨hartin, tameParametrizationGL2_of_inputs I, hgal, hrect, hL, hns⟩

end Inputs

end Langlands.LocalGL2
