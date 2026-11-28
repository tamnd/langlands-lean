/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2PrincipalSeriesInputs

/-!
# The contragredient of the principal series

Let $K$ be a nonarchimedean local field and let $\chi_1, \chi_2$ be smooth characters of $K^\times$. This file proves `Langlands.LocalGL2.PSContragredientIso K`: the contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is isomorphic to $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$.

## Main definitions

* `Langlands.LocalGL2.pcHaar`: the Haar measure of mass $1$ on a compact group.
* `Langlands.LocalGL2.pcInt`: the integral $\Lambda(\varphi) = \int_{GL_2(\mathcal{O}_K)} \varphi(k) \, dk$.
* `Langlands.LocalGL2.PcIsDelta`: the functions of modulus type, that is $\varphi(bg) = |a/d| \varphi(g)$ for $b \in B$, with $\varphi$ invariant on the right under an open subgroup.
* `Langlands.LocalGL2.PcIntInvariant`: the statement that $\Lambda$ is invariant under right translation on the functions of modulus type.
* `Langlands.LocalGL2.pcPair`: the pairing $\langle f, f' \rangle = \Lambda(f f')$ of $\mathrm{Ind}(\chi_1, \chi_2)$ and $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$.
* `Langlands.LocalGL2.pcIwahori`: the Iwahori subgroup $I$ of $GL_2(\mathcal{O}_K)$.
* `Langlands.LocalGL2.pcEta`: the element $\eta = \begin{pmatrix} 0 & 1 \\ \varpi & 0 \end{pmatrix}$, which normalizes $I$.
* `Langlands.LocalGL2.pcIwInt`: the integral over $I$.
* `Langlands.LocalGL2.pcInvSubgroup`: the subgroup of the elements that preserve $\Lambda$.

## Main results

* `Langlands.LocalGL2.pcIso_contragredient_of_pairing`: a nondegenerate invariant pairing of two admissible representations gives an isomorphism of one with the contragredient of the other.
* `Langlands.LocalGL2.pcNondeg`: the pairing is nondegenerate if $\Lambda$ is invariant.
* `Langlands.LocalGL2.pcContragredientIso_of_invariant`: `PcIntInvariant K` implies `PSContragredientIso K`.
* `Langlands.LocalGL2.pcInt_decomp`: the decomposition formula $\Lambda(\varphi) = \mu(I) \left(\int_I \varphi + q \int_I \varphi(w \, \cdot)\right)$.
* `Langlands.LocalGL2.pcInt_eta`: $\Lambda$ is invariant under $\eta$.
* `Langlands.LocalGL2.pcIntInvariant_holds`: `PcIntInvariant K`.
* `Langlands.LocalGL2.psContragredientIso_holds`: `PSContragredientIso K`.

## Proof

The pairing $\langle f, f' \rangle = \int_{GL_2(\mathcal{O}_K)} f(k) f'(k) \, dk$ is nondegenerate, because a vector of the principal series is determined by its values on $GL_2(\mathcal{O}_K)$. Both representations are admissible, so a nondegenerate invariant pairing identifies $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$ with the contragredient. The product $f f'$ is of modulus type, so the invariance of the pairing is the invariance of $\Lambda$ on the functions of modulus type.

The elements that preserve $\Lambda$ form a subgroup $H$. It contains $GL_2(\mathcal{O}_K)$ by the invariance of the Haar measure, and it contains the center. The group $GL_2(\mathcal{O}_K)$ is the union of the $q + 1$ cosets $w I$ and $n^-(s(r)) I$ for $r$ in the residue field. This gives the decomposition formula. Conjugation by $\eta$ preserves $I$, and $\eta w$ and $w \eta$ are diagonal. With the decomposition formula, it follows that $\eta \in H$. Thus $\mathrm{diag}(\varpi, 1) = w \eta \in H$, so each $\mathrm{diag}(x, 1)$ and each $n(y)$ are in $H$, and $B \subseteq H$. The Iwasawa decomposition $G = B \, GL_2(\mathcal{O}_K)$ then gives $H = G$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), chapter 1, section 3.
-/

namespace Langlands

universe u

open MeasureTheory Topology Filter

namespace LocalGL2

section Haar

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

variable (H) in
/-- The Haar measure of total mass $1$ on a compact group. -/
noncomputable def pcHaar : Measure H :=
  Measure.haarMeasure ⊤

/-- The measure `pcHaar H` is a Haar measure. -/
instance : (pcHaar H).IsHaarMeasure := by
  unfold pcHaar; infer_instance

/-- The measure `pcHaar H` has total mass $1$. -/
instance : IsProbabilityMeasure (pcHaar H) := by
  constructor
  unfold pcHaar
  rw [← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]

/-- A finite left invariant measure on a compact group is a multiple of the Haar measure of mass $1$. -/
theorem pcHaar_unique (ν : Measure H) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] :
    ν = ν Set.univ • pcHaar H := by
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • pcHaar H :=
    ⟨_, Measure.isMulInvariant_eq_smul_of_compactSpace ν (pcHaar H)⟩
  subst hc
  ext s hs
  simp only [Measure.smul_apply]
  rw [measure_univ (μ := pcHaar H), smul_one_smul]

/-- The Haar measure of mass $1$ on a compact group is invariant under right translations. -/
theorem pcHaar_map_mul_right (k : H) : (pcHaar H).map (· * k) = pcHaar H := by
  have : IsFiniteMeasure ((pcHaar H).map (· * k)) := inferInstance
  rw [pcHaar_unique ((pcHaar H).map (· * k)),
    Measure.map_apply (measurable_mul_const k) MeasurableSet.univ]
  simp

/-- Right translation does not change the integral for the Haar measure of mass $1$. -/
theorem integral_pcHaar_mul_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : H → E) (k : H) : ∫ x, f (x * k) ∂pcHaar H = ∫ x, f x ∂pcHaar H := by
  conv_rhs => rw [← pcHaar_map_mul_right k]
  have hk : MeasurableEmbedding (fun x : H => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  rw [hk.integral_map]

/-- Left translation does not change the integral for the Haar measure of mass $1$. -/
theorem integral_pcHaar_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : H → E) (k : H) : ∫ x, f (k * x) ∂pcHaar H = ∫ x, f x ∂pcHaar H :=
  integral_mul_left_eq_self f k

/-- A continuous automorphism does not change the integral for the Haar measure of mass $1$. -/
theorem integral_pcHaar_mulEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : H ≃* H) (he : Continuous e) (he' : Continuous e.symm) (f : H → E) :
    ∫ x, f (e x) ∂pcHaar H = ∫ x, f x ∂pcHaar H := by
  let e' : H ≃ₜ H := ⟨e.toEquiv, he, he'⟩
  have hm : (pcHaar H).map e = pcHaar H := by
    have : ((pcHaar H).map e).IsMulLeftInvariant :=
      isMulLeftInvariant_map e.toMonoidHom.toMulHom he.measurable e.surjective
    rw [pcHaar_unique ((pcHaar H).map e), Measure.map_apply he.measurable MeasurableSet.univ]
    simp
  conv_rhs => rw [← hm]
  have he2 : MeasurableEmbedding e := e'.toMeasurableEquiv.measurableEmbedding
  rw [he2.integral_map]

/-- For an open subgroup $J$ of a compact group $H$, the integral over $J$ for the Haar measure of $H$ is $\mu_H(J)$ times the integral for the Haar measure of $J$. -/
theorem integral_indicator_pcHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Subgroup H) (hJ : IsOpen (J : Set H)) (f : H → E) :
    have : CompactSpace J := isCompact_iff_compactSpace.mp
      (J.isClosed_of_isOpen hJ).isCompact
    ∫ x, (J : Set H).indicator f x ∂pcHaar H =
      (pcHaar H (J : Set H)).toReal • ∫ j : J, f j ∂pcHaar J := by
  intro
  have hm : MeasurableSet (J : Set H) := hJ.measurableSet
  let ν : Measure J := Measure.comap Subtype.val (pcHaar H)
  have hν : ∀ s : Set J, ν s = pcHaar H (Subtype.val '' s) := fun s =>
    (MeasurableEmbedding.subtype_coe hm).comap_apply _ s
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact measure_lt_top _ _⟩
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun j => Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (measurable_const_mul j) hs, hν, hν]
    have e : Subtype.val '' ((fun x => j * x) ⁻¹' s) =
        (fun x : H => (j : H) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨j * y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have hx : x ∈ J := by
          have : x = (j : H)⁻¹ * y := by rw [hxy]; group
          rw [this]
          exact J.mul_mem (J.inv_mem j.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have : j * ⟨x, hx⟩ = y := Subtype.ext hxy.symm
        rw [this]
        exact hy
    rw [e, measure_preimage_mul]
  rw [integral_indicator hm, ← integral_subtype_comap hm]
  change ∫ x : J, f x ∂ν = _
  rw [pcHaar_unique ν, integral_smul_measure, hν, Set.image_univ, Subtype.range_coe]

end Haar

section Pairing

open SmoothRep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The average of a vector over a compact open subgroup. For a smooth representation $\pi$, a compact open subgroup $U$ and a vector $v$, there is a vector $w$ fixed by $U$ with $D(w) = D(v)$ for each linear form $D$ that is invariant under $U$. The vector $w$ is the mean of the finitely many vectors $\pi(u) v$ for $u \in U$. -/
theorem pcExists_fixed_avg (π : SmoothRep G) {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (v : π.V) : ∃ w ∈ fixedVectors π.ρ U, ∀ D : Module.Dual ℂ π.V,
      (∀ u ∈ U, ∀ x, D (π.ρ u x) = D x) → D w = D v := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  let S : Subgroup U := (vecStabilizer π.ρ v).subgroupOf U
  have hS : IsOpen (S : Set U) := Subgroup.subgroupOf_isOpen U _ (π.smooth v)
  have : Finite (U ⧸ S) := S.quotient_finite_of_isOpen hS
  have : Fintype (U ⧸ S) := Fintype.ofFinite _
  let F : U ⧸ S → π.V := fun x => π.ρ (x.out : G) v
  have hF0 : ∀ z : U, F (z : U ⧸ S) = π.ρ (z : G) v := by
    intro z
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S z
    have h2 : π.ρ ((h : U) : G) v = v := Subgroup.mem_subgroupOf.1 h.2
    change π.ρ (((z : U ⧸ S).out : U) : G) v = _
    rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h2]
  have hF : ∀ (u : U) (x : U ⧸ S), F (u • x) = π.ρ (u : G) (F x) := by
    intro u x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [MulAction.Quotient.smul_mk, hF0, hF0, smul_eq_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  refine ⟨(Fintype.card (U ⧸ S) : ℂ)⁻¹ • ∑ x, F x, fun g hg => ?_, fun D hD => ?_⟩
  · rw [map_smul, map_sum]
    congr 1
    let u : U := ⟨g, hg⟩
    have := Fintype.sum_equiv (MulAction.toPerm u : Equiv.Perm (U ⧸ S)) (fun x => F (u • x))
      F (fun x => rfl)
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => (hF u x).symm
  · have hc : (Fintype.card (U ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [map_smul, map_sum]
    have : ∀ x, D (F x) = D v := fun x => hD _ (x.out).2 v
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    field_simp

/-- **A perfect invariant pairing gives the contragredient.** Let $\pi$ and $\pi'$ be admissible smooth representations of $G$, and let each open subgroup of $G$ contain a compact open subgroup. Let $P$ be a $G$-invariant bilinear pairing of $\pi$ and $\pi'$ that is nondegenerate on both sides. Then $w \mapsto P(\cdot, w)$ is an isomorphism of $\pi'$ onto the contragredient of $\pi$. The proof restricts $P$ to the finite dimensional spaces of vectors fixed by a compact open subgroup $U$, where it is perfect. -/
theorem pcIso_contragredient_of_pairing (π π' : SmoothRep G)
    (hcomp : ∀ H : Subgroup G, IsOpen (H : Set G) →
      ∃ U : Subgroup G, U ≤ H ∧ IsOpen (U : Set G) ∧ IsCompact (U : Set G))
    (hπ : π.IsAdmissible) (hπ' : π'.IsAdmissible)
    (P : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hP : ∀ g v w, P (π.ρ g v) (π'.ρ g w) = P v w)
    (hl : ∀ w, w ≠ 0 → ∃ v, P v w ≠ 0) (hr : ∀ v, v ≠ 0 → ∃ w, P v w ≠ 0) :
    π'.Iso π.contragredient := by
  have hinv : ∀ g (w : π'.V), π'.ρ g w = w → ∀ x, P (π.ρ g x) w = P x w := by
    intro g w hw x
    conv_lhs => rw [← hw]
    exact hP g x w
  have hinv' : ∀ g (v : π.V), π.ρ g v = v → ∀ y, P v (π'.ρ g y) = P v y := by
    intro g v hv y
    conv_lhs => rw [← hv]
    exact hP g v y
  have hgi : ∀ g (w : π'.V), π'.ρ g w = w → π'.ρ g⁻¹ w = w := by
    intro g w hw
    conv_lhs => rw [← hw]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let Φ : π'.V →ₗ[ℂ] π.contragredient.V :=
    { toFun := fun w => ⟨P.flip w, by
        refine Subgroup.isOpen_mono (H₁ := vecStabilizer π'.ρ w) (fun g hg => ?_) (π'.smooth w)
        rw [mem_vecStabilizer] at hg ⊢
        refine LinearMap.ext fun x => ?_
        rw [Representation.dual_apply]
        exact hinv g⁻¹ w (hgi g w hg) x⟩
      map_add' := fun a b => Subtype.ext (by exact map_add P.flip a b)
      map_smul' := fun c a => Subtype.ext (by exact map_smul P.flip c a) }
  have hΦ : ∀ w x, (show smoothVectors π.ρ.dual from Φ w).1 x = P x w := fun _ _ => rfl
  -- the perfect pairing on the fixed vectors
  have key : ∀ U : Subgroup G, IsOpen (U : Set G) → IsCompact (U : Set G) →
      Function.Surjective ((P.compl₁₂ (fixedVectors π.ρ U).subtype
        (fixedVectors π'.ρ U).subtype).flip) := by
    intro U hUo hUc
    have : FiniteDimensional ℂ (fixedVectors π.ρ U) := hπ U hUo
    have : FiniteDimensional ℂ (fixedVectors π'.ρ U) := hπ' U hUo
    have inj1 : Function.Injective ((P.compl₁₂ (fixedVectors π.ρ U).subtype
        (fixedVectors π'.ρ U).subtype).flip) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      by_contra hne
      have hne' : (w : π'.V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨x, hx⟩ := hl w hne'
      obtain ⟨v, hv, hvx⟩ := pcExists_fixed_avg π hUc x
      have := hvx (P.flip w) fun u hu y => hinv u w (w.2 u hu) y
      have h0 := LinearMap.congr_fun hw ⟨v, hv⟩
      simp only [LinearMap.flip_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
        LinearMap.zero_apply] at h0 this
      exact hx (this ▸ h0)
    have inj2 : Function.Injective (P.compl₁₂ (fixedVectors π.ρ U).subtype
        (fixedVectors π'.ρ U).subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      by_contra hne
      have hne' : (v : π.V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨y, hy⟩ := hr v hne'
      obtain ⟨w, hw, hwy⟩ := pcExists_fixed_avg π' hUc y
      have := hwy (P v) fun u hu z => hinv' u v (v.2 u hu) z
      have h0 := LinearMap.congr_fun hv ⟨w, hw⟩
      simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, LinearMap.zero_apply] at h0
      exact hy (this ▸ h0)
    have h1 := LinearMap.finrank_le_finrank_of_injective inj1
    have h2 := LinearMap.finrank_le_finrank_of_injective inj2
    rw [Subspace.dual_finrank_eq] at h2
    have heq := le_antisymm h1 (by rw [Subspace.dual_finrank_eq]; exact h2)
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 inj1
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    obtain ⟨x, hx⟩ := hl w hne
    have := congrArg (fun l : π.contragredient.V =>
      (show smoothVectors π.ρ.dual from l).1 x) hw
    exact hx this
  have hsurj : Function.Surjective Φ := by
    rintro ⟨l, hl'⟩
    obtain ⟨U, hUH, hUo, hUc⟩ := hcomp _ hl'
    have hlU : ∀ u ∈ U, ∀ x, l (π.ρ u x) = l x := by
      intro u hu x
      have h := LinearMap.congr_fun ((mem_vecStabilizer _ _ _).1 (hUH (U.inv_mem hu))) x
      rw [Representation.dual_apply, inv_inv] at h
      exact h
    obtain ⟨w, hw⟩ := key U hUo hUc (l ∘ₗ (fixedVectors π.ρ U).subtype)
    refine ⟨w, Subtype.ext (LinearMap.ext fun x => ?_)⟩
    obtain ⟨v, hv, hvx⟩ := pcExists_fixed_avg π hUc x
    have e1 := hvx (P.flip w) fun u hu y => hinv u w (w.2 u hu) y
    have e2 := hvx l hlU
    have e3 := LinearMap.congr_fun hw ⟨v, hv⟩
    simp only [LinearMap.flip_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
      LinearMap.coe_comp, Function.comp_apply] at e1 e3
    rw [hΦ, ← e1, e3, e2]
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun g w => Subtype.ext (LinearMap.ext fun x => ?_)⟩
  change P x (π'.ρ g w) = P (π.ρ g⁻¹ x) w
  rw [← hP g⁻¹ x (π'.ρ g w), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

end Pairing

section GL2Pairing

open GL2 SmoothRep

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The Borel $\sigma$-algebra on $GL_2(\mathcal{O}_K)$. -/
noncomputable instance pcMeas : MeasurableSpace (maxCompact K) :=
  borel _

/-- The $\sigma$-algebra `pcMeas` is the Borel $\sigma$-algebra. -/
instance pcBorel : BorelSpace (maxCompact K) :=
  ⟨rfl⟩

/-- The group $GL_2(\mathcal{O}_K)$ is a compact space. -/
instance pcCompact : CompactSpace (maxCompact K) :=
  isCompact_iff_compactSpace.mp isCompact_maxCompact

variable (K) in
/-- The integral $\Lambda(\varphi) = \int_{GL_2(\mathcal{O}_K)} \varphi(k) \, dk$ for the Haar measure of mass $1$ on $GL_2(\mathcal{O}_K)$. -/
noncomputable def pcInt (φ : GL (Fin 2) K → ℂ) : ℂ :=
  ∫ k : maxCompact K, φ k ∂pcHaar (maxCompact K)

variable (K) in
/-- A function $\varphi$ on $GL_2(K)$ is of modulus type if $\varphi(bg) = |a/d| \varphi(g)$ for each $b \in B$ with diagonal $(a, d)$, and $\varphi$ is invariant on the right under an open subgroup. The product of a vector of $\mathrm{Ind}(\chi_1, \chi_2)$ and a vector of $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$ is of this type. -/
def PcIsDelta (φ : GL (Fin 2) K → ℂ) : Prop :=
  (∀ b g : GL (Fin 2) K, b.1 1 0 = 0 →
    φ (b * g) = (normAbs K (b.1 0 0 / b.1 1 1) : ℂ) * φ g) ∧
  ∃ U : Subgroup (GL (Fin 2) K), IsOpen (U : Set (GL (Fin 2) K)) ∧ ∀ g, ∀ u ∈ U, φ (g * u) = φ g

variable (K) in
/-- **The invariance of the integral over $GL_2(\mathcal{O}_K)$.** For each function $\varphi$ of modulus type and each $g \in GL_2(K)$, $\int_{GL_2(\mathcal{O}_K)} \varphi(kg) \, dk = \int_{GL_2(\mathcal{O}_K)} \varphi(k) \, dk$. This is the statement that $\Lambda$ is a $G$-invariant linear form on $\mathrm{Ind}_B^G(\delta_B)$ (Bushnell and Henniart, Chapter 1, Section 3.5). -/
def PcIntInvariant : Prop :=
  ∀ φ : GL (Fin 2) K → ℂ, PcIsDelta K φ → ∀ g, pcInt K (fun x => φ (x * g)) = pcInt K φ

/-- A function on $GL_2(K)$ that is invariant on the right under an open subgroup is continuous. -/
theorem pcContinuous_of_right {φ : GL (Fin 2) K → ℂ} {U : Subgroup (GL (Fin 2) K)}
    (hU : IsOpen (U : Set (GL (Fin 2) K))) (hφ : ∀ g, ∀ u ∈ U, φ (g * u) = φ g) :
    Continuous φ := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hopen : IsOpen {x : GL (Fin 2) K | g⁻¹ * x ∈ U} :=
    hU.preimage (continuous_const.mul continuous_id)
  have hmem : g ∈ {x : GL (Fin 2) K | g⁻¹ * x ∈ U} := by
    simp only [Set.mem_ofPred_eq, inv_mul_cancel]
    exact U.one_mem
  refine (continuousAt_const (y := φ g)).congr
    (Filter.eventually_of_mem (hopen.mem_nhds hmem) fun x hx => ?_)
  have := hφ g _ hx
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- The integral $\Lambda$ is additive on functions that are invariant on the right under open subgroups. -/
theorem pcInt_add {φ ψ : GL (Fin 2) K → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    pcInt K (fun x => φ x + ψ x) = pcInt K φ + pcInt K ψ := by
  have hi : ∀ χ : GL (Fin 2) K → ℂ, Continuous χ →
      Integrable (fun k : maxCompact K => χ k) (pcHaar (maxCompact K)) := fun χ hχ =>
    (hχ.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_add (hi φ hφ) (hi ψ hψ)

/-- The integral $\Lambda$ is homogeneous. -/
theorem pcInt_smul (c : ℂ) (φ : GL (Fin 2) K → ℂ) :
    pcInt K (fun x => c * φ x) = c * pcInt K φ :=
  integral_const_mul c _

/-- A vector of $\mathrm{Ind}(\alpha_1, \alpha_2)$ is continuous. -/
theorem pcContinuous_ps {α₁ α₂ : Kˣ →* ℂˣ} (f : principalSeriesSpace K α₁ α₂) :
    Continuous (f : GL (Fin 2) K → ℂ) := by
  obtain ⟨U, hU, hfU⟩ := f.2.2
  exact pcContinuous_of_right hU hfU

/-- An element of $B \cap GL_2(\mathcal{O}_K)$ has $|a/d| = 1$. -/
theorem pcNormAbs_of_mem {b : GL (Fin 2) K} (hb : b.1 1 0 = 0) (hk : b ∈ maxCompact K) :
    normAbs K (b.1 0 0 / b.1 1 1) = 1 := by
  have ha := val_zero_zero_ne_zero ((mem_borel b).2 hb)
  have hd := val_one_one_ne_zero ((mem_borel b).2 hb)
  have hinv : ∀ i, (b⁻¹).1 i i = (b.1 i i)⁻¹ := by
    intro i
    rw [val_inv]
    fin_cases i <;> simp [Matrix.det_fin_two, hb] <;> field_simp
  have hv : ∀ i, ValuativeRel.valuation K (b.1 i i) = 1 := by
    intro i
    have h1 := hk.1 i i
    have h2 := hk.2 i i
    rw [hinv i, map_inv₀] at h2
    have hne : ValuativeRel.valuation K (b.1 i i) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      fin_cases i
      · exact ha
      · exact hd
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)
  rw [normAbs_div, normAbs_eq_one (hv 0), normAbs_eq_one (hv 1), div_one]

/-- The product of a vector of $\mathrm{Ind}(\alpha_1, \alpha_2)$ and a vector of $\mathrm{Ind}(\beta_1, \beta_2)$ is of modulus type when $\alpha_i \beta_i = 1$. -/
theorem pcIsDelta_mul {α₁ α₂ β₁ β₂ : Kˣ →* ℂˣ} (h₁ : ∀ a, (α₁ a : ℂ) * β₁ a = 1)
    (h₂ : ∀ a, (α₂ a : ℂ) * β₂ a = 1) (f : principalSeriesSpace K α₁ α₂)
    (f' : principalSeriesSpace K β₁ β₂) :
    PcIsDelta K (fun x => (f : GL (Fin 2) K → ℂ) x * (f' : GL (Fin 2) K → ℂ) x) := by
  refine ⟨fun b g hb => ?_, ?_⟩
  · have ha := val_zero_zero_ne_zero ((mem_borel b).2 hb)
    have hd := val_one_one_ne_zero ((mem_borel b).2 hb)
    show f.1 (b * g) * f'.1 (b * g) = _ * (f.1 g * f'.1 g)
    rw [f.2.1 b g (Units.mk0 _ ha) (Units.mk0 _ hd) hb rfl rfl,
      f'.2.1 b g (Units.mk0 _ ha) (Units.mk0 _ hd) hb rfl rfl]
    have e := Real.mul_self_sqrt (normAbs_nonneg (b.1 0 0 / b.1 1 1))
    have e' : ((Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ)) *
        (Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ) = (normAbs K (b.1 0 0 / b.1 1 1) : ℂ) := by
      rw [← Complex.ofReal_mul, e]
    have k1 := h₁ (Units.mk0 _ ha)
    have k2 := h₂ (Units.mk0 _ hd)
    simp only [Units.val_mk0] at e' ⊢
    linear_combination (f.1 g * f'.1 g * ((α₂ (Units.mk0 _ hd) : ℂ) * β₂ (Units.mk0 _ hd)) *
      ((Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ) *
        (Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ))) * k1 +
      (f.1 g * f'.1 g * ((Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ) *
        (Real.sqrt (normAbs K (b.1 0 0 / b.1 1 1)) : ℂ))) * k2 + (f.1 g * f'.1 g) * e'
  · obtain ⟨U, hU, hfU⟩ := f.2.2
    obtain ⟨U', hU', hfU'⟩ := f'.2.2
    exact ⟨U ⊓ U', hU.inter hU', fun g u hu => by
      simp only [hfU g u (Subgroup.mem_inf.1 hu).1, hfU' g u (Subgroup.mem_inf.1 hu).2]⟩


/-- **Nondegeneracy of the pairing.** Assume `PcIntInvariant K`. Let $\alpha_1, \alpha_2$ be smooth and let $\alpha_i \beta_i = 1$. For each nonzero vector $f$ of $\mathrm{Ind}(\beta_1, \beta_2)$ there is a vector $f''$ of $\mathrm{Ind}(\alpha_1, \alpha_2)$ with $\Lambda(f'' f) \ne 0$. The proof translates $f$ so that $f(1) \ne 0$. Then it takes for $f''$ the function with support $BU$ and $f''(bu) = \alpha_1(a)\alpha_2(d)|a/d|^{1/2}$, for a small compact open subgroup $U$. On $GL_2(\mathcal{O}_K)$ the product $f'' f$ is $f(1)$ times the indicator function of an open set that is not empty. -/
theorem pcNondeg (hI : PcIntInvariant K) {α₁ α₂ β₁ β₂ : Kˣ →* ℂˣ} (hα₁ : IsSmoothChar K α₁)
    (hα₂ : IsSmoothChar K α₂) (h₁ : ∀ a, (α₁ a : ℂ) * β₁ a = 1)
    (h₂ : ∀ a, (α₂ a : ℂ) * β₂ a = 1) (f : principalSeriesSpace K β₁ β₂) (hf : f ≠ 0) :
    ∃ f'' : principalSeriesSpace K α₁ α₂,
      pcInt K (fun x => (f'' : GL (Fin 2) K → ℂ) x * (f : GL (Fin 2) K → ℂ) x) ≠ 0 := by
  classical
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f.1 g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  let f₁ : principalSeriesSpace K β₁ β₂ := (principalSeries K β₁ β₂).ρ g₀ f
  have hf₁ : ∀ x, f₁.1 x = f.1 (x * g₀) := fun _ => rfl
  obtain ⟨U₀, hU₀, hf₁U⟩ := f₁.2.2
  let θ : borel K →* ℂˣ := borelChar α₁ α₂ * sqrtModulus K
  obtain ⟨γ, hγ0, hγ1, hθγ⟩ := exists_congruence_borelChar (hα₁.mul isSmoothChar_sqrtAbsChar)
    (hα₂.mul isSmoothChar_sqrtAbsChar.inv)
  rw [← borelChar_mul_sqrtModulus] at hθγ
  let U : Subgroup (GL (Fin 2) K) := U₀ ⊓ congruence K γ hγ0 hγ1
  have hUo : IsOpen (U : Set (GL (Fin 2) K)) := by
    rw [Subgroup.coe_inf]; exact hU₀.inter (isOpen_congruence _ _ _)
  have hUK : U ≤ maxCompact K := inf_le_right.trans (congruence_le_maxCompact hγ0 hγ1)
  have hθU : ∀ b : borel K, (b : GL (Fin 2) K) ∈ U → θ b = 1 := fun b hb =>
    hθγ b (Subgroup.mem_inf.1 hb).2
  let P : GL (Fin 2) K → Prop := fun g => ∃ b : borel K, (b : GL (Fin 2) K)⁻¹ * g ∈ U
  let F : GL (Fin 2) K → ℂ := fun g => if h : P g then (θ h.choose : ℂ) else 0
  have key : ∀ (b : borel K) (g : GL (Fin 2) K), (b : GL (Fin 2) K)⁻¹ * g ∈ U →
      F g = (θ b : ℂ) := by
    intro b g hb
    have h : P g := ⟨b, hb⟩
    simp only [F, dite_eq_left h]
    have hc := h.choose_spec
    have hm : ((b⁻¹ * h.choose : borel K) : GL (Fin 2) K) =
        ((b : GL (Fin 2) K)⁻¹ * g) * (((h.choose : borel K) : GL (Fin 2) K)⁻¹ * g)⁻¹ := by
      simp [mul_assoc]
    have h1 : θ (b⁻¹ * h.choose) = 1 := hθU _ (by rw [hm]; exact U.mul_mem hb (U.inv_mem hc))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
  have zero : ∀ g, ¬ P g → F g = 0 := fun g h => dite_eq_right h
  have hθb : ∀ (b : GL (Fin 2) K) (hb : b.1 1 0 = 0) (a d : Kˣ), b.1 0 0 = a → b.1 1 1 = d →
      (θ ⟨b, (mem_borel b).2 hb⟩ : ℂ) =
        (α₁ a : ℂ) * α₂ d * (Real.sqrt (normAbs K ((a : K) / d)) : ℂ) := by
    intro b hb a d ha hd
    have ea : diagFst (⟨b, (mem_borel b).2 hb⟩ : borel K) = a := Units.ext (by rw [val_diagFst]; exact ha)
    have ed : diagSnd (⟨b, (mem_borel b).2 hb⟩ : borel K) = d := Units.ext (by rw [val_diagSnd]; exact hd)
    simp only [θ, MonoidHom.mul_apply, Units.val_mul, borelChar_apply, sqrtModulus_apply, ea, ed]
    rw [← ha, ← hd]
  have hF : F ∈ principalSeriesSpace K α₁ α₂ := by
    refine ⟨fun b g a d hb ha hd => ?_, U, hUo, fun g u hu => ?_⟩
    · rw [← hθb b hb a d ha hd]
      by_cases hg : P g
      · obtain ⟨c, hc⟩ := hg
        rw [key c g hc, key (⟨b, (mem_borel b).2 hb⟩ * c) (b * g) (by simpa [mul_assoc] using hc),
          map_mul, Units.val_mul]
      · have : ¬ P (b * g) := by
          rintro ⟨c, hc⟩
          exact hg ⟨⟨b, (mem_borel b).2 hb⟩⁻¹ * c, by simpa [mul_assoc] using hc⟩
        rw [zero _ hg, zero _ this, mul_zero]
    · by_cases hg : P g
      · obtain ⟨c, hc⟩ := hg
        rw [key c g hc, key c (g * u) (by rw [← mul_assoc]; exact U.mul_mem hc hu)]
      · have : ¬ P (g * u) := by
          rintro ⟨c, hc⟩
          refine hg ⟨c, ?_⟩
          have := U.mul_mem hc (U.inv_mem hu)
          simpa [mul_assoc] using this
        rw [zero _ hg, zero _ this]
  let Fv : principalSeriesSpace K α₁ α₂ := ⟨F, hF⟩
  -- the product of `F` and `f₁` on `GL_2(O)`
  let S : Set (maxCompact K) := {k | P k}
  have hS : IsOpen S := by
    have : IsOpen {g : GL (Fin 2) K | P g} := by
      have : {g : GL (Fin 2) K | P g} = ⋃ b : borel K, (fun g => (b : GL (Fin 2) K)⁻¹ * g) ⁻¹' U := by
        ext g; simp [P]
      rw [this]
      exact isOpen_iUnion fun b => hUo.preimage (continuous_const.mul continuous_id)
    exact this.preimage continuous_subtype_val
  have h1S : (1 : maxCompact K) ∈ S := ⟨1, by simp⟩
  have hprod : ∀ k : maxCompact K, F k * f₁.1 k = S.indicator (fun _ => f₁.1 1) k := by
    intro k
    by_cases hk : P k
    · obtain ⟨b, hb⟩ := hk
      rw [Set.indicator_of_mem (show k ∈ S from ⟨b, hb⟩)]
      have hbK : (b : GL (Fin 2) K) ∈ maxCompact K := by
        have : (b : GL (Fin 2) K) = k * ((b : GL (Fin 2) K)⁻¹ * k)⁻¹ := by group
        rw [this]
        exact (maxCompact K).mul_mem k.2 ((maxCompact K).inv_mem (hUK hb))
      have e : (k : GL (Fin 2) K) = b * ((b : GL (Fin 2) K)⁻¹ * k) := by group
      have h3 : F k * f₁.1 k = ((normAbs K ((b : GL (Fin 2) K).1 0 0 /
          (b : GL (Fin 2) K).1 1 1) : ℝ) : ℂ) *
          (F ((b : GL (Fin 2) K)⁻¹ * k) * f₁.1 ((b : GL (Fin 2) K)⁻¹ * k)) := by
        have := (pcIsDelta_mul h₁ h₂ Fv f₁).1 b ((b : GL (Fin 2) K)⁻¹ * k) b.2
        rw [← e] at this
        exact this
      rw [h3, pcNormAbs_of_mem b.2 hbK, Complex.ofReal_one, one_mul, key 1 _ (by simpa using hb), map_one, Units.val_one, one_mul]
      have := hf₁U 1 _ (inf_le_left (a := U₀) hb)
      rwa [one_mul] at this
    · rw [Set.indicator_of_notMem (show k ∉ S from hk), zero _ hk, zero_mul]
  have hval : pcInt K (fun x => F x * f₁.1 x) ≠ 0 := by
    unfold pcInt
    simp_rw [hprod]
    rw [integral_indicator_const _ hS.measurableSet, Complex.real_smul]
    refine mul_ne_zero ?_ (by rw [hf₁, one_mul]; exact hg₀)
    have hpos := hS.measure_pos (pcHaar (maxCompact K)) ⟨1, h1S⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)).ne'
  refine ⟨(principalSeries K α₁ α₂).ρ g₀⁻¹ Fv, ?_⟩
  have := hI _ (pcIsDelta_mul h₁ h₂ ((principalSeries K α₁ α₂).ρ g₀⁻¹ Fv) f) g₀
  rw [← this]
  convert hval using 3 with x
  change F (x * g₀ * g₀⁻¹) * f.1 (x * g₀) = F x * f.1 (x * g₀)
  rw [mul_inv_cancel_right]

/-- The pairing $\langle f, f' \rangle = \int_{GL_2(\mathcal{O}_K)} f(k) f'(k) \, dk$ of $\mathrm{Ind}(\chi_1, \chi_2)$ and $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$. -/
noncomputable def pcPair (χ₁ χ₂ : Kˣ →* ℂˣ) :
    principalSeriesSpace K χ₁ χ₂ →ₗ[ℂ] principalSeriesSpace K χ₁⁻¹ χ₂⁻¹ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => pcInt K (fun x => (f : GL (Fin 2) K → ℂ) x *
      (f' : GL (Fin 2) K → ℂ) x))
    (fun f₁ f₂ f' => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact pcInt_add ((pcContinuous_ps f₁).mul (pcContinuous_ps f'))
        ((pcContinuous_ps f₂).mul (pcContinuous_ps f')))
    (fun c f f' => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact pcInt_smul c _)
    (fun f f₁ f₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact pcInt_add ((pcContinuous_ps f).mul (pcContinuous_ps f₁))
        ((pcContinuous_ps f).mul (pcContinuous_ps f₂)))
    (fun c f f' => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact pcInt_smul c _)

/-- The value of the pairing. -/
theorem pcPair_apply (χ₁ χ₂ : Kˣ →* ℂˣ) (f : principalSeriesSpace K χ₁ χ₂)
    (f' : principalSeriesSpace K χ₁⁻¹ χ₂⁻¹) :
    pcPair χ₁ χ₂ f f' = pcInt K (fun x => (f : GL (Fin 2) K → ℂ) x * (f' : GL (Fin 2) K → ℂ) x) :=
  rfl

/-- Each open subgroup $H$ of $GL_2(K)$ contains a compact open subgroup. -/
theorem pcExists_compact_open_le {H : Subgroup (GL (Fin 2) K)}
    (hH : IsOpen (H : Set (GL (Fin 2) K))) :
    ∃ U : Subgroup (GL (Fin 2) K), U ≤ H ∧ IsOpen (U : Set (GL (Fin 2) K)) ∧
      IsCompact (U : Set (GL (Fin 2) K)) :=
  ⟨H ⊓ congruence K 1 one_ne_zero le_rfl, inf_le_left, by
    rw [Subgroup.coe_inf]; exact hH.inter (isOpen_congruence _ _ _), by
    rw [Subgroup.coe_inf]
    exact (isCompact_congruence _ _).inter_left (Subgroup.isClosed_of_isOpen H hH)⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The relation $\chi(a) \chi^{-1}(a) = 1$. -/
theorem pcMul_inv_apply (χ : Kˣ →* ℂˣ) (a : Kˣ) : (χ a : ℂ) * (χ⁻¹ a : ℂ) = 1 := by
  rw [MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The relation $\chi^{-1}(a) \chi(a) = 1$. -/
theorem pcInv_mul_apply (χ : Kˣ →* ℂˣ) (a : Kˣ) : (χ⁻¹ a : ℂ) * (χ a : ℂ) = 1 := by
  rw [mul_comm, pcMul_inv_apply]

/-- **The contragredient of the principal series from the invariance of $\Lambda$.** If `PcIntInvariant K` holds, then `PSContragredientIso K` holds: the contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is isomorphic to $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$. The isomorphism sends $f'$ to the linear form $f \mapsto \int_{GL_2(\mathcal{O}_K)} f(k) f'(k) \, dk$. -/
theorem pcContragredientIso_of_invariant (hI : PcIntInvariant K) : PSContragredientIso K := by
  intro χ₁ χ₂ hχ₁ hχ₂
  refine (pcIso_contragredient_of_pairing (principalSeries K χ₁ χ₂)
    (principalSeries K χ₁⁻¹ χ₂⁻¹) (fun H hH => pcExists_compact_open_le hH)
    (principalSeries_isAdmissible hχ₁ hχ₂) (principalSeries_isAdmissible hχ₁.inv hχ₂.inv)
    (pcPair χ₁ χ₂) (fun g v w => ?_) (fun w hw => ?_) (fun v hv => ?_)).symm
  · exact hI _ (pcIsDelta_mul (pcMul_inv_apply χ₁) (pcMul_inv_apply χ₂) v w) g
  · exact pcNondeg hI hχ₁ hχ₂ (pcMul_inv_apply χ₁) (pcMul_inv_apply χ₂) w hw
  · obtain ⟨w, hw⟩ := pcNondeg hI hχ₁.inv hχ₂.inv (pcInv_mul_apply χ₁) (pcInv_mul_apply χ₂) v hv
    refine ⟨w, ?_⟩
    change pcInt K (fun x => v.1 x * w.1 x) ≠ 0
    simp_rw [mul_comm (v.1 _)]
    exact hw

end GL2Pairing

section Iwahori

open GL2 SmoothRep ValuativeRel LocalGL1

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The valuation of an element of the maximal ideal is less than $1$ exactly when it is not a unit of valuation $1$. -/
theorem pcV_lt_one_iff_ne {x : K} (hx : valuation K x ≤ 1) :
    valuation K x < 1 ↔ valuation K x ≠ 1 :=
  ⟨ne_of_lt, fun h => lt_of_le_of_ne hx h⟩

/-- For $x \ne 0$, $v(x) < 1$ exactly when $\mathrm{ord}(x) \ge 1$. -/
theorem pcV_lt_one_iff {x : K} (hx : x ≠ 0) : valuation K x < 1 ↔ 1 ≤ ord K x := by
  constructor
  · intro h
    have h1 := (valuation_le_one_iff hx).1 h.le
    have h2 : ord K x ≠ 0 := fun h0 => h.ne ((valuation_eq_one_iff hx).2 h0)
    omega
  · intro h
    exact lt_of_le_of_ne ((valuation_le_one_iff hx).2 (by omega))
      (fun h0 => by have := (valuation_eq_one_iff hx).1 h0; omega)

/-- The chosen uniformizer has valuation less than $1$. -/
theorem pcV_unif_lt : valuation K (unif K : K) < 1 :=
  (pcV_lt_one_iff (unif K).ne_zero).2 (by rw [ord_unif])

/-- If $v(x) < 1$ then $v(x \varpi^{-1}) \le 1$. -/
theorem pcV_mul_unif_inv {x : K} (hx : valuation K x < 1) :
    valuation K (x * (unif K : K)⁻¹) ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  have hu := (unif K).ne_zero
  rw [valuation_le_one_iff (mul_ne_zero h0 (inv_ne_zero hu)), ord_mul h0 (inv_ne_zero hu),
    ord_inv hu, ord_unif]
  have := (pcV_lt_one_iff h0).1 hx
  omega

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The determinant of an integral matrix is integral. -/
theorem pcV_det_le {M : Matrix (Fin 2) (Fin 2) K} (hM : IsIntegralMatrix M) :
    valuation K M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;>
    exact mul_le_one' (hM _ _) (hM _ _)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element of $GL_2(\mathcal{O}_K)$ has determinant of valuation $1$. -/
theorem pcV_det {k : GL (Fin 2) K} (hk : k ∈ maxCompact K) : valuation K k.1.det = 1 := by
  have h1 := pcV_det_le hk.1
  have h2 := pcV_det_le hk.2
  have e : k.1.det * (k⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have e' := congrArg (valuation K) e
  rw [map_mul, map_one] at e'
  by_contra hne
  have : valuation K k.1.det * valuation K (k⁻¹).1.det < 1 :=
    mul_lt_of_lt_of_le_one (lt_of_le_of_ne h1 hne) h2
  rw [e'] at this
  exact lt_irrefl _ this

variable (K) in
/-- The Iwahori subgroup $I$ of $GL_2(\mathcal{O}_K)$: the elements whose lower left entry is in the maximal ideal. -/
def pcIwahori : Subgroup (maxCompact K) where
  carrier := {k | valuation K ((k : GL (Fin 2) K).1 1 0) < 1}
  mul_mem' {a b} ha hb := by
    change valuation K (((a : GL (Fin 2) K).1 * (b : GL (Fin 2) K).1) 1 0) < 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_of_lt_of_le_one ha (b.2.1 0 0)
    · exact mul_lt_of_le_one_of_lt (a.2.1 1 1) hb
  one_mem' := by
    change valuation K ((1 : Matrix (Fin 2) (Fin 2) K) 1 0) < 1
    simp
  inv_mem' {a} ha := by
    change valuation K (((a : GL (Fin 2) K)⁻¹).1 1 0) < 1
    rw [val_inv]
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, map_mul, map_inv₀, pcV_det a.2, inv_one, one_mul, Valuation.map_neg]
    exact ha

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Membership in the Iwahori subgroup. -/
theorem pcMem_iwahori (k : maxCompact K) :
    k ∈ pcIwahori K ↔ valuation K ((k : GL (Fin 2) K).1 1 0) < 1 :=
  Iff.rfl

/-- The Iwahori subgroup is open in $GL_2(\mathcal{O}_K)$. -/
theorem pcIsOpen_iwahori : IsOpen (pcIwahori K : Set (maxCompact K)) := by
  have h : IsOpen {x : K | valuation K (x - 0) < 1} := isOpen_valuation_sub_lt 0 1
  simp only [sub_zero] at h
  have hc : Continuous fun k : maxCompact K => (k : GL (Fin 2) K).1 1 0 :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem 1 0
  exact h.preimage hc

/-- The Iwahori subgroup is a compact space. -/
instance pcIwCompact : CompactSpace (pcIwahori K) :=
  isCompact_iff_compactSpace.mp ((pcIwahori K).isClosed_of_isOpen pcIsOpen_iwahori).isCompact

variable (K) in
/-- The element $\eta = \begin{pmatrix} 0 & 1 \\ \varpi & 0 \end{pmatrix}$ of $GL_2(K)$. It normalizes the Iwahori subgroup. -/
noncomputable def pcEta : GL (Fin 2) K :=
  ⟨!![0, 1; (unif K : K), 0], !![0, (unif K : K)⁻¹; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, (unif K).ne_zero], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, (unif K).ne_zero]⟩

/-- The matrix of $\eta k \eta^{-1}$. -/
theorem pcEta_conj_val (k : GL (Fin 2) K) : (pcEta K * k * (pcEta K)⁻¹).1 =
    !![k.1 1 1, k.1 1 0 * (unif K : K)⁻¹; (unif K : K) * k.1 0 1, k.1 0 0] := by
  have hu := (unif K).ne_zero
  rw [Units.val_mul, Units.val_mul]
  change (!![0, 1; (unif K : K), 0] * k.1 * !![0, (unif K : K)⁻¹; 1, 0]) = _
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  field_simp

/-- The matrix of $\eta^{-1} k \eta$. It is the matrix of $\eta k \eta^{-1}$. -/
theorem pcEtaInv_conj (k : GL (Fin 2) K) :
    (pcEta K)⁻¹ * k * pcEta K = pcEta K * k * (pcEta K)⁻¹ := by
  have hu := (unif K).ne_zero
  refine Units.ext ?_
  rw [pcEta_conj_val, Units.val_mul, Units.val_mul]
  change (!![0, (unif K : K)⁻¹; 1, 0] * k.1 * !![0, 1; (unif K : K), 0]) = _
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> field_simp

/-- Conjugation by $\eta$ maps the Iwahori subgroup into itself. -/
theorem pcEta_conj_mem (k : pcIwahori K) :
    pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹ ∈ maxCompact K ∧
      valuation K ((pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹).1 1 0) < 1 := by
  have key : ∀ k : pcIwahori K,
      IsIntegralMatrix (pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹).1 ∧
      valuation K ((pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹).1 1 0) < 1 := by
    intro k
    have h := (k : maxCompact K).2.1
    have hk : valuation K (((k : maxCompact K) : GL (Fin 2) K).1 1 0) < 1 := k.2
    rw [pcEta_conj_val]
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact h 1 1
      · exact pcV_mul_unif_inv hk
      · simpa [map_mul] using mul_le_one' pcV_unif_lt.le (h 0 1)
      · exact h 0 0
    · simpa [map_mul] using mul_lt_of_lt_of_le_one pcV_unif_lt (h 0 1)
  refine ⟨⟨(key k).1, ?_⟩, (key k).2⟩
  have e : (pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹)⁻¹ =
      pcEta K * ((k⁻¹ : pcIwahori K) : maxCompact K) * (pcEta K)⁻¹ := by
    simp [mul_assoc]
  rw [e]
  exact (key k⁻¹).1

/-- The map $k \mapsto \eta k \eta^{-1}$ on the Iwahori subgroup. -/
noncomputable def pcConjFun (k : pcIwahori K) : pcIwahori K :=
  ⟨⟨_, (pcEta_conj_mem k).1⟩, (pcEta_conj_mem k).2⟩

/-- The value of `pcConjFun`. -/
theorem pcConjFun_val (k : pcIwahori K) : (((pcConjFun k : pcIwahori K) : maxCompact K) :
    GL (Fin 2) K) = pcEta K * ((k : maxCompact K) : GL (Fin 2) K) * (pcEta K)⁻¹ :=
  rfl

/-- Conjugation by $\eta$ on the Iwahori subgroup is an involution, because $\eta^2 = \varpi$ is central. -/
theorem pcConjFun_conjFun (k : pcIwahori K) : pcConjFun (pcConjFun k) = k := by
  have hu := (unif K).ne_zero
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  rw [pcConjFun_val, pcEta_conj_val, pcConjFun_val, pcEta_conj_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- Conjugation by $\eta$ as a continuous automorphism of the Iwahori subgroup. -/
noncomputable def pcConj : pcIwahori K ≃* pcIwahori K where
  toFun := pcConjFun
  invFun := pcConjFun
  left_inv := pcConjFun_conjFun
  right_inv := pcConjFun_conjFun
  map_mul' a b := Subtype.ext (Subtype.ext (by
    simp only [pcConjFun_val, Subgroup.coe_mul]
    group))

/-- Conjugation by $\eta$ is continuous on the Iwahori subgroup. -/
theorem pcContinuous_conj : Continuous (pcConj (K := K)) := by
  change Continuous pcConjFun
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
    continuous_const

variable (K) in
/-- The integral $A(\psi) = \int_I \psi(i) \, di$ over the Iwahori subgroup, for the Haar measure of mass $1$ on $I$. -/
noncomputable def pcIwInt (ψ : GL (Fin 2) K → ℂ) : ℂ :=
  ∫ i : pcIwahori K, ψ ((i : maxCompact K) : GL (Fin 2) K) ∂pcHaar (pcIwahori K)

/-- Conjugation by $\eta$ does not change the integral over the Iwahori subgroup: $\int_I \psi(x i \eta) \, di = \int_I \psi(x \eta i) \, di$. -/
theorem pcIwInt_eta (ψ : GL (Fin 2) K → ℂ) (x : GL (Fin 2) K) :
    pcIwInt K (fun i => ψ (x * i * pcEta K)) = pcIwInt K (fun i => ψ (x * pcEta K * i)) := by
  unfold pcIwInt
  conv_rhs => rw [← integral_pcHaar_mulEquiv pcConj pcContinuous_conj pcContinuous_conj]
  congr 1
  funext i
  change ψ (x * _ * pcEta K) = ψ (x * pcEta K * (pcEta K * _ * (pcEta K)⁻¹))
  rw [← pcEtaInv_conj]
  group

/-- The real number $\mu(I)$, the mass of the Iwahori subgroup for the Haar measure of mass $1$ on $GL_2(\mathcal{O}_K)$. -/
noncomputable def pcC : ℝ :=
  (pcHaar (maxCompact K) (pcIwahori K : Set (maxCompact K))).toReal

/-- If the left translate of a set $S$ by $x \in GL_2(\mathcal{O}_K)$ is the Iwahori subgroup, then the integral of $\varphi$ over $S$ is $\mu(I) \int_I \varphi(x i) \, di$. -/
theorem pcInt_cell {S : Set (maxCompact K)} (x : maxCompact K)
    (hS : ∀ k, x * k ∈ S ↔ k ∈ (pcIwahori K : Set (maxCompact K))) (f : GL (Fin 2) K → ℂ) :
    ∫ k, S.indicator (fun k : maxCompact K => f k) k ∂pcHaar (maxCompact K) =
      (pcC (K := K)) • pcIwInt K (fun g => f ((x : GL (Fin 2) K) * g)) := by
  rw [← integral_pcHaar_mul_left _ x]
  have e : (fun k => S.indicator (fun k : maxCompact K => f k) (x * k)) =
      (pcIwahori K : Set (maxCompact K)).indicator
        (fun k : maxCompact K => f ((x : GL (Fin 2) K) * k)) := by
    funext k
    by_cases hk : k ∈ (pcIwahori K : Set (maxCompact K))
    · rw [Set.indicator_of_mem ((hS k).2 hk), Set.indicator_of_mem hk]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hk ((hS k).1 h)), Set.indicator_of_notMem hk]
  rw [e, integral_indicator_pcHaar _ pcIsOpen_iwahori]
  rfl

/-- An element of $\mathcal{O}_K$ has residue $0$ exactly when its valuation is less than $1$. -/
theorem pcResidue_eq_zero_iff (a : 𝒪[K]) :
    IsLocalRing.residue 𝒪[K] a = 0 ↔ valuation K (a : K) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
  exact (pcV_lt_one_iff_ne a.2).symm

open Classical in
/-- A lift to $\mathcal{O}_K$ of an element of the residue field. The lift of $0$ is $0$. -/
noncomputable def pcLift (r : 𝓀[K]) : 𝒪[K] :=
  if r = 0 then 0 else (IsLocalRing.residue_surjective r).choose

/-- The residue of the lift of $r$ is $r$. -/
theorem pcResidue_lift (r : 𝓀[K]) : IsLocalRing.residue 𝒪[K] (pcLift r) = r := by
  unfold pcLift
  split_ifs with h
  · simp [h]
  · exact (IsLocalRing.residue_surjective r).choose_spec

/-- The lift of $0$ is $0$. -/
theorem pcLift_zero : pcLift (0 : 𝓀[K]) = 0 := by
  simp [pcLift]

/-- The lift of a nonzero residue is a unit of $\mathcal{O}_K$. -/
theorem pcV_lift {r : 𝓀[K]} (hr : r ≠ 0) : valuation K (pcLift r : K) = 1 := by
  by_contra h
  apply hr
  rw [← pcResidue_lift r, pcResidue_eq_zero_iff]
  exact lt_of_le_of_ne (pcLift r).2 h

/-- For $z \in \mathcal{O}_K$, $v(z - s(r)) < 1$ exactly when the residue of $z$ is $r$. -/
theorem pcV_sub_lift_lt_iff {z : K} (hz : valuation K z ≤ 1) (r : 𝓀[K]) :
    valuation K (z - pcLift r) < 1 ↔ IsLocalRing.residue 𝒪[K] ⟨z, hz⟩ = r := by
  conv_rhs => rw [← pcResidue_lift r, ← sub_eq_zero, ← map_sub, pcResidue_eq_zero_iff]
  rfl

variable (K) in
/-- The $q + 1$ cells of $GL_2(\mathcal{O}_K)$. The cell `none` is the set of $k$ with $v(k_{00}) < 1$. The cell `some r` is the set of $k$ with $v(k_{10} - s(r) k_{00}) < 1$. -/
def pcCell : Option 𝓀[K] → Set (maxCompact K)
  | none => {k | valuation K ((k : GL (Fin 2) K).1 0 0) < 1}
  | some r => {k | valuation K ((k : GL (Fin 2) K).1 1 0 -
      (pcLift r : K) * (k : GL (Fin 2) K).1 0 0) < 1}

/-- Each cell is open. -/
theorem pcIsOpen_cell (o : Option 𝓀[K]) : IsOpen (pcCell K o) := by
  have h : IsOpen {x : K | valuation K (x - 0) < 1} := isOpen_valuation_sub_lt 0 1
  simp only [sub_zero] at h
  have hc : ∀ i j, Continuous fun k : maxCompact K => (k : GL (Fin 2) K).1 i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  cases o with
  | none => exact h.preimage (hc 0 0)
  | some r => exact h.preimage ((hc 1 0).sub (continuous_const.mul (hc 0 0)))

attribute [local instance] Fintype.ofFinite in
/-- The cells cover $GL_2(\mathcal{O}_K)$ and do not overlap. -/
theorem pcCell_sum (k : maxCompact K) (f : maxCompact K → ℂ) :
    ∑ o, (pcCell K o).indicator f k = f k := by
  rw [Fintype.sum_option]
  have hk := k.2
  have hdet := pcV_det hk
  rw [Matrix.det_fin_two] at hdet
  have ha : valuation K ((k : GL (Fin 2) K).1 0 0) ≤ 1 := hk.1 0 0
  have hc : valuation K ((k : GL (Fin 2) K).1 1 0) ≤ 1 := hk.1 1 0
  by_cases h0 : valuation K ((k : GL (Fin 2) K).1 0 0) < 1
  · have hc1 : ¬ valuation K ((k : GL (Fin 2) K).1 1 0) < 1 := by
      intro hc'
      have : valuation K ((k : GL (Fin 2) K).1 0 0 * (k : GL (Fin 2) K).1 1 1 -
          (k : GL (Fin 2) K).1 0 1 * (k : GL (Fin 2) K).1 1 0) < 1 := by
        rw [sub_eq_add_neg]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [map_mul]
          exact mul_lt_of_lt_of_le_one h0 (hk.1 1 1)
        · rw [Valuation.map_neg, map_mul]
          exact mul_lt_of_le_one_of_lt (hk.1 0 1) hc'
      rw [hdet] at this
      exact lt_irrefl _ this
    rw [Set.indicator_of_mem (show k ∈ pcCell K none from h0), Finset.sum_eq_zero, add_zero]
    intro r _
    refine Set.indicator_of_notMem ?_ _
    intro hr
    apply hc1
    have hs : valuation K ((pcLift r : K) * (k : GL (Fin 2) K).1 0 0) < 1 := by
      rw [map_mul]
      exact mul_lt_of_le_one_of_lt (pcLift r).2 h0
    have := Valuation.map_add_lt _ hr hs
    rwa [sub_add_cancel] at this
  · have ha1 : valuation K ((k : GL (Fin 2) K).1 0 0) = 1 := le_antisymm ha (not_lt.1 h0)
    have ha0 : (k : GL (Fin 2) K).1 0 0 ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact zero_ne_one ha1
    have hz : valuation K ((k : GL (Fin 2) K).1 1 0 / (k : GL (Fin 2) K).1 0 0) ≤ 1 := by
      rw [map_div₀, ha1, div_one]
      exact hc
    rw [Set.indicator_of_notMem (show k ∉ pcCell K none from h0), zero_add]
    have key : ∀ r, k ∈ pcCell K (some r) ↔ IsLocalRing.residue 𝒪[K] ⟨_, hz⟩ = r := by
      intro r
      rw [← pcV_sub_lift_lt_iff hz r]
      change valuation K ((k : GL (Fin 2) K).1 1 0 -
        (pcLift r : K) * (k : GL (Fin 2) K).1 0 0) < 1 ↔ _
      rw [show (k : GL (Fin 2) K).1 1 0 - (pcLift r : K) * (k : GL (Fin 2) K).1 0 0 =
        (k : GL (Fin 2) K).1 0 0 * ((k : GL (Fin 2) K).1 1 0 / (k : GL (Fin 2) K).1 0 0 -
          (pcLift r : K)) by field_simp, map_mul, ha1, one_mul]
    rw [Finset.sum_eq_single (IsLocalRing.residue 𝒪[K] ⟨_, hz⟩)]
    · exact Set.indicator_of_mem ((key _).2 rfl) _
    · intro r _ hr
      exact Set.indicator_of_notMem (fun h => hr ((key r).1 h).symm) _
    · intro h
      exact absurd (Finset.mem_univ _) h

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Weyl element is in $GL_2(\mathcal{O}_K)$. -/
theorem pcWeyl_mem : (weyl : GL (Fin 2) K) ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [weyl_val]
    fin_cases i <;> fin_cases j <;> simp
  · rw [weyl_inv, weyl_val]
    fin_cases i <;> fin_cases j <;> simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $v(x) \le 1$ the element $n(x)$ is in $GL_2(\mathcal{O}_K)$. -/
theorem pcUnip_mem {x : K} (hx : valuation K x ≤ 1) : unip x ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [unip_val]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [unip_inv, unip_val]
    fin_cases i <;> fin_cases j <;> simp [hx]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The lower unipotent element with entry $0$ is the identity. -/
theorem pcLowerUnip_zero : lowerUnip (0 : K) = 1 :=
  Units.ext (by
    change !![1, 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.one_fin_two])

/-- The left translate of the cell `none` by $w$ is the Iwahori subgroup. -/
theorem pcCell_none_iff (k : maxCompact K) :
    (⟨weyl, pcWeyl_mem⟩ : maxCompact K) * k ∈ pcCell K none ↔
      k ∈ (pcIwahori K : Set (maxCompact K)) := by
  change valuation K ((weyl * (k : GL (Fin 2) K)).1 0 0) < 1 ↔
    valuation K ((k : GL (Fin 2) K).1 1 0) < 1
  rw [Units.val_mul, weyl_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The left translate of the cell `some r` by $\begin{pmatrix} 1 & 0 \\ s(r) & 1 \end{pmatrix}$ is the Iwahori subgroup. -/
theorem pcCell_some_iff (r : 𝓀[K]) (k : maxCompact K) :
    (⟨lowerUnip (pcLift r : K), lowerUnip_mem (pcLift r).2⟩ : maxCompact K) * k ∈
      pcCell K (some r) ↔ k ∈ (pcIwahori K : Set (maxCompact K)) := by
  change valuation K ((lowerUnip (pcLift r : K) * (k : GL (Fin 2) K)).1 1 0 -
      (pcLift r : K) * (lowerUnip (pcLift r : K) * (k : GL (Fin 2) K)).1 0 0) < 1 ↔
    valuation K ((k : GL (Fin 2) K).1 1 0) < 1
  rw [Units.val_mul]
  change valuation K ((!![1, 0; (pcLift r : K), 1] * (k : GL (Fin 2) K).1) 1 0 -
      (pcLift r : K) * (!![1, 0; (pcLift r : K), 1] * (k : GL (Fin 2) K).1) 0 0) < 1 ↔ _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Left translation by an element of $I$ does not change the integral over $I$. -/
theorem pcIwInt_mul_left (h : pcIwahori K) (ψ : GL (Fin 2) K → ℂ) :
    pcIwInt K (fun g => ψ (((h : maxCompact K) : GL (Fin 2) K) * g)) = pcIwInt K ψ :=
  integral_pcHaar_mul_left (fun i : pcIwahori K => ψ ((i : maxCompact K) : GL (Fin 2) K)) h

/-- For $v(y) = 1$ and $\varphi$ of modulus type, $\int_I \varphi(n^-(y) i) \, di = \int_I \varphi(w i) \, di$. It uses $n^-(y) = b w n(y^{-1})$ with $b = \begin{pmatrix} -y^{-1} & 1 \\ 0 & y \end{pmatrix}$. -/
theorem pcIwInt_lower {φ : GL (Fin 2) K → ℂ}
    (hδ : ∀ b g : GL (Fin 2) K, b.1 1 0 = 0 →
      φ (b * g) = (normAbs K (b.1 0 0 / b.1 1 1) : ℂ) * φ g)
    {y : K} (hy : valuation K y = 1) :
    pcIwInt K (fun g => φ (lowerUnip y * g)) = pcIwInt K (fun g => φ (weyl * g)) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hm : unip y⁻¹ ∈ maxCompact K := pcUnip_mem (by rw [map_inv₀, hy, inv_one])
  let n : pcIwahori K := ⟨⟨unip y⁻¹, hm⟩, by
    change valuation K ((unip y⁻¹).1 1 0) < 1
    simp [unip_val]⟩
  rw [← pcIwInt_mul_left n (fun g => φ (weyl * g))]
  unfold pcIwInt
  congr 1
  funext i
  show φ (lowerUnip y * ((i : maxCompact K) : GL (Fin 2) K)) =
    φ (weyl * (unip y⁻¹ * ((i : maxCompact K) : GL (Fin 2) K)))
  have hb : (lowerUnip y * (unip y⁻¹)⁻¹ * weyl⁻¹).1 = !![-y⁻¹, 1; 0, y] := by
    rw [unip_inv, weyl_inv, Units.val_mul, Units.val_mul, unip_val, weyl_val]
    change !![1, 0; y, 1] * !![1, -y⁻¹; 0, 1] * !![0, 1; 1, 0] = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy0]
  have e : lowerUnip y * ((i : maxCompact K) : GL (Fin 2) K) =
      (lowerUnip y * (unip y⁻¹)⁻¹ * weyl⁻¹) *
        (weyl * (unip y⁻¹ * ((i : maxCompact K) : GL (Fin 2) K))) := by
    group
  have hn : normAbs K ((lowerUnip y * (unip y⁻¹)⁻¹ * weyl⁻¹).1 0 0 /
      (lowerUnip y * (unip y⁻¹)⁻¹ * weyl⁻¹).1 1 1) = 1 := by
    rw [hb]
    exact normAbs_eq_one (by simp [hy])
  rw [e, hδ _ _ (by rw [hb]; rfl), hn, Complex.ofReal_one, one_mul]

attribute [local instance] Fintype.ofFinite in
/-- **The decomposition formula.** For $\varphi$ continuous of modulus type, $\int_{GL_2(\mathcal{O}_K)} \varphi = \mu(I) \left(\int_I \varphi(i) \, di + q \int_I \varphi(w i) \, di\right)$. -/
theorem pcInt_decomp {φ : GL (Fin 2) K → ℂ} (hφ : Continuous φ)
    (hδ : ∀ b g : GL (Fin 2) K, b.1 1 0 = 0 →
      φ (b * g) = (normAbs K (b.1 0 0 / b.1 1 1) : ℂ) * φ g) :
    pcInt K φ = (pcC (K := K) : ℂ) *
      (pcIwInt K φ + (residueCard K : ℂ) * pcIwInt K (fun g => φ (weyl * g))) := by
  classical
  have hint : ∀ o, Integrable ((pcCell K o).indicator (fun k : maxCompact K => φ k))
      (pcHaar (maxCompact K)) := fun o =>
    ((hφ.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).indicator (pcIsOpen_cell o).measurableSet
  have hsum : pcInt K φ = ∑ o, ∫ k, (pcCell K o).indicator (fun k : maxCompact K => φ k) k
      ∂pcHaar (maxCompact K) := by
    rw [← integral_finsetSum _ (fun o _ => hint o)]
    unfold pcInt
    congr 1
    funext k
    exact (pcCell_sum k (fun k : maxCompact K => φ k)).symm
  have hw := pcInt_cell ⟨weyl, pcWeyl_mem⟩ pcCell_none_iff φ
  have hr : ∀ r : 𝓀[K], ∫ k, (pcCell K (some r)).indicator (fun k : maxCompact K => φ k) k
      ∂pcHaar (maxCompact K) = (pcC (K := K)) • (pcIwInt K (fun g => φ (weyl * g)) +
        if r = 0 then pcIwInt K φ - pcIwInt K (fun g => φ (weyl * g)) else 0) := by
    intro r
    rw [pcInt_cell ⟨lowerUnip _, lowerUnip_mem (pcLift r).2⟩ (pcCell_some_iff r) φ]
    congr 1
    split_ifs with h
    · subst h
      rw [add_sub_cancel]
      simp only [pcLift_zero, ZeroMemClass.coe_zero, pcLowerUnip_zero, one_mul]
    · rw [add_zero]
      exact pcIwInt_lower hδ (pcV_lift h)
  rw [hsum, Fintype.sum_option, hw, Finset.sum_congr rfl (fun r _ => hr r), ← Finset.smul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, Complex.real_smul, nsmul_eq_mul]
  rw [show residueCard K = Fintype.card 𝓀[K] from Nat.card_eq_fintype_card]
  ring

/-- A function of modulus type is continuous. -/
theorem pcIsDelta_continuous {φ : GL (Fin 2) K → ℂ} (hφ : PcIsDelta K φ) : Continuous φ := by
  obtain ⟨_, U, hU, hφU⟩ := hφ
  exact pcContinuous_of_right hU hφU

/-- A right translate of a function of modulus type is of modulus type. -/
theorem pcIsDelta_right {φ : GL (Fin 2) K → ℂ} (hφ : PcIsDelta K φ) (g : GL (Fin 2) K) :
    PcIsDelta K (fun x => φ (x * g)) := by
  obtain ⟨h1, U, hU, hφU⟩ := hφ
  refine ⟨fun b x hb => by simp only [mul_assoc]; exact h1 b (x * g) hb,
    U.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun x u hu => ?_⟩
  · have hc : Continuous fun u : GL (Fin 2) K => g⁻¹ * u * g :=
      (continuous_const.mul continuous_id).mul continuous_const
    convert hU.preimage hc using 1
    ext u
    simp
  · have e : x * u * g = x * g * (g⁻¹ * u * g) := by group
    simp only []
    rw [e]
    exact hφU _ _ (by simpa using hu)

/-- The matrix of $\eta w$ is $\mathrm{diag}(1, \varpi)$. -/
theorem pcEta_weyl_val : (pcEta K * weyl).1 = !![1, 0; 0, (unif K : K)] := by
  rw [Units.val_mul, weyl_val]
  change !![0, 1; (unif K : K), 0] * !![0, 1; 1, 0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix of $w \eta$ is $\mathrm{diag}(\varpi, 1)$. -/
theorem pcWeyl_eta_val : (weyl * pcEta K).1 = !![(unif K : K), 0; 0, 1] := by
  rw [Units.val_mul, weyl_val]
  change !![0, 1; 1, 0] * !![0, 1; (unif K : K), 0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The absolute value of the chosen uniformizer is $q^{-1}$. -/
theorem pcNormAbs_unif : (normAbs K (unif K : K) : ℂ) = (residueCard K : ℂ)⁻¹ := by
  rw [LocalGL1.normAbs_eq_zpow (unif K).ne_zero, ord_unif]
  push_cast
  rw [zpow_neg_one]

/-- The absolute value of $\varpi^{-1}$ is $q$. -/
theorem pcNormAbs_inv_unif : (normAbs K (1 / (unif K : K)) : ℂ) = (residueCard K : ℂ) := by
  rw [normAbs_div, normAbs_one, Complex.ofReal_div, Complex.ofReal_one, pcNormAbs_unif, one_div,
    inv_inv]

/-- **Invariance under $\eta$.** For $\varphi$ of modulus type, $\Lambda(R_\eta \varphi) = \Lambda(\varphi)$. -/
theorem pcInt_eta {φ : GL (Fin 2) K → ℂ} (hφ : PcIsDelta K φ) :
    pcInt K (fun x => φ (x * pcEta K)) = pcInt K φ := by
  have hφ' := pcIsDelta_right hφ (pcEta K)
  rw [pcInt_decomp (pcIsDelta_continuous hφ') hφ'.1, pcInt_decomp (pcIsDelta_continuous hφ) hφ.1]
  have hq : (residueCard K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (residueCard_pos K).ne'
  have h1 : pcIwInt K (fun g => φ (g * pcEta K)) =
      (residueCard K : ℂ) * pcIwInt K (fun g => φ (weyl * g)) := by
    have := pcIwInt_eta φ 1
    simp only [one_mul] at this
    rw [this]
    unfold pcIwInt
    rw [← integral_const_mul]
    congr 1
    funext i
    beta_reduce
    have e : pcEta K * ((i : maxCompact K) : GL (Fin 2) K) =
        (pcEta K * weyl) * (weyl * ((i : maxCompact K) : GL (Fin 2) K)) := by
      rw [← mul_assoc, mul_assoc (pcEta K), weyl_mul_weyl, mul_one]
    rw [e, hφ.1 _ _ (by rw [pcEta_weyl_val]; rfl), pcEta_weyl_val]
    rw [show (!![1, 0; 0, (unif K : K)] : Matrix (Fin 2) (Fin 2) K) 0 0 /
      !![1, 0; 0, (unif K : K)] 1 1 = 1 / (unif K : K) from rfl, pcNormAbs_inv_unif]
  have h2 : pcIwInt K (fun g => φ (weyl * g * pcEta K)) =
      (residueCard K : ℂ)⁻¹ * pcIwInt K φ := by
    rw [pcIwInt_eta φ weyl]
    unfold pcIwInt
    rw [← integral_const_mul]
    congr 1
    funext i
    beta_reduce
    rw [hφ.1 _ _ (by rw [pcWeyl_eta_val]; rfl), pcWeyl_eta_val]
    rw [show (!![(unif K : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 /
      !![(unif K : K), 0; 0, 1] 1 1 = (unif K : K) / 1 from rfl, div_one, pcNormAbs_unif]
  rw [h1, h2, mul_inv_cancel_left₀ hq]
  ring

variable (K) in
/-- The subgroup of the elements $g$ of $GL_2(K)$ with $\Lambda(R_g \varphi) = \Lambda(\varphi)$ for each $\varphi$ of modulus type. -/
def pcInvSubgroup : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∀ φ, PcIsDelta K φ → pcInt K (fun x => φ (x * g)) = pcInt K φ}
  mul_mem' {a b} ha hb := by
    intro φ hφ
    have h1 := ha _ (pcIsDelta_right hφ b)
    calc pcInt K (fun x => φ (x * (a * b))) = pcInt K (fun x => φ (x * a * b)) := by
          simp only [mul_assoc]
      _ = pcInt K (fun x => φ (x * b)) := h1
      _ = pcInt K φ := hb φ hφ
  one_mem' := by
    intro φ _
    show pcInt K (fun x => φ (x * 1)) = _
    simp only [mul_one]
  inv_mem' {a} ha := by
    intro φ hφ
    have h1 : pcInt K (fun x => φ (x * a * a⁻¹)) = pcInt K (fun x => φ (x * a⁻¹)) :=
      ha _ (pcIsDelta_right hφ a⁻¹)
    simp only [mul_inv_cancel_right] at h1
    exact h1.symm

/-- The group $GL_2(\mathcal{O}_K)$ preserves $\Lambda$. -/
theorem pcMaxCompact_le : maxCompact K ≤ pcInvSubgroup K := by
  intro g hg φ _
  exact integral_pcHaar_mul_right (fun k : maxCompact K => φ k) ⟨g, hg⟩

/-- The element $\eta$ preserves $\Lambda$. -/
theorem pcEta_mem : pcEta K ∈ pcInvSubgroup K :=
  fun _ hφ => pcInt_eta hφ

/-- The center of $GL_2(K)$ preserves $\Lambda$. -/
theorem pcScalar_mem (d : Kˣ) : ((diagTorus K d d : torus K) : GL (Fin 2) K) ∈ pcInvSubgroup K := by
  intro φ hφ
  unfold pcInt
  congr 1
  funext k
  beta_reduce
  have hc : (k : GL (Fin 2) K) * ((diagTorus K d d : torus K) : GL (Fin 2) K) =
      ((diagTorus K d d : torus K) : GL (Fin 2) K) * k := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    change _ * !![(d : K), 0; 0, (d : K)] = !![(d : K), 0; 0, (d : K)] * _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [hc, hφ.1 _ _ rfl]
  change (normAbs K ((d : K) / (d : K)) : ℂ) * _ = _
  rw [div_self d.ne_zero, normAbs_one, Complex.ofReal_one, one_mul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
variable (K) in
/-- The homomorphism $x \mapsto \mathrm{diag}(x, 1)$ from $K^\times$ to $GL_2(K)$. -/
noncomputable def pcDiag : Kˣ →* GL (Fin 2) K :=
  (torus K).subtype.comp (diagTorusHom.comp (MonoidHom.inl Kˣ Kˣ))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The matrix of $\mathrm{diag}(x, 1)$. -/
theorem pcDiag_val (x : Kˣ) : (pcDiag K x).1 = !![(x : K), 0; 0, 1] := by
  change !![(x : K), 0; 0, ((1 : Kˣ) : K)] = _
  rw [Units.val_one]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For a unit $u$ of $\mathcal{O}_K$, $\mathrm{diag}(u, 1)$ is in $GL_2(\mathcal{O}_K)$. -/
theorem pcDiag_mem_maxCompact {u : Kˣ} (hu : valuation K (u : K) = 1) :
    pcDiag K u ∈ maxCompact K := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [pcDiag_val]
    fin_cases i <;> fin_cases j <;> simp [hu]
  · rw [← map_inv, pcDiag_val]
    fin_cases i <;> fin_cases j <;> simp [hu]

/-- Each element $\mathrm{diag}(x, 1)$ preserves $\Lambda$. It is $\mathrm{diag}(u, 1) (w \eta)^m$ with $u$ a unit and $m = \mathrm{ord}(x)$. -/
theorem pcDiag_mem (x : Kˣ) : pcDiag K x ∈ pcInvSubgroup K := by
  have e : x = (x * unif K ^ (-ord K x)) * unif K ^ (ord K x) := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hv : valuation K ((x * unif K ^ (-ord K x) : Kˣ) : K) = 1 :=
    (valuation_eq_one_iff (Units.ne_zero _)).2 (ord_mul_unif_zpow x)
  have ht : pcDiag K (unif K) = weyl * pcEta K := Units.ext (by rw [pcDiag_val, pcWeyl_eta_val])
  rw [e, map_mul, map_zpow]
  refine (pcInvSubgroup K).mul_mem (pcMaxCompact_le (pcDiag_mem_maxCompact hv)) ?_
  refine zpow_mem ?_ _
  rw [ht]
  exact (pcInvSubgroup K).mul_mem (pcMaxCompact_le pcWeyl_mem) pcEta_mem

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Conjugation of $n(b)$ by $\mathrm{diag}(a, 1)$ is $n(ab)$. -/
theorem pcDiag_conj_unip (a : Kˣ) (b : K) :
    pcDiag K a * unip b * (pcDiag K a)⁻¹ = unip ((a : K) * b) := by
  refine Units.ext ?_
  rw [← map_inv, Units.val_mul, Units.val_mul, pcDiag_val, pcDiag_val, unip_val, unip_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Each element $n(y)$ preserves $\Lambda$. -/
theorem pcUnip_mem_inv (y : K) : unip y ∈ pcInvSubgroup K := by
  by_cases hy : y = 0
  · rw [hy, unip_zero]
    exact (pcInvSubgroup K).one_mem
  let a : Kˣ := unif K ^ ord K y
  have ha : (a : K) = (unif K : K) ^ ord K y := Units.val_zpow_eq_zpow_val _ _
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hv : valuation K ((a : K)⁻¹ * y) ≤ 1 := by
    rw [valuation_le_one_iff (mul_ne_zero (inv_ne_zero ha0) hy), ord_mul (inv_ne_zero ha0) hy,
      ord_inv ha0, ha, ord_zpow, ord_unif]
    omega
  have e : unip y = pcDiag K a * unip ((a : K)⁻¹ * y) * (pcDiag K a)⁻¹ := by
    rw [pcDiag_conj_unip, mul_inv_cancel_left₀ ha0]
  rw [e]
  exact (pcInvSubgroup K).mul_mem ((pcInvSubgroup K).mul_mem (pcDiag_mem a)
    (pcMaxCompact_le (pcUnip_mem hv))) ((pcInvSubgroup K).inv_mem (pcDiag_mem a))

/-- Each element of $B$ preserves $\Lambda$. It is $\mathrm{diag}(d, d) \, n(\beta / d) \, \mathrm{diag}(a / d, 1)$. -/
theorem pcBorel_mem {b : GL (Fin 2) K} (hb : b ∈ GL2.borel K) : b ∈ pcInvSubgroup K := by
  have h10 : b.1 1 0 = 0 := (mem_borel b).1 hb
  let a : Kˣ := Units.mk0 _ (val_zero_zero_ne_zero hb)
  let d : Kˣ := Units.mk0 _ (val_one_one_ne_zero hb)
  have hd : b.1 1 1 ≠ 0 := d.ne_zero
  have e : b = ((diagTorus K d d : torus K) : GL (Fin 2) K) * unip (b.1 0 1 / d) *
      pcDiag K (a / d) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, pcDiag_val, unip_val]
    change _ = !![(d : K), 0; 0, (d : K)] * _ * _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h10, a, d] <;> field_simp
  rw [e]
  exact (pcInvSubgroup K).mul_mem ((pcInvSubgroup K).mul_mem (pcScalar_mem d)
    (pcUnip_mem_inv _)) (pcDiag_mem _)

/-- **The invariance of $\Lambda$.** For each function $\varphi$ of modulus type and each $g \in GL_2(K)$, $\int_{GL_2(\mathcal{O}_K)} \varphi(kg) \, dk = \int_{GL_2(\mathcal{O}_K)} \varphi(k) \, dk$. The proof uses the Iwasawa decomposition $G = B \, GL_2(\mathcal{O}_K)$. -/
theorem pcIntInvariant_holds : PcIntInvariant K := by
  intro φ hφ g
  obtain ⟨b, hb, k, hk, rfl⟩ := iwasawa g
  exact (pcInvSubgroup K).mul_mem (pcBorel_mem hb) (pcMaxCompact_le hk) φ hφ

/-- **The contragredient of a principal series.** For smooth characters $\chi_1, \chi_2$ of $K^\times$, the contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is isomorphic to $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$. -/
theorem psContragredientIso_holds : PSContragredientIso K :=
  pcContragredientIso_of_invariant pcIntInvariant_holds

end Iwahori

end LocalGL2

end Langlands
