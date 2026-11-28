/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2PrincipalSeriesInputs

/-!
# Two of the principal series inputs

This file proves two of the six inputs in `Langlands.LocalGL2.PSInputProps`. The first is `Langlands.LocalGL2.SmoothDualExtends`: a smooth linear form on a subrepresentation extends to a smooth linear form on the whole representation. The proof averages a linear extension over a compact open subgroup with the Haar measure of mass $1$. The second is `Langlands.LocalGL2.PSSupercuspidalJacquet`: a supercuspidal representation of $GL_2(K)$ has zero Jacquet module. The proof uses Frobenius reciprocity, the Iwahori factorization of a small congruence subgroup and the elements $\mathrm{diag}(\varpi^k, 1)$.

Then the file reduces `Langlands.LocalGL2.PSInputProps` and `Langlands.LocalGL2.NonSupercuspidalInputs` to the four inputs that are still open.

## Main definitions

* `Langlands.LocalGL2.psAvgForm`: the average of a linear form over a compact subgroup.
* `Langlands.LocalGL2.psEvalOne`: the linear form $v \mapsto \Phi(v)(1)$ for a map $\Phi$ to a principal series.

## Main results

* `Langlands.LocalGL2.smoothDualExtends_holds`: smooth linear forms extend along injective maps.
* `Langlands.LocalGL2.psSupercuspidalJacquet_holds`: supercuspidal representations have zero Jacquet module.
* `Langlands.LocalGL2.psSubNotSupercuspidal_holds`: a subrepresentation of the principal series is not supercuspidal.
* `Langlands.LocalGL2.psSubContragredient_of_contragredientIso`: the contragredient input from `PSContragredientIso` alone.
* `Langlands.LocalGL2.psInputProps_of_open`: `PSInputProps` from the four open inputs.
* `Langlands.LocalGL2.nonSupercuspidalInputs_of_contragredient_lFactor`: `NonSupercuspidalInputs` from the four open inputs.

## Still open

The inputs `PSContragredientIso`, `PSLFactorIrreducible`, `PSLFactorDetChar` and `PSLFactorSteinberg` are not proved here. The first needs the invariant pairing of $\mathrm{Ind}(\chi)$ and $\mathrm{Ind}(\chi^{-1})$ by integration over $B \backslash G$. The other three need the computation of Godement-Jacquet zeta integrals.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Chapter 2.
-/

namespace Langlands

universe u

open Representation MeasureTheory Topology Filter

namespace LocalGL2

section Average

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a smooth representation $\pi$, a vector $v$ and a linear form $L$, the function $g \mapsto L(\pi(g)^{-1} v)$ is continuous. It is constant on the open cosets $\mathrm{Stab}(v) g$. -/
theorem psContinuous_form_inv (π : SmoothRep G) (L : Module.Dual ℂ π.V) (v : π.V) :
    Continuous fun g : G => L (π.ρ g⁻¹ v) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hopen : IsOpen {x : G | x * g⁻¹ ∈ vecStabilizer π.ρ v} :=
    (π.smooth v).preimage (continuous_id.mul continuous_const)
  have hmem : g ∈ {x : G | x * g⁻¹ ∈ vecStabilizer π.ρ v} := by
    simp only [Set.mem_ofPred_eq, mul_inv_cancel]
    exact one_mem _
  refine (continuousAt_const (y := L (π.ρ g⁻¹ v))).congr
    (Filter.eventually_of_mem (hopen.mem_nhds hmem) fun x hx => ?_)
  have hx' : π.ρ (x * g⁻¹) v = v := hx
  have hx'' : π.ρ (x * g⁻¹)⁻¹ v = v := by
    conv_lhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e : x⁻¹ = g⁻¹ * (x * g⁻¹)⁻¹ := by group
  change L (π.ρ g⁻¹ v) = L (π.ρ x⁻¹ v)
  rw [e, map_mul, Module.End.mul_apply, hx'']

/-- The average $v \mapsto \int_U L(\pi(u)^{-1} v) \, du$ of a linear form $L$ over a compact subgroup $U$, for the Haar measure of total mass $1$ on $U$. -/
noncomputable def psAvgForm (π : SmoothRep G) {U : Subgroup G} (hU : IsCompact (U : Set G))
    (L : Module.Dual ℂ π.V) : Module.Dual ℂ π.V :=
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  { toFun := fun v => ∫ u : U, L (π.ρ (u : G)⁻¹ v) ∂(Measure.haarMeasure ⊤)
    map_add' := fun v w => by
      have hi : ∀ x : π.V, Integrable (fun u : U => L (π.ρ (u : G)⁻¹ x))
          (Measure.haarMeasure ⊤) := fun x =>
        ((psContinuous_form_inv π L x).comp continuous_subtype_val).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      simp only [map_add]
      exact integral_add (hi v) (hi w)
    map_smul' := fun c v => by
      simp only [map_smul, smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul c _ }

/-- The average of $L$ over $U$ is invariant under $U$: $\bar L(\pi(u_0) v) = \bar L(v)$ for $u_0 \in U$. -/
theorem psAvgForm_ρ (π : SmoothRep G) {U : Subgroup G} (hU : IsCompact (U : Set G))
    (L : Module.Dual ℂ π.V) {u₀ : G} (hu₀ : u₀ ∈ U) (v : π.V) :
    psAvgForm π hU L (π.ρ u₀ v) = psAvgForm π hU L v := by
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  change ∫ u : U, L (π.ρ (u : G)⁻¹ (π.ρ u₀ v)) ∂(Measure.haarMeasure ⊤) =
    ∫ u : U, L (π.ρ (u : G)⁻¹ v) ∂(Measure.haarMeasure ⊤)
  rw [← integral_mul_left_eq_self (fun u : U => L (π.ρ (u : G)⁻¹ v)) (⟨u₀, hu₀⟩ : U)⁻¹]
  congr 1
  funext u
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  simp

/-- If $L(\pi(u)^{-1} v) = c$ for each $u \in U$, then the average of $L$ over $U$ takes the value $c$ at $v$. -/
theorem psAvgForm_eq_of_forall (π : SmoothRep G) {U : Subgroup G} (hU : IsCompact (U : Set G))
    (L : Module.Dual ℂ π.V) {v : π.V} {c : ℂ} (h : ∀ u ∈ U, L (π.ρ u⁻¹ v) = c) :
    psAvgForm π hU L v = c := by
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  change ∫ u : U, L (π.ρ (u : G)⁻¹ v) ∂(Measure.haarMeasure ⊤) = c
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u : U => h u u.2), integral_const]
  have h1 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts U)) Set.univ = 1 := by
    rw [← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]
  simp [Measure.real, h1]

end Average

section DualExtends

open GL2 SmoothRep

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Each open subgroup $H$ of $GL_2(K)$ contains the compact open subgroup $H \cap U_1$, for the congruence subgroup $U_1$ of level $1$. -/
theorem psExists_compact_open_le {H : Subgroup (GL (Fin 2) K)}
    (hH : IsOpen (H : Set (GL (Fin 2) K))) :
    ∃ U : Subgroup (GL (Fin 2) K), U ≤ H ∧ IsOpen (U : Set (GL (Fin 2) K)) ∧
      IsCompact (U : Set (GL (Fin 2) K)) :=
  ⟨H ⊓ congruence K 1 one_ne_zero le_rfl, inf_le_left, by
    rw [Subgroup.coe_inf]; exact hH.inter (isOpen_congruence _ _ _), by
    rw [Subgroup.coe_inf]
    exact (isCompact_congruence _ _).inter_left (Subgroup.isClosed_of_isOpen H hH)⟩

variable (K) in
/-- **Smooth linear forms extend** along injective maps of smooth representations of $GL_2(K)$. This is `Langlands.LocalGL2.SmoothDualExtends`. Let $\lambda$ be a smooth linear form on $\sigma$, fixed by a compact open subgroup $U$. Take a left inverse $g$ of $f$ and put $L = \lambda \circ g$. The average $\lambda'(v) = \int_U L(\pi(u)^{-1} v) \, du$ is fixed by $U$, and $\lambda'(f(w)) = \lambda(w)$ because $\lambda$ is fixed by $U$. -/
theorem smoothDualExtends_holds : SmoothDualExtends K := by
  intro σ π f hf hfg l hl
  obtain ⟨U, hUl, hUo, hUc⟩ := psExists_compact_open_le (H := vecStabilizer σ.ρ.dual l) hl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hf)
  have hlU : ∀ u ∈ U, ∀ w, l (σ.ρ u⁻¹ w) = l w := fun u hu w =>
    LinearMap.congr_fun (hUl hu) w
  refine ⟨psAvgForm π hUc (l ∘ₗ g), Subgroup.isOpen_mono (H₁ := U) (fun u hu => ?_) hUo, ?_⟩
  · rw [mem_vecStabilizer]
    refine LinearMap.ext fun v => ?_
    rw [Representation.dual_apply]
    exact psAvgForm_ρ π hUc _ (U.inv_mem hu) v
  · refine LinearMap.ext fun w => psAvgForm_eq_of_forall π hUc _ fun u hu => ?_
    rw [LinearMap.comp_apply, ← hfg, ← LinearMap.comp_apply g f, hg, LinearMap.id_apply,
      hlU u hu]

end DualExtends

section Jacquet

open GL2 SmoothRep LocalGL1 ValuativeRel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The function $g \mapsto g_{22} (g^{-1})_{11}$ on $GL_2(K)$. It does not change under multiplication by the center. -/
noncomputable def psCenterInv (g : GL (Fin 2) K) : K :=
  g.1 1 1 * (g⁻¹).1 0 0

/-- The function $g \mapsto g_{22} (g^{-1})_{11}$ is continuous on $GL_2(K)$. -/
theorem psContinuous_centerInv : Continuous (psCenterInv : GL (Fin 2) K → K) :=
  (Units.continuous_val.matrix_elem 1 1).mul
    ((Units.continuous_val.comp continuous_inv).matrix_elem 0 0)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The function `psCenterInv` does not change under multiplication by a scalar matrix. -/
theorem psCenterInv_mul_scalar (c : GL (Fin 2) K) (z : Kˣ) :
    psCenterInv (c * scalarGL K 2 z) = psCenterInv c := by
  have hz : ((scalarGL K 2 z)⁻¹ : GL (Fin 2) K) = scalarGL K 2 z⁻¹ := (map_inv _ z).symm
  unfold psCenterInv
  rw [_root_.mul_inv_rev, hz, Units.val_mul, Units.val_mul]
  simp only [scalarGL, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination (c.1 1 1 * (c⁻¹).1 0 0) * Units.inv_mul z

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The value of `psCenterInv` at $\mathrm{diag}(u, 1)$ is $u^{-1}$. -/
theorem psCenterInv_diag (u : Kˣ) :
    psCenterInv ((diagTorusHom (u, 1) : torus K) : GL (Fin 2) K) = ((u⁻¹ : Kˣ) : K) := by
  unfold psCenterInv
  change (1 : K) * ((u⁻¹ : Kˣ) : K) = _
  rw [one_mul]

/-- The elements $\mathrm{diag}(\varpi^k, 1)$, $k \in \mathbb{N}$, are not in $C Z$ for one compact set $C$. -/
theorem psNot_forall_diag_mem {C : Set (GL (Fin 2) K)} (hC : IsCompact C) :
    ¬ ∀ k : ℕ, ∃ c ∈ C, ∃ z : Kˣ,
      ((diagTorusHom (unif K ^ k, 1) : torus K) : GL (Fin 2) K) = c * scalarGL K 2 z := by
  intro h
  have hS := hC.image psContinuous_centerInv
  obtain ⟨n, hn⟩ := hS.elim_directed_cover (fun n : ℕ => ordBall K (-(n : ℤ)))
    (fun n => isOpen_ordBall _) (fun z _ => by
      by_cases hz : z = 0
      · exact Set.mem_iUnion.2 ⟨0, hz ▸ zero_mem_ordBall _⟩
      · refine Set.mem_iUnion.2 ⟨(-ord K z).toNat, (mem_ordBall_of_ne_zero hz).2 ?_⟩
        omega)
    (fun i j => ⟨max i j, ordBall_anti (by omega), ordBall_anti (by omega)⟩)
  obtain ⟨c, hc, z, e⟩ := h (n + 1)
  have hmem : psCenterInv c ∈ ordBall K (-(n : ℤ)) := hn ⟨c, hc, rfl⟩
  rw [← psCenterInv_mul_scalar c z, ← e, psCenterInv_diag] at hmem
  rw [mem_ordBall_of_ne_zero (Units.ne_zero _), Units.val_inv_eq_inv_val, ord_inv (Units.ne_zero _),
    Units.val_pow_eq_pow_val, ← zpow_natCast, ord_zpow, ord_unif] at hmem
  push_cast at hmem
  omega

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The congruence subgroups decrease with the level. -/
theorem psCongruence_mono {γ γ' : ValueGroupWithZero K} {hγ0 : γ ≠ 0} {hγ1 : γ ≤ 1}
    {hγ0' : γ' ≠ 0} {hγ1' : γ' ≤ 1} (h : γ ≤ γ') :
    congruence K γ hγ0 hγ1 ≤ congruence K γ' hγ0' hγ1' :=
  fun _ hg => ⟨fun i j => (hg.1 i j).trans_le h, fun i j => (hg.2 i j).trans_le h⟩

/-- The linear form $v \mapsto \Phi(v)(1)$ on $\pi$, for a map $\Phi$ from $\pi$ to a principal series. -/
noncomputable def psEvalOne {π : SmoothRep (GL (Fin 2) K)} {α₁ α₂ : Kˣ →* ℂˣ}
    {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}
    (Φ : IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ) : Module.Dual ℂ π.V where
  toFun v := (ind.toFun (Φ v) 1).down
  map_add' v w := by rw [map_add]; rfl
  map_smul' c v := by rw [map_smul]; rfl

/-- The form $\mu = $ `psEvalOne` $\Phi$ satisfies $\mu(\pi(g) v) = \Phi(v)(g)$. -/
theorem psEvalOne_ρ {π : SmoothRep (GL (Fin 2) K)} {α₁ α₂ : Kˣ →* ℂˣ}
    {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}
    (Φ : IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ) (g : GL (Fin 2) K) (v : π.V) :
    psEvalOne Φ (π.ρ g v) = (ind.toFun (Φ v) g).down := by
  change (ind.toFun (Φ (π.ρ g v)) 1).down = _
  rw [IntertwiningMap.isIntertwining]
  change (ind.toFun (Φ v) (1 * g)).down = _
  rw [one_mul]

/-- The form $\mu = $ `psEvalOne` $\Phi$ satisfies $\mu(\pi(b) v) = \chi(b) \mu(v)$ for $b$ in the Borel subgroup. -/
theorem psEvalOne_borel {π : SmoothRep (GL (Fin 2) K)} {α₁ α₂ : Kˣ →* ℂˣ}
    {hα₁ : IsSmoothChar K α₁} {hα₂ : IsSmoothChar K α₂}
    (Φ : IntertwiningMap π.ρ (principalSeriesInd α₁ α₂ hα₁ hα₂).ρ) (b : GL2.borel K) (v : π.V) :
    psEvalOne Φ (π.ρ b v) = (borelChar α₁ α₂ b : ℂ) * psEvalOne Φ v := by
  rw [psEvalOne_ρ, ← mul_one (b : GL (Fin 2) K), principalSeriesInd_mul_left]
  rfl

variable (K) in
/-- **Supercuspidal representations have zero Jacquet module.** This is `Langlands.LocalGL2.PSSupercuspidalJacquet`. If $\pi_N \neq 0$, then Frobenius reciprocity gives an injective map $\Phi$ from $\pi$ to a principal series, and $\mu(v) = \Phi(v)(1)$ satisfies $\mu(\pi(b) v) = \chi(b) \mu(v)$ for $b \in B$. Take $v$ with $\mu(v) \neq 0$ and a small congruence subgroup $U$, and let $\lambda$ be the average of $\mu$ over $U$. The Iwahori factorization of $U$ gives $\lambda(\pi(t^k) v) = \chi(t)^k \mu(v) \neq 0$ for $t = \mathrm{diag}(\varpi, 1)$ and each $k \ge 0$. These elements $t^k$ are not in $C Z$ for a compact set $C$. -/
theorem psSupercuspidalJacquet_holds : PSSupercuspidalJacquet K := by
  intro π hsc
  by_contra hc
  obtain ⟨α₁, α₂, hα₁, hα₂, Φ, hΦ⟩ :=
    exists_injective_principalSeriesInd_of_isAdmissible π.1 π.2.1 π.2.2 hc
  -- a vector with `μ v ≠ 0`
  obtain ⟨v, hv⟩ : ∃ v, psEvalOne Φ v ≠ 0 := by
    have := π.2.1.1
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : π.1.V)
    have h1 : Φ v₀ ≠ 0 := fun h => hv₀ (hΦ (h.trans (map_zero Φ).symm))
    have h2 : ind.toFun (Φ v₀) ≠ 0 := fun h => h1 (ind.toFun_injective (h.trans rfl))
    obtain ⟨x, hx⟩ := Function.ne_iff.1 h2
    refine ⟨π.1.ρ x v₀, ?_⟩
    rw [psEvalOne_ρ]
    exact fun h => hx (ULift.ext h)
  -- the level
  obtain ⟨γ₀, hγ₀, hγ₁, hχ⟩ := exists_congruence_borelChar hα₁ hα₂
  have hO : IsOpen (lowerUnip ⁻¹' (vecStabilizer π.1.ρ v : Set (GL (Fin 2) K))) :=
    continuous_lowerUnip.isOpen_preimage _ (π.1.smooth v)
  have h0 : (0 : K) ∈ lowerUnip ⁻¹' (vecStabilizer π.1.ρ v : Set (GL (Fin 2) K)) := by
    rw [Set.mem_preimage, lowerUnip_zero]
    exact (vecStabilizer _ _).one_mem
  obtain ⟨δ, hδ⟩ := IsValuativeTopology.mem_nhds_iff'.1 (hO.mem_nhds h0)
  set γ := min γ₀ (δ : ValueGroupWithZero K) with hγ
  have hγ0 : γ ≠ 0 := by
    rw [← zero_lt_iff] at hγ₀ ⊢
    exact lt_min hγ₀ (zero_lt_iff.2 δ.ne_zero)
  have hγ1 : γ ≤ 1 := (min_le_left _ _).trans hγ₁
  set U := congruence K γ hγ0 hγ1
  have hUc : IsCompact (U : Set (GL (Fin 2) K)) := isCompact_congruence _ _
  set l := psAvgForm π.1 hUc (psEvalOne Φ)
  have hl : l ∈ smoothVectors π.1.ρ.dual := by
    refine Subgroup.isOpen_mono (H₁ := U) (fun u hu => ?_) (isOpen_congruence _ _ _)
    rw [mem_vecStabilizer]
    refine LinearMap.ext fun w => ?_
    rw [Representation.dual_apply]
    exact psAvgForm_ρ π.1 hUc _ (U.inv_mem hu) w
  obtain ⟨C, hC, hCs⟩ := hsc v ⟨l, hl⟩
  refine psNot_forall_diag_mem hC fun k => hCs _ ?_
  -- the coefficient at `t^k`
  set t : torus K := diagTorusHom (unif K ^ k, 1)
  have hval : valuation K ((unif K ^ k : Kˣ) : K) ≤ 1 := by
    rw [valuation_le_one_iff (Units.ne_zero _), Units.val_pow_eq_pow_val, ← zpow_natCast,
      ord_zpow, ord_unif]
    omega
  have key : ∀ u ∈ U, psEvalOne Φ (π.1.ρ u⁻¹ (π.1.ρ t v)) =
      (borelChar α₁ α₂ ⟨t, torus_le_borel t.2⟩ : ℂ) * psEvalOne Φ v := by
    intro u hu
    obtain ⟨x, y, hy, hb'⟩ := exists_unip_mul_torus_mul_lowerUnip hγ0 hγ1 (U.inv_mem hu)
    set b' := (unip x)⁻¹ * u⁻¹ * (lowerUnip y)⁻¹
    have hyU : lowerUnip y ∈ U := lowerUnip_mem_congruence hγ0 hγ1 hy
    have hxU : unip x ∈ U := by
      have e : unip x = u⁻¹ * (lowerUnip y)⁻¹ * b'⁻¹ := by simp [b']
      rw [e]
      exact U.mul_mem (U.mul_mem (U.inv_mem hu) (U.inv_mem hyU)) (U.inv_mem hb'.2)
    have hxB : unip x ∈ GL2.borel K := unipotent_le_borel (unip_mem x)
    have hbB : unip x * b' ∈ GL2.borel K := (GL2.borel K).mul_mem hxB (torus_le_borel hb'.1)
    have hbU : unip x * b' ∈ U := U.mul_mem hxU hb'.2
    have hb1 : borelChar α₁ α₂ ⟨_, hbB⟩ = 1 := hχ _ (psCongruence_mono (min_le_left _ _) hbU)
    have hfix : π.1.ρ (lowerUnip ((unif K ^ k : Kˣ) * y)) v = v := by
      refine hδ ?_
      change valuation K (_ - 0) < (δ : ValueGroupWithZero K)
      rw [sub_zero, map_mul]
      exact (mul_le_of_le_one_left' hval).trans_lt (hy.trans_le (min_le_right _ _))
    have e : u⁻¹ * (t : GL (Fin 2) K) =
        (⟨_, hbB⟩ * ⟨t, torus_le_borel t.2⟩ : GL2.borel K) *
          lowerUnip ((unif K ^ k : Kˣ) * y) := by
      rw [← diagTorusHom_inv_mul_lowerUnip_mul]
      simp only [Subgroup.coe_mul, b', t]
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfix,
      psEvalOne_borel, map_mul, hb1, one_mul]
  change l (π.1.ρ t v) ≠ 0
  rw [psAvgForm_eq_of_forall π.1 hUc _ key]
  exact mul_ne_zero (Units.ne_zero _) hv

end Jacquet

section Combination

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The six principal series inputs follow from the four inputs that are still open: the contragredient of the principal series and the three L-factor computations. -/
theorem psInputProps_of_open (hD : PSContragredientIso K) (h1 : PSLFactorIrreducible K)
    (h2 : PSLFactorDetChar K) (h3 : PSLFactorSteinberg K) : PSInputProps K :=
  ⟨psSupercuspidalJacquet_holds K, hD, smoothDualExtends_holds K, h1, h2, h3⟩

/-- The non-supercuspidal inputs follow from the contragredient of the principal series and the three L-factor computations. -/
theorem nonSupercuspidalInputs_of_contragredient_lFactor (hD : PSContragredientIso K)
    (h1 : PSLFactorIrreducible K) (h2 : PSLFactorDetChar K) (h3 : PSLFactorSteinberg K) :
    NonSupercuspidalInputs K :=
  nonSupercuspidalInputs_of_psInputProps (psInputProps_of_open K hD h1 h2 h3)

/-- **A subrepresentation of the principal series is not supercuspidal.** This is `Langlands.LocalGL2.PSSubNotSupercuspidal`, with no open input. -/
theorem psSubNotSupercuspidal_holds : PSSubNotSupercuspidal K :=
  psSubNotSupercuspidal_of (psSupercuspidalJacquet_holds K)

/-- The contragredient input `Langlands.LocalGL2.PSSubContragredient` follows from the contragredient of the principal series alone. -/
theorem psSubContragredient_of_contragredientIso (hD : PSContragredientIso K) :
    PSSubContragredient K :=
  psSubContragredient_of hD (smoothDualExtends_holds K)

end Combination

end LocalGL2

end Langlands
