/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2TameTypes
import Langlands.Smooth.PrincipalSeries
import Mathlib.Algebra.Module.CharacterModule

/-!
# Compact induction from a type is supercuspidal

Let $G$ be a topological group, $J$ an open subgroup of $G$ that is compact modulo a central subgroup $Z$, and $\Lambda$ a character of $J$ with open kernel. Assume that each element of $G$ that intertwines $\Lambda$ lies in $J$. Let $\pi = c\text{-}\mathrm{Ind}_J^G \Lambda$ and let $f_0$ be the vector `Langlands.cIndBasic`, which is $\Lambda$ on $J$ and $0$ outside $J$. This file proves the following facts (Bushnell and Henniart, 10.1 and 11.4).

* The matrix coefficient $g \mapsto f_0(g)$ of $f_0$ and the evaluation $f \mapsto f(1)$ is not zero, and it has support in $J$. So its support is compact modulo $Z$.
* Let $K'$ be a compact open subgroup of $G$. For each $h \in G$ such that $\Lambda$ is trivial on $J \cap h K' h^{-1}$, there is a vector of $V^{K'}$ with support $J h K'$. If $V^{K'}$ has finite dimension, then these $h$ lie in finitely many double cosets $J t K'$.
* If $\pi$ is admissible and $G$ has a basis of compact open subgroups at $1$, then $\pi$ is supercuspidal: each matrix coefficient has support in $C Z$ for a compact set $C$.

For $G = GL_2(K)$ this reduces `Langlands.LocalGL2.CIndSupercuspidal` to the admissibility of $\pi$. The file takes the admissibility from the named input `Langlands.LocalGL2.CompactCoeffAdmissible`: an irreducible smooth representation of $GL_2(K)$ with a nonzero matrix coefficient of compact support modulo the centre is admissible. The representation $\pi$ is irreducible by `Langlands.isIrreducible_cInd`, and $f_0$ gives the coefficient.

The file also proves that $K$ has an additive character of level one.

## Main definitions

* `Langlands.TrivialOnConj`: $\Lambda$ is trivial on $J \cap h K' h^{-1}$.
* `Langlands.dcVec`: the vector of $V^{K'}$ with support $J h K'$ and the value $\Lambda(j)$ at $j h k$.
* `Langlands.cIndEvalOne`: the evaluation $f \mapsto f(1)$, as a smooth vector of the dual.
* `Langlands.LocalGL2.CompactCoeffAdmissible`: an irreducible smooth representation of $GL_2(K)$ with a nonzero matrix coefficient of compact support modulo the centre is admissible (Bushnell and Henniart, 10.1 and 10.2).

## Main results

* `Langlands.ρ_cIndBasic_of_mem`: $J$ acts on $f_0$ by $\Lambda$.
* `Langlands.coeff_cIndBasic_cIndEvalOne`: the coefficient of $f_0$ and the evaluation at $1$ is $g \mapsto f_0(g)$.
* `Langlands.le_of_forall_intertwines`: the central subgroup $Z$ lies in $J$.
* `Langlands.exists_isCompact_of_isCompactModCenter`: $J \subseteq C Z$ for a compact set $C$.
* `Langlands.exists_finset_of_finiteDimensional`: if $V^{K'}$ has finite dimension, then the $h$ with `TrivialOnConj` lie in finitely many double cosets $J t K'$.
* `Langlands.isSupercuspidal_cInd_of_isAdmissible`: an admissible $c\text{-}\mathrm{Ind}_J^G \Lambda$ is supercuspidal.
* `Langlands.LocalGL2.isOpen_maxCompact`, `Langlands.LocalGL2.exists_isCompact_isOpen_le`: $GL_2(\mathcal{O}_K)$ is open, and each open subgroup of $GL_2(K)$ contains a compact open subgroup.
* `Langlands.LocalGL2.isSupercuspidal_cInd_of_isAdmissible`: the same statement for $GL_2(K)$ and the scalar matrices.
* `Langlands.LocalGL2.isAdmissible_cInd`: `CompactCoeffAdmissible` gives the admissibility of $c\text{-}\mathrm{Ind}_J^{GL_2(K)} \Lambda$.
* `Langlands.LocalGL2.cIndSupercuspidal_of_compactCoeffAdmissible`: `CompactCoeffAdmissible` gives `Langlands.LocalGL2.CIndSupercuspidal`.
* `Langlands.LocalGL1.exists_isConductor_neg_one`: there is an additive character $\psi$ of $K$ of level one, that is, `IsConductor ψ (-1)`.

## Proof

Let $l$ be a smooth linear form on $\pi$ and let $K'$ be a compact open subgroup that fixes $l$. If $l(\pi(g) f_0) \neq 0$ and $j \in J$ with $k = g j g^{-1} \in K'$, then $l(\pi(g) f_0) = l(\pi(k) \pi(g) f_0) = \Lambda(j) l(\pi(g) f_0)$. So $\Lambda$ is trivial on $J \cap g^{-1} K' g$, and $g^{-1}$ lies in one of the finitely many double cosets $J t K'$ that carry a vector of $V^{K'}$. Then $g \in K' t^{-1} J \subseteq K' t^{-1} C_J Z$. A general vector is a finite sum of translates $\pi(s^{-1}) f_0$, so its coefficients have support in a finite union of such sets.

The vectors with support $J h K'$ for distinct double cosets are linearly independent, because the vector for $J h K'$ is $1$ at $h$ and $0$ on the other double cosets. So only finitely many double cosets carry them when $V^{K'}$ has finite dimension.

For the additive character, let $\mathfrak{p}$ be the maximal ideal. The element $1$ is not zero in $K / \mathfrak{p}$. A character of $K / \mathfrak{p}$ with values in $\mathbb{Q} / \mathbb{Z}$ that is not zero at $1$ exists, because $\mathbb{Q} / \mathbb{Z}$ is an injective cogenerator. The composite with $x \mapsto e^{2 \pi i x}$ is trivial on $\mathfrak{p}$ and not trivial on $\mathcal{O}_K$.

## Still open

* A proof of `Langlands.LocalGL2.CompactCoeffAdmissible`. In Bushnell and Henniart it follows from the theory of cuspidal representations and Jacquet modules (10.1 and 10.2, with chapter 2). A direct proof for $c\text{-}\mathrm{Ind}_J^G \Lambda$ must show that only finitely many double cosets $J h K'$ have $\Lambda$ trivial on $J \cap h K' h^{-1}$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, Springer, 2006, §§10 and 11.
-/

namespace Langlands

universe w

open SmoothRep

open scoped Pointwise

section General

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {J : Subgroup G} {Λ : J →* ℂˣ}

/-- The group $J$ acts on the vector $f_0$ by $\Lambda$: $\pi(j) f_0 = \Lambda(j) f_0$. -/
theorem ρ_cIndBasic_of_mem (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) (j : J) :
    (cInd J Λ).ρ j (cIndBasic J Λ hJ hΛ) = (Λ j : ℂ) • cIndBasic J Λ hJ hΛ := by
  refine cInd.ext fun x => ?_
  rw [cInd.toFun_ρ, cInd.toFun_smul, cInd.toFun_cIndBasic]
  by_cases hx : x ∈ J
  · rw [cIndBasicFun_of_mem J Λ (J.mul_mem hx j.2), cIndBasicFun_of_mem J Λ hx]
    have e : (⟨x * j, J.mul_mem hx j.2⟩ : J) = ⟨x, hx⟩ * j := rfl
    rw [e, map_mul, Units.val_mul, mul_comm]
  · rw [cIndBasicFun_of_not_mem J Λ hx,
      cIndBasicFun_of_not_mem J Λ fun h => hx ((J.mul_mem_cancel_right j.2).1 h), mul_zero]

variable (J Λ) in
/-- The evaluation $f \mapsto f(1)$ is a smooth vector of the dual of $c\text{-}\mathrm{Ind}_J^G \Lambda$: it is fixed by the kernel of $\Lambda$, which is open. -/
theorem toFunLin_one_mem_smoothVectors (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    cInd.toFunLin J Λ 1 ∈ smoothVectors (cInd J Λ).ρ.dual := by
  change IsOpen (vecStabilizer (cInd J Λ).ρ.dual (cInd.toFunLin J Λ 1) : Set G)
  refine Subgroup.isOpen_mono (H₁ := Λ.ker.map J.subtype) ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [mem_vecStabilizer]
    refine LinearMap.ext fun f => ?_
    change cInd.toFun ((cInd J Λ).ρ (k : G)⁻¹ f) 1 = cInd.toFun f 1
    have h := cInd.toFun_mul_left f k⁻¹ 1
    rw [mul_one, map_inv, MonoidHom.mem_ker.1 hk, inv_one, Units.val_one, one_mul] at h
    rw [cInd.toFun_ρ, one_mul]
    simpa using h
  · rw [Subgroup.coe_map]
    exact hJ.isOpenMap_subtype_val _ hΛ

variable (J Λ) in
/-- The evaluation $f \mapsto f(1)$, as a smooth vector of the dual of $c\text{-}\mathrm{Ind}_J^G \Lambda$. -/
noncomputable def cIndEvalOne (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) :
    smoothVectors (cInd J Λ).ρ.dual :=
  ⟨cInd.toFunLin J Λ 1, toFunLin_one_mem_smoothVectors J Λ hJ hΛ⟩

/-- The matrix coefficient of $f_0$ and the evaluation at $1$ is $g \mapsto f_0(g)$. -/
theorem coeff_cIndBasic_cIndEvalOne (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))
    (g : G) : (cInd J Λ).coeff (cIndBasic J Λ hJ hΛ) (cIndEvalOne J Λ hJ hΛ) g =
      cIndBasicFun J Λ g := by
  change cInd.toFun ((cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ)) 1 = _
  rw [cInd.toFun_ρ, one_mul, cInd.toFun_cIndBasic]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If each element that intertwines $\Lambda$ lies in $J$, then each central subgroup $Z$ lies in $J$, because a central element intertwines $\Lambda$. -/
theorem le_of_forall_intertwines {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hI : ∀ g, Intertwines J Λ g → g ∈ J) : Z ≤ J := fun z hz => hI z fun x h => by
  have e : (⟨z * x * z⁻¹, h⟩ : J) = x := Subtype.ext (by
    change z * (x : G) * z⁻¹ = x
    rw [← Subgroup.mem_center_iff.1 (hZc hz) x, mul_inv_cancel_right])
  rw [e]

/-- Let $Z$ be a central subgroup and $K_0$ a compact open subgroup of $G$. If $J$ is compact modulo $Z$ in the form `IsCompactModCenter`, then $J \subseteq C Z$ for a compact set $C$. The set $C$ is $T K_0$ for a finite set $T$ of representatives of $J / (Z \cap J)(K_0 \cap J)$. -/
theorem exists_isCompact_of_isCompactModCenter {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    {K₀ : Subgroup G} (hK₀ : IsCompact (K₀ : Set G)) (hK₀o : IsOpen (K₀ : Set G))
    (hc : IsCompactModCenter J Z) :
    ∃ C : Set G, IsCompact C ∧ ∀ j ∈ J, ∃ c ∈ C, ∃ z ∈ Z, j = c * z := by
  classical
  let U : Subgroup J := K₀.subgroupOf J
  have hU : IsOpen (U : Set J) := hK₀o.preimage continuous_subtype_val
  let Z' : Subgroup J := Z.subgroupOf J
  have : Z'.Normal := Subgroup.normal_of_le_center fun z hz => Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hZc hz) g)
  have : (Z' ⊔ U).FiniteIndex := hc U hU
  let : Fintype (J ⧸ (Z' ⊔ U)) := Fintype.ofFinite _
  let T : Finset G := Finset.univ.image fun q : J ⧸ (Z' ⊔ U) => ((q.out : J) : G)
  refine ⟨(T : Set G) * (K₀ : Set G), T.finite_toSet.isCompact.mul hK₀, fun j hj => ?_⟩
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul (Z' ⊔ U) (⟨j, hj⟩ : J)
  obtain ⟨z, hz, u, hu, hzu⟩ := Subgroup.mem_sup_of_normal_left.1 ((Z' ⊔ U).inv_mem b.2)
  set o : J := (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ (Z' ⊔ U)).out with ho
  have h1 : (⟨j, hj⟩ : J) = o * z * u := by
    rw [mul_assoc, hzu, hb]
    group
  have h2 : j = (o : G) * z * u := congrArg Subtype.val h1
  have hzc : (z : G) ∈ Subgroup.center G := hZc (Subgroup.mem_subgroupOf.1 hz)
  refine ⟨(o : G) * u, Set.mul_mem_mul (Finset.mem_coe.2 (Finset.mem_image_of_mem _
    (Finset.mem_univ _))) (Subgroup.mem_subgroupOf.1 hu), z, Subgroup.mem_subgroupOf.1 hz, ?_⟩
  rw [h2, mul_assoc, mul_assoc, Subgroup.mem_center_iff.1 hzc]

variable (J Λ) in
/-- The character $\Lambda$ is trivial on $J \cap h K' h^{-1}$: each $j \in J$ with $h^{-1} j h \in K'$ has $\Lambda(j) = 1$. Exactly then the double coset $J h K'$ carries a nonzero vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ fixed by $K'$. -/
def TrivialOnConj (K' : Subgroup G) (h : G) : Prop :=
  ∀ j : J, h⁻¹ * j * h ∈ K' → Λ j = 1

open scoped Classical in
variable (J Λ) in
/-- The function on $G$ with support $J h K'$ and the value $\Lambda(j)$ at $j h k$. It is well defined when `TrivialOnConj J Λ K' h` holds. -/
noncomputable def dcFun (K' : Subgroup G) (h x : G) : ℂ :=
  if hx : ∃ j : J, ∃ k ∈ K', x = j * h * k then (Λ hx.choose : ℂ) else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The value of `dcFun` at $j h k$ is $\Lambda(j)$. -/
theorem dcFun_eq {K' : Subgroup G} {h : G} (hh : TrivialOnConj J Λ K' h) {x : G} {j : J} {k : G}
    (hk : k ∈ K') (hx : x = j * h * k) : dcFun J Λ K' h x = Λ j := by
  have hx' : ∃ j : J, ∃ k ∈ K', x = j * h * k := ⟨j, k, hk, hx⟩
  rw [dcFun, dite_eq_left hx']
  obtain ⟨k', hk', hx''⟩ := hx'.choose_spec
  set j' := hx'.choose
  have heq : (j : G) * h * k = j' * h * k' := hx.symm.trans hx''
  have hj' : (j' : G) = j * h * k * k'⁻¹ * h⁻¹ := by
    rw [heq]
    group
  have h1 : Λ (j⁻¹ * j') = 1 := hh _ (by
    have e : h⁻¹ * ((j⁻¹ * j' : J) : G) * h = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, hj']
      group
    rw [e]
    exact K'.mul_mem hk (K'.inv_mem hk'))
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The function `dcFun` is zero outside $J h K'$. -/
theorem dcFun_of_not_mem {K' : Subgroup G} {h x : G}
    (hx : ¬ ∃ j : J, ∃ k ∈ K', x = j * h * k) :
    dcFun J Λ K' h x = 0 := by
  rw [dcFun, dite_eq_right hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The function `dcFun` is invariant on the right under $K'$. -/
theorem dcFun_mul_right {K' : Subgroup G} {h : G} (hh : TrivialOnConj J Λ K' h) (x : G) {u : G}
    (hu : u ∈ K') : dcFun J Λ K' h (x * u) = dcFun J Λ K' h x := by
  by_cases hx : ∃ j : J, ∃ k ∈ K', x = j * h * k
  · obtain ⟨j, k, hk, rfl⟩ := hx
    rw [dcFun_eq hh hk rfl, dcFun_eq (j := j) hh (K'.mul_mem hk hu) (by group)]
  · have hx' : ¬ ∃ j : J, ∃ k ∈ K', x * u = j * h * k := by
      rintro ⟨j, k, hk, e⟩
      refine hx ⟨j, k * u⁻¹, K'.mul_mem hk (K'.inv_mem hu), ?_⟩
      rw [← mul_assoc, ← e]
      group
    rw [dcFun_of_not_mem hx, dcFun_of_not_mem hx']

/-- For a compact open subgroup $K'$ and `TrivialOnConj J Λ K' h`, the function `dcFun` lies in $c\text{-}\mathrm{Ind}_J^G \Lambda$. Its support $J h K'$ is a finite union of cosets $J h k$, because $K' \cap h^{-1} J h$ is open in the compact group $K'$. -/
theorem dcFun_mem {K' : Subgroup G} (hK' : IsCompact (K' : Set G)) (hK'o : IsOpen (K' : Set G))
    (hJ : IsOpen (J : Set G)) {h : G} (hh : TrivialOnConj J Λ K' h) :
    dcFun J Λ K' h ∈ cIndSpace J Λ := by
  classical
  refine ⟨fun j₀ x => ?_, ⟨K', hK'o, fun x u hu => dcFun_mul_right hh x hu⟩, ?_⟩
  · by_cases hx : ∃ j : J, ∃ k ∈ K', x = j * h * k
    · obtain ⟨j, k, hk, rfl⟩ := hx
      rw [dcFun_eq hh hk rfl, dcFun_eq (j := j₀ * j) hh hk (by rw [Subgroup.coe_mul]; group),
        map_mul, Units.val_mul]
    · have hx' : ¬ ∃ j : J, ∃ k ∈ K', (j₀ : G) * x = j * h * k := by
        rintro ⟨j, k, hk, e⟩
        refine hx ⟨j₀⁻¹ * j, k, hk, ?_⟩
        rw [Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc, mul_assoc, ← mul_assoc _ h, ← e]
        group
      rw [dcFun_of_not_mem hx, dcFun_of_not_mem hx', mul_zero]
  · let L : Subgroup K' := (J.comap (MulAut.conj h).toMonoidHom).subgroupOf K'
    have : CompactSpace K' := isCompact_iff_compactSpace.1 hK'
    have hL : IsOpen (L : Set K') := (isOpen_comap_conj hJ h).preimage continuous_subtype_val
    have : Finite (K' ⧸ L) := Subgroup.quotient_finite_of_isOpen L hL
    let : Fintype (K' ⧸ L) := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : K' ⧸ L => h * ((q.out : K') : G)⁻¹, fun x hx => ?_⟩
    have hx' : ∃ j : J, ∃ k ∈ K', x = j * h * k := by
      by_contra hc
      exact hx (dcFun_of_not_mem hc)
    obtain ⟨j, k, hk, rfl⟩ := hx'
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L (⟨k, hk⟩ : K')⁻¹
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ
      (((⟨k, hk⟩ : K')⁻¹ : K') : K' ⧸ L)), ?_⟩
    have hl' : h * ((l : K') : G) * h⁻¹ ∈ J := by
      have := l.2
      rwa [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at this
    rw [hl]
    convert J.mul_mem j.2 hl' using 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group

variable (J Λ) in
/-- The vector of $c\text{-}\mathrm{Ind}_J^G \Lambda$ with support $J h K'$ and the value $\Lambda(j)$ at $j h k$, for a compact open subgroup $K'$ and `TrivialOnConj J Λ K' h`. -/
noncomputable def dcVec {K' : Subgroup G} (hK' : IsCompact (K' : Set G))
    (hK'o : IsOpen (K' : Set G)) (hJ : IsOpen (J : Set G)) {h : G}
    (hh : TrivialOnConj J Λ K' h) : (cInd J Λ).V :=
  (⟨dcFun J Λ K' h, dcFun_mem hK' hK'o hJ hh⟩ : cIndSpace J Λ)

/-- The vector `dcVec` is fixed by $K'$. -/
theorem dcVec_mem_fixedVectors {K' : Subgroup G} (hK' : IsCompact (K' : Set G))
    (hK'o : IsOpen (K' : Set G)) (hJ : IsOpen (J : Set G)) {h : G}
    (hh : TrivialOnConj J Λ K' h) : dcVec J Λ hK' hK'o hJ hh ∈ fixedVectors (cInd J Λ).ρ K' :=
  fun _ hk => cInd.ext fun x => dcFun_mul_right hh x hk

/-- Let $K'$ be a compact open subgroup and assume that $V^{K'}$ has finite dimension, where $V = c\text{-}\mathrm{Ind}_J^G \Lambda$. Then there is a finite set $T$ such that each $h$ with `TrivialOnConj J Λ K' h` lies in a double coset $J t K'$ with $t \in T$. The vectors `dcVec` for distinct double cosets are linearly independent. -/
theorem exists_finset_of_finiteDimensional {K' : Subgroup G} (hK' : IsCompact (K' : Set G))
    (hK'o : IsOpen (K' : Set G)) (hJ : IsOpen (J : Set G))
    (hfd : FiniteDimensional ℂ (fixedVectors (cInd J Λ).ρ K')) :
    ∃ T : Finset G, ∀ h, TrivialOnConj J Λ K' h →
      ∃ t ∈ T, ∃ j ∈ J, ∃ k ∈ K', h = j * t * k := by
  classical
  let P := {q : DoubleCoset.Quotient (J : Set G) K' //
    ∃ h, DoubleCoset.mk J K' h = q ∧ TrivialOnConj J Λ K' h}
  let r : P → G := fun q => q.2.choose
  have hr : ∀ q : P, DoubleCoset.mk J K' (r q) = q.1 ∧ TrivialOnConj J Λ K' (r q) :=
    fun q => q.2.choose_spec
  let v : P → fixedVectors (cInd J Λ).ρ K' := fun q =>
    ⟨dcVec J Λ hK' hK'o hJ (hr q).2, dcVec_mem_fixedVectors hK' hK'o hJ (hr q).2⟩
  have hval : ∀ q q' : P, cInd.toFun (v q : (cInd J Λ).V) (r q') = if q = q' then 1 else 0 := by
    intro q q'
    change dcFun J Λ K' (r q) (r q') = _
    split_ifs with hqq
    · subst hqq
      rw [dcFun_eq (j := 1) (hr q).2 K'.one_mem (by simp), map_one, Units.val_one]
    · refine dcFun_of_not_mem fun ⟨j, k, hk, e⟩ => hqq (Subtype.ext ?_)
      rw [← (hr q).1, ← (hr q').1]
      exact DoubleCoset.eq.2 ⟨j, j.2, k, hk, e⟩
  have hv : LinearIndependent ℂ v := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have h1 := congrArg (fun w : fixedVectors (cInd J Λ).ρ K' =>
      cInd.toFun (w : (cInd J Λ).V) (r i)) hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, cInd.toFun_sum, cInd.toFun_smul, hval,
      mul_ite, mul_one, mul_zero, ZeroMemClass.coe_zero] at h1
    rw [Finset.sum_eq_single i (fun b _ hb => ite_eq_right hb) (fun h => absurd hi h),
      ite_eq_left rfl] at h1
    exact h1
  have : Finite P := hv.finite_of_isNoetherian
  let : Fintype P := Fintype.ofFinite P
  refine ⟨Finset.univ.image r, fun h hh => ?_⟩
  let q : P := ⟨DoubleCoset.mk J K' h, h, rfl, hh⟩
  obtain ⟨j, hj, k, hk, e⟩ := DoubleCoset.eq.1 (hr q).1
  exact ⟨r q, Finset.mem_image_of_mem _ (Finset.mem_univ _), j, hj, k, hk, e⟩

omit [IsTopologicalGroup G] in
/-- If $k^{-1}$ fixes a linear form $l$ for the dual action, then $l(\pi(k) w) = l(w)$. -/
theorem apply_ρ_of_inv_mem_vecStabilizer {π : SmoothRep G} {l : Module.Dual ℂ π.V} {k : G}
    (hk : k⁻¹ ∈ vecStabilizer π.ρ.dual l) (w : π.V) : l (π.ρ k w) = l w := by
  rw [mem_vecStabilizer] at hk
  have h := congrArg (fun m : Module.Dual ℂ π.V => m w) hk
  change l (π.ρ k⁻¹⁻¹ w) = l w at h
  rwa [inv_inv] at h

/-- Let $l$ be a linear form fixed by $K'$. If $l(\pi(g) f_0) \neq 0$, then $\Lambda$ is trivial on $J \cap g^{-1} K' g$. -/
theorem trivialOnConj_of_ne_zero (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J))
    {K' : Subgroup G} {l : Module.Dual ℂ (cInd J Λ).V}
    (hl : K' ≤ vecStabilizer (cInd J Λ).ρ.dual l) {g : G}
    (hg : l ((cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ)) ≠ 0) : TrivialOnConj J Λ K' g⁻¹ := by
  intro j hj
  rw [inv_inv] at hj
  have h1 := apply_ρ_of_inv_mem_vecStabilizer (hl (K'.inv_mem hj))
    ((cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ))
  have h2 : (cInd J Λ).ρ (g * j * g⁻¹) ((cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ)) =
      (Λ j : ℂ) • (cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ) := by
    rw [← Module.End.mul_apply, ← map_mul, show g * j * g⁻¹ * g = g * j by group, map_mul,
      Module.End.mul_apply, ρ_cIndBasic_of_mem, map_smul]
  rw [h2, map_smul, smul_eq_mul] at h1
  exact Units.ext (mul_right_cancel₀ hg (h1.trans (one_mul _).symm))

/-- **Admissible compact inductions are supercuspidal** (Bushnell and Henniart, 10.1 and 11.4). Let $\iota : Z \to G$ have central image, and assume that each open subgroup of $G$ contains a compact open subgroup. Let $J$ be open and compact modulo $\iota(Z)$, and $\Lambda$ a character of $J$ with open kernel. If $c\text{-}\mathrm{Ind}_J^G \Lambda$ is admissible, then it is supercuspidal: each matrix coefficient has support in $C \iota(Z)$ for a compact set $C$. -/
theorem isSupercuspidal_cInd_of_isAdmissible {Z : Type*} [Group Z] (ι : Z →* G)
    (hι : ι.range ≤ Subgroup.center G)
    (hK : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ K' : Subgroup G, K' ≤ U ∧ IsOpen (K' : Set G) ∧ IsCompact (K' : Set G))
    (hJ : IsOpen (J : Set G)) (hΛ : IsOpen (Λ.ker : Set J)) (hc : IsCompactModCenter J ι.range)
    (hadm : (cInd J Λ).IsAdmissible) : (cInd J Λ).IsSupercuspidal ι := by
  classical
  intro v l
  obtain ⟨K₀, -, hK₀o, hK₀⟩ := hK ⊤ isOpen_univ
  obtain ⟨CJ, hCJ, hCJmem⟩ := exists_isCompact_of_isCompactModCenter hι hK₀ hK₀o hc
  obtain ⟨K', hK'l, hK'o, hK'⟩ := hK _ l.2
  obtain ⟨T, hT⟩ := exists_finset_of_finiteDimensional hK' hK'o hJ (hadm K' hK'o)
  let C₁ : Set G := (K' : Set G) * ((T.image (·⁻¹) : Finset G) : Set G) * CJ
  have hC₁ : IsCompact C₁ := (hK'.mul (Finset.finite_toSet _).isCompact).mul hCJ
  have key : ∀ g,
      (l : Module.Dual ℂ (cInd J Λ).V) ((cInd J Λ).ρ g (cIndBasic J Λ hJ hΛ)) ≠ 0 →
      ∃ c ∈ C₁, ∃ z ∈ ι.range, g = c * z := by
    intro g hg
    obtain ⟨t, ht, j, hj, k, hk, e⟩ := hT g⁻¹ (trivialOnConj_of_ne_zero hJ hΛ hK'l hg)
    obtain ⟨c, hc, z, hz, hjc⟩ := hCJmem j⁻¹ (J.inv_mem hj)
    refine ⟨k⁻¹ * t⁻¹ * c, Set.mul_mem_mul (Set.mul_mem_mul (K'.inv_mem hk)
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ ht))) hc, z, hz, ?_⟩
    rw [mul_assoc (k⁻¹ * t⁻¹), ← hjc, ← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, ← e,
      inv_inv]
  obtain ⟨S, hS⟩ := eq_sum_translate_cIndBasic J Λ hJ hΛ v
  refine ⟨C₁ * (S : Set G), hC₁.mul S.finite_toSet.isCompact, fun g hg => ?_⟩
  unfold SmoothRep.coeff at hg
  rw [hS, map_sum, map_sum] at hg
  obtain ⟨s, hs, hs0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
  rw [map_smul, map_smul, smul_eq_mul] at hs0
  have hs1 := right_ne_zero_of_mul hs0
  rw [← Module.End.mul_apply, ← map_mul] at hs1
  obtain ⟨c, hc, _, ⟨z, rfl⟩, e⟩ := key _ hs1
  refine ⟨c * s, Set.mul_mem_mul hc (Finset.mem_coe.2 hs), z, ?_⟩
  have hz : ι z ∈ Subgroup.center G := hι ⟨z, rfl⟩
  calc g = g * s⁻¹ * s := by group
    _ = c * ι z * s := by rw [e]
    _ = c * s * ι z := by rw [mul_assoc, ← Subgroup.mem_center_iff.1 hz s, mul_assoc]

end General

end Langlands

namespace Langlands.LocalGL2

universe u

open SmoothRep Matrix ValuativeRel GL2

section GL2

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The congruence subgroup of level $1$ lies in $GL_2(\mathcal{O}_K)$. -/
theorem congruence_one_le_maxCompact :
    congruence K 1 one_ne_zero le_rfl ≤ maxCompact K := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) K, IsSmallMatrix 1 (M - 1) → IsIntegralMatrix M := by
    intro M hM i j
    have e : M i j = (M - 1) i j + (1 : Matrix (Fin 2) (Fin 2) K) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ (hM i j).le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  exact fun g hg => ⟨key _ hg.1, key _ hg.2⟩

/-- The subgroup $GL_2(\mathcal{O}_K)$ is open. -/
theorem isOpen_maxCompact : IsOpen (maxCompact K : Set (GL (Fin 2) K)) :=
  Subgroup.isOpen_mono congruence_one_le_maxCompact (isOpen_congruence _ _ _)

/-- Each open subgroup $U$ of $GL_2(K)$ contains a compact open subgroup, namely $U \cap GL_2(\mathcal{O}_K)$. -/
theorem exists_isCompact_isOpen_le (U : Subgroup (GL (Fin 2) K))
    (hU : IsOpen (U : Set (GL (Fin 2) K))) :
    ∃ K' : Subgroup (GL (Fin 2) K), K' ≤ U ∧ IsOpen (K' : Set (GL (Fin 2) K)) ∧
      IsCompact (K' : Set (GL (Fin 2) K)) :=
  ⟨U ⊓ maxCompact K, inf_le_left, by rw [Subgroup.coe_inf]; exact hU.inter isOpen_maxCompact,
    by
      rw [Subgroup.coe_inf]
      exact isCompact_maxCompact.inter_left (Subgroup.isClosed_of_isOpen U hU)⟩

/-- **Admissible compact inductions are supercuspidal** for $GL_2(K)$ (Bushnell and Henniart, 10.1 and 11.4). Let $J$ be an open subgroup of $GL_2(K)$ that is compact modulo the centre and $\Lambda$ a character of $J$ with open kernel. If $c\text{-}\mathrm{Ind}_J^{GL_2(K)} \Lambda$ is admissible, then it is supercuspidal. -/
theorem isSupercuspidal_cInd_of_isAdmissible {J : Subgroup (GL (Fin 2) K)} {Λ : J →* ℂˣ}
    (hJ : IsOpen (J : Set (GL (Fin 2) K))) (hΛ : IsOpen (Λ.ker : Set J))
    (hc : IsCompactModCenter J (scalarGL K 2).range) (hadm : (cInd J Λ).IsAdmissible) :
    (cInd J Λ).IsSupercuspidal (scalarGL K 2) :=
  Langlands.isSupercuspidal_cInd_of_isAdmissible (scalarGL K 2) range_scalarGL_le_center
    exists_isCompact_isOpen_le hJ hΛ hc hadm

variable (K) in
/-- **Irreducible representations with a compact coefficient are admissible** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 10.1 and 10.2; for $GL_n$ it is part of the theorem of Jacquet and Bernstein that each irreducible smooth representation is admissible). Let $\pi$ be an irreducible smooth representation of $GL_2(K)$. If $\pi$ has a matrix coefficient $g \mapsto \lambda(\pi(g) v)$, with $\lambda$ a smooth vector of the dual, that is not zero and has support in $C K^\times$ for a compact set $C$, then $\pi$ is admissible. -/
def CompactCoeffAdmissible : Prop :=
  ∀ π : SmoothRep (GL (Fin 2) K), π.IsIrreducible →
    ∀ (v : π.V) (l : smoothVectors π.ρ.dual), (∃ g, π.coeff v l g ≠ 0) →
      (∃ C : Set (GL (Fin 2) K), IsCompact C ∧
        ∀ g, π.coeff v l g ≠ 0 → ∃ c ∈ C, ∃ z, g = c * scalarGL K 2 z) →
      π.IsAdmissible

/-- The coefficient of $f_0$ and the evaluation at $1$ is not zero and has support in $C K^\times$ for a compact set $C$. -/
theorem exists_compact_coeff_cInd {J : Subgroup (GL (Fin 2) K)} {Λ : J →* ℂˣ}
    (hJ : IsOpen (J : Set (GL (Fin 2) K))) (hΛ : IsOpen (Λ.ker : Set J))
    (hc : IsCompactModCenter J (scalarGL K 2).range) :
    (∃ g, (cInd J Λ).coeff (cIndBasic J Λ hJ hΛ) (cIndEvalOne J Λ hJ hΛ) g ≠ 0) ∧
      ∃ C : Set (GL (Fin 2) K), IsCompact C ∧
        ∀ g, (cInd J Λ).coeff (cIndBasic J Λ hJ hΛ) (cIndEvalOne J Λ hJ hΛ) g ≠ 0 →
          ∃ c ∈ C, ∃ z, g = c * scalarGL K 2 z := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · rw [coeff_cIndBasic_cIndEvalOne, cIndBasicFun_of_mem J Λ J.one_mem]
    exact Units.ne_zero _
  · obtain ⟨C, hC, hCm⟩ := exists_isCompact_of_isCompactModCenter range_scalarGL_le_center
      isCompact_maxCompact isOpen_maxCompact hc
    refine ⟨C, hC, fun g hg => ?_⟩
    rw [coeff_cIndBasic_cIndEvalOne] at hg
    have hgJ : g ∈ J := by
      by_contra h
      exact hg (cIndBasicFun_of_not_mem J Λ h)
    obtain ⟨c, hcC, _, ⟨z, rfl⟩, e⟩ := hCm g hgJ
    exact ⟨c, hcC, z, e⟩

/-- **Admissibility of compact induction from a type**, given `CompactCoeffAdmissible`. Let $J$ be an open subgroup of $GL_2(K)$ that is compact modulo the centre and $\Lambda$ a character of $J$ with open kernel whose intertwining is $J$. Then $c\text{-}\mathrm{Ind}_J^{GL_2(K)} \Lambda$ is admissible: it is irreducible, and the coefficient of $f_0$ has compact support modulo the centre. -/
theorem isAdmissible_cInd (hca : CompactCoeffAdmissible K) {J : Subgroup (GL (Fin 2) K)}
    {Λ : J →* ℂˣ} (hJ : IsOpen (J : Set (GL (Fin 2) K))) (hΛ : IsOpen (Λ.ker : Set J))
    (hc : IsCompactModCenter J (scalarGL K 2).range) (hI : ∀ g, Intertwines J Λ g → g ∈ J) :
    (cInd J Λ).IsAdmissible :=
  hca _ (isIrreducible_cInd J Λ hJ hΛ range_scalarGL_le_center hc hI) _ _
    (exists_compact_coeff_cInd hJ hΛ hc).1 (exists_compact_coeff_cInd hJ hΛ hc).2

/-- **Compact induction from a type is supercuspidal** (Bushnell and Henniart, The local Langlands conjecture for GL(2), 11.4), given `CompactCoeffAdmissible`. -/
theorem cIndSupercuspidal_of_compactCoeffAdmissible (hca : CompactCoeffAdmissible K) :
    CIndSupercuspidal K := fun _ _ hJ hΛ hc hI =>
  ⟨isAdmissible_cInd hca hJ hΛ hc hI,
    isSupercuspidal_cInd_of_isAdmissible hJ hΛ hc (isAdmissible_cInd hca hJ hΛ hc hI)⟩

end GL2

end Langlands.LocalGL2

namespace Langlands.LocalGL1

universe u

open ValuativeRel

section LevelOne

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The homomorphism $\mathbb{Q} / \mathbb{Z} \to \mathbb{C}^\times$, $x \mapsto e^{2 \pi i x}$. -/
noncomputable def ratCircleExp : AddCircle (1 : ℚ) →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    { toFun := fun q => Additive.ofMul (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * q))
        (Complex.exp_ne_zero _))
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp
      map_add' := fun a b => by
        apply Additive.toMul.injective
        ext
        simp [mul_add, Complex.exp_add] }
    (by
      rintro _ ⟨n, rfl⟩
      rw [AddMonoidHom.mem_ker]
      apply Additive.toMul.injective
      ext
      simp only [zsmul_eq_mul, mul_one, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul,
        Units.val_mk0, Rat.cast_intCast, toMul_zero, Units.val_one]
      rw [show 2 * Real.pi * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n)

/-- The map $x \mapsto e^{2 \pi i x}$ on $\mathbb{Q} / \mathbb{Z}$ is $1$ only at $0$. -/
theorem ratCircleExp_eq_zero {a : AddCircle (1 : ℚ)} (h : ratCircleExp a = 0) : a = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H q =>
    have h1 : Complex.exp (2 * Real.pi * Complex.I * q) = 1 := by
      have := congrArg (fun x : Additive ℂˣ => ((Additive.toMul x : ℂˣ) : ℂ)) h
      simpa [ratCircleExp] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    have hq : (q : ℂ) = n := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ h2
      rw [hn]
      ring
    have hq' : q = n := by exact_mod_cast hq
    rw [QuotientAddGroup.eq_zero_iff, hq']
    exact ⟨n, by simp⟩

/-- **Existence of a character of level one.** Each nonarchimedean local field $K$ has an additive character $\psi$ that is trivial on $\mathfrak{p}$ and not trivial on $\mathcal{O}_K$, that is, `IsConductor ψ (-1)`. -/
theorem exists_isConductor_neg_one : ∃ ψ : AddChar K ℂ, IsConductor ψ (-1) := by
  let P : AddSubgroup K := ordBallAddSubgroup 1
  have h1 : (QuotientAddGroup.mk (1 : K) : K ⧸ P) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    have h' : (1 : K) ∈ ordBall K 1 := h
    rw [mem_ordBall_of_ne_zero one_ne_zero, ord_one] at h'
    omega
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero h1
  let e : K →+ Additive ℂˣ := ratCircleExp.comp (c.comp (QuotientAddGroup.mk' P))
  let ψ : AddChar K ℂ :=
    { toFun := fun x => ((Additive.toMul (e x) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp }
  refine ⟨ψ, ⟨fun x hx => ?_, ⟨1, ?_, fun h => hc ?_⟩⟩⟩
  · have hx' : (QuotientAddGroup.mk x : K ⧸ P) = 0 := (QuotientAddGroup.eq_zero_iff x).2 hx
    change ((Additive.toMul (ratCircleExp (c (QuotientAddGroup.mk x))) : ℂˣ) : ℂ) = 1
    rw [hx', map_zero, map_zero]
    rfl
  · rw [show (-(-1 : ℤ) - 1) = 0 by norm_num, mem_ordBall_of_ne_zero one_ne_zero, ord_one]
  · refine ratCircleExp_eq_zero ?_
    apply Additive.toMul.injective
    exact Units.ext h

end LevelOne

end Langlands.LocalGL1
