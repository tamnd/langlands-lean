/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.WeilGroup.Degree

/-!
# The inertia subgroup of the Weil group

This file gives the checks F2 and F3 of spec 06 for the topology of the Weil group. The topology of $W_K$ is the coarsest topology that makes the inclusion in $G_K$ continuous and the action on $\bar k$ locally constant.

* `Langlands.WeilGroup.isCompact_inertia`: the inertia subgroup $I_K$ is compact. It is also open, by `Langlands.WeilGroup.isOpen_inertia`. This is the check F2.
* `Langlands.WeilGroup.not_isOpen_inertia_induced`: in the subspace topology from $G_K$, the inertia subgroup is not open. So the topology of $W_K$ is strictly finer than the subspace topology, and the wrong topology fails the check F2. This is the check F3.

The proof of the second result uses that $W_K$ is dense in $G_K$ and that the Frobenius has infinite order. If $I_K$ were open in the subspace topology, its closure in $G_K$ would be an open subgroup, so it would have finite index. Then $\mathrm{Gal}(\bar k / k)$ would be finite.
-/

namespace Langlands.WeilGroup

open LocalField Topology

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On the inertia subgroup, the topology of $W_K$ is the subspace topology from $G_K$. -/
theorem isInducing_toGalois_inertia :
    Topology.IsInducing (fun x : inertia K => toGalois K x) := by
  constructor
  change TopologicalSpace.induced Subtype.val
      (TopologicalSpace.induced (toGalois K) inferInstance ⊓
        TopologicalSpace.induced (toResidue K) ⊥) = _
  rw [induced_inf, induced_compose, induced_compose]
  have hconst : (toResidue K ∘ Subtype.val : inertia K → _) = fun _ => 1 :=
    funext fun x => x.2
  rw [hconst, @induced_const _ (inertia K) ⊥ 1, inf_top_eq]
  rfl

/-- The image of the inertia subgroup in $G_K$ is the kernel of the action on $\bar k$. -/
theorem range_toGalois_inertia :
    Set.range (fun x : inertia K => toGalois K x) = (residueAut K).ker := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hg
    have hw : g ∈ weilSubgroup K := by
      rw [← SetLike.mem_coe, coe_weilSubgroup]
      have h1 : residueAut K g = 1 := hg
      change residueAut K g ∈ (Subgroup.zpowers (LocalField.frobenius K) : Set _)
      rw [h1]
      exact (Subgroup.zpowers (LocalField.frobenius K)).one_mem
    exact ⟨⟨⟨g, hw⟩, hg⟩, rfl⟩

/-- **F2 for the Weil group.** The inertia subgroup $I_K$ is compact. -/
theorem isCompact_inertia : IsCompact (inertia K : Set (WeilGroup K)) := by
  rw [isCompact_iff_compactSpace]
  have hc : IsClosed ((residueAut K).ker : Set (Field.absoluteGaloisGroup K)) :=
    isClosed_singleton.preimage (continuous_residueAut K)
  have hE : Topology.IsClosedEmbedding (fun x : inertia K => toGalois K x) := by
    refine ⟨⟨isInducing_toGalois_inertia K, fun x y h => Subtype.ext (toGalois_injective K h)⟩, ?_⟩
    rw [range_toGalois_inertia]
    exact hc
  exact hE.compactSpace

/-- **F3 for the Weil group.** In the subspace topology from $G_K$, the inertia subgroup is not open. -/
theorem not_isOpen_inertia_induced :
    ¬ IsOpen[TopologicalSpace.induced (toGalois K) inferInstance]
      (inertia K : Set (WeilGroup K)) := by
  intro h
  obtain ⟨U, hU, hUI⟩ := isOpen_induced_iff.mp h
  set H := (residueAut K).ker
  have hcl : IsClosed (H : Set (Field.absoluteGaloisGroup K)) :=
    isClosed_singleton.preimage (continuous_residueAut K)
  have hsub : U ∩ Set.range (toGalois K) ⊆ H := by
    rintro _ ⟨hg, w, rfl⟩
    have hw : w ∈ inertia K := by
      rw [← SetLike.mem_coe, ← hUI]
      exact hg
    exact hw
  have hUH : U ⊆ H := by
    refine ((denseRange_toGalois K).open_subset_closure_inter hU).trans ?_
    exact closure_minimal hsub hcl
  have h1 : (1 : Field.absoluteGaloisGroup K) ∈ U := by
    have : (1 : WeilGroup K) ∈ toGalois K ⁻¹' U := by
      rw [hUI]
      exact (inertia K).one_mem
    simpa using this
  have hHo : IsOpen (H : Set (Field.absoluteGaloisGroup K)) :=
    H.isOpen_of_mem_nhds (Filter.mem_of_superset (hU.mem_nhds h1) hUH)
  have : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  have hfin : Finite (Field.absoluteGaloisGroup K ⧸ H) := H.quotient_finite_of_isOpen hHo
  have hΓ : Finite (residueFieldBar K ≃ₐ[residueField K] residueFieldBar K) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective _ (residueAut_surjective K)).toEquiv
  exact not_isOfFinOrder_frobenius K (isOfFinOrder_of_finite _)

end Langlands.WeilGroup
