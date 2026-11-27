/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Perfectoid.BDeRham
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RepresentationTheory.Basic

/-!
# The Galois action on the de Rham period rings

Let $p$ be a prime and let $R$ be a $p$-adically complete ring in which $p$ is not a unit. Mathlib defines the tilt $R^\flat$ (`PreTilt R p`), the map $\theta : W(R^\flat) \to R$ of Fontaine (`fontaineTheta`), the ring $B_{dR}^+(R)$ as the completion of $W(R^\flat)[1/p]$ at the kernel of $\theta[1/p]$ (`BDeRhamPlus R p`), and the ring $B_{dR}(R)$ as the localization of $B_{dR}^+(R)$ at the generators of this kernel (`BDeRham R p`). This file makes these constructions functorial in $R$. As a result, a group $G$ that acts on $R$ by ring automorphisms acts on $B_{dR}^+(R)$ and on $B_{dR}(R)$ by ring automorphisms. For $R = \mathcal{O}_{\mathbb{C}_p}$ and $G = \mathrm{Gal}(\overline{\mathbb{Q}}_p / \mathbb{Q}_p)$ this is the Galois action of Fontaine.

The file then defines, for a representation $V$ of $G$ over a field $K$ and a $K$-algebra $B$ with an action of $G$, the module $D_B(V) = (B \otimes_K V)^G$ over the ring $B^G$, the condition that $V$ is $B$-admissible, and with $B = B_{dR}(R)$ the condition to be de Rham. At last it defines the filtration of $B_{dR}(R)$ by the powers of the ideal of $B_{dR}^+(R)$ that the kernel of $\theta$ generates, the induced filtration of $D_{dR}(V)$, and the Hodge-Tate weights as the jumps of this filtration.

## Main definitions

* `Langlands.Padic.preTiltMap`, `Langlands.Padic.wittMap`, `Langlands.Padic.locMap`: the maps $R^\flat \to S^\flat$, $W(R^\flat) \to W(S^\flat)$ and $W(R^\flat)[1/p] \to W(S^\flat)[1/p]$ of a ring homomorphism $f : R \to S$.
* `Langlands.Padic.bdrPlusMap`: the map $B_{dR}^+(R) \to B_{dR}^+(S)$ of a ring homomorphism $f : R \to S$.
* `Langlands.Padic.bdrMap`: the map $B_{dR}(R) \to B_{dR}(S)$ of a ring isomorphism $e : R \cong S$.
* `Langlands.Padic.bdrCommRing`: the ring structure of $B_{dR}(R)$, which Mathlib does not give.
* `Langlands.Padic.bdrPlusAction`, `Langlands.Padic.bdrAction`: the actions of $G$ on $B_{dR}^+(R)$ and on $B_{dR}(R)$ by ring endomorphisms.
* `Langlands.Padic.preTiltAction`, `Langlands.Padic.wittAction`: the actions of $G$ on $R^\flat$ and on $W(R^\flat)$. They are not instances.
* `Langlands.Padic.deRhamInvariants`: the module $D_B(V) = (B \otimes_K V)^G$ over $B^G$.
* `Langlands.Padic.IsAdmissible`: the rank of $D_B(V)$ over $B^G$ is $\dim_K V$.
* `Langlands.Padic.IsDeRham`: $V$ is $B_{dR}(R)$-admissible.
* `Langlands.Padic.bdrFil`: the filtration $\mathrm{Fil}^i B_{dR}(R)$, $i \in \mathbb{Z}$.
* `Langlands.Padic.deRhamFil`: the filtration $\mathrm{Fil}^i D_{dR}(V)$.
* `Langlands.Padic.hodgeTateWeights`: the set of the jumps of the filtration of $D_{dR}(V)$.

## Main results

* `Langlands.Padic.untilt_preTiltMap`: $f(x^\sharp) = f^\flat(x)^\sharp$.
* `Langlands.Padic.fontaineTheta_comp_wittMap`: $\theta_S \circ W(f^\flat) = f \circ \theta_R$.
* `Langlands.Padic.fontaineThetaInvertP_comp_locMap`: the same identity after $p$ is inverted.
* `Langlands.Padic.bdrPlusMap_id`, `Langlands.Padic.bdrPlusMap_comp`, `Langlands.Padic.bdrMap_refl`, `Langlands.Padic.bdrMap_trans`: the maps are functorial.
* `Langlands.Padic.fontaineTheta_wittMap_smul`: $\theta(g x) = g \theta(x)$ for $g \in G$.
* `Langlands.Padic.smul_algebraMap_bdr`: the map $B_{dR}^+(R) \to B_{dR}(R)$ commutes with $G$.
* `Langlands.Padic.isAdmissible_trivial`: if $B^G$ is not the zero ring, the trivial representation $K$ is $B$-admissible.
* `Langlands.Padic.bdrFil_natCast`, `Langlands.Padic.bdrFil_antitone`, `Langlands.Padic.deRhamFil_antitone`: the filtrations are decreasing, and $\mathrm{Fil}^n B_{dR} = I^n B_{dR}^+$ for $n \ge 0$.

## Implementation notes

Each automorphism of the ring $R$ fixes $p$, so it needs no compatibility condition. The map of $B_{dR}^+$ exists for each ring homomorphism, but the map of $B_{dR}$ is defined for ring isomorphisms only, because $B_{dR}(R)$ inverts the generators of the kernel of $\theta$, and a general homomorphism does not send a generator to a generator. Mathlib gives no ring structure on `BDeRham R p`, so this file gives it from the localization.

The condition to be de Rham asks that the rank of $D_{dR}(V)$ over the ring $B_{dR}(R)^G$ is $\dim_K V$. For $R = \mathcal{O}_{\mathbb{C}_p}$ and $G = G_{\mathbb{Q}_p}$ the ring $B_{dR}^G$ is the field $\mathbb{Q}_p$, by the theorem of Ax, Sen and Tate, and the condition is the classical one. This file does not prove that $B_{dR}(R)^G$ is a field. The field $K$ and the structure of $K$-algebra on $B_{dR}(R)$ are arguments, because Mathlib has no map $\mathbb{Q}_p \to B_{dR}(R)$ and no Galois action on $\mathbb{C}_p$.

The filtration uses the ideal $I$ of $B_{dR}^+(R)$ that the image of $\ker \theta[1/p]$ generates. Mathlib does not extend $\theta$ to $B_{dR}^+$ and does not show that $I$ is principal. So $\mathrm{Fil}^i B_{dR}$ is $I^i B_{dR}^+$ for $i \ge 0$, and the set of $x$ with $I^{-i} x \subseteq B_{dR}^+$ for $i < 0$. When $I = (t)$ with $t$ a unit of $B_{dR}$, this is $t^i B_{dR}^+$. The integer $i$ is a Hodge-Tate weight if $\mathrm{Fil}^{i+1} D_{dR}(V) \neq \mathrm{Fil}^i D_{dR}(V)$. With this convention the cyclotomic character has the weight $-1$.

## References

* J.-M. Fontaine, Le corps des périodes p-adiques, Astérisque 223 (1994).
* O. Brinon and B. Conrad, CMI summer school notes on p-adic Hodge theory, sections 4 and 6.
-/

open Ideal TensorProduct WittVector

namespace Langlands.Padic

universe u

section Adic

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- If $I \subseteq f^{-1}(J)$, then $I^n \subseteq f^{-1}(J^n)$. -/
theorem pow_le_comap_pow {φ : A →+* B} {I : Ideal A} {J : Ideal B} (h : I ≤ J.comap φ) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n

/-- The projections of the adic completion to $A / I^n$ are compatible. -/
theorem factorPow_evalₐ (I : Ideal A) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  have := s.property hle
  simp only [AdicCompletion.evalₐ_mk]
  simp only [smul_eq_mul, Ideal.mul_top] at this
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ((SModEq.sub_mem).1 this.symm)

/-- The maps $\hat{A}_I \to A / I^n \to B / J^n$ are compatible. -/
theorem adicMap_compat (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp ((Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) =
    (Ideal.quotientMap (J ^ m) φ (pow_le_comap_pow h m)).comp
      (AdicCompletion.evalₐ I m : AdicCompletion I A →+* A ⧸ I ^ m) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [← factorPow_evalₐ I hle x, ← hy]
  rfl

/-- The map $\hat{A}_I \to \hat{B}_J$ of the adic completions of a ring homomorphism $\varphi : A \to B$ with $\varphi(I) \subseteq J$. -/
noncomputable def adicMap (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun hle => adicMap_compat φ I J h hle)

/-- The map of adic completions modulo $J^n$ is the map $A / I^n \to B / J^n$. -/
theorem evalₐ_adicMap (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicMap φ I J h x) =
      Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow h n) (AdicCompletion.evalₐ I n x) := by
  rw [adicMap, AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- The map of adic completions extends $\varphi$. -/
theorem adicMap_of (φ : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ) (x : A) :
    adicMap φ I J h (AdicCompletion.of I A x) = AdicCompletion.of J B (φ x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_adicMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl

/-- The map of adic completions of the identity is the identity. -/
theorem adicMap_id (I : Ideal A) (h : I ≤ I.comap (RingHom.id A)) :
    adicMap (RingHom.id A) I I h = RingHom.id _ := by
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [evalₐ_adicMap, RingHom.id_apply, ← hy]
  rfl

/-- The map of adic completions of a composite is the composite of the maps. -/
theorem adicMap_comp (φ : A →+* B) (ψ : B →+* C) (I : Ideal A) (J : Ideal B) (L : Ideal C)
    (h : I ≤ J.comap φ) (h' : J ≤ L.comap ψ) (h'' : I ≤ L.comap (ψ.comp φ)) :
    adicMap (ψ.comp φ) I L h'' = (adicMap ψ J L h').comp (adicMap φ I J h) := by
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [RingHom.comp_apply, evalₐ_adicMap, evalₐ_adicMap, evalₐ_adicMap, ← hy]
  rfl

/-- The map of adic completions depends only on the ring homomorphism. -/
theorem adicMap_congr {φ ψ : A →+* B} (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap φ)
    (h' : I ≤ J.comap ψ) (e : φ = ψ) : adicMap φ I J h = adicMap ψ I J h' := by
  subst e
  rfl

end Adic

section Functoriality

variable {p : ℕ} {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]

/-- A ring homomorphism sends $pR$ into $pS$. -/
theorem span_p_le_comap (f : R →+* S) :
    span {(p : R)} ≤ (span {(p : S)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simp [map_natCast]

variable (p) in
/-- The map $R / p \to S / p$ of a ring homomorphism $f : R \to S$. -/
noncomputable def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap _ f (span_p_le_comap f)

/-- The map $R / p \to S / p$ sends the class of $x$ to the class of $f(x)$. -/
@[simp]
theorem modPMap_mk (f : R →+* S) (x : R) :
    modPMap p f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

variable (p) in
/-- The map $R[1/p] \to S[1/p]$ of a ring homomorphism $f : R \to S$. -/
noncomputable def locMapBase (f : R →+* S) :
    Localization.Away (p : R) →+* Localization.Away (p : S) :=
  Localization.awayLift ((algebraMap _ _).comp f) (p : R)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : S))

/-- The map $R[1/p] \to S[1/p]$ extends $f$. -/
@[simp]
theorem locMapBase_algebraMap (f : R →+* S) (x : R) :
    locMapBase p f (algebraMap _ _ x) = algebraMap _ _ (f x) := by
  simp [locMapBase]

/-- The prime $p$ is nilpotent in $S / p^n S$. -/
theorem isNilpotent_natCast_quotient_pow (n : ℕ) :
    IsNilpotent (p : S ⧸ span {(p : S)} ^ n) :=
  ⟨n, by
    rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩

variable [Fact p.Prime] [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]

variable (p) in
/-- The map $f^\flat : R^\flat \to S^\flat$ of the tilts of a ring homomorphism $f : R \to S$. -/
noncomputable def preTiltMap (f : R →+* S) : PreTilt R p →+* PreTilt S p :=
  Perfection.map p (modPMap p f)

/-- The coefficients of $f^\flat(x)$ are the images of the coefficients of $x$. -/
@[simp]
theorem coeff_preTiltMap (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    PreTilt.coeff n (preTiltMap p f x) = modPMap p f (PreTilt.coeff n x) := rfl

/-- The map of tilts of the identity is the identity. -/
theorem preTiltMap_id : preTiltMap p (RingHom.id R) = RingHom.id _ := by
  ext x
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n _ = PreTilt.coeff n x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [coeff_preTiltMap, ← hy, modPMap_mk]
  rfl

/-- The map of tilts of a composite is the composite of the maps. -/
theorem preTiltMap_comp (f : R →+* S) (g : S →+* T) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) := by
  ext x
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n _ = PreTilt.coeff n _
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap, ← hy]
  rfl

variable (p) in
/-- The map $W(f^\flat) : W(R^\flat) \to W(S^\flat)$ of a ring homomorphism $f : R \to S$. -/
noncomputable def wittMap (f : R →+* S) :
    WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) :=
  WittVector.map (preTiltMap p f)

/-- The map of Witt vectors of the identity is the identity. -/
theorem wittMap_id : wittMap p (RingHom.id R) = RingHom.id _ := by
  rw [wittMap, preTiltMap_id, WittVector.map_id]

/-- The map of Witt vectors of a composite is the composite of the maps. -/
theorem wittMap_comp (f : R →+* S) (g : S →+* T) :
    wittMap p (g.comp f) = (wittMap p g).comp (wittMap p f) := by
  ext x n
  simp [wittMap, preTiltMap_comp]

variable (p) in
/-- The map $W(R^\flat)[1/p] \to W(S^\flat)[1/p]$ of a ring homomorphism $f : R \to S$. -/
noncomputable def locMap (f : R →+* S) :
    Localization.Away (p : WittVector p (PreTilt R p)) →+*
      Localization.Away (p : WittVector p (PreTilt S p)) :=
  Localization.awayLift ((algebraMap _ _).comp (wittMap p f)) (p : WittVector p (PreTilt R p))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : WittVector p (PreTilt S p)))

/-- The map $W(R^\flat)[1/p] \to W(S^\flat)[1/p]$ extends $W(f^\flat)$. -/
@[simp]
theorem locMap_algebraMap (f : R →+* S) (x : WittVector p (PreTilt R p)) :
    locMap p f (algebraMap _ _ x) = algebraMap _ _ (wittMap p f x) := by
  simp [locMap]

/-- The map of $W(R^\flat)[1/p]$ of the identity is the identity. -/
theorem locMap_id : locMap p (RingHom.id R) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p))) ?_
  ext x
  simp [wittMap_id]

/-- The map of $W(R^\flat)[1/p]$ of a composite is the composite of the maps. -/
theorem locMap_comp (f : R →+* S) (g : S →+* T) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p))) ?_
  ext x
  simp [wittMap_comp]

/-- For a ring isomorphism $e$, the map of $W(\cdot^\flat)[1/p]$ of $e$ is inverse to the map of $e^{-1}$. -/
theorem locMap_symm_apply (e : R ≃+* S) (x : Localization.Away (p : WittVector p (PreTilt S p))) :
    locMap p (e : R →+* S) (locMap p (e.symm : S →+* R) x) = x := by
  rw [← RingHom.comp_apply, ← locMap_comp]
  have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by
    ext y; simp
  rw [this, locMap_id, RingHom.id_apply]

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- The untilt commutes with the maps: $f^\flat(x)^\sharp = f(x^\sharp)$. -/
theorem untilt_preTiltMap (f : R →+* S) (x : PreTilt R p) :
    (preTiltMap p f x).untilt = f x.untilt := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f w, ?_, ?_⟩
  · change _ = PreTilt.coeff n (preTiltMap p f x)
    rw [coeff_preTiltMap, ← hw, modPMap_mk]
  · have h : x.untilt ≡ w ^ p ^ n [SMOD span {(p : R)} ^ (n + 1)] :=
      Perfection.teichmuller_sModEq hw
    rw [SModEq.sub_mem] at h ⊢
    have hle : (span {(p : R)} ^ (n + 1)).map f ≤ span {(p : S)} ^ (n + 1) := by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
    have := hle (Ideal.mem_map_of_mem f ((Ideal.neg_mem_iff _).2 h))
    rwa [map_neg, map_sub, map_pow, neg_sub] at this

/-- The map $\theta$ of Fontaine is natural: $\theta_S \circ W(f^\flat) = f \circ \theta_R$. -/
theorem fontaineTheta_comp_wittMap (f : R →+* S) :
    (fontaineTheta S p).comp (wittMap p f) = f.comp (fontaineTheta R p) := by
  refine DFunLike.coe_injective (IsHausdorff.funext' (span {(p : S)}) fun n x => ?_)
  have key :
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp ((fontaineTheta S p).comp (wittMap p f)) =
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (fontaineTheta R p)) := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ (isNilpotent_natCast_quotient_pow n)
      fun y => ?_
    simp [wittMap, WittVector.map_teichmuller, untilt_preTiltMap]
  exact congrArg (fun φ => φ x) key

/-- The map $\theta[1/p]$ is natural: $\theta_S[1/p] \circ W(f^\flat)[1/p] = f[1/p] \circ \theta_R[1/p]$. -/
theorem fontaineThetaInvertP_comp_locMap (f : R →+* S) :
    (fontaineThetaInvertP S p).comp (locMap p f) =
      (locMapBase p f).comp (fontaineThetaInvertP R p) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p))) ?_
  ext x
  simp only [RingHom.comp_apply, locMap_algebraMap, fontaineThetaInvertP]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq, RingHom.comp_apply,
    locMapBase_algebraMap]
  rw [← RingHom.comp_apply (fontaineTheta S p), fontaineTheta_comp_wittMap, RingHom.comp_apply]

/-- The map $W(R^\flat)[1/p] \to W(S^\flat)[1/p]$ sends $\ker \theta_R[1/p]$ into $\ker \theta_S[1/p]$. -/
theorem ker_le_comap_locMap (f : R →+* S) :
    RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP S p)).comap (locMap p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, fontaineThetaInvertP_comp_locMap,
    RingHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]

variable (p) in
/-- The map $B_{dR}^+(R) \to B_{dR}^+(S)$ of a ring homomorphism $f : R \to S$. -/
noncomputable def bdrPlusMap (f : R →+* S) : BDeRhamPlus R p →+* BDeRhamPlus S p :=
  adicMap (locMap p f) _ _ (ker_le_comap_locMap f)

/-- The map $B_{dR}^+(R) \to B_{dR}^+(S)$ extends the map of $W(R^\flat)[1/p]$. -/
theorem bdrPlusMap_of (f : R →+* S) (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    bdrPlusMap p f (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ (locMap p f x) :=
  adicMap_of _ _ _ _ x

/-- The map of $B_{dR}^+$ of the identity is the identity. -/
theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id R) = RingHom.id _ := by
  rw [bdrPlusMap, adicMap_congr _ _ _ (fun x hx => by simpa [locMap_id] using hx) locMap_id]
  exact adicMap_id _ _

variable [IsAdicComplete (span {(p : T)}) T] in
/-- The map of $B_{dR}^+$ of a composite is the composite of the maps. -/
theorem bdrPlusMap_comp (f : R →+* S) (g : S →+* T) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) := by
  have h3 : RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP T p)).comap ((locMap p g).comp (locMap p f)) :=
    fun x hx => by
      rw [Ideal.mem_comap, RingHom.comp_apply]
      exact Ideal.mem_comap.1 (ker_le_comap_locMap g (Ideal.mem_comap.1 (ker_le_comap_locMap f hx)))
  unfold bdrPlusMap
  rw [adicMap_congr _ _ _ h3 (locMap_comp f g)]
  exact adicMap_comp _ _ _ _ _ (ker_le_comap_locMap f) (ker_le_comap_locMap g) h3

/-- The submonoid of $B_{dR}^+(R)$ that `BDeRham R p` inverts: it is generated by the images of the generators $a$ of $\ker \theta[1/p]$. -/
noncomputable def bdrSubmonoid (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] : Submonoid (BDeRhamPlus R p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}}

/-- The ring structure of $B_{dR}(R)$, from the localization. -/
noncomputable instance bdrCommRing : CommRing (BDeRham R p) :=
  inferInstanceAs (CommRing (Localization (bdrSubmonoid R p)))

/-- The algebra structure of $B_{dR}(R)$ over $B_{dR}^+(R)$, from the localization. -/
noncomputable instance bdrAlgebra : Algebra (BDeRhamPlus R p) (BDeRham R p) :=
  inferInstanceAs (Algebra _ (Localization (bdrSubmonoid R p)))

/-- The ring $B_{dR}(R)$ is the localization of $B_{dR}^+(R)$ at `bdrSubmonoid R p`. -/
instance bdr_isLocalization : IsLocalization (bdrSubmonoid R p) (BDeRham R p) :=
  inferInstanceAs (IsLocalization _ (Localization (bdrSubmonoid R p)))

/-- For a ring isomorphism $e$, the map of $W(\cdot^\flat)[1/p]$ sends $\ker \theta_R[1/p]$ onto $\ker \theta_S[1/p]$. -/
theorem ker_eq_map_locMap (e : R ≃+* S) :
    RingHom.ker (fontaineThetaInvertP S p) =
      (RingHom.ker (fontaineThetaInvertP R p)).map (locMap p (e : R →+* S)) := by
  refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 (ker_le_comap_locMap _))
  rw [← locMap_symm_apply e x]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.1 (ker_le_comap_locMap _ hx))

/-- For a ring isomorphism $e$, the map of $B_{dR}^+$ sends the inverted submonoid into the inverted submonoid. -/
theorem bdrSubmonoid_le_comap (e : R ≃+* S) :
    bdrSubmonoid R p ≤ (bdrSubmonoid S p).comap (bdrPlusMap p (e : R →+* S)) := by
  rw [bdrSubmonoid, Submonoid.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  refine Submonoid.subset_closure ⟨locMap p (e : R →+* S) a, ?_, (bdrPlusMap_of _ a).symm⟩
  change RingHom.ker _ = _
  rw [ker_eq_map_locMap e, show RingHom.ker _ = _ from ha, Ideal.map_span, Set.image_singleton]

variable (p) in
/-- The map $B_{dR}(R) \to B_{dR}(S)$ of a ring isomorphism $e : R \cong S$. -/
noncomputable def bdrMap (e : R ≃+* S) : BDeRham R p →+* BDeRham S p :=
  IsLocalization.map (M := bdrSubmonoid R p) (T := bdrSubmonoid S p) (BDeRham S p)
    (bdrPlusMap p (e : R →+* S)) (bdrSubmonoid_le_comap e)

/-- The map of $B_{dR}$ extends the map of $B_{dR}^+$. -/
theorem bdrMap_algebraMap (e : R ≃+* S) (x : BDeRhamPlus R p) :
    bdrMap p e (algebraMap _ _ x) = algebraMap _ _ (bdrPlusMap p (e : R →+* S) x) :=
  IsLocalization.map_eq _ _

/-- The map of $B_{dR}$ of the identity is the identity. -/
theorem bdrMap_refl : bdrMap p (RingEquiv.refl R) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (bdrSubmonoid R p) (RingHom.ext fun x => ?_)
  rw [RingHom.comp_apply, bdrMap_algebraMap]
  have : ((RingEquiv.refl R : R ≃+* R) : R →+* R) = RingHom.id R := rfl
  rw [this, bdrPlusMap_id]
  rfl

variable [IsAdicComplete (span {(p : T)}) T] in
/-- The map of $B_{dR}$ of a composite is the composite of the maps. -/
theorem bdrMap_trans (e : R ≃+* S) (e' : S ≃+* T) :
    bdrMap p (e.trans e') = (bdrMap p e').comp (bdrMap p e) := by
  refine IsLocalization.ringHom_ext (bdrSubmonoid R p) (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, bdrMap_algebraMap]
  have : ((e.trans e' : R ≃+* T) : R →+* T) = (e' : S →+* T).comp (e : R →+* S) := rfl
  rw [this, bdrPlusMap_comp]
  rfl

end Functoriality

section Action

/-- The action of a monoid $M$ on a semiring $A$ given by ring endomorphisms $\varphi(g)$ with $\varphi(1) = \mathrm{id}$ and $\varphi(gh) = \varphi(g) \circ \varphi(h)$. -/
abbrev mulSemiringActionOfMap {M A : Type*} [Monoid M] [Semiring A] (φ : M → A →+* A)
    (h1 : φ 1 = RingHom.id A) (hm : ∀ g h, φ (g * h) = (φ g).comp (φ h)) :
    MulSemiringAction M A where
  smul g x := φ g x
  one_smul x := by
    change φ 1 x = x
    rw [h1, RingHom.id_apply]
  mul_smul g h x := by
    change φ (g * h) x = φ g (φ h x)
    rw [hm, RingHom.comp_apply]
  smul_zero g := map_zero (φ g)
  smul_add g := map_add (φ g)
  smul_one g := map_one (φ g)
  smul_mul g := map_mul (φ g)

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable (M : Type*) [Monoid M] [MulSemiringAction M R]

omit [Fact p.Prime] [Fact ¬IsUnit (p : R)] in
/-- The ring endomorphism of $1$ is the identity. -/
theorem toRingHom_one : MulSemiringAction.toRingHom M R 1 = RingHom.id R :=
  RingHom.ext fun x => one_smul M x

omit [Fact p.Prime] [Fact ¬IsUnit (p : R)] in
/-- The ring endomorphism of $gh$ is the composite of the ring endomorphisms of $g$ and $h$. -/
theorem toRingHom_mul (g h : M) :
    MulSemiringAction.toRingHom M R (g * h) =
      (MulSemiringAction.toRingHom M R g).comp (MulSemiringAction.toRingHom M R h) :=
  RingHom.ext fun x => mul_smul g h x

variable (p R) in
/-- The action of $M$ on the tilt $R^\flat$. It is not an instance. -/
noncomputable abbrev preTiltAction : MulSemiringAction M (PreTilt R p) :=
  mulSemiringActionOfMap (fun g => preTiltMap p (MulSemiringAction.toRingHom M R g))
    (by rw [toRingHom_one, preTiltMap_id]) (fun g h => by rw [toRingHom_mul, preTiltMap_comp])

variable (p R) in
/-- The action of $M$ on $W(R^\flat)$. It is not an instance. -/
noncomputable abbrev wittAction : MulSemiringAction M (WittVector p (PreTilt R p)) :=
  mulSemiringActionOfMap (fun g => wittMap p (MulSemiringAction.toRingHom M R g))
    (by rw [toRingHom_one, wittMap_id]) (fun g h => by rw [toRingHom_mul, wittMap_comp])

variable [IsAdicComplete (span {(p : R)}) R]

/-- The map $\theta$ of Fontaine commutes with the action: $\theta(g x) = g \theta(x)$. -/
theorem fontaineTheta_wittMap_smul (g : M) (x : WittVector p (PreTilt R p)) :
    fontaineTheta R p (wittMap p (MulSemiringAction.toRingHom M R g) x) =
      g • fontaineTheta R p x := by
  rw [← RingHom.comp_apply, fontaineTheta_comp_wittMap]
  rfl

/-- The action of $M$ on $B_{dR}^+(R)$ by ring endomorphisms. -/
noncomputable instance bdrPlusAction : MulSemiringAction M (BDeRhamPlus R p) :=
  mulSemiringActionOfMap (fun g => bdrPlusMap p (MulSemiringAction.toRingHom M R g))
    (by rw [toRingHom_one, bdrPlusMap_id]) (fun g h => by rw [toRingHom_mul, bdrPlusMap_comp])

/-- The action of $g$ on $B_{dR}^+(R)$ is the map of $B_{dR}^+$ of $x \mapsto g x$. -/
theorem bdrPlus_smul_def (g : M) (x : BDeRhamPlus R p) :
    g • x = bdrPlusMap p (MulSemiringAction.toRingHom M R g) x := rfl

end Action

section GroupAction

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable (G : Type*) [Group G] [MulSemiringAction G R]

omit [Fact p.Prime] [Fact ¬IsUnit (p : R)] in
/-- The ring automorphism of $1$ is the identity. -/
theorem toRingEquiv_one : MulSemiringAction.toRingEquiv G R 1 = RingEquiv.refl R :=
  RingEquiv.ext fun x => one_smul G x

omit [Fact p.Prime] [Fact ¬IsUnit (p : R)] in
/-- The ring automorphism of $gh$ is the composite of the ring automorphisms of $h$ and $g$. -/
theorem toRingEquiv_mul (g h : G) :
    MulSemiringAction.toRingEquiv G R (g * h) =
      (MulSemiringAction.toRingEquiv G R h).trans (MulSemiringAction.toRingEquiv G R g) :=
  RingEquiv.ext fun x => mul_smul g h x

variable [IsAdicComplete (span {(p : R)}) R]

/-- The action of $G$ on $B_{dR}(R)$ by ring automorphisms. -/
noncomputable instance bdrAction : MulSemiringAction G (BDeRham R p) :=
  mulSemiringActionOfMap (fun g => bdrMap p (MulSemiringAction.toRingEquiv G R g))
    (by rw [toRingEquiv_one, bdrMap_refl]) (fun g h => by rw [toRingEquiv_mul, bdrMap_trans])

/-- The action of $g$ on $B_{dR}(R)$ is the map of $B_{dR}$ of $x \mapsto g x$. -/
theorem bdr_smul_def (g : G) (x : BDeRham R p) :
    g • x = bdrMap p (MulSemiringAction.toRingEquiv G R g) x := rfl

/-- The map $B_{dR}^+(R) \to B_{dR}(R)$ commutes with the action of $G$. -/
theorem smul_algebraMap_bdr (g : G) (x : BDeRhamPlus R p) :
    g • (algebraMap (BDeRhamPlus R p) (BDeRham R p) x) = algebraMap _ _ (g • x) :=
  bdrMap_algebraMap _ x

end GroupAction

section Invariants

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [CommRing B] [Algebra K B]
  [MulSemiringAction G B] [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module K V]

variable (B) in
/-- The diagonal action $g \otimes \rho(g)$ of $g \in G$ on $B \otimes_K V$. -/
noncomputable def tensorAction (ρ : Representation K G V) (g : G) : B ⊗[K] V →ₗ[K] B ⊗[K] V :=
  TensorProduct.map (MulSemiringAction.toAlgHom K B g).toLinearMap (ρ g)

/-- The diagonal action on a pure tensor: $g (b \otimes v) = g b \otimes \rho(g) v$. -/
theorem tensorAction_tmul (ρ : Representation K G V) (g : G) (b : B) (v : V) :
    tensorAction B ρ g (b ⊗ₜ v) = (g • b) ⊗ₜ ρ g v := rfl

/-- The diagonal action is semilinear over $B$: $g (b x) = (g b) (g x)$. -/
theorem tensorAction_smul (ρ : Representation K G V) (g : G) (b : B) (x : B ⊗[K] V) :
    tensorAction B ρ g (b • x) = (g • b) • tensorAction B ρ g x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', tensorAction_tmul, tensorAction_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_mul', smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable (B) in
/-- The module $D_B(V) = (B \otimes_K V)^G$ over the ring of invariants $B^G$. -/
noncomputable def deRhamInvariants (ρ : Representation K G V) :
    Submodule (FixedPoints.subalgebra K B G) (B ⊗[K] V) where
  carrier := {x | ∀ g, tensorAction B ρ g x = x}
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by
    change tensorAction B ρ g ((c : B) • x) = (c : B) • x
    rw [tensorAction_smul, hx g, FixedPoints.mem_subalgebra.1 c.2 g]

variable (B) in
/-- The representation $V$ is $B$-admissible if the rank of $D_B(V)$ over the ring $B^G$ is $\dim_K V$. The rank is `Module.finrank` over the ring $B^G$, which this file does not show to be a field. -/
def IsAdmissible (ρ : Representation K G V) : Prop :=
  Module.finrank (FixedPoints.subalgebra K B G) (deRhamInvariants B ρ) = Module.finrank K V

/-- For the trivial representation $K$, the isomorphism $B \otimes_K K \cong B$ commutes with $G$. -/
theorem rid_tensorAction_trivial (g : G) (x : B ⊗[K] K) :
    AlgebraTensorModule.rid K B B (tensorAction B (Representation.trivial K G K) g x) =
      g • AlgebraTensorModule.rid K B B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b k =>
    rw [tensorAction_tmul, Representation.trivial_apply]
    simp only [AlgebraTensorModule.rid_tmul]
    exact (smul_comm g k b).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

variable (B) in
/-- For the trivial representation $K$, the module $D_B(K)$ is isomorphic to $B^G$. -/
noncomputable def trivialInvariantsEquiv :
    deRhamInvariants B (Representation.trivial K G K) ≃ₗ[FixedPoints.subalgebra K B G]
      FixedPoints.subalgebra K B G where
  toFun x := ⟨AlgebraTensorModule.rid K B B x.1, fun g => by
    rw [← rid_tensorAction_trivial, x.2 g]⟩
  invFun c := ⟨(c : B) ⊗ₜ 1, fun g => by
    rw [tensorAction_tmul, Representation.trivial_apply, FixedPoints.mem_subalgebra.1 c.2 g]⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' c x := Subtype.ext (by
    change AlgebraTensorModule.rid K B B ((c : B) • x.1) = (c : B) * _
    rw [map_smul, smul_eq_mul])
  left_inv x := Subtype.ext ((AlgebraTensorModule.rid K B B).symm_apply_apply x.1)
  right_inv c := Subtype.ext (by
    change AlgebraTensorModule.rid K B B ((c : B) ⊗ₜ[K] (1 : K)) = c
    simp)

variable (B) in
/-- If $B^G$ is not the zero ring, then the trivial representation $K$ is $B$-admissible. -/
theorem isAdmissible_trivial [Nontrivial (FixedPoints.subalgebra K B G)] :
    IsAdmissible B (Representation.trivial K G K) := by
  rw [IsAdmissible, (trivialInvariantsEquiv B).finrank_eq, Module.finrank_self,
    Module.finrank_self]

end Invariants

section DeRham

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable {K : Type*} [Field K] {G : Type*} [Group G] [MulSemiringAction G R]
  [Algebra K (BDeRham R p)] [SMulCommClass G K (BDeRham R p)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A representation $V$ of $G$ over $K$ is de Rham if it is $B_{dR}(R)$-admissible: the rank of $D_{dR}(V) = (B_{dR}(R) \otimes_K V)^G$ over the ring $B_{dR}(R)^G$ is $\dim_K V$. For $R = \mathcal{O}_{\mathbb{C}_p}$, $K = \mathbb{Q}_p$ and $G = G_{\mathbb{Q}_p}$, the ring $B_{dR}^G$ is the field $\mathbb{Q}_p$ by the theorem of Ax, Sen and Tate, and this is the classical condition. This file does not prove that $B_{dR}(R)^G$ is a field. -/
def IsDeRham (ρ : Representation K G V) : Prop :=
  IsAdmissible (BDeRham R p) ρ

/-- The ideal $I$ of $B_{dR}^+(R)$ that the image of $\ker \theta[1/p]$ generates. -/
noncomputable def bdrIdeal : Ideal (BDeRhamPlus R p) :=
  Ideal.span (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ ''
    (RingHom.ker (fontaineThetaInvertP R p) : Set _))

/-- The filtration of $B_{dR}(R)$: $\mathrm{Fil}^i$ is the set of $x$ with $y x \in I^{\max(i, 0)} B_{dR}^+$ for each $y \in I^{\max(-i, 0)}$. For $i \ge 0$ it is $I^i B_{dR}^+$, and for $i < 0$ it is the set of $x$ with $I^{-i} x \subseteq B_{dR}^+$. -/
noncomputable def bdrFil (i : ℤ) : Submodule (BDeRhamPlus R p) (BDeRham R p) where
  carrier := {x | ∀ y ∈ bdrIdeal R p ^ (-i).toNat,
    y • x ∈ Submodule.map (Algebra.linearMap (BDeRhamPlus R p) (BDeRham R p))
      (bdrIdeal R p ^ i.toNat)}
  add_mem' hx hy y hyI := by
    rw [smul_add]
    exact Submodule.add_mem _ (hx y hyI) (hy y hyI)
  zero_mem' y _ := by
    rw [smul_zero]
    exact Submodule.zero_mem _
  smul_mem' c x hx y hyI := by
    rw [smul_comm]
    exact Submodule.smul_mem _ c (hx y hyI)

/-- For $n \ge 0$, $\mathrm{Fil}^n B_{dR}(R) = I^n B_{dR}^+(R)$. -/
theorem bdrFil_natCast (n : ℕ) :
    bdrFil R p n =
      Submodule.map (Algebra.linearMap (BDeRhamPlus R p) (BDeRham R p)) (bdrIdeal R p ^ n) := by
  ext x
  have h1 : (-(n : ℤ)).toNat = 0 := by omega
  have h2 : (n : ℤ).toNat = n := Int.toNat_natCast n
  change (∀ y ∈ bdrIdeal R p ^ (-(n : ℤ)).toNat, _) ↔ _
  rw [h1, h2, pow_zero]
  refine ⟨fun hx => ?_, fun hx y _ => Submodule.smul_mem _ y hx⟩
  simpa using hx 1 (Ideal.one_eq_top (R := BDeRhamPlus R p) ▸ Submodule.mem_top)

/-- The filtration of $B_{dR}(R)$ is decreasing: $\mathrm{Fil}^{i+1} \subseteq \mathrm{Fil}^i$. -/
theorem bdrFil_succ_le (i : ℤ) : bdrFil R p (i + 1) ≤ bdrFil R p i := by
  intro x hx y hy
  have h1 : (-(i + 1)).toNat ≤ (-i).toNat := by omega
  have h2 : i.toNat ≤ (i + 1).toNat := by omega
  exact Submodule.map_mono (Ideal.pow_le_pow_right h2)
    (hx y (Ideal.pow_le_pow_right h1 hy))

/-- The filtration of $B_{dR}(R)$ is decreasing. -/
theorem bdrFil_antitone : Antitone (bdrFil R p) :=
  antitone_int_of_succ_le (bdrFil_succ_le R p)

variable (K V) in
/-- The filtration of $B_{dR}(R) \otimes_K V$: $\mathrm{Fil}^i$ is the additive group generated by the $b \otimes v$ with $b \in \mathrm{Fil}^i B_{dR}(R)$. -/
noncomputable def tensorFil (i : ℤ) : AddSubgroup (BDeRham R p ⊗[K] V) :=
  AddSubgroup.closure {x | ∃ b ∈ bdrFil R p i, ∃ v : V, x = b ⊗ₜ v}

/-- The filtration of $D_{dR}(V)$: $\mathrm{Fil}^i D_{dR}(V) = D_{dR}(V) \cap \mathrm{Fil}^i (B_{dR}(R) \otimes_K V)$, as an additive group. -/
noncomputable def deRhamFil (ρ : Representation K G V) (i : ℤ) :
    AddSubgroup (BDeRham R p ⊗[K] V) :=
  (deRhamInvariants (BDeRham R p) ρ).toAddSubgroup ⊓ tensorFil R p K V i

/-- The filtration of $D_{dR}(V)$ is decreasing. -/
theorem deRhamFil_antitone (ρ : Representation K G V) : Antitone (deRhamFil R p ρ) := by
  intro i j hij
  refine inf_le_inf_left _ (AddSubgroup.closure_mono ?_)
  rintro _ ⟨b, hb, v, rfl⟩
  exact ⟨b, bdrFil_antitone R p hij hb, v, rfl⟩

/-- The Hodge-Tate weights of $V$: the integers $i$ with $\mathrm{Fil}^{i+1} D_{dR}(V) \neq \mathrm{Fil}^i D_{dR}(V)$, the jumps of the filtration. The definition makes sense for each $V$, but it is the classical notion only for de Rham $V$. With this convention the cyclotomic character has the weight $-1$. -/
def hodgeTateWeights (ρ : Representation K G V) : Set ℤ :=
  {i | deRhamFil R p ρ (i + 1) ≠ deRhamFil R p ρ i}

end DeRham

end Langlands.Padic
