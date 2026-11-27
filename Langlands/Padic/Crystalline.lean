/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.DeRhamQp
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Polynomial.Derivation

/-!
# The rings $A_{cris}$, $B_{cris}^+$, $B_{cris}$ and $B_{st}$

This file defines the crystalline period rings of a $p$-adically complete ring $R$. The ring $A_{cris}^0(R)$ is the $W(R^\flat)$-subalgebra of $W(R^\flat)[1/p]$ that the divided powers $x^n / n!$ of the elements $x$ of $\ker \theta$ generate. The ring $A_{cris}(R)$ is the $p$-adic completion of $A_{cris}^0(R)$, and $B_{cris}^+(R) = A_{cris}(R)[1/p]$. The Frobenius of $W(R^\flat)$ extends to these rings, and it commutes with the action of a monoid that acts on $R$. The element $t = \log [\varepsilon] = \sum_{j \ge 1} (-1)^{j-1} ([\varepsilon] - 1)^j / j$ is a limit in $A_{cris}(R)$ for each $\varepsilon \in R^\flat$ with $\varepsilon^\sharp = 1$. The ring $B_{cris}(R)$ is $B_{cris}^+(R)$ with the elements $g t$ inverted, and $B_{st}(R) = B_{cris}(R)[u]$ with $N = -d/du$. For $R = \mathcal{O}_{\mathbb{C}_p}$ and $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \ldots)$, this gives the predicate `IsCrystallineQp`.

## Main definitions

* `Langlands.Padic.dividedPowers`: the elements $x^n / n!$ of $W(R^\flat)[1/p]$ with $x \in \ker \theta$.
* `Langlands.Padic.acrisZero`: the ring $A_{cris}^0(R)$, the $W(R^\flat)$-subalgebra of $W(R^\flat)[1/p]$ that the divided powers generate. This is the image of the divided power envelope of $W(R^\flat)$ at $\ker \theta$ in $W(R^\flat)[1/p]$, not the envelope itself.
* `Langlands.Padic.Acris`: the ring $A_{cris}(R)$, the $p$-adic completion of $A_{cris}^0(R)$.
* `Langlands.Padic.BcrisPlus`: the ring $B_{cris}^+(R) = A_{cris}(R)[1/p]$.
* `Langlands.Padic.acrisMap`, `Langlands.Padic.bcrisPlusMap`: the functoriality in $R$.
* `Langlands.Padic.locFrob`, `Langlands.Padic.acrisFrob`, `Langlands.Padic.bcrisPlusFrob`: the Frobenius $\varphi$ on $W(R^\flat)[1/p]$, $A_{cris}(R)$ and $B_{cris}^+(R)$.
* `Langlands.Padic.acrisAction`, `Langlands.Padic.bcrisPlusAction`, `Langlands.Padic.bcrisAction`: the action of a monoid $M$ that acts on $R$.
* `Langlands.Padic.logTeich`: the element $t = \log [\varepsilon]$ of $A_{cris}(R)$.
* `Langlands.Padic.Bcris`: the ring $B_{cris}(R)$, the localization of $B_{cris}^+(R)$ at the submonoid that the elements $g t$, $g \in M$, generate.
* `Langlands.Padic.bcrisPlusQpAlgebra`: the $\mathbb{Q}_p$-algebra structure on $B_{cris}^+(R)$.
* `Langlands.Padic.monodromy`: the operator $N = -d/du$ on $A[u]$.
* `Langlands.Padic.Bst`: the ring $B_{st}(R) = B_{cris}(R)[u]$.
* `Langlands.Padic.epsCp`: the element $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \ldots)$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$.
* `Langlands.Padic.BcrisCp`, `Langlands.Padic.BstCp`: the rings $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ and $B_{st}(\mathcal{O}_{\mathbb{C}_p})$.
* `Langlands.Padic.IsCrystallineQp`: a representation of $G_{\mathbb{Q}_p}$ is $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$-admissible.

## Main results

* `Langlands.Padic.locFrob_mem_acrisZero`: the Frobenius of $W(R^\flat)[1/p]$ sends $A_{cris}^0(R)$ into itself.
* `Langlands.Padic.acrisMap_comp_acrisFrob`, `Langlands.Padic.bcrisPlusMap_comp_bcrisPlusFrob`: the Frobenius commutes with the functoriality in $R$.
* `Langlands.Padic.acrisFrob_smul`, `Langlands.Padic.bcrisPlusFrob_smul`: the Frobenius commutes with the action of $M$.
* `Langlands.Padic.isAdicCauchy_logPartial`: the partial sums of the series of $\log [\varepsilon]$ are a $p$-adic Cauchy sequence in $A_{cris}^0(R)$.
* `Langlands.Padic.bcris_smulCommClass`: the action of $M$ on $B_{cris}(R)$ is $\mathbb{Q}_p$-linear.
* `Langlands.Padic.monodromy_X`, `Langlands.Padic.monodromy_C`, `Langlands.Padic.monodromy_mul`: $N(u) = -1$, $N = 0$ on the coefficients, and the Leibniz rule.
* `Langlands.Padic.untilt_epsCp`: the untilt of $\varepsilon$ is $1$.
* `Langlands.Padic.isCrystallineQp_trivial_of_nontrivial`: if $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation is crystalline.

## Implementation notes

The file does not prove these statements: $g t = \chi(g) t$, $\varphi(t) = p t$, $t \ne 0$ and $\varepsilon \ne 1$. Thus $B_{cris}(R)$ inverts all the elements $g t$, which is $B_{cris}^+(R)[1/t]$ only when $g t = \chi(g) t$, and the file does not show that $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring. The Frobenius on $B_{cris}(R)$ and $B_{st}(R)$, the action of $G_{\mathbb{Q}_p}$ on $B_{st}(R)$ with $g u = u + c(g) t$, and the predicates for semistable and potentially semistable representations are not in this file.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

set_option hygiene false in
/-- The ring $W(R^\flat)[1/p]$. -/
local notation "LocW[" R ", " p "]" => Localization.Away (p : WittVector p (PreTilt R p))

section Acris

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S : Type u} [CommRing S]
  {T : Type u} [CommRing T] [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
  [IsAdicComplete (span {(p : T)}) T]

/-- The divided powers $x^n / n!$ in $W(R^\flat)[1/p]$ of the elements $x$ of $\ker \theta$: the elements $y$ with $n! \, y = x^n$. -/
def dividedPowers (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
    [IsAdicComplete (span {(p : R)}) R] : Set (LocW[R, p]) :=
  {y | ∃ x ∈ RingHom.ker (fontaineTheta R p), ∃ n : ℕ,
    (n.factorial : LocW[R, p]) * y = algebraMap _ _ x ^ n}

/-- The ring $A_{cris}^0(R)$: the $W(R^\flat)$-subalgebra of $W(R^\flat)[1/p]$ that the divided powers $x^n / n!$ of the elements $x$ of $\ker \theta$ generate. -/
noncomputable def acrisZero (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] :
    Subalgebra (WittVector p (PreTilt R p)) (LocW[R, p]) :=
  Algebra.adjoin _ (dividedPowers R p)

/-- The map of $W(\cdot^\flat)[1/p]$ sends the divided powers into the divided powers. -/
theorem locMap_mem_dividedPowers (f : R →+* S) {y : LocW[R, p]}
    (hy : y ∈ dividedPowers R p) : locMap p f y ∈ dividedPowers S p := by
  obtain ⟨x, hx, n, hn⟩ := hy
  refine ⟨wittMap p f x, ?_, n, ?_⟩
  · rw [RingHom.mem_ker, ← RingHom.comp_apply, fontaineTheta_comp_wittMap, RingHom.comp_apply,
      RingHom.mem_ker.1 hx, map_zero]
  · rw [← locMap_algebraMap, ← map_pow, ← hn, map_mul, map_natCast]

/-- The map of $W(\cdot^\flat)[1/p]$ sends $A_{cris}^0(R)$ into $A_{cris}^0(S)$. -/
theorem locMap_mem_acrisZero (f : R →+* S) {y : LocW[R, p]}
    (hy : y ∈ acrisZero R p) : locMap p f y ∈ acrisZero S p := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin (locMap_mem_dividedPowers f hy)
  | algebraMap r =>
    rw [locMap_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

variable (p) in
/-- The map $A_{cris}^0(R) \to A_{cris}^0(S)$ of a ring homomorphism $f : R \to S$. -/
noncomputable def acrisZeroMap (f : R →+* S) : acrisZero R p →+* acrisZero S p :=
  RingHom.codRestrict ((locMap p f).comp (acrisZero R p).val.toRingHom) (acrisZero S p)
    (fun y => locMap_mem_acrisZero f y.2)

/-- The map $A_{cris}^0(R) \to A_{cris}^0(S)$ is the restriction of the map of $W(\cdot^\flat)[1/p]$. -/
theorem coe_acrisZeroMap (f : R →+* S) (y : acrisZero R p) :
    (acrisZeroMap p f y : LocW[S, p]) = locMap p f y :=
  rfl

/-- The map of $A_{cris}^0$ of the identity is the identity. -/
theorem acrisZeroMap_id : acrisZeroMap p (RingHom.id R) = RingHom.id _ := by
  ext y
  rw [coe_acrisZeroMap, locMap_id]
  rfl

/-- The map of $A_{cris}^0$ of a composite is the composite of the maps. -/
theorem acrisZeroMap_comp (f : R →+* S) (g : S →+* T) :
    acrisZeroMap p (g.comp f) = (acrisZeroMap p g).comp (acrisZeroMap p f) := by
  ext y
  rw [coe_acrisZeroMap, locMap_comp]
  rfl

/-- The map $A_{cris}^0(R) \to A_{cris}^0(S)$ sends $p A_{cris}^0(R)$ into $p A_{cris}^0(S)$. -/
theorem span_p_le_comap_acrisZeroMap (f : R →+* S) :
    span {(p : acrisZero R p)} ≤ (span {(p : acrisZero S p)}).comap (acrisZeroMap p f) :=
  @span_p_le_comap p (acrisZero R p) (Subalgebra.toCommRing _) (acrisZero S p)
    (Subalgebra.toCommRing _) (acrisZeroMap p f)

/-- The ring $A_{cris}(R)$: the $p$-adic completion of $A_{cris}^0(R)$. -/
abbrev Acris (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
    [IsAdicComplete (span {(p : R)}) R] : Type u :=
  AdicCompletion (span {(p : acrisZero R p)}) (acrisZero R p)

/-- The ring $B_{cris}^+(R) = A_{cris}(R)[1/p]$. -/
abbrev BcrisPlus (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
    [IsAdicComplete (span {(p : R)}) R] : Type u :=
  Localization.Away (p : Acris R p)

variable (p) in
/-- The map $A_{cris}(R) \to A_{cris}(S)$ of a ring homomorphism $f : R \to S$. -/
noncomputable def acrisMap (f : R →+* S) : Acris R p →+* Acris S p :=
  @adicMap (acrisZero R p) (acrisZero S p) (Subalgebra.toCommRing _) (Subalgebra.toCommRing _)
    (acrisZeroMap p f) (span {(p : acrisZero R p)}) (span {(p : acrisZero S p)})
    (span_p_le_comap_acrisZeroMap f)

/-- The map $A_{cris}(R) \to A_{cris}(S)$ extends the map of $A_{cris}^0$. -/
theorem acrisMap_of (f : R →+* S) (x : acrisZero R p) :
    acrisMap p f (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ (acrisZeroMap p f x) :=
  adicMap_of _ _ _ _ x

/-- The map of $A_{cris}$ of the identity is the identity. -/
theorem acrisMap_id : acrisMap p (RingHom.id R) = RingHom.id _ := by
  unfold acrisMap
  rw [@adicMap_congr (acrisZero R p) (acrisZero R p) (Subalgebra.toCommRing _)
    (Subalgebra.toCommRing _) _ (RingHom.id _) _ _ _ (fun x hx => by rwa [Ideal.comap_id])
    acrisZeroMap_id]
  exact @adicMap_id (acrisZero R p) (Subalgebra.toCommRing _) _ _

/-- The map of $A_{cris}$ of a composite is the composite of the maps. -/
theorem acrisMap_comp (f : R →+* S) (g : S →+* T) :
    acrisMap p (g.comp f) = (acrisMap p g).comp (acrisMap p f) := by
  have h3 : span {(p : acrisZero R p)} ≤
      (span {(p : acrisZero T p)}).comap ((acrisZeroMap p g).comp (acrisZeroMap p f)) :=
    fun x hx => by
      rw [Ideal.mem_comap, RingHom.comp_apply]
      exact Ideal.mem_comap.1 (span_p_le_comap_acrisZeroMap g
        (Ideal.mem_comap.1 (span_p_le_comap_acrisZeroMap f hx)))
  unfold acrisMap
  rw [@adicMap_congr (acrisZero R p) (acrisZero T p) (Subalgebra.toCommRing _)
    (Subalgebra.toCommRing _) _ _ _ _ _ h3 (acrisZeroMap_comp f g)]
  exact @adicMap_comp (acrisZero R p) (acrisZero S p) (acrisZero T p) (Subalgebra.toCommRing _)
    (Subalgebra.toCommRing _) (Subalgebra.toCommRing _) _ _ _ _ _
    (span_p_le_comap_acrisZeroMap f) (span_p_le_comap_acrisZeroMap g) h3

variable (p) in
/-- The map $B_{cris}^+(R) \to B_{cris}^+(S)$ of a ring homomorphism $f : R \to S$. -/
noncomputable def bcrisPlusMap (f : R →+* S) : BcrisPlus R p →+* BcrisPlus S p :=
  Localization.awayLift ((algebraMap _ _).comp (acrisMap p f)) (p : Acris R p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Acris S p))

/-- The map $B_{cris}^+(R) \to B_{cris}^+(S)$ extends the map of $A_{cris}$. -/
@[simp]
theorem bcrisPlusMap_algebraMap (f : R →+* S) (x : Acris R p) :
    bcrisPlusMap p f (algebraMap _ _ x) = algebraMap _ _ (acrisMap p f x) := by
  simp [bcrisPlusMap]

/-- The map of $B_{cris}^+$ of the identity is the identity. -/
theorem bcrisPlusMap_id : bcrisPlusMap p (RingHom.id R) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : Acris R p)) ?_
  ext x
  simp [acrisMap_id]

/-- The map of $B_{cris}^+$ of a composite is the composite of the maps. -/
theorem bcrisPlusMap_comp (f : R →+* S) (g : S →+* T) :
    bcrisPlusMap p (g.comp f) = (bcrisPlusMap p g).comp (bcrisPlusMap p f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : Acris R p)) ?_
  ext x
  simp [acrisMap_comp]

end Acris

section Frobenius

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]

/-- The Frobenius of $W(R^\flat)$ is congruent to the $p$-th power modulo $p$: $\varphi(x) = x^p + p z$ for some $z \in W(R^\flat)$. -/
theorem exists_frobenius_eq_pow_add (x : WittVector p (PreTilt R p)) :
    ∃ z, frobenius x = x ^ p + p * z := by
  set a := frobenius x - x ^ p with ha
  have h0 : a.coeff 0 = 0 := by
    have : WittVector.constantCoeff a = 0 := by
      rw [ha, map_sub, map_pow, constantCoeff_apply, constantCoeff_apply, coeff_frobenius_charP,
        sub_self]
    rwa [constantCoeff_apply] at this
  obtain ⟨w, hw⟩ := (frobenius_bijective p (PreTilt R p)).2 (a.shift (0 + 1))
  have hv : w * p = a := by
    rw [← verschiebung_frobenius, hw]
    refine (verschiebung_shift a 0 (fun i hi => by
      rw [Nat.lt_one_iff.1 hi]
      exact h0)).trans ?_
    ext n
    simp [shift_coeff]
  refine ⟨w, ?_⟩
  rw [mul_comm, hv, ha]
  ring

/-- For each $m$, the element $p^m / m!$ of $W(R^\flat)[1/p]$ lies in the image of $W(R^\flat)$, since $v_p(m!) \le m$. -/
theorem exists_factorial_mul_eq_p_pow (m : ℕ) :
    ∃ w : WittVector p (PreTilt R p),
      (m.factorial : LocW[R, p]) * algebraMap _ _ w =
        (p : LocW[R, p]) ^ m := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hm : (m.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  set c : ℚ_[p] := (p : ℚ_[p]) ^ m / m.factorial with hc_def
  have hc : ‖c‖ ≤ 1 := by
    rw [Padic.norm_le_one_iff_val_nonneg, hc_def, div_eq_mul_inv,
      Padic.valuation_mul (pow_ne_zero _ hp) (inv_ne_zero hm), Padic.valuation_inv,
      Padic.valuation_pow, Padic.valuation_p, Padic.valuation_natCast]
    have := padicValNat_factorial_le (p := p) m
    omega
  set z : ℤ_[p] := ⟨c, (PadicInt.mem_subring_iff p).2 hc⟩
  refine ⟨zpToWitt R p z, ?_⟩
  rw [← qpToLoc_algebraMap, ← map_natCast (qpToLoc R p), ← map_mul]
  have : (m.factorial : ℚ_[p]) * algebraMap ℤ_[p] ℚ_[p] z = (p : ℚ_[p]) ^ m := by
    change (m.factorial : ℚ_[p]) * c = _
    rw [hc_def]
    field_simp
  rw [this, map_pow, map_natCast]

/-- Each factorial $N!$ is a unit in $W(R^\flat)[1/p]$. -/
theorem isUnit_factorial_loc (N : ℕ) :
    IsUnit (N.factorial : LocW[R, p]) := by
  rw [← map_natCast (qpToLoc R p)]
  exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))).map _

/-- The Frobenius $\varphi$ of $W(R^\flat)[1/p]$: the extension of the Frobenius of $W(R^\flat)$. -/
noncomputable def locFrob (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] :
    LocW[R, p] →+*
      LocW[R, p] :=
  Localization.awayLift ((algebraMap _ _).comp frobenius) (p : WittVector p (PreTilt R p))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : WittVector p (PreTilt R p)))

/-- The Frobenius of $W(R^\flat)[1/p]$ extends the Frobenius of $W(R^\flat)$. -/
@[simp]
theorem locFrob_algebraMap (x : WittVector p (PreTilt R p)) :
    locFrob R p (algebraMap _ _ x) = algebraMap _ _ (frobenius x) := by
  simp [locFrob]

variable [IsAdicComplete (span {(p : R)}) R]

/-- The Frobenius of $W(R^\flat)[1/p]$ sends each divided power $x^n / n!$ with $x \in \ker \theta$ into $A_{cris}^0(R)$. With $\varphi(x) = x^p + p z$, the proof writes $\varphi(x)^n / n!$ as $\sum_k \frac{(pk)!}{k!} \cdot \frac{x^{pk}}{(pk)!} \cdot \frac{p^{n-k}}{(n-k)!} \cdot z^{n-k}$. -/
theorem locFrob_mem_acrisZero_of_mem {y : LocW[R, p]}
    (hy : y ∈ dividedPowers R p) : locFrob R p y ∈ acrisZero R p := by
  obtain ⟨x, hx, n, hn⟩ := hy
  obtain ⟨z, hz⟩ := exists_frobenius_eq_pow_add x
  set x' : LocW[R, p] := algebraMap _ _ x
  set z' : LocW[R, p] := algebraMap _ _ z
  let u : ℕ → (LocW[R, p])ˣ := fun N => (isUnit_factorial_loc (R := R) N).unit
  let d : ℕ → LocW[R, p] := fun k => ((u (p * k))⁻¹ : (LocW[R, p])ˣ) * x' ^ (p * k)
  have hd (k : ℕ) : ((p * k).factorial : LocW[R, p]) * d k = x' ^ (p * k) := by
    change ((u (p * k) : (LocW[R, p])ˣ) : LocW[R, p]) * _ = _
    exact Units.mul_inv_cancel_left _ _
  let e : ℕ → WittVector p (PreTilt R p) := fun m =>
    Classical.choose (exists_factorial_mul_eq_p_pow (R := R) m)
  have he (m : ℕ) : (m.factorial : LocW[R, p]) * algebraMap _ _ (e m) = (p : LocW[R, p]) ^ m :=
    Classical.choose_spec (exists_factorial_mul_eq_p_pow (R := R) m)
  let T : ℕ → LocW[R, p] := fun k =>
    (((p * k).factorial / k.factorial : ℕ) : LocW[R, p]) * d k *
    algebraMap _ _ (e (n - k)) * z' ^ (n - k)
  have hT (k : ℕ) : T k ∈ acrisZero R p := by
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.natCast_mem _ _) (Algebra.subset_adjoin ⟨x, hx, p * k, hd k⟩))
      (Subalgebra.algebraMap_mem _ _)) (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _)
  have hsum : locFrob R p y = ∑ k ∈ Finset.range (n + 1), T k := by
    refine (isUnit_factorial_loc (R := R) n).mul_left_cancel ?_
    rw [Finset.mul_sum]
    have h1 : (n.factorial : LocW[R, p]) * locFrob R p y = (x' ^ p + p * z') ^ n := by
      rw [← map_natCast (locFrob R p) n.factorial, ← map_mul, hn, map_pow, locFrob_algebraMap,
        hz, map_add, map_pow, map_mul, map_natCast]
    rw [h1, add_pow]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hnat : n.factorial * ((p * k).factorial / k.factorial) =
        n.choose k * (p * k).factorial * (n - k).factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hkn]
      have hdvd := Nat.mul_div_cancel' (Nat.factorial_dvd_factorial
        (Nat.le_mul_of_pos_left k (Fact.out : p.Prime).pos))
      calc n.choose k * k.factorial * (n - k).factorial * ((p * k).factorial / k.factorial)
          = n.choose k * (n - k).factorial *
              (k.factorial * ((p * k).factorial / k.factorial)) := by ring
        _ = _ := by rw [hdvd]; ring
    have hcast : (n.factorial : LocW[R, p]) *
        (((p * k).factorial / k.factorial : ℕ) : LocW[R, p]) =
        (n.choose k : LocW[R, p]) * ((p * k).factorial : LocW[R, p]) *
          ((n - k).factorial : LocW[R, p]) := by
      have := congrArg (Nat.cast : ℕ → LocW[R, p]) hnat
      simpa only [Nat.cast_mul] using this
    symm
    calc (n.factorial : LocW[R, p]) * T k
        = ((n.factorial : LocW[R, p]) *
            (((p * k).factorial / k.factorial : ℕ) : LocW[R, p])) * d k *
            algebraMap _ _ (e (n - k)) * z' ^ (n - k) := by
          simp only [T]
          ring
      _ = (n.choose k : LocW[R, p]) * (((p * k).factorial : LocW[R, p]) * d k) *
            (((n - k).factorial : LocW[R, p]) * algebraMap _ _ (e (n - k))) * z' ^ (n - k) := by
          rw [hcast]
          ring
      _ = (x' ^ p) ^ k * (p * z') ^ (n - k) * (n.choose k : LocW[R, p]) := by
          rw [hd, he, ← pow_mul]
          ring
  rw [hsum]
  exact Subalgebra.sum_mem _ fun k _ => hT k

/-- The Frobenius of $W(R^\flat)[1/p]$ sends $A_{cris}^0(R)$ into itself. -/
theorem locFrob_mem_acrisZero {y : LocW[R, p]}
    (hy : y ∈ acrisZero R p) : locFrob R p y ∈ acrisZero R p := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact locFrob_mem_acrisZero_of_mem hy
  | algebraMap r =>
    rw [locFrob_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

variable (R p) in
/-- The Frobenius $\varphi$ of $A_{cris}^0(R)$: the restriction of the Frobenius of $W(R^\flat)[1/p]$. -/
noncomputable def acrisZeroFrob : acrisZero R p →+* acrisZero R p :=
  RingHom.codRestrict ((locFrob R p).comp (acrisZero R p).val.toRingHom) (acrisZero R p)
    (fun y => locFrob_mem_acrisZero y.2)

/-- The Frobenius of $A_{cris}^0(R)$ is the restriction of the Frobenius of $W(R^\flat)[1/p]$. -/
theorem coe_acrisZeroFrob (y : acrisZero R p) :
    (acrisZeroFrob R p y : LocW[R, p]) = locFrob R p y :=
  rfl

/-- The Frobenius of $A_{cris}^0(R)$ sends $p A_{cris}^0(R)$ into itself. -/
theorem span_p_le_comap_acrisZeroFrob :
    span {(p : acrisZero R p)} ≤ (span {(p : acrisZero R p)}).comap (acrisZeroFrob R p) :=
  @span_p_le_comap p (acrisZero R p) (Subalgebra.toCommRing _) (acrisZero R p)
    (Subalgebra.toCommRing _) (acrisZeroFrob R p)

variable (R p) in
/-- The Frobenius $\varphi$ of $A_{cris}(R)$: the map of $p$-adic completions of the Frobenius of $A_{cris}^0(R)$. -/
noncomputable def acrisFrob : Acris R p →+* Acris R p :=
  @adicMap (acrisZero R p) (acrisZero R p) (Subalgebra.toCommRing _) (Subalgebra.toCommRing _)
    (acrisZeroFrob R p) (span {(p : acrisZero R p)}) (span {(p : acrisZero R p)})
    span_p_le_comap_acrisZeroFrob

/-- The Frobenius of $A_{cris}(R)$ extends the Frobenius of $A_{cris}^0(R)$. -/
theorem acrisFrob_of (x : acrisZero R p) :
    acrisFrob R p (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ (acrisZeroFrob R p x) :=
  adicMap_of _ _ _ _ x

variable (R p) in
/-- The Frobenius $\varphi$ of $B_{cris}^+(R) = A_{cris}(R)[1/p]$. -/
noncomputable def bcrisPlusFrob : BcrisPlus R p →+* BcrisPlus R p :=
  Localization.awayLift ((algebraMap _ _).comp (acrisFrob R p)) (p : Acris R p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Acris R p))

/-- The Frobenius of $B_{cris}^+(R)$ extends the Frobenius of $A_{cris}(R)$. -/
@[simp]
theorem bcrisPlusFrob_algebraMap (x : Acris R p) :
    bcrisPlusFrob R p (algebraMap _ _ x) = algebraMap _ _ (acrisFrob R p x) := by
  simp [bcrisPlusFrob]

end Frobenius

section FrobeniusCommutes

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {p : ℕ} [Fact p.Prime]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The map of Witt vectors of a ring homomorphism commutes with the Frobenius. -/
theorem wittMap_frobenius (f : R →+* S) (x : WittVector p (PreTilt R p)) :
    wittMap p f (frobenius x) = frobenius (wittMap p f x) := by
  ext n
  simp [wittMap, coeff_frobenius_charP]

/-- The map of $W(\cdot^\flat)[1/p]$ of a ring homomorphism commutes with the Frobenius. -/
theorem locMap_comp_locFrob (f : R →+* S) :
    (locMap p f).comp (locFrob R p) = (locFrob S p).comp (locMap p f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p))) ?_
  ext x
  simp [wittMap_frobenius]

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- The map of $A_{cris}^0$ of a ring homomorphism commutes with the Frobenius. -/
theorem acrisZeroMap_comp_acrisZeroFrob (f : R →+* S) :
    (acrisZeroMap p f).comp (acrisZeroFrob R p) = (acrisZeroFrob S p).comp (acrisZeroMap p f) := by
  ext y
  change locMap p f (locFrob R p y) = locFrob S p (locMap p f y)
  rw [← RingHom.comp_apply, locMap_comp_locFrob, RingHom.comp_apply]

/-- The map of $A_{cris}$ of a ring homomorphism commutes with the Frobenius. -/
theorem acrisMap_comp_acrisFrob (f : R →+* S) :
    (acrisMap p f).comp (acrisFrob R p) = (acrisFrob S p).comp (acrisMap p f) := by
  have h1 : span {(p : acrisZero R p)} ≤ (span {(p : acrisZero S p)}).comap
      ((acrisZeroMap p f).comp (acrisZeroFrob R p)) := fun x hx => by
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_comap.1 (span_p_le_comap_acrisZeroMap f
      (Ideal.mem_comap.1 (span_p_le_comap_acrisZeroFrob hx)))
  have h2 : span {(p : acrisZero R p)} ≤ (span {(p : acrisZero S p)}).comap
      ((acrisZeroFrob S p).comp (acrisZeroMap p f)) := fun x hx => by
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_comap.1 (span_p_le_comap_acrisZeroFrob
      (Ideal.mem_comap.1 (span_p_le_comap_acrisZeroMap f hx)))
  unfold acrisMap acrisFrob
  rw [← @adicMap_comp (acrisZero R p) (acrisZero R p) (acrisZero S p) (Subalgebra.toCommRing _)
      (Subalgebra.toCommRing _) (Subalgebra.toCommRing _) _ _ _ _ _
      span_p_le_comap_acrisZeroFrob (span_p_le_comap_acrisZeroMap f) h1,
    ← @adicMap_comp (acrisZero R p) (acrisZero S p) (acrisZero S p) (Subalgebra.toCommRing _)
      (Subalgebra.toCommRing _) (Subalgebra.toCommRing _) _ _ _ _ _
      (span_p_le_comap_acrisZeroMap f) span_p_le_comap_acrisZeroFrob h2]
  exact @adicMap_congr (acrisZero R p) (acrisZero S p) (Subalgebra.toCommRing _)
    (Subalgebra.toCommRing _) _ _ _ _ h1 h2 (acrisZeroMap_comp_acrisZeroFrob f)

/-- The map of $B_{cris}^+$ of a ring homomorphism commutes with the Frobenius. -/
theorem bcrisPlusMap_comp_bcrisPlusFrob (f : R →+* S) :
    (bcrisPlusMap p f).comp (bcrisPlusFrob R p) = (bcrisPlusFrob S p).comp (bcrisPlusMap p f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p : Acris R p)) ?_
  ext x
  simp only [RingHom.comp_apply, bcrisPlusFrob_algebraMap, bcrisPlusMap_algebraMap]
  rw [← RingHom.comp_apply (acrisMap p f), acrisMap_comp_acrisFrob, RingHom.comp_apply]

end FrobeniusCommutes

section Log

/-- In a commutative ring $A$, each multiple $p^m c$ is in $(p)^m A$. -/
theorem mem_span_p_pow_smul_top {A : Type*} [CommRing A] (p m : ℕ) (c : A) :
    (p : A) ^ m * c ∈ (span {(p : A)} ^ m • ⊤ : Submodule A A) := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩

/-- For $p m \le j$, the power $p^m$ divides $j!$. -/
theorem p_pow_dvd_factorial (p : ℕ) [Fact p.Prime] {m j : ℕ} (h : p * m ≤ j) :
    p ^ m ∣ j.factorial := by
  refine dvd_trans ?_ (Nat.factorial_dvd_factorial h)
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _), padicValNat_factorial_mul]
  omega

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- For $\varepsilon \in R^\flat$ with untilt $1$, the element $[\varepsilon] - 1$ of $W(R^\flat)$ is in $\ker \theta$. -/
theorem teichmuller_sub_one_mem_ker {ε : PreTilt R p} (hε : ε.untilt = 1) :
    teichmuller p ε - 1 ∈ RingHom.ker (fontaineTheta R p) := by
  rw [RingHom.mem_ker, map_sub, map_one, fontaineTheta_teichmuller, hε, sub_self]

/-- The divided power $([\varepsilon] - 1)^j / j!$ in $W(R^\flat)[1/p]$. -/
noncomputable def logDiv (ε : PreTilt R p) (j : ℕ) : LocW[R, p] :=
  (((isUnit_factorial_loc (R := R) j).unit)⁻¹ : (LocW[R, p])ˣ) *
    algebraMap _ _ (teichmuller p ε - 1) ^ j

omit [IsAdicComplete (span {(p : R)}) R] in
/-- The defining property of the divided power: $j! \cdot ([\varepsilon] - 1)^{[j]} = ([\varepsilon] - 1)^j$. -/
theorem factorial_mul_logDiv (ε : PreTilt R p) (j : ℕ) :
    (j.factorial : LocW[R, p]) * logDiv ε j =
      algebraMap _ _ (teichmuller p ε - 1) ^ j :=
  Units.mul_inv_cancel_left ((isUnit_factorial_loc (R := R) j).unit) _

/-- For $\varepsilon$ with untilt $1$, the divided power $([\varepsilon] - 1)^j / j!$ is in $A_{cris}^0(R)$. -/
theorem logDiv_mem {ε : PreTilt R p} (hε : ε.untilt = 1) (j : ℕ) :
    logDiv ε j ∈ acrisZero R p :=
  Algebra.subset_adjoin ⟨_, teichmuller_sub_one_mem_ker hε, j, factorial_mul_logDiv ε j⟩

/-- The $j$-th term $(-1)^j ([\varepsilon] - 1)^{j+1} / (j+1) = (-1)^j \, j! \, ([\varepsilon] - 1)^{[j+1]}$ of the series of $\log [\varepsilon]$, as an element of $A_{cris}^0(R)$. -/
noncomputable def logTerm {ε : PreTilt R p} (hε : ε.untilt = 1) (j : ℕ) : acrisZero R p :=
  ⟨(-1) ^ j * (j.factorial : LocW[R, p]) *
    logDiv ε (j + 1), Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
      (Subalgebra.natCast_mem _ _)) (logDiv_mem hε _)⟩

/-- For $p m \le j$, the $j$-th term of the series of $\log [\varepsilon]$ is in $p^m A_{cris}^0(R)$. -/
theorem logTerm_mem {ε : PreTilt R p} (hε : ε.untilt = 1) {m j : ℕ} (h : p * m ≤ j) :
    logTerm hε j ∈
      (span {(p : acrisZero R p)} ^ m • ⊤ : Submodule (acrisZero R p) (acrisZero R p)) := by
  obtain ⟨c, hc⟩ := p_pow_dvd_factorial p h
  have : logTerm hε j = (p : acrisZero R p) ^ m *
      ((-1) ^ j * (c : acrisZero R p) * ⟨logDiv ε (j + 1), logDiv_mem hε _⟩) := by
    apply Subtype.ext
    change (-1) ^ j * (j.factorial : LocW[R, p]) *
      logDiv ε (j + 1) = (p : LocW[R, p]) ^ m *
        ((-1) ^ j * (c : LocW[R, p]) * logDiv ε (j + 1))
    rw [hc, Nat.cast_mul, Nat.cast_pow]
    ring
  rw [this]
  exact @mem_span_p_pow_smul_top (acrisZero R p) (Subalgebra.toCommRing _) p m _

/-- The partial sums $\sum_{j < N} (-1)^j ([\varepsilon] - 1)^{j+1} / (j+1)$ of the series of $\log [\varepsilon]$. -/
noncomputable def logPartial {ε : PreTilt R p} (hε : ε.untilt = 1) (N : ℕ) : acrisZero R p :=
  ∑ j ∈ Finset.range N, logTerm hε j

/-- The partial sums $s_{pk}$ of the series of $\log [\varepsilon]$ form a $p$-adic Cauchy sequence in $A_{cris}^0(R)$: $s_{pm} \equiv s_{pn}$ modulo $p^m$ for $m \le n$. -/
theorem isAdicCauchy_logPartial {ε : PreTilt R p} (hε : ε.untilt = 1) :
    AdicCompletion.IsAdicCauchy (span {(p : acrisZero R p)}) (acrisZero R p)
      (fun k => logPartial hε (p * k)) := by
  intro m n hmn
  dsimp only
  rw [SModEq.sub_mem, logPartial, logPartial, ← neg_sub, neg_mem_iff,
    ← Finset.sum_range_add_sum_Ico _ (Nat.mul_le_mul_left p hmn), add_sub_cancel_left]
  exact Submodule.sum_mem _ fun j hj => logTerm_mem hε (Finset.mem_Ico.1 hj).1

/-- The element $t = \log [\varepsilon] = \sum_{n \ge 1} (-1)^{n+1} ([\varepsilon] - 1)^n / n$ of $A_{cris}(R)$, for $\varepsilon \in R^\flat$ with untilt $1$. It is the limit of the partial sums $s_{pk}$. For $R = \mathcal{O}_{\mathbb{C}_p}$ and $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \dots)$ this is the period $t$ of $\mathbb{Q}_p(1)$; this file does not prove the formula $g t = \chi(g) t$. -/
noncomputable def logTeich {ε : PreTilt R p} (hε : ε.untilt = 1) : Acris R p :=
  AdicCompletion.mk _ _ ⟨_, isAdicCauchy_logPartial hε⟩

end Log

section Action

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable (M : Type*) [Monoid M] [MulSemiringAction M R]

/-- The action of $M$ on $A_{cris}(R)$ by ring endomorphisms. -/
noncomputable instance acrisAction : MulSemiringAction M (Acris R p) :=
  mulSemiringActionOfMap (fun g => acrisMap p (MulSemiringAction.toRingHom M R g))
    (by rw [toRingHom_one, acrisMap_id]) (fun g h => by rw [toRingHom_mul, acrisMap_comp])

/-- The action of $g$ on $A_{cris}(R)$ is the map of $A_{cris}$ of $x \mapsto g x$. -/
theorem acris_smul_def (g : M) (x : Acris R p) :
    g • x = acrisMap p (MulSemiringAction.toRingHom M R g) x := rfl

/-- The action of $M$ on $B_{cris}^+(R)$ by ring endomorphisms. -/
noncomputable instance bcrisPlusAction : MulSemiringAction M (BcrisPlus R p) :=
  mulSemiringActionOfMap (fun g => bcrisPlusMap p (MulSemiringAction.toRingHom M R g))
    (by rw [toRingHom_one, bcrisPlusMap_id]) (fun g h => by rw [toRingHom_mul, bcrisPlusMap_comp])

/-- The action of $g$ on $B_{cris}^+(R)$ is the map of $B_{cris}^+$ of $x \mapsto g x$. -/
theorem bcrisPlus_smul_def (g : M) (x : BcrisPlus R p) :
    g • x = bcrisPlusMap p (MulSemiringAction.toRingHom M R g) x := rfl

/-- The Frobenius of $A_{cris}(R)$ commutes with the action of $M$: $\varphi(g x) = g \varphi(x)$. -/
theorem acrisFrob_smul (g : M) (x : Acris R p) :
    acrisFrob R p (g • x) = g • acrisFrob R p x := by
  rw [acris_smul_def, acris_smul_def, ← RingHom.comp_apply, ← RingHom.comp_apply,
    acrisMap_comp_acrisFrob]

/-- The Frobenius of $B_{cris}^+(R)$ commutes with the action of $M$: $\varphi(g x) = g \varphi(x)$. -/
theorem bcrisPlusFrob_smul (g : M) (x : BcrisPlus R p) :
    bcrisPlusFrob R p (g • x) = g • bcrisPlusFrob R p x := by
  rw [bcrisPlus_smul_def, bcrisPlus_smul_def, ← RingHom.comp_apply, ← RingHom.comp_apply,
    bcrisPlusMap_comp_bcrisPlusFrob]

end Action

section Bcris

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable (M : Type*) [Monoid M] [MulSemiringAction M R]

/-- The submonoid of $B_{cris}^+(R)$ that the elements $g t$ generate, for $g \in M$ and $t = \log [\varepsilon]$. -/
noncomputable def bcrisSubmonoid {ε : PreTilt R p} (hε : ε.untilt = 1) :
    Submonoid (BcrisPlus R p) :=
  Submonoid.closure
    (Set.range fun g : M => g • algebraMap (Acris R p) (BcrisPlus R p) (logTeich hε))

/-- The ring $B_{cris}(R)$: the localization of $B_{cris}^+(R)$ at the elements $g t$, for $g \in M$ and $t = \log [\varepsilon]$. For $R = \mathcal{O}_{\mathbb{C}_p}$ and $M = G_{\mathbb{Q}_p}$, the formula $g t = \chi(g) t$ makes this $B_{cris}^+[1/t]$; this file does not prove that formula, and it inverts all the $g t$ so that the action of $M$ extends. -/
abbrev Bcris {ε : PreTilt R p} (hε : ε.untilt = 1) : Type u :=
  Localization (bcrisSubmonoid M hε)

/-- The action of $h \in M$ on $B_{cris}^+(R)$ sends the submonoid of the elements $g t$ into itself. -/
theorem bcrisSubmonoid_le_comap {ε : PreTilt R p} (hε : ε.untilt = 1) (h : M) :
    bcrisSubmonoid M hε ≤ (bcrisSubmonoid M hε).comap
      (MulSemiringAction.toRingHom M (BcrisPlus R p) h) := by
  refine Submonoid.closure_le.2 ?_
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Submonoid.mem_comap, MulSemiringAction.toRingHom_apply]
  exact Submonoid.subset_closure ⟨h * g, mul_smul h g _⟩

variable {M} in
/-- The map of $B_{cris}(R)$ of $h \in M$. -/
noncomputable def bcrisMap {ε : PreTilt R p} (hε : ε.untilt = 1) (h : M) :
    Bcris M hε →+* Bcris M hε :=
  IsLocalization.map _ (MulSemiringAction.toRingHom M (BcrisPlus R p) h)
    (bcrisSubmonoid_le_comap M hε h)

variable {M} in
/-- The map of $B_{cris}(R)$ of $h$ extends the action of $h$ on $B_{cris}^+(R)$. -/
theorem bcrisMap_algebraMap {ε : PreTilt R p} (hε : ε.untilt = 1) (h : M) (x : BcrisPlus R p) :
    bcrisMap hε h (algebraMap _ _ x) = algebraMap _ _ (h • x) :=
  IsLocalization.map_eq _ _

/-- The action of $M$ on $B_{cris}(R)$ by ring endomorphisms. -/
noncomputable instance bcrisAction {ε : PreTilt R p} (hε : ε.untilt = 1) :
    MulSemiringAction M (Bcris M hε) :=
  mulSemiringActionOfMap (fun h => bcrisMap hε h)
    (IsLocalization.ringHom_ext (bcrisSubmonoid M hε) (RingHom.ext fun x => by
      rw [RingHom.comp_apply, bcrisMap_algebraMap, one_smul, RingHom.id_comp]))
    (fun g h => IsLocalization.ringHom_ext (bcrisSubmonoid M hε) (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, bcrisMap_algebraMap,
        bcrisMap_algebraMap, bcrisMap_algebraMap, mul_smul]))

variable {M} in
/-- The action of $g$ on $B_{cris}(R)$ extends the action on $B_{cris}^+(R)$. -/
theorem smul_algebraMap_bcris {ε : PreTilt R p} (hε : ε.untilt = 1) (g : M) (x : BcrisPlus R p) :
    g • (algebraMap (BcrisPlus R p) (Bcris M hε) x) = algebraMap _ _ (g • x) :=
  bcrisMap_algebraMap hε g x

end Bcris

section Qp

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S : Type u} [CommRing S]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- The map $\mathbb{Z}_p \to B_{cris}^+(R)$ through $W(R^\flat)$, $A_{cris}^0(R)$ and $A_{cris}(R)$. -/
noncomputable def zpToBcrisPlus (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] : ℤ_[p] →+* BcrisPlus R p :=
  (algebraMap (Acris R p) (BcrisPlus R p)).comp ((algebraMap (acrisZero R p) (Acris R p)).comp
    ((algebraMap (WittVector p (PreTilt R p)) (acrisZero R p)).comp (zpToWitt R p)))

/-- Each nonzero $p$-adic integer is a unit in $B_{cris}^+(R)$. -/
theorem isUnit_zpToBcrisPlus (y : nonZeroDivisors ℤ_[p]) : IsUnit (zpToBcrisPlus R p y) := by
  have hy : (y : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero y
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_pow, map_natCast]
  refine ((Units.isUnit _).map _).mul (IsUnit.pow _ ?_)
  simpa using IsLocalization.Away.algebraMap_isUnit (p : Acris R p)

/-- The map $\mathbb{Q}_p \to B_{cris}^+(R)$ that extends $\mathbb{Z}_p \to B_{cris}^+(R)$. -/
noncomputable def qpToBcrisPlus (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] : ℚ_[p] →+* BcrisPlus R p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) isUnit_zpToBcrisPlus

/-- The map $\mathbb{Q}_p \to B_{cris}^+(R)$ extends $\mathbb{Z}_p \to B_{cris}^+(R)$. -/
theorem qpToBcrisPlus_algebraMap (x : ℤ_[p]) :
    qpToBcrisPlus R p (algebraMap ℤ_[p] ℚ_[p] x) = zpToBcrisPlus R p x :=
  IsLocalization.lift_eq _ _

/-- The map of $B_{cris}^+$ of a ring homomorphism commutes with the maps from $\mathbb{Z}_p$. -/
theorem bcrisPlusMap_comp_zpToBcrisPlus (f : R →+* S) :
    (bcrisPlusMap p f).comp (zpToBcrisPlus R p) = zpToBcrisPlus S p := by
  ext x
  simp only [zpToBcrisPlus, RingHom.comp_apply, bcrisPlusMap_algebraMap]
  congr 1
  change acrisMap p f (AdicCompletion.of _ _ _) = AdicCompletion.of _ _ _
  rw [acrisMap_of]
  congr 1
  apply Subtype.ext
  rw [coe_acrisZeroMap]
  change locMap p f (algebraMap _ _ (zpToWitt R p x)) = algebraMap _ _ (zpToWitt S p x)
  rw [locMap_algebraMap]
  exact congrArg _ (RingHom.congr_fun (wittMap_comp_zpToWitt f) x)

/-- The map of $B_{cris}^+$ of a ring homomorphism commutes with the maps from $\mathbb{Q}_p$. -/
theorem bcrisPlusMap_comp_qpToBcrisPlus (f : R →+* S) :
    (bcrisPlusMap p f).comp (qpToBcrisPlus R p) = qpToBcrisPlus S p := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, qpToBcrisPlus_algebraMap,
    qpToBcrisPlus_algebraMap, ← RingHom.comp_apply, bcrisPlusMap_comp_zpToBcrisPlus]

/-- The $\mathbb{Q}_p$-algebra structure on $B_{cris}^+(R)$. -/
noncomputable instance bcrisPlusQpAlgebra : Algebra ℚ_[p] (BcrisPlus R p) :=
  (qpToBcrisPlus R p).toAlgebra

variable (M : Type*) [Monoid M] [MulSemiringAction M R]

/-- The action of $M$ on $B_{cris}(R)$ is $\mathbb{Q}_p$-linear. -/
instance bcris_smulCommClass {ε : PreTilt R p} (hε : ε.untilt = 1) :
    SMulCommClass M ℚ_[p] (Bcris M hε) where
  smul_comm g c x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    rw [IsScalarTower.algebraMap_apply ℚ_[p] (BcrisPlus R p) (Bcris M hε),
      smul_algebraMap_bcris, bcrisPlus_smul_def]
    exact congrArg _ (RingHom.congr_fun (bcrisPlusMap_comp_qpToBcrisPlus _) c)

end Qp

section Bst

section Monodromy

variable {A : Type*} [CommRing A]

variable (A) in
/-- The operator $N = -d/du$ on the polynomial ring $A[u]$, as an $A$-linear derivation. -/
noncomputable def monodromy : Derivation A (Polynomial A) (Polynomial A) :=
  (-1 : A) • Polynomial.derivative'

/-- The operator $N$ is $-d/du$. -/
theorem monodromy_apply (x : Polynomial A) : monodromy A x = -Polynomial.derivative x := by
  simp [monodromy]

/-- $N(u) = -1$. -/
theorem monodromy_X : monodromy A Polynomial.X = -1 := by
  simp [monodromy_apply]

/-- $N$ is zero on $A$. -/
theorem monodromy_C (b : A) : monodromy A (Polynomial.C b) = 0 := by
  simp

/-- The Leibniz rule $N(xy) = x N(y) + y N(x)$. -/
theorem monodromy_mul (x y : Polynomial A) :
    monodromy A (x * y) = x * monodromy A y + y * monodromy A x := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

end Monodromy

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable (M : Type*) [Monoid M] [MulSemiringAction M R]

/-- The ring $B_{st}(R) = B_{cris}(R)[u]$, the polynomial ring in one variable $u$ over $B_{cris}(R)$, with the monodromy operator `monodromy (Bcris M hε)`. The variable $u$ stands for $\log [p^\flat]$. -/
abbrev Bst {ε : PreTilt R p} (hε : ε.untilt = 1) : Type _ := Polynomial (Bcris M hε)

end Bst

section Cp

variable {p : ℕ} [Fact p.Prime]

/-- A primitive $p$-th root of unity in $\mathbb{C}_p$. -/
noncomputable def zetaCp (p : ℕ) [Fact p.Prime] : ℂ_[p] :=
  Classical.choose (HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] p)

/-- The element `zetaCp p` is a primitive $p$-th root of unity. -/
theorem isPrimitiveRoot_zetaCp : IsPrimitiveRoot (zetaCp p) p :=
  Classical.choose_spec (HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] p)

/-- A compatible sequence of $p$-power roots of unity in $\mathbb{C}_p$: $z_0 = 1$, $z_1$ is a primitive $p$-th root of unity, and $z_{n+1}^p = z_n$. -/
noncomputable def epsRoots (p : ℕ) [Fact p.Prime] : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => zetaCp p
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (epsRoots p (n + 1))
      (Fact.out : p.Prime).pos)

/-- The relation $z_{n+1}^p = z_n$. -/
theorem epsRoots_succ_pow (n : ℕ) : epsRoots p (n + 1) ^ p = epsRoots p n := by
  match n with
  | 0 => exact (isPrimitiveRoot_zetaCp (p := p)).pow_eq_one
  | n + 1 => exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (epsRoots p (n + 1))
      (Fact.out : p.Prime).pos)

/-- The relation $z_n^{p^n} = 1$. -/
theorem epsRoots_pow (n : ℕ) : epsRoots p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [epsRoots]
  | succ n ih => rw [pow_succ', pow_mul, epsRoots_succ_pow, ih]

/-- Each $z_n$ has norm $1$. -/
theorem norm_epsRoots (n : ℕ) : ‖epsRoots p n‖ = 1 := by
  have h : ‖epsRoots p n‖ ^ p ^ n = 1 := by rw [← norm_pow, epsRoots_pow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).1 h

/-- The element $z_n$ of $\mathcal{O}_{\mathbb{C}_p}$. -/
noncomputable def epsRootsInt (p : ℕ) [Fact p.Prime] (n : ℕ) : PadicComplexInt p :=
  ⟨epsRoots p n, (mem_padicComplexInt_iff _).2 (norm_epsRoots n).le⟩

/-- The element $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \ldots)$ of $\mathcal{O}_{\mathbb{C}_p}^\flat$. -/
noncomputable def epsCp (p : ℕ) [Fact p.Prime] : PreTilt (PadicComplexInt p) p :=
  ⟨fun n => Ideal.Quotient.mk _ (epsRootsInt p n), fun n => by
    change Ideal.Quotient.mk _ (epsRootsInt p (n + 1)) ^ p = _
    rw [← map_pow]
    exact congrArg _ (Subtype.ext (epsRoots_succ_pow n))⟩

/-- The untilt of $\varepsilon$ is $1$. -/
theorem untilt_epsCp : (epsCp p).untilt = 1 := by
  refine Perfection.teichmuller_spec fun n => ⟨epsRootsInt p n, rfl, ?_⟩
  have : epsRootsInt p n ^ p ^ n = 1 := Subtype.ext (by push_cast; exact epsRoots_pow n)
  rw [this]

variable (p) in
/-- The ring $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ with the action of $G_{\mathbb{Q}_p}$, built with $t = \log[\varepsilon]$ for $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \ldots)$. -/
abbrev BcrisCp : Type _ :=
  Bcris (R := PadicComplexInt p) (p := p) (Field.absoluteGaloisGroup ℚ_[p]) untilt_epsCp

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]

/-- A representation $V$ of $G_{\mathbb{Q}_p}$ on a finite-dimensional $\mathbb{Q}_p$-vector space is crystalline if it is $B_{cris}$-admissible, with $B_{cris} = B_{cris}(\mathcal{O}_{\mathbb{C}_p})$: the rank of $(B_{cris} \otimes_{\mathbb{Q}_p} V)^{G_{\mathbb{Q}_p}}$ over $B_{cris}^{G_{\mathbb{Q}_p}}$ is $\dim_{\mathbb{Q}_p} V$. -/
def IsCrystallineQp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V) : Prop :=
  IsAdmissible (BcrisCp p) ρ

/-- If $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is crystalline. -/
theorem isCrystallineQp_trivial_of_nontrivial [Nontrivial (BcrisCp p)] :
    IsCrystallineQp (Representation.trivial ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) ℚ_[p]) :=
  isAdmissible_trivial _

variable (p) in
/-- The ring $B_{st}(\mathcal{O}_{\mathbb{C}_p}) = B_{cris}(\mathcal{O}_{\mathbb{C}_p})[u]$. -/
abbrev BstCp : Type _ := Polynomial (BcrisCp p)

end Cp

end Langlands.Padic
