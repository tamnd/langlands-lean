/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations
import Mathlib.Algebra.Lie.AdjointAction.Derivation

/-!
# The elementary adjoint Chevalley group in characteristic zero

Let $k$ be a field of characteristic zero, let $\Phi$ be a reduced crystallographic root system over $k$ with a base $\Delta$, and let $L$ be the Lie algebra of the Geck construction of Mathlib (`RootPairing.GeckConstruction.lieAlgebra`). For a simple root $\alpha_i$, the Geck generators $e_i$ and $f_i$ have nilpotent adjoint endomorphisms. This file defines the root elements $x_{\pm\alpha_i}(t) = \exp(t\, \mathrm{ad}\, e_i)$ and $\exp(t\, \mathrm{ad}\, f_i)$ as Lie algebra automorphisms of $L$, and the elementary adjoint Chevalley group as the subgroup of $\mathrm{Aut}(L)$ that they generate. It also defines the action $h(\chi)$ of the points $\chi$ of the adjoint torus $T_{\mathrm{ad}}(k) = \mathrm{Hom}(\mathbb{Z}\Phi, k^\times)$ on $L$, and proves that the torus acts on the root subgroups through the roots.

The group in this file is a group of $k$-points in $\mathrm{Aut}(L)$. It is not the Chevalley group scheme over $\mathbb{Z}$, and it is not the full group $G_{\mathrm{ad}}(k)$ of $k$-points of the adjoint group.

## Main definitions

* `Langlands.Groups.Chevalley.lieAutGroup`: the group structure on the Lie algebra automorphisms $L \simeq L$.
* `Langlands.Groups.Chevalley.expAd`: the automorphism $\exp(t\, \mathrm{ad}\, x)$ for $x$ with $\mathrm{ad}\, x$ nilpotent, and `Langlands.Groups.Chevalley.expAdHom`, the homomorphism $t \mapsto \exp(t\, \mathrm{ad}\, x)$.
* `Langlands.Groups.Chevalley.adNilpotentExpSubgroup`: the subgroup that all these exponentials generate.
* `Langlands.Groups.Chevalley.simpleRootElement`, `Langlands.Groups.Chevalley.negSimpleRootElement`: the root elements $x_{\alpha_i}(t)$ and $x_{-\alpha_i}(t)$ of the Geck Lie algebra.
* `Langlands.Groups.Chevalley.ElementaryAdjointChevalleyGroup`: the subgroup of $\mathrm{Aut}(L)$ that the elements $x_{\pm\alpha_i}(t)$ generate.
* `Langlands.Groups.Chevalley.weylElement`: the element $w_{\alpha_i}(t) = x_{\alpha_i}(t) x_{-\alpha_i}(-t^{-1}) x_{\alpha_i}(t)$.
* `Langlands.Groups.Chevalley.rootLattice`: the root lattice $\mathbb{Z}\Phi$.
* `Langlands.Groups.Chevalley.torusElement`, `Langlands.Groups.Chevalley.torusHom`: the action $h(\chi)$ of a character $\chi : \mathbb{Z}\Phi \to k^\times$ on $L$, and the homomorphism $\chi \mapsto h(\chi)$.

## Main results

* `Langlands.Groups.Chevalley.expAd_add`, `Langlands.Groups.Chevalley.expAd_zero`, `Langlands.Groups.Chevalley.expAd_neg`: the one parameter group law of $t \mapsto \exp(t\, \mathrm{ad}\, x)$.
* `Langlands.Groups.Chevalley.expAd_apply_sl2_h`, `Langlands.Groups.Chevalley.expAd_apply_sl2_f`: the action of $\exp(t\, \mathrm{ad}\, e)$ on an $\mathfrak{sl}_2$ triple $(h, e, f)$.
* `Langlands.Groups.Chevalley.lieEquiv_mul_expAd_mul_inv`: the formula $\varphi \exp(t\, \mathrm{ad}\, x) \varphi^{-1} = \exp(t\, \mathrm{ad}(\varphi x))$, and `Langlands.Groups.Chevalley.adNilpotentExpSubgroup_normal`.
* `Langlands.Groups.Chevalley.isNilpotent_ad_geckE`, `Langlands.Groups.Chevalley.isNilpotent_ad_geckF`, `Langlands.Groups.Chevalley.isSl2Triple_geck`: the facts about the Geck generators that the construction uses.
* `Langlands.Groups.Chevalley.simpleRootElement_mem`, `Langlands.Groups.Chevalley.simpleRootElement_add`, `Langlands.Groups.Chevalley.simpleRootElement_neg` and the same for the negative roots: the root elements are in the group and the root subgroups are images of the additive group of $k$.
* `Langlands.Groups.Chevalley.simpleRootElement_apply_f`, `Langlands.Groups.Chevalley.negSimpleRootElement_apply_e` and the related results: the action on $e_i$, $h_i$ and $f_i$.
* `Langlands.Groups.Chevalley.weylElement_one_apply_geckE`, `Langlands.Groups.Chevalley.weylElement_one_apply_geckF`, `Langlands.Groups.Chevalley.weylElement_one_apply_geckH`: $w_{\alpha_i}(1)$ maps $e_i$, $f_i$, $h_i$ to $-f_i$, $-e_i$, $-h_i$.
* `Langlands.Groups.Chevalley.torusElement_apply_geckE`, `Langlands.Groups.Chevalley.torusElement_apply_geckF`, `Langlands.Groups.Chevalley.torusElement_apply_geckH`: $h(\chi)$ acts on $e_i$ by $\chi(\alpha_i)$, on $f_i$ by $\chi(\alpha_i)^{-1}$ and trivially on $h_i$.
* `Langlands.Groups.Chevalley.torusElement_mul_simpleRootElement_mul_inv`, `Langlands.Groups.Chevalley.torusElement_mul_negSimpleRootElement_mul_inv`: $h(\chi) x_{\pm\alpha_i}(t) h(\chi)^{-1} = x_{\pm\alpha_i}(\chi(\alpha_i)^{\pm 1} t)$.
* `Langlands.Groups.Chevalley.torusElement_conj_mem`: the torus normalizes the elementary adjoint Chevalley group.

## Implementation notes

The root system is over the field $k$ itself, so no base change is necessary. The Geck Lie algebra is a Lie subalgebra of the matrices indexed by $\Delta \sqcup \Phi$. The element $h(\chi)$ is conjugation by the diagonal matrix with the entries $1$ on $\Delta$ and $\chi(\alpha)$ on $\alpha \in \Phi$. The exponential is `LieDerivation.exp` of Mathlib, applied to the inner derivation $t\, \mathrm{ad}\, x$. The group is generated by the simple root elements only. The root elements $x_\alpha(t)$ for the other roots $\alpha$, the Steinberg relations, the Bruhat decomposition and the equality with $G_{\mathrm{ad}}(k)$ for algebraically closed $k$ are not in this file.

## References

* C. Chevalley, Sur certains groupes simples, Tohoku Math. J. 7 (1955).
* R. Steinberg, Lectures on Chevalley groups, chapters 1 to 3.
* M. Geck, On the construction of semisimple Lie algebras and Chevalley groups, Proc. Amer. Math. Soc. 145 (2017).
-/

noncomputable section

namespace Langlands.Groups.Chevalley

open RootPairing GeckConstruction

section AutGroup

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The group of Lie algebra automorphisms of $L$. The product $f g$ is the composite $f \circ g$. -/
instance lieAutGroup : Group (L ≃ₗ⁅R⁆ L) where
  mul f g := g.trans f
  toOne := inferInstance
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := LieEquiv.ext fun x => f.symm_apply_apply x

/-- The product of two automorphisms is the composite map. -/
@[simp] theorem lieAut_mul_apply (f g : L ≃ₗ⁅R⁆ L) (x : L) : (f * g) x = f (g x) := rfl

/-- The unit of the automorphism group is the identity map. -/
@[simp] theorem lieAut_one_apply (x : L) : (1 : L ≃ₗ⁅R⁆ L) x = x := rfl

/-- The inverse of an automorphism is the inverse map. -/
theorem lieAut_inv_apply (f : L ≃ₗ⁅R⁆ L) (x : L) : f⁻¹ x = f.symm x := rfl

end AutGroup

section Exp

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Module ℚ L]

omit [Module ℚ L] in
/-- If $\mathrm{ad}\, x$ is nilpotent, then $t \cdot \mathrm{ad}\, x$ is nilpotent for each scalar $t$. -/
theorem isNilpotent_smul_ad {x : L} (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) :
    IsNilpotent (t • LieAlgebra.ad k L x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [smul_pow, hn, smul_zero]

/-- The automorphism $\exp(t \cdot \mathrm{ad}\, x) = \sum_n t^n (\mathrm{ad}\, x)^n / n!$ of $L$ for an element $x$ with $\mathrm{ad}\, x$ nilpotent. The sum is finite, and it is a Lie algebra automorphism by `LieDerivation.exp` of Mathlib. -/
def expAd (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) : L ≃ₗ⁅k⁆ L :=
  LieDerivation.exp (t • LieDerivation.ad k L x) (by simpa using isNilpotent_smul_ad hx t)

/-- The value of $\exp(t \cdot \mathrm{ad}\, x)$ at $y$ is the exponential series of the endomorphism $t \cdot \mathrm{ad}\, x$ applied to $y$. -/
theorem expAd_apply (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) (y : L) :
    expAd x hx t y = IsNilpotent.exp (t • LieAlgebra.ad k L x) y := by
  simp [expAd, LieDerivation.exp_map_apply]

/-- The equation $\exp(0 \cdot \mathrm{ad}\, x) = 1$. -/
theorem expAd_zero (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) : expAd x hx 0 = 1 := by
  refine LieEquiv.ext fun y => ?_
  rw [expAd_apply, zero_smul, IsNilpotent.exp_zero]
  rfl

/-- The one parameter group law $\exp((s + t) \mathrm{ad}\, x) = \exp(s\, \mathrm{ad}\, x) \exp(t\, \mathrm{ad}\, x)$. -/
theorem expAd_add (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (s t : k) :
    expAd x hx (s + t) = expAd x hx s * expAd x hx t := by
  ext y
  have hs := isNilpotent_smul_ad hx s
  have ht := isNilpotent_smul_ad hx t
  rw [lieAut_mul_apply, expAd_apply, expAd_apply, expAd_apply, add_smul,
    IsNilpotent.exp_add_of_commute ((Commute.refl _).smul_left s |>.smul_right t) hs ht]
  rfl

/-- The equation $\exp(-t\, \mathrm{ad}\, x) = \exp(t\, \mathrm{ad}\, x)^{-1}$. -/
theorem expAd_neg (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) :
    expAd x hx (-t) = (expAd x hx t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← expAd_add, neg_add_cancel, expAd_zero]

/-- If $[x, y] = 0$, then $\exp(t\, \mathrm{ad}\, x)$ fixes $y$. -/
theorem expAd_apply_of_lie_eq_zero (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k)
    {y : L} (hy : ⁅x, y⁆ = 0) : expAd x hx t y = y := by
  rw [expAd_apply, ← Module.End.smul_def,
    IsNilpotent.exp_smul_eq_sum (k := 1) (by simp [Module.End.smul_def, hy])
      (isNilpotent_smul_ad hx t)]
  simp

/-- The automorphism $\exp(t\, \mathrm{ad}\, x)$ fixes $x$. -/
theorem expAd_apply_self (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) :
    expAd x hx t x = x :=
  expAd_apply_of_lie_eq_zero x hx t (lie_self x)

/-- For an $\mathfrak{sl}_2$ triple $(h, e, f)$ with $\mathrm{ad}\, e$ nilpotent, $\exp(t\, \mathrm{ad}\, e)(h) = h - 2 t e$. -/
theorem expAd_apply_sl2_h {h e f : L} (ht : IsSl2Triple h e f)
    (he : IsNilpotent (LieAlgebra.ad k L e)) (t : k) :
    expAd e he t h = h - (2 * t) • e := by
  have heh : ⁅e, h⁆ = -(2 : k) • e := by
    rw [← lie_skew, ht.lie_h_e_smul k]; simp
  rw [expAd_apply, ← Module.End.smul_def,
    IsNilpotent.exp_smul_eq_sum (k := 2) (by simp [Module.End.smul_def, sq, heh])
      (isNilpotent_smul_ad he t)]
  simp [Finset.sum_range_succ, Module.End.smul_def, heh, sub_eq_add_neg, mul_smul,
    smul_comm t (2 : k)]

/-- For an $\mathfrak{sl}_2$ triple $(h, e, f)$ with $\mathrm{ad}\, e$ nilpotent, $\exp(t\, \mathrm{ad}\, e)(f) = f + t h - t^2 e$. -/
theorem expAd_apply_sl2_f {h e f : L} (ht : IsSl2Triple h e f)
    (he : IsNilpotent (LieAlgebra.ad k L e)) (t : k) :
    expAd e he t f = f + t • h - t ^ 2 • e := by
  have heh : ⁅e, h⁆ = -(2 : k) • e := by
    rw [← lie_skew, ht.lie_h_e_smul k]; simp
  rw [expAd_apply, ← Module.End.smul_def,
    IsNilpotent.exp_smul_eq_sum (k := 3)
      (by simp [Module.End.smul_def, pow_succ, ht.lie_e_f, heh]) (isNilpotent_smul_ad he t)]
  have h2 : ((t • LieAlgebra.ad k L e) ^ 2) f = (2 : ℕ) • (-(t ^ 2 • e)) := by
    simp [sq, ht.lie_e_f, heh, smul_smul, two_smul]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Module.End.smul_def,
    h2, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num [ht.lie_e_f, sub_eq_add_neg]

/-- The homomorphism $t \mapsto \exp(t\, \mathrm{ad}\, x)$ from the additive group of $k$ to the automorphism group of $L$. -/
def expAdHom (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) :
    Multiplicative k →* (L ≃ₗ⁅k⁆ L) where
  toFun t := expAd x hx t.toAdd
  map_one' := expAd_zero x hx
  map_mul' s t := expAd_add x hx s.toAdd t.toAdd

omit [Module ℚ L] in
/-- For an automorphism $\varphi$, the equation $\mathrm{ad}(\varphi x) \circ \varphi = \varphi \circ \mathrm{ad}\, x$. -/
theorem ad_comp_lieEquiv (φ : L ≃ₗ⁅k⁆ L) (x : L) :
    LieAlgebra.ad k L (φ x) ∘ₗ (φ : L →ₗ[k] L) =
      (φ : L →ₗ[k] L) ∘ₗ LieAlgebra.ad k L x := by
  ext y; simpa using (φ.map_lie x y).symm

omit [Module ℚ L] in
/-- If $\mathrm{ad}\, x$ is nilpotent, then $\mathrm{ad}(\varphi x)$ is nilpotent for each automorphism $\varphi$. -/
theorem isNilpotent_ad_lieEquiv_apply (φ : L ≃ₗ⁅k⁆ L) {x : L}
    (hx : IsNilpotent (LieAlgebra.ad k L x)) : IsNilpotent (LieAlgebra.ad k L (φ x)) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, LinearMap.ext fun y => ?_⟩
  have h := congr($(Module.End.commute_pow_left_of_commute (ad_comp_lieEquiv φ x) n) (φ.symm y))
  simpa [hn] using h

/-- The conjugation formula $\varphi \exp(t\, \mathrm{ad}\, x) \varphi^{-1} = \exp(t\, \mathrm{ad}(\varphi x))$. -/
theorem lieEquiv_mul_expAd_mul_inv (φ : L ≃ₗ⁅k⁆ L) (x : L)
    (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k) :
    φ * expAd x hx t * φ⁻¹ = expAd (φ x) (isNilpotent_ad_lieEquiv_apply φ hx) t := by
  have hc : (t • LieAlgebra.ad k L (φ x)) ∘ₗ (φ : L →ₗ[k] L) =
      (φ : L →ₗ[k] L) ∘ₗ (t • LieAlgebra.ad k L x) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ad_comp_lieEquiv]
  have h := Module.End.commute_exp_left_of_commute (isNilpotent_smul_ad hx t)
    (isNilpotent_smul_ad (isNilpotent_ad_lieEquiv_apply φ hx) t) hc
  refine LieEquiv.ext fun y => ?_
  have hy := congr($h (φ.symm y))
  simp only [LinearMap.comp_apply] at hy
  simp only [lieAut_mul_apply, lieAut_inv_apply, expAd_apply]
  simpa using hy.symm

/-- The automorphism $\exp(t\, \mathrm{ad}\, x)$ depends only on $x$ and $t$, and not on the proof of nilpotency. -/
theorem expAd_congr {x y : L} (h : x = y) (hx : IsNilpotent (LieAlgebra.ad k L x))
    (hy : IsNilpotent (LieAlgebra.ad k L y)) (t : k) : expAd x hx t = expAd y hy t := by
  subst h; rfl

/-- The equation $\exp(t\, \mathrm{ad}(c x)) = \exp(t c\, \mathrm{ad}\, x)$. -/
theorem expAd_smul (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (c : k)
    (hcx : IsNilpotent (LieAlgebra.ad k L (c • x))) (t : k) :
    expAd (c • x) hcx t = expAd x hx (t * c) := by
  refine LieEquiv.ext fun y => ?_
  rw [expAd_apply, expAd_apply, map_smul, smul_smul]

variable (k L) in
/-- The subgroup of the automorphisms of $L$ that the automorphisms $\exp(t\, \mathrm{ad}\, x)$ generate, for all $x$ with $\mathrm{ad}\, x$ nilpotent and all $t$ in $k$. -/
def adNilpotentExpSubgroup : Subgroup (L ≃ₗ⁅k⁆ L) :=
  Subgroup.closure
    {g | ∃ (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x)) (t : k), expAd x hx t = g}

/-- Each automorphism $\exp(t\, \mathrm{ad}\, x)$ is in `adNilpotentExpSubgroup`. -/
theorem expAd_mem_adNilpotentExpSubgroup (x : L) (hx : IsNilpotent (LieAlgebra.ad k L x))
    (t : k) : expAd x hx t ∈ adNilpotentExpSubgroup k L :=
  Subgroup.subset_closure ⟨x, hx, t, rfl⟩

/-- The subgroup `adNilpotentExpSubgroup` is normal in the group of all automorphisms of $L$. -/
instance adNilpotentExpSubgroup_normal : (adNilpotentExpSubgroup k L).Normal := by
  refine ⟨fun n hn φ => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨x, hx, t, rfl⟩ := hg
    rw [lieEquiv_mul_expAd_mul_inv]
    exact expAd_mem_adNilpotentExpSubgroup _ _ t
  | one => simp 
  | mul a b _ _ ha hb =>
    have : φ * (a * b) * φ⁻¹ = (φ * a * φ⁻¹) * (φ * b * φ⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : φ * a⁻¹ * φ⁻¹ = (φ * a * φ⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

end Exp

section RootLattice

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k ι M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} (b : P.Base)

variable (P) in
/-- The root lattice $\mathbb{Z}\Phi$: the additive subgroup of $M$ that the roots generate. -/
def rootLattice : AddSubgroup M := AddSubgroup.closure (Set.range P.root)

variable (P) in
/-- A root, as an element of the root lattice. -/
def latticeRoot (j : ι) : rootLattice P := ⟨P.root j, AddSubgroup.subset_closure ⟨j, rfl⟩⟩

/-- The diagonal entries of the action of a character $\chi$ of the root lattice on the space of the Geck construction: $1$ on the basis vectors $u_i$ and $\chi(\alpha_j)$ on the basis vectors $v_j$. -/
def torusDiag (χ : rootLattice P →+ Additive kˣ) : b.support ⊕ ι → k
  | .inl _ => 1
  | .inr j => ((χ (latticeRoot P j)).toMul : k)

/-- The entry of `torusDiag` at $u_i$ is $1$. -/
@[simp] theorem torusDiag_inl (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    torusDiag b χ (.inl i) = 1 := rfl

/-- The entry of `torusDiag` at $v_j$ is $\chi(\alpha_j)$. -/
@[simp] theorem torusDiag_inr (χ : rootLattice P →+ Additive kˣ) (j : ι) :
    torusDiag b χ (.inr j) = ((χ (latticeRoot P j)).toMul : k) := rfl

/-- The root $-\alpha_i = s_i(\alpha_i)$ is the negative of $\alpha_i$ in the root lattice. -/
theorem latticeRoot_reflectionPerm_self (i : ι) :
    latticeRoot P (P.reflectionPerm i i) = -latticeRoot P i := by
  apply Subtype.ext; simp [latticeRoot]

/-- If $\alpha_a = \alpha_i + \alpha_c$ in $M$, then the same equation holds in the root lattice. -/
theorem latticeRoot_eq_add {a i c : ι} (h : P.root a = P.root i + P.root c) :
    latticeRoot P a = latticeRoot P i + latticeRoot P c := Subtype.ext h

/-- If $\alpha_a = \alpha_c - \alpha_i$ in $M$, then the same equation holds in the root lattice. -/
theorem latticeRoot_eq_sub {a i c : ι} (h : P.root a = P.root c - P.root i) :
    latticeRoot P a = latticeRoot P c - latticeRoot P i := Subtype.ext h

/-- The diagonals of $\chi$ and $\chi^{-1}$ are inverse to each other. -/
theorem torusDiag_mul_neg (χ : rootLattice P →+ Additive kˣ) :
    torusDiag b χ * torusDiag b (-χ) = 1 := by
  ext (a | a)
  · simp
  · simp only [Pi.mul_apply, torusDiag_inr, AddMonoidHom.neg_apply, toMul_neg,
      Units.val_inv_eq_inv_val, Pi.one_apply]
    field_simp

/-- The diagonal of a product of characters is the product of the diagonals. -/
theorem torusDiag_add (χ ψ : rootLattice P →+ Additive kˣ) :
    torusDiag b (χ + ψ) = torusDiag b χ * torusDiag b ψ := by
  ext (a | a) <;> simp

variable [Fintype ι] [DecidableEq ι]

/-- The diagonal matrix of $\chi$ is invertible, with the diagonal matrix of $\chi^{-1}$ as inverse. -/
instance invertibleTorusDiag (χ : rootLattice P →+ Additive kˣ) :
    Invertible (Matrix.diagonal (torusDiag b χ)) where
  invOf := Matrix.diagonal (torusDiag b (-χ))
  invOf_mul_self := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; rw [mul_comm]; exact congrFun (torusDiag_mul_neg b χ) a
  mul_invOf_self := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; exact congrFun (torusDiag_mul_neg b χ) a

/-- Conjugation $A \mapsto D_\chi A D_\chi^{-1}$ by the diagonal matrix $D_\chi$ of a character $\chi$, as a Lie algebra automorphism of the matrix algebra. -/
def torusConj (χ : rootLattice P →+ Additive kˣ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) k ≃ₗ⁅k⁆
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) k :=
  Matrix.lieConj _ (invertibleTorusDiag b χ)

/-- The formula $A \mapsto D_\chi A D_{\chi^{-1}}$ for `torusConj`. -/
theorem torusConj_apply (χ : rootLattice P →+ Additive kˣ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) :
    torusConj b χ A =
      Matrix.diagonal (torusDiag b χ) * A * Matrix.diagonal (torusDiag b (-χ)) := by
  rw [torusConj, Matrix.lieConj_apply, ← Matrix.invOf_eq_nonsing_inv]
  rfl

/-- Conjugation by $D_\chi$ is inverse to conjugation by $D_{\chi^{-1}}$. -/
theorem torusConj_torusConj_neg (χ : rootLattice P →+ Additive kˣ) (A) :
    torusConj b χ (torusConj b (-χ) A) = A := by
  have h1 : Matrix.diagonal (torusDiag b χ) * Matrix.diagonal (torusDiag b (-χ)) = 1 :=
    (invertibleTorusDiag b χ).mul_invOf_self
  have h2 : torusDiag b (- -χ) = torusDiag b χ := by ext (a | a) <;> simp
  simp only [torusConj_apply, h2, Matrix.mul_assoc]
  rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end RootLattice

section Geck

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k ι M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] (b : P.Base)

/-- The Geck generator $e_i$ for a simple root $\alpha_i$, as an element of the Geck Lie algebra. -/
def geckE (i : b.support) : lieAlgebra b := ⟨e i, e_mem_lieAlgebra i⟩

/-- The Geck generator $f_i$ for a simple root $\alpha_i$, as an element of the Geck Lie algebra. -/
def geckF (i : b.support) : lieAlgebra b := ⟨f i, f_mem_lieAlgebra i⟩

/-- The Geck generator $h_i$ for a simple root $\alpha_i$, as an element of the Geck Lie algebra. -/
def geckH (i : b.support) : lieAlgebra b := ⟨h i, h_mem_lieAlgebra i⟩

/-- The equation $D_\chi e_i D_\chi^{-1} = \chi(\alpha_i) e_i$ for the matrices of the Geck construction. -/
theorem diagonal_mul_e_mul_diagonal (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    Matrix.diagonal (torusDiag b χ) * e i * Matrix.diagonal (torusDiag b (-χ)) =
      ((χ (latticeRoot P i)).toMul : k) • e i := by
  classical
  let := P.indexNeg
  ext (a | a) (c | c)
  · simp [e]
  · simp only [e, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inl, torusDiag_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with hac
    · obtain ⟨rfl, rfl⟩ := hac
      simp [latticeRoot_reflectionPerm_self]
    · simp
  · simp only [e, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inl, torusDiag_inr,
      Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with hac
    · subst hac; simp
    · simp
  · simp only [e, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inr,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with hac
    · rw [latticeRoot_eq_add hac]
      simp only [map_add, toMul_add, Units.val_mul, AddMonoidHom.neg_apply, toMul_neg,
        Units.val_inv_eq_inv_val]
      field_simp
    · simp

/-- The equation $D_\chi f_i D_\chi^{-1} = \chi(\alpha_i)^{-1} f_i$ for the matrices of the Geck construction. -/
theorem diagonal_mul_f_mul_diagonal (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    Matrix.diagonal (torusDiag b χ) * f i * Matrix.diagonal (torusDiag b (-χ)) =
      ((χ (latticeRoot P i)).toMul⁻¹ : kˣ) • f i := by
  classical
  ext (a | a) (c | c)
  · simp [f]
  · simp only [f, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inl, torusDiag_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Matrix.smul_apply, Units.smul_def, smul_eq_mul]
    split_ifs with hac
    · obtain ⟨rfl, rfl⟩ := hac
      simp
    · simp
  · simp only [f, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inl, torusDiag_inr,
      Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.smul_apply, Units.smul_def, smul_eq_mul]
    split_ifs with hac
    · subst hac; simp [latticeRoot_reflectionPerm_self]
    · simp
  · simp only [f, Matrix.diagonal_mul, Matrix.mul_diagonal, torusDiag_inr,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.smul_apply, Units.smul_def, smul_eq_mul]
    split_ifs with hac
    · rw [latticeRoot_eq_sub hac]
      simp only [map_sub, toMul_sub, Units.val_div_eq_div_val, AddMonoidHom.neg_apply, toMul_neg,
        Units.val_inv_eq_inv_val]
      field_simp
    · simp

omit [CharZero k] in
/-- The equation $D_\chi h_i D_\chi^{-1} = h_i$ for the matrices of the Geck construction. -/
theorem diagonal_mul_h_mul_diagonal (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    Matrix.diagonal (torusDiag b χ) * h i * Matrix.diagonal (torusDiag b (-χ)) = h i := by
  classical
  rw [h_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext (a | a)
  · simp
  · simp only [torusDiag_inr, Sum.elim_inr, AddMonoidHom.neg_apply, toMul_neg,
      Units.val_inv_eq_inv_val]
    field_simp

/-- Conjugation by $D_\chi$ maps the Geck Lie algebra into itself. -/
theorem lieAlgebra_le_comap_torusConj (χ : rootLattice P →+ Additive kˣ) :
    lieAlgebra b ≤ (lieAlgebra b).comap (torusConj b χ : _ →ₗ⁅k⁆ _) := by
  refine LieSubalgebra.lieSpan_le.2 ?_
  rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) <;>
    simp only [SetLike.mem_coe, LieSubalgebra.mem_comap,
      LieEquiv.coe_toLieHom, torusConj_apply]
  · rw [diagonal_mul_h_mul_diagonal]; exact h_mem_lieAlgebra i
  · rw [diagonal_mul_e_mul_diagonal]; exact (lieAlgebra b).smul_mem _ (e_mem_lieAlgebra i)
  · rw [diagonal_mul_f_mul_diagonal, Units.smul_def]
    exact (lieAlgebra b).smul_mem _ (f_mem_lieAlgebra i)

/-- Conjugation by $D_\chi$ maps the Geck Lie algebra onto itself. -/
theorem map_torusConj_lieAlgebra (χ : rootLattice P →+ Additive kˣ) :
    (lieAlgebra b).map (torusConj b χ : _ →ₗ⁅k⁆ _) = lieAlgebra b := by
  refine le_antisymm (LieSubalgebra.map_le_iff_le_comap.2 (lieAlgebra_le_comap_torusConj b χ))
    fun A hA => ?_
  exact ⟨torusConj b (-χ) A, lieAlgebra_le_comap_torusConj b (-χ) hA,
    torusConj_torusConj_neg b χ A⟩

/-- The automorphism $h(\chi)$ of the Geck Lie algebra for a character $\chi : \mathbb{Z}\Phi \to k^\times$ of the root lattice. It is the action of the point $\chi$ of the adjoint maximal torus $T_{\mathrm{ad}}(k) = \mathrm{Hom}(\mathbb{Z}\Phi, k^\times)$. It acts on the root space of $\alpha$ by $\chi(\alpha)$ and trivially on the Cartan subalgebra. -/
def torusElement (χ : rootLattice P →+ Additive kˣ) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  (torusConj b χ).ofSubalgebras _ _ (map_torusConj_lieAlgebra b χ)

/-- The matrix of $h(\chi)(x)$ is $D_\chi x D_\chi^{-1}$. -/
theorem coe_torusElement_apply (χ : rootLattice P →+ Additive kˣ) (x : lieAlgebra b) :
    (torusElement b χ x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) =
      Matrix.diagonal (torusDiag b χ) * x * Matrix.diagonal (torusDiag b (-χ)) := by
  rw [torusElement, LieEquiv.ofSubalgebras_apply, torusConj_apply]

/-- The formula $h(\chi)(e_i) = \chi(\alpha_i) e_i$. -/
theorem torusElement_apply_geckE (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    torusElement b χ (geckE b i) = ((χ (latticeRoot P i)).toMul : k) • geckE b i :=
  Subtype.ext <| by rw [coe_torusElement_apply]; exact diagonal_mul_e_mul_diagonal b χ i

/-- The formula $h(\chi)(f_i) = \chi(\alpha_i)^{-1} f_i$. -/
theorem torusElement_apply_geckF (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    torusElement b χ (geckF b i) = ((χ (latticeRoot P i)).toMul⁻¹ : kˣ) • geckF b i :=
  Subtype.ext <| by rw [coe_torusElement_apply]; exact diagonal_mul_f_mul_diagonal b χ i

/-- The element $h(\chi)$ fixes $h_i$. -/
theorem torusElement_apply_geckH (χ : rootLattice P →+ Additive kˣ) (i : b.support) :
    torusElement b χ (geckH b i) = geckH b i :=
  Subtype.ext <| by rw [coe_torusElement_apply]; exact diagonal_mul_h_mul_diagonal b χ i

/-- The equation $h(\chi \psi) = h(\chi) h(\psi)$. -/
theorem torusElement_add (χ ψ : rootLattice P →+ Additive kˣ) :
    torusElement b (χ + ψ) = torusElement b χ * torusElement b ψ := by
  refine LieEquiv.ext fun x => Subtype.ext ?_
  have hn : torusDiag b (-(χ + ψ)) = torusDiag b (-ψ) * torusDiag b (-χ) := by
    ext (a | a) <;> simp [mul_comm]
  rw [lieAut_mul_apply, coe_torusElement_apply, coe_torusElement_apply, coe_torusElement_apply,
    hn, torusDiag_add]
  have hd (d₁ d₂ : b.support ⊕ ι → k) :
      Matrix.diagonal (d₁ * d₂) = Matrix.diagonal d₁ * Matrix.diagonal d₂ :=
    (Matrix.diagonal_mul_diagonal d₁ d₂).symm
  rw [hd, hd]
  simp only [Matrix.mul_assoc]

/-- The equation $h(1) = 1$. -/
theorem torusElement_zero : torusElement b (0 : rootLattice P →+ Additive kˣ) = 1 := by
  refine LieEquiv.ext fun x => Subtype.ext ?_
  have h0 : torusDiag b (0 : rootLattice P →+ Additive kˣ) = 1 := by ext (a | a) <;> simp
  have h0' : torusDiag b (-0 : rootLattice P →+ Additive kˣ) = 1 := by ext (a | a) <;> simp
  rw [coe_torusElement_apply, h0', h0, Matrix.diagonal_one', Matrix.one_mul, Matrix.mul_one]
  rfl

/-- The homomorphism $\chi \mapsto h(\chi)$ from $T_{\mathrm{ad}}(k) = \mathrm{Hom}(\mathbb{Z}\Phi, k^\times)$ to the automorphism group of the Geck Lie algebra. -/
def torusHom :
    Multiplicative (rootLattice P →+ Additive kˣ) →* (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) where
  toFun χ := torusElement b χ.toAdd
  map_one' := torusElement_zero b
  map_mul' χ ψ := torusElement_add b χ.toAdd ψ.toAdd

variable [P.IsReduced]

/-- The endomorphism $\mathrm{ad}\, e_i$ of the Geck Lie algebra is nilpotent. -/
theorem isNilpotent_ad_geckE (i : b.support) :
    IsNilpotent (LieAlgebra.ad k (lieAlgebra b) (geckE b i)) :=
  LieAlgebra.isNilpotent_ad_of_isNilpotent (isNilpotent_e i)

/-- The endomorphism $\mathrm{ad}\, f_i$ of the Geck Lie algebra is nilpotent. -/
theorem isNilpotent_ad_geckF (i : b.support) :
    IsNilpotent (LieAlgebra.ad k (lieAlgebra b) (geckF b i)) :=
  LieAlgebra.isNilpotent_ad_of_isNilpotent (isNilpotent_f i)

/-- The elements $(h_i, e_i, f_i)$ of the Geck Lie algebra are an $\mathfrak{sl}_2$ triple. -/
theorem isSl2Triple_geck (i : b.support) : IsSl2Triple (geckH b i) (geckE b i) (geckF b i) := by
  have ht := isSl2Triple (b := b) i
  refine ⟨fun h0 => ht.h_ne_zero congr(Subtype.val $h0), Subtype.ext ht.lie_e_f,
    Subtype.ext ht.lie_h_e_nsmul, Subtype.ext ht.lie_h_f_nsmul⟩

/-- The element $x_{\alpha_i}(t) = \exp(t\, \mathrm{ad}\, e_i)$ of the root subgroup of the simple root $\alpha_i$. -/
def simpleRootElement (i : b.support) (t : k) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  expAd (geckE b i) (isNilpotent_ad_geckE b i) t

/-- The element $x_{-\alpha_i}(t) = \exp(t\, \mathrm{ad}\, f_i)$ of the root subgroup of the negative simple root $-\alpha_i$. -/
def negSimpleRootElement (i : b.support) (t : k) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  expAd (geckF b i) (isNilpotent_ad_geckF b i) t

/-- The elementary adjoint Chevalley group of the root system over the field $k$ of characteristic zero. It is the subgroup of the Lie algebra automorphisms of the Geck Lie algebra $L$ that the elements $x_{\alpha_i}(t)$ and $x_{-\alpha_i}(t)$ generate, for the simple roots $\alpha_i$ of the base and all $t$ in $k$. This is the group of $k$-points of the elementary subgroup of the adjoint group, as a group of automorphisms of $L$. It is not the group scheme and not the full group $G_{\mathrm{ad}}(k)$. The classical definition uses the root elements $x_\alpha(t)$ for all roots $\alpha$. These are conjugate to the simple root elements under the Weyl elements, so the two groups agree (Steinberg, Lectures on Chevalley groups, section 3), but this file does not prove that. -/
def ElementaryAdjointChevalleyGroup : Subgroup (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) :=
  Subgroup.closure (Set.range (fun p : b.support × k => simpleRootElement b p.1 p.2) ∪
    Set.range (fun p : b.support × k => negSimpleRootElement b p.1 p.2))

/-- The element $x_{\alpha_i}(t)$ is in the elementary adjoint Chevalley group. -/
theorem simpleRootElement_mem (i : b.support) (t : k) :
    simpleRootElement b i t ∈ ElementaryAdjointChevalleyGroup b :=
  Subgroup.subset_closure (Or.inl ⟨(i, t), rfl⟩)

/-- The element $x_{-\alpha_i}(t)$ is in the elementary adjoint Chevalley group. -/
theorem negSimpleRootElement_mem (i : b.support) (t : k) :
    negSimpleRootElement b i t ∈ ElementaryAdjointChevalleyGroup b :=
  Subgroup.subset_closure (Or.inr ⟨(i, t), rfl⟩)

/-- The equation $x_{\alpha_i}(s + t) = x_{\alpha_i}(s) x_{\alpha_i}(t)$. -/
theorem simpleRootElement_add (i : b.support) (s t : k) :
    simpleRootElement b i (s + t) = simpleRootElement b i s * simpleRootElement b i t :=
  expAd_add _ _ s t

/-- The equation $x_{-\alpha_i}(s + t) = x_{-\alpha_i}(s) x_{-\alpha_i}(t)$. -/
theorem negSimpleRootElement_add (i : b.support) (s t : k) :
    negSimpleRootElement b i (s + t) = negSimpleRootElement b i s * negSimpleRootElement b i t :=
  expAd_add _ _ s t

/-- The equation $x_{\alpha_i}(0) = 1$. -/
theorem simpleRootElement_zero (i : b.support) : simpleRootElement b i 0 = 1 :=
  expAd_zero _ _

/-- The equation $x_{-\alpha_i}(0) = 1$. -/
theorem negSimpleRootElement_zero (i : b.support) : negSimpleRootElement b i 0 = 1 :=
  expAd_zero _ _

/-- The equation $x_{\alpha_i}(-t) = x_{\alpha_i}(t)^{-1}$. -/
theorem simpleRootElement_neg (i : b.support) (t : k) :
    simpleRootElement b i (-t) = (simpleRootElement b i t)⁻¹ :=
  expAd_neg _ _ t

/-- The equation $x_{-\alpha_i}(-t) = x_{-\alpha_i}(t)^{-1}$. -/
theorem negSimpleRootElement_neg (i : b.support) (t : k) :
    negSimpleRootElement b i (-t) = (negSimpleRootElement b i t)⁻¹ :=
  expAd_neg _ _ t

/-- The elementary adjoint Chevalley group is contained in the group that all the exponentials of nilpotent inner derivations generate. -/
theorem elementaryAdjointChevalleyGroup_le :
    ElementaryAdjointChevalleyGroup b ≤ adNilpotentExpSubgroup k (lieAlgebra b) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ (⟨⟨i, t⟩, rfl⟩ | ⟨⟨i, t⟩, rfl⟩)
  · exact expAd_mem_adNilpotentExpSubgroup _ _ t
  · exact expAd_mem_adNilpotentExpSubgroup _ _ t

/-- The element $x_{\alpha_i}(t)$ fixes $e_i$. -/
theorem simpleRootElement_apply_e (i : b.support) (t : k) :
    simpleRootElement b i t (geckE b i) = geckE b i :=
  expAd_apply_self _ _ t

/-- The formula $x_{\alpha_i}(t)(h_i) = h_i - 2 t e_i$. -/
theorem simpleRootElement_apply_h (i : b.support) (t : k) :
    simpleRootElement b i t (geckH b i) = geckH b i - (2 * t) • geckE b i :=
  expAd_apply_sl2_h (isSl2Triple_geck b i) _ t

/-- The formula $x_{\alpha_i}(t)(f_i) = f_i + t h_i - t^2 e_i$. -/
theorem simpleRootElement_apply_f (i : b.support) (t : k) :
    simpleRootElement b i t (geckF b i) = geckF b i + t • geckH b i - t ^ 2 • geckE b i :=
  expAd_apply_sl2_f (isSl2Triple_geck b i) _ t

/-- The element $x_{-\alpha_i}(t)$ fixes $f_i$. -/
theorem negSimpleRootElement_apply_f (i : b.support) (t : k) :
    negSimpleRootElement b i t (geckF b i) = geckF b i :=
  expAd_apply_self _ _ t

/-- The formula $x_{-\alpha_i}(t)(h_i) = h_i + 2 t f_i$. -/
theorem negSimpleRootElement_apply_h (i : b.support) (t : k) :
    negSimpleRootElement b i t (geckH b i) = geckH b i + (2 * t) • geckF b i := by
  have h := expAd_apply_sl2_h (isSl2Triple_geck b i).symm (isNilpotent_ad_geckF b i) t
  rw [map_neg, neg_eq_iff_eq_neg] at h
  simpa [negSimpleRootElement, sub_eq_add_neg, add_comm] using h

/-- The formula $x_{-\alpha_i}(t)(e_i) = e_i - t h_i - t^2 f_i$. -/
theorem negSimpleRootElement_apply_e (i : b.support) (t : k) :
    negSimpleRootElement b i t (geckE b i) = geckE b i - t • geckH b i - t ^ 2 • geckF b i := by
  have h := expAd_apply_sl2_f (isSl2Triple_geck b i).symm (isNilpotent_ad_geckF b i) t
  simpa [negSimpleRootElement, sub_eq_add_neg] using h

/-- The torus acts on the simple root subgroups through the roots: $h(\chi) x_{\alpha_i}(t) h(\chi)^{-1} = x_{\alpha_i}(\chi(\alpha_i) t)$. -/
theorem torusElement_mul_simpleRootElement_mul_inv (χ : rootLattice P →+ Additive kˣ)
    (i : b.support) (t : k) :
    torusElement b χ * simpleRootElement b i t * (torusElement b χ)⁻¹ =
      simpleRootElement b i (t * ((χ (latticeRoot P i)).toMul : k)) := by
  have hn := isNilpotent_ad_lieEquiv_apply (torusElement b χ) (isNilpotent_ad_geckE b i)
  rw [torusElement_apply_geckE] at hn
  rw [simpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (torusElement_apply_geckE b χ i) _ hn, expAd_smul _ (isNilpotent_ad_geckE b i)]
  rfl

/-- The torus acts on the negative simple root subgroups through the roots: $h(\chi) x_{-\alpha_i}(t) h(\chi)^{-1} = x_{-\alpha_i}(\chi(\alpha_i)^{-1} t)$. -/
theorem torusElement_mul_negSimpleRootElement_mul_inv (χ : rootLattice P →+ Additive kˣ)
    (i : b.support) (t : k) :
    torusElement b χ * negSimpleRootElement b i t * (torusElement b χ)⁻¹ =
      negSimpleRootElement b i (t * ((χ (latticeRoot P i)).toMul⁻¹ : kˣ)) := by
  have hn := isNilpotent_ad_lieEquiv_apply (torusElement b χ) (isNilpotent_ad_geckF b i)
  rw [torusElement_apply_geckF, Units.smul_def] at hn
  rw [negSimpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr ((torusElement_apply_geckF b χ i).trans (Units.smul_def _ _)) _ hn,
    expAd_smul _ (isNilpotent_ad_geckF b i)]
  rfl

/-- The torus $T_{\mathrm{ad}}(k)$ normalizes the elementary adjoint Chevalley group. -/
theorem torusElement_conj_mem (χ : rootLattice P →+ Additive kˣ)
    {g : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b} (hg : g ∈ ElementaryAdjointChevalleyGroup b) :
    torusElement b χ * g * (torusElement b χ)⁻¹ ∈ ElementaryAdjointChevalleyGroup b := by
  set φ := torusElement b χ
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨⟨i, t⟩, rfl⟩
    · rw [torusElement_mul_simpleRootElement_mul_inv]; exact simpleRootElement_mem b i _
    · rw [torusElement_mul_negSimpleRootElement_mul_inv]; exact negSimpleRootElement_mem b i _
  | one => simp
  | mul a c _ _ ha hc =>
    have : φ * (a * c) * φ⁻¹ = (φ * a * φ⁻¹) * (φ * c * φ⁻¹) := by group
    rw [this]; exact mul_mem ha hc
  | inv a _ ha =>
    have : φ * a⁻¹ * φ⁻¹ = (φ * a * φ⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

/-- The element $w_{\alpha_i}(t) = x_{\alpha_i}(t) x_{-\alpha_i}(-t^{-1}) x_{\alpha_i}(t)$. -/
def weylElement (i : b.support) (t : k) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  simpleRootElement b i t * negSimpleRootElement b i (-t⁻¹) * simpleRootElement b i t

/-- The element $w_{\alpha_i}(t)$ is in the elementary adjoint Chevalley group. -/
theorem weylElement_mem (i : b.support) (t : k) :
    weylElement b i t ∈ ElementaryAdjointChevalleyGroup b :=
  mul_mem (mul_mem (simpleRootElement_mem b i t) (negSimpleRootElement_mem b i _))
    (simpleRootElement_mem b i t)

/-- The formula $w_{\alpha_i}(1)(e_i) = -f_i$. -/
theorem weylElement_one_apply_geckE (i : b.support) :
    weylElement b i 1 (geckE b i) = -geckF b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e, inv_one,
    negSimpleRootElement_apply_e, map_sub, simpleRootElement_apply_h, simpleRootElement_apply_f,
    map_smul]
  module

/-- The formula $w_{\alpha_i}(1)(f_i) = -e_i$. -/
theorem weylElement_one_apply_geckF (i : b.support) :
    weylElement b i 1 (geckF b i) = -geckE b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e, inv_one,
    negSimpleRootElement_apply_e, negSimpleRootElement_apply_f, negSimpleRootElement_apply_h,
    map_sub, map_add, simpleRootElement_apply_h, simpleRootElement_apply_f, map_smul]
  module

/-- The formula $w_{\alpha_i}(1)(h_i) = -h_i$. -/
theorem weylElement_one_apply_geckH (i : b.support) :
    weylElement b i 1 (geckH b i) = -geckH b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e, inv_one,
    negSimpleRootElement_apply_e, negSimpleRootElement_apply_h,
    map_sub, map_add, simpleRootElement_apply_h, simpleRootElement_apply_f, map_smul]
  module

end Geck

end Langlands.Groups.Chevalley
