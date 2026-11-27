/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Langlands.Groups.Chevalley
import Langlands.Groups.RootDatum

/-!
# Root elements, coroot elements and the adjoint root datum

Let $k$ be a field of characteristic zero, let $\Phi$ be a reduced crystallographic root system over $k$ with a base $\Delta$, and let $L$ be the Lie algebra of the Geck construction of Mathlib. This file continues `Langlands/Groups/Chevalley.lean`. It defines a root vector $X_\beta \in L$ and a root element $x_\beta(t) = \exp(t\, \mathrm{ad}\, X_\beta)$ for every root $\beta$, and it proves that these elements generate the elementary adjoint Chevalley group. It defines the elements $h_{\alpha_i}(t) = w_{\alpha_i}(t) w_{\alpha_i}(1)^{-1}$ and computes their action. It proves the commutation of the root elements of orthogonal simple roots and the rank one relations. Finally, it constructs the root datum of the split adjoint group from $\Phi$ and $\Delta$, and identifies its L-group datum with the dual datum, which is simply connected.

This file imports `Langlands/Groups/Chevalley.lean` and uses its definitions `lieAutGroup`, `expAd`, `geckE`, `geckF`, `geckH`, `simpleRootElement`, `negSimpleRootElement`, `ElementaryAdjointChevalleyGroup`, `weylElement` and `torusElement`.

## Main definitions

* `Langlands.Groups.ChevalleyRoots.wordPerm`, `Langlands.Groups.ChevalleyRoots.rootWord`: words in the simple reflections, and for each root $\beta$ a word $s_{i_1} \cdots s_{i_r}$ and a simple root $\alpha_j$ with $\beta = s_{i_1} \cdots s_{i_r} \alpha_j$.
* `Langlands.Groups.ChevalleyRoots.weightSpace`: the subspace of $L$ on which each $\mathrm{ad}\, h_j$ acts by $\langle \mu, \alpha_j^\vee \rangle$.
* `Langlands.Groups.ChevalleyRoots.weylWord`: the product $w_{\alpha_{i_1}}(1) \cdots w_{\alpha_{i_r}}(1)$ for a word.
* `Langlands.Groups.ChevalleyRoots.rootVector`: the root vector $X_\beta = w_{\alpha_{i_1}}(1) \cdots w_{\alpha_{i_r}}(1)\, e_j$ for the word of $\beta$.
* `Langlands.Groups.ChevalleyRoots.rootElement`: the root element $x_\beta(t) = \exp(t\, \mathrm{ad}\, X_\beta)$ for every root $\beta$.
* `Langlands.Groups.ChevalleyRoots.corootElement`: the element $h_{\alpha_i}(t) = w_{\alpha_i}(t) w_{\alpha_i}(1)^{-1}$.
* `Langlands.Groups.ChevalleyRoots.basisWeight`: the weight of each basis vector of $L$, which is $0$ for the Cartan part and $\beta$ for the root $\beta$.
* `Langlands.Groups.ChevalleyRoots.corootPairing`, `Langlands.Groups.ChevalleyRoots.corootChar`: the pairing $\mu \mapsto \langle \mu, \alpha_i^\vee \rangle$ on the root lattice, and the character $\mu \mapsto t^{\langle \mu, \alpha_i^\vee \rangle}$.
* `Langlands.Groups.ChevalleyRoots.simpleChar`: a character of the root lattice with value $t$ on $\alpha_i$.
* `Langlands.Groups.ChevalleyRoots.adjointRootDatum`: the root datum $(\mathbb{Z}\Phi, \Phi, \mathrm{Hom}(\mathbb{Z}\Phi, \mathbb{Z}), \Phi^\vee)$ of the split adjoint group.
* `Langlands.Groups.ChevalleyRoots.adjointBase`: the base of this root datum with the simple roots of $\Delta$.

## Main results

* `Langlands.Groups.ChevalleyRoots.exists_wordPerm_eq`: each root is the image of a simple root under a word in the simple reflections.
* `Langlands.Groups.ChevalleyRoots.weylElement_mem_weightSpace`: for $t \neq 0$, $w_{\alpha_i}(t)$ maps the weight space of $\mu$ to the weight space of $s_{\alpha_i} \mu$.
* `Langlands.Groups.ChevalleyRoots.rootVector_mem_weightSpace`, `Langlands.Groups.ChevalleyRoots.rootVector_ne_zero`, `Langlands.Groups.ChevalleyRoots.isNilpotent_ad_rootVector`: $X_\beta$ is a nonzero vector of weight $\beta$ with nilpotent adjoint endomorphism.
* `Langlands.Groups.ChevalleyRoots.rootElement_of_mem_support`, `Langlands.Groups.ChevalleyRoots.rootElement_reflectionPerm_self`: for a simple root, $x_{\alpha_i}(t)$ and $x_{-\alpha_i}(t)$ are the root elements of `Chevalley.lean`, up to the sign of $t$ for $-\alpha_i$.
* `Langlands.Groups.ChevalleyRoots.rootElement_add`, `Langlands.Groups.ChevalleyRoots.rootElement_mem`, `Langlands.Groups.ChevalleyRoots.rootElement_eq_conj`: the root subgroups are images of the additive group of $k$, they are in the elementary adjoint Chevalley group, and they are conjugates of simple root subgroups by Weyl elements.
* `Langlands.Groups.ChevalleyRoots.closure_rootElement`: the root elements $x_\beta(t)$ for all roots $\beta$ generate the elementary adjoint Chevalley group.
* `Langlands.Groups.ChevalleyRoots.lieEquiv_ext_geck`: an automorphism of $L$ is determined by its values on the $e_i$, $f_i$ and $h_i$.
* `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckE`, `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckF`, `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckH`: for $t \neq 0$, $h_{\alpha_i}(t)$ acts on $e_i$ by $t^2$, on $f_i$ by $t^{-2}$ and trivially on each $h_j$.
* `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckE_of_pairing_eq_zero`, `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckF_of_pairing_eq_zero`: $h_{\alpha_i}(t)$ fixes $e_j$ and $f_j$ for a simple root $\alpha_j \neq \alpha_i$ with $\langle \alpha_j, \alpha_i^\vee \rangle = 0$.
* `Langlands.Groups.ChevalleyRoots.corootElement_mul`: in rank one, $h_\alpha(s t) = h_\alpha(s) h_\alpha(t)$.
* `Langlands.Groups.ChevalleyRoots.torusElement_apply_of_mem_weightSpace`: the torus element $h(\chi)$ acts on the weight space of $\mu$ by $\chi(\mu)$.
* `Langlands.Groups.ChevalleyRoots.torusElement_mul_rootElement_mul_inv`, `Langlands.Groups.ChevalleyRoots.torusElement_mul_weylElement_mul_inv`: $h(\chi) x_\beta(t) h(\chi)^{-1} = x_\beta(\chi(\beta) t)$ and $h(\chi) w_{\alpha_i}(t) h(\chi)^{-1} = w_{\alpha_i}(\chi(\alpha_i) t)$.
* `Langlands.Groups.ChevalleyRoots.weylElement_neg`: $w_{\alpha_i}(-t) = w_{\alpha_i}(t)^{-1}$.
* `Langlands.Groups.ChevalleyRoots.corootElement_apply_of_mem_weightSpace`, `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckE_zpow`, `Langlands.Groups.ChevalleyRoots.corootElement_apply_geckF_zpow`: for $t \neq 0$, $h_{\alpha_i}(t)$ acts on the weight space of $\mu$ by $t^{\langle \mu, \alpha_i^\vee \rangle}$, so $h_{\alpha_i}(t) e_j = t^{\langle \alpha_j, \alpha_i^\vee \rangle} e_j$ and $h_{\alpha_i}(t) f_j = t^{-\langle \alpha_j, \alpha_i^\vee \rangle} f_j$ for all simple roots $\alpha_j$.
* `Langlands.Groups.ChevalleyRoots.corootElement_eq_torusElement`: $h_{\alpha_i}(t)$ is the torus element $h(\chi)$ of `Chevalley.lean` for the character $\chi = t^{\langle \cdot, \alpha_i^\vee \rangle}$.
* `Langlands.Groups.ChevalleyRoots.corootElement_mul_units`: $h_{\alpha_i}(s t) = h_{\alpha_i}(s) h_{\alpha_i}(t)$ for $s, t \neq 0$, in all ranks.
* `Langlands.Groups.ChevalleyRoots.commute_rootElement_of_weightSpace_eq_bot`: $x_\alpha(s)$ and $x_\beta(t)$ commute if the weight space of $\alpha + \beta$ is zero.
* `Langlands.Groups.ChevalleyRoots.weylElement_mul_simpleRootElement_mul_inv`, `Langlands.Groups.ChevalleyRoots.weylElement_mul_negSimpleRootElement_mul_inv`, `Langlands.Groups.ChevalleyRoots.corootElement_mul_simpleRootElement_mul_inv`, `Langlands.Groups.ChevalleyRoots.corootElement_mul_negSimpleRootElement_mul_inv`: the rank one relations $w_{\alpha}(t) x_{\pm\alpha}(u) w_{\alpha}(t)^{-1} = x_{\mp\alpha}(-t^{\mp 2} u)$ and $h_{\alpha}(t) x_{\pm\alpha}(u) h_{\alpha}(t)^{-1} = x_{\pm\alpha}(t^{\pm 2} u)$.
* `Langlands.Groups.ChevalleyRoots.commute_simpleRootElement_negSimpleRootElement`: $x_{\alpha_i}(s)$ and $x_{-\alpha_j}(t)$ commute for distinct simple roots.
* `Langlands.Groups.ChevalleyRoots.commute_simpleRootElement_of_pairing_eq_zero`, `Langlands.Groups.ChevalleyRoots.commute_negSimpleRootElement_of_pairing_eq_zero`: the root elements of distinct orthogonal simple roots commute.
* `Langlands.Groups.ChevalleyRoots.adjointRootDatum_rootSpan`: the roots span the character lattice, so the root datum is adjoint.
* `Langlands.Groups.ChevalleyRoots.dual_adjointRootDatum_corootSpan`: the coroots of the dual root datum span its cocharacter lattice, so the dual root datum is simply connected.
* `Langlands.Groups.ChevalleyRoots.lgroupDatum_split_adjoint`: the L-group datum of the split adjoint group is the split datum of the dual root datum with the dual base.

## Implementation notes

The root vector $X_\beta$ depends on a choice of a word for $\beta$. For a simple root the word is empty, and for the negative of a simple root $\alpha_i$ the word is $s_{\alpha_i}$, so $X_{\alpha_i} = e_i$ and $X_{-\alpha_i} = -f_i$. The results on orthogonal roots need the root system to be irreducible, because the Geck relation $[e_i, f_j] = 0$ for $i \neq j$ is proved in Mathlib with this hypothesis.

These results are not in this file. The weight space of $\alpha + \beta$ is zero when $\alpha + \beta$ is not a root and $\alpha \neq -\beta$, but this needs the root space decomposition of $L$, which is open here. Thus the commutation of $x_\alpha(s)$ and $x_\beta(t)$ for such roots is proved only under the hypothesis that this weight space is zero, and for simple roots. The general Steinberg commutator formula for $\alpha + \beta \in \Phi$ is open. The link between the torus of the root datum and the group in $\mathrm{Aut}(L)$ is not in this file.

## References

* C. Chevalley, Sur certains groupes simples, Tohoku Math. J. 7 (1955).
* R. Steinberg, Lectures on Chevalley groups, chapters 1 to 3.
* M. Geck, On the construction of semisimple Lie algebras and Chevalley groups, Proc. Amer. Math. Soc. 145 (2017).
* A. Borel, Automorphic L-functions, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2 (1979).
-/

noncomputable section

namespace Langlands.Groups.ChevalleyRoots

open RootPairing GeckConstruction Langlands.Groups.Chevalley

section Exp

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Module ℚ L]

/-- If $[x, y] = 0$, then $\exp(s\, \mathrm{ad}\, x)$ and $\exp(t\, \mathrm{ad}\, y)$ commute. -/
theorem commute_expAd_of_lie_eq_zero {x y : L} (hx : IsNilpotent (LieAlgebra.ad k L x))
    (hy : IsNilpotent (LieAlgebra.ad k L y)) (hxy : ⁅x, y⁆ = 0) (s t : k) :
    Commute (expAd x hx s) (expAd y hy t) := by
  have hc : Commute (LieAlgebra.ad k L x) (LieAlgebra.ad k L y) :=
    LinearMap.ext fun z => by
      simp only [Module.End.mul_apply, LieAlgebra.ad_apply]
      rw [leibniz_lie, hxy, zero_lie, zero_add]
  have hc' := (hc.smul_left s).smul_right t
  have h1 := IsNilpotent.exp_add_of_commute hc' (isNilpotent_smul_ad hx s)
    (isNilpotent_smul_ad hy t)
  have h2 := IsNilpotent.exp_add_of_commute hc'.symm (isNilpotent_smul_ad hy t)
    (isNilpotent_smul_ad hx s)
  rw [add_comm, h2] at h1
  refine LieEquiv.ext fun z => ?_
  simp only [lieAut_mul_apply, expAd_apply]
  exact congr($h1.symm z)

end Exp

section WeylWords

variable {k ι M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N] {P : RootPairing ι k M N} (b : P.Base)

/-- The permutation of the roots of a word $s_{i_1} \cdots s_{i_n}$ in the simple reflections. The value at $\beta$ is $s_{i_1}(\cdots s_{i_n}(\beta))$. -/
def wordPerm : List b.support → ι → ι
  | [] => fun β => β
  | i :: l => fun β => P.reflectionPerm i (wordPerm l β)

/-- The linear map of a word $s_{i_1} \cdots s_{i_n}$ in the simple reflections on $M$. -/
def wordReflection : List b.support → M → M
  | [] => fun m => m
  | i :: l => fun m => P.reflection i (wordReflection l m)

/-- The word of a list $i :: l$ is $s_i$ composed with the word of $l$. -/
@[simp] theorem wordPerm_cons (i : b.support) (l : List b.support) (β : ι) :
    wordPerm b (i :: l) β = P.reflectionPerm i (wordPerm b l β) := rfl

/-- The empty word is the identity. -/
@[simp] theorem wordPerm_nil (β : ι) : wordPerm b [] β = β := rfl

/-- The word of a concatenation is the composite of the words. -/
theorem wordPerm_append (l l' : List b.support) (β : ι) :
    wordPerm b (l ++ l') β = wordPerm b l (wordPerm b l' β) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

/-- The word of a list maps the root $\beta$ to the root of index `wordPerm b l β`. -/
theorem root_wordPerm (l : List b.support) (β : ι) :
    P.root (wordPerm b l β) = wordReflection b l (P.root β) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [wordReflection, root_reflectionPerm, ih]

/-- The linear map of a word commutes with negation. -/
theorem wordReflection_neg (l : List b.support) (m : M) :
    wordReflection b l (-m) = -wordReflection b l m := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [wordReflection, ih]

/-- Every root is the image of a simple root under a word in the simple reflections. -/
theorem exists_wordPerm_eq [Finite ι] [CharZero k] [P.IsCrystallographic] [P.IsReduced]
    (β : ι) : ∃ (l : List b.support) (j : b.support), wordPerm b l j = β := by
  refine b.induction_reflect (p := fun β => ∃ (l : List b.support) (j : b.support),
    wordPerm b l j = β) β ?_ ?_ ?_
  · rintro γ ⟨l, j, rfl⟩
    refine ⟨l ++ [j], j, P.root.injective ?_⟩
    rw [root_reflectionPerm, reflection_apply_self]
    simp only [wordPerm_append, wordPerm_cons, wordPerm_nil, root_wordPerm, root_reflectionPerm,
      reflection_apply_self, wordReflection_neg]
  · intro γ hγ
    exact ⟨[], ⟨γ, hγ⟩, rfl⟩
  · rintro γ j ⟨l, i, rfl⟩ hj
    exact ⟨⟨j, hj⟩ :: l, i, rfl⟩

/-- The reflection of the reflection of a root in itself is the root: $-(-\beta) = \beta$. -/
theorem reflectionPerm_reflectionPerm_self (β : ι) :
    P.reflectionPerm (P.reflectionPerm β β) (P.reflectionPerm β β) = β := by
  let := P.indexNeg
  exact neg_neg β

/-- The negative $-\alpha_i$ of a simple root is not a simple root. -/
theorem reflectionPerm_self_notMem_support [CharZero k] (i : b.support) :
    P.reflectionPerm i i ∉ b.support := by
  intro h
  let := P.indexNeg
  exact (Base.IsPos.neg_iff_not b (i : ι)).mp (Base.isPos_of_mem_support h)
    (Base.isPos_of_mem_support i.2)

/-- There is a word in the simple reflections and a simple root with image $\beta$, in the form of a pair. -/
theorem exists_rootWord [Finite ι] [CharZero k] [P.IsCrystallographic] [P.IsReduced] (β : ι) :
    ∃ p : List b.support × b.support, wordPerm b p.1 p.2 = β := by
  obtain ⟨l, j, h⟩ := exists_wordPerm_eq b β
  exact ⟨(l, j), h⟩

open scoped Classical in
/-- A choice of a word $w$ in the simple reflections and of a simple root $\alpha_j$ with $w(\alpha_j) = \beta$. For a simple root $\beta = \alpha_i$ the choice is the empty word and $\alpha_i$. For $\beta = -\alpha_i$ the choice is the word $s_i$ and $\alpha_i$. -/
def rootWord [Finite ι] [CharZero k] [P.IsCrystallographic] [P.IsReduced] (β : ι) :
    List b.support × b.support :=
  if h : β ∈ b.support then ([], ⟨β, h⟩)
  else if h' : P.reflectionPerm β β ∈ b.support then ([⟨_, h'⟩], ⟨_, h'⟩)
  else Classical.choose (exists_rootWord b β)

variable [Finite ι] [CharZero k] [P.IsCrystallographic] [P.IsReduced]

/-- The chosen word maps the chosen simple root to $\beta$. -/
theorem wordPerm_rootWord (β : ι) : wordPerm b (rootWord b β).1 (rootWord b β).2 = β := by
  unfold rootWord
  split_ifs with h h'
  · rfl
  · exact reflectionPerm_reflectionPerm_self β
  · exact Classical.choose_spec (exists_rootWord b β)

/-- For a simple root $\alpha_i$ the chosen word is empty and the chosen simple root is $\alpha_i$. -/
theorem rootWord_of_mem_support (i : b.support) : rootWord b i = ([], i) := by
  simp [rootWord, i.2]

/-- For the negative $-\alpha_i$ of a simple root the chosen word is $s_i$ and the chosen simple root is $\alpha_i$. -/
theorem rootWord_reflectionPerm_self (i : b.support) :
    rootWord b (P.reflectionPerm i i) = ([i], i) := by
  have h' : P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i) ∈ b.support := by
    rw [reflectionPerm_reflectionPerm_self]; exact i.2
  have hi : (⟨_, h'⟩ : b.support) = i := Subtype.ext (reflectionPerm_reflectionPerm_self _)
  simp [rootWord, reflectionPerm_self_notMem_support b i, h', hi]

end WeylWords

section Geck

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k ι M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] (b : P.Base)

/-- The bracket $[h_j, e_i] = \langle \alpha_i, \alpha_j^\vee \rangle e_i$ in the Geck Lie algebra. -/
theorem lie_geckH_geckE (j i : b.support) :
    ⁅geckH b j, geckE b i⁆ = P.pairing i j • geckE b i := by
  have hl := lie_h_e (b := b) i j
  refine Subtype.ext ?_
  change ⁅h j, e i⁆ = P.pairing i j • e i
  rw [hl, ← P.algebraMap_pairingIn ℤ]
  simp [Base.cartanMatrixIn_def, Int.cast_smul_eq_zsmul]

/-- The bracket $[h_j, f_i] = -\langle \alpha_i, \alpha_j^\vee \rangle f_i$ in the Geck Lie algebra. -/
theorem lie_geckH_geckF (j i : b.support) :
    ⁅geckH b j, geckF b i⁆ = -P.pairing i j • geckF b i := by
  have hl := lie_h_f (b := b) i j
  refine Subtype.ext ?_
  change ⁅h j, f i⁆ = -P.pairing i j • f i
  rw [hl, ← P.algebraMap_pairingIn ℤ]
  simp [Base.cartanMatrixIn_def, Int.cast_smul_eq_zsmul]

/-- The weight space of weight $m \in M$ in the Geck Lie algebra: the elements $x$ with $[h_j, x] = \langle m, \alpha_j^\vee \rangle x$ for all simple roots $\alpha_j$. -/
def weightSpace (m : M) : Submodule k (lieAlgebra b) where
  carrier := {x | ∀ j : b.support, ⁅geckH b j, x⁆ = P.coroot' j m • x}
  add_mem' {x y} hx hy j := by simp only [Set.mem_ofPred_eq] at hx hy; rw [lie_add, hx j, hy j,
    smul_add]
  zero_mem' j := by simp
  smul_mem' c x hx j := by
    simp only [Set.mem_ofPred_eq] at hx; rw [lie_smul, hx j, smul_comm]

/-- The element $e_i$ is in the weight space of the simple root $\alpha_i$. -/
theorem geckE_mem_weightSpace (i : b.support) : geckE b i ∈ weightSpace b (P.root i) := by
  intro j
  rw [lie_geckH_geckE, root_coroot'_eq_pairing]

/-- The element $f_i$ is in the weight space of the negative simple root $-\alpha_i$. -/
theorem geckF_mem_weightSpace (i : b.support) : geckF b i ∈ weightSpace b (-P.root i) := by
  intro j
  rw [lie_geckH_geckF, map_neg, root_coroot'_eq_pairing]

variable [P.IsReduced]

/-- The formula $w_{\alpha_i}(t)(e_i) = -t^{-2} f_i$ for $t \neq 0$. -/
theorem weylElement_apply_geckE (i : b.support) {t : k} (ht : t ≠ 0) :
    weylElement b i t (geckE b i) = -(t⁻¹ ^ 2) • geckF b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e,
    negSimpleRootElement_apply_e, map_sub, simpleRootElement_apply_h, simpleRootElement_apply_f,
    map_smul]
  match_scalars <;> field_simp <;> ring

/-- The formula $w_{\alpha_i}(t)(f_i) = -t^2 e_i$ for $t \neq 0$. -/
theorem weylElement_apply_geckF (i : b.support) {t : k} (ht : t ≠ 0) :
    weylElement b i t (geckF b i) = -(t ^ 2) • geckE b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e,
    negSimpleRootElement_apply_e, negSimpleRootElement_apply_f, negSimpleRootElement_apply_h,
    map_sub, map_add, simpleRootElement_apply_h, simpleRootElement_apply_f, map_smul]
  match_scalars <;> field_simp <;> ring

/-- The formula $w_{\alpha_i}(t)(h_i) = -h_i$ for $t \neq 0$. -/
theorem weylElement_apply_geckH (i : b.support) {t : k} (ht : t ≠ 0) :
    weylElement b i t (geckH b i) = -geckH b i := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement_apply_e,
    negSimpleRootElement_apply_e, negSimpleRootElement_apply_h,
    map_sub, map_add, simpleRootElement_apply_h, simpleRootElement_apply_f, map_smul]
  match_scalars <;> field_simp <;> ring

/-- The formula $w_{\alpha_i}(t)(h_j) = h_j - \langle \alpha_i, \alpha_j^\vee \rangle h_i$ for $t \neq 0$. Thus $w_{\alpha_i}(t)$ acts on the Cartan subalgebra as the simple reflection $s_{\alpha_i}$. -/
theorem weylElement_apply_geckH_of (i j : b.support) {t : k} (ht : t ≠ 0) :
    weylElement b i t (geckH b j) = geckH b j - P.pairing i j • geckH b i := by
  set z := geckH b j - (P.pairing i j / 2) • geckH b i with hz
  have he : ⁅geckE b i, z⁆ = 0 := by
    rw [hz, lie_sub, lie_smul, ← lie_skew, ← lie_skew (geckE b i) (geckH b i), lie_geckH_geckE,
      lie_geckH_geckE, P.pairing_same]
    module
  have hf : ⁅geckF b i, z⁆ = 0 := by
    rw [hz, lie_sub, lie_smul, ← lie_skew, ← lie_skew (geckF b i) (geckH b i), lie_geckH_geckF,
      lie_geckH_geckF, P.pairing_same]
    module
  have hwz : weylElement b i t z = z := by
    simp only [weylElement, lieAut_mul_apply, simpleRootElement, negSimpleRootElement,
      expAd_apply_of_lie_eq_zero _ _ _ he, expAd_apply_of_lie_eq_zero _ _ _ hf]
  have hj : geckH b j = z + (P.pairing i j / 2) • geckH b i := by rw [hz]; abel
  rw [hj, map_add, map_smul, hwz, weylElement_apply_geckH b i ht, hz]
  module

/-- The element $w_{\alpha_i}(t)$ for $t \neq 0$ maps the weight space of $m$ to the weight space of $s_{\alpha_i}(m)$. -/
theorem weylElement_mem_weightSpace (i : b.support) {t : k} (ht : t ≠ 0) {m : M}
    {x : lieAlgebra b} (hx : x ∈ weightSpace b m) :
    weylElement b i t x ∈ weightSpace b (P.reflection i m) := by
  intro j
  have hh : geckH b j = weylElement b i t (geckH b j - P.pairing i j • geckH b i) := by
    rw [map_sub, map_smul, weylElement_apply_geckH_of b i j ht, weylElement_apply_geckH b i ht]
    module
  rw [hh, ← LieEquiv.map_lie, sub_lie, smul_lie, hx j, hx i, reflection_apply]
  simp only [map_sub, map_smul, root_coroot'_eq_pairing, smul_eq_mul]
  module

/-- The element $w_{\alpha_{i_1}}(1) \cdots w_{\alpha_{i_n}}(1)$ of a word in the simple reflections. -/
def weylWord : List b.support → (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b)
  | [] => 1
  | i :: l => weylElement b i 1 * weylWord l

/-- The element of a word is in the elementary adjoint Chevalley group. -/
theorem weylWord_mem (l : List b.support) : weylWord b l ∈ ElementaryAdjointChevalleyGroup b := by
  induction l with
  | nil => exact one_mem _
  | cons i l ih => exact mul_mem (weylElement_mem b i 1) ih

/-- The element of a word $w$ maps the weight space of $m$ to the weight space of $w(m)$. -/
theorem weylWord_mem_weightSpace (l : List b.support) {m : M} {x : lieAlgebra b}
    (hx : x ∈ weightSpace b m) : weylWord b l x ∈ weightSpace b (wordReflection b l m) := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact weylElement_mem_weightSpace b i one_ne_zero ih

/-- The root vector $e_\beta = w(e_j)$ for the chosen word $w$ and simple root $\alpha_j$ with $w(\alpha_j) = \beta$. -/
def rootVector (β : ι) : lieAlgebra b :=
  weylWord b (rootWord b β).1 (geckE b (rootWord b β).2)

/-- The root vector $e_\beta$ is in the weight space of the root $\beta$. -/
theorem rootVector_mem_weightSpace (β : ι) : rootVector b β ∈ weightSpace b (P.root β) := by
  have h := weylWord_mem_weightSpace b (rootWord b β).1 (geckE_mem_weightSpace b (rootWord b β).2)
  rwa [← root_wordPerm, wordPerm_rootWord] at h

/-- The root vector $e_\beta$ is not zero. -/
theorem rootVector_ne_zero (β : ι) : rootVector b β ≠ 0 := by
  intro h
  exact (isSl2Triple_geck b _).e_ne_zero ((weylWord b _).injective (h.trans (map_zero _).symm))

/-- The endomorphism $\mathrm{ad}\, e_\beta$ is nilpotent. -/
theorem isNilpotent_ad_rootVector (β : ι) :
    IsNilpotent (LieAlgebra.ad k (lieAlgebra b) (rootVector b β)) :=
  isNilpotent_ad_lieEquiv_apply _ (isNilpotent_ad_geckE b _)

/-- For a simple root $\alpha_i$ the root vector is $e_i$. -/
theorem rootVector_of_mem_support (i : b.support) : rootVector b i = geckE b i := by
  simp [rootVector, rootWord_of_mem_support, weylWord]

/-- For the negative $-\alpha_i$ of a simple root the root vector is $-f_i$. -/
theorem rootVector_reflectionPerm_self (i : b.support) :
    rootVector b (P.reflectionPerm i i) = -geckF b i := by
  simp [rootVector, rootWord_reflectionPerm_self, weylWord,
    weylElement_apply_geckE b i one_ne_zero]

/-- The root element $x_\beta(t) = \exp(t\, \mathrm{ad}\, e_\beta)$ for a root $\beta$. -/
def rootElement (β : ι) (t : k) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  expAd (rootVector b β) (isNilpotent_ad_rootVector b β) t

/-- The root element is a conjugate of a simple root element: $x_\beta(t) = w\, x_{\alpha_j}(t)\, w^{-1}$ for the chosen word $w$ and simple root $\alpha_j$. -/
theorem rootElement_eq_conj (β : ι) (t : k) :
    rootElement b β t = weylWord b (rootWord b β).1 * simpleRootElement b (rootWord b β).2 t *
      (weylWord b (rootWord b β).1)⁻¹ :=
  (lieEquiv_mul_expAd_mul_inv _ _ _ t).symm

/-- The equation $x_\beta(s + t) = x_\beta(s) x_\beta(t)$. -/
theorem rootElement_add (β : ι) (s t : k) :
    rootElement b β (s + t) = rootElement b β s * rootElement b β t :=
  expAd_add _ _ s t

/-- The equation $x_\beta(0) = 1$. -/
theorem rootElement_zero (β : ι) : rootElement b β 0 = 1 :=
  expAd_zero _ _

/-- The equation $x_\beta(-t) = x_\beta(t)^{-1}$. -/
theorem rootElement_neg (β : ι) (t : k) : rootElement b β (-t) = (rootElement b β t)⁻¹ :=
  expAd_neg _ _ t

/-- The root element $x_\beta(t)$ is in the elementary adjoint Chevalley group. -/
theorem rootElement_mem (β : ι) (t : k) :
    rootElement b β t ∈ ElementaryAdjointChevalleyGroup b := by
  rw [rootElement_eq_conj]
  exact mul_mem (mul_mem (weylWord_mem b _) (simpleRootElement_mem b _ t))
    (inv_mem (weylWord_mem b _))

/-- For a simple root $\alpha_i$ the root element is the simple root element: $x_{\alpha_i}(t) = \exp(t\, \mathrm{ad}\, e_i)$. -/
theorem rootElement_of_mem_support (i : b.support) (t : k) :
    rootElement b i t = simpleRootElement b i t :=
  expAd_congr (rootVector_of_mem_support b i) _ _ t

/-- For the negative $-\alpha_i$ of a simple root the root element is $x_{-\alpha_i}(t) = \exp(-t\, \mathrm{ad}\, f_i)$. -/
theorem rootElement_reflectionPerm_self (i : b.support) (t : k) :
    rootElement b (P.reflectionPerm i i) t = negSimpleRootElement b i (-t) := by
  have h : rootVector b (P.reflectionPerm i i) = (-1 : k) • geckF b i := by
    rw [rootVector_reflectionPerm_self, neg_one_smul]
  have hn := isNilpotent_ad_rootVector b (P.reflectionPerm i i)
  rw [h] at hn
  rw [rootElement, expAd_congr h _ hn, expAd_smul _ (isNilpotent_ad_geckF b i), mul_neg_one]
  rfl

/-- The root elements $x_\beta(t)$ for all roots $\beta$ and all $t$ in $k$ generate the elementary adjoint Chevalley group. -/
theorem closure_rootElement :
    Subgroup.closure (Set.range fun p : ι × k => rootElement b p.1 p.2) =
      ElementaryAdjointChevalleyGroup b := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨⟨β, t⟩, rfl⟩
    exact rootElement_mem b β t
  · rintro _ (⟨⟨i, t⟩, rfl⟩ | ⟨⟨i, t⟩, rfl⟩)
    · exact Subgroup.subset_closure ⟨(i, t), rootElement_of_mem_support b i t⟩
    · refine Subgroup.subset_closure ⟨(P.reflectionPerm i i, -t), ?_⟩
      simp only [rootElement_reflectionPerm_self, neg_neg]

omit [P.IsReduced] in
/-- Two automorphisms of the Geck Lie algebra that agree on all $e_i$, $f_i$ and $h_i$ are equal. -/
theorem lieEquiv_ext_geck {φ ψ : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b}
    (he : ∀ i, φ (geckE b i) = ψ (geckE b i)) (hf : ∀ i, φ (geckF b i) = ψ (geckF b i))
    (hh : ∀ i, φ (geckH b i) = ψ (geckH b i)) : φ = ψ := by
  refine LieEquiv.ext fun y => ?_
  obtain ⟨x, hx⟩ := y
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · exact hh i
    · exact he i
    · exact hf i
  | zero => exact (map_zero φ).trans (map_zero ψ).symm
  | add x y hx hy px py =>
    exact (map_add φ ⟨x, hx⟩ ⟨y, hy⟩).trans
      ((congrArg₂ (· + ·) px py).trans (map_add ψ _ _).symm)
  | smul a x hx px =>
    exact (map_smul φ a ⟨x, hx⟩).trans ((congrArg (a • ·) px).trans (map_smul ψ a _).symm)
  | lie x y hx hy px py =>
    exact (φ.map_lie ⟨x, hx⟩ ⟨y, hy⟩).trans
      ((congrArg₂ (⁅·, ·⁆) px py).trans (ψ.map_lie _ _).symm)

/-- The inverse of $w_{\alpha_i}(1)$ maps $e_i$ to $-f_i$. -/
theorem weylElement_one_inv_apply_geckE (i : b.support) :
    (weylElement b i 1)⁻¹ (geckE b i) = -geckF b i := by
  rw [lieAut_inv_apply, LieEquiv.symm_apply_eq, map_neg, weylElement_apply_geckF b i one_ne_zero]
  simp

/-- The inverse of $w_{\alpha_i}(1)$ maps $f_i$ to $-e_i$. -/
theorem weylElement_one_inv_apply_geckF (i : b.support) :
    (weylElement b i 1)⁻¹ (geckF b i) = -geckE b i := by
  rw [lieAut_inv_apply, LieEquiv.symm_apply_eq, map_neg, weylElement_apply_geckE b i one_ne_zero]
  simp

/-- The inverse of $w_{\alpha_i}(1)$ maps $h_j$ to $h_j - \langle \alpha_i, \alpha_j^\vee \rangle h_i$. -/
theorem weylElement_one_inv_apply_geckH (i j : b.support) :
    (weylElement b i 1)⁻¹ (geckH b j) = geckH b j - P.pairing i j • geckH b i := by
  rw [lieAut_inv_apply, LieEquiv.symm_apply_eq, map_sub, map_smul,
    weylElement_apply_geckH_of b i j one_ne_zero, weylElement_apply_geckH b i one_ne_zero]
  module

/-- The rank one relation $w_{\alpha_i}(t) x_{\alpha_i}(u) w_{\alpha_i}(t)^{-1} = x_{-\alpha_i}(-t^{-2} u)$ for $t \neq 0$. -/
theorem weylElement_mul_simpleRootElement_mul_inv (i : b.support) {t : k} (ht : t ≠ 0) (u : k) :
    weylElement b i t * simpleRootElement b i u * (weylElement b i t)⁻¹ =
      negSimpleRootElement b i (-(t⁻¹ ^ 2 * u)) := by
  have hn := isNilpotent_ad_lieEquiv_apply (weylElement b i t) (isNilpotent_ad_geckE b i)
  rw [weylElement_apply_geckE b i ht] at hn
  rw [simpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (weylElement_apply_geckE b i ht) _ hn, expAd_smul _ (isNilpotent_ad_geckF b i),
    negSimpleRootElement]
  congr 1
  ring

/-- The rank one relation $w_{\alpha_i}(t) x_{-\alpha_i}(u) w_{\alpha_i}(t)^{-1} = x_{\alpha_i}(-t^2 u)$ for $t \neq 0$. -/
theorem weylElement_mul_negSimpleRootElement_mul_inv (i : b.support) {t : k} (ht : t ≠ 0)
    (u : k) :
    weylElement b i t * negSimpleRootElement b i u * (weylElement b i t)⁻¹ =
      simpleRootElement b i (-(t ^ 2 * u)) := by
  have hn := isNilpotent_ad_lieEquiv_apply (weylElement b i t) (isNilpotent_ad_geckF b i)
  rw [weylElement_apply_geckF b i ht] at hn
  rw [negSimpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (weylElement_apply_geckF b i ht) _ hn, expAd_smul _ (isNilpotent_ad_geckE b i),
    simpleRootElement]
  congr 1
  ring

/-- The element $h_{\alpha_i}(t) = w_{\alpha_i}(t) w_{\alpha_i}(1)^{-1}$ of the image of the coroot $\alpha_i^\vee$. -/
def corootElement (i : b.support) (t : k) : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b :=
  weylElement b i t * (weylElement b i 1)⁻¹

/-- The element $h_{\alpha_i}(t)$ is in the elementary adjoint Chevalley group. -/
theorem corootElement_mem (i : b.support) (t : k) :
    corootElement b i t ∈ ElementaryAdjointChevalleyGroup b :=
  mul_mem (weylElement_mem b i t) (inv_mem (weylElement_mem b i 1))

/-- The equation $h_{\alpha_i}(1) = 1$. -/
theorem corootElement_one (i : b.support) : corootElement b i 1 = 1 :=
  mul_inv_cancel _

/-- The formula $h_{\alpha_i}(t)(e_i) = t^2 e_i$ for $t \neq 0$, where $2 = \langle \alpha_i, \alpha_i^\vee \rangle$. -/
theorem corootElement_apply_geckE (i : b.support) {t : k} (ht : t ≠ 0) :
    corootElement b i t (geckE b i) = t ^ 2 • geckE b i := by
  rw [corootElement, lieAut_mul_apply, weylElement_one_inv_apply_geckE, map_neg,
    weylElement_apply_geckF b i ht, neg_smul, neg_neg]

/-- The formula $h_{\alpha_i}(t)(f_i) = t^{-2} f_i$ for $t \neq 0$. -/
theorem corootElement_apply_geckF (i : b.support) {t : k} (ht : t ≠ 0) :
    corootElement b i t (geckF b i) = t⁻¹ ^ 2 • geckF b i := by
  rw [corootElement, lieAut_mul_apply, weylElement_one_inv_apply_geckF, map_neg,
    weylElement_apply_geckE b i ht, neg_smul, neg_neg]

/-- The element $h_{\alpha_i}(t)$ for $t \neq 0$ fixes each $h_j$, so it acts trivially on the Cartan subalgebra. -/
theorem corootElement_apply_geckH (i j : b.support) {t : k} (ht : t ≠ 0) :
    corootElement b i t (geckH b j) = geckH b j := by
  rw [corootElement, lieAut_mul_apply, weylElement_one_inv_apply_geckH, map_sub, map_smul,
    weylElement_apply_geckH_of b i j ht, weylElement_apply_geckH b i ht]
  module

/-- The rank one relation $h_{\alpha_i}(t) x_{\alpha_i}(u) h_{\alpha_i}(t)^{-1} = x_{\alpha_i}(t^2 u)$ for $t \neq 0$. -/
theorem corootElement_mul_simpleRootElement_mul_inv (i : b.support) {t : k} (ht : t ≠ 0)
    (u : k) :
    corootElement b i t * simpleRootElement b i u * (corootElement b i t)⁻¹ =
      simpleRootElement b i (t ^ 2 * u) := by
  have hn := isNilpotent_ad_lieEquiv_apply (corootElement b i t) (isNilpotent_ad_geckE b i)
  rw [corootElement_apply_geckE b i ht] at hn
  rw [simpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (corootElement_apply_geckE b i ht) _ hn, expAd_smul _ (isNilpotent_ad_geckE b i),
    mul_comm]
  rfl

/-- The rank one relation $h_{\alpha_i}(t) x_{-\alpha_i}(u) h_{\alpha_i}(t)^{-1} = x_{-\alpha_i}(t^{-2} u)$ for $t \neq 0$. -/
theorem corootElement_mul_negSimpleRootElement_mul_inv (i : b.support) {t : k} (ht : t ≠ 0)
    (u : k) :
    corootElement b i t * negSimpleRootElement b i u * (corootElement b i t)⁻¹ =
      negSimpleRootElement b i (t⁻¹ ^ 2 * u) := by
  have hn := isNilpotent_ad_lieEquiv_apply (corootElement b i t) (isNilpotent_ad_geckF b i)
  rw [corootElement_apply_geckF b i ht] at hn
  rw [negSimpleRootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (corootElement_apply_geckF b i ht) _ hn, expAd_smul _ (isNilpotent_ad_geckF b i),
    mul_comm]
  rfl

/-- In rank one, $t \mapsto h_{\alpha}(t)$ is multiplicative: $h_\alpha(s t) = h_\alpha(s) h_\alpha(t)$ for $s, t \neq 0$. -/
theorem corootElement_mul [Subsingleton b.support] (i : b.support) {s t : k} (hs : s ≠ 0)
    (ht : t ≠ 0) : corootElement b i (s * t) = corootElement b i s * corootElement b i t := by
  have hst := mul_ne_zero hs ht
  refine lieEquiv_ext_geck b (fun j => ?_) (fun j => ?_) (fun j => ?_)
  · obtain rfl := Subsingleton.elim j i
    rw [lieAut_mul_apply, corootElement_apply_geckE b j hst, corootElement_apply_geckE b j ht,
      map_smul, corootElement_apply_geckE b j hs, smul_smul, mul_pow, mul_comm]
  · obtain rfl := Subsingleton.elim j i
    rw [lieAut_mul_apply, corootElement_apply_geckF b j hst, corootElement_apply_geckF b j ht,
      map_smul, corootElement_apply_geckF b j hs, smul_smul, mul_inv, mul_pow, mul_comm]
  · rw [lieAut_mul_apply, corootElement_apply_geckH b i j hst, corootElement_apply_geckH b i j ht,
      corootElement_apply_geckH b i j hs]

section Irreducible

variable [P.IsIrreducible]

/-- For distinct simple roots, $[e_i, f_j] = 0$ (Geck, Lemma 3.5). -/
theorem lie_geckE_geckF_of_ne {i j : b.support} (hij : i ≠ j) : ⁅geckE b i, geckF b j⁆ = 0 :=
  Subtype.ext (lie_e_f_ne (b := b) hij)

/-- For distinct simple roots the elements $x_{\alpha_i}(s)$ and $x_{-\alpha_j}(t)$ commute. This is the Steinberg relation for the pair $\alpha_i, -\alpha_j$, as $\alpha_i - \alpha_j$ is not a root. -/
theorem commute_simpleRootElement_negSimpleRootElement {i j : b.support} (hij : i ≠ j)
    (s t : k) : Commute (simpleRootElement b i s) (negSimpleRootElement b j t) :=
  commute_expAd_of_lie_eq_zero _ _ (lie_geckE_geckF_of_ne b hij) s t

/-- For distinct orthogonal simple roots, $[e_i, e_j] = 0$. The proof uses that $e_j$ is a lowest weight vector of weight $0$ for the $\mathfrak{sl}_2$ triple of $\alpha_i$. -/
theorem lie_geckE_geckE_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) : ⁅geckE b i, geckE b j⁆ = 0 := by
  have ht := (isSl2Triple_geck b i).symm
  have hp : ht.HasPrimitiveVectorWith (geckE b j) (0 : k) :=
    { ne_zero := (isSl2Triple_geck b j).e_ne_zero
      lie_h := by rw [neg_lie, lie_geckH_geckE, h0]; simp
      lie_e := by rw [← lie_skew, lie_geckE_geckF_of_ne b (Ne.symm hij), neg_zero] }
  have h := hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  simpa using h

/-- For distinct orthogonal simple roots, $[f_i, f_j] = 0$. -/
theorem lie_geckF_geckF_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) : ⁅geckF b i, geckF b j⁆ = 0 := by
  have ht := isSl2Triple_geck b i
  have hp : ht.HasPrimitiveVectorWith (geckF b j) (0 : k) :=
    { ne_zero := (isSl2Triple_geck b j).f_ne_zero
      lie_h := by rw [lie_geckH_geckF, h0]; simp
      lie_e := lie_geckE_geckF_of_ne b hij }
  have h := hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  simpa using h

/-- For distinct orthogonal simple roots $\alpha_i \perp \alpha_j$, the root elements $x_{\alpha_i}(s)$ and $x_{\alpha_j}(t)$ commute. -/
theorem commute_simpleRootElement_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (s t : k) :
    Commute (simpleRootElement b i s) (simpleRootElement b j t) :=
  commute_expAd_of_lie_eq_zero _ _ (lie_geckE_geckE_of_pairing_eq_zero b hij h0) s t

/-- For distinct orthogonal simple roots $\alpha_i \perp \alpha_j$, the root elements $x_{-\alpha_i}(s)$ and $x_{-\alpha_j}(t)$ commute. -/
theorem commute_negSimpleRootElement_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (s t : k) :
    Commute (negSimpleRootElement b i s) (negSimpleRootElement b j t) :=
  commute_expAd_of_lie_eq_zero _ _ (lie_geckF_geckF_of_pairing_eq_zero b hij h0) s t

/-- For a simple root $\alpha_j \neq \alpha_i$ orthogonal to $\alpha_i$, the element $w_{\alpha_i}(t)$ fixes $e_j$. -/
theorem weylElement_apply_geckE_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (t : k) : weylElement b i t (geckE b j) = geckE b j := by
  have hf : ⁅geckF b i, geckE b j⁆ = 0 := by
    rw [← lie_skew, lie_geckE_geckF_of_ne b (Ne.symm hij), neg_zero]
  simp only [weylElement, lieAut_mul_apply, simpleRootElement, negSimpleRootElement,
    expAd_apply_of_lie_eq_zero _ _ _ (lie_geckE_geckE_of_pairing_eq_zero b hij h0),
    expAd_apply_of_lie_eq_zero _ _ _ hf]

/-- For a simple root $\alpha_j \neq \alpha_i$ orthogonal to $\alpha_i$, the element $w_{\alpha_i}(t)$ fixes $f_j$. -/
theorem weylElement_apply_geckF_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (t : k) : weylElement b i t (geckF b j) = geckF b j := by
  simp only [weylElement, lieAut_mul_apply, simpleRootElement, negSimpleRootElement,
    expAd_apply_of_lie_eq_zero _ _ _ (lie_geckE_geckF_of_ne b hij),
    expAd_apply_of_lie_eq_zero _ _ _ (lie_geckF_geckF_of_pairing_eq_zero b hij h0)]

/-- For a simple root $\alpha_j \neq \alpha_i$ orthogonal to $\alpha_i$, the element $h_{\alpha_i}(t)$ fixes $e_j$. This is the formula $h_{\alpha_i}(t) e_j = t^{\langle \alpha_j, \alpha_i^\vee \rangle} e_j$ in the case $\langle \alpha_j, \alpha_i^\vee \rangle = 0$. -/
theorem corootElement_apply_geckE_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (t : k) : corootElement b i t (geckE b j) = geckE b j := by
  have h1 := weylElement_apply_geckE_of_pairing_eq_zero b hij h0 1
  rw [corootElement, lieAut_mul_apply, lieAut_inv_apply,
    (LieEquiv.symm_apply_eq _).2 h1.symm, weylElement_apply_geckE_of_pairing_eq_zero b hij h0]

/-- For a simple root $\alpha_j \neq \alpha_i$ orthogonal to $\alpha_i$, the element $h_{\alpha_i}(t)$ fixes $f_j$. -/
theorem corootElement_apply_geckF_of_pairing_eq_zero {i j : b.support} (hij : i ≠ j)
    (h0 : P.pairing j i = 0) (t : k) : corootElement b i t (geckF b j) = geckF b j := by
  have h1 := weylElement_apply_geckF_of_pairing_eq_zero b hij h0 1
  rw [corootElement, lieAut_mul_apply, lieAut_inv_apply,
    (LieEquiv.symm_apply_eq _).2 h1.symm, weylElement_apply_geckF_of_pairing_eq_zero b hij h0]

end Irreducible

section Torus

omit [DecidableEq ι] [P.IsReduced] in
/-- An element $v$ of the span of the roots with $\langle v, \alpha_j^\vee \rangle = 0$ for all simple roots $\alpha_j$ is zero. -/
theorem eq_zero_of_coroot'_eq_zero {v : M} (hv : v ∈ P.rootSpan k)
    (h : ∀ j : b.support, P.coroot' j v = 0) : v = 0 := by
  have hall : ∀ β, P.coroot' β v = 0 := by
    intro β
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun ℤ).1
      (b.coroot_mem_span_int β)
    change P.toLinearMap v (P.coroot β) = 0
    rw [← hc, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_zsmul]
    change c j • P.coroot' j v = 0
    rw [h j, smul_zero]
  have hk : v ∈ LinearMap.ker P.RootForm := by
    rw [LinearMap.mem_ker]
    ext y
    simp [rootForm_apply_apply, hall]
  exact Submodule.disjoint_def.1 P.disjoint_rootSpan_ker_rootForm v hv hk

/-- The weight of a basis vector of the space of the Geck construction: $0$ for $u_i$ and $\alpha$ for $v_\alpha$. -/
def basisWeight : b.support ⊕ ι → M := Sum.elim 0 P.root

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] [P.IsReduced] in
/-- The weight of a basis vector is in the span of the roots. -/
theorem basisWeight_mem (a : b.support ⊕ ι) : basisWeight b a ∈ P.rootSpan k := by
  rcases a with a | a
  · exact zero_mem _
  · exact Submodule.subset_span ⟨a, rfl⟩

omit [P.IsReduced] in
/-- The matrix of $h_j$ is the diagonal matrix with the entries $\langle \mathrm{wt}(a), \alpha_j^\vee \rangle$. -/
theorem coe_geckH (j : b.support) :
    ((geckH b j : lieAlgebra b) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) =
      Matrix.diagonal fun a => P.coroot' j (basisWeight b a) := by
  change h j = _
  rw [h_eq_diagonal]
  congr 1
  ext (a | a)
  · simp [basisWeight]
  · simp [basisWeight, ← P.algebraMap_pairingIn ℤ]

omit [P.IsReduced] in
/-- An element of the weight space of $\mu$ has a zero entry at $(a, c)$ unless $\mathrm{wt}(a) - \mathrm{wt}(c) = \mu$. -/
theorem apply_eq_zero_of_mem_weightSpace {μ : M} (hμ : μ ∈ P.rootSpan k) {x : lieAlgebra b}
    (hx : x ∈ weightSpace b μ) {a c : b.support ⊕ ι}
    (hac : basisWeight b a - basisWeight b c ≠ μ) :
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) a c = 0 := by
  by_contra hne
  apply hac
  rw [← sub_eq_zero]
  refine eq_zero_of_coroot'_eq_zero b
    (sub_mem (sub_mem (basisWeight_mem b a) (basisWeight_mem b c)) hμ) fun j => ?_
  have h1 := congr(($(hx j) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) a c)
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, coe_geckH] at h1
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    SetLike.val_smul, Matrix.smul_apply, smul_eq_mul] at h1
  rw [map_sub, map_sub]
  apply mul_right_cancel₀ hne
  linear_combination h1

omit [P.IsReduced] in
/-- The element $h_i$ is in the weight space of $0$. -/
theorem geckH_mem_weightSpace (i : b.support) : geckH b i ∈ weightSpace b 0 := by
  intro j
  rw [map_zero, zero_smul]
  exact Subtype.ext (lie_h_h j i)

omit [P.IsReduced] in
/-- The bracket of elements of the weight spaces of $\mu$ and $\nu$ is in the weight space of $\mu + \nu$. -/
theorem lie_mem_weightSpace {μ ν : M} {x y : lieAlgebra b} (hx : x ∈ weightSpace b μ)
    (hy : y ∈ weightSpace b ν) : ⁅x, y⁆ ∈ weightSpace b (μ + ν) := by
  intro j
  rw [leibniz_lie, hx j, hy j, smul_lie, lie_smul, map_add, add_smul]

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] [P.IsReduced] in
/-- The root lattice is contained in the span of the roots. -/
theorem mem_rootSpan_of_mem_rootLattice {R : Type*} [CommRing R] [Module R M] {μ : M}
    (hμ : μ ∈ rootLattice P) : μ ∈ P.rootSpan R :=
  (AddSubgroup.closure_le (K := (P.rootSpan R).toAddSubgroup)).2
    (fun _ hx => Submodule.subset_span hx) hμ

omit [CharZero k] [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] [P.IsReduced] in
variable (P) in
/-- The inclusion of the root lattice in the $\mathbb{Z}$-span of the roots. -/
def latticeToSpan : rootLattice P →+ P.rootSpan ℤ where
  toFun x := ⟨x, mem_rootSpan_of_mem_rootLattice x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
variable (P) in
/-- The pairing $\mu \mapsto \langle \mu, \alpha_i^\vee \rangle$ of the root lattice with a coroot, with values in $\mathbb{Z}$. -/
def corootPairing (i : ι) : rootLattice P →+ ℤ :=
  (P.coroot'In ℤ i).toAddMonoidHom.comp (latticeToSpan P)

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- The integer $\langle \mu, \alpha_i^\vee \rangle$ maps to the pairing in $k$. -/
theorem algebraMap_corootPairing (i : ι) (μ : rootLattice P) :
    ((corootPairing P i μ : ℤ) : k) = P.coroot' i μ := by
  rw [← eq_intCast (algebraMap ℤ k)]
  exact algebraMap_coroot'In_apply P ℤ i (latticeToSpan P μ)

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- The pairing of the root $\alpha_j$ with $\alpha_i^\vee$ is $\langle \alpha_j, \alpha_i^\vee \rangle$. -/
@[simp]
theorem corootPairing_latticeRoot (i j : ι) :
    corootPairing P i (latticeRoot P j) = P.pairingIn ℤ j i := rfl

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- The root lattice is stable under the simple reflections. -/
theorem reflection_mem_rootLattice (i : ι) {μ : M} (hμ : μ ∈ rootLattice P) :
    P.reflection i μ ∈ rootLattice P := by
  have h : P.reflection i μ = μ - corootPairing P i (⟨μ, hμ⟩ : rootLattice P) • P.root i := by
    rw [reflection_apply, ← Int.cast_smul_eq_zsmul k, algebraMap_corootPairing]
  rw [h]
  exact sub_mem hμ (zsmul_mem (latticeRoot P i).2 _)

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- For a character $\chi$ of the root lattice, $\chi(\mu) - \chi(s_i \mu) = \langle \mu, \alpha_i^\vee \rangle \chi(\alpha_i)$, written additively. -/
theorem char_sub_reflection (χ : rootLattice P →+ Additive kˣ) (i : ι) {μ : M}
    (hμ : μ ∈ rootLattice P) :
    χ (⟨μ, hμ⟩ : rootLattice P) - χ (⟨P.reflection i μ, reflection_mem_rootLattice i hμ⟩ : rootLattice P) =
      corootPairing P i (⟨μ, hμ⟩ : rootLattice P) • χ (latticeRoot P i) := by
  rw [← map_sub, ← map_zsmul]
  congr 1
  refine Subtype.ext ?_
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_zsmul]
  rw [reflection_apply, ← Int.cast_smul_eq_zsmul k, algebraMap_corootPairing]
  simp [latticeRoot]

omit [P.IsReduced] in
variable (P) in
/-- The cocharacter of the coroot $\alpha_i^\vee$: for $c \in k^\times$ the character $\mu \mapsto c^{\langle \mu, \alpha_i^\vee \rangle}$ of the root lattice, that is, the point $\alpha_i^\vee(c)$ of the adjoint torus. -/
def corootChar (i : ι) (c : kˣ) : rootLattice P →+ Additive kˣ :=
  (zmultiplesHom (Additive kˣ) (Additive.ofMul c)).comp (corootPairing P i)

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- The formula $\alpha_i^\vee(c)(\mu) = c^{\langle \mu, \alpha_i^\vee \rangle}$. -/
@[simp]
theorem toMul_corootChar_apply (i : ι) (c : kˣ) (μ : rootLattice P) :
    (corootChar P i c μ).toMul = c ^ corootPairing P i μ := by
  simp [corootChar, toMul_zsmul]

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- The cocharacter of a coroot is a homomorphism: $\alpha_i^\vee(c d) = \alpha_i^\vee(c) \alpha_i^\vee(d)$. -/
theorem corootChar_mul (i : ι) (c d : kˣ) :
    corootChar P i (c * d) = corootChar P i c + corootChar P i d := by
  ext μ
  simp [corootChar, ofMul_mul, mul_zpow]

omit [P.IsReduced] in
variable (P) in
/-- A character $\chi$ of the root lattice with $\chi(\alpha_i) = c$ for a simple root $\alpha_i$: the coordinate of $\alpha_i$ in the basis of simple roots, composed with $n \mapsto c^n$. -/
def simpleChar (i : b.support) (c : kˣ) : rootLattice P →+ Additive kˣ :=
  (zmultiplesHom (Additive kˣ) (Additive.ofMul c)).comp
    ((b.toWeightBasisInt.coord i).toAddMonoidHom.comp (latticeToSpan P))

omit [Fintype ι] [DecidableEq ι] [P.IsCrystallographic] [P.IsReduced] in
/-- The formula $\chi(\alpha_i) = c$ for the character `simpleChar`. -/
theorem toMul_simpleChar_apply_self (i : b.support) (c : kˣ) :
    (simpleChar P b i c (latticeRoot P i)).toMul = c := by
  have h : latticeToSpan P (latticeRoot P i) = b.toWeightBasisInt i :=
    Subtype.ext (b.coe_toWeightBasisInt_apply i).symm
  simp [simpleChar, h]

omit [P.IsReduced] in
/-- The torus acts on the weight space of $\mu$ through the character: $h(\chi) x = \chi(\mu) x$ for $\mu$ in the root lattice. -/
theorem torusElement_apply_of_mem_weightSpace (χ : rootLattice P →+ Additive kˣ) {μ : M}
    (hμ : μ ∈ rootLattice P) {x : lieAlgebra b} (hx : x ∈ weightSpace b μ) :
    torusElement b χ x = ((χ (⟨μ, hμ⟩ : rootLattice P)).toMul : k) • x := by
  let w : b.support ⊕ ι → rootLattice P := Sum.elim 0 (latticeRoot P)
  have hd (ψ : rootLattice P →+ Additive kˣ) (a : b.support ⊕ ι) :
      torusDiag b ψ a = ((ψ (w a)).toMul : k) := by
    rcases a with a | a <;> simp [w]
  have hw (a : b.support ⊕ ι) : (w a : M) = basisWeight b a := by
    rcases a with a | a <;> rfl
  refine Subtype.ext ?_
  rw [coe_torusElement_apply, SetLike.val_smul]
  ext a c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, hd, hd]
  by_cases hac : basisWeight b a - basisWeight b c = μ
  · have hl : w a - w c = ⟨μ, hμ⟩ := Subtype.ext (by rw [AddSubgroup.coe_sub, hw, hw, hac])
    rw [← hl, map_sub, toMul_sub, AddMonoidHom.neg_apply, toMul_neg, Units.val_div_eq_div_val,
      Units.val_inv_eq_inv_val]
    ring
  · rw [apply_eq_zero_of_mem_weightSpace b (mem_rootSpan_of_mem_rootLattice hμ) hx hac]
    simp

omit [P.IsReduced] in
/-- The inverse of $h(\chi)$ is $h(\chi^{-1})$. -/
theorem torusElement_neg (χ : rootLattice P →+ Additive kˣ) :
    torusElement b (-χ) = (torusElement b χ)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by
    rw [← torusElement_add, show χ + -χ = 0 by ext; simp, torusElement_zero])).symm

/-- The torus acts on the root vector $X_\beta$ through the root: $h(\chi) X_\beta = \chi(\beta) X_\beta$. -/
theorem torusElement_apply_rootVector (χ : rootLattice P →+ Additive kˣ) (β : ι) :
    torusElement b χ (rootVector b β) = ((χ (latticeRoot P β)).toMul : k) • rootVector b β :=
  torusElement_apply_of_mem_weightSpace b χ (latticeRoot P β).2 (rootVector_mem_weightSpace b β)

/-- The torus acts on all root subgroups through the roots: $h(\chi) x_\beta(t) h(\chi)^{-1} = x_\beta(\chi(\beta) t)$. -/
theorem torusElement_mul_rootElement_mul_inv (χ : rootLattice P →+ Additive kˣ) (β : ι)
    (t : k) :
    torusElement b χ * rootElement b β t * (torusElement b χ)⁻¹ =
      rootElement b β (t * ((χ (latticeRoot P β)).toMul : k)) := by
  have hn := isNilpotent_ad_lieEquiv_apply (torusElement b χ) (isNilpotent_ad_rootVector b β)
  rw [torusElement_apply_rootVector] at hn
  rw [rootElement, lieEquiv_mul_expAd_mul_inv,
    expAd_congr (torusElement_apply_rootVector b χ β) _ hn,
    expAd_smul _ (isNilpotent_ad_rootVector b β)]
  rfl

/-- The equation $w_{\alpha_i}(-t) = w_{\alpha_i}(t)^{-1}$. -/
theorem weylElement_neg (i : b.support) (t : k) :
    weylElement b i (-t) = (weylElement b i t)⁻¹ := by
  have h : negSimpleRootElement b i t⁻¹ = (negSimpleRootElement b i (-t⁻¹))⁻¹ := by
    rw [← negSimpleRootElement_neg, neg_neg]
  rw [weylElement, weylElement, simpleRootElement_neg, inv_neg, neg_neg, h]
  group

/-- The torus acts on the Weyl elements through the simple roots: $h(\chi) w_{\alpha_i}(t) h(\chi)^{-1} = w_{\alpha_i}(\chi(\alpha_i) t)$. -/
theorem torusElement_mul_weylElement_mul_inv (χ : rootLattice P →+ Additive kˣ) (i : b.support)
    (t : k) :
    torusElement b χ * weylElement b i t * (torusElement b χ)⁻¹ =
      weylElement b i (t * ((χ (latticeRoot P i)).toMul : k)) := by
  set φ := torusElement b χ
  have h : φ * weylElement b i t * φ⁻¹ = (φ * simpleRootElement b i t * φ⁻¹) *
      (φ * negSimpleRootElement b i (-t⁻¹) * φ⁻¹) * (φ * simpleRootElement b i t * φ⁻¹) := by
    rw [weylElement]; group
  rw [h, torusElement_mul_simpleRootElement_mul_inv, torusElement_mul_negSimpleRootElement_mul_inv,
    weylElement, Units.val_inv_eq_inv_val, mul_inv, neg_mul]

/-- The element $h_{\alpha_i}(c)$ acts on the weight space of $\mu$ by $c^{\langle \mu, \alpha_i^\vee \rangle}$, for $\mu$ in the root lattice and $c \in k^\times$. -/
theorem corootElement_apply_of_mem_weightSpace (i : b.support) (c : kˣ) {μ : M}
    (hμ : μ ∈ rootLattice P) {x : lieAlgebra b} (hx : x ∈ weightSpace b μ) :
    corootElement b i c x = ((c ^ corootPairing P i (⟨μ, hμ⟩ : rootLattice P) : kˣ) : k) • x := by
  set χ := simpleChar P b i c
  have hcu : (χ (latticeRoot P i)).toMul = c := toMul_simpleChar_apply_self b i c
  have hw : weylElement b i c = torusElement b χ * weylElement b i 1 * (torusElement b χ)⁻¹ := by
    rw [torusElement_mul_weylElement_mul_inv, one_mul, hcu]
  have hs := reflection_mem_rootLattice (i : ι) hμ
  have hy := weylElement_mem_weightSpace b i (neg_ne_zero.2 one_ne_zero) hx
  have key : ((-χ) (⟨_, hs⟩ : rootLattice P)).toMul * (χ (⟨μ, hμ⟩ : rootLattice P)).toMul = c ^ corootPairing P i (⟨μ, hμ⟩ : rootLattice P) := by
    rw [← toMul_add, AddMonoidHom.neg_apply, neg_add_eq_sub, char_sub_reflection, toMul_zsmul,
      hcu]
  have h1 : weylElement b i 1 (weylElement b i (-1) x) = x := by
    rw [weylElement_neg, ← lieAut_mul_apply, mul_inv_cancel, lieAut_one_apply]
  rw [corootElement, hw, ← weylElement_neg, ← torusElement_neg, lieAut_mul_apply,
    lieAut_mul_apply, lieAut_mul_apply, torusElement_apply_of_mem_weightSpace b (-χ) hs hy,
    map_smul, h1, map_smul, torusElement_apply_of_mem_weightSpace b χ hμ hx, smul_smul,
    ← Units.val_mul, key]

/-- The formula $h_{\alpha_i}(c) e_j = c^{\langle \alpha_j, \alpha_i^\vee \rangle} e_j$ for all simple roots $\alpha_j$ and $c \in k^\times$. -/
theorem corootElement_apply_geckE_zpow (i j : b.support) (c : kˣ) :
    corootElement b i c (geckE b j) = ((c ^ P.pairingIn ℤ j i : kˣ) : k) • geckE b j :=
  corootElement_apply_of_mem_weightSpace b i c (latticeRoot P j).2 (geckE_mem_weightSpace b j)

/-- The formula $h_{\alpha_i}(c) f_j = c^{-\langle \alpha_j, \alpha_i^\vee \rangle} f_j$ for all simple roots $\alpha_j$ and $c \in k^\times$. -/
theorem corootElement_apply_geckF_zpow (i j : b.support) (c : kˣ) :
    corootElement b i c (geckF b j) = ((c ^ (-P.pairingIn ℤ j i) : kˣ) : k) • geckF b j := by
  rw [corootElement_apply_of_mem_weightSpace b i c (neg_mem (latticeRoot P j).2)
    (geckF_mem_weightSpace b j)]
  congr 3
  exact (map_neg (corootPairing P (i : ι)) (latticeRoot P j)).trans (by simp)

/-- The element $h_{\alpha_i}(c) = w_{\alpha_i}(c) w_{\alpha_i}(1)^{-1}$ is the torus element $h(\chi)$ of the character $\chi = \alpha_i^\vee(c) : \mu \mapsto c^{\langle \mu, \alpha_i^\vee \rangle}$. -/
theorem corootElement_eq_torusElement (i : b.support) (c : kˣ) :
    corootElement b i c = torusElement b (corootChar P i c) := by
  have key {μ : M} (hμ : μ ∈ rootLattice P) {x : lieAlgebra b} (hx : x ∈ weightSpace b μ) :
      corootElement b i c x = torusElement b (corootChar P i c) x := by
    rw [corootElement_apply_of_mem_weightSpace b i c hμ hx,
      torusElement_apply_of_mem_weightSpace b _ hμ hx, toMul_corootChar_apply]
  exact lieEquiv_ext_geck b (fun j => key (latticeRoot P j).2 (geckE_mem_weightSpace b j))
    (fun j => key (neg_mem (latticeRoot P j).2) (geckF_mem_weightSpace b j))
    (fun j => key (zero_mem _) (geckH_mem_weightSpace b j))

/-- The map $c \mapsto h_{\alpha_i}(c)$ is a homomorphism: $h_{\alpha_i}(c d) = h_{\alpha_i}(c) h_{\alpha_i}(d)$ for $c, d \in k^\times$. -/
theorem corootElement_mul_units (i : b.support) (c d : kˣ) :
    corootElement b i ((c * d : kˣ) : k) = corootElement b i c * corootElement b i d := by
  rw [corootElement_eq_torusElement, corootElement_eq_torusElement, corootElement_eq_torusElement,
    corootChar_mul, torusElement_add]

/-- The bracket $[X_\alpha, X_\beta]$ is in the weight space of $\alpha + \beta$. -/
theorem lie_rootVector_mem_weightSpace (α β : ι) :
    ⁅rootVector b α, rootVector b β⁆ ∈ weightSpace b (P.root α + P.root β) :=
  lie_mem_weightSpace b (rootVector_mem_weightSpace b α) (rootVector_mem_weightSpace b β)

/-- If the weight space of $\alpha + \beta$ is zero, then $x_\alpha(s)$ and $x_\beta(t)$ commute. -/
theorem commute_rootElement_of_weightSpace_eq_bot {α β : ι}
    (h : weightSpace b (P.root α + P.root β) = ⊥) (s t : k) :
    Commute (rootElement b α s) (rootElement b β t) := by
  have hm := lie_rootVector_mem_weightSpace b α β
  rw [h, Submodule.mem_bot] at hm
  exact commute_expAd_of_lie_eq_zero _ _ hm s t

end Torus

end Geck

section AdjointDatum

variable {ι k M N : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] (P : RootPairing ι k M N) [Finite ι] [P.IsCrystallographic]

/-- The coroots $\alpha^\vee$ as integer valued linear forms on the root lattice are injective in $\alpha$. -/
theorem coroot'In_injective : Function.Injective (P.coroot'In ℤ) := by
  intro i j hij
  have h1 := congr($hij (P.rootSpanMem ℤ i))
  have h2 := congr($hij (P.rootSpanMem ℤ j))
  simp only [coroot'In_rootSpanMem_eq_pairingIn, P.pairingIn_same] at h1 h2
  exact (P.pairingIn_two_two_iff ℤ i j).1 ⟨h1.symm, h2⟩

/-- The root datum of the split adjoint group of the root system $P$. The character lattice is the root lattice $X = \mathbb{Z}\Phi$, the cocharacter lattice is the coweight lattice $\mathrm{Hom}(X, \mathbb{Z})$, the roots are the roots of $P$ and the coroots are the linear forms $\langle \cdot, \alpha^\vee \rangle$. -/
def adjointRootDatum : RootDatum ι (P.rootSpan ℤ) (Module.Dual ℤ (P.rootSpan ℤ)) where
  toLinearMap := Module.Dual.eval ℤ (P.rootSpan ℤ)
  isPerfPair_toLinearMap := by
    have := Module.IsTorsionFree.trans_faithfulSMul ℤ k M
    infer_instance
  root := ⟨P.rootSpanMem ℤ, fun i j h => P.root.injective congr(Subtype.val $h)⟩
  coroot := ⟨P.coroot'In ℤ, coroot'In_injective P⟩
  root_coroot_two i := by
    change P.coroot'In ℤ i (P.rootSpanMem ℤ i) = 2
    simp
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    change P.rootSpanMem ℤ j - P.coroot'In ℤ i (P.rootSpanMem ℤ j) • P.rootSpanMem ℤ i =
      P.rootSpanMem ℤ (P.reflectionPerm i j)
    refine Subtype.ext ?_
    simp only [coroot'In_rootSpanMem_eq_pairingIn, Submodule.coe_sub, Submodule.coe_smul,
      root_reflectionPerm, reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
    rw [algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]
  reflectionPerm_coroot i j := by
    change P.coroot'In ℤ j - P.coroot'In ℤ j (P.rootSpanMem ℤ i) • P.coroot'In ℤ i =
      P.coroot'In ℤ (P.reflectionPerm i j)
    refine LinearMap.ext fun x => (FaithfulSMul.algebraMap_injective ℤ k) ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_mul,
      algebraMap_coroot'In_apply, coroot'In_rootSpanMem_eq_pairingIn, P.algebraMap_pairingIn,
      coroot_reflectionPerm, coreflection_apply_coroot, coroot', LinearMap.flip_apply, map_sub,
      map_smul, smul_eq_mul, LinearMap.sub_apply, LinearMap.smul_apply]

/-- The roots of the adjoint root datum are the roots of $P$. -/
@[simp]
theorem adjointRootDatum_root (i : ι) : ((adjointRootDatum P).root i : M) = P.root i := rfl

/-- The pairing of the adjoint root datum is the pairing of $P$ with values in $\mathbb{Z}$. -/
@[simp]
theorem adjointRootDatum_pairing (i j : ι) :
    (adjointRootDatum P).pairing i j = P.pairingIn ℤ i j := rfl

/-- The roots of the adjoint root datum span its character lattice. So the root datum is adjoint. -/
theorem adjointRootDatum_rootSpan : (adjointRootDatum P).rootSpan ℤ = ⊤ := by
  have h : Set.range (adjointRootDatum P).root =
      (Subtype.val : P.rootSpan ℤ → M) ⁻¹' Set.range P.root := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  change Submodule.span ℤ (Set.range (adjointRootDatum P).root) = ⊤
  rw [h]
  exact Submodule.span_span_coe_preimage

/-- The coroots of the dual of the adjoint root datum span its cocharacter lattice. So the dual root datum is simply connected. -/
theorem dual_adjointRootDatum_corootSpan :
    (RootDatum.dual (adjointRootDatum P)).corootSpan ℤ = ⊤ :=
  adjointRootDatum_rootSpan P

variable {P}

/-- The base of the adjoint root datum with the same simple roots as the base $b$ of $P$. -/
def adjointBase (b : P.Base) : (adjointRootDatum P).Base :=
  Base.mkOfPairwiseLEZero (adjointRootDatum P) (s := b.support) b.linearIndependentInt
    (fun _ hi _ hj hij => by
      simpa [RootPairing.pairingIn, adjointRootDatum_pairing] using
        b.pairingIn_le_zero_of_ne hij hi hj)
    (fun i => by
      classical
      obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun ℤ).1
        (b.coroot_mem_span_int i)
      refine (Submodule.mem_span_image_finset_iff_exists_fun ℤ).2 ⟨c, ?_⟩
      refine LinearMap.ext fun x => (FaithfulSMul.algebraMap_injective ℤ k) ?_
      change algebraMap ℤ k ((∑ j, c j • P.coroot'In ℤ j) x) = algebraMap ℤ k (P.coroot'In ℤ i x)
      rw [algebraMap_coroot'In_apply, coroot', ← hc, LinearMap.sum_apply, map_sum, map_sum,
        LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.smul_apply, map_zsmul, map_zsmul, LinearMap.smul_apply,
        algebraMap_coroot'In_apply])
    (fun i => by
      classical
      obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun ℤ).1
        (b.root_mem_span_int i)
      refine (Submodule.mem_span_image_finset_iff_exists_fun ℤ).2 ⟨c, Subtype.ext ?_⟩
      rw [adjointRootDatum_root, ← hc, Submodule.coe_sum]
      rfl)

/-- The simple roots of the adjoint base are the simple roots of $b$. -/
@[simp]
theorem adjointBase_support (b : P.Base) : (adjointBase b).support = b.support := rfl

/-- The L-group datum of the split adjoint group of $(P, b)$ is the split datum of the dual root datum with the dual base. The dual root datum is simply connected by `dual_adjointRootDatum_corootSpan`. -/
theorem lgroupDatum_split_adjoint (Γ : Type*) [Group Γ] (b : P.Base) :
    (QuasiSplitDatum.split (Γ := Γ) (adjointRootDatum P) (adjointBase b)).lgroupDatum =
      QuasiSplitDatum.split (RootDatum.dual (adjointRootDatum P)) (adjointBase b).flip :=
  QuasiSplitDatum.dual_split _ _

end AdjointDatum

end Langlands.Groups.ChevalleyRoots
