/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Groups.ChevalleyRoots
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Split tori, root subgroups, split reductive groups and L-groups of tori

This file defines the split torus $T(R) = \mathrm{Hom}(X, R^\times)$ of a lattice $X$, with its characters and cocharacters. It gives two concrete split groups that the torus and the root subgroups generate: the adjoint Chevalley group of a crystallographic reduced root system over a field of characteristic zero, and $\mathrm{GL}_n$. In both cases it proves that the torus normalizes each root subgroup $U_\alpha \cong (k, +)$ by the formula $h \, x_\alpha(t) \, h^{-1} = x_\alpha(\alpha(h) t)$. Then it defines the L-group $\hat T(R) \rtimes \Gamma$ of the maximal torus of a quasi-split datum, with the semidirect product of Mathlib, and it proves that for a split datum it is the direct product.

## Main definitions

* `Langlands.Groups.SplitTorus`: the split torus $T(R) = \mathrm{Hom}(X, R^\times)$.
* `Langlands.Groups.SplitTorus.character`, `Langlands.Groups.SplitTorus.cocharacter`: the characters $X$ and the cocharacters $Y$ of $T(R)$.
* `Langlands.Groups.RootDatum.rootCharacter`, `Langlands.Groups.RootDatum.corootCocharacter`: the characters of the roots and the cocharacters of the coroots of a root datum.
* `Langlands.Groups.SplitAdjoint.torusHom`: the adjoint torus $\mathrm{Hom}(Q, k^\times)$ as automorphisms of the Chevalley Lie algebra.
* `Langlands.Groups.SplitAdjoint.rootSubgroup`, `Langlands.Groups.SplitAdjoint.rootSubgroupEquiv`: the root subgroup $U_\beta$ and the isomorphism $(k, +) \cong U_\beta$.
* `Langlands.Groups.SplitAdjoint.AdjointChevalleyGroup`: the adjoint Chevalley group $G(k)$ that the torus and the root elements generate.
* `Langlands.Groups.SplitGL.torusHom`, `Langlands.Groups.SplitGL.rootElement`: the diagonal torus and the root elements $1 + t E_{ij}$ of $\mathrm{GL}_n(R)$, for the root datum `Langlands.Groups.RootDatum.gl`.
* `Langlands.Groups.SplitTorus.torusAction`: the action of $\mathrm{Aut}(Y)$ on $\mathrm{Hom}(Y, R^\times)$.
* `Langlands.Groups.LGroup.dualTorusAction`, `Langlands.Groups.LGroup.TorusLGroup`: the action of $\Gamma$ on the dual torus and the L-group $\hat T(R) \rtimes \Gamma$ of the torus.
* `Langlands.Groups.LGroup.GLLGroup`: the L-group $\mathrm{GL}_n(R) \rtimes \Gamma$ of split $\mathrm{GL}_n$.

## Main results

* `Langlands.Groups.SplitAdjoint.torusHom_mul_rootElement_mul_inv`: $h \, x_\beta(s) \, h^{-1} = x_\beta(\beta(h) s)$ in the adjoint Chevalley group.
* `Langlands.Groups.SplitAdjoint.torusHom_corootCocharacter`: the coroot cocharacters give the elements `corootElement`, so the torus of this file contains the elements `torusElement` of `Langlands.Groups.Chevalley`.
* `Langlands.Groups.SplitAdjoint.torusHom_injective`, `Langlands.Groups.SplitAdjoint.rootHom_injective`: the torus and the maps $t \mapsto x_\beta(t)$ are injective.
* `Langlands.Groups.SplitAdjoint.map_conj_rootSubgroup`: the torus normalizes each root subgroup.
* `Langlands.Groups.SplitAdjoint.mem_adjointChevalleyGroup_iff`: $G(k) = T(k) E(k)$, with $E(k)$ the elementary subgroup.
* `Langlands.Groups.SplitAdjoint.elementary_normal`: $E(k)$ is normal in $G(k)$.
* `Langlands.Groups.SplitGL.torusHom_mul_rootElement_mul_inv`: $h \, x_\alpha(s) \, h^{-1} = x_\alpha(\alpha(h) s)$ in $\mathrm{GL}_n(R)$, with $\alpha$ the root character of `gl n`.
* `Langlands.Groups.SplitGL.rootElement_commutator`: $[x_{ij}(s), x_{jl}(t)] = x_{il}(st)$.
* `Langlands.Groups.SplitGL.closure_torus_rootElement`: over a field the torus and the root elements generate $\mathrm{GL}_n(k)$.
* `Langlands.Groups.LGroup.dualTorusAction_eq_one`, `Langlands.Groups.LGroup.torusLGroupEquivProd`: for a split datum the action on the dual torus is trivial and the L-group of the torus is $\hat T(R) \times \Gamma$.
* `Langlands.Groups.LGroup.torusLGroupToGL_injective`: the L-group of the diagonal torus of split $\mathrm{GL}_n$ embeds in the L-group of $\mathrm{GL}_n$.

## Implementation notes

The adjoint group is a group of automorphisms of the Chevalley Lie algebra of `Langlands.Groups.Chevalley`. Its torus is $\mathrm{Hom}(Q, k^\times)$ with $Q$ the root lattice, which is the character lattice of the adjoint root datum `Langlands.Groups.ChevalleyRoots.adjointRootDatum`. The group is the closure of the torus and the root elements. This file does not prove that it is the group of $k$-points of a group scheme.

For a general reductive root datum, this file uses $\mathrm{GL}_n$ as the honest construction. The torus is $\mathrm{Hom}(\mathbb{Z}^n, R^\times)$, the characters and the roots are those of `Langlands.Groups.RootDatum.gl`, and the conjugation formula uses the root character of `gl n`. A Steinberg presentation for a general root datum needs the structure constants of the commutator relations, and they are not available in the project, so this file does not construct $G(k)$ for a general root datum.

The L-group uses the coefficient ring $R$. For the L-group of the theory, take $R = \mathbb{C}$ and $\Gamma$ the Weil group or the Galois group. The group $\Gamma$ acts on $Y$ through the dual datum `Langlands.Groups.QuasiSplitDatum.dual`, and on $\mathrm{Hom}(Y, R^\times)$ by $t \mapsto t \circ \gamma^{-1}$. This file gives the L-group of a general quasi-split group only for the torus. For $\mathrm{GL}_n$ it gives the split L-group, because the dual group $\mathrm{GL}_n$ is in this file.

## References

* R. Steinberg, Lectures on Chevalley groups, chapter 3.
* A. Borel, Automorphic L-functions, in Automorphic forms, representations and L-functions, Proc. Sympos. Pure Math. 33, part 2, 1979, section 2.
* T. A. Springer, Linear algebraic groups, chapter 7 and chapter 8.
-/

noncomputable section

namespace Langlands.Groups

open Module Function

/-- The split torus $T(R) = \mathrm{Hom}(X, R^\times)$ with the character lattice $X$, as the group of homomorphisms from $X$ to the units of $R$. -/
abbrev SplitTorus (X : Type*) [AddCommGroup X] (R : Type*) [CommRing R] : Type _ :=
  Multiplicative X →* Rˣ

namespace SplitTorus

variable {X Y X' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X']
  {R : Type*} [CommRing R]

variable (R) in
/-- The character $t \mapsto t(x)$ of the torus $T(R)$ for $x \in X$. -/
def character (x : X) : SplitTorus X R →* Rˣ where
  toFun t := t (Multiplicative.ofAdd x)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The value of the character $x$ at $t$ is $t(x)$. -/
@[simp] theorem character_apply (x : X) (t : SplitTorus X R) :
    character R x t = t (Multiplicative.ofAdd x) := rfl

/-- The characters form a group: $(x + x')(t) = x(t) \cdot x'(t)$. -/
theorem character_add (x x' : X) (t : SplitTorus X R) :
    character R (x + x') t = character R x t * character R x' t := by
  simp [← map_mul]

variable (R) in
/-- The cocharacter $c \mapsto (x \mapsto c^{\langle x, y \rangle})$ of the torus $T(R)$ for $y \in Y$ and a pairing $\langle \cdot, \cdot \rangle$ of $X$ and $Y$. -/
def cocharacter (p : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (y : Y) : Rˣ →* SplitTorus X R where
  toFun c :=
    { toFun x := c ^ p x.toAdd y
      map_one' := by simp
      map_mul' x x' := by simp [zpow_add] }
  map_one' := by ext; simp
  map_mul' c d := by ext; simp [mul_zpow]

/-- The character $x$ of the cocharacter $y$ is $c \mapsto c^{\langle x, y \rangle}$. -/
theorem character_cocharacter (p : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (x : X) (y : Y) (c : Rˣ) :
    character R x (cocharacter R p y c) = c ^ p x y := rfl

variable (R) in
/-- The map of tori $T'(R) \to T(R)$ that a homomorphism $X \to X'$ of character lattices gives. -/
def comap (f : X →+ X') : SplitTorus X' R →* SplitTorus X R where
  toFun t := t.comp (AddMonoidHom.toMultiplicative f)
  map_one' := rfl
  map_mul' _ _ := rfl

variable (R) in
/-- The element of $T(R)$ that an additive homomorphism $X \to R^\times$ gives. -/
def lift (f : X →+ Additive Rˣ) : SplitTorus X R := AddMonoidHom.toMultiplicativeLeft f

/-- Two elements of $T(R)$ are equal if they are equal on a family that spans $X$. -/
theorem ext_of_span {ι : Type*} {v : ι → X} (hv : Submodule.span ℤ (Set.range v) = ⊤)
    {t s : SplitTorus X R} (h : ∀ i, t (Multiplicative.ofAdd (v i)) = s (Multiplicative.ofAdd (v i))) :
    t = s := by
  ext1
  have := LinearMap.ext_on_range (f := (MonoidHom.toAdditiveRight t).toIntLinearMap)
    (g := (MonoidHom.toAdditiveRight s).toIntLinearMap) hv (fun i => congrArg Additive.ofMul (h i))
  exact AddMonoidHom.ext fun x => LinearMap.congr_fun this x

end SplitTorus

namespace RootDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootDatum ι X Y)
  (R : Type*) [CommRing R]

/-- The character of the torus $T(R)$ that the root $\alpha_i \in X$ gives. -/
def rootCharacter (i : ι) : SplitTorus X R →* Rˣ := SplitTorus.character R (P.root i)

/-- The cocharacter of the torus $T(R)$ that the coroot $\alpha_i^\vee \in Y$ gives. -/
def corootCocharacter (i : ι) : Rˣ →* SplitTorus X R :=
  SplitTorus.cocharacter R P.toLinearMap (P.coroot i)

/-- The root $\alpha_i$ of the coroot cocharacter $\alpha_j^\vee$ is $c \mapsto c^{\langle \alpha_i, \alpha_j^\vee \rangle}$. -/
theorem rootCharacter_corootCocharacter (i j : ι) (c : Rˣ) :
    rootCharacter P R i (corootCocharacter P R j c) = c ^ P.pairing i j := rfl

end RootDatum

namespace SplitAdjoint

open RootPairing GeckConstruction Chevalley ChevalleyRoots

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k ι M N : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {P : RootPairing ι k M N} [P.IsCrystallographic] (b : P.Base)

variable (P) in
/-- The character of the root lattice that an element of the adjoint torus gives, for use with `torusElement`. -/
def torusChar (t : SplitTorus (P.rootSpan ℤ) k) : rootLattice P →+ Additive kˣ :=
  (MonoidHom.toAdditiveRight t).comp (latticeToSpan P)

/-- The adjoint torus $T(k) = \mathrm{Hom}(Q, k^\times)$, with $Q$ the root lattice, as a group of Lie algebra automorphisms of the Chevalley Lie algebra. The element $t$ acts on the root space of $\beta$ by $\beta(t)$. This is the map $t \mapsto$ `torusElement b (torusChar P t)`. -/
def torusHom : SplitTorus (P.rootSpan ℤ) k →* (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) where
  toFun t := torusElement b (torusChar P t)
  map_one' := torusElement_zero b
  map_mul' t s := torusElement_add b (torusChar P t) (torusChar P s)

omit [DecidableEq ι] in
/-- The character `torusChar P t` at the root $\beta$ is the value of the root character $\beta$ of the adjoint root datum at $t$. -/
theorem torusChar_latticeRoot (t : SplitTorus (P.rootSpan ℤ) k) (β : ι) :
    (torusChar P t (latticeRoot P β)).toMul =
      RootDatum.rootCharacter (adjointRootDatum P) k β t := rfl

variable [P.IsReduced]

/-- The image of the coroot cocharacter $\alpha_i^\vee(c)$ of the adjoint root datum is `corootElement b i c`. -/
theorem torusHom_corootCocharacter (i : b.support) (c : kˣ) :
    torusHom b (RootDatum.corootCocharacter (adjointRootDatum P) k i c) = corootElement b i c := by
  rw [corootElement_eq_torusElement]
  rfl

/-- The torus normalizes the root elements: $h \, x_\beta(s) \, h^{-1} = x_\beta(\beta(h) s)$. -/
theorem torusHom_mul_rootElement_mul_inv (t : SplitTorus (P.rootSpan ℤ) k) (β : ι) (s : k) :
    torusHom b t * rootElement b β s * (torusHom b t)⁻¹ =
      rootElement b β ((RootDatum.rootCharacter (adjointRootDatum P) k β t : k) * s) := by
  rw [mul_comm]
  exact torusElement_mul_rootElement_mul_inv b _ β s

/-- The adjoint torus acts faithfully on the Lie algebra. -/
theorem torusHom_injective : Injective (torusHom b (P := P)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  refine SplitTorus.ext_of_span (adjointRootDatum_rootSpan P) fun β => ?_
  have h := torusElement_apply_rootVector b (torusChar P t) β
  change torusHom b t (rootVector b β) = _ at h
  rw [ht, lieAut_one_apply] at h
  have h1 : ((torusChar P t (latticeRoot P β)).toMul : k) = 1 := by
    have h2 : (((torusChar P t (latticeRoot P β)).toMul : k) - 1) • rootVector b β = 0 := by
      rw [sub_smul, ← h, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 (rootVector_ne_zero b β)
  exact Units.val_eq_one.1 h1


/-- The homomorphism $t \mapsto x_\beta(t) = \exp(t \operatorname{ad} e_\beta)$ from $(k, +)$. -/
def rootHom (β : ι) : Multiplicative k →* (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) :=
  expAdHom (rootVector b β) (isNilpotent_ad_rootVector b β)

/-- The value of `rootHom b β` at $t$ is $x_\beta(t)$. -/
@[simp] theorem rootHom_apply (β : ι) (t : Multiplicative k) :
    rootHom b β t = rootElement b β t.toAdd := rfl

/-- The root element $x_\beta(t)$ is $1$ if and only if $t = 0$. -/
theorem rootElement_eq_one_iff (β : ι) (t : k) : rootElement b β t = 1 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ rootElement_zero b β⟩
  set w := weylWord b (rootWord b β).1
  have h1 : simpleRootElement b (rootWord b β).2 t = 1 := by
    have h2 := congrArg (fun g => w⁻¹ * g * w) h
    rw [rootElement_eq_conj] at h2
    simpa [w, mul_assoc] using h2
  have h3 := congrArg (fun g => g (geckH b (rootWord b β).2)) h1
  simp only [simpleRootElement_apply_h, lieAut_one_apply, sub_eq_self] at h3
  rcases smul_eq_zero.1 h3 with h4 | h4
  · simpa using h4
  · exact absurd h4 (isSl2Triple_geck b _).e_ne_zero

/-- The map $t \mapsto x_\beta(t)$ is injective. -/
theorem rootHom_injective (β : ι) : Injective (rootHom b β) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  exact (rootElement_eq_one_iff b β t.toAdd).1 ht

/-- The root subgroup $U_\beta = \{x_\beta(t)\}$. -/
def rootSubgroup (β : ι) : Subgroup (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) := (rootHom b β).range

/-- The root subgroup $U_\beta = \{x_\beta(t)\}$. -/
def rootSubgroupEquiv (β : ι) : Multiplicative k ≃* rootSubgroup b β :=
  MonoidHom.ofInjective (rootHom_injective b β)

/-- The isomorphism `rootSubgroupEquiv b β` sends $t$ to $x_\beta(t)$. -/
@[simp] theorem coe_rootSubgroupEquiv (β : ι) (t : Multiplicative k) :
    (rootSubgroupEquiv b β t : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) = rootElement b β t.toAdd := rfl

/-- The root element $x_\beta(t)$ is in $U_\beta$. -/
theorem rootElement_mem_rootSubgroup (β : ι) (t : k) : rootElement b β t ∈ rootSubgroup b β :=
  ⟨Multiplicative.ofAdd t, rfl⟩

/-- Through the isomorphism $(k, +) \cong U_\beta$, conjugation by $h$ is multiplication by $\beta(h)$. -/
theorem torusHom_conj_rootSubgroupEquiv (t : SplitTorus (P.rootSpan ℤ) k) (β : ι)
    (s : Multiplicative k) :
    torusHom b t * (rootSubgroupEquiv b β s : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) * (torusHom b t)⁻¹ =
      rootSubgroupEquiv b β (Multiplicative.ofAdd
        (((RootDatum.rootCharacter (adjointRootDatum P) k β t : kˣ) : k) * s.toAdd)) :=
  torusHom_mul_rootElement_mul_inv b t β s.toAdd

/-- The torus normalizes the root subgroup $U_\beta$. -/
theorem torusHom_conj_mem_rootSubgroup (t : SplitTorus (P.rootSpan ℤ) k) (β : ι)
    {g : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b} (hg : g ∈ rootSubgroup b β) :
    torusHom b t * g * (torusHom b t)⁻¹ ∈ rootSubgroup b β := by
  obtain ⟨s, rfl⟩ := hg
  rw [rootHom_apply, torusHom_mul_rootElement_mul_inv]
  exact rootElement_mem_rootSubgroup b β _

/-- Conjugation by an element of the torus maps $U_\beta$ onto $U_\beta$. -/
theorem map_conj_rootSubgroup (t : SplitTorus (P.rootSpan ℤ) k) (β : ι) :
    (rootSubgroup b β).map (MulAut.conj (torusHom b t)).toMonoidHom = rootSubgroup b β := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact torusHom_conj_mem_rootSubgroup b t β hg
  · refine ⟨(torusHom b t)⁻¹ * g * (torusHom b t)⁻¹⁻¹, ?_, ?_⟩
    · rw [← map_inv]
      exact torusHom_conj_mem_rootSubgroup b t⁻¹ β hg
    · simp [mul_assoc]

/-- The adjoint Chevalley group $G(k)$: the group of Lie algebra automorphisms that the adjoint torus and the root elements generate. -/
def AdjointChevalleyGroup : Subgroup (lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b) :=
  Subgroup.closure (Set.range (torusHom b) ∪ Set.range fun p : ι × k => rootElement b p.1 p.2)

/-- The adjoint torus is in $G(k)$. -/
theorem torusHom_mem (t : SplitTorus (P.rootSpan ℤ) k) : torusHom b t ∈ AdjointChevalleyGroup b :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

/-- The root subgroups are in $G(k)$. -/
theorem rootSubgroup_le (β : ι) : rootSubgroup b β ≤ AdjointChevalleyGroup b := by
  rintro _ ⟨t, rfl⟩
  exact Subgroup.subset_closure (Or.inr ⟨(β, t.toAdd), rfl⟩)

/-- The elementary subgroup $E(k)$ is in $G(k)$. -/
theorem elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup :
    ElementaryAdjointChevalleyGroup b ≤ AdjointChevalleyGroup b := by
  rw [← closure_rootElement, AdjointChevalleyGroup]
  exact Subgroup.closure_mono Set.subset_union_right

/-- The torus normalizes the elementary subgroup $E(k)$. -/
theorem torusHom_conj_mem_elementary (t : SplitTorus (P.rootSpan ℤ) k)
    {g : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b} (hg : g ∈ ElementaryAdjointChevalleyGroup b) :
    torusHom b t * g * (torusHom b t)⁻¹ ∈ ElementaryAdjointChevalleyGroup b :=
  torusElement_conj_mem b _ hg

/-- Each element of $G(k)$ is $h e$ with $h$ in the torus and $e \in E(k)$, so $G(k) = T(k) E(k)$. -/
theorem mem_adjointChevalleyGroup_iff {g : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b} :
    g ∈ AdjointChevalleyGroup b ↔
      ∃ t : SplitTorus (P.rootSpan ℤ) k, ∃ e ∈ ElementaryAdjointChevalleyGroup b, g = torusHom b t * e := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨t, rfl⟩ | ⟨⟨β, s⟩, rfl⟩
      · exact ⟨t, 1, one_mem _, (mul_one _).symm⟩
      · exact ⟨1, _, rootElement_mem b β s, by simp⟩
    | one => exact ⟨1, 1, one_mem _, by simp⟩
    | mul g g' _ _ ih ih' =>
      obtain ⟨t, e, he, rfl⟩ := ih
      obtain ⟨t', e', he', rfl⟩ := ih'
      refine ⟨t * t', (torusHom b t')⁻¹ * e * (torusHom b t')⁻¹⁻¹ * e', ?_, ?_⟩
      · refine mul_mem ?_ he'
        rw [← map_inv]
        exact torusHom_conj_mem_elementary b _ he
      · simp [mul_assoc]
    | inv g _ ih =>
      obtain ⟨t, e, he, rfl⟩ := ih
      refine ⟨t⁻¹, torusHom b t * e⁻¹ * (torusHom b t)⁻¹, ?_, ?_⟩
      · exact torusHom_conj_mem_elementary b _ (inv_mem he)
      · rw [show torusHom b t⁻¹ = (torusHom b t)⁻¹ from map_inv (torusHom b) t]
        group
  · rintro ⟨t, e, he, rfl⟩
    exact mul_mem (torusHom_mem b t) (elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b he)

/-- The group $G(k)$ is the join of the torus and the elementary subgroup. -/
theorem adjointChevalleyGroup_eq_sup :
    AdjointChevalleyGroup b = (torusHom b).range ⊔ ElementaryAdjointChevalleyGroup b := by
  refine le_antisymm (fun g hg => ?_) (sup_le ?_ (elementaryAdjointChevalleyGroup_le_adjointChevalleyGroup b))
  · obtain ⟨t, e, he, rfl⟩ := (mem_adjointChevalleyGroup_iff b).1 hg
    exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right he)
  · rintro _ ⟨t, rfl⟩
    exact torusHom_mem b t

/-- The group $G(k)$ normalizes the elementary subgroup $E(k)$. -/
theorem conj_mem_elementary {g x : lieAlgebra b ≃ₗ⁅k⁆ lieAlgebra b}
    (hg : g ∈ AdjointChevalleyGroup b) (hx : x ∈ ElementaryAdjointChevalleyGroup b) :
    g * x * g⁻¹ ∈ ElementaryAdjointChevalleyGroup b := by
  obtain ⟨t, e, he, rfl⟩ := (mem_adjointChevalleyGroup_iff b).1 hg
  have h : torusHom b t * e * x * (torusHom b t * e)⁻¹ =
      torusHom b t * (e * x * e⁻¹) * (torusHom b t)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [h]
  exact torusHom_conj_mem_elementary b t (mul_mem (mul_mem he hx) (inv_mem he))

/-- The elementary subgroup $E(k)$ is a normal subgroup of $G(k)$. -/
theorem elementary_normal :
    ((ElementaryAdjointChevalleyGroup b).subgroupOf (AdjointChevalleyGroup b)).Normal :=
  ⟨fun _ hx g => Subgroup.mem_subgroupOf.2 (conj_mem_elementary b g.2 (Subgroup.mem_subgroupOf.1 hx))⟩

end SplitAdjoint

namespace SplitGL

open Matrix RootDatum

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The diagonal entry $t_i = t(e_i)$ of an element of the torus of $\mathrm{GL}_n$, with $e_i$ the standard basis vector of $\mathbb{Z}^n$. -/
def torusEntry (t : SplitTorus (Fin n → ℤ) R) (i : Fin n) : Rˣ :=
  t (Multiplicative.ofAdd (Pi.single i 1))

/-- The element $x \mapsto \prod_i d_i^{x_i}$ of the torus of $\mathrm{GL}_n$ with the diagonal entries $d$. -/
def ofUnits (d : Fin n → Rˣ) : SplitTorus (Fin n → ℤ) R where
  toFun x := ∏ i, d i ^ x.toAdd i
  map_one' := by simp
  map_mul' x y := by simp [_root_.zpow_add, Finset.prod_mul_distrib]

/-- The diagonal entries of `ofUnits d` are $d$. -/
theorem torusEntry_ofUnits (d : Fin n → Rˣ) (i : Fin n) : torusEntry (ofUnits d) i = d i := by
  simp [torusEntry, ofUnits, Pi.single_apply]

/-- An element of the torus of $\mathrm{GL}_n$ is determined by its diagonal entries. -/
theorem ofUnits_torusEntry (t : SplitTorus (Fin n → ℤ) R) : ofUnits (torusEntry t) = t := by
  refine SplitTorus.ext_of_span (Pi.basisFun ℤ (Fin n)).span_eq fun i => ?_
  rw [Pi.basisFun_apply]
  exact torusEntry_ofUnits _ i

variable (n R) in
/-- The torus $\mathrm{Hom}(\mathbb{Z}^n, R^\times)$ of $\mathrm{GL}_n$ is isomorphic to $(R^\times)^n$. -/
def torusEquiv : SplitTorus (Fin n → ℤ) R ≃* (Fin n → Rˣ) where
  toFun := torusEntry
  invFun := ofUnits
  left_inv := ofUnits_torusEntry
  right_inv d := funext (torusEntry_ofUnits d)
  map_mul' _ _ := rfl

/-- The root character $e_i - e_j$ of `gl n` is $t \mapsto t_i t_j^{-1}$. -/
theorem rootCharacter_gl (p : glIndex n) (t : SplitTorus (Fin n → ℤ) R) :
    rootCharacter (gl n) R p t = torusEntry t p.1.1 * (torusEntry t p.1.2)⁻¹ := by
  rw [rootCharacter, SplitTorus.character_apply, gl_root, ofAdd_sub, map_div, div_eq_mul_inv]
  rfl

/-- The diagonal entries of the coroot cocharacter $e_i - e_j$ of `gl n` at $c$ are $c^{(e_i - e_j)_m}$. -/
theorem torusEntry_corootCocharacter (p : glIndex n) (c : Rˣ) (m : Fin n) :
    torusEntry (corootCocharacter (gl n) R p c) m = c ^ glRoot p.1.1 p.1.2 m := by
  change c ^ (Pi.single m 1 ⬝ᵥ glRoot p.1.1 p.1.2) = _
  rw [single_one_dotProduct]

/-- The invertible diagonal matrix with the diagonal entries $d$. -/
def diagUnits (d : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal fun i => (d i : R), diagonal fun i => ((d i)⁻¹ : Rˣ), by simp, by simp⟩

variable (n R) in
/-- The embedding of the torus $\mathrm{Hom}(\mathbb{Z}^n, R^\times)$ as the diagonal matrices in $\mathrm{GL}_n(R)$. -/
def torusHom : SplitTorus (Fin n → ℤ) R →* GL (Fin n) R where
  toFun t := diagUnits (torusEntry t)
  map_one' := Units.ext <| by simp [diagUnits, torusEntry]
  map_mul' t s := Units.ext <| by simp [diagUnits, torusEntry]

/-- The matrix of `torusHom n R t` is the diagonal matrix with the entries $t_i$. -/
theorem coe_torusHom (t : SplitTorus (Fin n → ℤ) R) :
    (torusHom n R t : Matrix (Fin n) (Fin n) R) = diagonal fun i => (torusEntry t i : R) := rfl

/-- The diagonal embedding of the torus is injective. -/
theorem torusHom_injective : Injective (torusHom n R) := by
  intro t s h
  rw [← ofUnits_torusEntry t, ← ofUnits_torusEntry s]
  congr 1
  funext i
  have := congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i i) h
  exact Units.ext (by simpa [coe_torusHom] using this)

/-- The root element $x_{ij}(t) = 1 + t E_{ij}$ of $\mathrm{GL}_n(R)$ for the root $e_i - e_j$ of `gl n`. -/
def rootElement (p : glIndex n) (t : R) : GL (Fin n) R :=
  ⟨transvection p.1.1 p.1.2 t, transvection p.1.1 p.1.2 (-t),
    by rw [transvection_mul_transvection_same _ _ p.2]; simp,
    by rw [transvection_mul_transvection_same _ _ p.2]; simp⟩

/-- The matrix of $x_{ij}(t)$ is the transvection $1 + t E_{ij}$. -/
theorem coe_rootElement (p : glIndex n) (t : R) :
    (rootElement p t : Matrix (Fin n) (Fin n) R) = transvection p.1.1 p.1.2 t := rfl

/-- The homomorphism $t \mapsto x_{ij}(t)$ from $(R, +)$ to $\mathrm{GL}_n(R)$. -/
def rootHom (p : glIndex n) : Multiplicative R →* GL (Fin n) R where
  toFun t := rootElement p t.toAdd
  map_one' := Units.ext <| by simp [coe_rootElement]
  map_mul' s t := Units.ext <| by
    simp [coe_rootElement, transvection_mul_transvection_same _ _ p.2]

/-- The root elements satisfy $x_{ij}(s + t) = x_{ij}(s) x_{ij}(t)$. -/
theorem rootElement_add (p : glIndex n) (s t : R) :
    rootElement p (s + t) = rootElement p s * rootElement p t :=
  (rootHom p).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- The map $t \mapsto x_{ij}(t)$ is injective. -/
theorem rootHom_injective (p : glIndex n) : Injective (rootHom (R := R) p) := by
  intro s t h
  have := congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) h
  simpa [rootHom, coe_rootElement, transvection, one_apply_ne p.2] using this

/-- The torus normalizes the root elements of $\mathrm{GL}_n$: $h \, x_\alpha(s) \, h^{-1} = x_\alpha(\alpha(h) s)$, with $\alpha$ the root character of `gl n`. -/
theorem torusHom_mul_rootElement_mul_inv (t : SplitTorus (Fin n → ℤ) R) (p : glIndex n) (s : R) :
    torusHom n R t * rootElement p s * (torusHom n R t)⁻¹ =
      rootElement p ((rootCharacter (gl n) R p t : R) * s) := by
  refine Units.ext ?_
  rw [rootCharacter_gl]
  ext a c
  have hinv : ((torusHom n R t)⁻¹ : GL (Fin n) R).val =
      diagonal fun i => ((torusEntry t i)⁻¹ : Rˣ).val := rfl
  rw [Units.val_mul, Units.val_mul, hinv, coe_torusHom, coe_rootElement, coe_rootElement,
    mul_diagonal, diagonal_mul]
  simp only [transvection, Matrix.add_apply, one_apply, single_apply]
  by_cases hac : a = c
  · subst hac
    have : ¬ (p.1.1 = a ∧ p.1.2 = a) := fun h => p.2 (h.1.trans h.2.symm)
    simp [this]
  · by_cases h : p.1.1 = a ∧ p.1.2 = c
    · obtain ⟨rfl, rfl⟩ := h
      simp [hac]
      ring
    · simp [hac, h]

/-- The root elements $x_{ij}(s)$ and $x_{kl}(t)$ commute if $j \neq k$ and $l \neq i$. -/
theorem commute_rootElement {p q : glIndex n} (h1 : p.1.2 ≠ q.1.1) (h2 : q.1.2 ≠ p.1.1) (s t : R) :
    Commute (rootElement p s) (rootElement q t) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_rootElement, transvection, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_mul_single_of_ne, h1, h2, ne_eq, not_false_eq_true,
    add_zero]
  abel

/-- The commutator relation $[x_{ij}(s), x_{jl}(t)] = x_{il}(st)$ for distinct $i, j, l$. -/
theorem rootElement_commutator {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t : R) :
    rootElement ⟨(i, j), hij⟩ s * rootElement ⟨(j, l), hjl⟩ t *
        (rootElement ⟨(i, j), hij⟩ s)⁻¹ * (rootElement ⟨(j, l), hjl⟩ t)⁻¹ =
      rootElement ⟨(i, l), hil⟩ (s * t) := by
  have hinv (p : glIndex n) (u : R) : (rootElement p u)⁻¹ = rootElement p (-u) := by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← rootElement_add, neg_add_cancel]
    exact Units.ext (by simp [coe_rootElement])
  refine Units.ext ?_
  simp only [hinv, Units.val_mul, coe_rootElement, transvection, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne, ne_eq,
    hij.symm, hjl.symm, hil.symm, not_false_eq_true, add_zero]
  ext a b
  simp only [Matrix.add_apply, single_apply, one_apply]
  split_ifs <;> ring

/-- The roots of `gl n` satisfy $(e_i - e_j) + (e_j - e_l) = e_i - e_l$. -/
theorem gl_root_add {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (gl n).root ⟨(i, j), hij⟩ + (gl n).root ⟨(j, l), hjl⟩ = (gl n).root ⟨(i, l), hil⟩ := by
  simp [gl_root]

variable {k : Type*} [Field k]

/-- Over a field, the diagonal torus and the root elements generate $\mathrm{GL}_n(k)$. -/
theorem closure_torus_rootElement :
    Subgroup.closure (Set.range (torusHom n k) ∪ Set.range fun p : glIndex n × k => rootElement p.1 p.2) =
      ⊤ := by
  set S := Subgroup.closure (Set.range (torusHom n k) ∪
    Set.range fun p : glIndex n × k => rootElement p.1 p.2)
  refine eq_top_iff.2 fun g _ => ?_
  suffices h : ∃ g' ∈ S, (g' : Matrix (Fin n) (Fin n) k) = g by
    obtain ⟨g', hg', h⟩ := h
    rwa [← Units.ext h]
  refine diagonal_transvection_induction_of_det_ne_zero (fun M => ∃ g' ∈ S, (g' : Matrix _ _ k) = M)
    (g : Matrix (Fin n) (Fin n) k) g.det_ne_zero (fun D hD => ?_) (fun t => ?_)
    (fun A B _ _ hA hB => ?_)
  · rw [det_diagonal, Finset.prod_ne_zero_iff] at hD
    refine ⟨torusHom n k (ofUnits fun i => Units.mk0 (D i) (hD i (Finset.mem_univ i))),
      Subgroup.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
    rw [coe_torusHom]
    congr 1
    funext i
    rw [torusEntry_ofUnits, Units.val_mk0]
  · exact ⟨rootElement ⟨(t.i, t.j), t.hij⟩ t.c,
      Subgroup.subset_closure (Or.inr ⟨(⟨(t.i, t.j), t.hij⟩, t.c), rfl⟩), rfl⟩
  · obtain ⟨a, ha, rfl⟩ := hA
    obtain ⟨b, hb, rfl⟩ := hB
    exact ⟨a * b, mul_mem ha hb, rfl⟩

end SplitGL

namespace SplitTorus

variable {Y : Type*} [AddCommGroup Y] (R : Type*) [CommRing R]

/-- The action of the linear automorphisms of $Y$ on the torus $\mathrm{Hom}(Y, R^\times)$. The automorphism $e$ sends $t$ to $t \circ e^{-1}$. -/
def torusAction : (Y ≃ₗ[ℤ] Y) →* MulAut (SplitTorus Y R) where
  toFun e := MulEquiv.monoidHomCongrLeft e.toAddEquiv.toMultiplicative
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The formula for the action: $(e \cdot t)(y) = t(e^{-1} y)$. -/
@[simp] theorem torusAction_apply (e : Y ≃ₗ[ℤ] Y) (t : SplitTorus Y R) (y : Multiplicative Y) :
    torusAction R e t y = t (Multiplicative.ofAdd (e.symm y.toAdd)) := rfl

end SplitTorus

namespace LGroup

open SplitTorus QuasiSplitDatum RootDatum

variable {Γ : Type*} [Group Γ] {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (R : Type*) [CommRing R]

/-- A semidirect product with the trivial action is the direct product. -/
def semidirectProductOneEquiv (H G : Type*) [Group H] [Group G] :
    H ⋊[(1 : G →* MulAut H)] G ≃* H × G :=
  SemidirectProduct.mulEquivProd

/-- The action of $\Gamma$ on the dual torus $\hat T(R) = \mathrm{Hom}(Y, R^\times)$. It is the action on $Y$ of the dual datum, through `torusAction`. -/
def dualTorusAction (D : QuasiSplitDatum Γ ι X Y) : Γ →* MulAut (SplitTorus Y R) :=
  (torusAction R).comp ((RootPairing.Equiv.weightHom D.dual.datum).comp D.dual.action)

/-- The formula for the dual action: $(\gamma \cdot t)(y) = t(\gamma^{-1} y)$, with $\gamma$ acting on $Y$ through the dual datum. -/
theorem dualTorusAction_apply (D : QuasiSplitDatum Γ ι X Y) (γ : Γ) (t : SplitTorus Y R)
    (y : Y) : dualTorusAction R D γ t (Multiplicative.ofAdd y) =
      t (Multiplicative.ofAdd ((D.dual.action γ).weightEquiv.symm y)) := rfl

/-- The L-group of the maximal torus: $\hat T(R) \rtimes \Gamma$, with $\hat T(R) = \mathrm{Hom}(Y, R^\times)$ and $\Gamma$ acting through the dual datum. For $R = \mathbb{C}$ this is the L-group of the torus. -/
abbrev TorusLGroup (D : QuasiSplitDatum Γ ι X Y) : Type _ :=
  SplitTorus Y R ⋊[dualTorusAction R D] Γ

/-- For a split datum the dual action on the dual torus is trivial. -/
theorem dualTorusAction_eq_one {D : QuasiSplitDatum Γ ι X Y} (h : D.IsSplit) :
    dualTorusAction R D = 1 := by
  have h' : D.dual.action = 1 := h.dual
  simp only [dualTorusAction, h', MonoidHom.comp_one]

/-- For a split datum the L-group of the torus is the direct product $\hat T(R) \times \Gamma$. -/
def torusLGroupEquivProd {D : QuasiSplitDatum Γ ι X Y} (h : D.IsSplit) :
    TorusLGroup R D ≃* SplitTorus Y R × Γ :=
  (SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl Γ)
    (fun γ => by rw [dualTorusAction_eq_one R h]; rfl)).trans
    (semidirectProductOneEquiv (SplitTorus Y R) Γ)

/-- The equivalence `torusLGroupEquivProd` keeps the two components. -/
@[simp] theorem torusLGroupEquivProd_apply {D : QuasiSplitDatum Γ ι X Y} (h : D.IsSplit)
    (g : TorusLGroup R D) : torusLGroupEquivProd R h g = (g.left, g.right) := rfl

/-- The L-group of split $\mathrm{GL}_n$: the direct product $\mathrm{GL}_n(R) \rtimes \Gamma$ with the trivial action. -/
abbrev GLLGroup (n : ℕ) (Γ : Type*) [Group Γ] : Type _ :=
  GL (Fin n) R ⋊[(1 : Γ →* MulAut (GL (Fin n) R))] Γ

/-- The embedding of the L-group of the diagonal torus of split $\mathrm{GL}_n$ into the L-group of $\mathrm{GL}_n$. It is the diagonal embedding on the dual torus and the identity on $\Gamma$. -/
def torusLGroupToGL (n : ℕ) :
    TorusLGroup R (split (Γ := Γ) (gl n) (glBase n)) →* GLLGroup R n Γ :=
  SemidirectProduct.map (SplitGL.torusHom n R) (MonoidHom.id Γ) (fun γ => by
    rw [dualTorusAction_eq_one R (isSplit_split _ _)]
    rfl)

/-- The embedding `torusLGroupToGL` is injective. -/
theorem torusLGroupToGL_injective (n : ℕ) :
    Injective (torusLGroupToGL (Γ := Γ) R n) := by
  intro g g' h
  have h1 := congrArg SemidirectProduct.left h
  have h2 := congrArg SemidirectProduct.right h
  exact SemidirectProduct.ext (SplitGL.torusHom_injective h1) h2

end LGroup

end Langlands.Groups
