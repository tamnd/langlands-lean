/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Padic.LogTeich

/-!
# The ring $B_{st}$ and semistable representations

This file defines the Frobenius of $B_{cris}(R)$, the ring $B_{st}(R) = B_{cris}(R)[u]$ with its Galois action $g(u) = u + c(g)$ for a cocycle $c$, its Frobenius with $\varphi(u) = p u$ and its monodromy operator $N$. With the Kummer cocycle $c(\sigma) = \log [\eta_\sigma]$ it defines semistable and potentially semistable representations of $G_{\mathbb{Q}_p}$.

## Main definitions

* `bcrisFrob`: the Frobenius of $B_{cris}(R)$.
* `BstCocycle`: a cocycle $c : M \to B$ with $c(g h) = g c(h) + c(g)$.
* `BstPoly`: the ring $B[u]$ with the action $g(u) = u + c(g)$ of $M$.
* `bstFrob`: the Frobenius of $B[u]$ for an endomorphism $\varphi$ of $B$ and $u \mapsto q u$.
* `bstN`: the monodromy operator $N = -d/du$ of $B[u]$.
* `BstCocycle.ofAcris`: the image in $B_{cris}(R)$ of a cocycle with values in $A_{cris}(R)$.
* `bstFrobBcris`: the Frobenius of $B_{st}(R)$, with $\varphi(u) = p u$.
* `kummerCocycle`: the Kummer cocycle $\sigma \mapsto \log [\eta_\sigma]$ in $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$.
* `BstGal`: the ring $B_{st}(\mathcal{O}_{\mathbb{C}_p})$ with the action of $G_{\mathbb{Q}_p}$.
* `bstFrobCp`: the Frobenius of $B_{st}(\mathcal{O}_{\mathbb{C}_p})$.
* `galFixing`: the subgroup $G_L$ of $G_{\mathbb{Q}_p}$ for an intermediate field $L$.
* `IsSemistableQp`: the representation is $B_{st}$-admissible.
* `IsPotentiallySemistableQp`: the restriction to $G_L$ is $B_{st}$-admissible for a finite extension $L$ of $\mathbb{Q}_p$.

## Main results

* `bcrisFrob_algebraMap`, `bcrisFrob_smul`: the Frobenius of $B_{cris}(R)$ extends that of $B_{cris}^+(R)$ and commutes with $M$.
* `smul_bstU`: $g(u) = u + c(g)$.
* `bstFrob_bstU`, `bstFrob_smul`: $\varphi(u) = q u$, and $\varphi$ commutes with $M$ if $\varphi(c(g)) = q c(g)$.
* `bstN_bstU`, `bstN_smul`, `bstN_bstFrob`: $N(u) = -1$, $N g = g N$ and $N \varphi = q \varphi N$.
* `bstFrobBcris_smul_ofAcris`: for a cocycle with values in $A_{cris}(R)$ and $\varphi(c(g)) = p c(g)$, the Frobenius of $B_{st}(R)$ commutes with $M$.
* `smul_uBst`, `bstFrobCp_uBst`, `bstFrobCp_smul`, `bstN_smul_cp`, `bstN_bstFrobCp`: the same relations for $B_{st}(\mathcal{O}_{\mathbb{C}_p})$.
* `isAdmissible_comp_iff`: admissibility does not change along a surjective group homomorphism.
* `IsSemistableQp.isPotentiallySemistableQp`: a semistable representation is potentially semistable.
* `isSemistableQp_trivial_of_nontrivial`: if $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation is semistable.

## Implementation notes

`BstPoly` is a type synonym of the polynomial ring, so that the action of $M$ is the action through the cocycle and not the action on the coefficients. The ring `BstCp` of `Langlands.Padic.Crystalline` is the polynomial ring without this action.

The constructions are generic in the ring $B$ and in $R$. The instances of $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ are deep localizations, and the elaboration of statements on it directly is slow. So the results for $\mathcal{O}_{\mathbb{C}_p}$ are applications of the generic results.

The implication crystalline $\Rightarrow$ semistable is not proved here. It needs $B_{st}^{G_{\mathbb{Q}_p}} = B_{cris}^{G_{\mathbb{Q}_p}}$ and $D_{st}(V) = D_{cris}(V)$ for crystalline $V$, thus that $u$ is transcendental over $B_{cris}$ in a Galois-compatible way. The rank in `IsAdmissible` is over the ring $B^{G}$, which is not shown to be a field.

The statement $t \neq 0$ is not proved here. Thus the nontriviality of $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$, and with it the semistability of the trivial representation, stays conditional.

The identification $\log [\eta_\sigma] = c(\sigma) t$ with the Kummer cocycle $c$ of $p$ and the relation $g t = \chi(g) t$ are not proved here.
-/

open Ideal WittVector

namespace Langlands.Padic

universe u

section BcrisFrob

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable (M : Type*) [Monoid M] [MulSemiringAction M R]

/-- The Frobenius of $B_{cris}^+(R)$ sends $g t$ to $p \cdot g t$. -/
theorem bcrisPlusFrob_smul_logTeich {ε : PreTilt R p} (hε : ε.untilt = 1) (g : M) :
    bcrisPlusFrob R p (g • algebraMap (Acris R p) (BcrisPlus R p) (logTeich hε)) =
      (p : BcrisPlus R p) * (g • algebraMap (Acris R p) (BcrisPlus R p) (logTeich hε)) := by
  rw [bcrisPlusFrob_smul, bcrisPlusFrob_algebraMap, acrisFrob_logTeich_eq, map_mul, smul_mul',
    map_natCast]
  rw [show g • (p : BcrisPlus R p) = p from map_natCast (MulSemiringAction.toRingHom M _ g) p]

/-- The Frobenius of $B_{cris}^+(R)$, followed by the map to $B_{cris}(R)$, sends the submonoid of the elements $g t$ to units. -/
theorem bcrisSubmonoid_le_frob {ε : PreTilt R p} (hε : ε.untilt = 1) :
    bcrisSubmonoid M hε ≤ (IsUnit.submonoid (Bcris M hε)).comap
      ((algebraMap (BcrisPlus R p) (Bcris M hε)).comp (bcrisPlusFrob R p)) := by
  refine Submonoid.closure_le.2 ?_
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Submonoid.mem_comap, IsUnit.mem_submonoid_iff, RingHom.comp_apply,
    bcrisPlusFrob_smul_logTeich, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.map_units (Bcris M hε)
    (⟨_, Submonoid.subset_closure ⟨g, rfl⟩⟩ : bcrisSubmonoid M hε))
  rw [← map_natCast (algebraMap (Acris R p) (BcrisPlus R p))]
  exact ((IsLocalization.Away.algebraMap_isUnit (p : Acris R p)).map _)

variable {M} in
/-- The Frobenius $\varphi$ of $B_{cris}(R)$: the extension of the Frobenius of $B_{cris}^+(R)$. It exists since $\varphi(g t) = p \cdot g t$. -/
noncomputable def bcrisFrob {ε : PreTilt R p} (hε : ε.untilt = 1) :
    Bcris M hε →+* Bcris M hε :=
  IsLocalization.lift (M := bcrisSubmonoid M hε)
    (g := (algebraMap (BcrisPlus R p) (Bcris M hε)).comp (bcrisPlusFrob R p))
    (fun s => bcrisSubmonoid_le_frob M hε s.2)

variable {M} in
/-- The Frobenius of $B_{cris}(R)$ extends the Frobenius of $B_{cris}^+(R)$. -/
theorem bcrisFrob_algebraMap {ε : PreTilt R p} (hε : ε.untilt = 1) (x : BcrisPlus R p) :
    bcrisFrob hε (algebraMap _ (Bcris M hε) x) = algebraMap _ _ (bcrisPlusFrob R p x) :=
  IsLocalization.lift_eq _ _

variable {M} in
/-- The Frobenius of $B_{cris}(R)$ commutes with the action of $M$. -/
theorem bcrisFrob_smul {ε : PreTilt R p} (hε : ε.untilt = 1) (g : M) (x : Bcris M hε) :
    bcrisFrob hε (g • x) = g • bcrisFrob hε x := by
  have := IsLocalization.ringHom_ext (bcrisSubmonoid M hε)
    (j := (bcrisFrob hε).comp (MulSemiringAction.toRingHom M (Bcris M hε) g))
    (k := (MulSemiringAction.toRingHom M (Bcris M hε) g).comp (bcrisFrob hε))
    (RingHom.ext fun y => by
      simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
      rw [smul_algebraMap_bcris, bcrisFrob_algebraMap, bcrisFrob_algebraMap, bcrisPlusFrob_smul,
        smul_algebraMap_bcris])
  exact RingHom.congr_fun this x

end BcrisFrob

section BstPoly

open Polynomial

variable {M : Type*} [Monoid M] {B : Type*} [CommRing B] [MulSemiringAction M B]

variable (M B) in
/-- A cocycle $c : M \to B$: $c(1) = 0$ and $c(g h) = g c(h) + c(g)$. -/
structure BstCocycle where
  /-- The function $g \mapsto c(g)$. -/
  toFun : M → B
  /-- The relation $c(1) = 0$. -/
  map_one' : toFun 1 = 0
  /-- The cocycle relation $c(g h) = g c(h) + c(g)$. -/
  map_mul' : ∀ g h, toFun (g * h) = g • toFun h + toFun g

/-- The map of $B[u]$ of $g \in M$ for a cocycle $c$: the action of $g$ on the coefficients and $u \mapsto u + c(g)$. -/
noncomputable def bstMap (c : BstCocycle M B) (g : M) : Polynomial B →+* Polynomial B :=
  (compRingHom (X + C (c.toFun g))).comp (mapRingHom (MulSemiringAction.toRingHom M B g))

/-- The formula for `bstMap`. -/
theorem bstMap_apply (c : BstCocycle M B) (g : M) (f : Polynomial B) :
    bstMap c g f = (f.map (MulSemiringAction.toRingHom M B g)).comp (X + C (c.toFun g)) := rfl

/-- The map `bstMap c g` extends the action of $g$ on $B$. -/
theorem bstMap_C (c : BstCocycle M B) (g : M) (b : B) : bstMap c g (C b) = C (g • b) := by
  rw [bstMap_apply, map_C, C_comp, MulSemiringAction.toRingHom_apply]

/-- The map `bstMap c g` sends $u$ to $u + c(g)$. -/
theorem bstMap_X (c : BstCocycle M B) (g : M) : bstMap c g X = X + C (c.toFun g) := by
  rw [bstMap_apply, map_X, X_comp]

/-- The map `bstMap c 1` is the identity. -/
theorem bstMap_one (c : BstCocycle M B) : bstMap c 1 = RingHom.id _ := by
  refine Polynomial.ringHom_ext (fun b => ?_) ?_
  · rw [bstMap_C, one_smul, RingHom.id_apply]
  · rw [bstMap_X, c.map_one', map_zero, add_zero, RingHom.id_apply]

/-- The map `bstMap c (g * h)` is the composition of `bstMap c g` and `bstMap c h`. -/
theorem bstMap_mul (c : BstCocycle M B) (g h : M) :
    bstMap c (g * h) = (bstMap c g).comp (bstMap c h) := by
  refine Polynomial.ringHom_ext (fun b => ?_) ?_
  · rw [RingHom.comp_apply, bstMap_C, bstMap_C, bstMap_C, mul_smul]
  · rw [RingHom.comp_apply, bstMap_X, bstMap_X, map_add, bstMap_X, bstMap_C, c.map_mul',
      map_add, add_assoc, add_comm (C (g • c.toFun h))]

variable (c : BstCocycle M B)

/-- The ring $B[u]$ with the action of $M$ defined by the cocycle $c$: $g$ acts on $B$ as before and sends $u$ to $u + c(g)$. With $B = B_{cris}$ and $c(g) = \log [g(p^\flat)/p^\flat]$ this is $B_{st}$. -/
def BstPoly (_c : BstCocycle M B) : Type _ := Polynomial B

/-- The ring structure on `BstPoly c`. -/
noncomputable instance : CommRing (BstPoly c) := inferInstanceAs (CommRing (Polynomial B))

/-- The algebra structure on `BstPoly c` over a base ring of $B$. -/
noncomputable instance {K : Type*} [CommRing K] [Algebra K B] : Algebra K (BstPoly c) :=
  inferInstanceAs (Algebra K (Polynomial B))

/-- The action of $M$ on `BstPoly c` by ring endomorphisms. It is an action by the cocycle relation of $c$. -/
noncomputable instance bstPolyAction : MulSemiringAction M (BstPoly c) :=
  mulSemiringActionOfMap (bstMap c) (bstMap_one c) (bstMap_mul c)

/-- The action of $g$ on `BstPoly c` is `bstMap c g`. -/
theorem bstPoly_smul_def (g : M) (f : BstPoly c) : g • f = bstMap c g f := rfl

/-- The inclusion $B \to B[u]$. -/
noncomputable def bstC : B →+* BstPoly c := C

/-- The variable $u$ of $B[u]$. For $B_{st}$ it plays the role of $\log [p^\flat]$. -/
noncomputable def bstU : BstPoly c := (X : Polynomial B)

/-- The action of $g$ on $B[u]$ extends the action on $B$. -/
theorem smul_bstC (g : M) (b : B) : g • bstC c b = bstC c (g • b) :=
  bstMap_C c g b

/-- The formula $g(u) = u + c(g)$ in $B[u]$. -/
theorem smul_bstU (g : M) : g • bstU c = bstU c + bstC c (c.toFun g) :=
  bstMap_X c g

/-- If the action of $M$ on $B$ is $K$-linear, then so is the action on $B[u]$. -/
instance bstPoly_smulCommClass {K : Type*} [CommRing K] [Algebra K B] [SMulCommClass M K B] :
    SMulCommClass M K (BstPoly c) where
  smul_comm g q f := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    change bstMap c g (C (algebraMap K B q)) = C (algebraMap K B q)
    rw [bstMap_C, smul_algebraMap]

variable (φ : B →+* B) (q : B)

/-- The Frobenius of $B[u]$ for a ring endomorphism $\varphi$ of $B$ and $q \in B$: $\varphi$ on the coefficients and $u \mapsto q u$. For $B_{st}$, $\varphi$ is the Frobenius of $B_{cris}$ and $q = p$. -/
noncomputable def bstFrob : BstPoly c →+* BstPoly c :=
  (compRingHom (C q * X)).comp (mapRingHom φ)

/-- The formula for `bstFrob`. -/
theorem bstFrob_apply (f : BstPoly c) :
    bstFrob c φ q f = (Polynomial.map φ (show Polynomial B from f)).comp (C q * X) := rfl

/-- The Frobenius of $B[u]$ extends $\varphi$. -/
theorem bstFrob_bstC (b : B) : bstFrob c φ q (bstC c b) = bstC c (φ b) := by
  change (Polynomial.map φ (C b)).comp (C q * X) = C (φ b)
  rw [map_C, C_comp]

/-- The formula $\varphi(u) = q u$ in $B[u]$. -/
theorem bstFrob_bstU : bstFrob c φ q (bstU c) = bstC c q * bstU c := by
  change (Polynomial.map φ X).comp (C q * X) = C q * X
  rw [map_X, X_comp]
  rfl

/-- If $\varphi$ commutes with $M$, $g q = q$ and $\varphi(c(g)) = q c(g)$ for all $g$, then the Frobenius of $B[u]$ commutes with the action of $M$. -/
theorem bstFrob_smul (hφ : ∀ (g : M) b, φ (g • b) = g • φ b) (hq : ∀ g : M, g • q = q)
    (hc : ∀ g, φ (c.toFun g) = q * c.toFun g) (g : M) (f : BstPoly c) :
    bstFrob c φ q (g • f) = g • bstFrob c φ q f := by
  have := Polynomial.ringHom_ext
    (f := (bstFrob c φ q).comp (MulSemiringAction.toRingHom M (BstPoly c) g))
    (g := (MulSemiringAction.toRingHom M (BstPoly c) g).comp (bstFrob c φ q))
    (fun b => by
      change bstFrob c φ q (g • bstC c b) = g • bstFrob c φ q (bstC c b)
      rw [smul_bstC, bstFrob_bstC, bstFrob_bstC, smul_bstC, hφ])
    (by
      change bstFrob c φ q (g • bstU c) = g • bstFrob c φ q (bstU c)
      rw [smul_bstU, map_add, bstFrob_bstU, bstFrob_bstC, hc, smul_mul', smul_bstU, smul_bstC,
        hq, map_mul]
      ring)
  exact RingHom.congr_fun this f

/-- The monodromy operator $N = -d/du$ of $B[u]$. -/
noncomputable def bstN (f : BstPoly c) : BstPoly c :=
  monodromy B (show Polynomial B from f)

/-- The formula $N(u) = -1$. -/
theorem bstN_bstU : bstN c (bstU c) = -1 :=
  monodromy_X

/-- The operator $N$ is zero on $B$. -/
theorem bstN_bstC (b : B) : bstN c (bstC c b) = 0 :=
  monodromy_C b

/-- The monodromy operator commutes with `bstMap c g`. -/
theorem monodromy_bstMap (g : M) (f : Polynomial B) :
    monodromy B (bstMap c g f) = bstMap c g (monodromy B f) := by
  rw [monodromy_apply, monodromy_apply, bstMap_apply, bstMap_apply, derivative_comp,
    derivative_add, derivative_X, derivative_C, add_zero, one_mul, derivative_map,
    Polynomial.map_neg, neg_comp]

/-- The monodromy operator commutes with the action of $M$: $N(g x) = g N(x)$. -/
theorem bstN_smul (g : M) (f : BstPoly c) : bstN c (g • f) = g • bstN c f :=
  monodromy_bstMap c g f

/-- The relation $N \varphi = q \varphi N$ on $B[u]$, for polynomials. -/
theorem monodromy_bstFrob (f : Polynomial B) :
    monodromy B ((Polynomial.map φ f).comp (C q * X)) =
      C q * (Polynomial.map φ (monodromy B f)).comp (C q * X) := by
  rw [monodromy_apply, monodromy_apply, derivative_comp, derivative_C_mul_X, derivative_map,
    Polynomial.map_neg, neg_comp, mul_neg]

/-- The relation $N \varphi = q \varphi N$ in $B[u]$. For $B_{st}$ this is $N \varphi = p \varphi N$. -/
theorem bstN_bstFrob (f : BstPoly c) :
    bstN c (bstFrob c φ q f) = bstC c q * bstFrob c φ q (bstN c f) :=
  monodromy_bstFrob φ q f

end BstPoly

section BcrisCocycle

open Polynomial

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
variable {M : Type*} [Monoid M] [MulSemiringAction M R] {ε : PreTilt R p} {hε : ε.untilt = 1}

/-- The action of $g$ commutes with the map $A_{cris}(R) \to B_{cris}(R)$. -/
theorem smul_algebraMap_algebraMap (g : M) (x : Acris R p) :
    g • algebraMap (BcrisPlus R p) (Bcris M hε) (algebraMap (Acris R p) (BcrisPlus R p) x) =
      algebraMap (BcrisPlus R p) (Bcris M hε)
        (algebraMap (Acris R p) (BcrisPlus R p) (g • x)) := by
  rw [smul_algebraMap_bcris, bcrisPlus_smul_def, bcrisPlusMap_algebraMap]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The image in $B_{cris}(R)$ of a function $k$ with $k(g h) = g k(h) + k(g)$ satisfies the same relation. -/
theorem algebraMap_cocycle (k : M → Acris R p) (hm : ∀ g h, k (g * h) = g • k h + k g)
    (g h : M) :
    algebraMap (BcrisPlus R p) (Bcris M hε) (algebraMap (Acris R p) (BcrisPlus R p) (k (g * h))) =
      g • algebraMap (BcrisPlus R p) (Bcris M hε)
          (algebraMap (Acris R p) (BcrisPlus R p) (k h)) +
      algebraMap (BcrisPlus R p) (Bcris M hε) (algebraMap (Acris R p) (BcrisPlus R p) (k g)) := by
  rw [smul_algebraMap_algebraMap, ← RingHom.map_add, ← RingHom.map_add, hm]

variable (hε) in
/-- The image in $B_{cris}(R)$ of a cocycle $k : M \to A_{cris}(R)$. -/
noncomputable def BstCocycle.ofAcris (k : M → Acris R p) (h1 : k 1 = 0)
    (hm : ∀ g h, k (g * h) = g • k h + k g) : BstCocycle M (Bcris M hε) where
  toFun g := algebraMap (BcrisPlus R p) (Bcris M hε) (algebraMap (Acris R p) (BcrisPlus R p) (k g))
  map_one' := by rw [h1, map_zero, map_zero]
  map_mul' := algebraMap_cocycle k hm

/-- The value of `BstCocycle.ofAcris` at $g$ is the image of $k(g)$. -/
theorem BstCocycle.ofAcris_apply (k : M → Acris R p) (h1 : k 1 = 0)
    (hm : ∀ g h, k (g * h) = g • k h + k g) (g : M) :
    (BstCocycle.ofAcris hε k h1 hm).toFun g =
      algebraMap (BcrisPlus R p) (Bcris M hε) (algebraMap (Acris R p) (BcrisPlus R p) (k g)) :=
  rfl

/-- If $\varphi(k(g)) = p k(g)$ in $A_{cris}(R)$, then the same holds for the image of $k$ in $B_{cris}(R)$. -/
theorem BstCocycle.frob_ofAcris (k : M → Acris R p) (h1 : k 1 = 0)
    (hm : ∀ g h, k (g * h) = g • k h + k g) (hk : ∀ g, acrisFrob R p (k g) = p * k g)
    (g : M) :
    bcrisFrob hε ((BstCocycle.ofAcris hε k h1 hm).toFun g) =
      p * (BstCocycle.ofAcris hε k h1 hm).toFun g := by
  rw [BstCocycle.ofAcris_apply, bcrisFrob_algebraMap, bcrisPlusFrob_algebraMap, hk, map_mul,
    map_mul, map_natCast, map_natCast]

/-- For a cocycle of the form $g \mapsto \log [\eta_g]$ with $\eta_g$ of untilt $1$, the relation $\varphi(c(g)) = p c(g)$ holds in $B_{cris}(R)$. -/
theorem BstCocycle.frob_ofAcris_logTeich (η : M → PreTilt R p) (hη : ∀ g, (η g).untilt = 1)
    (h1 : logTeich (hη 1) = 0)
    (hm : ∀ g h, logTeich (hη (g * h)) = g • logTeich (hη h) + logTeich (hη g)) (g : M) :
    bcrisFrob hε ((BstCocycle.ofAcris hε (fun g => logTeich (hη g)) h1 hm).toFun g) =
      p * (BstCocycle.ofAcris hε (fun g => logTeich (hη g)) h1 hm).toFun g :=
  BstCocycle.frob_ofAcris _ h1 hm (fun g => acrisFrob_logTeich_eq (hη g)) g

/-- The action of $M$ on $B_{cris}(R)$ fixes $p$. -/
theorem smul_natCast_bcris (g : M) : g • (p : Bcris M hε) = p :=
  map_natCast (MulSemiringAction.toRingHom M (Bcris M hε) g) p

variable (c : BstCocycle M (Bcris M hε))

/-- The $\mathbb{Q}_p$-algebra structure on $B_{cris}(R)[u]$. -/
noncomputable instance bstPolyBcrisQpAlgebra : Algebra ℚ_[p] (BstPoly c) := inferInstance

/-- The action of $M$ on $B_{cris}(R)[u]$ is $\mathbb{Q}_p$-linear. -/
instance bstPolyBcris_smulCommClass : SMulCommClass M ℚ_[p] (BstPoly c) :=
  bstPoly_smulCommClass c

/-- The Frobenius of $B_{st}(R) = B_{cris}(R)[u]$: the Frobenius of $B_{cris}(R)$ on the coefficients and $\varphi(u) = p u$. -/
noncomputable def bstFrobBcris : BstPoly c →+* BstPoly c :=
  bstFrob c (bcrisFrob hε) p

/-- The formula $\varphi(u) = p u$ in $B_{st}(R)$. -/
theorem bstFrobBcris_bstU : bstFrobBcris c (bstU c) = bstC c (p : Bcris M hε) * bstU c :=
  bstFrob_bstU _ _ _

/-- The Frobenius of $B_{st}(R)$ extends the Frobenius of $B_{cris}(R)$. -/
theorem bstFrobBcris_bstC (b : Bcris M hε) :
    bstFrobBcris c (bstC c b) = bstC c (bcrisFrob hε b) :=
  bstFrob_bstC _ _ _ b

/-- The relation $N \varphi = p \varphi N$ in $B_{st}(R)$. -/
theorem bstN_bstFrobBcris (f : BstPoly c) :
    bstN c (bstFrobBcris c f) = bstC c (p : Bcris M hε) * bstFrobBcris c (bstN c f) :=
  bstN_bstFrob _ _ _ f

/-- If $\varphi(c(g)) = p c(g)$ for all $g$, then the Frobenius of $B_{st}(R)$ commutes with the action of $M$. -/
theorem bstFrobBcris_smul (hc : ∀ g, bcrisFrob hε (c.toFun g) = p * c.toFun g) (g : M)
    (f : BstPoly c) : bstFrobBcris c (g • f) = g • bstFrobBcris c f :=
  bstFrob_smul _ _ _ (bcrisFrob_smul hε) smul_natCast_bcris hc g f

/-- For the image $c$ of a cocycle $k : M \to A_{cris}(R)$ with $\varphi(k(g)) = p k(g)$, the Frobenius of $B_{st}(R)$ commutes with the action of $M$. -/
theorem bstFrobBcris_smul_ofAcris (k : M → Acris R p) (h1 : k 1 = 0)
    (hm : ∀ g h, k (g * h) = g • k h + k g) (hk : ∀ g, acrisFrob R p (k g) = p * k g) (g : M)
    (f : BstPoly (BstCocycle.ofAcris hε k h1 hm)) :
    bstFrobBcris _ (g • f) = g • bstFrobBcris _ f :=
  bstFrob_smul _ _ _ (bcrisFrob_smul hε) smul_natCast_bcris
    (BstCocycle.frob_ofAcris k h1 hm hk) g f

end BcrisCocycle

section Admissible

open TensorProduct

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [CommRing B] [Algebra K B]
  [MulSemiringAction G B] [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] [MulSemiringAction H B] [SMulCommClass H K B]

/-- Let $f : H \to G$ be a surjective group homomorphism such that $H$ acts on $B$ through $f$. Then $V$ is $B$-admissible for $G$ if and only if it is $B$-admissible for $H$. -/
theorem isAdmissible_comp_iff (f : H →* G) (hf : Function.Surjective f)
    (hB : ∀ (h : H) (b : B), h • b = f h • b) (ρ : Representation K G V) :
    IsAdmissible B (ρ.comp f) ↔ IsAdmissible B ρ := by
  have hT : ∀ h : H, tensorAction B (ρ.comp f) h = tensorAction B ρ (f h) := fun h => by
    refine TensorProduct.ext' fun b v => ?_
    rw [tensorAction_tmul, tensorAction_tmul, hB]
    rfl
  have hfix : ∀ b : B, (∀ h : H, h • b = b) ↔ ∀ g : G, g • b = b := fun b =>
    ⟨fun hh g => by
      obtain ⟨h, rfl⟩ := hf g
      rw [← hB]
      exact hh h, fun hh h => by rw [hB]; exact hh _⟩
  have hinv : ∀ x : B ⊗[K] V,
      (∀ h : H, tensorAction B (ρ.comp f) h x = x) ↔ ∀ g : G, tensorAction B ρ g x = x :=
    fun x => ⟨fun hh g => by
      obtain ⟨h, rfl⟩ := hf g
      rw [← hT]
      exact hh h, fun hh h => by rw [hT]; exact hh _⟩
  let i : FixedPoints.subalgebra K B H → FixedPoints.subalgebra K B G := fun b =>
    ⟨b.1, FixedPoints.mem_subalgebra.2 ((hfix b.1).1 (FixedPoints.mem_subalgebra.1 b.2))⟩
  have hi : Function.Bijective i := by
    refine ⟨fun a b hab => Subtype.ext (by have := congrArg Subtype.val hab; exact this),
      fun b => ?_⟩
    exact ⟨⟨b.1, FixedPoints.mem_subalgebra.2
      ((hfix b.1).2 (FixedPoints.mem_subalgebra.1 b.2))⟩, rfl⟩
  let j : deRhamInvariants B (ρ.comp f) ≃+ deRhamInvariants B ρ :=
    { toFun := fun x => ⟨x.1, (hinv x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hinv x.1).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have := rank_eq_of_equiv_equiv i j hi (fun _ _ => rfl)
  unfold IsAdmissible Module.finrank
  rw [this]

end Admissible

section Cp

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The Kummer cocycle $\sigma \mapsto \log [\eta_\sigma]$ of $G_{\mathbb{Q}_p}$ with values in $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$, with $\eta_\sigma = \sigma(p^\flat)/p^\flat$. -/
noncomputable def kummerCocycle : BstCocycle (Field.absoluteGaloisGroup ℚ_[p]) (BcrisCp p) :=
  BstCocycle.ofAcris untilt_epsCp (fun σ => logTeich (untilt_kummerFlat σ)) kummerLog_one
    kummerLog_mul

variable (p) in
/-- The ring $B_{st}(\mathcal{O}_{\mathbb{C}_p}) = B_{cris}(\mathcal{O}_{\mathbb{C}_p})[u]$ with the action of $G_{\mathbb{Q}_p}$ given by $\sigma(u) = u + \log [\eta_\sigma]$, so $u$ plays the role of $\log [p^\flat]$. -/
abbrev BstGal : Type _ := BstPoly (kummerCocycle p)

variable (p) in
/-- The variable $u$ of $B_{st}(\mathcal{O}_{\mathbb{C}_p})$. -/
noncomputable abbrev uBst : BstGal p := bstU (kummerCocycle p)

/-- The formula $\sigma(u) = u + \log [\eta_\sigma]$ in $B_{st}(\mathcal{O}_{\mathbb{C}_p})$. -/
theorem smul_uBst (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    σ • uBst p = uBst p + bstC (kummerCocycle p) (algebraMap (BcrisPlus (PadicComplexInt p) p)
      (BcrisCp p) (algebraMap (Acris (PadicComplexInt p) p) _ (kummerLog σ))) :=
  smul_bstU _ σ

variable (p) in
/-- The Frobenius $\varphi$ of $B_{st}(\mathcal{O}_{\mathbb{C}_p})$: the Frobenius of $B_{cris}$ on the coefficients and $\varphi(u) = p u$. -/
noncomputable def bstFrobCp : BstGal p →+* BstGal p :=
  bstFrobBcris (kummerCocycle p)

/-- The formula $\varphi(u) = p u$ in $B_{st}(\mathcal{O}_{\mathbb{C}_p})$. -/
theorem bstFrobCp_uBst : bstFrobCp p (uBst p) = bstC _ (p : BcrisCp p) * uBst p :=
  bstFrobBcris_bstU _

/-- The Frobenius of $A_{cris}(\mathcal{O}_{\mathbb{C}_p})$ sends $\log [\eta_\sigma]$ to $p \log [\eta_\sigma]$. -/
theorem acrisFrob_kummerLog (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    acrisFrob (PadicComplexInt p) p (kummerLog σ) = p * kummerLog σ :=
  acrisFrob_logTeich_eq (untilt_kummerFlat σ)

/-- The Frobenius of $B_{st}(\mathcal{O}_{\mathbb{C}_p})$ commutes with the action of $G_{\mathbb{Q}_p}$. -/
theorem bstFrobCp_smul (σ : Field.absoluteGaloisGroup ℚ_[p]) (f : BstGal p) :
    bstFrobCp p (σ • f) = σ • bstFrobCp p f :=
  bstFrobBcris_smul _ (BstCocycle.frob_ofAcris_logTeich _ _ _ _) σ f

/-- The monodromy operator of $B_{st}(\mathcal{O}_{\mathbb{C}_p})$ commutes with $G_{\mathbb{Q}_p}$. -/
theorem bstN_smul_cp (σ : Field.absoluteGaloisGroup ℚ_[p]) (f : BstGal p) :
    bstN _ (σ • f) = σ • bstN (kummerCocycle p) f :=
  bstN_smul _ σ f

/-- The relation $N \varphi = p \varphi N$ in $B_{st}(\mathcal{O}_{\mathbb{C}_p})$. -/
theorem bstN_bstFrobCp (f : BstGal p) :
    bstN _ (bstFrobCp p f) = bstC _ (p : BcrisCp p) * bstFrobCp p (bstN (kummerCocycle p) f) :=
  bstN_bstFrobBcris _ f

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]

/-- A representation $V$ of $G_{\mathbb{Q}_p}$ is semistable if it is $B_{st}$-admissible, with $B_{st} = B_{st}(\mathcal{O}_{\mathbb{C}_p})$ as in `BstGal`: the rank of $(B_{st} \otimes_{\mathbb{Q}_p} V)^{G_{\mathbb{Q}_p}}$ over $B_{st}^{G_{\mathbb{Q}_p}}$ is $\dim_{\mathbb{Q}_p} V$. -/
def IsSemistableQp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V) : Prop :=
  IsAdmissible (BstGal p) ρ

variable (p) in
/-- The subgroup $G_L$ of $G_{\mathbb{Q}_p}$ of the elements that fix an intermediate field $L$ of $\overline{\mathbb{Q}}_p / \mathbb{Q}_p$. -/
noncomputable def galFixing (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    Subgroup (Field.absoluteGaloisGroup ℚ_[p]) :=
  L.fixingSubgroup

/-- A representation $V$ of $G_{\mathbb{Q}_p}$ is potentially semistable if there is a finite extension $L$ of $\mathbb{Q}_p$ in $\overline{\mathbb{Q}}_p$ such that the restriction of $V$ to $G_L$ is $B_{st}$-admissible. -/
def IsPotentiallySemistableQp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V) :
    Prop :=
  ∃ L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] L ∧
    IsAdmissible (BstGal p)
      (ρ.comp (galFixing p L).subtype)

omit [FiniteDimensional ℚ_[p] V] in
/-- A semistable representation is potentially semistable, with $L = \mathbb{Q}_p$. -/
theorem IsSemistableQp.isPotentiallySemistableQp
    {ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) V} (h : IsSemistableQp ρ) :
    IsPotentiallySemistableQp ρ := by
  refine ⟨⊥, inferInstance, ?_⟩
  refine (isAdmissible_comp_iff (galFixing p ⊥).subtype (fun g => ⟨⟨g, ?_⟩, rfl⟩)
    (fun _ _ => rfl) ρ).2 h
  rw [galFixing, IntermediateField.fixingSubgroup_bot]
  exact Subgroup.mem_top g

/-- If $B_{cris}(\mathcal{O}_{\mathbb{C}_p})$ is not the zero ring, then the trivial representation $\mathbb{Q}_p$ of $G_{\mathbb{Q}_p}$ is semistable. -/
theorem isSemistableQp_trivial_of_nontrivial [Nontrivial (BcrisCp p)] :
    IsSemistableQp (Representation.trivial ℚ_[p] (Field.absoluteGaloisGroup ℚ_[p]) ℚ_[p]) :=
  haveI : Nontrivial (BstGal p) := inferInstanceAs (Nontrivial (Polynomial (BcrisCp p)))
  isAdmissible_trivial _

end Cp

end Langlands.Padic
