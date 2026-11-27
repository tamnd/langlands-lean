/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Local.GL2Reduction

/-!
# The local Langlands correspondence for GL(2) off the supercuspidal representations

Let $K$ be a nonarchimedean local field and let $\mathrm{art}_K$ be a local Artin map. This file proves the hypothesis `Langlands.LocalGL2.NonSupercuspidalLLC` of `Langlands/Local/GL2Reduction.lean` from eight finer published theorems on the principal series of $GL_2(K)$ and from a classification on the Galois side, which this file proves.

On the Galois side, the file proves that each Weil-Deligne representation of dimension 2 that is not irreducible is isomorphic to a model $\varphi_1 \oplus \varphi_2$ with $N = 0$, or to a model with $N \ne 0$ and $\varphi_1 = \varphi_2 \|\cdot\|$. It proves when two models are isomorphic, it computes the dual, the twists, the determinant and the L-factor of the models, and it compares characters of $W_K$ and of $K^\times$ through $\mathrm{art}_K$.

On the automorphic side, the eight inputs are closed hypotheses of type `Prop` with a citation. They speak only about the irreducible subrepresentations of the principal series $\mathrm{Ind}(\chi_1, \chi_2)$ and about supercuspidality. None of them mentions Weil-Deligne representations or the map $e$. The file proves the central character and the twists of the subrepresentations of the principal series.

The bijection `Langlands.LocalGL2.nsEquiv` sends the class of a subrepresentation of $\mathrm{Ind}(\chi_1, \chi_2)$ to the class of the model for $\varphi_i = \chi_i \circ \mathrm{art}_K^{-1}$, with $N \ne 0$ exactly when $\chi_1 = \chi_2 |\cdot|$.

## Main definitions

* `Langlands.LocalGL2.IsStW`, `Langlands.LocalGL2.IsSt`: the Steinberg condition $\varphi_1 = \varphi_2 \|\cdot\|$ and $\chi_1 = \chi_2 |\cdot|$.
* `Langlands.LocalGL2.wdModel`: the model Weil-Deligne representation of dimension 2 for two characters of $W_K$.
* `Langlands.LocalGL2.charLFactorW`: the L-factor of a character of $W_K$.
* `Langlands.LocalGL2.charOfWeil`: the character $\varphi \circ \mathrm{art}_K$ of $K^\times$.
* `Langlands.LocalGL2.PSSubExists`, `Langlands.LocalGL2.PSSubUnique`, `Langlands.LocalGL2.PSSubRigid`, `Langlands.LocalGL2.PSSubSwap`, `Langlands.LocalGL2.NonSupercuspidalExhaustion`, `Langlands.LocalGL2.PSSubNotSupercuspidal`, `Langlands.LocalGL2.PSSubContragredient`, `Langlands.LocalGL2.PSSubLFactor`: the eight published theorems.
* `Langlands.LocalGL2.NonSupercuspidalInputs`: the eight theorems for one field.
* `Langlands.LocalGL2.psParam`, `Langlands.LocalGL2.nsEquiv`: the parameter of a pair of characters and the bijection.
* `Langlands.LocalGL2.GL2OddFineInputs`: the inputs of `Langlands.LocalGL2.GL2OddInputs` with `Langlands.LocalGL2.NonSupercuspidalLLC` replaced by the eight theorems.

## Main results

* `Langlands.LocalGL2.exists_iso_wdModel`: each Weil-Deligne representation of dimension 2 that is not irreducible is isomorphic to a model.
* `Langlands.LocalGL2.iso_wdModel_iff`: two models are isomorphic exactly when the characters are equal, or swapped and not in the Steinberg case.
* `Langlands.LocalGL2.isDual_wdModel`, `Langlands.LocalGL2.isTwist_wdModel`, `Langlands.LocalGL2.det_wdModel`: the dual, the twists and the determinant of a model.
* `Langlands.LocalGL2.lFactor_wdModel`: the L-factor of a model.
* `Langlands.LocalGL2.hasCentralChar_of_hasHom`, `Langlands.LocalGL2.hasHom_twist`: the central character and the twists of a subrepresentation of the principal series.
* `Langlands.LocalGL2.nonSupercuspidalLLC_of_inputs`: the eight theorems give `Langlands.LocalGL2.NonSupercuspidalLLC`.
* `Langlands.localLanglandsGL2_odd_of_fineInputs`: the finer inputs for all $K$ with $p \ne 2$ give `Langlands.LocalLanglandsGL2Odd`.

## Implementation notes

Each input is stated for irreducible admissible representations, so the zero representation is excluded. Each input asks the characters to be smooth. The statement `Langlands.LocalGL2.PSSubRigid` keeps the condition $\chi_1 \chi_2^{-1} \ne |\cdot|^{\pm 1}$ in the swapped case: in the reducible case the Jacquet module of the subrepresentation has dimension one, so the swap does not occur.

The relation `SmoothRep.HasHom` is a nonzero map of representations. For an irreducible source the map is injective (`Langlands.LocalGL2.injective_of_isIrreducible`), so `HasHom` is an embedding.

## Still open

* Proofs of the eight inputs. The files in `Langlands/Smooth` study the principal series, its Jacquet module and its irreducibility criterion for another model of the induced representation. A proof needs a comparison of that model with `Langlands.principalSeries`, the length two result in the reducible case, the cuspidality criterion with matrix coefficients, and the zeta integrals of Godement and Jacquet for $GL_2$.
* A proof of `Langlands.LocalGL2.TameParametrizationGL2` and of the other inputs of `Langlands.LocalGL2.GL2OddInputs`.
* The case $p = 2$.

## References

* C. J. Bushnell and G. Henniart, The local Langlands conjecture for GL(2), Grundlehren 335, chapter 2, sections 9 and 10, section 26 and section 33.
* R. Godement and H. Jacquet, Zeta functions of simple algebras, Lecture Notes in Math. 260.
* H. Jacquet and R. P. Langlands, Automorphic forms on GL(2), Lecture Notes in Math. 114, section 3.
-/

namespace Langlands

open Matrix

universe u

namespace LocalGL2

section Diagonal

/-- The diagonal matrix $\mathrm{diag}(a, b)$ as an element of $GL_2(\mathbb{C})$. -/
def diagGL (a b : ℂˣ) : GL (Fin 2) ℂ where
  val := diagonal ![(a : ℂ), b]
  inv := diagonal ![((a⁻¹ : ℂˣ) : ℂ), ((b⁻¹ : ℂˣ) : ℂ)]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

/-- The matrix of $\mathrm{diag}(a, b)$. -/
theorem val_diagGL (a b : ℂˣ) : ((diagGL a b : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    diagonal ![(a : ℂ), b] :=
  rfl

/-- The matrix of $\mathrm{diag}(a, b)^{-1}$. -/
theorem val_diagGL_inv (a b : ℂˣ) : (((diagGL a b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    diagonal ![((a⁻¹ : ℂˣ) : ℂ), ((b⁻¹ : ℂˣ) : ℂ)] :=
  rfl

variable {G : Type*} [Group G]

/-- The homomorphism $g \mapsto \mathrm{diag}(\varphi_1(g), \varphi_2(g))$ given by two characters. -/
def diagHom (φ₁ φ₂ : G →* ℂˣ) : G →* GL (Fin 2) ℂ where
  toFun g := diagGL (φ₁ g) (φ₂ g)
  map_one' := by
    apply Units.ext
    rw [val_diagGL, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mul, val_diagGL, val_diagGL, val_diagGL, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp

/-- The matrix of $\mathrm{diag}(\varphi_1(g), \varphi_2(g))$. -/
theorem val_diagHom (φ₁ φ₂ : G →* ℂˣ) (g : G) :
    ((diagHom φ₁ φ₂ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = diagonal ![(φ₁ g : ℂ), φ₂ g] :=
  rfl

/-- A diagonal matrix of size 2 is semisimple. -/
theorem isSemisimple_diagonal (a b : ℂ) : Module.End.IsSemisimple (toLin' (diagonal ![a, b])) := by
  by_cases h : a = b
  · subst h
    have : toLin' (diagonal ![a, a]) = a • LinearMap.id := by
      refine LinearMap.ext fun v => funext fun i => ?_
      fin_cases i <;> simp [mulVec_diagonal]
    rw [this]
    exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id
  · open Polynomial in
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := (X - C a) * (X - C b))
    · exact (separable_X_sub_C.mul separable_X_sub_C
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 h).isUnit)).squarefree
    · simp only [map_mul, map_sub, aeval_X, aeval_C]
      refine LinearMap.ext fun v => funext fun i => ?_
      fin_cases i <;> simp [mulVec_diagonal, Module.algebraMap_end_apply]

/-- **A semisimple unipotent matrix is diagonal.** If a semisimple matrix of size 2 is upper triangular with equal diagonal entries, then it is a scalar matrix. -/
theorem upper_eq_zero_of_isSemisimple {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hs : Module.End.IsSemisimple (toLin' M)) (h10 : M 1 0 = 0) (hd : M 0 0 = M 1 1) : M 0 1 = 0 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![0, M 0 1; 0, 0] with hA
  have hMA : toLin' A = toLin' M - algebraMap ℂ (Module.End ℂ (Fin 2 → ℂ)) (M 0 0) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    fin_cases i <;> simp [hA, Module.algebraMap_end_apply, mulVec, dotProduct, Fin.sum_univ_two,
      h10, hd]
  have hss : Module.End.IsSemisimple (toLin' A) :=
    hMA ▸ Module.End.isSemisimple_sub_algebraMap_iff.2 hs
  have hnil : IsNilpotent (toLin' A) := ⟨2, by
    rw [pow_two, Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
    have : A * A = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA]
    rw [this, map_zero]⟩
  have h0 : A = 0 := Matrix.toLin'.injective
    ((Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss).trans (map_zero _).symm)
  have := congrFun (congrFun h0 0) 1
  simpa [hA] using this

/-- The diagonal entries of an upper triangular matrix in $GL_2(\mathbb{C})$ are not zero. -/
theorem diag_ne_zero_of_upper (g : GL (Fin 2) ℂ) (h : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    (i : Fin 2) : (g : Matrix (Fin 2) (Fin 2) ℂ) i i ≠ 0 := by
  have hd := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_fin_two, h, mul_zero, sub_zero] at hd
  fin_cases i
  · exact left_ne_zero_of_mul hd
  · exact right_ne_zero_of_mul hd

/-- For a homomorphism $r$ to the upper triangular matrices of $GL_2(\mathbb{C})$, the diagonal entry $g \mapsto r(g)_{ii}$ as a character. -/
noncomputable def upperChar (r : G →* GL (Fin 2) ℂ) (h : ∀ g, (r g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    (i : Fin 2) : G →* ℂˣ where
  toFun g := Units.mk0 ((r g : Matrix (Fin 2) (Fin 2) ℂ) i i) (diag_ne_zero_of_upper _ (h g) i)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [h]

/-- The value of the diagonal character. -/
theorem upperChar_apply (r : G →* GL (Fin 2) ℂ) (h : ∀ g, (r g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    (i : Fin 2) (g : G) : (upperChar r h i g : ℂ) = (r g : Matrix (Fin 2) (Fin 2) ℂ) i i :=
  rfl

end Diagonal

section Conj

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The conjugate $(g r g^{-1}, g N g^{-1})$ of a Weil-Deligne representation by $g \in GL_m(\mathbb{C})$. -/
noncomputable def conjBy {m : ℕ} (ρ : WeilDeligneRep K m) (g : GL (Fin m) ℂ) : WeilDeligneRep K m where
  r := (MulAut.conj g).toMonoidHom.comp ρ.r
  isOpen_ker := by
    refine Subgroup.isOpen_mono (fun w hw => ?_) ρ.isOpen_ker
    rw [MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  N := (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
  isNilpotent := by
    obtain ⟨n, hn⟩ := ρ.isNilpotent
    exact ⟨n, by rw [Units.conj_pow, hn, mul_zero, zero_mul]⟩
  conj w := by
    have h := ρ.conj w
    simp only [mul_assoc] at h
    change ((g * ρ.r w * g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) *
        ((g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) *
        (((g * ρ.r w * g⁻¹)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = _
    rw [show (g * ρ.r w * g⁻¹)⁻¹ = g * (ρ.r w)⁻¹ * g⁻¹ by group]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc ρ.N, ← mul_assoc (ρ.r w : Matrix (Fin m) (Fin m) ℂ), h, Matrix.smul_mul,
      Matrix.mul_smul]
  semisimple w := by
    have hGi : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (g : Matrix (Fin m) (Fin m) ℂ) = 1 :=
      Units.inv_mul g
    refine (LinearEquiv.isSemisimple_iff _ _ (Matrix.toLin'OfInv hGi (Units.mul_inv g)) ?_).1
      (ρ.semisimple w)
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, toLin'_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, mul_assoc]
    change (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ ((ρ.r w : Matrix (Fin m) (Fin m) ℂ) *ᵥ v) = _ *ᵥ
      ((g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v)
    rw [mulVec_mulVec, mulVec_mulVec, mul_assoc, mul_assoc, hGi, mul_one]

/-- A Weil-Deligne representation is isomorphic to each of its conjugates. -/
theorem iso_conjBy {m : ℕ} (ρ : WeilDeligneRep K m) (g : GL (Fin m) ℂ) : ρ.Iso (conjBy ρ g) :=
  ⟨g, fun _ => rfl, rfl⟩

/-- The class of a conjugate is the class of the representation. -/
theorem mk_conjBy {m : ℕ} (ρ : WeilDeligneRep K m) (g : GL (Fin m) ℂ) :
    WDIso.mk (conjBy ρ g) = WDIso.mk ρ :=
  (Quotient.sound (iso_conjBy ρ g)).symm

/-- If $g$ conjugates $\rho$ to $\rho'$, then $g$ maps $(V^{I_K})_{N = 0}$ of $\rho$ into that of $\rho'$. -/
theorem mulVec_mem_lSpace {m : ℕ} {ρ ρ' : WeilDeligneRep K m} {g : GL (Fin m) ℂ}
    (hr : ∀ w, ρ'.r w = g * ρ.r w * g⁻¹)
    (hN : ρ'.N = (g : Matrix (Fin m) (Fin m) ℂ) * ρ.N * ((g⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ))
    {v : Fin m → ℂ} (hv : v ∈ ρ.lSpace) : (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v ∈ ρ'.lSpace := by
  have hGi : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (g : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Units.inv_mul g
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hN, mulVec_mulVec, mul_assoc, hGi, mul_one, ← mulVec_mulVec, hv.1, mulVec_zero]
  · rw [hr, Units.val_mul, Units.val_mul, mulVec_mulVec, mul_assoc, hGi, mul_one, ← mulVec_mulVec,
      hv.2 i hi]

/-- **The L-factor is invariant under isomorphism.** If $\rho \cong \rho'$, then $L(s, \rho) = L(s, \rho')$. The matrix $g$ of the isomorphism maps $(V^{I_K})_{N = 0}$ of $\rho$ onto that of $\rho'$ and intertwines the actions of the geometric Frobenius. -/
theorem lFactor_eq_of_iso {m : ℕ} {ρ ρ' : WeilDeligneRep K m} (h : ρ.Iso ρ') :
    ρ'.lFactor = ρ.lFactor := by
  obtain ⟨g, hr, hN⟩ := h
  have hGG : (g : Matrix (Fin m) (Fin m) ℂ) * ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Units.mul_inv g
  have hGi : ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (g : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Units.inv_mul g
  have hr' : ∀ w, ρ.r w = g⁻¹ * ρ'.r w * g⁻¹⁻¹ := fun w => by rw [hr w]; group
  have hN' : ρ.N = ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * ρ'.N *
      ((g⁻¹⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    rw [hN, inv_inv]
    simp only [mul_assoc, hGi, mul_one, Units.inv_mul_cancel_left]
  let e : ρ.lSpace ≃ₗ[ℂ] ρ'.lSpace := LinearEquiv.ofLinearMap
    ((toLin' (g : Matrix (Fin m) (Fin m) ℂ)).restrict fun v hv => mulVec_mem_lSpace hr hN hv)
    ((toLin' ((g⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)).restrict
      fun v hv => mulVec_mem_lSpace hr' hN' hv)
    (LinearMap.ext fun v => Subtype.ext (by
      change (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ (((g⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ) *ᵥ v.1) = v.1
      rw [mulVec_mulVec, hGG, one_mulVec]))
    (LinearMap.ext fun v => Subtype.ext (by
      change ((g⁻¹ : GL (Fin m) ℂ) : Matrix _ _ ℂ) *ᵥ ((g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v.1) = v.1
      rw [mulVec_mulVec, hGi, one_mulVec]))
  have hF : ∀ v : ρ.lSpace, e (ρ.frobOnLSpace v) = ρ'.frobOnLSpace (e v) := fun v => by
    apply Subtype.ext
    change (g : Matrix (Fin m) (Fin m) ℂ) *ᵥ ((ρ.r (geomFrob K) : Matrix (Fin m) (Fin m) ℂ) *ᵥ v) =
      (ρ'.r (geomFrob K) : Matrix (Fin m) (Fin m) ℂ) *ᵥ ((g : Matrix (Fin m) (Fin m) ℂ) *ᵥ v)
    rw [hr]
    simp only [Units.val_mul, mulVec_mulVec, mul_assoc, hGi, mul_one]
  funext s
  have key : (1 - ((residueCard K : ℂ) ^ (-s)) • ρ'.frobOnLSpace) =
      (e : ρ.lSpace →ₗ[ℂ] ρ'.lSpace) ∘ₗ (1 - ((residueCard K : ℂ) ^ (-s)) • ρ.frobOnLSpace) ∘ₗ
        (e.symm : ρ'.lSpace →ₗ[ℂ] ρ.lSpace) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hF, LinearEquiv.apply_symm_apply]
  rw [WeilDeligneRep.lFactor, WeilDeligneRep.lFactor, key, LinearMap.det_conj]

end Conj

section Model

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The norm $w \mapsto |w|$ as a character of $W_K$. -/
noncomputable def normChar : WeilGroup K →* ℂˣ where
  toFun w := Units.mk0 (weilNorm K w) (weilNorm_ne_zero K w)
  map_one' := by
    apply Units.ext
    simp [weilNorm]
  map_mul' a b := by
    apply Units.ext
    have hq : (residueCard K : ℂ) ≠ 0 := by
      have : 0 < residueCard K := Nat.card_pos
      exact_mod_cast this.ne'
    simp only [weilNorm, map_mul, toAdd_mul, neg_add, Units.val_mk0, Units.val_mul]
    rw [zpow_add₀ hq]

/-- The value of the norm character. -/
theorem normChar_apply (w : WeilGroup K) : (normChar K w : ℂ) = weilNorm K w :=
  rfl

/-- The norm of the fixed geometric Frobenius element is $q^{-1}$. -/
theorem weilNorm_geomFrob : weilNorm K (geomFrob K) = ((residueCard K : ℂ))⁻¹ := by
  have h : WeilGroup.degree K (geomFrob K) = Multiplicative.ofAdd 1 :=
    (WeilGroup.degree_eq_one_iff K _).2 (Classical.choose_spec (WeilGroup.exists_isGeometricFrobenius K))
  rw [weilNorm, h, toAdd_ofAdd, _root_.zpow_neg, zpow_one]

/-- The number $q^{-1}$ is not a root of unity of order 1 or 2: $q^{-1} \ne 1$ and $q^{-2} \ne 1$. -/
theorem weilNorm_geomFrob_ne_one :
    weilNorm K (geomFrob K) ≠ 1 ∧ weilNorm K (geomFrob K) * weilNorm K (geomFrob K) ≠ 1 := by
  rw [weilNorm_geomFrob]
  have hq := LocalGL1.one_lt_residueCard (K := K)
  constructor
  · intro h
    rw [inv_eq_one, Nat.cast_eq_one] at h
    omega
  · intro h
    rw [← mul_inv, inv_eq_one, ← Nat.cast_mul, Nat.cast_eq_one, mul_eq_one] at h
    omega

/-- The Steinberg condition on the Galois side: $\varphi_1 = \varphi_2 |\cdot|$. -/
def IsStW (φ₁ φ₂ : WeilGroup K →* ℂˣ) : Prop :=
  ∀ w, (φ₁ w : ℂ) = φ₂ w * weilNorm K w

/-- The two Steinberg conditions $\varphi_1 = \varphi_2 |\cdot|$ and $\varphi_2 = \varphi_1 |\cdot|$ do not hold together. -/
theorem not_isStW_and (φ₁ φ₂ : WeilGroup K →* ℂˣ) : ¬(IsStW K φ₁ φ₂ ∧ IsStW K φ₂ φ₁) := by
  rintro ⟨h1, h2⟩
  have e1 := h1 (geomFrob K)
  rw [h2 (geomFrob K), mul_assoc] at e1
  have h0 : (φ₁ (geomFrob K) : ℂ) ≠ 0 := Units.ne_zero _
  exact (weilNorm_geomFrob_ne_one K).2 (mul_eq_left₀ h0 |>.1 e1.symm)

open scoped Classical in
/-- **The model representations.** The Weil-Deligne representation with $r = \varphi_1 \oplus \varphi_2$ and with $N$ the matrix unit $E_{12}$ if $\varphi_1 = \varphi_2 |\cdot|$, and $N = 0$ otherwise. For $N = E_{12}$ this is $\mathrm{Sp}(2) \otimes \varphi_2 |\cdot|^{1/2}$. -/
noncomputable def wdModel (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ : IsOpen (φ₁.ker : Set (WeilGroup K)))
    (h₂ : IsOpen (φ₂.ker : Set (WeilGroup K))) : WeilDeligneRep K 2 where
  r := diagHom φ₁ φ₂
  isOpen_ker := by
    refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) (fun w hw => ?_) (h₁.inter h₂)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hw
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [val_diagHom, hw.1, hw.2, Units.val_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  N := if IsStW K φ₁ φ₂ then single 0 1 1 else 0
  isNilpotent := by
    refine ⟨2, ?_⟩
    split_ifs
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, single_apply]
    · rw [pow_two, mul_zero]
  conj w := by
    split_ifs with h
    · change diagonal ![(φ₁ w : ℂ), φ₂ w] * single 0 1 1 *
          diagonal ![(((φ₁ w)⁻¹ : ℂˣ) : ℂ), (((φ₂ w)⁻¹ : ℂˣ) : ℂ)] = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_diagonal, h w, mul_comm _ (weilNorm K w)]
    · simp
  semisimple w := isSemisimple_diagonal _ _

variable {K}

/-- The matrix of $r(w)$ for a model representation. -/
theorem wdModel_r (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) (w : WeilGroup K) :
    ((wdModel K φ₁ φ₂ h₁ h₂).r w : Matrix (Fin 2) (Fin 2) ℂ) = diagonal ![(φ₁ w : ℂ), φ₂ w] :=
  rfl

open scoped Classical in
/-- The matrix $N$ of a model representation. -/
theorem wdModel_N (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) :
    (wdModel K φ₁ φ₂ h₁ h₂).N = if IsStW K φ₁ φ₂ then single 0 1 1 else 0 :=
  rfl

/-- If $M_{21} = 0$, then the line spanned by the first basis vector is stable under $M$. -/
theorem span_single_le_comap (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M 1 0 = 0) :
    Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} ≤
      (Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)}).comap (toLin' M) := by
  rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap,
    toLin'_apply, Submodule.mem_span_singleton]
  refine ⟨M 0 0, funext fun i => ?_⟩
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h]

/-- **A model representation is not irreducible.** The line spanned by the first basis vector is stable. -/
theorem not_isIrreducible_wdModel (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) :
    ¬(wdModel K φ₁ φ₂ h₁ h₂).IsIrreducible := by
  classical
  rintro ⟨-, h⟩
  rcases h (Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)})
    (fun w => span_single_le_comap _ (by simp [wdModel_r]))
    (span_single_le_comap _ (by rw [wdModel_N]; split_ifs <;> simp)) with h0 | h0
  · rw [Submodule.span_singleton_eq_bot] at h0
    exact one_ne_zero (congrFun h0 0)
  · have : (Pi.single 1 1 : Fin 2 → ℂ) ∈ Submodule.span ℂ {(Pi.single 0 1 : Fin 2 → ℂ)} :=
      h0 ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    have := congrFun hc 1
    simp at this

/-- The first column of a matrix of size 2. -/
theorem mulVec_single_zero (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (M *ᵥ (Pi.single 0 1 : Fin 2 → ℂ)) i = M i 0 := by
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- Each nonzero vector of $\mathbb{C}^2$ is the first column of a matrix in $GL_2(\mathbb{C})$. -/
theorem exists_mulVec_single_eq {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ∃ P : GL (Fin 2) ℂ, (P : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; v 1, 0] (by simp [det_fin_two, h1]),
      funext fun i => ?_⟩
    rw [mulVec_single_zero]
    fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, h0]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [det_fin_two, h0]),
      funext fun i => ?_⟩
    rw [mulVec_single_zero]
    fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- A stable subspace that is neither $0$ nor $\mathbb{C}^2$ is a line. -/
theorem exists_eq_span_of_ne {W : Submodule ℂ (Fin 2 → ℂ)} (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ W = Submodule.span ℂ {v} := by
  obtain ⟨v, hvW, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  refine ⟨v, hv, (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hvW)
    ?_).symm⟩
  have hlt := Submodule.finrank_lt h1
  rw [Module.finrank_fin_fun, finrank_span_singleton hv] at *
  omega

/-- **A representation that is not irreducible is conjugate to an upper triangular one.** If $\rho$ of dimension 2 is not irreducible, then $\rho$ is isomorphic to a representation with $r(w)_{21} = 0$ for each $w$ and $N_{21} = 0$. -/
theorem exists_iso_upper (ρ : WeilDeligneRep K 2) (h : ¬ρ.IsIrreducible) :
    ∃ ρ' : WeilDeligneRep K 2, ρ.Iso ρ' ∧ (∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∧
      ρ'.N 1 0 = 0 := by
  have hW : ∃ W : Submodule ℂ (Fin 2 → ℂ),
      (∀ w, W ≤ W.comap (toLin' (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ))) ∧ W ≤ W.comap (toLin' ρ.N) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hc
    refine h ⟨by norm_num, fun W hr hN => ?_⟩
    by_cases hb : W = ⊥
    · exact Or.inl hb
    · exact Or.inr (by_contra fun ht => hc ⟨W, hr, hN, hb, ht⟩)
  obtain ⟨W, hr, hN, h0, h1⟩ := hW
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_ne h0 h1
  obtain ⟨P, hP⟩ := exists_mulVec_single_eq hv
  have hPi : ((P⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = Pi.single 0 1 := by
    rw [← hP, mulVec_mulVec, Units.inv_mul, one_mulVec]
  have key : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (toLin' M) →
        (((P⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * M * (P : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
          = 0 := by
    intro M hM
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (hM (Submodule.mem_span_singleton_self v))
    rw [toLin'_apply] at hc
    rw [← mulVec_single_zero (((P⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * M *
      (P : Matrix (Fin 2) (Fin 2) ℂ)), ← mulVec_mulVec, hP, ← mulVec_mulVec, ← hc, mulVec_smul, hPi]
    simp
  refine ⟨conjBy ρ P⁻¹, iso_conjBy ρ P⁻¹, fun w => ?_, ?_⟩
  · change (((P⁻¹ * ρ.r w * P⁻¹⁻¹ : GL (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
    rw [inv_inv, Units.val_mul, Units.val_mul]
    exact key _ (hr w)
  · change (((P⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ρ.N *
      ((P⁻¹⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = 0
    rw [inv_inv]
    exact key _ hN

/-- **An upper triangular nilpotent matrix of size 2 is a multiple of $E_{12}$.** -/
theorem eq_smul_single_of_isNilpotent {N : Matrix (Fin 2) (Fin 2) ℂ} (h10 : N 1 0 = 0)
    (hN : IsNilpotent N) : N = N 0 1 • single 0 1 1 := by
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have hN2 : IsNilpotent (N * N) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hk, zero_pow two_ne_zero]⟩
  have ht2 := (Matrix.isNilpotent_trace_of_isNilpotent hN2).eq_zero
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, mul_zero,
    add_zero, zero_add] at ht ht2
  have ha : N 0 0 = 0 := by
    have hd : N 1 1 = -N 0 0 := by linear_combination ht
    rw [hd] at ht2
    have : N 0 0 * N 0 0 = 0 := by linear_combination ht2 / 2
    exact mul_self_eq_zero.1 this
  have hd : N 1 1 = 0 := by linear_combination ht - ha
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hd, h10]

/-- The matrix $\begin{pmatrix} 1 & -t \\ 0 & 1 \end{pmatrix}$ in $GL_2(\mathbb{C})$. -/
def upperGL (t : ℂ) : GL (Fin 2) ℂ where
  val := !![1, -t; 0, 1]
  inv := !![1, t; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ in $GL_2(\mathbb{C})$. -/
def swapGL : GL (Fin 2) ℂ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The conjugate of an upper triangular matrix by an upper unipotent matrix. -/
theorem conj_upperGL_apply (t : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M 1 0 = 0) :
    !![1, -t; 0, 1] * M * !![1, t; 0, 1] = !![M 0 0, M 0 0 * t + M 0 1 - t * M 1 1; 0, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, h]
  ring

/-- **Upper triangular semisimple representations commute.** If $r$ has values in the upper triangular matrices and each $r(w)$ is semisimple, then $r(w)$ and $r(w')$ commute. The commutator $r(w w' w^{-1} w'^{-1})$ is upper triangular with diagonal $(1, 1)$, so it is $1$ by `upper_eq_zero_of_isSemisimple`. -/
theorem commute_of_upper (ρ : WeilDeligneRep K 2) (hr : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    (w w' : WeilGroup K) : ρ.r w * ρ.r w' = ρ.r w' * ρ.r w := by
  set c := w * w' * w⁻¹ * w'⁻¹ with hc
  have hd : ∀ i, (ρ.r c : Matrix (Fin 2) (Fin 2) ℂ) i i = 1 := by
    intro i
    rw [← upperChar_apply ρ.r hr i]
    simp [hc, mul_comm (upperChar ρ.r hr i w), mul_assoc]
  have h01 := upper_eq_zero_of_isSemisimple (ρ.semisimple c) (hr c) ((hd 0).trans (hd 1).symm)
  have h1 : ρ.r c = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, h01, hr c]
  rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := mul_inv_eq_one.1 h1
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

/-- **Upper triangular representations are diagonalizable.** If $r$ has values in the upper triangular matrices and $N = n E_{12}$, then $\rho$ is isomorphic to a representation with diagonal $r$ and the same $N$. If the two diagonal characters are equal, then each $r(w)$ is a scalar by semisimplicity. Otherwise choose $w_0$ with distinct diagonal entries and conjugate $r(w_0)$ to a diagonal matrix by an upper unipotent matrix $u$; then each $r(w)$ commutes with $r(w_0)$, so it is diagonal. The matrix $u$ commutes with $E_{12}$. -/
theorem exists_iso_diag (ρ : WeilDeligneRep K 2)
    (hr : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) {n : ℂ} (hN : ρ.N = n • single 0 1 1) :
    ∃ ρ' : WeilDeligneRep K 2, ρ.Iso ρ' ∧
      (∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∧
      ρ'.N = n • single 0 1 1 := by
  by_cases hA : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  · exact ⟨ρ, WeilDeligneRep.setoid.iseqv.refl ρ, fun w =>
      ⟨upper_eq_zero_of_isSemisimple (ρ.semisimple w) (hr w) (hA w), hr w⟩, hN⟩
  push Not at hA
  obtain ⟨w₀, hw₀⟩ := hA
  set M₀ := (ρ.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) with hM₀
  set t := M₀ 0 1 / (M₀ 1 1 - M₀ 0 0) with ht
  have hsub : M₀ 1 1 - M₀ 0 0 ≠ 0 := sub_ne_zero.2 (Ne.symm hw₀)
  set ρ' := conjBy ρ (upperGL t) with hρ'
  have hval : ∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 0, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * t +
        (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 1 - t * (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 1;
        0, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 1] := fun w =>
    conj_upperGL_apply t _ (hr w)
  have hr' : ∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    intro w
    rw [hval]
    simp
  have hdiag : ∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ∧
      (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    intro w
    rw [hval]
    simp
  have h0 : (ρ'.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    rw [hval]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    rw [← hM₀, ht]
    field_simp
    ring
  refine ⟨ρ', iso_conjBy ρ _, fun w => ⟨?_, hr' w⟩, ?_⟩
  · have hc := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
      (commute_of_upper ρ' hr' w w₀)
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, mul_zero,
      zero_mul, zero_add, add_zero] at hc
    have hne : (ρ'.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - (ρ'.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := by
      rw [(hdiag w₀).1, (hdiag w₀).2]
      exact hsub
    have : (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 1 *
        ((ρ'.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - (ρ'.r w₀ : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 0 := by
      linear_combination hc
    exact (mul_eq_zero.1 this).resolve_right hne
  · change !![1, -t; 0, 1] * ρ.N * !![1, t; 0, 1] = _
    rw [hN, Matrix.mul_smul, Matrix.smul_mul, conj_upperGL_apply t _ (by simp)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The diagonal characters of an upper triangular Weil-Deligne representation have open kernels. -/
theorem isOpen_ker_upperChar (ρ : WeilDeligneRep K 2)
    (hr : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) (i : Fin 2) :
    IsOpen ((upperChar ρ.r hr i).ker : Set (WeilGroup K)) := by
  refine Subgroup.isOpen_mono (fun w hw => ?_) ρ.isOpen_ker
  rw [MonoidHom.mem_ker] at hw ⊢
  apply Units.ext
  rw [upperChar_apply, hw]
  simp

/-- **Diagonal representations are models.** If $r = \mathrm{diag}(\alpha, \delta)$ and $N = n E_{12}$, then $\rho$ is isomorphic to a model representation. If $n \ne 0$, then $\alpha = \delta |\cdot|$ and a diagonal matrix conjugates $N$ to $E_{12}$. If $n = 0$ and $\alpha = \delta |\cdot|$, then the swap matrix conjugates $\rho$ to the model of $(\delta, \alpha)$. -/
theorem exists_iso_wdModel_of_diag (ρ : WeilDeligneRep K 2)
    (hd : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    {n : ℂ} (hN : ρ.N = n • single 0 1 1) :
    ∃ (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ : IsOpen (φ₁.ker : Set (WeilGroup K)))
      (h₂ : IsOpen (φ₂.ker : Set (WeilGroup K))), ρ.Iso (wdModel K φ₁ φ₂ h₁ h₂) := by
  classical
  have hr : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := fun w => (hd w).2
  set α := upperChar ρ.r hr 0
  set δ := upperChar ρ.r hr 1
  have hα := isOpen_ker_upperChar ρ hr 0
  have hδ := isOpen_ker_upperChar ρ hr 1
  have hrd : ∀ w, (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ) = diagonal ![(α w : ℂ), δ w] := by
    intro w
    ext i j
    fin_cases i <;> fin_cases j <;> simp [α, δ, upperChar_apply, hd w]
  by_cases hn : n = 0
  · subst hn
    rw [zero_smul] at hN
    by_cases hS : IsStW K α δ
    · have hS' : ¬IsStW K δ α := fun h => not_isStW_and K α δ ⟨hS, h⟩
      refine ⟨δ, α, hδ, hα, swapGL, fun w => ?_, ?_⟩
      · apply Units.ext
        rw [Units.val_mul, Units.val_mul, hrd]
        change diagonal ![(δ w : ℂ), α w] = !![0, 1; 1, 0] * _ * !![0, 1; 1, 0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
      · rw [wdModel_N, hN]
        simp [hS']
    · refine ⟨α, δ, hα, hδ, 1, fun w => ?_, ?_⟩
      · apply Units.ext
        rw [one_mul, inv_one, mul_one, hrd]
        rfl
      · rw [wdModel_N, hN]
        simp [hS]
  · have hS : IsStW K α δ := by
      intro w
      have h := congrFun (congrFun (ρ.conj w) 0) 1
      rw [← map_inv, hrd, hrd, hN, map_inv, map_inv] at h
      simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal, single_apply] at h
      have hδ0 : (δ w : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at h
      linear_combination h
    refine ⟨α, δ, hα, hδ, diagGL 1 (Units.mk0 n hn), fun w => ?_, ?_⟩
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hrd]
      change diagonal ![(α w : ℂ), δ w] = diagonal ![((1 : ℂˣ) : ℂ), (Units.mk0 n hn : ℂ)] * _ *
        diagonal ![(((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ), (((Units.mk0 n hn)⁻¹ : ℂˣ) : ℂ)]
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [mul_inv_cancel_right₀ hn, mul_comm n]
    · rw [wdModel_N, hN]
      simp only [hS, ite_true]
      change _ = diagonal ![((1 : ℂˣ) : ℂ), (Units.mk0 n hn : ℂ)] * _ *
        diagonal ![(((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ), (((Units.mk0 n hn)⁻¹ : ℂˣ) : ℂ)]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_diagonal, hn]

/-- **The classification of the Weil-Deligne representations of dimension 2 that are not irreducible.** Each such representation is isomorphic to a model representation `wdModel`: either $\varphi_1 \oplus \varphi_2$ with $N = 0$ and $\varphi_1 \ne \varphi_2 |\cdot|$, or $\mathrm{Sp}(2) \otimes \chi$ with $\varphi_1 = \varphi_2 |\cdot|$ and $N = E_{12}$. -/
theorem exists_iso_wdModel (ρ : WeilDeligneRep K 2) (h : ¬ρ.IsIrreducible) :
    ∃ (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ : IsOpen (φ₁.ker : Set (WeilGroup K)))
      (h₂ : IsOpen (φ₂.ker : Set (WeilGroup K))), ρ.Iso (wdModel K φ₁ φ₂ h₁ h₂) := by
  obtain ⟨ρ₁, h₁, hr₁, hN₁⟩ := exists_iso_upper ρ h
  obtain ⟨ρ₂, h₂, hd₂, hN₂⟩ := exists_iso_diag ρ₁ hr₁ (eq_smul_single_of_isNilpotent hN₁ ρ₁.isNilpotent)
  obtain ⟨φ₁, φ₂, k₁, k₂, h₃⟩ := exists_iso_wdModel_of_diag ρ₂ hd₂ hN₂
  exact ⟨φ₁, φ₂, k₁, k₂, WeilDeligneRep.setoid.iseqv.trans h₁ (WeilDeligneRep.setoid.iseqv.trans h₂ h₃)⟩

/-- An isomorphism $g$ from $\rho$ to $\rho'$ gives $r'(w) g = g r(w)$ and $N' g = g N$. -/
theorem mul_eq_of_iso {ρ ρ' : WeilDeligneRep K 2} (h : ρ.Iso ρ') :
    ∃ g : GL (Fin 2) ℂ, (∀ w, (ρ'.r w : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (ρ.r w : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      ρ'.N * (g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) * ρ.N := by
  obtain ⟨g, hr, hN⟩ := h
  refine ⟨g, fun w => ?_, ?_⟩
  · rw [hr w, Units.val_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [hN, mul_assoc, Units.inv_mul, mul_one]

/-- Two characters are equal if they agree after multiplication by a nonzero number. -/
theorem char_eq_of_mul_eq {φ ψ : WeilGroup K →* ℂˣ} {c : ℂ} (hc : c ≠ 0)
    (h : ∀ w, (ψ w : ℂ) * c = c * φ w) : ψ = φ :=
  MonoidHom.ext fun w => Units.ext (mul_right_cancel₀ hc (by rw [h w, mul_comm]))

/-- If neither Steinberg condition holds, then the models of $(\varphi_1, \varphi_2)$ and $(\varphi_2, \varphi_1)$ are isomorphic by the swap matrix. -/
theorem iso_wdModel_swap (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) (hφ : ¬IsStW K φ₁ φ₂)
    (hψ : ¬IsStW K φ₂ φ₁) : (wdModel K φ₁ φ₂ h₁ h₂).Iso (wdModel K φ₂ φ₁ h₂ h₁) := by
  classical
  refine ⟨swapGL, fun w => ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change diagonal ![(φ₂ w : ℂ), φ₁ w] = !![0, 1; 1, 0] * diagonal ![(φ₁ w : ℂ), φ₂ w] *
      !![0, 1; 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
  · rw [wdModel_N, wdModel_N]
    simp [hφ, hψ]

/-- **The isomorphisms between model representations.** Two model representations are isomorphic exactly when the pairs of characters are equal, or when they differ by the swap and neither Steinberg condition holds. -/
theorem iso_wdModel_iff (φ₁ φ₂ ψ₁ ψ₂ : WeilGroup K →* ℂˣ) (h₁ h₂ k₁ k₂) :
    (wdModel K φ₁ φ₂ h₁ h₂).Iso (wdModel K ψ₁ ψ₂ k₁ k₂) ↔
      (ψ₁ = φ₁ ∧ ψ₂ = φ₂) ∨ (ψ₁ = φ₂ ∧ ψ₂ = φ₁ ∧ ¬IsStW K φ₁ φ₂ ∧ ¬IsStW K φ₂ φ₁) := by
  classical
  constructor
  · intro h
    obtain ⟨g, hr, hN⟩ := mul_eq_of_iso h
    set G := (g : Matrix (Fin 2) (Fin 2) ℂ) with hG
    have hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det g).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply, det_fin_two] at this
    have hrel : ∀ w i j, (![(ψ₁ w : ℂ), ψ₂ w] i) * G i j = G i j * ![(φ₁ w : ℂ), φ₂ w] j := by
      intro w i j
      have := congrFun (congrFun (hr w) i) j
      rwa [wdModel_r, wdModel_r, diagonal_mul, mul_diagonal] at this
    rw [wdModel_N, wdModel_N] at hN
    by_cases hφ : IsStW K φ₁ φ₂ <;> by_cases hψ : IsStW K ψ₁ ψ₂ <;>
      simp only [hφ, hψ, ite_true, ite_false, zero_mul, mul_zero] at hN
    · have h10 : G 1 0 = 0 := by
        have := congrFun (congrFun hN 0) 0
        simpa [Matrix.mul_apply, Fin.sum_univ_two, single_apply] using this
      rw [h10, mul_zero, sub_zero] at hdet
      left
      exact ⟨char_eq_of_mul_eq (left_ne_zero_of_mul hdet) fun w => by simpa using hrel w 0 0,
        char_eq_of_mul_eq (right_ne_zero_of_mul hdet) fun w => by simpa using hrel w 1 1⟩
    · exfalso
      have a : G 0 0 = 0 := by
        have := congrFun (congrFun hN 0) 1
        simp [Matrix.mul_apply, single_apply] at this
        exact this.symm
      have b : G 1 0 = 0 := by
        have := congrFun (congrFun hN 1) 1
        simp [Matrix.mul_apply, single_apply] at this
        exact this.symm
      exact hdet (by rw [a, b]; ring)
    · exfalso
      have a : G 1 0 = 0 := by
        have := congrFun (congrFun hN 0) 0
        simp [Matrix.mul_apply, single_apply] at this
        exact this
      have b : G 1 1 = 0 := by
        have := congrFun (congrFun hN 0) 1
        simp [Matrix.mul_apply, single_apply] at this
        exact this
      exact hdet (by rw [a, b]; ring)
    · by_cases hd : G 0 0 * G 1 1 = 0
      · replace hdet : G 0 1 * G 1 0 ≠ 0 := fun h0 => hdet (by rw [hd, h0, sub_zero])
        have e₁ : ψ₁ = φ₂ :=
          char_eq_of_mul_eq (left_ne_zero_of_mul hdet) fun w => by simpa using hrel w 0 1
        have e₂ : ψ₂ = φ₁ :=
          char_eq_of_mul_eq (right_ne_zero_of_mul hdet) fun w => by simpa using hrel w 1 0
        subst e₁ e₂
        exact Or.inr ⟨rfl, rfl, hφ, hψ⟩
      · left
        exact ⟨char_eq_of_mul_eq (left_ne_zero_of_mul hd) fun w => by simpa using hrel w 0 0,
          char_eq_of_mul_eq (right_ne_zero_of_mul hd) fun w => by simpa using hrel w 1 1⟩
  · rintro (⟨h, h'⟩ | ⟨h, h', hφ, hψ⟩)
    · subst h h'
      exact WeilDeligneRep.setoid.iseqv.refl _
    · subst h h'
      exact iso_wdModel_swap _ _ _ _ hφ hψ

/-- The kernel of $\varphi^{-1}$ is open if the kernel of $\varphi$ is open. -/
theorem isOpen_ker_inv {φ : WeilGroup K →* ℂˣ} (h : IsOpen (φ.ker : Set (WeilGroup K))) :
    IsOpen ((φ⁻¹).ker : Set (WeilGroup K)) := by
  refine Subgroup.isOpen_mono (fun w hw => ?_) h
  rw [MonoidHom.mem_ker] at hw ⊢
  rw [MonoidHom.inv_apply, hw, inv_one]

/-- The kernel of $\varphi \psi$ is open if the kernels of $\varphi$ and $\psi$ are open. -/
theorem isOpen_ker_mul {φ ψ : WeilGroup K →* ℂˣ} (h : IsOpen (φ.ker : Set (WeilGroup K)))
    (h' : IsOpen (ψ.ker : Set (WeilGroup K))) : IsOpen ((φ * ψ).ker : Set (WeilGroup K)) := by
  refine Subgroup.isOpen_mono (H₁ := φ.ker ⊓ ψ.ker) (fun w hw => ?_) (h.inter h')
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hw
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hw.1, hw.2, one_mul]

variable (K) in
/-- The Steinberg condition is stable under $(\varphi_1, \varphi_2) \mapsto (\varphi_2^{-1}, \varphi_1^{-1})$. -/
theorem isStW_inv_iff (φ₁ φ₂ : WeilGroup K →* ℂˣ) : IsStW K φ₂⁻¹ φ₁⁻¹ ↔ IsStW K φ₁ φ₂ := by
  refine forall_congr' fun w => ?_
  have h1 : (φ₁ w : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (φ₂ w : ℂ) ≠ 0 := Units.ne_zero _
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  constructor <;> intro h
  · field_simp at h
    linear_combination h
  · field_simp
    linear_combination h

variable (K) in
/-- The Steinberg condition is stable under a twist. -/
theorem isStW_mul_iff (φ₁ φ₂ φ : WeilGroup K →* ℂˣ) : IsStW K (φ₁ * φ) (φ₂ * φ) ↔ IsStW K φ₁ φ₂ := by
  refine forall_congr' fun w => ?_
  have h : (φ w : ℂ) ≠ 0 := Units.ne_zero _
  simp only [MonoidHom.mul_apply, Units.val_mul]
  constructor <;> intro h'
  · exact mul_right_cancel₀ h (by linear_combination h')
  · linear_combination (φ w : ℂ) * h'

/-- The matrix $\begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ in $GL_2(\mathbb{C})$. -/
def dualGL : GL (Fin 2) ℂ where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The dual of a model representation.** The dual of the model of $(\varphi_1, \varphi_2)$ is the model of $(\varphi_2^{-1}, \varphi_1^{-1})$. -/
theorem isDual_wdModel (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) :
    WDIso.IsDual (WDIso.mk (wdModel K φ₂⁻¹ φ₁⁻¹ (isOpen_ker_inv h₂) (isOpen_ker_inv h₁)))
      (WDIso.mk (wdModel K φ₁ φ₂ h₁ h₂)) := by
  classical
  refine ⟨_, conjBy (wdModel K φ₂⁻¹ φ₁⁻¹ (isOpen_ker_inv h₂) (isOpen_ker_inv h₁)) dualGL, rfl,
    mk_conjBy _ _, fun w => ?_, ?_⟩
  · change !![0, 1; -1, 0] * diagonal ![((φ₂⁻¹ w : ℂˣ) : ℂ), (φ₁⁻¹ w : ℂˣ)] * !![0, -1; 1, 0] =
      (diagonal ![(((φ₁ w)⁻¹ : ℂˣ) : ℂ), (((φ₂ w)⁻¹ : ℂˣ) : ℂ)])ᵀ
    rw [diagonal_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
  · change !![0, 1; -1, 0] * (wdModel K φ₂⁻¹ φ₁⁻¹ _ _).N * !![0, -1; 1, 0] = _
    rw [wdModel_N, wdModel_N]
    by_cases h : IsStW K φ₁ φ₂
    · simp only [(isStW_inv_iff K φ₁ φ₂).2 h, h, ite_true]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct,
        single_apply]
    · simp [mt (isStW_inv_iff K φ₁ φ₂).1 h, h]

/-- **The twist of a model representation.** The twist of the model of $(\varphi_1, \varphi_2)$ by $\varphi$ is the model of $(\varphi_1 \varphi, \varphi_2 \varphi)$. -/
theorem isTwist_wdModel (φ₁ φ₂ φ : WeilGroup K →* ℂˣ) (h₁ h₂) (h : IsOpen (φ.ker : Set (WeilGroup K))) :
    WDIso.IsTwist (WDIso.mk (wdModel K (φ₁ * φ) (φ₂ * φ) (isOpen_ker_mul h₁ h) (isOpen_ker_mul h₂ h)))
      (WDIso.mk (wdModel K φ₁ φ₂ h₁ h₂)) φ := by
  classical
  refine ⟨_, _, rfl, rfl, fun w => ?_, ?_⟩
  · rw [wdModel_r, wdModel_r]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  · rw [wdModel_N, wdModel_N]
    simp only [isStW_mul_iff]

open scoped Classical in
/-- **The determinant of a diagonal map on a coordinate subspace.** Let $S \subseteq \mathbb{C}^2$ be the subspace of the vectors $v$ with $v_1 = 0$ unless $P_0$ and $v_2 = 0$ unless $P_1$. If $E$ acts on $S$ by $\mathrm{diag}(c_0, c_1)$, then $\det E$ is the product of the $c_i$ for the $i$ with $P_i$. -/
theorem det_eq_of_diagonal (S : Submodule ℂ (Fin 2 → ℂ)) (P₀ P₁ : Prop)
    (hS : ∀ v, v ∈ S ↔ (P₀ ∨ v 0 = 0) ∧ (P₁ ∨ v 1 = 0)) (c₀ c₁ : ℂ) (E : Module.End ℂ S)
    (hE : ∀ v : S, (E v : Fin 2 → ℂ) = diagonal ![c₀, c₁] *ᵥ v) :
    LinearMap.det E = (if P₀ then c₀ else 1) * (if P₁ then c₁ else 1) := by
  have hsmul : ∀ (c : ℂ), (∀ v : S, (E v : Fin 2 → ℂ) = c • (v : Fin 2 → ℂ)) →
      LinearMap.det E = c ^ Module.finrank ℂ S := by
    intro c hc
    have : E = c • LinearMap.id := LinearMap.ext fun v => Subtype.ext (by rw [hc]; rfl)
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hline : ∀ i : Fin 2, (∀ v, v ∈ S ↔ ∀ j, j ≠ i → v j = 0) → Module.finrank ℂ S = 1 := by
    intro i hi
    have : S = Submodule.span ℂ {(Pi.single i 1 : Fin 2 → ℂ)} := by
      ext v
      rw [hi, Submodule.mem_span_singleton]
      constructor
      · intro h
        exact ⟨v i, funext fun j => by
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj, h j hj]⟩
      · rintro ⟨a, rfl⟩ j hj
        simp [hj]
    rw [this, finrank_span_singleton]
    simp
  by_cases h₀ : P₀ <;> by_cases h₁ : P₁ <;> simp only [h₀, h₁, ite_true, ite_false]
  · have htop : S = ⊤ := eq_top_iff.2 fun v _ => (hS v).2 ⟨Or.inl h₀, Or.inl h₁⟩
    let e := LinearEquiv.ofTop S htop
    have hc : (e : S →ₗ[ℂ] Fin 2 → ℂ) ∘ₗ E ∘ₗ (e.symm : (Fin 2 → ℂ) →ₗ[ℂ] S) =
        toLin' (diagonal ![c₀, c₁]) := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.ofTop_apply, toLin'_apply, e]
      rw [hE, LinearEquiv.ofTop_symm_apply]
    rw [← LinearMap.det_conj E e, hc, LinearMap.det_toLin', det_diagonal, Fin.prod_univ_two]
    rfl
  · rw [hsmul c₀ fun v => ?_, hline 0 fun v => ?_, pow_one, mul_one]
    · rw [hS]
      simp only [h₀, h₁, true_or, false_or, true_and]
      exact ⟨fun h j hj => by fin_cases j <;> simp_all, fun h => h 1 (by decide)⟩
    · have hv := ((hS v).1 v.2).2.resolve_left h₁
      rw [hE]
      funext j
      fin_cases j <;> simp [mulVec_diagonal, hv]
  · rw [hsmul c₁ fun v => ?_, hline 1 fun v => ?_, pow_one, one_mul]
    · rw [hS]
      simp only [h₀, h₁, true_or, false_or, and_true]
      exact ⟨fun h j hj => by fin_cases j <;> simp_all, fun h => h 0 (by decide)⟩
    · have hv := ((hS v).1 v.2).1.resolve_left h₀
      rw [hE]
      funext j
      fin_cases j <;> simp [mulVec_diagonal, hv]
  · have : Subsingleton S := by
      refine ⟨fun a b => Subtype.ext (funext fun j => ?_)⟩
      have ha := (hS a).1 a.2
      have hb := (hS b).1 b.2
      fin_cases j
      · exact (ha.1.resolve_left h₀).trans (hb.1.resolve_left h₀).symm
      · exact (ha.2.resolve_left h₁).trans (hb.2.resolve_left h₁).symm
    rw [LinearMap.det_eq_one_of_subsingleton, mul_one]

variable (K) in
open scoped Classical in
/-- The L-factor $L(s, \varphi)$ of a character of $W_K$: $(1 - \varphi(\Phi) q^{-s})^{-1}$ if $\varphi$ is trivial on the inertia subgroup, and $1$ otherwise. -/
noncomputable def charLFactorW (φ : WeilGroup K →* ℂˣ) (s : ℂ) : ℂ :=
  if ∀ i ∈ WeilGroup.inertia K, φ i = 1 then
    (1 - (φ (geomFrob K) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ else 1

/-- The vectors fixed by a diagonal matrix of characters. -/
theorem mulVec_diagonal_eq_iff (φ : WeilGroup K →* ℂˣ) (x : ℂ) :
    (∀ i ∈ WeilGroup.inertia K, (φ i : ℂ) * x = x) ↔ (∀ i ∈ WeilGroup.inertia K, φ i = 1) ∨ x = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inr hx
    · exact Or.inl fun i hi => Units.ext ((mul_eq_right₀ hx).1 (h i hi))
  · rintro (h | h) i hi
    · rw [h i hi, Units.val_one, one_mul]
    · rw [h, mul_zero]

open scoped Classical in
/-- **The L-factor of a model representation.** $L(s, \varphi_1 \oplus \varphi_2) = L(s, \varphi_1) L(s, \varphi_2)$ if $N = 0$, and $L(s, \mathrm{Sp}(2) \otimes \chi) = L(s, \varphi_1)$ if $\varphi_1 = \varphi_2 |\cdot|$. -/
theorem lFactor_wdModel (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) (s : ℂ) :
    (wdModel K φ₁ φ₂ h₁ h₂).lFactor s =
      charLFactorW K φ₁ s * if IsStW K φ₁ φ₂ then 1 else charLFactorW K φ₂ s := by
  set ρ := wdModel K φ₁ φ₂ h₁ h₂
  set P₀ := ∀ i ∈ WeilGroup.inertia K, φ₁ i = 1
  set P₁ := ∀ i ∈ WeilGroup.inertia K, φ₂ i = 1
  have hS : ∀ v, v ∈ ρ.lSpace ↔ (P₀ ∨ v 0 = 0) ∧ ((P₁ ∧ ¬IsStW K φ₁ φ₂) ∨ v 1 = 0) := by
    intro v
    change (ρ.N *ᵥ v = 0 ∧ ∀ i ∈ WeilGroup.inertia K, (ρ.r i : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = v) ↔ _
    have hfix : (∀ i ∈ WeilGroup.inertia K, (ρ.r i : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = v) ↔
        (P₀ ∨ v 0 = 0) ∧ (P₁ ∨ v 1 = 0) := by
      rw [← mulVec_diagonal_eq_iff, ← mulVec_diagonal_eq_iff, ← forall₂_and]
      refine forall₂_congr fun i _ => ?_
      rw [wdModel_r, funext_iff, Fin.forall_fin_two]
      simp [mulVec_diagonal]
    rw [hfix, wdModel_N]
    by_cases hst : IsStW K φ₁ φ₂
    · have : (single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) *ᵥ v = 0 ↔ v 1 = 0 := by
        rw [funext_iff, Fin.forall_fin_two]
        simp [mulVec, dotProduct, single_apply]
      simp only [hst, ite_true, this, not_true_eq_false, and_false, false_or]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2, Or.inr h1⟩
    · simp [hst]
  have hE : ∀ v : ρ.lSpace,
      (((1 : Module.End ℂ ρ.lSpace) - ((residueCard K : ℂ) ^ (-s)) • ρ.frobOnLSpace) v : Fin 2 → ℂ) =
        diagonal ![1 - (residueCard K : ℂ) ^ (-s) * φ₁ (geomFrob K),
          1 - (residueCard K : ℂ) ^ (-s) * φ₂ (geomFrob K)] *ᵥ v := by
    intro v
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, Submodule.coe_sub,
      Submodule.coe_smul]
    change (v : Fin 2 → ℂ) - _ • ((ρ.r (geomFrob K) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) = _
    rw [wdModel_r]
    funext j
    fin_cases j <;> simp [mulVec_diagonal] <;> ring
  rw [WeilDeligneRep.lFactor, det_eq_of_diagonal _ _ _ hS _ _ _ hE, mul_inv, charLFactorW,
    charLFactorW]
  by_cases hst : IsStW K φ₁ φ₂ <;> simp only [hst, not_true_eq_false, and_false, ite_false,
    inv_one, mul_one, not_false_eq_true, and_true, ite_true] <;> split_ifs <;> simp [mul_comm]

end Model

section Char

open LocalGL1

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The determinant of a model representation is $\varphi_1 \varphi_2$. -/
theorem det_wdModel (φ₁ φ₂ : WeilGroup K →* ℂˣ) (h₁ h₂) :
    (wdModel K φ₁ φ₂ h₁ h₂).det = φ₁ * φ₂ := by
  ext w
  change Matrix.det ((wdModel K φ₁ φ₂ h₁ h₂).r w : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [wdModel_r, det_diagonal, Fin.prod_univ_two]
  rfl

/-- The map $\chi \mapsto \chi \circ \mathrm{art}_K^{-1}$ is multiplicative. -/
theorem weilChar_mul (χ χ' : Kˣ →* ℂˣ) :
    weilChar K art (χ * χ') = weilChar K art χ * weilChar K art χ' :=
  MonoidHom.ext fun _ => rfl

/-- The map $\chi \mapsto \chi \circ \mathrm{art}_K^{-1}$ commutes with the inverse. -/
theorem weilChar_inv (χ : Kˣ →* ℂˣ) : weilChar K art χ⁻¹ = (weilChar K art χ)⁻¹ :=
  MonoidHom.ext fun _ => rfl

/-- The map $\chi \mapsto \chi \circ \mathrm{art}_K^{-1}$ is injective. -/
theorem weilChar_injective : Function.Injective (weilChar K art) := by
  intro χ χ' h
  ext x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
  have := congrArg (fun φ => (φ w : ℂ)) h
  simp only [weilChar_apply, hw, ContinuousMulEquiv.symm_apply_apply] at this
  exact this

/-- If $\chi$ and $\varphi$ correspond through $\mathrm{art}_K$, then $\varphi = \chi \circ \mathrm{art}_K^{-1}$. -/
theorem eq_weilChar_of_charCorrespond {χ : Kˣ →* ℂˣ} {φ : WeilGroup K →* ℂˣ}
    (h : CharCorrespond K art χ φ) : φ = weilChar K art χ := by
  ext w
  rw [weilChar_apply, h (art.symm (QuotientGroup.mk w)) w (ContinuousMulEquiv.apply_symm_apply _ _).symm]

/-- A smooth character of $W_K$, as a character of $W_K^{ab}$. -/
noncomputable def charAb (φ : WeilGroup K →* ℂˣ) (hφ : IsOpen (φ.ker : Set (WeilGroup K))) :
    WeilGroup.Ab K →* ℂˣ :=
  QuotientGroup.lift _ φ (Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker _) (Subgroup.isClosed_of_isOpen _ hφ))

/-- The character $\varphi \circ \mathrm{art}_K$ of $K^\times$ for a smooth character $\varphi$ of $W_K$. -/
noncomputable def charOfWeil (φ : WeilGroup K →* ℂˣ) (hφ : IsOpen (φ.ker : Set (WeilGroup K))) :
    Kˣ →* ℂˣ :=
  (charAb φ hφ).comp art.toMulEquiv.toMonoidHom

/-- The character $\varphi \circ \mathrm{art}_K$ gives back $\varphi$. -/
theorem weilChar_charOfWeil (φ : WeilGroup K →* ℂˣ) (hφ : IsOpen (φ.ker : Set (WeilGroup K))) :
    weilChar K art (charOfWeil art φ hφ) = φ := by
  ext w
  change ((charAb φ hφ) (art (art.symm (QuotientGroup.mk w))) : ℂ) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- The character $\varphi \circ \mathrm{art}_K$ is smooth. -/
theorem isSmoothChar_charOfWeil (φ : WeilGroup K →* ℂˣ) (hφ : IsOpen (φ.ker : Set (WeilGroup K))) :
    IsSmoothChar K (charOfWeil art φ hφ) := by
  have h : IsOpen ((charAb φ hφ).ker : Set (WeilGroup.Ab K)) := isOpen_coinduced.2 hφ
  exact art.continuous.isOpen_preimage _ h

/-- The character $\chi \circ \mathrm{art}_K^{-1}$ of $W_K$ is smooth if $\chi$ is smooth. -/
theorem isOpen_ker_weilChar {χ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ) :
    IsOpen ((weilChar K art χ).ker : Set (WeilGroup K)) :=
  (continuous_artSymm_mk K art).isOpen_preimage _ hχ

/-- For a local Artin map, $\|w\| = |\mathrm{art}_K^{-1}(w)|$. -/
theorem weilNorm_eq (hart : IsLocalArtinMap K art) (w : WeilGroup K) :
    weilNorm K w = (normAbs K (art.symm (QuotientGroup.mk w) : K) : ℂ) := by
  have h := degreeAb_art hart (art.symm (QuotientGroup.mk w))
  rw [ContinuousMulEquiv.apply_symm_apply, degreeAb_mk] at h
  rw [weilNorm, h, normAbs_eq_zpow (Units.ne_zero _), toAdd_ofAdd]
  push_cast
  rfl

variable (K) in
/-- The pair $(\chi_1, \chi_2)$ of characters of $K^\times$ is a Steinberg pair: $\chi_1 = \chi_2 |\cdot|$. -/
def IsSt (χ₁ χ₂ : Kˣ →* ℂˣ) : Prop :=
  ∀ x : Kˣ, (χ₁ x : ℂ) = χ₂ x * (normAbs K (x : K) : ℂ)

/-- The Steinberg condition is the same on the two sides. -/
theorem isStW_weilChar_iff (hart : IsLocalArtinMap K art) (χ₁ χ₂ : Kˣ →* ℂˣ) :
    IsStW K (weilChar K art χ₁) (weilChar K art χ₂) ↔ IsSt K χ₁ χ₂ := by
  constructor
  · intro h x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (art x)
    have := h w
    rwa [weilNorm_eq art hart, weilChar_apply, weilChar_apply, hw,
      ContinuousMulEquiv.symm_apply_apply] at this
  · intro h w
    rw [weilNorm_eq art hart, weilChar_apply, weilChar_apply]
    exact h _

/-- The L-factor of $\chi \circ \mathrm{art}_K^{-1}$ is the L-factor of $\chi$. -/
theorem charLFactorW_weilChar (hart : IsLocalArtinMap K art) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (s : ℂ) : charLFactorW K (weilChar K art χ) s = charLFactor K (unif K) χ s := by
  rw [charLFactor_eq_lFactor_of_iff K art hart χ hχ (unif K) isUniformizer_unif (unramified_iff hart χ),
    lFactor_wdOfChar]
  rfl

end Char

section Automorphic

open LocalGL1

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A nonzero map of representations from an irreducible representation is injective. -/
theorem injective_of_isIrreducible {G : Type u} [Group G] [TopologicalSpace G]
    {σ π : SmoothRep G} (hσ : σ.IsIrreducible) {f : σ.V →ₗ[ℂ] π.V} (hf : f ≠ 0)
    (hfg : ∀ g v, f (σ.ρ g v) = π.ρ g (f v)) : Function.Injective f := by
  have hst : IsStableSubspace σ.ρ (LinearMap.ker f) := fun g v hv => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hfg, LinearMap.mem_ker.1 hv, map_zero]
  rcases hσ.2 (LinearMap.ker f) hst with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hf

/-- The relation `HasHom` does not change if the source is replaced by an isomorphic representation. -/
theorem hasHom_of_iso {G : Type u} [Group G] [TopologicalSpace G] {σ σ' π : SmoothRep G}
    (h : σ.Iso σ') (h' : σ'.HasHom π) : σ.HasHom π := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf, hfg⟩ := h'
  refine ⟨f ∘ₗ (e : σ.V →ₗ[ℂ] σ'.V), fun h0 => hf (LinearMap.ext fun v => ?_), fun g v => ?_⟩
  · have := LinearMap.congr_fun h0 (e.symm v)
    simpa using this
  · simp [he, hfg]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The scalar matrices are central in $GL_2(K)$. -/
theorem mul_scalarGL (a : Kˣ) (g : GL (Fin 2) K) : g * scalarGL K 2 a = scalarGL K 2 a * g := by
  ext i j
  change ((g : Matrix (Fin 2) (Fin 2) K) * scalar (Fin 2) (a : K)) i j =
    (scalar (Fin 2) (a : K) * (g : Matrix (Fin 2) (Fin 2) K)) i j
  simp [mul_comm]

/-- **The central character of a subrepresentation of the principal series.** If an irreducible representation $\pi$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then $\pi$ has central character $\chi_1 \chi_2$. -/
theorem hasCentralChar_of_hasHom (π : IrrRep (GL (Fin 2) K)) {χ₁ χ₂ : Kˣ →* ℂˣ}
    (h : π.1.HasHom (principalSeries K χ₁ χ₂)) : π.1.HasCentralChar (χ₁ * χ₂) := by
  obtain ⟨f, hf, hfg⟩ := h
  have hinj := injective_of_isIrreducible π.2.1 hf hfg
  intro a v
  apply hinj
  rw [hfg, map_smul]
  apply Subtype.ext
  funext g
  change (f v).1 (g * scalarGL K 2 a) = ((χ₁ * χ₂) a : ℂ) * (f v).1 g
  have h10 : ((scalarGL K 2 a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    change scalar (Fin 2) (a : K) 1 0 = 0
    simp
  have h00 : ((scalarGL K 2 a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = a := by
    change scalar (Fin 2) (a : K) 0 0 = a
    simp
  have h11 : ((scalarGL K 2 a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = a := by
    change scalar (Fin 2) (a : K) 1 1 = a
    simp
  rw [mul_scalarGL, (f v).2.1 _ g a a h10 h00 h11, div_self a.ne_zero, normAbs_one, Real.sqrt_one,
    MonoidHom.mul_apply, Units.val_mul, Complex.ofReal_one, mul_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The determinant of an upper triangular matrix with diagonal $(a, d)$ is $ad$. -/
theorem det_eq_of_upper {b : GL (Fin 2) K} {a d : Kˣ} (h1 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h2 : (b : Matrix (Fin 2) (Fin 2) K) 0 0 = a) (h3 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 = d) :
    Matrix.GeneralLinearGroup.det b = a * d := by
  ext
  simp [Matrix.det_fin_two, h1, h2, h3]

/-- The product of a smooth character and a smooth character is smooth. -/
theorem isSmoothChar_mul {χ χ' : Kˣ →* ℂˣ} (h : IsSmoothChar K χ) (h' : IsSmoothChar K χ') :
    IsSmoothChar K (χ * χ') := by
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ'.ker) (fun x hx => ?_) (h.inter h')
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, mul_one]

/-- The function $g \mapsto \chi(\det g) f(g)$ is in $\mathrm{Ind}(\chi_1 \chi, \chi_2 \chi)$ if $f$ is in $\mathrm{Ind}(\chi_1, \chi_2)$. -/
theorem mul_detChar_mem (χ χ₁ χ₂ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ)
    (F : principalSeriesSpace K χ₁ χ₂) :
    (fun g => (detChar K 2 χ g : ℂ) * F.1 g) ∈ principalSeriesSpace K (χ₁ * χ) (χ₂ * χ) := by
  refine ⟨fun b g a d h1 h2 h3 => ?_, ?_⟩
  · change (χ (Matrix.GeneralLinearGroup.det (b * g)) : ℂ) * F.1 (b * g) = _
    rw [F.2.1 b g a d h1 h2 h3, map_mul, det_eq_of_upper h1 h2 h3]
    change _ = _ * _ * _ * ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1 g)
    simp only [map_mul, MonoidHom.mul_apply, Units.val_mul]
    ring
  · obtain ⟨U, hU, hFU⟩ := F.2.2
    refine ⟨U ⊓ (detChar K 2 χ).ker, hU.inter (isOpen_ker_detChar K 2 χ hχ), fun g u hu => ?_⟩
    rw [Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    simp only
    rw [map_mul, hu.2, mul_one, hFU g u hu.1]

/-- The map $f \mapsto (\chi \circ \det) f$ from $\mathrm{Ind}(\chi_1, \chi_2)$ to $\mathrm{Ind}(\chi_1 \chi, \chi_2 \chi)$. -/
noncomputable def mulDetChar (χ χ₁ χ₂ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    principalSeriesSpace K χ₁ χ₂ →ₗ[ℂ] principalSeriesSpace K (χ₁ * χ) (χ₂ * χ) where
  toFun F := ⟨_, mul_detChar_mem χ χ₁ χ₂ hχ F⟩
  map_add' F F' := Subtype.ext (funext fun g => by simp [mul_add])
  map_smul' c F := Subtype.ext (funext fun g => by simp [mul_left_comm])

/-- **The twist of a subrepresentation of the principal series.** If $\pi$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then $\pi \otimes \chi \circ \det$ has a nonzero map to $\mathrm{Ind}(\chi_1 \chi, \chi_2 \chi)$. -/
theorem hasHom_twist (π : SmoothRep (GL (Fin 2) K)) {χ χ₁ χ₂ : Kˣ →* ℂˣ} (hχ : IsSmoothChar K χ)
    (h : π.HasHom (principalSeries K χ₁ χ₂)) :
    (π.twist (detChar K 2 χ) (isOpen_ker_detChar K 2 χ hχ)).HasHom
      (principalSeries K (χ₁ * χ) (χ₂ * χ)) := by
  obtain ⟨f, hf, hfg⟩ := h
  refine ⟨mulDetChar χ χ₁ χ₂ hχ ∘ₗ f, fun h0 => hf (LinearMap.ext fun v => ?_), fun g (v : π.V) => ?_⟩
  · apply Subtype.ext
    funext x
    have := congrArg (fun F : principalSeriesSpace K (χ₁ * χ) (χ₂ * χ) => F.1 x)
      (LinearMap.congr_fun h0 v)
    change (detChar K 2 χ x : ℂ) * (f v).1 x = 0 at this
    exact (mul_eq_zero.1 this).resolve_left (Units.ne_zero _)
  · apply Subtype.ext
    funext x
    change (detChar K 2 χ x : ℂ) * (f ((detChar K 2 χ g : ℂ) • π.ρ g v)).1 x =
      (detChar K 2 χ (x * g) : ℂ) * (f v).1 (x * g)
    rw [map_smul, hfg, map_mul, Units.val_mul]
    change (detChar K 2 χ x : ℂ) * ((detChar K 2 χ g : ℂ) * (f v).1 (x * g)) = _
    ring

end Automorphic

section Inputs

open LocalGL1

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Existence of an irreducible subrepresentation of the principal series** (Bushnell and Henniart, The local Langlands conjecture for GL(2), Chapter 2, Section 9; Jacquet and Langlands, Automorphic forms on GL(2), LNM 114, Section 3). For smooth characters $\chi_1, \chi_2$ of $K^\times$, some irreducible admissible representation of $GL_2(K)$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$. The principal series has length at most 2. -/
def PSSubExists : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    ∃ π : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂)

/-- **Uniqueness of the irreducible subrepresentation** (Bushnell and Henniart, Chapter 2, Section 9; Jacquet and Langlands, LNM 114, Section 3). Two irreducible admissible representations with a nonzero map to the same $\mathrm{Ind}(\chi_1, \chi_2)$ are isomorphic. When $\mathrm{Ind}(\chi_1, \chi_2)$ is reducible, its composition series does not split. -/
def PSSubUnique : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    ∀ π π' : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      π'.1.HasHom (principalSeries K χ₁ χ₂) → π.1.Iso π'.1

/-- **The inducing pair is unique up to the swap** (Bushnell and Henniart, Chapter 2, Section 9, the Jacquet module and Frobenius reciprocity; Jacquet and Langlands, LNM 114, Section 3). If an irreducible admissible representation has nonzero maps to $\mathrm{Ind}(\chi_1, \chi_2)$ and to $\mathrm{Ind}(\psi_1, \psi_2)$, then $(\psi_1, \psi_2) = (\chi_1, \chi_2)$, or $(\psi_1, \psi_2) = (\chi_2, \chi_1)$ and $\chi_1 \chi_2^{-1} \ne |\cdot|^{\pm 1}$. The reason is that the Jacquet module of the subrepresentation is $\chi_1 \oplus \chi_2$ (up to the normalization) if $\mathrm{Ind}(\chi_1, \chi_2)$ is irreducible, and the character $\chi_1 \otimes \chi_2$ alone otherwise. -/
def PSSubRigid : Prop :=
  ∀ χ₁ χ₂ ψ₁ ψ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ → IsSmoothChar K ψ₁ →
    IsSmoothChar K ψ₂ → ∀ π : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      π.1.HasHom (principalSeries K ψ₁ ψ₂) →
        (ψ₁ = χ₁ ∧ ψ₂ = χ₂) ∨ (ψ₁ = χ₂ ∧ ψ₂ = χ₁ ∧ ¬IsSt K χ₁ χ₂ ∧ ¬IsSt K χ₂ χ₁)

/-- **The swap of an irreducible principal series** (Bushnell and Henniart, Chapter 2, Section 9, the irreducibility criterion). If $\chi_1 \chi_2^{-1} \ne |\cdot|^{\pm 1}$, then $\mathrm{Ind}(\chi_1, \chi_2)$ is irreducible and isomorphic to $\mathrm{Ind}(\chi_2, \chi_1)$. So a representation with a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$ has a nonzero map to $\mathrm{Ind}(\chi_2, \chi_1)$. -/
def PSSubSwap : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ → ¬IsSt K χ₁ χ₂ → ¬IsSt K χ₂ χ₁ →
    ∀ π : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      π.1.HasHom (principalSeries K χ₂ χ₁)

/-- **Each representation that is not supercuspidal is in a principal series** (Bushnell and Henniart, Chapter 2, Sections 9 and 10; Jacquet and Langlands, LNM 114, Section 3). If an irreducible admissible representation $\pi$ of $GL_2(K)$ is not supercuspidal, then $\pi$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$ for some smooth characters $\chi_1, \chi_2$. The proof uses the Jacquet module of $\pi$, Frobenius reciprocity, and the fact that $\pi$ is cuspidal exactly when its matrix coefficients have compact support modulo the center. -/
def NonSupercuspidalExhaustion : Prop :=
  ∀ π : IrrRep (GL (Fin 2) K), ¬π.1.IsSupercuspidal (scalarGL K 2) →
    ∃ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ ∧ IsSmoothChar K χ₂ ∧
      π.1.HasHom (principalSeries K χ₁ χ₂)

/-- **A subrepresentation of the principal series is not supercuspidal** (Bushnell and Henniart, Chapter 2, Sections 9 and 10). If an irreducible admissible representation has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then it is not supercuspidal: its Jacquet module is not zero, so some matrix coefficient does not have compact support modulo the center. -/
def PSSubNotSupercuspidal : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    ∀ π : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      ¬π.1.IsSupercuspidal (scalarGL K 2)

/-- **The contragredient of a subrepresentation of the principal series** (Bushnell and Henniart, Chapter 2, Section 9; Jacquet and Langlands, LNM 114, Section 3). If $\pi$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then each representation isomorphic to $\pi^\vee$ has a nonzero map to $\mathrm{Ind}(\chi_2^{-1}, \chi_1^{-1})$. The contragredient of $\mathrm{Ind}(\chi_1, \chi_2)$ is $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$, and a quotient of $\mathrm{Ind}(\chi_1^{-1}, \chi_2^{-1})$ is a subrepresentation of $\mathrm{Ind}(\chi_2^{-1}, \chi_1^{-1})$. -/
def PSSubContragredient : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    ∀ π π' : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      π'.1.Iso π.1.contragredient → π'.1.HasHom (principalSeries K χ₂⁻¹ χ₁⁻¹)

open scoped Classical in
/-- **The L-factor of a subrepresentation of the principal series** (Bushnell and Henniart, Chapter 6, Section 26; Godement and Jacquet, Zeta functions of simple algebras, LNM 260, Theorem 3.3; Jacquet and Langlands, LNM 114, Section 3). If an irreducible admissible representation $\pi$ has a nonzero map to $\mathrm{Ind}(\chi_1, \chi_2)$, then $L(s, \pi) = L(s, \chi_1)$ if $\chi_1 = \chi_2 |\cdot|$ (a twist of the Steinberg representation), and $L(s, \pi) = L(s, \chi_1) L(s, \chi_2)$ otherwise. -/
def PSSubLFactor : Prop :=
  ∀ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ → IsSmoothChar K χ₂ →
    ∀ π : IrrRep (GL (Fin 2) K), π.1.HasHom (principalSeries K χ₁ χ₂) →
      IsGJLFactor K π.1 fun s =>
        charLFactor K (unif K) χ₁ s * if IsSt K χ₁ χ₂ then 1 else charLFactor K (unif K) χ₂ s

/-- The published theorems on the representations of $GL_2(K)$ that are not supercuspidal, for one field $K$. -/
structure NonSupercuspidalInputs : Prop where
  /-- Existence of an irreducible subrepresentation of the principal series. -/
  subExists : PSSubExists K
  /-- Uniqueness of the irreducible subrepresentation. -/
  subUnique : PSSubUnique K
  /-- The inducing pair is unique up to the swap. -/
  subRigid : PSSubRigid K
  /-- The swap of an irreducible principal series. -/
  subSwap : PSSubSwap K
  /-- Each representation that is not supercuspidal is in a principal series. -/
  exhaustion : NonSupercuspidalExhaustion K
  /-- A subrepresentation of the principal series is not supercuspidal. -/
  notSupercuspidal : PSSubNotSupercuspidal K
  /-- The contragredient of a subrepresentation of the principal series. -/
  contragredient : PSSubContragredient K
  /-- The L-factor of a subrepresentation of the principal series. -/
  lFactor : PSSubLFactor K

end Inputs

section Assembly

open LocalGL1

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (art : Kˣ ≃ₜ* WeilGroup.Ab K)

/-- The Galois parameter $\varphi_1 \oplus \varphi_2$ (with $N \ne 0$ in the Steinberg case) of the subrepresentation of $\mathrm{Ind}(\chi_1, \chi_2)$, where $\varphi_i = \chi_i \circ \mathrm{art}_K^{-1}$. -/
noncomputable def psParam (χ₁ χ₂ : Kˣ →* ℂˣ) (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂) :
    WDIso K 2 :=
  WDIso.mk (wdModel K (weilChar K art χ₁) (weilChar K art χ₂) (isOpen_ker_weilChar art h₁)
    (isOpen_ker_weilChar art h₂))

/-- The class of a model representation depends only on the two characters. -/
theorem mk_wdModel_congr {φ₁ φ₂ ψ₁ ψ₂ : WeilGroup K →* ℂˣ} (e₁ : φ₁ = ψ₁) (e₂ : φ₂ = ψ₂) (h₁ h₂ k₁ k₂) :
    WDIso.mk (wdModel K φ₁ φ₂ h₁ h₂) = WDIso.mk (wdModel K ψ₁ ψ₂ k₁ k₂) := by
  subst e₁ e₂
  rfl

/-- The class `psParam` is not irreducible. -/
theorem psParam_notMem (χ₁ χ₂ : Kˣ →* ℂˣ) (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂) :
    psParam art χ₁ χ₂ h₁ h₂ ∉ irrClasses K := by
  rintro ⟨ρ, hρ, hirr⟩
  exact not_isIrreducible_wdModel _ _ _ _ (isIrreducible_of_iso (Quotient.exact hρ) hirr)

/-- If an irreducible representation is in $\mathrm{Ind}(\chi_1, \chi_2)$ and in $\mathrm{Ind}(\psi_1, \psi_2)$, the two pairs give the same Galois parameter. -/
theorem psParam_eq_of_hasHom (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K)
    {χ₁ χ₂ ψ₁ ψ₂ : Kˣ →* ℂˣ} (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂)
    (k₁ : IsSmoothChar K ψ₁) (k₂ : IsSmoothChar K ψ₂) (π : IrrRep (GL (Fin 2) K))
    (hχ : π.1.HasHom (principalSeries K χ₁ χ₂)) (hψ : π.1.HasHom (principalSeries K ψ₁ ψ₂)) :
    psParam art ψ₁ ψ₂ k₁ k₂ = psParam art χ₁ χ₂ h₁ h₂ := by
  rcases h.subRigid χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ k₁ k₂ π hχ hψ with ⟨rfl, rfl⟩ | ⟨rfl, rfl, n₁, n₂⟩
  · rfl
  · exact (Quotient.sound (iso_wdModel_swap _ _ _ _ (mt (isStW_weilChar_iff art hart _ _).1 n₁)
      (mt (isStW_weilChar_iff art hart _ _).1 n₂))).symm

/-- A subrepresentation of the principal series gives a class that is not supercuspidal. -/
theorem notMem_scClasses_of_hasHom (h : NonSupercuspidalInputs K) (π : IrrRep (GL (Fin 2) K))
    {χ₁ χ₂ : Kˣ →* ℂˣ} (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂)
    (hh : π.1.HasHom (principalSeries K χ₁ χ₂)) : IrrSmooth.mk π ∉ scClasses K := by
  rintro ⟨π', hmk, hsc⟩
  exact h.notSupercuspidal χ₁ χ₂ h₁ h₂ π' (hasHom_of_iso (Quotient.exact hmk) hh) hsc

/-- Each representative of a class that is not supercuspidal is in a principal series. -/
theorem exists_hasHom (h : NonSupercuspidalInputs K) (π : IrrRep (GL (Fin 2) K))
    (hπ : IrrSmooth.mk π ∉ scClasses K) :
    ∃ χ₁ χ₂ : Kˣ →* ℂˣ, IsSmoothChar K χ₁ ∧ IsSmoothChar K χ₂ ∧
      π.1.HasHom (principalSeries K χ₁ χ₂) :=
  h.exhaustion π fun hsc => hπ ⟨π, rfl, hsc⟩

/-- A pair of smooth characters for the chosen representative of a class that is not supercuspidal. -/
theorem exists_pair (h : NonSupercuspidalInputs K) (x : {x : IrrSmooth (GL (Fin 2) K) // x ∉ scClasses K}) :
    ∃ q : (Kˣ →* ℂˣ) × (Kˣ →* ℂˣ), IsSmoothChar K q.1 ∧ IsSmoothChar K q.2 ∧
      (Quotient.out x.1).1.HasHom (principalSeries K q.1 q.2) := by
  obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h (Quotient.out x.1) (by
    rw [show IrrSmooth.mk (Quotient.out x.1) = x.1 from Quotient.out_eq _]
    exact x.2)
  exact ⟨(χ₁, χ₂), h₁, h₂, hh⟩

/-- The map from the classes that are not supercuspidal to $\mathrm{WD}_2(W_K)$: the class of $\pi \subseteq \mathrm{Ind}(\chi_1, \chi_2)$ goes to `psParam` of $(\chi_1, \chi_2)$. -/
noncomputable def nsMap (h : NonSupercuspidalInputs K)
    (x : {x : IrrSmooth (GL (Fin 2) K) // x ∉ scClasses K}) : WDIso K 2 :=
  psParam art (exists_pair h x).choose.1 (exists_pair h x).choose.2 (exists_pair h x).choose_spec.1
    (exists_pair h x).choose_spec.2.1

/-- The value of `nsMap` does not depend on the representative or on the inducing pair. -/
theorem nsMap_eq (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K)
    (x : {x : IrrSmooth (GL (Fin 2) K) // x ∉ scClasses K}) (π : IrrRep (GL (Fin 2) K))
    (hπ : IrrSmooth.mk π = x.1) {χ₁ χ₂ : Kˣ →* ℂˣ} (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂)
    (hh : π.1.HasHom (principalSeries K χ₁ χ₂)) : nsMap art h x = psParam art χ₁ χ₂ h₁ h₂ := by
  have hiso : (Quotient.out x.1).1.Iso π.1 :=
    Quotient.exact ((Quotient.out_eq x.1).trans hπ.symm)
  exact psParam_eq_of_hasHom art hart h h₁ h₂ _ _ _ (hasHom_of_iso hiso hh)
    (exists_pair h x).choose_spec.2.2

/-- The map `nsMap` is injective. -/
theorem nsMap_injective (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K) :
    Function.Injective (nsMap art h) := by
  intro x x' hxx'
  obtain ⟨h₁, h₂, hh⟩ := (exists_pair h x).choose_spec
  obtain ⟨h₁', h₂', hh'⟩ := (exists_pair h x').choose_spec
  set q := (exists_pair h x).choose
  set q' := (exists_pair h x').choose
  have hiso := (iso_wdModel_iff _ _ _ _ _ _ _ _).1 (Quotient.exact hxx')
  have hU : (Quotient.out x.1).1.Iso (Quotient.out x'.1).1 := by
    rcases hiso with ⟨e₁, e₂⟩ | ⟨e₁, e₂, n₁, n₂⟩
    · rw [weilChar_injective art e₁, weilChar_injective art e₂] at hh'
      exact h.subUnique _ _ h₁ h₂ _ _ hh hh'
    · rw [weilChar_injective art e₁, weilChar_injective art e₂] at hh'
      exact h.subUnique _ _ h₂ h₁ _ _ (h.subSwap _ _ h₁ h₂ (mt (isStW_weilChar_iff art hart _ _).2 n₁)
        (mt (isStW_weilChar_iff art hart _ _).2 n₂) _ hh) hh'
  apply Subtype.ext
  rw [← Quotient.out_eq x.1, ← Quotient.out_eq x'.1]
  exact Quotient.sound hU

/-- The map `nsMap` hits each class that is not irreducible. -/
theorem nsMap_surjective (h : NonSupercuspidalInputs K) (hart : IsLocalArtinMap K art)
    (y : {y : WDIso K 2 // y ∉ irrClasses K}) :
    ∃ x, nsMap art h x = y.1 := by
  have hni : ¬(Quotient.out y.1 : WeilDeligneRep K 2).IsIrreducible :=
    fun hi => y.2 ⟨_, Quotient.out_eq _, hi⟩
  obtain ⟨φ₁, φ₂, k₁, k₂, hρ⟩ := exists_iso_wdModel _ hni
  obtain ⟨π, hh⟩ := h.subExists _ _ (isSmoothChar_charOfWeil art φ₁ k₁)
    (isSmoothChar_charOfWeil art φ₂ k₂)
  refine ⟨⟨IrrSmooth.mk π, notMem_scClasses_of_hasHom h π (isSmoothChar_charOfWeil art φ₁ k₁)
    (isSmoothChar_charOfWeil art φ₂ k₂) hh⟩, ?_⟩
  rw [nsMap_eq art hart h _ π rfl (isSmoothChar_charOfWeil art φ₁ k₁)
    (isSmoothChar_charOfWeil art φ₂ k₂) hh, psParam,
    mk_wdModel_congr (weilChar_charOfWeil art φ₁ k₁) (weilChar_charOfWeil art φ₂ k₂) _ _ k₁ k₂,
    ← Quotient.out_eq y.1]
  exact (Quotient.sound hρ).symm

/-- The bijection from the classes that are not supercuspidal to the classes that are not irreducible. -/
noncomputable def nsEquiv (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K) :
    {x : IrrSmooth (GL (Fin 2) K) // x ∉ scClasses K} ≃ {y : WDIso K 2 // y ∉ irrClasses K} :=
  Equiv.ofBijective (fun x => ⟨nsMap art h x, by
      obtain ⟨h₁, h₂, -⟩ := (exists_pair h x).choose_spec
      exact psParam_notMem art _ _ h₁ h₂⟩)
    ⟨fun x x' hxx' => nsMap_injective art hart h (congrArg Subtype.val hxx'),
      fun y => (nsMap_surjective art h hart y).imp fun _ hx => Subtype.ext hx⟩

/-- The value of `nsEquiv`. -/
theorem nsEquiv_apply (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K) (x) :
    (nsEquiv art hart h x).1 = nsMap art h x :=
  rfl

open scoped Classical in
/-- The L-factor of `psParam` of $(\chi_1, \chi_2)$ is $L(s, \chi_1)$ in the Steinberg case and $L(s, \chi_1) L(s, \chi_2)$ otherwise. -/
theorem lFactor_of_mk_eq_psParam (hart : IsLocalArtinMap K art) {χ₁ χ₂ : Kˣ →* ℂˣ}
    (h₁ : IsSmoothChar K χ₁) (h₂ : IsSmoothChar K χ₂) {ρ : WeilDeligneRep K 2}
    (hρ : WDIso.mk ρ = psParam art χ₁ χ₂ h₁ h₂) :
    ρ.lFactor = fun s =>
      charLFactor K (unif K) χ₁ s * if IsSt K χ₁ χ₂ then 1 else charLFactor K (unif K) χ₂ s := by
  rw [← lFactor_eq_of_iso (Quotient.exact hρ)]
  funext s
  rw [lFactor_wdModel, charLFactorW_weilChar art hart χ₁ h₁, charLFactorW_weilChar art hart χ₂ h₂]
  exact congrArg _ (if_congr (isStW_weilChar_iff art hart χ₁ χ₂) rfl rfl)

/-- **The correspondence off the supercuspidal representations, from finer published theorems.** For a local Artin map $\mathrm{art}_K$, the inputs `Langlands.LocalGL2.NonSupercuspidalInputs` give `Langlands.LocalGL2.NonSupercuspidalLLC`. The bijection is `Langlands.LocalGL2.nsEquiv`: the class of a subrepresentation of $\mathrm{Ind}(\chi_1, \chi_2)$ goes to the class of $\varphi_1 \oplus \varphi_2$, with $N \ne 0$ exactly when $\chi_1 = \chi_2 |\cdot|$, where $\varphi_i = \chi_i \circ \mathrm{art}_K^{-1}$. -/
theorem nonSupercuspidalLLC_of_inputs (hart : IsLocalArtinMap K art) (h : NonSupercuspidalInputs K) :
    NonSupercuspidalLLC K art := by
  refine ⟨nsEquiv art hart h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π hπ ω hω ρ hρ
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hπ
    rw [nsEquiv_apply, nsMap_eq art hart h _ π rfl h₁ h₂ hh] at hρ
    have := π.2.1.1
    rw [eq_of_hasCentralChar hω (hasCentralChar_of_hasHom π hh),
      ← WeilDeligneRep.det_eq_of_iso (Quotient.exact hρ), det_wdModel, ← weilChar_mul]
    exact charCorrespond_weilChar K art _
  · rintro x hx y hy χ hχ ⟨π, π', rfl, rfl, hiso⟩ φ hφ
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hx
    have hh' := hasHom_of_iso hiso (hasHom_twist π.1 hχ hh)
    rw [nsEquiv_apply, nsEquiv_apply, nsMap_eq art hart h ⟨_, hx⟩ π rfl h₁ h₂ hh,
      nsMap_eq art hart h _ π' rfl (isSmoothChar_mul h₁ hχ) (isSmoothChar_mul h₂ hχ) hh', psParam,
      psParam, eq_weilChar_of_charCorrespond art hφ,
      mk_wdModel_congr (weilChar_mul art χ₁ χ) (weilChar_mul art χ₂ χ) _ _
        (isOpen_ker_mul (isOpen_ker_weilChar art h₁) (isOpen_ker_weilChar art hχ))
        (isOpen_ker_mul (isOpen_ker_weilChar art h₂) (isOpen_ker_weilChar art hχ))]
    exact isTwist_wdModel _ _ _ _ _ (isOpen_ker_weilChar art hχ)
  · rintro x hx y hy ⟨π, π', rfl, rfl, hiso⟩
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hx
    have hh' := h.contragredient χ₁ χ₂ h₁ h₂ π π' hh hiso
    rw [nsEquiv_apply, nsEquiv_apply, nsMap_eq art hart h ⟨_, hx⟩ π rfl h₁ h₂ hh,
      nsMap_eq art hart h _ π' rfl (LocalGL2.isSmoothChar_inv h₂) (LocalGL2.isSmoothChar_inv h₁) hh',
      psParam, psParam,
      mk_wdModel_congr (weilChar_inv art χ₂) (weilChar_inv art χ₁) _ _
        (isOpen_ker_inv (isOpen_ker_weilChar art h₂)) (isOpen_ker_inv (isOpen_ker_weilChar art h₁))]
    exact isDual_wdModel _ _ _ _
  · intro π hπ ρ hρ
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hπ
    rw [nsEquiv_apply, nsMap_eq art hart h _ π rfl h₁ h₂ hh] at hρ
    rw [lFactor_of_mk_eq_psParam art hart h₁ h₂ hρ]
    exact h.lFactor χ₁ χ₂ h₁ h₂ π hh
  · rintro x y χ hχ hx ⟨π, π', rfl, rfl, hiso⟩
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hx
    exact notMem_scClasses_of_hasHom h π' (isSmoothChar_mul h₁ hχ) (isSmoothChar_mul h₂ hχ)
      (hasHom_of_iso hiso (hasHom_twist π.1 hχ hh))
  · rintro x y hx ⟨π, π', rfl, rfl, hiso⟩
    obtain ⟨χ₁, χ₂, h₁, h₂, hh⟩ := exists_hasHom h π hx
    exact notMem_scClasses_of_hasHom h π' (LocalGL2.isSmoothChar_inv h₂)
      (LocalGL2.isSmoothChar_inv h₁) (h.contragredient χ₁ χ₂ h₁ h₂ π π' hh hiso)

end Assembly

section Fine

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The published theorems for the local Langlands correspondence for $GL_2$, $p$ odd, with the correspondence off the supercuspidal representations replaced by the finer inputs `Langlands.LocalGL2.NonSupercuspidalInputs`. -/
structure GL2OddFineInputs : Prop where
  /-- Local class field theory for quadratic extensions. -/
  artin : ArtinCompat K
  /-- The tame parametrization theorem. -/
  tame : TameParametrizationGL2 K
  /-- The irreducible representations of $W_K$ of dimension 2. -/
  galois : GaloisTameParametrization K
  /-- The rectifier. -/
  rectifier : Rectifier K
  /-- The L-factor of a supercuspidal representation. -/
  lFactor : SupercuspidalLFactor K
  /-- The representations that are not supercuspidal. -/
  nonSc : NonSupercuspidalInputs K

variable {K} in
/-- The finer inputs give the inputs of `Langlands.LocalGL2.GL2OddInputs`. -/
theorem GL2OddFineInputs.toInputs {art : Kˣ ≃ₜ* WeilGroup.Ab K} (hart : IsLocalArtinMap K art)
    (h : GL2OddFineInputs K) : GL2OddInputs K art :=
  ⟨h.artin, h.tame, h.galois, h.rectifier, h.lFactor, nonSupercuspidalLLC_of_inputs art hart h.nonSc⟩

end Fine

end LocalGL2

open ValuativeRel in
/-- **The local Langlands correspondence for $GL_2$, $p$ odd, from finer published theorems.** If for each nonarchimedean local field $K$ with $p \ne 2$ the published theorems in `Langlands.LocalGL2.GL2OddFineInputs` hold, then `Langlands.LocalLanglandsGL2Odd` holds. -/
theorem localLanglandsGL2_odd_of_fineInputs
    (h : ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K], (2 : 𝓀[K]) ≠ 0 → LocalGL2.GL2OddFineInputs K) :
    LocalLanglandsGL2Odd.{u} :=
  localLanglandsGL2_odd_of_inputs fun K _ _ _ _ _ hart hp => (h K hp).toInputs hart

end Langlands
