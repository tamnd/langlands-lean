/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Statements.LocalLanglands

/-!
# The local Langlands correspondence for GSp(4)

Let $R$ be a commutative ring and let
$$J = \begin{pmatrix} 0 & 0 & 0 & 1 \\ 0 & 0 & 1 & 0 \\ 0 & -1 & 0 & 0 \\ -1 & 0 & 0 & 0 \end{pmatrix}.$$
The group $GSp_4(R)$ of symplectic similitudes is the group of the matrices $g \in GL_4(R)$ with ${}^t g J g = \nu(g) J$ for a unit $\nu(g)$ of $R$. The unit $\nu(g)$ is unique, and $\nu : GSp_4(R) \to R^\times$ is a homomorphism, the *similitude character*. The center of $GSp_4(R)$ for a field $R$ is the group of the scalar matrices $z \cdot 1$, and $\nu(z \cdot 1) = z^2$. The upper triangular matrices in $GSp_4$ form a Borel subgroup $B$, with the diagonal torus $T = \{\mathrm{diag}(a, b, c b^{-1}, c a^{-1})\}$, where $c = \nu$. The modulus character of $B$ is $\delta_B(t) = |a^4 b^2 c^{-3}|$.

## The L-parameters

The dual group of $GSp_4$ is $GSp_4(\mathbb{C})$. Let $K$ be a nonarchimedean local field. An *L-parameter* for $GSp_4(K)$ is a Frobenius semisimple Weil-Deligne representation $(r, N)$ of dimension 4 with $r(W_K) \subseteq GSp_4(\mathbb{C})$ and $N$ in the Lie algebra $\mathfrak{sp}_4(\mathbb{C})$, that is ${}^t N J + J N = 0$, up to conjugation by $GSp_4(\mathbb{C})$. A nilpotent element of the Lie algebra of $GSp_4$ has similitude zero, so it is in $\mathfrak{sp}_4$. The *similitude character* of $\varphi = (r, N)$ is the character $\nu \circ r$ of $W_K$.

The centralizer $S_\varphi$ of $\varphi$ in $GSp_4(\mathbb{C})$ contains the center $Z = \mathbb{C}^\times$. The parameter is *discrete* if it does not factor through a proper Levi subgroup. This is the case exactly when $S_\varphi / Z$ is finite. For a discrete parameter $A_\varphi = S_\varphi / Z$ is the component group, and for $GSp_4$ it is trivial or of order 2. For example, if $\varphi = \varphi_1 \oplus \varphi_2$ with $\varphi_1, \varphi_2$ irreducible of dimension 2, not isomorphic, and $\det \varphi_1 = \det \varphi_2$, then $S_\varphi / Z = \{1, \mathrm{diag}(1, 1, -1, -1)\}$ in a suitable basis.

## The theorem of Gan and Takeda

Let $K$ be a nonarchimedean local field of characteristic 0. Gan and Takeda proved that there is a surjective map $L : \mathrm{Irr}(GSp_4(K)) \to \Phi(GSp_4)$ with finite fibers, the L-packets $\Pi_\varphi = L^{-1}(\varphi)$, with these properties.

1. The central character $\omega_\pi$ corresponds to the similitude character $\nu \circ L(\pi)$ through the local Artin map.
2. $L(\pi \otimes \chi \circ \nu) = L(\pi) \otimes \chi$ for each character $\chi$ of $K^\times$, seen as a character of $W_K$.
3. $\pi$ is essentially square integrable exactly when $L(\pi)$ is discrete.
4. For a discrete parameter $\varphi$, $\Pi_\varphi$ is in bijection with the characters of $A_\varphi$, and it contains exactly one generic representation. For a tempered parameter the packet contains exactly one generic representation.
5. For the non-supercuspidal representations $L$ is given by the Langlands classification and the local Langlands correspondence for the Levi subgroups. For example, if $\pi$ is a subrepresentation of the principal series $\chi_1 \times \chi_2 \rtimes \sigma$, then $r(L(\pi)) = \sigma\chi_1\chi_2 \oplus \sigma\chi_1 \oplus \sigma\chi_2 \oplus \sigma$, and $N = 0$ if the principal series is irreducible (Roberts and Schmidt, table A.7).
6. For each generic or non-supercuspidal $\pi$ and each irreducible representation $\tau$ of $GL_r(K)$ with $r \le 2$, the γ-factors, L-factors and ε-factors of pairs agree: $\gamma(s, \pi \times \tau, \psi) = \gamma(s, L(\pi) \otimes \mathrm{rec}(\tau), \psi)$, and the same for $L$ and $\varepsilon$. For a non-generic supercuspidal $\pi$ the Plancherel measures agree.

These properties characterize $L$.

The file states the existence of a map with properties 1, 2, the part of 3 that says that a supercuspidal representation has a discrete parameter, the converse that a representation with an irreducible parameter is supercuspidal, the size $|A_\varphi|$ and the unique generic member of $\Pi_\varphi$ for each discrete $\varphi$, and property 5 for the principal series of the Borel subgroup. Here $\chi_1 \times \chi_2 \rtimes \sigma$ is the normalized induction from $B$ of the character $\mathrm{diag}(a, b, c b^{-1}, c a^{-1}) \mapsto \chi_1(a) \chi_2(b) \sigma(c)$. Its central character is $\chi_1 \chi_2 \sigma^2$, and this is the similitude character of the parameter in property 5 (`Langlands.gspPrincipalSeries_hasCentralChar`, `Langlands.GSpParam.simChar_eq_of_diagonal`).

* `Langlands.gsp4`, `Langlands.gsp4.sim`, `Langlands.gspScalar`: the group $GSp_4(R)$, its similitude character and its center.
* `Langlands.GSpParam`, `Langlands.GSpLParam`: the L-parameters and their classes.
* `Langlands.GSpParam.simChar`, `Langlands.GSpParam.centralizer`, `Langlands.GSpParam.componentCard`, `Langlands.GSpParam.IsDiscrete`.
* `Langlands.relInduced`, `Langlands.gspPrincipalSeries`: induced representations and the principal series $\chi_1 \times \chi_2 \rtimes \sigma$.
* `Langlands.SmoothRep.IsGSpGeneric`: a representation of $GSp_4(K)$ with a Whittaker functional.
* `Langlands.IsGSpLanglandsMap`, `Langlands.LocalLanglandsGSp4`.

## Implementation notes

**What is left out.** The γ-factors of pairs (property 6) are not in the statement. On the automorphic side they are the factors of Shahidi, or of the Rankin-Selberg integrals of Novodvorsky and Piatetski-Shapiro and Soudry, on the Whittaker models. On the Galois side they need the ε-factors of Deligne and Langlands. The Plancherel measures need the theory of intertwining operators. These are the properties that pin down $L$ on the supercuspidal representations. Also left out are the bijection of $\Pi_\varphi$ with the characters of $A_\varphi$ (the statement keeps only the number of elements), the packets of the parameters that are not discrete, the converse of property 3 for the essentially square integrable representations that are not supercuspidal, the monodromy $N$ for the reducible principal series, and the parameters of the representations induced from the Siegel and the Klingen parabolic subgroups.

So the statement does not determine $L$. It is still not true for trivial reasons. The map must send the constituents of each principal series to parameters with the given semisimple part $r$, the irreducible principal series to parameters with $N = 0$, and the central characters to the similitude characters. The fiber over each discrete parameter must have exactly $|A_\varphi|$ elements, one of them generic, and the supercuspidal representations must go to discrete parameters. A proof needs at least the classification of the non-supercuspidal representations of $GSp_4(K)$ (Sally and Tadić), the existence of the generic members of the packets, and a count of the supercuspidal representations by their parameters.

**Decisions.**

* The parameters are classes for the conjugation by $GSp_4(\mathbb{C})$, not by $GL_4(\mathbb{C})$. By a lemma of Gan and Takeda the two notions give the same classes, but the statement does not use the lemma.
* A parameter is discrete when the centralizer $S_\varphi$ has finite index over the center of $GSp_4(\mathbb{C})$, in the form `Subgroup.relIndex` $\ne 0$. Then the index is $|A_\varphi|$.
* The center of $GSp_4(K)$ is the image of `Langlands.gspScalar`, and the supercuspidal representations are those of `Langlands.SmoothRep.IsSupercuspidal` for this center.
* A representation is generic for a nontrivial continuous additive character $\psi$ of $K$ if it has a nonzero linear form $\lambda$ with $\lambda(\pi(u) v) = \psi(u_{12} + u_{23}) \lambda(v)$ for each unipotent upper triangular $u$. The two entries are the coordinates of the simple root groups, so $u \mapsto \psi(u_{12} + u_{23})$ is a generic character of the unipotent radical of $B$. The torus acts transitively on the generic characters, so the notion does not depend on $\psi$. The statement asks the property for each $\psi$.
* The induced representations are spaces of functions on the group that are smooth on the right, with a relation $f(bg) = c f(g)$ for the pairs $(b, c)$ of a relation $P$. For the principal series $P$ is the graph of $\chi \delta_B^{1/2}$ on $B$. This avoids the proof that this function on $B$ is a homomorphism.
* As in `Langlands.LocalLanglandsGL`, the representations are the irreducible admissible ones, and the Artin map is fixed with the conditions of `Langlands.IsLocalArtinMap`.

## References

* W. T. Gan, S. Takeda, The local Langlands conjecture for GSp(4), Ann. of Math. 173 (2011), main theorem.
* W. T. Gan, S. Takeda, Theta correspondences for GSp(4), Represent. Theory 15 (2011).
* B. Roberts, R. Schmidt, Local newforms for GSp(4), LNM 1918, Springer, 2007, section 2.2 and appendix A.
* P. J. Sally, M. Tadić, Induced representations and classifications for GSp(2, F) and Sp(2, F), Mém. Soc. Math. France 52 (1993).
-/

namespace Langlands

universe u

open Matrix

section Symplectic

variable (R : Type u) [CommRing R]

/-- The alternating matrix $J$ with rows $(0, 0, 0, 1)$, $(0, 0, 1, 0)$, $(0, -1, 0, 0)$ and $(-1, 0, 0, 0)$. -/
def gspForm : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/-- The entry $J_{14}$ is 1. -/
theorem gspForm_zero_three : gspForm R 0 3 = 1 := by
  simp [gspForm]

/-- The group $GSp_4(R)$ of the matrices $g \in GL_4(R)$ with ${}^t g J g = c J$ for a unit $c$ of $R$. -/
def gsp4 : Subgroup (GL (Fin 4) R) where
  carrier := {g | ∃ c : Rˣ, g.1ᵀ * gspForm R * g.1 = (c : R) • gspForm R}
  one_mem' := ⟨1, by simp⟩
  mul_mem' {g h} hg hh := by
    obtain ⟨c, hc⟩ := hg
    obtain ⟨d, hd⟩ := hh
    refine ⟨c * d, ?_⟩
    have : (g * h).1ᵀ * gspForm R * (g * h).1 = h.1ᵀ * (g.1ᵀ * gspForm R * g.1) * h.1 := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hc, Matrix.mul_smul, Matrix.smul_mul, hd, smul_smul, Units.val_mul, mul_comm]
  inv_mem' {g} hg := by
    obtain ⟨c, hc⟩ := hg
    refine ⟨c⁻¹, ?_⟩
    have key : g⁻¹.1ᵀ * (g.1ᵀ * gspForm R * g.1) * g⁻¹.1 = gspForm R := by
      have h1 : g⁻¹.1ᵀ * g.1ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.transpose_one]
      have h2 : g.1 * g⁻¹.1 = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc _ = (g⁻¹.1ᵀ * g.1ᵀ) * gspForm R * (g.1 * g⁻¹.1) := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [hc, Matrix.mul_smul, Matrix.smul_mul] at key
    conv_rhs => rw [← key]
    rw [smul_smul, Units.inv_mul, one_smul]

variable {R}

theorem mem_gsp4 {g : GL (Fin 4) R} :
    g ∈ gsp4 R ↔ ∃ c : Rˣ, g.1ᵀ * gspForm R * g.1 = (c : R) • gspForm R :=
  Iff.rfl

/-- The unit $c$ with ${}^t g J g = c J$ for $g \in GSp_4(R)$. -/
noncomputable def gsp4.simVal (g : gsp4 R) : Rˣ :=
  Classical.choose g.2

theorem gsp4.simVal_spec (g : gsp4 R) :
    g.1.1ᵀ * gspForm R * g.1.1 = (gsp4.simVal g : R) • gspForm R :=
  Classical.choose_spec g.2

/-- The similitude of $g$ is the entry $({}^t g J g)_{14}$. -/
theorem gsp4.coe_simVal (g : gsp4 R) :
    (gsp4.simVal g : R) = (g.1.1ᵀ * gspForm R * g.1.1) 0 3 := by
  rw [gsp4.simVal_spec, Matrix.smul_apply, gspForm_zero_three, smul_eq_mul, mul_one]

variable (R)

/-- The similitude character $\nu : GSp_4(R) \to R^\times$, with ${}^t g J g = \nu(g) J$. -/
noncomputable def gsp4.sim : gsp4 R →* Rˣ where
  toFun := gsp4.simVal
  map_one' := by
    ext
    rw [gsp4.coe_simVal]
    simp [gspForm_zero_three]
  map_mul' g h := by
    ext
    rw [Units.val_mul, gsp4.coe_simVal, gsp4.coe_simVal h]
    have : (g * h).1.1ᵀ * gspForm R * (g * h).1.1 =
        h.1.1ᵀ * (g.1.1ᵀ * gspForm R * g.1.1) * h.1.1 := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, gsp4.simVal_spec g, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

variable {R}

theorem gsp4.coe_sim (g : gsp4 R) : (gsp4.sim R g : R) = (g.1.1ᵀ * gspForm R * g.1.1) 0 3 :=
  gsp4.coe_simVal g

theorem gsp4.sim_spec (g : gsp4 R) : g.1.1ᵀ * gspForm R * g.1.1 = (gsp4.sim R g : R) • gspForm R :=
  gsp4.simVal_spec g

/-- If ${}^t g J g = c J$, then $\nu(g) = c$. -/
theorem gsp4.sim_eq {g : gsp4 R} {c : Rˣ} (h : g.1.1ᵀ * gspForm R * g.1.1 = (c : R) • gspForm R) :
    gsp4.sim R g = c := by
  ext
  rw [gsp4.coe_sim, h, Matrix.smul_apply, gspForm_zero_three, smul_eq_mul, mul_one]

variable (R)

/-- The embedding $z \mapsto z \cdot 1$ of $R^\times$ in $GSp_4(R)$. For a field $R$ its image is the center. -/
noncomputable def gspScalar : Rˣ →* gsp4 R :=
  (Units.map (Matrix.scalar (Fin 4) : R →+* Matrix (Fin 4) (Fin 4) R).toMonoidHom).codRestrict _
    fun a => ⟨a * a, by
      simp [← Matrix.smul_one_eq_diagonal, smul_smul]⟩

/-- The similitude of $z \cdot 1$ is $z^2$. -/
theorem sim_gspScalar (a : Rˣ) : gsp4.sim R (gspScalar R a) = a ^ 2 :=
  gsp4.sim_eq (by
    simp [gspScalar, ← Matrix.smul_one_eq_diagonal, smul_smul, pow_two])

/-- The similitude character is continuous. -/
theorem continuous_gsp4_sim [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (gsp4.sim R) := by
  have hv : Continuous fun g : gsp4 R => (g.1.1ᵀ * gspForm R * g.1.1) 0 3 := by
    have : Continuous fun g : gsp4 R => g.1.1 :=
      Units.continuous_val.comp continuous_subtype_val
    exact ((this.matrix_transpose.matrix_mul continuous_const).matrix_mul this).matrix_elem 0 3
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa [Function.comp_def, gsp4.coe_sim] using hv
  · have : (fun g => (((gsp4.sim R g)⁻¹ : Rˣ) : R)) =
        fun g : gsp4 R => ((g⁻¹).1.1ᵀ * gspForm R * (g⁻¹).1.1) 0 3 :=
      funext fun g => by rw [← map_inv, gsp4.coe_sim]
    rw [this]
    exact hv.comp continuous_inv

variable {R}

/-- The diagonal matrix $\mathrm{diag}(z x y, z x, z y, z)$ is in $GSp_4(R)$ with similitude $z^2 x y$. This is the shape of the parameters of the principal series. -/
theorem diagonal_mem_gsp4 (x y z : Rˣ) :
    (Matrix.diagonal ![(z : R) * x * y, z * x, z * y, z])ᵀ * gspForm R *
      Matrix.diagonal ![(z : R) * x * y, z * x, z * y, z] =
        ((z ^ 2 * x * y : Rˣ) : R) • gspForm R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gspForm, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end Symplectic

section Param

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- An L-parameter for $GSp_4(K)$: a Frobenius semisimple Weil-Deligne representation $(r, N)$ of dimension 4 with $r(w) \in GSp_4(\mathbb{C})$ for each $w$ and ${}^t N J + J N = 0$. -/
structure GSpParam where
  /-- The underlying Weil-Deligne representation of dimension 4. -/
  toWD : WeilDeligneRep K 4
  mem : ∀ w, toWD.r w ∈ gsp4 ℂ
  lie : toWD.Nᵀ * gspForm ℂ + gspForm ℂ * toWD.N = 0

namespace GSpParam

variable {K}

/-- Two parameters are isomorphic if one element $g$ of $GSp_4(\mathbb{C})$ conjugates $r$ to $r'$ and $N$ to $N'$. -/
def Iso (φ φ' : GSpParam K) : Prop :=
  ∃ g : gsp4 ℂ, (∀ w, φ'.toWD.r w = g.1 * φ.toWD.r w * g.1⁻¹) ∧
    φ'.toWD.N = g.1.1 * φ.toWD.N * (g.1⁻¹ : GL (Fin 4) ℂ).1

/-- The setoid of conjugation by $GSp_4(\mathbb{C})$. -/
instance setoid : Setoid (GSpParam K) where
  r := Iso
  iseqv := by
    refine ⟨fun φ => ⟨1, fun w => by simp, by simp⟩, ?_, ?_⟩
    · rintro φ φ' ⟨g, hr, hN⟩
      refine ⟨g⁻¹, fun w => by simp [hr, mul_assoc], ?_⟩
      simp [hN, ← mul_assoc]
    · rintro φ φ' φ'' ⟨g, hr, hN⟩ ⟨g', hr', hN'⟩
      refine ⟨g' * g, fun w => by simp [hr, hr', mul_assoc], ?_⟩
      simp [hN, hN', mul_assoc]

/-- The homomorphism $r : W_K \to GSp_4(\mathbb{C})$. -/
noncomputable def rGSp (φ : GSpParam K) : WeilGroup K →* gsp4 ℂ :=
  φ.toWD.r.codRestrict _ φ.mem

/-- The similitude character $\nu \circ r$ of $W_K$. -/
noncomputable def simChar (φ : GSpParam K) : WeilGroup K →* ℂˣ :=
  (gsp4.sim ℂ).comp φ.rGSp

/-- The centralizer $S_\varphi$ of the parameter in $GSp_4(\mathbb{C})$: the elements that commute with each $r(w)$ and with $N$. -/
def centralizer (φ : GSpParam K) : Subgroup (gsp4 ℂ) where
  carrier := {g | ∀ w, Commute g (φ.rGSp w) ∧ Commute g.1.1 φ.toWD.N}
  one_mem' w := ⟨Commute.one_left _, Commute.one_left _⟩
  mul_mem' ha hb w := ⟨(ha w).1.mul_left (hb w).1, by
    simpa using (ha w).2.mul_left (hb w).2⟩
  inv_mem' {g} ha w := ⟨(ha w).1.inv_left, by
    simpa using (ha w).2.units_inv_left⟩

/-- The index of the center $Z$ of $GSp_4(\mathbb{C})$ in $S_\varphi$, and $0$ if it is infinite. For a discrete parameter it is the order of the component group $A_\varphi = S_\varphi / Z$. -/
noncomputable def componentCard (φ : GSpParam K) : ℕ :=
  (Subgroup.center (gsp4 ℂ)).relIndex φ.centralizer

/-- A parameter is discrete if $S_\varphi / Z$ is finite. This is the case exactly when the parameter does not factor through a proper Levi subgroup of $GSp_4(\mathbb{C})$. -/
def IsDiscrete (φ : GSpParam K) : Prop :=
  φ.componentCard ≠ 0

/-- If $r(w) = \mathrm{diag}(\varphi_\sigma \varphi_1 \varphi_2, \varphi_\sigma \varphi_1, \varphi_\sigma \varphi_2, \varphi_\sigma)(w)$ for each $w$, then the similitude character is $\varphi_\sigma^2 \varphi_1 \varphi_2$. -/
theorem simChar_eq_of_diagonal (φ : GSpParam K) (φ₁ φ₂ φσ : WeilGroup K →* ℂˣ)
    (h : ∀ w, (φ.toWD.r w : Matrix (Fin 4) (Fin 4) ℂ) =
      Matrix.diagonal ![(φσ w : ℂ) * φ₁ w * φ₂ w, φσ w * φ₁ w, φσ w * φ₂ w, φσ w]) :
    φ.simChar = φσ ^ 2 * φ₁ * φ₂ := by
  ext w : 1
  refine gsp4.sim_eq ?_
  change (φ.toWD.r w : Matrix (Fin 4) (Fin 4) ℂ)ᵀ * gspForm ℂ * (φ.toWD.r w : Matrix _ _ ℂ) = _
  rw [h, diagonal_mem_gsp4 (φ₁ w) (φ₂ w) (φσ w)]
  simp

end GSpParam

/-- The L-parameters for $GSp_4(K)$: the classes of `GSpParam` under conjugation by $GSp_4(\mathbb{C})$. -/
def GSpLParam : Type u :=
  Quotient (GSpParam.setoid (K := K))

namespace GSpLParam

variable {K}

/-- The class of a parameter. -/
def mk (φ : GSpParam K) : GSpLParam K :=
  Quotient.mk _ φ

/-- `y` is the class of the twist $(\chi r, N)$ of a representative $(r, N)$ of `x` by a character $\chi$ of $W_K$. -/
def IsTwist (y x : GSpLParam K) (χ : WeilGroup K →* ℂˣ) : Prop :=
  ∃ φ φ' : GSpParam K, mk φ = x ∧ mk φ' = y ∧
    (∀ w, (φ'.toWD.r w : Matrix (Fin 4) (Fin 4) ℂ) =
      (χ w : ℂ) • (φ.toWD.r w : Matrix (Fin 4) (Fin 4) ℂ)) ∧ φ'.toWD.N = φ.toWD.N

end GSpLParam

end Param

section Induced

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a relation $P$ between elements of $G$ and complex numbers, the space of the functions $f : G \to \mathbb{C}$ that are invariant on the right under an open subgroup and satisfy $f(bg) = c f(g)$ whenever $P(b, c)$. If $P$ is the graph of a character $\mu$ of a closed subgroup $B$, this is the induced representation $\mathrm{Ind}_B^G \mu$ (without normalization). -/
def relInducedSpace (P : G → ℂ → Prop) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ b c g, P b c → f (b * g) = c * f g) ∧
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, f (g * u) = f g}
  add_mem' {f f'} hf hf' := by
    refine ⟨fun b c g h => ?_, ?_⟩
    · simp only [Pi.add_apply, hf.1 b c g h, hf'.1 b c g h]; ring
    · obtain ⟨U, hU, hfU⟩ := hf.2
      obtain ⟨U', hU', hfU'⟩ := hf'.2
      exact ⟨U ⊓ U', hU.inter hU', fun g u hu => by
        simp [hfU g u (Subgroup.mem_inf.1 hu).1, hfU' g u (Subgroup.mem_inf.1 hu).2]⟩
  zero_mem' := ⟨fun _ _ _ _ => by simp, ⊤, by simp, fun _ _ _ => rfl⟩
  smul_mem' a f hf := by
    refine ⟨fun b c g h => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.1 b c g h]; ring
    · obtain ⟨U, hU, hfU⟩ := hf.2
      exact ⟨U, hU, fun g u hu => by simp [hfU g u hu]⟩

theorem relInducedSpace_stable (P : G → ℂ → Prop) :
    IsStableSubspace (rightRegular G) (relInducedSpace P) := by
  intro h f hf
  refine ⟨fun b c g hb => ?_, ?_⟩
  · change f (b * g * h) = c * f (g * h)
    rw [mul_assoc, hf.1 b c (g * h) hb]
  · obtain ⟨U, hU, hfU⟩ := hf.2
    let c : G →* G := (MulAut.conj h⁻¹).toMonoidHom
    have hc : Continuous c := by
      change Continuous fun x => h⁻¹ * x * h⁻¹⁻¹
      fun_prop
    refine ⟨U.comap c, by rw [Subgroup.coe_comap]; exact hc.isOpen_preimage _ hU, fun g u hu => ?_⟩
    change f (g * u * h) = f (g * h)
    have := hfU (g * h) _ (Subgroup.mem_comap.1 hu)
    simpa [c, mul_assoc] using this

/-- The representation of $G$ by right translation on `relInducedSpace P`. -/
def relInduced (P : G → ℂ → Prop) : SmoothRep G where
  V := relInducedSpace P
  ρ := (rightRegular G).subrepresentation _ (relInducedSpace_stable P)
  smooth f := by
    obtain ⟨U, hU, hfU⟩ := f.2.2
    refine Subgroup.isOpen_mono (H₁ := U) ?_ hU
    intro u hu
    rw [mem_vecStabilizer]
    exact Subtype.ext (funext fun g => hfU g u hu)

end Induced

section PrincipalSeries

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The graph of the character $\chi \delta_B^{1/2}$ of the Borel subgroup $B$ of upper triangular matrices of $GSp_4(K)$: $P(b, c)$ holds if $b$ is upper triangular with diagonal $(a, d, \nu d^{-1}, \nu a^{-1})$ and $c = \chi_1(a) \chi_2(d) \sigma(\nu) |a^4 d^2 \nu^{-3}|^{1/2}$, where $\nu = \nu(b)$. -/
def gspBorelChar (χ₁ χ₂ σ : Kˣ →* ℂˣ) (b : gsp4 K) (c : ℂ) : Prop :=
  (∀ i j : Fin 4, j < i → b.1.1 i j = 0) ∧ ∃ a d : Kˣ, b.1.1 0 0 = a ∧ b.1.1 1 1 = d ∧
    c = (χ₁ a : ℂ) * χ₂ d * σ (gsp4.sim K b) *
      (Real.sqrt (normAbs K ((a : K) ^ 4 * (d : K) ^ 2 / (gsp4.sim K b : K) ^ 3)) : ℂ)

/-- The principal series $\chi_1 \times \chi_2 \rtimes \sigma$ of $GSp_4(K)$: the normalized induction from $B$ of the character $\mathrm{diag}(a, b, c b^{-1}, c a^{-1}) \mapsto \chi_1(a) \chi_2(b) \sigma(c)$. This is the notation of Sally and Tadić and of Roberts and Schmidt. -/
noncomputable def gspPrincipalSeries (χ₁ χ₂ σ : Kˣ →* ℂˣ) : SmoothRep (gsp4 K) :=
  relInduced (gspBorelChar K χ₁ χ₂ σ)

/-- The character $\chi \circ \nu$ of $GSp_4(K)$. -/
noncomputable def gspSimChar (χ : Kˣ →* ℂˣ) : gsp4 K →* ℂˣ :=
  χ.comp (gsp4.sim K)

theorem isOpen_ker_gspSimChar (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ) :
    IsOpen ((gspSimChar K χ).ker : Set (gsp4 K)) :=
  (continuous_gsp4_sim K).isOpen_preimage _ hχ

/-- An element of $GSp_4(K)$ is unipotent upper triangular: zero below the diagonal and one on the diagonal. These elements form the unipotent radical of $B$. -/
def IsGSpUnipotent (u : gsp4 K) : Prop :=
  ∀ i j : Fin 4, j ≤ i → u.1.1 i j = if i = j then 1 else 0

/-- A representation $\pi$ of $GSp_4(K)$ is generic for the additive character $\psi$ if there is a nonzero linear form $\lambda$ on $V$ with $\lambda(\pi(u) v) = \psi(u_{12} + u_{23}) \lambda(v)$ for each unipotent upper triangular $u$ (a Whittaker functional). -/
def SmoothRep.IsGSpGeneric (π : SmoothRep (gsp4 K)) (ψ : AddChar K ℂ) : Prop :=
  ∃ l : Module.Dual ℂ π.V, l ≠ 0 ∧ ∀ (u : gsp4 K) (v : π.V), IsGSpUnipotent K u →
    l (π.ρ u v) = ψ (u.1.1 0 1 + u.1.1 1 2) * l v

/-- The class `x` is generic for $\psi$ if some representative is. -/
def IrrSmooth.IsGSpGeneric (x : IrrSmooth (gsp4 K)) (ψ : AddChar K ℂ) : Prop :=
  ∃ π : IrrRep (gsp4 K), IrrSmooth.mk π = x ∧ π.1.IsGSpGeneric K ψ

/-- $\pi$ has central character $\omega$ for the embedding $\iota : K^\times \to G$ of the center: $\pi(\iota(a)) = \omega(a)$ for each $a \in K^\times$. -/
def SmoothRep.HasCentralCharVia {G : Type u} [Group G] [TopologicalSpace G] (π : SmoothRep G)
    (ι : Kˣ →* G) (ω : Kˣ →* ℂˣ) : Prop :=
  ∀ (a : Kˣ) (v : π.V), π.ρ (ι a) v = (ω a : ℂ) • v

/-- The central character of the principal series $\chi_1 \times \chi_2 \rtimes \sigma$ is $\chi_1 \chi_2 \sigma^2$. With `GSpParam.simChar_eq_of_diagonal` this shows that the conditions `central` and `principalSeries` of `IsGSpLanglandsMap` agree on the principal series. -/
theorem gspPrincipalSeries_hasCentralChar (χ₁ χ₂ σ : Kˣ →* ℂˣ) :
    (gspPrincipalSeries K χ₁ χ₂ σ).HasCentralCharVia K (gspScalar K) (χ₁ * χ₂ * σ ^ 2) := by
  intro a f
  apply Subtype.ext
  funext g
  change f.1 (g * gspScalar K a) = ((χ₁ * χ₂ * σ ^ 2) a : ℂ) * f.1 g
  have hc : g * gspScalar K a = gspScalar K a * g := by
    apply Subtype.ext
    apply Units.ext
    simp [gspScalar, ← Matrix.smul_one_eq_diagonal]
  rw [hc, f.2.1 _ _ g ⟨?_, a, a, ?_, ?_, rfl⟩]
  · rw [sim_gspScalar]
    have : ((a : K) ^ 4 * (a : K) ^ 2 / ((a ^ 2 : Kˣ) : K) ^ 3) = 1 := by
      have ha : (a : K) ≠ 0 := a.ne_zero
      push_cast
      field_simp
    have h1 : normAbs K 1 = 1 := by simp [normAbs]
    rw [this, h1]
    simp [pow_two, mul_assoc]
  · intro i j hij
    simp [gspScalar, Matrix.diagonal, hij.ne']
  · simp [gspScalar]
  · simp [gspScalar]

end PrincipalSeries

/-- The conditions on a map $L : \mathrm{Irr}(GSp_4(K)) \to \Phi(GSp_4)$ that the statement keeps from the main theorem of Gan and Takeda. The γ-factors of pairs, the Plancherel measures and the parametrization of the packets by the characters of $A_\varphi$ are left out, so these conditions do not determine $L$. -/
structure IsGSpLanglandsMap (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (art : Kˣ ≃ₜ* WeilGroup.Ab K)
    (L : IrrSmooth (gsp4 K) → GSpLParam K) : Prop where
  /-- Each parameter has a nonempty L-packet. -/
  surjective : Function.Surjective L
  /-- Each L-packet is finite. -/
  finite_fiber : ∀ x, (L ⁻¹' {x}).Finite
  /-- The central character corresponds to the similitude character. -/
  central : ∀ (π : IrrRep (gsp4 K)) (ω : Kˣ →* ℂˣ), π.1.HasCentralCharVia K (gspScalar K) ω →
    ∀ φ : GSpParam K, GSpLParam.mk φ = L (IrrSmooth.mk π) → CharCorrespond K art ω φ.simChar
  /-- $L(\pi \otimes \chi \circ \nu) = L(\pi) \otimes \chi$. -/
  twist : ∀ (x y : IrrSmooth (gsp4 K)) (χ : Kˣ →* ℂˣ) (hχ : IsSmoothChar K χ),
    IrrSmooth.IsTwist y x (gspSimChar K χ) (isOpen_ker_gspSimChar K χ hχ) →
      ∀ φ : WeilGroup K →* ℂˣ, CharCorrespond K art χ φ → GSpLParam.IsTwist (L y) (L x) φ
  /-- A subrepresentation of $\chi_1 \times \chi_2 \rtimes \sigma$ has a parameter with $r = \varphi_\sigma \varphi_1 \varphi_2 \oplus \varphi_\sigma \varphi_1 \oplus \varphi_\sigma \varphi_2 \oplus \varphi_\sigma$, and $N = 0$ if the principal series is irreducible. -/
  principalSeries : ∀ (π : IrrRep (gsp4 K)) (χ₁ χ₂ σ : Kˣ →* ℂˣ), IsSmoothChar K χ₁ →
    IsSmoothChar K χ₂ → IsSmoothChar K σ → π.1.HasHom (gspPrincipalSeries K χ₁ χ₂ σ) →
      ∀ φ₁ φ₂ φσ : WeilGroup K →* ℂˣ, CharCorrespond K art χ₁ φ₁ → CharCorrespond K art χ₂ φ₂ →
        CharCorrespond K art σ φσ → ∃ φ : GSpParam K, GSpLParam.mk φ = L (IrrSmooth.mk π) ∧
          (∀ w, (φ.toWD.r w : Matrix (Fin 4) (Fin 4) ℂ) =
            Matrix.diagonal ![(φσ w : ℂ) * φ₁ w * φ₂ w, φσ w * φ₁ w, φσ w * φ₂ w, φσ w]) ∧
          ((gspPrincipalSeries K χ₁ χ₂ σ).IsIrreducible → φ.toWD.N = 0)
  /-- A supercuspidal representation has a discrete parameter. -/
  supercuspidal : ∀ π : IrrRep (gsp4 K), π.1.IsSupercuspidal (gspScalar K) →
    ∀ φ : GSpParam K, GSpLParam.mk φ = L (IrrSmooth.mk π) → φ.IsDiscrete
  /-- A representation whose parameter is irreducible of dimension 4 is supercuspidal. -/
  irreducible : ∀ (π : IrrRep (gsp4 K)) (φ : GSpParam K), GSpLParam.mk φ = L (IrrSmooth.mk π) →
    φ.toWD.IsIrreducible → π.1.IsSupercuspidal (gspScalar K)
  /-- The L-packet of a discrete parameter has $|A_\varphi|$ elements. -/
  card_fiber : ∀ φ : GSpParam K, φ.IsDiscrete →
    Nat.card (L ⁻¹' {GSpLParam.mk φ}) = φ.componentCard
  /-- The L-packet of a discrete parameter has exactly one generic member, for each nontrivial continuous additive character $\psi$. -/
  generic : ∀ ψ : AddChar K ℂ, ψ ≠ 1 → Continuous ψ → ∀ φ : GSpParam K, φ.IsDiscrete →
    ∃! x, L x = GSpLParam.mk φ ∧ x.IsGSpGeneric K ψ

/-- **The local Langlands correspondence for $GSp_4$** (Gan and Takeda), existence part. For each nonarchimedean local field $K$ of characteristic 0 and each local Artin map $\mathrm{art}_K$, there is a surjective map $L : \mathrm{Irr}(GSp_4(K)) \to \Phi(GSp_4)$ with finite fibers such that:

* the central character $\omega_\pi$ corresponds to the similitude character of $L(\pi)$;
* $L(\pi \otimes \chi \circ \nu) = L(\pi) \otimes (\chi \circ \mathrm{art}_K^{-1})$;
* a subrepresentation of the principal series $\chi_1 \times \chi_2 \rtimes \sigma$ has a parameter with $r = \varphi_\sigma \varphi_1 \varphi_2 \oplus \varphi_\sigma \varphi_1 \oplus \varphi_\sigma \varphi_2 \oplus \varphi_\sigma$, where $\varphi = \chi \circ \mathrm{art}_K^{-1}$, and with $N = 0$ if the principal series is irreducible;
* a supercuspidal representation has a discrete parameter, and a representation with an irreducible parameter is supercuspidal;
* the L-packet of a discrete parameter $\varphi$ has $|A_\varphi|$ elements, exactly one of them generic.

The γ-factors of pairs with $GL_1$ and $GL_2$ and the Plancherel measures, which characterize $L$ in the theorem of Gan and Takeda, are not part of the statement. So the statement does not say that $L$ is unique, and the conditions do not determine $L$ on the supercuspidal representations. The module docstring lists the other parts that are left out. -/
def LocalLanglandsGSp4 : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] (art : Kˣ ≃ₜ* WeilGroup.Ab K), IsLocalArtinMap K art →
      ∃ L : IrrSmooth (gsp4 K) → GSpLParam K, IsGSpLanglandsMap K art L

end Langlands
