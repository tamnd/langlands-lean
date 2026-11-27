/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Tate.HeckeShiftRamifiedTheta

/-!
# The functional equation pair of a ramified character with unequal shifts

This file makes the functional equation pair of `Langlands/Tate/HeckeRamifiedSign.lean` for the twisted theta series with the coefficients $c_J$ of `Langlands/Tate/HeckeShiftRamifiedTheta.lean`. The twist by $\tau_\theta$ gives a different shift $i \theta_w$ at each infinite place $w$.

The coefficients have $c_J(0) = 0$. Thus the pair has the constant terms zero for all weights, and the completed partial sums are entire.

## Main definitions

* `Langlands.Tate.shiftCoeffCubeTheta`, `Langlands.Tate.shiftCoeffCubeDualTheta`: the cube averages of the twisted series with a coefficient.
* `Langlands.Tate.shiftRamifiedFEPair`: the functional equation pair of the cube averages of $c_J$ and $\overline{c_D}$.
* `Langlands.Tate.shiftRamifiedPartial`: the completed partial sum $\Lambda_J$ of $c_J$ with the shifts.
* `Langlands.Tate.shiftRamifiedPartialConj`: the conjugate completed partial sum $\Lambda^*_D$ of $c_D$ with the shifts.

## Main results

* `Langlands.Tate.differentiable_shiftRamifiedPartial`, `Langlands.Tate.differentiable_shiftRamifiedPartialConj`: the two partial sums are entire.
* `Langlands.Tate.shiftRamifiedPartial_sub`: $\Lambda_J(n / 2 - s) = \varepsilon_J \, \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \Lambda^*_D(s)$.
* `Langlands.Tate.hasSum_shiftRamifiedPartial`, `Langlands.Tate.hasSum_shiftRamifiedPartialConj`: the two partial sums as series for $\mathrm{Re}\, s > n / 2$.
-/

open MeasureTheory Module Filter Topology Set Complex Asymptotics ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem IsDedekindDomain
open scoped Real Classical nonZeroDivisors ENNReal

namespace Langlands.Tate

/-- The cube $[0, 1)^r$ of the unit coordinates. -/
local notation "cube" => Set.pi univ fun _ : Fin (rank _) => Ico (0 : ℝ) 1

section Cube

variable (K : Type*) [Field K] [NumberField K]
variable (ε : {w : InfinitePlace K // IsComplex w} → Bool)
variable (p : {w : InfinitePlace K // IsReal w} → ℕ) (k : {w : InfinitePlace K // IsComplex w} → ℕ)
variable (θ : InfinitePlace K → ℝ)

/-- The cube average $F(y) = \int_{[0, 1)^r} \tau_\theta(t(y, c)) \, \Theta_{\mathfrak{b}}^{p, k}(f; t(y, c)) \, dc$ of the twisted theta series with the coefficient $f$. -/
noncomputable def shiftCoeffCubeTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : K → ℂ) (y : ℝ) : ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    shiftCoeffTheta K ε p k θ b f (unitScale K y c)

/-- The cube average $G(y) = \int_{[0, 1)^r} \tau_{-\theta}(t(y, -c)) \, \Theta_{\mathfrak{b}}^{\vee, p, k}(g; t(y, -c)) \, dc$ of the twisted dual theta series with the coefficient $g$. -/
noncomputable def shiftCoeffCubeDualTheta (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : K → ℂ) (y : ℝ) :
    ℂ :=
  ∫ c in Set.pi univ (fun _ : Fin (rank K) => Ico (0 : ℝ) 1),
    shiftCoeffDualTheta K ε p k θ b g (unitScale K y (-c))

variable {K ε p k θ}
variable {f g : K → ℂ}

/-- If $|f| \le 1$ and $f(0) = 0$, then the cube average $F$ is continuous on $y > 0$. -/
theorem continuousOn_shiftCoeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (shiftCoeffCubeTheta K ε p k θ b f) (Ioi 0) :=
  continuousOn_integral_unitCube (u := id) _ continuous_id
    (fun _ hc i => abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_shiftCoeffTheta hf1 b ht)
    fun _ hs => ⟨_, fun _ hst =>
      (norm_shiftCoeffTheta b _).trans_le (norm_signCoeffTheta_le hf1 hf0 b hs hst)⟩

/-- If $|g| \le 1$ and $g(0) = 0$, then the dual cube average $G$ is continuous on $y > 0$. -/
theorem continuousOn_shiftCoeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (shiftCoeffCubeDualTheta K ε p k θ b g) (Ioi 0) :=
  continuousOn_integral_unitCube (u := Neg.neg) _ continuous_neg
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (fun _ ht => continuousAt_shiftCoeffDualTheta hg1 b ht)
    fun _ hs => ⟨_, fun _ hst =>
      (norm_shiftCoeffDualTheta b _).trans_le (norm_signCoeffDualTheta_le hg1 hg0 b hs hst)⟩

/-- If $|f| \le 1$ and $f(0) = 0$, then $F(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_shiftCoeffCubeTheta (hf1 : ∀ α, ‖f α‖ ≤ 1) (hf0 : f 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    shiftCoeffCubeTheta K ε p k θ b f =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := id) _ (fun _ hc i => abs_le_one_of_mem_unitCube hc i) b
    heckeConst_pos.le (fun _ hs _ hst =>
      (norm_shiftCoeffTheta b _).trans_le (norm_signCoeffTheta_le hf1 hf0 b hs hst)) r

/-- If $|g| \le 1$ and $g(0) = 0$, then $G(y) = O(y^r)$ at infinity for each real $r$. -/
theorem isBigO_shiftCoeffCubeDualTheta (hg1 : ∀ β, ‖g β‖ ≤ 1) (hg0 : g 0 = 0)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    shiftCoeffCubeDualTheta K ε p k θ b g =O[atTop] (· ^ r) :=
  isBigO_integral_unitCube (u := Neg.neg) _
    (fun _ hc i => by rw [Pi.neg_apply, abs_neg]; exact abs_le_one_of_mem_unitCube hc i)
    (dualUnit K b) heckeConst_pos.le (fun _ hs _ hst =>
      (norm_shiftCoeffDualTheta b _).trans_le (norm_signCoeffDualTheta_le hg1 hg0 b hs hst)) r

end Cube

section Pair

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ}

/-- **The functional equation of the twisted cube averages of $c_J$.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. For $x > 0$, $F_J(1 / x) = \varepsilon_J \, x^{n / 2} \, G_J(x)$, where $F_J$ is the twisted cube average of $c_J$ on $J$ and $G_J$ is the twisted dual cube average of $\overline{c_D}$ on $\mathfrak{f} J$. -/
theorem shiftCoeffCubeTheta_one_div (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) {x : ℝ} (hx : 0 < x) :
    shiftCoeffCubeTheta K ε p k θ (FractionalIdeal.mk0 K J)
        (periodicCoeff χ (FractionalIdeal.mk0 K J)) (1 / x) =
      (ramifiedRootConst χ p k J * ((x ^ ((finrank ℚ K : ℝ) / 2) : ℝ) : ℂ)) •
        shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) x := by
  have hk : √x ^ finrank ℚ K = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hinv : (1 / x)⁻¹ = x := by rw [one_div, inv_inv]
  have hs : ((√(1 / x) ^ finrank ℚ K)⁻¹ : ℝ) = x ^ ((finrank ℚ K : ℝ) / 2) := by
    rw [one_div, Real.sqrt_inv, inv_pow, inv_inv, hk]
  rw [shiftCoeffCubeTheta, shiftCoeffCubeDualTheta, smul_eq_mul]
  simp_rw [shiftCoeffTheta_periodicCoeff_unitScale hS hu hp J (one_div_pos.2 hx), hinv, hs]
  rw [integral_const_mul]

variable (ε p k θ) in
/-- **The twisted FE pair of a ramified character.** Let $\chi$ be unitary and ramified at one place, and let $p_v \le 1$. The twisted cube averages $F_J$ of $c_J$ and $G_J$ of $\overline{c_D}$ are a Mathlib FE pair of weight $n / 2$ with the constant $\varepsilon_J$ and with both constant terms zero. -/
noncomputable def shiftRamifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : WeakFEPair ℂ where
  f := shiftCoeffCubeTheta K ε p k θ (FractionalIdeal.mk0 K J)
    (periodicCoeff χ (FractionalIdeal.mk0 K J))
  g := shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
    (fun β => conj (periodicCoeff χ (gaussDual χ J) β))
  k := finrank ℚ K / 2
  ε := ramifiedRootConst χ p k J
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_shiftCoeffCubeTheta (norm_periodicCoeff_le hu _) (periodicCoeff_zero _)
    _).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_shiftCoeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
    (by rw [periodicCoeff_zero, map_zero]) _).locallyIntegrableOn measurableSet_Ioi
  hk := by have := finrank_pos (R := ℚ) (M := K); positivity
  hε := ramifiedRootConst_ne_zero hS hu J
  h_feq x hx := shiftCoeffCubeTheta_one_div hS hu hp J hx
  hf_top r := by
    simpa only [sub_zero] using isBigO_shiftCoeffCubeTheta (norm_periodicCoeff_le hu _)
      (periodicCoeff_zero _) _ r
  hg_top r := by
    simpa only [sub_zero] using isBigO_shiftCoeffCubeDualTheta (norm_conj_periodicCoeff_le hu _)
      (by rw [periodicCoeff_zero, map_zero]) _ r

/-- The twisted FE pair of a ramified character is a strong FE pair. -/
theorem isStrongFEPair_shiftRamifiedFEPair (hS : (ramifiedSet χ).Nonempty)
    (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1) (hp : ∀ v, p v ≤ 1)
    (J : (Ideal (𝓞 K))⁰) : IsStrongFEPair (shiftRamifiedFEPair ε p k θ hS hu hp J) :=
  ⟨rfl, rfl⟩

end Pair

section Completed

variable {K : Type*} [Field K] [NumberField K] {χ : HeckeCharacter K}
variable {ε : {w : InfinitePlace K // IsComplex w} → Bool}
variable {p : {w : InfinitePlace K // IsReal w} → ℕ} {k : {w : InfinitePlace K // IsComplex w} → ℕ}
variable {θ : InfinitePlace K → ℝ}
variable (hS : (ramifiedSet χ).Nonempty) (hu : ∀ x : IdeleGroup (𝓞 K) K, ‖(ideleChar χ x : ℂ)‖ = 1)
variable (hp : ∀ v, p v ≤ 1)

/-- The completed function of the twisted ramified pair is the Mellin transform of $F_J$. -/
theorem Λ_shiftRamifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (shiftRamifiedFEPair ε p k θ hS hu hp J).Λ =
      mellin (shiftCoeffCubeTheta K ε p k θ (FractionalIdeal.mk0 K J)
        (periodicCoeff χ (FractionalIdeal.mk0 K J))) :=
  (isStrongFEPair_shiftRamifiedFEPair hS hu hp J).Λ_eq

/-- The completed function of the dual twisted ramified pair is the Mellin transform of $G_J$. -/
theorem symm_Λ_shiftRamifiedFEPair_eq (J : (Ideal (𝓞 K))⁰) :
    (shiftRamifiedFEPair ε p k θ hS hu hp J).symm.Λ =
      mellin (shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) :=
  (isStrongFEPair_shiftRamifiedFEPair hS hu hp J).symm_Λ_eq

/-- The functional equation $\Lambda_J(n / 2 - s) = \varepsilon_J \, \mathcal{M}G_J(s)$ of the twisted ramified pair for all complex $s$. -/
theorem Λ_shiftRamifiedFEPair_sub (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (shiftRamifiedFEPair ε p k θ hS hu hp J).Λ (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J *
        mellin (shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
          (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s := by
  have := (shiftRamifiedFEPair ε p k θ hS hu hp J).functional_equation s
  rw [symm_Λ_shiftRamifiedFEPair_eq hS hu hp J, smul_eq_mul] at this
  convert this using 2
  · simp [shiftRamifiedFEPair]
  · rfl

/-- **The twisted dual series is the conjugate series.** If $c_D(u \beta) \chi_\infty(u) \tau_\theta(u) = c_D(\beta)$ for all units $u$, where $D = (\mathfrak{f} J)^\vee$, and $y > 0$, then $G_J(y) = \tau_\theta((n_w^2)_w) \, \overline{F_D(\lambda y)}$, where $F_D$ is the twisted cube average of $c_D$ on $D$. -/
theorem shiftCoeffCubeDualTheta_eq_conj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β) {y : ℝ} (hy : 0 < y) :
    shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β)) y =
      torusConst θ * conj (shiftCoeffCubeTheta K ε p k θ (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J)) (heckeScale K * y)) := by
  have h : ∀ c : Fin (rank K) → ℝ,
      (fun w => (mult w : ℝ) ^ 2 * unitScale K y (-c) w) =
        unitScale K (heckeScale K * y) (heckeShift K - c) :=
    fun c => funext fun w => mult_sq_mul_unitScale_neg y c w
  have hcc : (fun β => conj (conj (periodicCoeff χ (gaussDual χ J) β))) =
      periodicCoeff χ (gaussDual χ J) := funext fun β => Complex.conj_conj _
  have hd : dualUnit K (FractionalIdeal.mk0 K (conductorNZ χ * J)) = gaussDual χ J := rfl
  rw [shiftCoeffCubeDualTheta, shiftCoeffCubeTheta]
  simp_rw [shiftCoeffDualTheta_eq ε p k θ _ _ (unitScale_pos hy _), hcc, hd, h]
  rw [integral_const_mul, integral_conj, integral_unitCube_sub
    (fun c => shiftCoeffTheta K ε p k θ (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))
      (unitScale K (heckeScale K * y) c))
    (fun m c => shiftCoeffTheta_unitScale_add_int hc _ (mul_pos (heckeScale_pos K) hy) c m)
    (heckeShift K)]

/-- **The Mellin transform of the twisted dual series.** Under the unit condition of `Langlands.Tate.shiftCoeffCubeDualTheta_eq_conj`, $\mathcal{M}G_J(s) = \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \overline{\mathcal{M}F_D(\bar{s})}$ for all complex $s$. -/
theorem mellin_shiftCoeffCubeDualTheta (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    mellin (shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      torusConst θ * (heckeScale K : ℂ) ^ (-s) * conj (mellin (shiftCoeffCubeTheta K ε p k θ
        (gaussDual χ J) (periodicCoeff χ (gaussDual χ J))) (conj s)) := by
  have h : mellin (shiftCoeffCubeDualTheta K ε p k θ (FractionalIdeal.mk0 K (conductorNZ χ * J))
        (fun β => conj (periodicCoeff χ (gaussDual χ J) β))) s =
      mellin (fun y => torusConst θ • conj (shiftCoeffCubeTheta K ε p k θ (gaussDual χ J)
        (periodicCoeff χ (gaussDual χ J)) (heckeScale K * y))) s :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by
      simp only [shiftCoeffCubeDualTheta_eq_conj J hc hy, smul_eq_mul]
  rw [h, mellin_const_smul, mellin_conj, mellin_comp_mul_left _ _ (heckeScale_pos K), smul_eq_mul,
    smul_eq_mul, map_mul, conj_ofReal_cpow (heckeScale_pos K).le, map_neg, Complex.conj_conj]
  ring

variable (χ ε p k θ) in
/-- The completed partial sum $\Lambda_J(s) = 2^r c_K \, \mathcal{M}F_J(s)$ of the coefficient $c_J$ on the integral ideal $J$ with the shifts $i \theta_w$. -/
noncomputable def shiftRamifiedPartial (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (shiftCoeffCubeTheta K ε p k θ (FractionalIdeal.mk0 K J)
      (periodicCoeff χ (FractionalIdeal.mk0 K J))) s

variable (χ ε p k θ) in
/-- The conjugate completed partial sum $\Lambda^*_D(s) = \overline{2^r c_K \, \mathcal{M}F_D(\bar{s})}$ of the coefficient $c_D$ on $D = (\mathfrak{f} J)^\vee$ with the shifts $i \theta_w$. -/
noncomputable def shiftRamifiedPartialConj (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  conj (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
    mellin (shiftCoeffCubeTheta K ε p k θ (gaussDual χ J) (periodicCoeff χ (gaussDual χ J)))
      (conj s))

include hS hu hp in
/-- **The twisted completed partial sum is entire.** -/
theorem differentiable_shiftRamifiedPartial (J : (Ideal (𝓞 K))⁰) :
    Differentiable ℂ (shiftRamifiedPartial χ ε p k θ J) := by
  have e : shiftRamifiedPartial χ ε p k θ J = fun s =>
      ((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (shiftRamifiedFEPair ε p k θ hS hu hp J).Λ s := by
    funext s
    rw [Λ_shiftRamifiedFEPair_eq hS hu hp J, shiftRamifiedPartial]
  rw [e]
  exact (isStrongFEPair_shiftRamifiedFEPair hS hu hp J).differentiable_Λ.const_mul _

include hS hu hp in
/-- Under the unit condition for $c_D$, $\Lambda^*_D(s) = \tau_\theta((n_w^2)_w)^{-1} \, \lambda^s \, 2^r c_K \, \mathcal{M}G_J(s)$. -/
theorem shiftRamifiedPartialConj_eq (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    shiftRamifiedPartialConj χ ε p k θ J s = (torusConst θ)⁻¹ * (heckeScale K : ℂ) ^ s *
      (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (shiftRamifiedFEPair ε p k θ hS hu hp J).symm.Λ s) := by
  have hl : (heckeScale K : ℂ) ^ s * (heckeScale K : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.2 (heckeScale_pos K).ne'), add_neg_cancel, cpow_zero]
  have hT : (torusConst θ)⁻¹ * torusConst θ = 1 :=
    inv_mul_cancel₀ (norm_ne_zero_iff.1 (by rw [norm_torusConst]; exact one_ne_zero))
  rw [symm_Λ_shiftRamifiedFEPair_eq hS hu hp J, mellin_shiftCoeffCubeDualTheta J hc,
    shiftRamifiedPartialConj, map_mul, Complex.conj_ofReal]
  set C := ((unitConst K * 2 ^ rank K : ℝ) : ℂ)
  set M := conj (mellin (shiftCoeffCubeTheta K ε p k θ (gaussDual χ J)
    (periodicCoeff χ (gaussDual χ J))) (conj s))
  linear_combination (-(C * M * ((torusConst θ)⁻¹ * torusConst θ))) * hl - C * M * hT

include hS hu hp in
/-- **The twisted conjugate completed partial sum is entire.** -/
theorem differentiable_shiftRamifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β) :
    Differentiable ℂ (shiftRamifiedPartialConj χ ε p k θ J) := by
  have e : shiftRamifiedPartialConj χ ε p k θ J = fun s =>
      (torusConst θ)⁻¹ * (heckeScale K : ℂ) ^ s *
        (((unitConst K * 2 ^ rank K : ℝ) : ℂ) * (shiftRamifiedFEPair ε p k θ hS hu hp J).symm.Λ s) :=
    funext (shiftRamifiedPartialConj_eq hS hu hp J hc)
  rw [e]
  refine Differentiable.mul (Differentiable.const_mul (fun s => ?_) _)
    ((isStrongFEPair_shiftRamifiedFEPair hS hu hp J).symm.differentiable_Λ.const_mul _)
  exact differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 (heckeScale_pos K).ne'))

include hS hu hp in
/-- **The functional equation of the twisted completed partial sums.** Let $\chi$ be unitary and ramified at one place, let $p_v \le 1$, and let $c_D$ satisfy the unit condition with $\tau_\theta$. Then for all complex $s$, $\Lambda_J(n / 2 - s) = \varepsilon_J \, \tau_\theta((n_w^2)_w) \, \lambda^{-s} \, \Lambda^*_D(s)$. -/
theorem shiftRamifiedPartial_sub (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β) (s : ℂ) :
    shiftRamifiedPartial χ ε p k θ J (finrank ℚ K / 2 - s) =
      ramifiedRootConst χ p k J * torusConst θ * (heckeScale K : ℂ) ^ (-s) *
        shiftRamifiedPartialConj χ ε p k θ J s := by
  rw [shiftRamifiedPartial, ← Λ_shiftRamifiedFEPair_eq hS hu hp J, Λ_shiftRamifiedFEPair_sub,
    mellin_shiftCoeffCubeDualTheta J hc, shiftRamifiedPartialConj, map_mul, Complex.conj_ofReal]
  ring

include hu in
/-- **The twisted completed partial sum as a series.** If $c_J$ satisfies the unit condition with $\tau_\theta$ and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda_J(s) = \sum_{\alpha \in (J \setminus 0) / \mathcal{O}_K^\times} w_K \, c_J(\alpha) \, \Gamma_{p, k}^\theta(s') \, \chi_\infty(\alpha) \, \tau_\theta(\alpha) \, |N(\alpha)|^{-s'}.$$ -/
theorem hasSum_shiftRamifiedPartial (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (α : K), periodicCoeff χ (FractionalIdeal.mk0 K J) ((u : K) * α) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (FractionalIdeal.mk0 K J) α)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (FractionalIdeal.mk0 K J) => (torsionOrder K : ℂ) *
        (periodicCoeff χ (FractionalIdeal.mk0 K J) (orbitRep (FractionalIdeal.mk0 K J) I) *
        (shiftGamma p k θ (2 * s / finrank ℚ K) *
          signInfinityWeight ε p k (orbitRep (FractionalIdeal.mk0 K J) I : K) *
          torusWeight θ (orbitRep (FractionalIdeal.mk0 K J) I : K) *
          ((|(Algebra.norm ℚ (orbitRep (FractionalIdeal.mk0 K J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (shiftRamifiedPartial χ ε p k θ J s) := by
  have h := hasSum_integral_shiftCoeffTheta (a := FractionalIdeal.mk0 K J)
    (norm_periodicCoeff_le hu _) (periodicCoeff_zero _) hc hs
  rw [shiftRamifiedPartial, mellin]
  simp_rw [smul_eq_mul, shiftCoeffCubeTheta]
  exact h

include hu in
/-- **The twisted conjugate completed partial sum as a series.** If $c_D$ satisfies the unit condition with $\tau_\theta$ and $\mathrm{Re}\, s > n / 2$, then with $s' = 2 s / n$, $$\Lambda^*_D(s) = \sum_{\beta \in (D \setminus 0) / \mathcal{O}_K^\times} w_K \, \overline{c_D(\beta)} \, \Gamma_{p, k}^{-\theta}(s') \, \overline{\chi_\infty(\beta)} \, \tau_{-\theta}(\beta) \, |N(\beta)|^{-s'}.$$ -/
theorem hasSum_shiftRamifiedPartialConj (J : (Ideal (𝓞 K))⁰)
    (hc : ∀ (u : (𝓞 K)ˣ) (β : K), periodicCoeff χ (gaussDual χ J) ((u : K) * β) *
      signInfinityWeight ε p k (u : K) * torusWeight θ (u : K) =
        periodicCoeff χ (gaussDual χ J) β)
    {s : ℂ} (hs : (finrank ℚ K : ℝ) / 2 < s.re) :
    HasSum (fun I : Orbits (gaussDual χ J) => (torsionOrder K : ℂ) *
        (conj (periodicCoeff χ (gaussDual χ J) (orbitRep (gaussDual χ J) I)) *
        (shiftGamma p k (-θ) (2 * s / finrank ℚ K) *
          conj (signInfinityWeight ε p k (orbitRep (gaussDual χ J) I : K)) *
          torusWeight (-θ) (orbitRep (gaussDual χ J) I : K) *
          ((|(Algebra.norm ℚ (orbitRep (gaussDual χ J) I : K) : ℝ)| : ℝ) : ℂ) ^
            (-(2 * s / finrank ℚ K)))))
      (shiftRamifiedPartialConj χ ε p k θ J s) := by
  have hs' : (finrank ℚ K : ℝ) / 2 < (conj s).re := by rwa [Complex.conj_re]
  have h := hasSum_integral_shiftCoeffTheta (a := gaussDual χ J)
    (norm_periodicCoeff_le hu _) (periodicCoeff_zero _) hc hs'
  have e := h.map (starRingEnd ℂ) continuous_conj
  have hv : shiftRamifiedPartialConj χ ε p k θ J s =
      starRingEnd ℂ (((unitConst K * 2 ^ rank K : ℝ) : ℂ) *
        ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (conj s - 1) *
          ∫ c in Set.pi univ (fun _ => Ico (0 : ℝ) 1), shiftCoeffTheta K ε p k θ (gaussDual χ J)
            (periodicCoeff χ (gaussDual χ J)) (unitScale K y c)) := by
    rw [shiftRamifiedPartialConj, mellin]
    simp_rw [smul_eq_mul, shiftCoeffCubeTheta]
  rw [hv]
  have hcs : 2 * conj s / (finrank ℚ K : ℂ) = conj (2 * s / finrank ℚ K) := by
    simp [map_div₀, map_ofNat]
  refine e.congr_fun fun I => ?_
  simp only [Function.comp_apply, hcs, map_mul, map_natCast, ← map_neg,
    conj_ofReal_cpow (abs_nonneg _), Complex.conj_conj, conj_shiftGamma, conj_torusWeight]

end Completed

end Langlands.Tate
