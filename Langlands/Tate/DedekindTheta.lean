/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Tate.GlobalLattice
import Langlands.Tate.PoissonTheta

/-!
# The theta function of a fractional ideal

Let $K$ be a number field of degree $n$ with discriminant $d_K$ and different $\mathfrak{d}$. We use the notation of `Langlands.Tate.GlobalLattice`: $|x|_w = |\sigma_w(x)|$ and $n_w \in \{1, 2\}$ for an infinite place $w$. For a fractional ideal $I$ and real numbers $t_w > 0$, one for each infinite place, the theta function is $$\theta_I(t) = \sum_{\alpha \in I} \exp\Big(-\pi \sum_w n_w t_w |\alpha|_w^2\Big).$$ This is the theta function of Hecke's proof of the functional equation of the Dedekind zeta function. For the trivial character only the variable $t$ on the infinite places occurs.

## Main results

* `Langlands.Tate.summable_dedekindTheta`: the series converges.
* `Langlands.Tate.dedekindTheta_dual`: the transformation formula $$\theta_{\mathfrak{a}}(t) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|} \prod_w t_w^{n_w / 2}} \, \theta_{\mathfrak{a}^\vee}(t^{-1})$$ for a nonzero fractional ideal $\mathfrak{a}$, where $\mathfrak{a}^\vee$ is the dual for the trace form.
* `Langlands.Tate.dedekindTheta_inv_mul_different`: the same formula with $\mathfrak{a}^\vee = (\mathfrak{a} \mathfrak{d})^{-1}$.
* `Langlands.Tate.dedekindTheta_dual_const`: the case of one variable, $\theta_{\mathfrak{a}}(t) = (N(\mathfrak{a}) \sqrt{|d_K|} \, t^{n/2})^{-1} \, \theta_{\mathfrak{a}^\vee}(1/t)$.
* `Langlands.Tate.dedekindTheta_unit`: $\theta_I((t_w |u|_w^2)_w) = \theta_I(t)$ for a unit $u$ of $\mathcal{O}_K$.

## Proof

Put $c_w = \sqrt{n_w t_w}$ and $c'_w = \sqrt{n_w / t_w}$, so $c_w c'_w = n_w$. Let $\Lambda = \varphi_c(\mathfrak{a})$ be the lattice of `Langlands.Tate.globalLattice` in the euclidean mixed space $E$. Then $|\varphi_c(\alpha)|^2 = \sum_w n_w t_w |\alpha|_w^2$, so $\theta_{\mathfrak{a}}(t)$ is the lattice theta function $\sum_{\ell \in \Lambda} e^{-\pi |\ell|^2}$. The dual lattice is $\Lambda^\vee = \psi_{c'}(\mathfrak{a}^\vee)$, and $|\psi_{c'}(\beta)|^2 = \sum_w n_w t_w^{-1} |\beta|_w^2$. So the theta function of $\Lambda^\vee$ is $\theta_{\mathfrak{a}^\vee}(t^{-1})$. The formula `Langlands.Tate.tsum_zlattice_gaussian` at $t = 1$ now gives the result with the factor $\mathrm{covol}(\Lambda)^{-1}$. By `Langlands.Tate.covolume_globalLattice`, $$\mathrm{covol}(\Lambda) = \prod_w \sqrt{n_w t_w}^{\,n_w} \cdot N(\mathfrak{a}) \, 2^{-r_2} \sqrt{|d_K|} = N(\mathfrak{a}) \sqrt{|d_K|} \prod_w t_w^{n_w / 2},$$ because $\prod_w \sqrt{n_w}^{\,n_w} = 2^{r_2}$.

The covolume is for the Lebesgue measure of $E$, and the dual lattice is for the inner product of $E$. With these conventions no other constant appears.

## References

* E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, chapter VIII.
* J. Neukirch, Algebraic number theory, chapter VII, section 5.
* D. Ramakrishnan and R. Valenza, Fourier analysis on number fields, section 7.2.
-/

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped RealInnerProductSpace nonZeroDivisors

namespace Langlands.Tate

section Summable

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A function $f$ on $V$ with decay of order $N > \dim V$, in the sense of `Langlands.Tate.HasDecay`, is summable on each full lattice $L \subset V$. -/
theorem summable_zlattice_of_hasDecay {f : V → ℂ} {N : ℕ} (hf : HasDecay f N)
    (hN : finrank ℝ V < N) : Summable fun ℓ : L => f ℓ := by
  let b := Module.Free.chooseBasis ℤ L
  rw [← (latticeIndexEquiv L b).summable_iff]
  have := (hf.comp (latticeEquiv L b) _ (norm_le_latticeEquiv L b)).summable_intPoint
    (by rwa [← finrank_eq_card L b])
  simpa [Function.comp_def, coe_latticeIndexEquiv] using this

end Summable

open scoped Classical

variable {K : Type*} [Field K]

/-- The scaling constants $c_w = \sqrt{n_w t_w}$ for $t_w > 0$. With them $|\varphi_c(x)|^2 = \sum_w n_w t_w |x|_w^2$. -/
noncomputable def thetaScale {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    InfinitePlace K → ℝˣ :=
  fun w => Units.mk0 (√((mult w : ℝ) * t w))
    (Real.sqrt_ne_zero'.2 (mul_pos (Nat.cast_pos.2 mult_pos) (ht w)))

/-- The value $c_w = \sqrt{n_w t_w}$ of the scaling constants. -/
theorem coe_thetaScale {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (w : InfinitePlace K) :
    (thetaScale ht w : ℝ) = √((mult w : ℝ) * t w) := rfl

/-- The square of the scaling constant is $c_w^2 = n_w t_w$. -/
theorem thetaScale_sq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) (w : InfinitePlace K) :
    (thetaScale ht w : ℝ) ^ 2 = (mult w : ℝ) * t w := by
  rw [coe_thetaScale, Real.sq_sqrt (mul_pos (Nat.cast_pos.2 mult_pos) (ht w)).le]

/-- If each $t_w$ is positive, then each $t_w^{-1}$ is positive. -/
theorem inv_pos_of_forall {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ∀ w, 0 < (fun w => (t w)⁻¹) w := fun w => inv_pos.2 (ht w)

/-- The constants for $t$ and for $t^{-1}$ satisfy $\sqrt{n_w t_w} \sqrt{n_w / t_w} = n_w$. So they fit the duality `Langlands.Tate.mem_dualLattice_globalLattice`. -/
theorem thetaScale_mul_thetaScale_inv {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (w : InfinitePlace K) :
    (thetaScale ht w : ℝ) * thetaScale (inv_pos_of_forall ht) w = mult w := by
  have hm : (0 : ℝ) < mult w := Nat.cast_pos.2 mult_pos
  rw [coe_thetaScale, coe_thetaScale, ← Real.sqrt_mul (mul_pos hm (ht w)).le,
    show (mult w : ℝ) * t w * (mult w * (t w)⁻¹) = (mult w : ℝ) ^ 2 by
      field_simp [(ht w).ne'],
    Real.sqrt_sq hm.le]

variable [NumberField K]

variable (K) in
/-- The theta function of a fractional ideal $I$ in several variables, $$\theta_I(t) = \sum_{\alpha \in I} \exp\Big(-\pi \sum_w n_w t_w |\alpha|_w^2\Big).$$ It is meaningful for $t_w > 0$. -/
noncomputable def dedekindTheta (I : FractionalIdeal (𝓞 K)⁰ K) (t : InfinitePlace K → ℝ) : ℝ :=
  ∑' α : I, Real.exp (-Real.pi * ∑ w, (mult w : ℝ) * t w * w (α : K) ^ 2)

/-- The product $\prod_w |c_w|^{n_w}$ for $c_w = \sqrt{n_w t_w}$ is $2^{r_2} \prod_w \sqrt{t_w}^{\,n_w}$, since $\sqrt{2}^{\,2} = 2$ at each complex place. -/
theorem prod_abs_thetaScale {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ∏ w, |(thetaScale ht w : ℝ)| ^ mult w = 2 ^ nrComplexPlaces K * ∏ w, √(t w) ^ mult w := by
  have h1 : ∀ w, |(thetaScale ht w : ℝ)| ^ mult w = √(mult w : ℝ) ^ mult w * √(t w) ^ mult w := by
    intro w
    rw [coe_thetaScale, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
      mul_pow]
  simp_rw [h1, Finset.prod_mul_distrib]
  congr 1
  rw [prod_eq_prod_mul_prod]
  have hr : ∀ w : {w : InfinitePlace K // IsReal w}, √(mult w.1 : ℝ) ^ mult w.1 = 1 := by
    intro w; rw [mult_isReal w]; simp
  have hc : ∀ w : {w : InfinitePlace K // IsComplex w}, √(mult w.1 : ℝ) ^ mult w.1 = 2 := by
    intro w; rw [mult_isComplex w]; simp
  simp_rw [hr, hc, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

/-- For $c_w = \sqrt{n_w t_w}$ the factor $2^{r_2}$ cancels the factor $2^{-r_2}$ of `Langlands.Tate.covolume_globalLattice`: $$\mathrm{covol}(\Lambda_c(\mathfrak{a})) = N(\mathfrak{a}) \sqrt{|d_K|} \prod_w \sqrt{t_w}^{\,n_w}.$$ -/
theorem covolume_globalLattice_thetaScale (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    ZLattice.covolume (globalLattice K (thetaScale ht) a) =
      (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|discr K| *
        ∏ w, √(t w) ^ mult w := by
  have h2 : (2 : ℝ) ^ nrComplexPlaces K * 2⁻¹ ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]; norm_num
  rw [covolume_globalLattice, prod_abs_thetaScale]
  linear_combination ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
    √|discr K| * ∏ w, √(t w) ^ mult w) * h2

/-- For $c_w = \sqrt{n_w t_w}$, $|\varphi_c(x)|^2 = \sum_w n_w t_w |x|_w^2$. -/
theorem norm_globalEmbedding_thetaScale_sq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x : K) :
    ‖globalEmbedding K (fun w => (thetaScale ht w : ℝ)) x‖ ^ 2 =
      ∑ w, (mult w : ℝ) * t w * w x ^ 2 := by
  rw [norm_globalEmbedding_sq]
  simp_rw [thetaScale_sq]

/-- For $c_w = \sqrt{n_w t_w}$, $|\psi_c(x)|^2 = \sum_w n_w t_w |x|_w^2$. -/
theorem norm_globalConjEmbedding_thetaScale_sq {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w)
    (x : K) :
    ‖globalConjEmbedding K (fun w => (thetaScale ht w : ℝ)) x‖ ^ 2 =
      ∑ w, (mult w : ℝ) * t w * w x ^ 2 := by
  rw [norm_globalConjEmbedding_sq]
  simp_rw [thetaScale_sq]

variable (K) in
/-- The theta function of $\mathfrak{a}$ is the theta function of the lattice $\Lambda_c(\mathfrak{a})$ at $1$, for $c_w = \sqrt{n_w t_w}$: $\theta_{\mathfrak{a}}(t) = \sum_{\ell \in \Lambda_c(\mathfrak{a})} e^{-\pi |\ell|^2}$. -/
theorem dedekindTheta_eq_tsum_globalLattice (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    dedekindTheta K a t = ∑' ℓ : globalLattice K (thetaScale ht) a,
      Real.exp (-(Real.pi * 1) * ‖(ℓ : euclidean.mixedSpace K)‖ ^ 2) := by
  rw [← (globalLatticeEquiv K (thetaScale ht) a).tsum_eq, dedekindTheta]
  simp_rw [coe_globalLatticeEquiv, norm_globalEmbedding_thetaScale_sq, mul_one]
  rfl

/-- The series of $\theta_{\mathfrak{a}}(t)$ converges for $t_w > 0$. -/
theorem summable_dedekindTheta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    Summable fun α : (a : FractionalIdeal (𝓞 K)⁰ K) =>
      Real.exp (-Real.pi * ∑ w, (mult w : ℝ) * t w * w (α : K) ^ 2) := by
  refine (globalLatticeEquiv K (thetaScale ht) a).symm.summable_iff.mp ?_
  have := summable_zlattice_of_hasDecay (globalLattice K (thetaScale ht) a)
    (hasDecay_gaussian (E := euclidean.mixedSpace K) Real.pi_pos _)
    (Nat.lt_succ_self (finrank ℝ (euclidean.mixedSpace K)))
  rw [← Complex.summable_ofReal]
  refine this.congr fun ℓ => ?_
  obtain ⟨α, rfl⟩ := (globalLatticeEquiv K (thetaScale ht) a).surjective ℓ
  simp only [Function.comp_apply, Equiv.symm_apply_apply, coe_globalLatticeEquiv,
    norm_globalEmbedding_thetaScale_sq]

/-- The theta transformation formula for a nonzero fractional ideal $\mathfrak{a}$ and $t_w > 0$: $$\theta_{\mathfrak{a}}(t) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|} \prod_w \sqrt{t_w}^{\,n_w}} \, \theta_{\mathfrak{a}^\vee}(t^{-1}),$$ where $\mathfrak{a}^\vee$ is the dual of $\mathfrak{a}$ for the trace form and $t^{-1} = (t_w^{-1})_w$. -/
theorem dedekindTheta_dual (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    dedekindTheta K a t =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|discr K| *
          ∏ w, √(t w) ^ mult w)⁻¹ *
        dedekindTheta K (FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K))
          (fun w => (t w)⁻¹) := by
  have h := tsum_zlattice_gaussian (globalLattice K (thetaScale ht) a) one_pos
  rw [← dedekindTheta_eq_tsum_globalLattice K a ht, covolume_globalLattice_thetaScale,
    ← (globalDualEquiv K (thetaScale ht) a (thetaScale (inv_pos_of_forall ht))
      (thetaScale_mul_thetaScale_inv ht)).tsum_eq] at h
  simp_rw [coe_globalDualEquiv, norm_globalConjEmbedding_thetaScale_sq, Real.one_rpow, inv_one,
    mul_one, div_one] at h
  rw [h, dedekindTheta]
  rfl

/-- The theta transformation formula with the different: $$\theta_{\mathfrak{a}}(t) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|} \prod_w \sqrt{t_w}^{\,n_w}} \, \theta_{(\mathfrak{a} \mathfrak{d})^{-1}}(t^{-1}).$$ -/
theorem dedekindTheta_inv_mul_different (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : InfinitePlace K → ℝ} (ht : ∀ w, 0 < t w) :
    dedekindTheta K a t =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|discr K| *
          ∏ w, √(t w) ^ mult w)⁻¹ *
        dedekindTheta K ((a : FractionalIdeal (𝓞 K)⁰ K) *
          (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ (fun w => (t w)⁻¹) := by
  rw [dedekindTheta_dual a ht, dual_eq_inv_mul_different]

/-- For a constant $t$, $\prod_w \sqrt{t}^{\,n_w} = \sqrt{t}^{\,n}$ with $n = [K : \mathbb{Q}]$. -/
theorem prod_sqrt_pow_mult (t : ℝ) : ∏ w : InfinitePlace K, √t ^ mult w = √t ^ finrank ℚ K := by
  rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]

/-- The theta transformation formula in one variable. For $t > 0$ write $\theta_{\mathfrak{a}}(t)$ for the value at the constant vector $(t)_w$, that is $\sum_{\alpha \in \mathfrak{a}} e^{-\pi t \sum_w n_w |\alpha|_w^2}$. Then $$\theta_{\mathfrak{a}}(t) = \frac{1}{N(\mathfrak{a}) \sqrt{|d_K|} \, t^{n/2}} \, \theta_{\mathfrak{a}^\vee}(1/t).$$ -/
theorem dedekindTheta_dual_const (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    dedekindTheta K a (fun _ => t) =
      ((FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|discr K| *
          √t ^ finrank ℚ K)⁻¹ *
        dedekindTheta K (FractionalIdeal.dual ℤ ℚ (a : FractionalIdeal (𝓞 K)⁰ K))
          (fun _ => t⁻¹) := by
  rw [dedekindTheta_dual a (t := fun _ => t) fun _ => ht, prod_sqrt_pow_mult]

omit [NumberField K] in
/-- A fractional ideal is stable under multiplication by a unit $u$ of $\mathcal{O}_K$: $u x \in I$ if and only if $x \in I$. -/
theorem unit_mul_mem_iff (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) {x : K} :
    (u : K) * x ∈ I ↔ x ∈ I := by
  constructor
  · intro h
    have := Submodule.smul_mem (I : Submodule (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h
    rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
  · intro h
    have := Submodule.smul_mem (I : Submodule (𝓞 K) K) (u : 𝓞 K) h
    rwa [Algebra.smul_def] at this

variable (K) in
/-- Multiplication by a unit $u$ of $\mathcal{O}_K$, as a bijection $I \to I$ of a fractional ideal. -/
noncomputable def unitMulEquiv (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) :
    {x : K // x ∈ I} ≃ {x : K // x ∈ I} where
  toFun x := ⟨(u : K) * x, (unit_mul_mem_iff I u).2 x.2⟩
  invFun x := ⟨((u⁻¹ : (𝓞 K)ˣ) : K) * x, (unit_mul_mem_iff I u⁻¹).2 x.2⟩
  left_inv x := by
    ext
    simp only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  right_inv x := by
    ext
    simp only [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- The theta function is invariant under the units: $\theta_I((t_w |u|_w^2)_w) = \theta_I(t)$ for each unit $u$ of $\mathcal{O}_K$. The reason is that $\alpha \mapsto u \alpha$ is a bijection of $I$. -/
theorem dedekindTheta_unit (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ)
    (t : InfinitePlace K → ℝ) :
    dedekindTheta K I (fun w => t w * w (u : K) ^ 2) = dedekindTheta K I t := by
  rw [dedekindTheta, dedekindTheta]
  conv_rhs => rw [← (unitMulEquiv K I u).tsum_eq]
  refine tsum_congr fun x => ?_
  simp only [unitMulEquiv, Equiv.coe_fn_mk, map_mul, mul_pow]
  congr 2
  exact Finset.sum_congr rfl fun w _ => by ring

end Langlands.Tate
