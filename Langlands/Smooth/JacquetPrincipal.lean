/-
Copyright (c) 2026 The langlands-lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.Smooth.PrincipalSeries
import Langlands.Smooth.Bruhat

/-!
# The Jacquet module of a principal series of $GL_2$

Let $K$ be a nonarchimedean local field with residue field of cardinality $q$, let $B = TN$ be the upper triangular Borel subgroup of $G = GL_2(K)$, and let $\chi_1, \chi_2$ be smooth characters of $K^\times$. This file proves that the Jacquet module $V_N$ of the principal series $V = \mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ (unnormalized induction) has dimension $2$. It gives $V_N$ as an extension of representations of $T$ $$0 \to (V_w)_N \to V_N \to \chi_1 \otimes \chi_2 \to 0,$$ where $V_w$ is the subspace of the functions with support in the big cell $BwN$, and $(V_w)_N$ is the character $\mathrm{diag}(a, d) \mapsto \chi_2(a)|a| \chi_1(d)|d|^{-1}$. This is the Weyl conjugate $\chi_2 \otimes \chi_1$ twisted by the modulus character $\delta_B(\mathrm{diag}(a, d)) = |a/d|$.

## Main definitions

* `Langlands.piBall`: the ball $\{x : v(x) \le v(\varpi)^n\}$ of $K$, as an additive subgroup.
* `Langlands.bigCellFun`: the linear map $f \mapsto (x \mapsto f(w n(x)))$ from the principal series to the functions on $K$.
* `Langlands.bigCellJacquetKer`: the subspace $V_w(N)$ spanned by the vectors $n \cdot f - f$ with $n \in N$ and $f \in V_w$.
* `Langlands.bigCellChar`: the character $\mathrm{diag}(a, d) \mapsto \chi_2(a)|a| \chi_1(d)|d|^{-1}$ of $T$.
* `Langlands.bigCellJacquet`: the Jacquet module $(V_w)_N = V_w / V_w(N)$, as a smooth representation of $T$.
* `Langlands.bigCellJacquetIncl`: the map $(V_w)_N \to V_N$ of representations of $T$.

## Main results

* `Langlands.principalSeriesBigCell_shortExact`: $0 \to V_w \to V \to \mathbb{C} \to 0$ is exact, where $V \to \mathbb{C}$ is $f \mapsto f(1)$.
* `Langlands.bigCellFun_inj`, `Langlands.bigCellFun_eventually_zero`: on $V_w$ the map $f \mapsto \varphi_f$ is injective, and $\varphi_f$ vanishes outside a ball.
* `Langlands.exists_sub_smul_mem_bigCellJacquetKer`, `Langlands.not_mem_jacquetKer_of_indicator`: $V_w / V_w(N)$ is spanned by the class of one vector $f_0$, and $f_0 \notin V(N)$.
* `Langlands.mem_bigCellJacquetKer_of_mem_jacquetKer`, `Langlands.bigCellJacquetIncl_injective`: $V_w \cap V(N) = V_w(N)$, so $(V_w)_N \to V_N$ is injective.
* `Langlands.bigCellJacquetIncl_exact`: the sequence $(V_w)_N \to V_N \to \chi_1 \otimes \chi_2$ is exact.
* `Langlands.bigCellJacquet_iso`, `Langlands.finrank_bigCellJacquet`: $(V_w)_N$ is the character `bigCellChar` of $T$, and has dimension $1$.
* `Langlands.principalSeriesJacquet_shortExact`: the short exact sequence $0 \to (V_w)_N \to V_N \to \chi_1 \otimes \chi_2 \to 0$ of representations of $T$.
* `Langlands.finrank_principalSeriesJacquet`: $V_N$ has dimension $2$.

## Proof

The map $f \mapsto \varphi_f$ with $\varphi_f(x) = f(w n(x))$ identifies $V_w$ with a space of locally constant functions on $K$ that vanish outside a ball, and $n(y)$ acts as the translation by $y$. No Haar measure is used. For $f \in V_w$ and a compact open subgroup $N_1 = N(\varpi^{n_1})$ of $N$, let $S_f$ be the stabilizer of $f$ in $N_1$. Then $[N_1 : S_f] f$ is congruent modulo $V_w(N)$ to the coset sum $\sum_{q \in N_1 / S_f} n_q f$. If $\varphi_f$ vanishes outside the ball of index $n_1$, the function of this coset sum is constant on that ball and $0$ outside it. Thus all these coset sums are multiples of the coset sum of a fixed vector $f_0$ with $\varphi_{f_0}$ the indicator function of a ball, and $V_w / V_w(N)$ is spanned by the class of $f_0$. The indices $[N(\varpi^m) : N(\varpi^n)] = q^{m - n}$ give the action of $T$. Jacquet's lemma `Langlands.SmoothRep.mem_jacquetKer_unipotent_iff` gives $f_0 \notin V(N)$ and $V_w \cap V(N) = V_w(N)$.
-/

universe u

open Representation Matrix

namespace Langlands

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open ValuativeRel GL2

/-- The closed ball $\{x : v(x) \le v(\varpi)^n\}$ of $K$, as an additive subgroup. Here $v(\varpi)$ is the generator `uniformizer K` of the value group that is less than $1$. -/
def piBall (n : ℤ) : AddSubgroup K where
  carrier := {x | valuation K x ≤ uniformizer K ^ n}
  zero_mem' := by simp
  add_mem' {x y} hx hy := show valuation K (x + y) ≤ _ from
    (Valuation.map_add _ x y).trans (max_le hx hy)
  neg_mem' {x} hx := show valuation K (-x) ≤ _ by simpa using hx

variable {K}

/-- Membership in the ball $\{x : v(x) \le v(\varpi)^n\}$. -/
theorem mem_piBall {n : ℤ} {x : K} : x ∈ piBall K n ↔ valuation K x ≤ uniformizer K ^ n := by
  rfl

/-- Since $v(\varpi) < 1$, the map $n \mapsto v(\varpi)^n$ reverses the order. -/
theorem uniformizer_zpow_le_iff {m n : ℤ} :
    uniformizer K ^ m ≤ uniformizer K ^ n ↔ n ≤ m :=
  zpow_le_zpow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one

/-- The balls decrease when $n$ increases. -/
theorem piBall_antitone {m n : ℤ} (h : m ≤ n) : piBall K n ≤ piBall K m :=
  fun _ hx => (mem_piBall.1 hx).trans (uniformizer_zpow_le_iff.2 h)

/-- In the value group, $\gamma < v(\varpi)^n$ exactly when $\gamma \le v(\varpi)^{n + 1}$. -/
theorem lt_uniformizer_zpow_iff {n : ℤ} {γ : ValueGroupWithZero K} :
    γ < uniformizer K ^ n ↔ γ ≤ uniformizer K ^ (n + 1) := by
  have hu : uniformizer K ≠ 0 := uniformizer_ne_zero
  have h0 : (0 : ValueGroupWithZero K) < uniformizer K ^ n := zpow_pos uniformizer_pos n
  rw [← mul_lt_mul_iff_of_pos_right (zpow_pos uniformizer_pos (-n)), zpow_neg,
    mul_inv_cancel₀ h0.ne', ← le_uniformizer_iff,
    ← mul_le_mul_iff_of_pos_right h0, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one,
    zpow_add₀ hu, zpow_one, mul_comm]

/-- The isomorphism of the value group with $\mathbb{Z}$ with zero takes $v(\varpi)$ to $\exp(-1)$. -/
theorem uniformizer_iso :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (uniformizer K) =
      WithZero.exp (-1) := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply le_antisymm
  · have h1 : e (uniformizer K) < 1 := by
      simpa using e.strictMono (uniformizer_lt_one (R := K))
    have h0 : e (uniformizer K) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    have : WithZero.log (e (uniformizer K)) < 0 := by
      rwa [← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]
    omega
  · have : e.symm (WithZero.exp (-1)) ≤ uniformizer K := by
      rw [le_uniformizer_iff]
      have h := e.symm.strictMono (show WithZero.exp (-1 : ℤ) < 1 by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
      simpa using h
    simpa using (map_le_map_iff e).2 this

/-- The valuation of a nonzero element is a power of $v(\varpi)$. -/
theorem exists_valuation_eq_zpow {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, valuation K x = uniformizer K ^ n := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have h0 : e (valuation K x) ≠ 0 := by simpa using hx
  refine ⟨-WithZero.log (e (valuation K x)), EquivLike.injective e ?_⟩
  have hz : e (uniformizer K ^ (-WithZero.log (e (valuation K x)))) =
      e (uniformizer K) ^ (-WithZero.log (e (valuation K x))) := map_zpow₀ e _ _
  rw [hz, uniformizer_iso, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
    WithZero.exp_log h0]

/-- The ball of radius $v(\varpi)$ is the maximal ideal $\{x : v(x) < 1\}$. -/
theorem mem_piBall_one {x : K} : x ∈ piBall K 1 ↔ valuation K x < 1 := by
  rw [mem_piBall, zpow_one, le_uniformizer_iff]

/-- The index of the maximal ideal in the ring of integers is the cardinality $q$ of the residue field. -/
theorem relIndex_piBall_one_zero : (piBall K 1).relIndex (piBall K 0) = residueCard K := by
  let f : 𝒪[K] →+ K := (𝒪[K]).subtype.toAddMonoidHom
  have hr : f.range = piBall K 0 := by
    ext x
    simp only [AddMonoidHom.mem_range, mem_piBall, zpow_zero]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hc : (piBall K 1).comap f = (𝓂[K]).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, mem_piBall_one, Submodule.mem_toAddSubgroup,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm
  rw [← hr, ← AddSubgroup.index_comap, hc, AddSubgroup.index_eq_card]
  rfl

/-- Multiplication by $c$ with $v(c) = v(\varpi)^k$ takes the ball of index $n$ to the ball of index $n + k$. -/
theorem map_mulLeft_piBall {c : K} (hc : c ≠ 0) {k : ℤ} (hk : valuation K c = uniformizer K ^ k)
    (n : ℤ) : (piBall K n).map (AddMonoidHom.mulLeft c) = piBall K (n + k) := by
  have hu : uniformizer K ≠ 0 := uniformizer_ne_zero
  ext y
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, mem_piBall]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [map_mul, hk, zpow_add₀ hu, mul_comm (uniformizer K ^ n)]
    gcongr
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by field_simp⟩
    rw [map_mul, map_inv₀, hk, ← zpow_neg]
    calc uniformizer K ^ (-k) * valuation K y ≤ uniformizer K ^ (-k) * uniformizer K ^ (n + k) :=
          by gcongr
      _ = uniformizer K ^ n := by rw [← zpow_add₀ hu]; ring_nf

/-- Each ball has index $q$ in the next larger ball. -/
theorem relIndex_piBall_add_one (n : ℤ) :
    (piBall K (n + 1)).relIndex (piBall K n) = residueCard K := by
  obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (uniformizer K ^ n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact zpow_ne_zero n uniformizer_ne_zero (by simpa using hc.symm)
  have hinj : Function.Injective (AddMonoidHom.mulLeft c) := mul_right_injective₀ hc0
  have h := AddSubgroup.relIndex_map_map_of_injective (piBall K 1) (piBall K 0) hinj
  rw [map_mulLeft_piBall hc0 hc, map_mulLeft_piBall hc0 hc, zero_add, add_comm,
    relIndex_piBall_one_zero] at h
  exact h

/-- The ball of index $n + k$ has index $q^k$ in the ball of index $n$. -/
theorem relIndex_piBall_add (n : ℤ) (k : ℕ) :
    (piBall K (n + k)).relIndex (piBall K n) = residueCard K ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← AddSubgroup.relIndex_mul_relIndex (piBall K (n + (k + 1 : ℕ))) (piBall K (n + k))
      (piBall K n) (piBall_antitone (by omega)) (piBall_antitone (by omega)), ih,
      show n + ((k + 1 : ℕ) : ℤ) = n + k + 1 by push_cast; ring, relIndex_piBall_add_one, pow_succ,
      mul_comm]

/-- An element $c$ with $v(c) = v(\varpi)^k$ has absolute value $q^{-k}$. -/
theorem normAbs_eq_zpow {c : K} (hc : c ≠ 0) {k : ℤ} (hk : valuation K c = uniformizer K ^ k) :
    normAbs K c = (residueCard K : ℝ) ^ (-k) := by
  rw [normAbs_of_ne_zero hc, hk]
  congr 1
  have hz : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (uniformizer K ^ k) =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (uniformizer K) ^ k := map_zpow₀ _ _ _
  rw [hz, uniformizer_iso, ← WithZero.exp_zsmul, WithZero.log_exp, smul_eq_mul, mul_neg_one]

namespace GL2

/-- The map $x \mapsto n(x)$ as a group homomorphism from `Multiplicative K`. -/
def unipHom : Multiplicative K →* GL (Fin 2) K where
  toFun x := unip x.toAdd
  map_one' := unip_zero
  map_mul' x y := unip_add x.toAdd y.toAdd

/-- The subgroup $N(\varpi^n)$ is the image of the ball of index $n$ under $x \mapsto n(x)$. -/
theorem unipBall_eq_map (n : ℤ) :
    unipBall K (uniformizer K ^ n) = (piBall K n).toSubgroup.map unipHom := by
  ext g
  rw [mem_unipBall, Subgroup.mem_map]
  constructor
  · rintro ⟨hg, hv⟩
    exact ⟨Multiplicative.ofAdd (g.1 0 1), hv, (eq_unip hg).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨unip_mem _, by simpa [unipHom, unip_val, mem_piBall] using hx⟩

/-- The index of $N(\varpi^m)$ in $N(\varpi^n)$ is the index of the corresponding balls of $K$. -/
theorem relIndex_unipBall (m n : ℤ) :
    (unipBall K (uniformizer K ^ m)).relIndex (unipBall K (uniformizer K ^ n)) =
      (piBall K m).relIndex (piBall K n) := by
  rw [unipBall_eq_map, unipBall_eq_map, Subgroup.relIndex_map_map_of_injective,
    AddSubgroup.relIndex_toSubgroup]
  exact fun x y h => unip_injective (K := K) h

/-- The real number $[N(\varpi^n) : N(\varpi^m)] = q^{m - n}$ for $n \le m$. -/
theorem relIndex_unipBall_eq {m n : ℤ} (h : n ≤ m) :
    ((unipBall K (uniformizer K ^ m)).relIndex (unipBall K (uniformizer K ^ n)) : ℝ) =
      (residueCard K : ℝ) ^ (m - n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = n + k := ⟨(m - n).toNat, by omega⟩
  rw [relIndex_unipBall, relIndex_piBall_add, Nat.cast_pow, add_sub_cancel_left, zpow_natCast]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Conjugation by the Weyl element takes $n(x)$ to the lower unipotent matrix with entry $x$. -/
theorem weyl_mul_unip_mul_weyl (x : K) : weyl * unip x * weyl = lowerUnip x := by
  ext i j
  rw [Units.val_mul, Units.val_mul, weyl_val, unip_val]
  fin_cases i <;> fin_cases j <;> simp [lowerUnip, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix $\begin{pmatrix} -x^{-1} & 1 \\ 0 & x \end{pmatrix}$ of $B$, for $x \neq 0$. -/
noncomputable def bigCellBorel (x : K) (hx : x ≠ 0) : GL (Fin 2) K :=
  ⟨!![-x⁻¹, 1; 0, x], !![-x, 1; 0, x⁻¹], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The matrix `bigCellBorel x hx` is in $B$. -/
theorem bigCellBorel_mem (x : K) (hx : x ≠ 0) : bigCellBorel x hx ∈ borel K := by
  simp [mem_borel, bigCellBorel]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $x \neq 0$, $w n(x)$ is a product of an element of $B$ and the lower unipotent matrix with entry $x^{-1}$. -/
theorem weyl_mul_unip_eq (x : K) (hx : x ≠ 0) :
    weyl * unip x = bigCellBorel x hx * lowerUnip x⁻¹ := by
  ext i j
  rw [Units.val_mul, Units.val_mul, weyl_val, unip_val]
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnip, bigCellBorel, Matrix.mul_apply, Fin.sum_univ_two, hx]

/-- The map from $K$ to the lower unipotent matrices is continuous. -/
theorem continuous_lowerUnip : Continuous (lowerUnip : K → GL (Fin 2) K) := by
  have h : ∀ f : K → Matrix (Fin 2) (Fin 2) K, (∀ i j, Continuous fun x => f x i j) →
      Continuous f := fun f hf => continuous_pi fun i => continuous_pi fun j => hf i j
  refine Units.continuous_iff.mpr ⟨h _ fun i j => ?_, h _ fun i j => ?_⟩
  · change Continuous fun x : K => !![(1 : K), 0; x, 1] i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun x : K => !![(1 : K), 0; -x, 1] i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end GL2

section Groups

variable {G : Type u} [Group G]

/-- Let $S$ be a subgroup of finite index of $N_1$ and let $F$ be a function on $G$ that is right invariant under $S$. Then for $g \in N_1$, the sum of $F(g n_q)$ over the cosets $q \in N_1 / S$ is the sum of $F(n_q)$. -/
theorem sum_out_mul_left {N₁ : Subgroup G} (S : Subgroup N₁) [Fintype (N₁ ⧸ S)]
    {M : Type*} [AddCommMonoid M] (F : G → M)
    (hF : ∀ (n : G) (s : N₁), s ∈ S → F (n * s) = F n) (g : N₁) :
    ∑ q : N₁ ⧸ S, F (g * (Quotient.out q : N₁)) = ∑ q : N₁ ⧸ S, F (Quotient.out q : N₁) := by
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
  change F (g * (Quotient.out q : N₁)) = F (Quotient.out (g • q) : N₁)
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S (g * Quotient.out q)
  rw [hh, Subgroup.coe_mul, Subgroup.coe_mul, hF _ h h.2]

/-- The coset $q \in N_1 / S$ is the trivial coset exactly when its representative is in $S$. -/
theorem out_mem_iff {N₁ : Subgroup G} {S : Subgroup N₁} (q : N₁ ⧸ S) :
    Quotient.out q ∈ S ↔ q = ((1 : N₁) : N₁ ⧸ S) := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

/-- Let $\theta$ be a character of $H$ and let $U$ be an open subgroup of $G$ such that $\theta$ is trivial on $H \cap U$. Then $\mathrm{Ind}_H^G \theta$ has a vector $f$ with support $HU$ and $f(hu) = \theta(h)$. -/
theorem SmoothRep.exists_ind_charRep_support [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (θ : H →* ℂˣ) (hθ : IsOpen (θ.ker : Set H))
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hθU : ∀ h : H, (h : G) ∈ U → θ h = 1) :
    ∃ f : (SmoothRep.ind H (SmoothRep.charRep θ hθ)).V,
      (∀ (b : H) (g : G), (b : G)⁻¹ * g ∈ U → SmoothRep.ind.toFun f g = ULift.up (θ b : ℂ)) ∧
      (∀ g : G, (∀ b : H, (b : G)⁻¹ * g ∉ U) → SmoothRep.ind.toFun f g = 0) := by
  classical
  let P : G → Prop := fun g => ∃ b : H, (b : G)⁻¹ * g ∈ U
  let F : G → ULift.{u} ℂ := fun g => if h : P g then ULift.up (θ h.choose : ℂ) else 0
  have key : ∀ (b : H) (g : G), (b : G)⁻¹ * g ∈ U → F g = ULift.up (θ b : ℂ) := by
    intro b g hb
    have h : P g := ⟨b, hb⟩
    simp only [F, dite_eq_left h]
    have hc := h.choose_spec
    have hm : ((b⁻¹ * h.choose : H) : G) = ((b : G)⁻¹ * g) * (((h.choose : H) : G)⁻¹ * g)⁻¹ := by
      simp [mul_assoc]
    have h1 : θ (b⁻¹ * h.choose) = 1 := hθU _ (by rw [hm]; exact U.mul_mem hb (U.inv_mem hc))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
  have zero : ∀ g, ¬ P g → F g = 0 := fun g h => dite_eq_right h
  have hF : F ∈ indSpace H (SmoothRep.charRep θ hθ) := by
    refine ⟨fun h g => ?_, U, hU, fun g u hu => ?_⟩
    · change F (h * g) = (θ h : ℂ) • F g
      by_cases hg : P g
      · obtain ⟨b, hb⟩ := hg
        rw [key b g hb, key (h * b) (h * g) (by simpa [mul_assoc] using hb)]
        apply ULift.ext
        simp
      · have : ¬ P (h * g) := by
          rintro ⟨b, hb⟩
          exact hg ⟨h⁻¹ * b, by simpa [mul_assoc] using hb⟩
        rw [zero _ hg, zero _ this, smul_zero]
    · by_cases hg : P g
      · obtain ⟨b, hb⟩ := hg
        rw [key b g hb, key b (g * u) (by rw [← mul_assoc]; exact U.mul_mem hb hu)]
      · have : ¬ P (g * u) := by
          rintro ⟨b, hb⟩
          refine hg ⟨b, ?_⟩
          have := U.mul_mem hb (U.inv_mem hu)
          simpa [mul_assoc] using this
        rw [zero _ hg, zero _ this]
  refine ⟨show indSpace H (SmoothRep.charRep θ hθ) from ⟨F, hF⟩, key, fun g hg => ?_⟩
  exact zero g fun ⟨b, hb⟩ => hg b hb

end Groups

section BigCellFunction

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

/-- The function $\varphi_f : x \mapsto f(w n(x))$ on $K$ of a vector $f$ of the principal series, as a linear map. -/
noncomputable def bigCellFun : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V →ₗ[ℂ] K → ℂ where
  toFun f x := (SmoothRep.ind.toFun f (weyl * unip x)).down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The value of `bigCellFun f` at $x$ is $f(w n(x))$. -/
theorem bigCellFun_apply (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) (x : K) :
    bigCellFun f x = (SmoothRep.ind.toFun f (weyl * unip x)).down :=
  rfl

/-- A vector of $V_w$ is determined by its function $\varphi_f$ on $K$, by the Bruhat decomposition. -/
theorem bigCellFun_inj {f f' : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V}
    (hf : f ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) (hf' : f' ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂)
    (h : bigCellFun f = bigCellFun f') : f = f' := by
  apply SmoothRep.ind.toFun_injective
  funext g
  by_cases hg : g ∈ bigCell K
  · obtain ⟨b, hb, n, hn, rfl⟩ := hg
    rw [eq_unip hn, mul_assoc, show b = ((⟨b, hb⟩ : GL2.borel K) : GL (Fin 2) K) from rfl,
      principalSeriesInd_mul_left, principalSeriesInd_mul_left]
    congr 1
    exact ULift.ext (congrFun h _)
  · rw [(mem_principalSeriesBigCell_iff f).1 hf g hg, (mem_principalSeriesBigCell_iff f').1 hf' g hg]

/-- The translate of $f$ by $n(y)$ has the function $x \mapsto \varphi_f(x + y)$. -/
theorem bigCellFun_ρ_unip (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) (x y : K) :
    bigCellFun ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ (unip y) f) x = bigCellFun f (x + y) := by
  change (SmoothRep.ind.toFun f (weyl * unip x * unip y)).down = _
  rw [mul_assoc, ← unip_add]
  rfl

/-- The subspace $V_w$ is stable under $B$. -/
theorem ρ_mem_principalSeriesBigCell {f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V}
    (hf : f ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) {b : GL (Fin 2) K} (hb : b ∈ GL2.borel K) :
    (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ b f ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂ :=
  principalSeriesBigCell_stable χ₁ χ₂ hχ₁ hχ₂ ⟨b, hb⟩ hf

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For $t \in T$ the product $w n(x) t$ is $(w t w) \cdot w n(x t_{22} / t_{11})$. -/
theorem weyl_mul_unip_mul_torus (t : GL (Fin 2) K) (ht : t ∈ torus K) (x : K) :
    weyl * unip x * t = (weyl * t * weyl) * (weyl * unip (x * t.1 1 1 / t.1 0 0)) := by
  have ha : t.1 0 0 ≠ 0 := val_zero_zero_ne_zero (torus_le_borel ht)
  rw [mem_torus] at ht
  ext i j
  simp only [Units.val_mul, weyl_val, unip_val, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]
  field_simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The conjugate of an element of $T$ by the Weyl element is in $B$. -/
theorem weyl_conj_torus_mem (t : GL (Fin 2) K) (ht : t ∈ torus K) : weyl * t * weyl ∈ GL2.borel K := by
  rw [mem_borel, weyl_conj_val]
  exact ht.2

/-- The translate of $f$ by $t = \mathrm{diag}(a, d)$ has the function $x \mapsto \chi_1(d)\chi_2(a) \varphi_f(x d / a)$. -/
theorem bigCellFun_ρ_torus (f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V) (t : torus K) (x : K) :
    bigCellFun ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ t f) x =
      (χ₁ (diagSnd ⟨t, torus_le_borel t.2⟩) : ℂ) * χ₂ (diagFst ⟨t, torus_le_borel t.2⟩) *
        bigCellFun f (x * (t : GL (Fin 2) K).1 1 1 / (t : GL (Fin 2) K).1 0 0) := by
  change (SmoothRep.ind.toFun f (weyl * unip x * (t : GL (Fin 2) K))).down = _
  have ht := t.2
  rw [weyl_mul_unip_mul_torus _ ht,
    show weyl * (t : GL (Fin 2) K) * weyl =
      ((⟨_, weyl_conj_torus_mem _ ht⟩ : GL2.borel K) : GL (Fin 2) K) from rfl,
    principalSeriesInd_mul_left]
  rw [mem_torus] at ht
  have e1 : diagFst (⟨_, weyl_conj_torus_mem _ t.2⟩ : GL2.borel K) = diagSnd ⟨t, torus_le_borel t.2⟩ := by
    ext
    simp only [val_diagFst, val_diagSnd, Units.val_mul, weyl_val, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp [ht.1, ht.2]
  have e2 : diagSnd (⟨_, weyl_conj_torus_mem _ t.2⟩ : GL2.borel K) = diagFst ⟨t, torus_le_borel t.2⟩ := by
    ext
    simp only [val_diagFst, val_diagSnd, Units.val_mul, weyl_val, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp [ht.1, ht.2]
  rw [e1, e2]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The lower unipotent matrix with entry $0$ is $1$. -/
theorem lowerUnip_zero : lowerUnip (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnip]

/-- For $f \in V_w$ the function $\varphi_f$ has compact support: it vanishes for $v(x) > v(\varpi)^n$ for some $n$. For $x \neq 0$ we have $w n(x) = b \, \bar n(x^{-1})$ with $b \in B$, and $f$ is invariant under $\bar n(y)$ for small $y$, so $\varphi_f(x)$ is a multiple of $f(1) = 0$. -/
theorem bigCellFun_eventually_zero {f : (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).V}
    (hf : f ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) :
    ∃ n : ℤ, ∀ x, uniformizer K ^ n < valuation K x → bigCellFun f x = 0 := by
  have hO : IsOpen (lowerUnip ⁻¹'
      (vecStabilizer (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ f : Set (GL (Fin 2) K))) :=
    continuous_lowerUnip.isOpen_preimage _ ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).smooth f)
  have h0 : (0 : K) ∈ lowerUnip ⁻¹'
      (vecStabilizer (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ f : Set (GL (Fin 2) K)) := by
    rw [Set.mem_preimage, lowerUnip_zero]
    exact (vecStabilizer _ _).one_mem
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.1 (hO.mem_nhds h0)
  obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hc.symm)
  obtain ⟨m, hm⟩ := exists_valuation_eq_zpow hc0
  refine ⟨-m, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxi : lowerUnip x⁻¹ ∈ vecStabilizer (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ f := by
    refine hγ (show valuation K (x⁻¹ - 0) < γ from ?_)
    have hpos : (0 : ValueGroupWithZero K) < uniformizer K ^ m := zpow_pos uniformizer_pos m
    rw [sub_zero, map_inv₀, ← hc, hm, inv_lt_comm₀ (zero_lt_iff.2 (by simpa using hx0)) hpos, ← zpow_neg]
    exact hx
  rw [mem_vecStabilizer] at hxi
  have hf1 : SmoothRep.ind.toFun f 1 = 0 := hf
  rw [bigCellFun_apply, weyl_mul_unip_eq x hx0,
    show bigCellBorel x hx0 = ((⟨_, bigCellBorel_mem x hx0⟩ : GL2.borel K) : GL (Fin 2) K) from rfl,
    principalSeriesInd_mul_left]
  have : SmoothRep.ind.toFun f (lowerUnip x⁻¹) = 0 := by
    calc SmoothRep.ind.toFun f (lowerUnip x⁻¹)
        = SmoothRep.ind.toFun ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ (lowerUnip x⁻¹) f) 1 := by
          change _ = SmoothRep.ind.toFun f (1 * lowerUnip x⁻¹)
          rw [one_mul]
      _ = 0 := by rw [hxi, hf1]
  rw [this, smul_zero]
  rfl

/-- There is a vector $f_0 \in V_w$ such that $\varphi_{f_0}$ is the indicator function of a ball $\{x : v(x) \le v(\varpi)^{n_0}\}$. Take $F$ in the principal series with support $BU$ and $F = 1$ on $U$, for a small congruence subgroup $U$, and put $f_0 = w \cdot F$. Then $\varphi_{f_0}(x) = F(\bar n(x))$. -/
theorem exists_bigCellFun_indicator :
    ∃ n₀ : ℤ, ∃ f₀ ∈ principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂,
      ∀ x, bigCellFun f₀ x = if valuation K x ≤ uniformizer K ^ n₀ then 1 else 0 := by
  obtain ⟨γ, hγ0, hγ1, h⟩ := exists_congruence_borelChar hχ₁ hχ₂
  obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective γ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hγ0 (by simpa using hc.symm)
  obtain ⟨k, hk⟩ := exists_valuation_eq_zpow hc0
  set m := max k 0
  have hm0 : uniformizer K ^ m ≠ 0 := zpow_ne_zero _ uniformizer_ne_zero
  have hm1 : uniformizer K ^ m ≤ 1 := by
    rw [← zpow_zero (uniformizer K)]
    exact uniformizer_zpow_le_iff.2 (le_max_right _ _)
  have hmγ : uniformizer K ^ m ≤ γ := by
    rw [← hc, hk]
    exact uniformizer_zpow_le_iff.2 (le_max_left _ _)
  have hU : ∀ b : GL2.borel K, (b : GL (Fin 2) K) ∈ congruence K _ hm0 hm1 →
      borelChar χ₁ χ₂ b = 1 := fun b hb =>
    h b ⟨fun i j => (hb.1 i j).trans_le hmγ, fun i j => (hb.2 i j).trans_le hmγ⟩
  obtain ⟨F, hF1, hF0⟩ := SmoothRep.exists_ind_charRep_support (borelChar χ₁ χ₂)
    (isOpen_ker_borelChar hχ₁ hχ₂) _ (isOpen_congruence _ hm0 hm1) hU
  have hu11 : ∀ u ∈ congruence K _ hm0 hm1, valuation K (u.1 1 1) = 1 := fun u hu => by
    have h1 := hu.1 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    rw [show u.1 1 1 = 1 + (u.1 1 1 - 1) by ring]
    exact Valuation.map_one_add_of_lt _ (h1.trans_le hm1)
  have hdec : ∀ (b : GL2.borel K) (g : GL (Fin 2) K) (i : Fin 2),
      g.1 1 i = (b : GL (Fin 2) K).1 1 1 * ((b : GL (Fin 2) K)⁻¹ * g).1 1 i := by
    intro b g i
    have hb : (b : GL (Fin 2) K).1 1 0 = 0 := b.2
    conv_lhs => rw [show g = (b : GL (Fin 2) K) * ((b : GL (Fin 2) K)⁻¹ * g) by group]
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb, zero_mul, zero_add]
  refine ⟨m + 1, (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ weyl F, ?_, fun x => ?_⟩
  · change SmoothRep.ind.toFun F (1 * weyl) = 0
    rw [one_mul]
    refine hF0 _ fun b hb => ?_
    have e := hdec b weyl 1
    rw [weyl_val] at e
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e
    have h0 := (mul_eq_zero.1 e.symm).resolve_left (val_one_one_ne_zero b.2)
    have := hu11 _ hb
    rw [h0, map_zero] at this
    exact zero_ne_one this
  · change (SmoothRep.ind.toFun F (weyl * unip x * weyl)).down = _
    rw [weyl_mul_unip_mul_weyl]
    split_ifs with hx
    · have hxlt : valuation K x < uniformizer K ^ m := lt_uniformizer_zpow_iff.2 hx
      have hpos : (0 : ValueGroupWithZero K) < uniformizer K ^ m := zero_lt_iff.2 hm0
      have hmem : ((1 : GL2.borel K) : GL (Fin 2) K)⁻¹ * lowerUnip x ∈ congruence K _ hm0 hm1 := by
        rw [OneMemClass.coe_one, inv_one, one_mul]
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · change valuation K ((!![1, 0; x, 1] - 1 : Matrix (Fin 2) (Fin 2) K) i j) < _
          fin_cases i <;> fin_cases j <;> simp [hxlt, hpos]
        · change valuation K ((!![1, 0; -x, 1] - 1 : Matrix (Fin 2) (Fin 2) K) i j) < _
          fin_cases i <;> fin_cases j <;> simp [hxlt, hpos]
      rw [hF1 1 _ hmem, map_one, Units.val_one]
    · rw [hF0 _ fun b hb => ?_]
      · rfl
      have hxlt : ¬ valuation K x < uniformizer K ^ m := fun h' => hx (lt_uniformizer_zpow_iff.1 h')
      have e0 := hdec b (lowerUnip x) 0
      have e1 := hdec b (lowerUnip x) 1
      change x = _ at e0
      change (1 : K) = _ at e1
      have hv1 := congrArg (valuation K) e1
      rw [map_one, map_mul, hu11 _ hb, mul_one] at hv1
      have h10 := hb.1 1 0
      simp only [Matrix.sub_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
        sub_zero] at h10
      apply hxlt
      rw [e0, map_mul, ← hv1, one_mul]
      exact h10

end BigCellFunction

section CosetSums

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

local notation "Vw" => principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂

/-- The translate of $f$ by $n \in N$ has the function $x \mapsto \varphi_f(x + n_{12})$. -/
theorem bigCellFun_ρ_of_mem (f : (Ψ).V) {n : GL (Fin 2) K} (hn : n ∈ unipotent K) (x : K) :
    bigCellFun ((Ψ).ρ n f) x = bigCellFun f (x + n.1 0 1) := by
  conv_lhs => rw [eq_unip hn]
  exact bigCellFun_ρ_unip f x _

/-- A coset sum over a subgroup of $N$ of a vector of $V_w$ is in $V_w$. -/
theorem cosetSum_mem_principalSeriesBigCell {f : (Ψ).V} (hf : f ∈ Vw) {N₁ : Subgroup (GL (Fin 2) K)}
    (hN₁ : N₁ ≤ unipotent K) (S : Subgroup N₁) [S.FiniteIndex] : (Ψ).cosetSum N₁ S f ∈ Vw := by
  have := Fintype.ofFinite (N₁ ⧸ S)
  rw [SmoothRep.cosetSum_eq_sum]
  exact Submodule.sum_mem _ fun q _ =>
    ρ_mem_principalSeriesBigCell hf (unipotent_le_borel (hN₁ (Quotient.out q).2))

/-- The function of a coset sum: $\varphi(x) = \sum_q \varphi_f(x + x_q)$, where $n(x_q)$ runs through the chosen representatives. -/
theorem bigCellFun_cosetSum (f : (Ψ).V) {N₁ : Subgroup (GL (Fin 2) K)} (hN₁ : N₁ ≤ unipotent K)
    (S : Subgroup N₁) [Fintype (N₁ ⧸ S)] (x : K) :
    bigCellFun ((Ψ).cosetSum N₁ S f) x =
      ∑ q : N₁ ⧸ S, bigCellFun f (x + ((Quotient.out q : N₁) : GL (Fin 2) K).1 0 1) := by
  rw [SmoothRep.cosetSum_eq_sum, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun q _ => bigCellFun_ρ_of_mem f (hN₁ (Quotient.out q).2) x

/-- Let $f$ be a vector such that $\varphi_f$ vanishes outside the ball $\{v(x) \le v(\varpi)^{n_1}\}$, and let $N_1$ be the subgroup of the $n(x)$ with $x$ in this ball. Then the function of the coset sum of $f$ over $N_1 / (N_1 \cap \mathrm{Stab}(f))$ is constant on the ball and $0$ outside it. -/
theorem bigCellFun_cosetSum_stabIn {f : (Ψ).V} {n₁ : ℤ}
    (hsupp : ∀ x, uniformizer K ^ n₁ < valuation K x → bigCellFun f x = 0) (x : K) :
    bigCellFun ((Ψ).cosetSum (unipBall K (uniformizer K ^ n₁))
        ((Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f) f) x =
      if valuation K x ≤ uniformizer K ^ n₁ then
        bigCellFun ((Ψ).cosetSum (unipBall K (uniformizer K ^ n₁))
          ((Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f) f) 0
      else 0 := by
  set N₁ := unipBall K (uniformizer K ^ n₁)
  have hN₁ : N₁ ≤ unipotent K := fun g hg => hg.1
  set S := (Ψ).stabIn N₁ f
  have := (Ψ).finiteIndex_stabIn (isCompact_unipBall (uniformizer K ^ n₁)) f
  have := Fintype.ofFinite (N₁ ⧸ S)
  let F : GL (Fin 2) K → ℂ := fun n => (SmoothRep.ind.toFun f (weyl * n)).down
  have hF : ∀ (n : GL (Fin 2) K) (s : N₁), s ∈ S → F (n * s) = F n := by
    intro n s hs
    have h := ((Ψ).mem_stabIn s).1 hs
    calc F (n * s) = (SmoothRep.ind.toFun ((Ψ).ρ s f) (weyl * n)).down := by
          simp only [F, ← mul_assoc]
          rfl
      _ = F n := by rw [h]
  have hsum : ∀ y, bigCellFun ((Ψ).cosetSum N₁ S f) y =
      ∑ q : N₁ ⧸ S, F (unip y * (Quotient.out q : N₁)) := by
    intro y
    rw [bigCellFun_cosetSum f hN₁]
    refine Finset.sum_congr rfl fun q _ => ?_
    conv_rhs => rw [eq_unip (hN₁ (Quotient.out q).2)]
    simp only [F, ← unip_add]
    rfl
  by_cases hx : valuation K x ≤ uniformizer K ^ n₁
  · simp only [hx, ↓reduceIte]
    rw [hsum, hsum, unip_zero]
    simp only [one_mul]
    exact sum_out_mul_left S F hF ⟨unip x, unip_mem x, by simpa [unip_val] using hx⟩
  · simp only [hx, ↓reduceIte]
    rw [bigCellFun_cosetSum f hN₁]
    refine Finset.sum_eq_zero fun q _ => hsupp _ ?_
    have hq : valuation K (((Quotient.out q : N₁) : GL (Fin 2) K).1 0 1) ≤ uniformizer K ^ n₁ :=
      (Quotient.out q).2.2
    have hlt := not_le.1 hx
    rw [Valuation.map_add_eq_of_lt_left _ (hq.trans_lt hlt)]
    exact hlt

/-- Let $f \in V_w$ with $\varphi_f = \kappa \cdot 1_{\{v(x) \le v(\varpi)^n\}}$ and $\kappa \neq 0$. Then $n(y)$ fixes $f$ exactly when $v(y) \le v(\varpi)^n$. -/
theorem mem_stabIn_of_indicator {f : (Ψ).V} {κ : ℂ} {n : ℤ} (hf : f ∈ Vw) (hκ : κ ≠ 0)
    (hφ : ∀ x, bigCellFun f x = if valuation K x ≤ uniformizer K ^ n then κ else 0)
    {N₁ : Subgroup (GL (Fin 2) K)} (hN₁ : N₁ ≤ unipotent K) (s : N₁) :
    s ∈ (Ψ).stabIn N₁ f ↔ valuation K ((s : GL (Fin 2) K).1 0 1) ≤ uniformizer K ^ n := by
  rw [SmoothRep.mem_stabIn]
  constructor
  · intro h
    have h0 := congrFun (congrArg bigCellFun h) 0
    rw [bigCellFun_ρ_of_mem f (hN₁ s.2), zero_add, hφ, hφ, map_zero] at h0
    by_contra hy
    simp only [hy, zero_le, ↓reduceIte] at h0
    exact hκ h0.symm
  · intro hy
    refine bigCellFun_inj (ρ_mem_principalSeriesBigCell hf (unipotent_le_borel (hN₁ s.2))) hf ?_
    funext x
    rw [bigCellFun_ρ_of_mem f (hN₁ s.2), hφ, hφ]
    have h := (piBall K n).add_mem_cancel_right (y := x) (mem_piBall.2 hy)
    simp only [mem_piBall] at h
    simp only [h]

/-- Under the same hypothesis, $N_1 \cap \mathrm{Stab}(f)$ is $N_1 \cap N(\varpi^n)$. -/
theorem stabIn_eq_of_indicator {f : (Ψ).V} {κ : ℂ} {n : ℤ} (hf : f ∈ Vw) (hκ : κ ≠ 0)
    (hφ : ∀ x, bigCellFun f x = if valuation K x ≤ uniformizer K ^ n then κ else 0)
    {N₁ : Subgroup (GL (Fin 2) K)} (hN₁ : N₁ ≤ unipotent K) :
    (Ψ).stabIn N₁ f = (unipBall K (uniformizer K ^ n)).subgroupOf N₁ := by
  ext s
  rw [mem_stabIn_of_indicator hf hκ hφ hN₁, Subgroup.mem_subgroupOf, mem_unipBall]
  exact ⟨fun h => ⟨hN₁ s.2, h⟩, fun h => h.2⟩

/-- Under the same hypothesis, the function of the coset sum of $f$ over $N_1 / (N_1 \cap \mathrm{Stab}(f))$ has the value $\kappa$ at $0$: only the trivial coset contributes. -/
theorem bigCellFun_cosetSum_zero_of_indicator {f : (Ψ).V} {κ : ℂ} {n : ℤ}
    (hf : f ∈ Vw) (hκ : κ ≠ 0)
    (hφ : ∀ x, bigCellFun f x = if valuation K x ≤ uniformizer K ^ n then κ else 0) (n₁ : ℤ) :
    bigCellFun ((Ψ).cosetSum (unipBall K (uniformizer K ^ n₁))
      ((Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f) f) 0 = κ := by
  have hN₁ : unipBall K (uniformizer K ^ n₁) ≤ unipotent K := fun g hg => hg.1
  have := (Ψ).finiteIndex_stabIn (isCompact_unipBall (uniformizer K ^ n₁)) f
  have := Fintype.ofFinite (unipBall K (uniformizer K ^ n₁) ⧸
    (Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f)
  classical
  have key : ∀ q : unipBall K (uniformizer K ^ n₁) ⧸
      (Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f,
      bigCellFun f (0 + ((Quotient.out q : unipBall K (uniformizer K ^ n₁)) :
        GL (Fin 2) K).1 0 1) =
      if q = ((1 : unipBall K (uniformizer K ^ n₁)) : _ ⧸ _) then κ else 0 := by
    intro q
    have h := (mem_stabIn_of_indicator hf hκ hφ hN₁ (Quotient.out q)).symm.trans (out_mem_iff q)
    rw [zero_add, hφ]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (h.1 h1) h2
    · exact absurd (h.2 h2) h1
    · rfl
  rw [bigCellFun_cosetSum f hN₁, Finset.sum_congr rfl fun q _ => key q, Finset.sum_ite_eq']
  simp

end CosetSums

section BigCellCoinvariants

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

local notation "Vw" => principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The subspace $V_w(N)$: the span of the vectors $n \cdot f - f$ with $n \in N$ and $f \in V_w$, as a subspace of the principal series. -/
noncomputable def bigCellJacquetKer : Submodule ℂ (Ψ).V :=
  Submodule.span ℂ {v | ∃ n ∈ unipotent K, ∃ f ∈ Vw, (Ψ).ρ n f - f = v}

local notation "Ww" => bigCellJacquetKer χ₁ χ₂ hχ₁ hχ₂

/-- The generators $n \cdot f - f$ of $V_w(N)$ are in $V_w(N)$. -/
theorem sub_mem_bigCellJacquetKer {n : GL (Fin 2) K} (hn : n ∈ unipotent K) {f : (Ψ).V}
    (hf : f ∈ Vw) : (Ψ).ρ n f - f ∈ Ww :=
  Submodule.subset_span ⟨n, hn, f, hf, rfl⟩

/-- The subspace $V_w(N)$ is contained in $V_w$. -/
theorem bigCellJacquetKer_le : Ww ≤ Vw :=
  Submodule.span_le.2 fun _ ⟨_, hn, _, hf, h⟩ =>
    h ▸ sub_mem (ρ_mem_principalSeriesBigCell hf (unipotent_le_borel hn)) hf

/-- The subspace $V_w(N)$ is contained in $V(N)$. -/
theorem bigCellJacquetKer_le_jacquetKer : Ww ≤ (Ψ).jacquetKer (unipotent K) :=
  Submodule.span_le.2 fun _ ⟨_, hn, f, _, h⟩ => h ▸ (Ψ).sub_mem_jacquetKer hn f

/-- The subspace $V_w(N)$ is stable under $T$. -/
theorem bigCellJacquetKer_stable (t : torus K) {v : (Ψ).V} (hv : v ∈ Ww) :
    (Ψ).ρ t v ∈ Ww := by
  refine (Submodule.span_le (p := (bigCellJacquetKer χ₁ χ₂ hχ₁ hχ₂).comap ((Ψ).ρ t))).2 ?_ hv
  rintro _ ⟨n, hn, f, hf, rfl⟩
  have hn' : (t : GL (Fin 2) K) * n * (t : GL (Fin 2) K)⁻¹ ∈ unipotent K :=
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_unipotent (torus_le_borel t.2)) n).1 hn
  have key : (Ψ).ρ t ((Ψ).ρ n f - f) =
      (Ψ).ρ ((t : GL (Fin 2) K) * n * (t : GL (Fin 2) K)⁻¹) ((Ψ).ρ t f) - (Ψ).ρ t f := by
    rw [map_sub]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  change (Ψ).ρ t ((Ψ).ρ n f - f) ∈ Ww
  rw [key]
  exact sub_mem_bigCellJacquetKer hn' (ρ_mem_principalSeriesBigCell hf (torus_le_borel t.2))

/-- For $f \in V_w$ and a subgroup $S$ of finite index of $N_1 \le N$, the vector $[N_1 : S] f - \sum_{q \in N_1 / S} n_q f$ is in $V_w(N)$. -/
theorem card_smul_sub_cosetSum_mem {f : (Ψ).V} (hf : f ∈ Vw) {N₁ : Subgroup (GL (Fin 2) K)}
    (hN₁ : N₁ ≤ unipotent K) (S : Subgroup N₁) [S.FiniteIndex] :
    (Nat.card (N₁ ⧸ S) : ℂ) • f - (Ψ).cosetSum N₁ S f ∈ Ww := by
  have := Fintype.ofFinite (N₁ ⧸ S)
  rw [SmoothRep.cosetSum_eq_sum, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Nat.cast_smul_eq_nsmul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [← neg_sub]
  exact neg_mem (sub_mem_bigCellJacquetKer (hN₁ (Quotient.out q).2) hf)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The index of a subgroup of finite index is a nonzero complex number. -/
theorem natCard_quotient_ne_zero {N₁ : Subgroup (GL (Fin 2) K)} (S : Subgroup N₁)
    [S.FiniteIndex] : (Nat.card (N₁ ⧸ S) : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero, ← Subgroup.index_eq_card]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- Let $f_0 \in V_w$ with $\varphi_{f_0} = 1_{\{v(x) \le v(\varpi)^{n_0}\}}$, and let $f \in V_w$ with $\varphi_f = 0$ outside $\{v(x) \le v(\varpi)^{n_1}\}$, for $n_1 \le n_0$. Let $N_1 = N(\varpi^{n_1})$. Then $[N_1 : S_f] f - c [N_1 : S_{f_0}] f_0 \in V_w(N)$, where $S_f$ is the stabilizer of $f$ in $N_1$ and $c$ is the value at $0$ of the function of the coset sum of $f$. -/
theorem sub_mem_bigCellJacquetKer_of_indicator {f₀ : (Ψ).V} {n₀ : ℤ} (hf₀ : f₀ ∈ Vw)
    (hφ₀ : ∀ x, bigCellFun f₀ x = if valuation K x ≤ uniformizer K ^ n₀ then 1 else 0)
    {f : (Ψ).V} (hf : f ∈ Vw) {n₁ : ℤ} (hn₁ : n₁ ≤ n₀)
    (hsupp : ∀ x, uniformizer K ^ n₁ < valuation K x → bigCellFun f x = 0) :
    (Nat.card (unipBall K (uniformizer K ^ n₁) ⧸
        (Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f) : ℂ) • f -
      (bigCellFun ((Ψ).cosetSum (unipBall K (uniformizer K ^ n₁))
          ((Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f) f) 0 *
        Nat.card (unipBall K (uniformizer K ^ n₁) ⧸
          (Ψ).stabIn (unipBall K (uniformizer K ^ n₁)) f₀)) • f₀ ∈ Ww := by
  set N₁ := unipBall K (uniformizer K ^ n₁)
  have hN₁ : N₁ ≤ unipotent K := fun g hg => hg.1
  have := (Ψ).finiteIndex_stabIn (isCompact_unipBall (uniformizer K ^ n₁)) f
  have := (Ψ).finiteIndex_stabIn (isCompact_unipBall (uniformizer K ^ n₁)) f₀
  set c := bigCellFun ((Ψ).cosetSum N₁ ((Ψ).stabIn N₁ f) f) 0
  have hsupp₀ : ∀ x, uniformizer K ^ n₁ < valuation K x → bigCellFun f₀ x = 0 := by
    intro x hx
    rw [hφ₀]
    have : ¬ valuation K x ≤ uniformizer K ^ n₀ := fun h =>
      (not_le.2 hx) (h.trans (uniformizer_zpow_le_iff.2 hn₁))
    simp only [this, ↓reduceIte]
  have heq : (Ψ).cosetSum N₁ ((Ψ).stabIn N₁ f) f =
      c • (Ψ).cosetSum N₁ ((Ψ).stabIn N₁ f₀) f₀ := by
    refine bigCellFun_inj (cosetSum_mem_principalSeriesBigCell hf hN₁ _)
      (Submodule.smul_mem _ _ (cosetSum_mem_principalSeriesBigCell hf₀ hN₁ _)) ?_
    funext x
    rw [map_smul, Pi.smul_apply, bigCellFun_cosetSum_stabIn hsupp,
      bigCellFun_cosetSum_stabIn hsupp₀, bigCellFun_cosetSum_zero_of_indicator hf₀ one_ne_zero hφ₀]
    split_ifs
    · simp [c]
      rfl
    · simp
  have h1 := card_smul_sub_cosetSum_mem hf hN₁ ((Ψ).stabIn N₁ f)
  have h2 := card_smul_sub_cosetSum_mem hf₀ hN₁ ((Ψ).stabIn N₁ f₀)
  have e : (Nat.card (N₁ ⧸ (Ψ).stabIn N₁ f) : ℂ) • f -
      (c * Nat.card (N₁ ⧸ (Ψ).stabIn N₁ f₀)) • f₀ =
      ((Nat.card (N₁ ⧸ (Ψ).stabIn N₁ f) : ℂ) • f - (Ψ).cosetSum N₁ ((Ψ).stabIn N₁ f) f) -
        c • ((Nat.card (N₁ ⧸ (Ψ).stabIn N₁ f₀) : ℂ) • f₀ -
          (Ψ).cosetSum N₁ ((Ψ).stabIn N₁ f₀) f₀) := by
    rw [heq, smul_sub, mul_smul]
    abel
  rw [e]
  exact sub_mem h1 (Submodule.smul_mem _ c h2)

/-- Let $f_0$ be as above. Then each $f \in V_w$ is congruent to a multiple of $f_0$ modulo $V_w(N)$. -/
theorem exists_sub_smul_mem_bigCellJacquetKer {f₀ : (Ψ).V} {n₀ : ℤ} (hf₀ : f₀ ∈ Vw)
    (hφ₀ : ∀ x, bigCellFun f₀ x = if valuation K x ≤ uniformizer K ^ n₀ then 1 else 0)
    {f : (Ψ).V} (hf : f ∈ Vw) : ∃ c : ℂ, f - c • f₀ ∈ Ww := by
  obtain ⟨n, hn⟩ := bigCellFun_eventually_zero hf
  have hsupp : ∀ x, uniformizer K ^ (min n n₀) < valuation K x → bigCellFun f x = 0 :=
    fun x hx => hn x ((uniformizer_zpow_le_iff.2 (min_le_left n n₀)).trans_lt hx)
  have hE := sub_mem_bigCellJacquetKer_of_indicator hf₀ hφ₀ hf (min_le_right n n₀) hsupp
  have := (Ψ).finiteIndex_stabIn (isCompact_unipBall (uniformizer K ^ (min n n₀))) f
  have hc := natCard_quotient_ne_zero ((Ψ).stabIn (unipBall K (uniformizer K ^ (min n n₀))) f)
  have h := Submodule.smul_mem Ww (Nat.card (unipBall K (uniformizer K ^ (min n n₀)) ⧸
    (Ψ).stabIn (unipBall K (uniformizer K ^ (min n n₀))) f) : ℂ)⁻¹ hE
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul] at h
  exact ⟨_, h⟩

/-- A finite set of matrices has a uniform bound on the valuation of the upper right entry. -/
theorem exists_zpow_bound (s : Finset (GL (Fin 2) K)) :
    ∃ n : ℤ, ∀ g ∈ s, valuation K (g.1 0 1) ≤ uniformizer K ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨n, h⟩ := ih
    by_cases ha : a.1 0 1 = 0
    · refine ⟨n, fun g hg => ?_⟩
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · simp [ha]
      · exact h g hg
    · obtain ⟨k, hk⟩ := exists_valuation_eq_zpow ha
      refine ⟨min n k, fun g hg => ?_⟩
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · rw [hk]
        exact uniformizer_zpow_le_iff.2 (min_le_right _ _)
      · exact (h g hg).trans (uniformizer_zpow_le_iff.2 (min_le_left _ _))

/-- The vector $f_0$ is not in $V(N)$: by Jacquet's lemma, for a large compact open subgroup $N_1$ of $N$ the coset sum of $f_0$ over $N_1$ would be $0$, but its function has the value $1$ at $0$. -/
theorem not_mem_jacquetKer_of_indicator {f₀ : (Ψ).V} {n₀ : ℤ} (hf₀ : f₀ ∈ Vw)
    (hφ₀ : ∀ x, bigCellFun f₀ x = if valuation K x ≤ uniformizer K ^ n₀ then 1 else 0) :
    f₀ ∉ (Ψ).jacquetKer (unipotent K) := by
  intro h
  obtain ⟨s, hsN, hs⟩ := (Ψ).cosetSum_eq_zero_of_mem_jacquetKer h
  obtain ⟨n, hn⟩ := exists_zpow_bound s
  have h0 := hs (unipBall K (uniformizer K ^ n)) (isCompact_unipBall _)
    (fun g hg => ⟨hsN hg, hn g hg⟩)
  have h1 := bigCellFun_cosetSum_zero_of_indicator hf₀ one_ne_zero hφ₀ n
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/-- A vector of $V_w$ that is in $V(N)$ is in $V_w(N)$. This is the injectivity of $(V_w)_N \to V_N$. -/
theorem mem_bigCellJacquetKer_of_mem_jacquetKer {f : (Ψ).V} (hf : f ∈ Vw)
    (h : f ∈ (Ψ).jacquetKer (unipotent K)) : f ∈ Ww := by
  obtain ⟨N₀, hN₀, hav⟩ := ((Ψ).mem_jacquetKer_unipotent_iff f).1 h
  have hcs := ((Ψ).nAverage_eq_zero_iff hN₀.2.1 f).1 hav
  have := (Ψ).finiteIndex_stabIn hN₀.2.1 f
  have h1 := card_smul_sub_cosetSum_mem hf hN₀.1 ((Ψ).stabIn N₀ f)
  rw [hcs, sub_zero] at h1
  have hc := natCard_quotient_ne_zero ((Ψ).stabIn N₀ f)
  have h2 := Submodule.smul_mem Ww (Nat.card (N₀ ⧸ (Ψ).stabIn N₀ f) : ℂ)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

variable (χ₁ χ₂) in
/-- The character $\mathrm{diag}(a, d) \mapsto \chi_2(a)|a| \chi_1(d)|d|^{-1}$ of $T$. This is the conjugate $\chi_2 \otimes \chi_1$ of $\chi_1 \otimes \chi_2$ by the Weyl element, twisted by the modulus character $\delta_B(\mathrm{diag}(a, d)) = |a/d|$. -/
noncomputable def bigCellChar : torus K →* ℂˣ :=
  torusChar (χ₂ * absChar K) (χ₁ * (absChar K)⁻¹)

/-- The character `bigCellChar` is smooth. -/
theorem isOpen_ker_bigCellChar (hχ₁ : IsSmoothChar K χ₁) (hχ₂ : IsSmoothChar K χ₂) :
    IsOpen ((bigCellChar χ₁ χ₂).ker : Set (torus K)) :=
  isOpen_ker_torusChar (hχ₂.mul isSmoothChar_absChar) (hχ₁.mul isSmoothChar_absChar.inv)

/-- Let $f_0$ be as above. Then $t \cdot f_0 \equiv \theta(t) f_0$ modulo $V_w(N)$ for each $t \in T$, where $\theta$ is `bigCellChar`. -/
theorem ρ_torus_sub_mem_bigCellJacquetKer {f₀ : (Ψ).V} {n₀ : ℤ} (hf₀ : f₀ ∈ Vw)
    (hφ₀ : ∀ x, bigCellFun f₀ x = if valuation K x ≤ uniformizer K ^ n₀ then 1 else 0)
    (t : torus K) : (Ψ).ρ t f₀ - (bigCellChar χ₁ χ₂ t : ℂ) • f₀ ∈ Ww := by
  set b : GL2.borel K := ⟨t, torus_le_borel t.2⟩
  set a : K := (t : GL (Fin 2) K).1 0 0
  set d : K := (t : GL (Fin 2) K).1 1 1
  have ha : a ≠ 0 := (diagFst b).ne_zero
  have hd : d ≠ 0 := (diagSnd b).ne_zero
  set κ : ℂ := (χ₁ (diagSnd b) : ℂ) * χ₂ (diagFst b)
  have hκ : κ ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  obtain ⟨j, hj⟩ := exists_valuation_eq_zpow (div_ne_zero hd ha)
  have hf : (Ψ).ρ t f₀ ∈ Vw := ρ_mem_principalSeriesBigCell hf₀ (torus_le_borel t.2)
  have hφ : ∀ x, bigCellFun ((Ψ).ρ t f₀) x =
      if valuation K x ≤ uniformizer K ^ (n₀ - j) then κ else 0 := by
    intro x
    rw [bigCellFun_ρ_torus, mul_div_assoc, hφ₀, map_mul, hj]
    have hiff : valuation K x * uniformizer K ^ j ≤ uniformizer K ^ n₀ ↔
        valuation K x ≤ uniformizer K ^ (n₀ - j) := by
      rw [zpow_sub₀ uniformizer_ne_zero, le_div_iff₀ (zpow_pos uniformizer_pos _)]
    by_cases hx : valuation K x ≤ uniformizer K ^ (n₀ - j)
    · simp only [hiff.2 hx, hx, ↓reduceIte, mul_one]
      rfl
    · simp only [mt hiff.1 hx, hx, ↓reduceIte, mul_zero]
  set n₁ := min n₀ (n₀ - j)
  have hsupp : ∀ x, uniformizer K ^ n₁ < valuation K x → bigCellFun ((Ψ).ρ t f₀) x = 0 := by
    intro x hx
    rw [hφ]
    have : ¬ valuation K x ≤ uniformizer K ^ (n₀ - j) := fun h =>
      (not_le.2 hx) (h.trans (uniformizer_zpow_le_iff.2 (min_le_right _ _)))
    simp only [this, ↓reduceIte]
  have hE := sub_mem_bigCellJacquetKer_of_indicator hf₀ hφ₀ hf (min_le_left n₀ (n₀ - j)) hsupp
  have hN₁ : unipBall K (uniformizer K ^ n₁) ≤ unipotent K := fun g hg => hg.1
  rw [bigCellFun_cosetSum_zero_of_indicator hf hκ hφ n₁,
    stabIn_eq_of_indicator hf hκ hφ hN₁, stabIn_eq_of_indicator hf₀ one_ne_zero hφ₀ hN₁] at hE
  set q : ℂ := (residueCard K : ℂ)
  have hq : q ≠ 0 := Nat.cast_ne_zero.2 (residueCard_pos K).ne'
  have hcard : ∀ m : ℤ, n₁ ≤ m → (Nat.card (unipBall K (uniformizer K ^ n₁) ⧸
      (unipBall K (uniformizer K ^ m)).subgroupOf (unipBall K (uniformizer K ^ n₁))) : ℂ) =
        q ^ (m - n₁) := by
    intro m hm
    have h := congrArg (fun r : ℝ => (r : ℂ)) (relIndex_unipBall_eq (K := K) hm)
    push_cast at h
    rw [← Subgroup.index_eq_card]
    exact h
  rw [hcard _ (min_le_right _ _), hcard _ (min_le_left _ _)] at hE
  have hθ : (bigCellChar χ₁ χ₂ t : ℂ) = κ * q ^ j := by
    have hr : normAbs K a * (normAbs K d)⁻¹ = (residueCard K : ℝ) ^ j := by
      rw [← div_eq_mul_inv, ← inv_div, ← normAbs_div, normAbs_eq_zpow (div_ne_zero hd ha) hj,
        zpow_neg, inv_inv]
    have hrC : ((normAbs K a : ℝ) : ℂ) * ((normAbs K d : ℝ) : ℂ)⁻¹ = q ^ j := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hr, Complex.ofReal_zpow,
        Complex.ofReal_natCast]
    change ((χ₂ * absChar K) (diagFst b) * (χ₁ * (absChar K)⁻¹) (diagSnd b) : ℂˣ).1 = _
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      absChar_apply, val_diagFst, val_diagSnd]
    linear_combination κ * hrC
  have hne : q ^ (n₀ - j - n₁) ≠ 0 := zpow_ne_zero _ hq
  have h := Submodule.smul_mem Ww (q ^ (n₀ - j - n₁))⁻¹ hE
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_smul] at h
  convert h using 3
  rw [hθ, show n₀ - n₁ = (n₀ - j - n₁) + j by ring, zpow_add₀ hq]
  field_simp

end BigCellCoinvariants

section BigCellJacquet

variable {χ₁ χ₂ : Kˣ →* ℂˣ} {hχ₁ : IsSmoothChar K χ₁} {hχ₂ : IsSmoothChar K χ₂}

local notation "Ψ" => principalSeriesInd χ₁ χ₂ hχ₁ hχ₂

local notation "Vw" => principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂

local notation "Ww" => bigCellJacquetKer χ₁ χ₂ hχ₁ hχ₂

local notation "hTN" => torus_le_borel.trans borel_le_normalizer_unipotent

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The representation of $T$ on $V_w$, by restriction of the principal series. -/
noncomputable def bigCellRep : Representation ℂ (torus K) (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) :=
  Representation.subrepresentation ((principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ.comp (torus K).subtype)
    (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂)
    (fun t _ hf => ρ_mem_principalSeriesBigCell hf (torus_le_borel t.2))

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The subspace $V_w(N)$, as a subspace of $V_w$. -/
noncomputable def bigCellJacquetKerSub : Submodule ℂ (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) :=
  (bigCellJacquetKer χ₁ χ₂ hχ₁ hχ₂).comap (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂).subtype

/-- The subspace $V_w(N)$ of $V_w$ is stable under $T$. -/
theorem bigCellJacquetKerSub_stable (t : torus K) :
    bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂ ≤
      (bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂).comap (bigCellRep χ₁ χ₂ hχ₁ hχ₂ t) :=
  fun _ hf => bigCellJacquetKer_stable t hf

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The Jacquet module $(V_w)_N = V_w / V_w(N)$ of the subspace $V_w$ of the principal series, as a smooth representation of $T$. -/
noncomputable def bigCellJacquet : SmoothRep (torus K) where
  V := principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂ ⧸ bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂
  ρ := Representation.quotient (bigCellRep χ₁ χ₂ hχ₁ hχ₂) _ bigCellJacquetKerSub_stable
  smooth x := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : IsOpen ((Subtype.val : torus K → GL (Fin 2) K) ⁻¹'
        (vecStabilizer (principalSeriesInd χ₁ χ₂ hχ₁ hχ₂).ρ (f : (Ψ).V) : Set _)) :=
      continuous_subtype_val.isOpen_preimage _ ((Ψ).smooth f)
    refine Subgroup.isOpen_mono
      (H₁ := (vecStabilizer (Ψ).ρ (f : (Ψ).V)).comap (torus K).subtype) ?_ this
    intro m hm
    rw [Subgroup.mem_comap, mem_vecStabilizer] at hm
    rw [mem_vecStabilizer]
    change Submodule.Quotient.mk (bigCellRep χ₁ χ₂ hχ₁ hχ₂ m f) = _
    congr 1
    exact Subtype.ext hm

variable (χ₁ χ₂ hχ₁ hχ₂) in
/-- The map $(V_w)_N \to (\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N$ of representations of $T$ that the inclusion $V_w \subseteq \mathrm{Ind}_B^G(\chi_1 \otimes \chi_2)$ gives. -/
noncomputable def bigCellJacquetIncl :
    IntertwiningMap (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).ρ (principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂).ρ where
  toLinearMap := (bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂).liftQ
    ((Ψ).jacquetMk (unipotent K) (torus K) hTN ∘ₗ (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂).subtype)
    (fun _ hf => LinearMap.mem_ker.2 (((Ψ).jacquetMk_eq_zero_iff hTN _).2
      (bigCellJacquetKer_le_jacquetKer hf)))
  isIntertwining' _ := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The value of `bigCellJacquetIncl` at the class of $f \in V_w$ is the class of $f$. -/
theorem bigCellJacquetIncl_mk (f : principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂) :
    bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂ (Submodule.Quotient.mk f) =
      (Ψ).jacquetMk (unipotent K) (torus K) hTN f :=
  rfl

/-- The map $(V_w)_N \to V_N$ is injective. -/
theorem bigCellJacquetIncl_injective :
    Function.Injective (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂) := by
  change Function.Injective ((bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂).liftQ _ _)
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun f hf => ?_
  rw [LinearMap.mem_ker] at hf
  exact mem_bigCellJacquetKer_of_mem_jacquetKer f.2 (((Ψ).jacquetMk_eq_zero_iff hTN _).1 hf)

/-- The sequence $(V_w)_N \to V_N \to \chi_1 \otimes \chi_2$ is exact. -/
theorem bigCellJacquetIncl_exact :
    Function.Exact (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂) (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂) := by
  intro y
  constructor
  · intro hy
    obtain ⟨g, rfl⟩ := (Ψ).jacquetMk_surjective (unipotent K) (torus K) hTN y
    have hg : g ∈ Vw := hy
    exact ⟨Submodule.Quotient.mk ⟨g, hg⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hg

/-- The Jacquet module $(V_w)_N$ is isomorphic to the character `bigCellChar` of $T$: $\mathrm{diag}(a, d) \mapsto \chi_2(a)|a| \chi_1(d)|d|^{-1}$. -/
theorem bigCellJacquet_iso :
    (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).Iso
      (SmoothRep.charRep (bigCellChar χ₁ χ₂) (isOpen_ker_bigCellChar hχ₁ hχ₂)) := by
  obtain ⟨n₀, f₀, hf₀, hφ₀⟩ := exists_bigCellFun_indicator (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁)
    (hχ₂ := hχ₂)
  let x₀ : principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂ ⧸ bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂ :=
    Submodule.Quotient.mk ⟨f₀, hf₀⟩
  let L : ULift.{u} ℂ →ₗ[ℂ] principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂ ⧸
      bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂ :=
    LinearMap.toSpanSingleton ℂ _ x₀ ∘ₗ ULift.moduleEquiv.toLinearMap
  have hL : ∀ c : ULift.{u} ℂ, L c = c.down • x₀ := fun _ => rfl
  have hx₀ : x₀ ≠ 0 := by
    intro h
    refine not_mem_jacquetKer_of_indicator hf₀ hφ₀ (bigCellJacquetKer_le_jacquetKer ?_)
    exact (Submodule.Quotient.mk_eq_zero (bigCellJacquetKerSub χ₁ χ₂ hχ₁ hχ₂)).1 h
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker, hL, smul_eq_zero] at hc
    rcases hc with hc | hc
    · exact ULift.ext hc
    · exact absurd hc hx₀
  have hsurj : Function.Surjective L := by
    intro x
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc⟩ := exists_sub_smul_mem_bigCellJacquetKer hf₀ hφ₀ hf
    refine ⟨ULift.up c, ?_⟩
    rw [hL]
    change Submodule.Quotient.mk (c • (⟨f₀, hf₀⟩ : principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂)) = _
    rw [Submodule.Quotient.eq]
    change c • f₀ - f ∈ Ww
    rw [← neg_sub]
    exact neg_mem hc
  have hx : ∀ t : torus K, (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).ρ t x₀ =
      (bigCellChar χ₁ χ₂ t : ℂ) • x₀ := by
    intro t
    change Submodule.Quotient.mk (bigCellRep χ₁ χ₂ hχ₁ hχ₂ t ⟨f₀, hf₀⟩) =
      Submodule.Quotient.mk ((bigCellChar χ₁ χ₂ t : ℂ) •
        (⟨f₀, hf₀⟩ : principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂))
    rw [Submodule.Quotient.eq]
    exact ρ_torus_sub_mem_bigCellJacquetKer hf₀ hφ₀ t
  refine SmoothRep.Iso.symm ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun t c => ?_⟩
  obtain ⟨c⟩ := c
  change ((bigCellChar χ₁ χ₂ t : ℂ) * c) • x₀ = (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).ρ t (c • x₀)
  rw [mul_comm, ← smul_smul, ← hx]
  exact (map_smul ((bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).ρ t) c x₀).symm

/-- The Jacquet module $(V_w)_N$ has dimension $1$. -/
theorem finrank_bigCellJacquet : Module.finrank ℂ (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).V = 1 := by
  obtain ⟨e, -⟩ := (bigCellJacquet_iso (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂))
  rw [e.finrank_eq]
  change Module.finrank ℂ (ULift.{u} ℂ) = 1
  rw [ULift.moduleEquiv.finrank_eq, Module.finrank_self]

/-- The Jacquet module $(\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N$ has finite dimension. -/
theorem principalSeriesJacquet_finite :
    Module.Finite ℂ (principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂).V := by
  have : Module.Finite ℂ (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).V :=
    Module.finite_of_finrank_eq_succ finrank_bigCellJacquet
  have : Module.Finite ℂ (SmoothRep.charRep (torusChar χ₁ χ₂)
      (isOpen_ker_torusChar hχ₁ hχ₂)).V :=
    Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).symm
  exact Module.Finite.of_exact (f := (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂).toLinearMap)
    (g := (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂).toLinearMap)
    bigCellJacquetIncl_exact (principalSeriesJacquetEval_surjective hχ₁ hχ₂)

/-- The Jacquet module $(\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N$ of the principal series has dimension $2$. -/
theorem finrank_principalSeriesJacquet :
    Module.finrank ℂ (principalSeriesJacquet χ₁ χ₂ hχ₁ hχ₂).V = 2 := by
  have := principalSeriesJacquet_finite (χ₁ := χ₁) (χ₂ := χ₂) (hχ₁ := hχ₁) (hχ₂ := hχ₂)
  set g := (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂).toLinearMap
  set ι := (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂).toLinearMap
  rw [← LinearMap.finrank_range_add_finrank_ker g]
  have h1 : LinearMap.range g = ⊤ :=
    LinearMap.range_eq_top.2 (principalSeriesJacquetEval_surjective hχ₁ hχ₂)
  have h2 : LinearMap.ker g = LinearMap.range ι :=
    (LinearMap.exact_iff.1 bigCellJacquetIncl_exact)
  rw [h1, h2, finrank_top, LinearMap.finrank_range_of_inj bigCellJacquetIncl_injective,
    finrank_bigCellJacquet]
  change Module.finrank ℂ (ULift.{u} ℂ) + 1 = 2
  rw [ULift.moduleEquiv.finrank_eq, Module.finrank_self]

/-- The first step: $0 \to V_w \to \mathrm{Ind}_B^G(\chi_1 \otimes \chi_2) \to \mathbb{C} \to 0$ is exact, where the second map is $f \mapsto f(1)$. -/
theorem principalSeriesBigCell_shortExact :
    Function.Exact (principalSeriesBigCell χ₁ χ₂ hχ₁ hχ₂).subtype
        (principalSeriesEvalOne χ₁ χ₂ hχ₁ hχ₂) ∧
      Function.Surjective (principalSeriesEvalOne χ₁ χ₂ hχ₁ hχ₂) := by
  refine ⟨LinearMap.exact_subtype_ker_map _, fun y => ?_⟩
  obtain ⟨f, hf⟩ := principalSeriesInd_exists_eq_one hχ₁ hχ₂
  refine ⟨y.down • f, ?_⟩
  rw [map_smul]
  change y.down • SmoothRep.ind.toFun f 1 = y
  rw [hf]
  apply ULift.ext
  change y.down * 1 = y.down
  rw [mul_one]

/-- The Jacquet module of the principal series is an extension of $\chi_1 \otimes \chi_2$ by $(V_w)_N$: the sequence $0 \to (V_w)_N \to (\mathrm{Ind}_B^G(\chi_1 \otimes \chi_2))_N \to \chi_1 \otimes \chi_2 \to 0$ of representations of $T$ is exact, and $(V_w)_N$ is the character `bigCellChar`. -/
theorem principalSeriesJacquet_shortExact :
    Function.Injective (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂) ∧
      Function.Exact (bigCellJacquetIncl χ₁ χ₂ hχ₁ hχ₂)
        (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂) ∧
      Function.Surjective (principalSeriesJacquetEval χ₁ χ₂ hχ₁ hχ₂) ∧
      (bigCellJacquet χ₁ χ₂ hχ₁ hχ₂).Iso
        (SmoothRep.charRep (bigCellChar χ₁ χ₂) (isOpen_ker_bigCellChar hχ₁ hχ₂)) :=
  ⟨bigCellJacquetIncl_injective, bigCellJacquetIncl_exact,
    principalSeriesJacquetEval_surjective hχ₁ hχ₂, bigCellJacquet_iso⟩

end BigCellJacquet

end Langlands
