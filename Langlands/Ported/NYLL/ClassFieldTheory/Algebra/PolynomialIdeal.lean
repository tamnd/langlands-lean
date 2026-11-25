/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Algebra/PolynomialIdeal.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.Ideal.BigOperators

/-! # Polynomial evaluation in an ideal -/

@[expose] public section

/-- Evaluating a polynomial whose coefficient images belong to an ideal stays in that ideal. -/
theorem Polynomial.eval₂_mem_ideal_of_coeff_mem
    {R : Type*} {S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) :
    P.eval₂ f z ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right (z ^ i) I (hcoeff i)
