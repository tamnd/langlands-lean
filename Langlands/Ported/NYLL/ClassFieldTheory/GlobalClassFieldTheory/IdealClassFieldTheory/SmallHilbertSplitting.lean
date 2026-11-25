/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertSplitting.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.Algebra.PrincipalFractionalIdeal
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius
public import Langlands.Ported.NYLL.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-!
# Splitting in the small Hilbert class field

The small Hilbert class field has reciprocity quotient the ordinary ideal
class group.  Thus the Frobenius class of a finite prime is its ordinary
ideal class, and it is trivial precisely when the prime ideal is principal.
-/



@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFieldTheory
open NumberField IsDedekindDomain


variable {K : Type*} [Field K] [NumberField K]

/-- The Frobenius class of a finite prime in the reciprocity quotient of
the small Hilbert class field. -/
noncomputable def smallHilbertFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      GlobalClassFields.smallHilbertClassFieldNormSubgroup :=
  (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm
    (ClassGroup.mk K (finitePrimeFractionalIdeal v))

/-- Reciprocity formulation of complete splitting in the small Hilbert
class field: the prime Frobenius class is trivial. -/
def SplitsCompletelyInSmallHilbertClassField
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  smallHilbertFrobeniusClass v = 1

/-- A finite prime splits completely in the small Hilbert class
field if and only if its prime ideal is principal. -/
theorem splitsCompletelyInSmallHilbertClassField_iff_principal
    (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletelyInSmallHilbertClassField v ↔
      finitePrimeFractionalIdeal v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  change
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)).symm
          (ClassGroup.mk K (finitePrimeFractionalIdeal v)) =
        1 ↔
      finitePrimeFractionalIdeal v ∈
        (toPrincipalIdeal (𝓞 K) K).range
  rw [←
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.map_one,
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.injective.eq_iff]
  exact
    ClassGroup.mk_eq_one_iff_mem_principal
      (finitePrimeFractionalIdeal v)

/-- Existential generator form of the small Hilbert splitting criterion. -/
theorem splitsCompletelyInSmallHilbertClassField_iff_exists_generator
    (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletelyInSmallHilbertClassField v ↔
      ∃ x : Kˣ,
        toPrincipalIdeal (𝓞 K) K x =
          finitePrimeFractionalIdeal v := by
  rw [splitsCompletelyInSmallHilbertClassField_iff_principal]
  rfl

end IdealClassFieldTheory
end GlobalClassFieldTheory
