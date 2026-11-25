/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/KroneckerWeber/Core.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

module

public import Langlands.Ported.NYLL.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.Final
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.RayClassComparison
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.Setup
public import Langlands.Ported.NYLL.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

@[expose] public section

noncomputable section

universe u

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type u) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  let : Small.{0} L := ClassFieldTheory.numberField_small L
  let S := Shrink.{0} L
  let : NumberField S := ClassFieldTheory.numberField_shrink L
  let e : S ≃ₐ[ℚ] L := (Shrink.ringEquiv L).toRatAlgEquiv
  let : IsAbelianGalois ℚ S := IsAbelianGalois.of_algHom e.toAlgHom
  exact ⟨kroneckerWeberConductorCandidate (L := S),
    kroneckerWeberConductorCandidate_pos (L := S),
    ⟨(kroneckerWeberCyclotomicEmbedding (L := S)).comp e.symm.toAlgHom⟩⟩

end KroneckerWeber

end
