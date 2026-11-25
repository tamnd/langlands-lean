/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ClassFieldTheory/Theorems/GlobalClassFieldTheory/All.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.

import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocityQuotient
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquivMk
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinNormKernel
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinDecomposition
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceCompletionLocalArtin
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinLocalValue
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
import Langlands.Ported.NYLL.ClassFieldTheory.Theorems.GlobalClassFieldTheory.MaximalAbelianGlobalArtin

/-!
# Global class field theory

This module collects finite ideal-theoretic reciprocity and the topological
maximal-abelian statements. The latter are proved via topological comparison
with the existing restricted-product implementation.
-/
