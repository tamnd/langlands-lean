/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Bridge.FormalConjectures
import Langlands.Bridge.NYLL
import Langlands.Cohomology.Shapiro
import Langlands.Fidelity.ClassField
import Langlands.Fidelity.Galois
import Langlands.Fidelity.Maass
import Langlands.Fidelity.Modularity
import Langlands.Ported.FormalConjectures.Wikipedia
import Langlands.Reciprocity.Exists
import Langlands.Reciprocity.GL1
import Langlands.Reciprocity.Unique
import Langlands.Statements.Basic
import Langlands.Statements.ClassField
import Langlands.Statements.Galois
import Langlands.Statements.Hecke
import Langlands.Statements.Maass
import Langlands.Statements.Modularity
import Langlands.Statements.Torus
import Langlands.Statements.TorusInduced
import Langlands.Torus.Induced
import Langlands.Torus.Split
import Langlands.WeilGroup.Ab
import Langlands.WeilGroup.Degree
import Langlands.WeilGroup.Dense
import Langlands.WeilGroup.Embedding
import Langlands.WeilGroup.Inertia
import Langlands.WeilGroup.Restrict

/-!
# The Langlands program in Lean

This is the root of the package `Langlands`. It imports each file of the main tree. The statements of the program are in `Langlands/Statements/`.
-/
