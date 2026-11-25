/-
Copyright (c) 2026 The langlands authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Langlands.Bridge.FormalConjectures
import Langlands.Bridge.NYLL
import Langlands.Bridge.NYLLGlobal
import Langlands.Cohomology.Shapiro
import Langlands.Fidelity.ClassField
import Langlands.Fidelity.Galois
import Langlands.Fidelity.Maass
import Langlands.Fidelity.Modularity
import Langlands.Hecke.Rational
import Langlands.Ported.FormalConjectures.Wikipedia
import Langlands.Reciprocity.Exists
import Langlands.Reciprocity.GL1
import Langlands.Reciprocity.Unique
import Langlands.Statements.Automorphic
import Langlands.Statements.Basic
import Langlands.Statements.ClassField
import Langlands.Statements.FunctionField
import Langlands.Statements.FundamentalLemma
import Langlands.Statements.Galois
import Langlands.Statements.GSp4
import Langlands.Statements.GlobalGL
import Langlands.Statements.GodementJacquet
import Langlands.Statements.HasseWeil
import Langlands.Statements.Hecke
import Langlands.Statements.LocalLanglands
import Langlands.Statements.Maass
import Langlands.Statements.Modularity
import Langlands.Statements.NumberFieldGL
import Langlands.Statements.PadicGalois
import Langlands.Statements.Reciprocity
import Langlands.Statements.Smooth
import Langlands.Statements.Torus
import Langlands.Statements.TorusInduced
import Langlands.Statements.WeilDeligne
import Langlands.Tate.ArchimedeanFourier
import Langlands.Tate.ArchimedeanGamma
import Langlands.Tate.ArchimedeanParameter
import Langlands.Tate.ArchimedeanZeta
import Langlands.Tate.NonArchimedeanCharacter
import Langlands.Tate.NonArchimedeanFourier
import Langlands.Tate.NonArchimedeanGauss
import Langlands.Tate.NonArchimedeanLocalEquation
import Langlands.Tate.NonArchimedeanMeasure
import Langlands.Tate.NonArchimedeanZeta
import Langlands.Tate.PoissonLattice
import Langlands.Tate.PoissonSummation
import Langlands.Tate.PoissonTheta
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
