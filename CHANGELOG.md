# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- `Langlands/Tate/DedekindFE.lean`: the functional equation of the Dedekind zeta function of each number field K. The completed function xi_K(u) is |d_K|^(u/2) Gamma_K(u) zeta_K(u) for Re u > 1, it is holomorphic outside u = 0 and u = 1, and xi_K(1 - u) = xi_K(u). This is the case of the trivial character of the theorem of Hecke.

- `Langlands/Tate/UnitClass.lean`: the integral ideals I with a I principal are the ideals in the class of the inverse of a, and a generator of a I has the norm N(a) N(I). So the Mellin transform of the unit theta function is a multiple of the partial zeta function of the class of the inverse of a.

## v0.1.12 (2026-11-26)

### Added

- `Langlands/Tate/UnitMellin.lean`: the change of variables of Mathlib's `expMapBasis` in the integral of the Gamma factor of a number field, and the Mellin transform of one theta term integrated over all unit coordinates c in R^r. This is the second step of the proof of Hecke of the functional equation of the Dedekind zeta function.
- `Langlands/Tate/UnitUnfold.lean`: the unfolding of the unit theta function over the units of O_K, and the Mellin transform of the unit theta function as a Dirichlet series over the integral ideals I with a I principal. This is the third step of the proof of Hecke of the functional equation of the Dedekind zeta function.

## v0.1.11 (2026-11-26)

### Added

- `Langlands/Tate/UnitTheta.lean`: the theta function of a fractional ideal averaged over the units with an integral over [0, 1)^r, its transformation formula with the dual ideal, its decay at infinity, and the pair of the two functions as a `WeakFEPair`. This is the first step of the proof of Hecke of the functional equation of the Dedekind zeta function of each number field.

## v0.1.10 (2026-11-26)

### Added

- `Langlands/Tate/QuadraticDedekind.lean`: the Dedekind zeta function of an imaginary quadratic field as the class zeta function at 2u, with its holomorphic continuation to C minus {0, 1} and its functional equation under u to 1 - u. The file proves that each unit of the field is a root of unity and counts the generators of a principal ideal J I.

## v0.1.9 (2026-11-26)

### Added

- `Langlands/Tate/IdealZeta.lean`: the trace form zeta function of a nonzero fractional ideal of a number field, its continuation, its residue at s = n and its functional equation with the dual ideal for the trace form. The file also proves that two lattices with the same theta function and the same covolume have the same completed Epstein zeta function.
- `Langlands/Tate/ImaginaryQuadratic.lean`: the class zeta function of an imaginary quadratic field, a sum over the ideal classes, with its Dirichlet series and its functional equation under s to 2 - s. The file proves that each term depends only on the ideal class, with the identity theorem for holomorphic functions.

### Fixed

- `manifests/statements.sha256` has the hash of each of the 21 files of `Langlands/Statements/`. Before, it did not list 13 of them, and the hash of `Galois.lean` was the hash before the change of #49. Row Q4 of the trust report reads this file.

## v0.1.8 (2026-11-26)

### Added

- `Langlands/Tate/EpsteinZeta.lean`: the Epstein zeta function of a full lattice in a real inner product space, its meromorphic continuation, the functional equation that relates the lattice to its dual lattice, and the residue at s = n. The file also proves that the dual of the dual lattice is the lattice and that the dual lattice has the inverse covolume.

## v0.1.7 (2026-11-26)

### Added

- `Langlands/Statements/GSp4.lean`: `LocalLanglandsGSp4`, the theorem of Gan and Takeda, with GSp(4) as a matrix group, its L-parameters into GSp(4, C) and the size of each discrete L-packet.
- `Langlands/Statements/NumberFieldGL.lean` and `Reciprocity.lean`: the algebraic and regular algebraic cusp forms of Clozel through the Capelli operator, l-adic Galois representations of a number field, and the statements `ReciprocityGL` (open, weak form), `AutomorphicToGalois` and `GlobalJacquetLanglandsGL2`.
- `Langlands/Tate/GlobalLattice.lean`, `DedekindTheta.lean` and `DedekindMellin.lean`: the lattice of a fractional ideal with its covolume and its dual, the theta transformation formula for a number field, the Gamma factor of a number field and the Mellin transform of one term of the theta function.

### Fixed

- `Langlands/Statements/Galois.lean`: the docstring of `ArtinConjecture` now says correctly how the poles of the completed L-function and of L(s, rho) are related.

## v0.1.6 (2026-11-26)

### Added

- `Langlands/Tate/NonArchimedeanCharacter.lean`, `NonArchimedeanGauss.lean` and `NonArchimedeanLocalEquation.lean`: the invariance of the multiplicative measure at a finite place, the vanishing of the zeta integral of a ramified character on the integers, Gauss sums with the absolute value q^(-a/2), and the local functional equation of Tate's thesis at a finite place for an unramified and for a ramified character, with an explicit epsilon factor.
- `Langlands/Statements/FunctionField.lean`: `ReciprocityFunctionFieldGL`, the theorem of L. Lafforgue for GL(n) over a global function field, with the places, the adele ring, cusp eigenforms, Hecke operators and l-adic Galois representations of a function field.

## v0.1.5 (2026-11-26)

### Added

- `Langlands/Tate/NonArchimedean*.lean`: the Haar measure on the completion at a finite place, the local zeta integral, and its value at an unramified place, which is the local factor of the Hecke L-function. The Fourier transform of the characteristic function of the integers for an additive character with a given conductor.
- `Langlands/Tate/Poisson*.lean`: the Poisson summation formula on a full lattice of a real inner product space, with the covolume and the dual lattice, and the theta transformation formula.
- `Langlands/Statements/Smooth.lean`, `WeilDeligne.lean` and `GodementJacquet.lean`: smooth representations, Weil-Deligne representations and the standard L-factor of a representation of GL(n).
- `Langlands/Statements/LocalLanglands.lean`: `LocalLanglandsGL`, `LocalLanglandsGL2`, `LocalLanglandsSL2` and `JacquetLanglandsGL2`.
- `Langlands/Statements/Automorphic.lean` and `GlobalGL.lean`: cusp forms on GL(n) over the adeles, Hecke operators, Satake parameters, and `RamanujanGL`, `FunctorialityGL`, `SymPowerFunctoriality` and `BaseChangeCyclic`.
- `Langlands/Statements/HasseWeil.lean`, `FundamentalLemma.lean` and `PadicGalois.lean`: `HasseWeil`, `FundamentalLemma` and `FontaineMazurGL2Q`, and the vocabulary for the conjecture of Breuil and Mezard.

## v0.1.4 (2026-11-26)

### Added

- `Langlands/Bridge/NYLLGlobal.lean`: the proofs `Bridge.globalReciprocity` of `GlobalReciprocity` and `Bridge.globalExistence` of `GlobalExistence`, from the port of global class field theory. The Artin map is the geometric global norm residue map of the port.
- `Langlands/Tate/`: the archimedean local theory of Tate's thesis. It has the local zeta integrals at the real and the complex places, the Gamma factors, the Fourier transforms of the standard test functions, the local root numbers and the local functional equations, and the products over the infinite places of a number field.
- `docs/cross-check.md`: the comparison of three project statements with riemann-lean, and the reason why the cross-check package is not built.
- `scripts/L4LPackage.lean`: lean4lean on all the modules of the package in one environment.

### Changed

- The job lean4lean of the workflow trust runs `scripts/L4LPackage.lean`. The old command loaded one environment for each module in parallel, and the runner did not have sufficient memory.
- `Comparator/Challenge.lean` and `comparator.json` pin `Bridge.globalReciprocity`, `Bridge.globalExistence`, `Bridge.kroneckerWeber` and `heckeFunctionalEquationAt_rat`.

## v0.1.3 (2026-11-26)

### Added

- `Langlands/Hecke/Rational.lean`: the proof `heckeFunctionalEquationAt_rat` of Hecke's theorem for Q. A Hecke character of Q is a primitive Dirichlet character times a power of the idele norm. Its completed L-function is the completed Dirichlet L-function at a shifted point, and the functional equation, the root number and the poles come from Mathlib.

### Changed

- `Langlands/Statements/Hecke.lean`: the new statement `HeckeFunctionalEquationAt K` is Hecke's theorem for one number field. `HeckeFunctionalEquation` is now this statement for all number fields. The content of the statement is the same.

- `Langlands/Ported/NYLL`: the port of global class field theory from n-yamaguchi-0729/ClassFieldTheory. The port adds 114 files to the 692 files of the local theory. It has finite abelian global reciprocity, the existence theorem, the Artin map from the idele class group to the abelianized absolute Galois group, and the theorem of Kronecker and Weber. The changes for the Mathlib of the project pin are in `manifests/ported.yaml`.
- `Langlands/Bridge/NYLLGlobal.lean`: the proof `Bridge.kroneckerWeber` of the statement `KroneckerWeber`.

- `Langlands/Statements/Galois.lean`: Galois representations of modular forms with a character, Frobenius elements, inertia and complex conjugation in the absolute Galois group of Q, and the Artin L-function with the factors at the ramified primes. The statements are `EichlerShimuraDeligne`, `SerreModularityWeak`, `ArtinConjecture` and `ArtinOdd2Q`.
- `Langlands/Statements/Maass.lean`: the hyperbolic Laplacian, square integrable eigenfunctions on congruence quotients, Maass cusp forms with a character and the normalized Hecke operators. The statements are `SelbergEigenvalue` and `RamanujanMaass`.
- `Langlands/Fidelity/Galois.lean` and `Langlands/Fidelity/Maass.lean`: the fidelity checks of these statements. A Frobenius element and a complex conjugation exist, the Artin L-function of the trivial representation is the Euler product of the Dedekind zeta function, and the constant function shows that the conditions in `SelbergEigenvalue` and `RamanujanMaass` are necessary.

## v0.1.2 (2026-11-25)

### Added

- `Langlands/Statements/Hecke.lean`: Hecke characters of a number field, their conductor, the finite L-function as an Euler product, the archimedean Gamma factors and the completed L-function. The statement `HeckeFunctionalEquation` gives the meromorphic continuation and the functional equation of the completed L-function. The statement `ArchimedeanParametersExist` gives the archimedean parameters. Neither statement is proved yet.
- `Langlands/Statements/TorusInduced.lean` and `Langlands/Torus/Induced.lean`: the statement `LocalLanglandsTorusInduced` and its proof `localLanglandsTorusInduced`. For a finite extension L of K, the characters of the units of L correspond to the classes in the first cohomology of the Weil group of K with values in the coinduced module. The relation uses a local Artin map of L and Shapiro's isomorphism.
- `Langlands/WeilGroup/Embedding.lean`: the Weil group is Hausdorff, and `weilEquiv` is an isomorphism of topological groups from the Weil group of L to its image in the Weil group of K.

- `Langlands/WeilGroup/Restrict.lean`: for a finite extension L of K in the algebraic closure, the subgroup of the Weil group of K that fixes L is open, of finite index, and normal when L is normal over K. The map `weilHom` from the Weil group of L to the Weil group of K is injective and continuous, with this subgroup as its image. It multiplies the degree by the residue degree of L over K.

- `comparator.json`, `Comparator/Challenge.lean` and `Comparator/Solution.lean`: the challenge for `lake comparator`, with the pinned statements of `localReciprocityGL1`, `Bridge.localExistence` and `localLanglandsTorusSplit`. The trust workflow has a new job that runs `lake comparator --paranoid`. This is row Q4 of the trust report.

- `Langlands/Reciprocity/GL1.lean`: the proof `localReciprocityGL1` of the statement `LocalReciprocityGL1`. For each nonarchimedean local field there is exactly one local Artin map from the units of the field to the abelianized Weil group.
- `Langlands/Reciprocity/Exists.lean`: the existence `exists_isLocalArtinMap`. The map is the inverse of the injection `toGaloisAb` composed with the absolute local Artin map of the port. The image of the units is the image of the inertia subgroup, and the map is continuous in both directions.
- `Langlands/Reciprocity/Unique.lean`: the uniqueness `isLocalArtinMap_unique`, through the uniqueness of coherent families of finite Artin maps in the port.

- `Langlands/Cohomology/Shapiro.lean`: continuous one-cocycles, coboundaries and the first continuous cohomology group. Shapiro's lemma `Shapiro.shapiro` gives an isomorphism from the first cohomology of a coinduced module from an open subgroup H to the group of continuous homomorphisms on H.

- `Langlands/WeilGroup/Degree.lean`: the residue field of the algebraic closure is algebraically closed, and the Frobenius has infinite order. The degree map `WeilGroup.degree` from the Weil group to the integers has the inertia subgroup as its kernel, and it is surjective and locally constant. A geometric Frobenius has degree one.
- `Langlands/WeilGroup/Inertia.lean`: the checks F2 and F3 for the topology of the Weil group. The inertia subgroup is compact (`isCompact_inertia`). In the subspace topology from the absolute Galois group, the inertia subgroup is not open (`not_isOpen_inertia_induced`).

## v0.1.1 (2026-11-25)

### Added

- `Langlands/Statements/Torus.lean`: the statement `LocalLanglandsTorusSplit n`, the local Langlands correspondence for the split torus of rank n. The bijection is fixed: it is the composite with a local Artin map.
- `Langlands/Torus/Split.lean`: the proof `localLanglandsTorusSplit`, and `WeilGroup.Ab.lift`, which factors a continuous homomorphism to a commutative Hausdorff group through the abelianization of the Weil group.
- `Langlands/WeilGroup/Dense.lean`: the ring `integers K` is local, so each element of the absolute Galois group fixes its maximal ideal. The absolute Galois group is compact, also in characteristic p. The map to the Galois group of the residue field is continuous, surjective and open. The Weil group is dense in the absolute Galois group (`denseRange_toGalois`).
- `Langlands/WeilGroup/Ab.lean`: the map `toGaloisAb` from the abelianization of the Weil group to the abelianization of the absolute Galois group is continuous and injective, and `mem_range_toGaloisAb` gives its range. The topological abelianization of the Weil group is Hausdorff.

### Added

- `Langlands/Ported/NYLL/`: 341 more files from n-yamaguchi-0729/ClassFieldTheory at commit fc644f4. The port now has all the theorems of `ClassFieldTheory/Theorems/LocalClassFieldTheory`: local existence, the coherent family of local Artin maps, its uniqueness, the normalization at a uniformizer and profinite local reciprocity. The entry `nyll` of `manifests/ported.yaml` lists the changes for the Mathlib of the project pin.
- `Langlands/Bridge/NYLL.lean`: `localExistence` proves the statement `Langlands.LocalExistence`. The lemma `exists_intermediateField_of_finiteAbelianExtension` moves a finite abelian extension from the separable closure to the algebraic closure and keeps the norm group.

## v0.1.0 (2026-11-25)

### Changed

- This release closes milestone S0. It has the same Lean content as v0.0.2. The statements of S0 are in Langlands/Statements, and the bridges and the fidelity checks of S0 are complete.

## v0.0.2 (2026-11-25)

### Added

- `Langlands/Statements/Modularity.lean`: the statements `ModularityEllipticQ`, `ModularitySemistableQ`, `HasseWeilEllipticQ`, `RamanujanPeterssonHolomorphic` and `SatoTate`, with the structure `IsNormalizedEigenform` and the predicate `HasCMOverQ`. The coefficients of an elliptic curve come from `WeierstrassCurve.LFunction` in Mathlib, and the coefficients of a cusp form come from its $q$-expansion.

- `Langlands/Fidelity/ClassField.lean`: the positive instances `localExistence_top` and `kroneckerWeber_bot`, and the lemma `normGroup_bot`.
- `Langlands/Fidelity/Modularity.lean`: the total mass of the Sato-Tate measure, the CM curve $y^2 = x^3 - x$ and the curve $X_0(11)$ without CM.
- `Langlands/Ported/FormalConjectures/Wikipedia.lean`: the statements of modularity, Sato-Tate, Ramanujan-Petersson for $\tau$ and Hasse-Weil from formal-conjectures at commit 9097e2f, as `def ... : Prop`.
- `Langlands/Bridge/FormalConjectures.lean`: `HasseWeilEllipticQ` implies the Hasse-Weil statement of formal-conjectures over $\mathbb{Q}$. The statement `modularity_conjecture` of formal-conjectures is false as stated, because it reads the coefficients in the parameter $q_N$ and not in $q_1$ (`not_modularity_conjecture`).
- `manifests/ported.yaml`: the record of each ported source.
- `Langlands/Ported/NYLL/`: the port of finite abelian local reciprocity from n-yamaguchi-0729/ClassFieldTheory at commit fc644f4. These are the 327 files of the import closure of `ClassFieldTheory.finiteAbelianLocalReciprocity`, with the Mathlib names of v4.35.0. The entry `nyll` of `manifests/ported.yaml` lists the changes.
- `Langlands/Bridge/NYLL.lean`: `finiteAbelianLocalReciprocity` for a finite abelian extension in an algebraic closure, with the kernel given by `Langlands.normGroup`. This is the first theorem of the project with a full proof.
- `Langlands/Fidelity/ClassField.lean`: the checks F2 and F3 for the class field statements. `LocalReciprocityGL1` implies finite abelian local reciprocity (F2). Without the condition at a uniformizer the local reciprocity map is never unique, and this proof uses no hypothesis (F3). A map is a geometric Artin map if and only if its composite with inversion is an arithmetic Artin map (F3).
- `Langlands/Fidelity/Modularity.lean`: `ModularityEllipticQ` implies `ModularitySemistableQ` (F2), and `SatoTate` contradicts the variant with the uniform measure (F3).
- `Langlands/Fidelity/ClassField.lean` and `Langlands/Fidelity/Modularity.lean`: the positive instances `isArtinMap_bot` for `GlobalReciprocity` and `satoTate_full` for `SatoTate`.
- `Langlands/Bridge/FormalConjectures.lean`: the bridge `satoTate_conjecture_of_satoTate` from `SatoTate` to the Sato-Tate statement of formal-conjectures, with the hypotheses `ApAgree` and `HasseBound`, and the bridge `ramanujan_petersson_of_ramanujanPeterssonHolomorphic` from `RamanujanPeterssonHolomorphic` to the statement for $\tau$, with the hypothesis `DeltaIsEigenform`.
- `manifests/statements.sha256`: the hashes of the three files of `Langlands/Statements/`. The workflow `check` now compares them (check F7 of spec 06.3).

### Changed

- `formalization.yaml` uses the key `BLGHT11` for the paper of Barnet-Lamb, Geraghty, Harris and Taylor.
- `formalization.yaml` lists the sources of the modularity statements, the copied statements of formal-conjectures, the classification and the status of each main result.

## v0.0.1 (2026-11-25)

### Added

- The package `Langlands` on Lean v4.35.0 and Mathlib v4.35.0.
- The workflows `build`, `check`, `trust` and `scorecard`, and the scripts `Export.lean`, `Decls.lean`, `axioms.py`, `scan.sh` and `style.py`.
- `Langlands/Statements/Basic.lean`: the Weil group `WeilGroup K` of a nonarchimedean local field as a subgroup of the absolute Galois group, its topology, the inertia subgroup, `IsGeometricFrobenius`, the abelianization `WeilGroup.Ab` and the restriction to a finite abelian extension. The file has no `sorry`.
- `Langlands/Statements/ClassField.lean`: the statements `LocalReciprocityGL1`, `LocalExistence`, `GlobalReciprocity`, `GlobalExistence` and `KroneckerWeber`, with the structures `IsLocalArtinMap` and `IsArtinMap` in the geometric normalization.
