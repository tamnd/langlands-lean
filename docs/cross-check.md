# Cross-check with riemann-lean

This file is the S2 item "in the cross-check package, the same statements from riemann-lean (05.6), or a written reason why not". It covers the map nodes `LG-cross-rl-cft` and `LG-cross-rl-tate` (spec 04) and the riemann-lean rows of the tables in spec 05.6 and 06.4.

The result has two parts. First, a comparison of three riemann-lean results with the project statements, in mathematical terms. Second, the reasons why the project does not build the cross-check package now.

## The source that was read

| Item | Value |
|---|---|
| Repository | `tamnd/riemann-lean`, a copy of the release of 2026-11-20 by Levent Alpöge |
| Commit | `54f24d40f22dda515b978dfacfb3164991d30317` (2026-11-25) |
| Lean | v4.33.1 (`lean/lean-toolchain`) |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` (`lean/lake-manifest.json`) |
| Licence of the Lean files | none; `NOTICE.md` says that the copyright stays with the author |

I read the files with `grep` and a text reader only. I did not build riemann-lean and I did not run a script from it. This file does not copy Lean code or a Lean statement from riemann-lean. It names declarations and files, and it describes their content in my own words.

All riemann-lean paths below are relative to `lean/src/GroundTheory/GlobalFields/`. A path such as `General.lean:190` gives the line of the declaration.

## Summary

| Project statement | riemann-lean result | Relation | Bridge work |
|---|---|---|---|
| `Langlands.GlobalReciprocity` | `reciprocityMap` and its Frobenius lemma | riemann-lean is stronger. The Frobenius normalization is the opposite one. | Take the pointwise inverse of the map. Then match the hypotheses. Short. |
| `Langlands.GlobalExistence` | `ker_reciprocityMap` with the existence theorem | the same theorem, with norm groups in riemann-lean | Move the class field into the fixed algebraic closure. Then use the bridge above. Short. |
| `Langlands.HeckeFunctionalEquation` | `completedLFunction_eq_rootNumber_mul` | riemann-lean covers only unitary characters. Its completed L-function has an extra factor. The two root numbers are equal. | Reduce to unitary characters, change the normalization, prove $\lvert W \rvert = 1$, and prove meromorphy. Medium. |

I found no difference of meaning. The normalization of the reciprocity map is the opposite one, and this is expected (risk 3 of 06.5). The project chose the geometric normalization on purpose, and riemann-lean uses the arithmetic one.

## 1. Global reciprocity

### What riemann-lean proves

Let $K$ be a number field. Let $L$ be a number field with a $K$-algebra structure, such that $L/K$ is Galois with a commutative Galois group. riemann-lean defines a homomorphism $\mathrm{rec}_{L/K} : C_K \to \mathrm{Gal}(L/K)$ from the idele class group of $K$. This is `reciprocityMap` (`GlobalReciprocity/General.lean:190`).

The map is the product of local symbols over all places. At a finite place it is the local norm residue symbol of $K_v$. At an infinite place it is the symbol of the real or complex completion. The product is first a map on ideles (`ideleSymbol`, `NormResidueSymbol/RangeIdeleNormLeKerIdeleSymbol.lean:21`). riemann-lean proves that it is trivial on the principal ideles, so it factors through $C_K$.

riemann-lean proves these facts about the map:

- it is continuous (`continuous_reciprocityMap`, `General.lean:198`);
- it is surjective (`reciprocityMap_surjective`, `General.lean:230`);
- its kernel is the image of the norm map $C_L \to C_K$ (`ker_reciprocityMap`, `General.lean:201`);
- it gives an isomorphism $C_K / N_{L/K} C_L \cong \mathrm{Gal}(L/K)$ (`reciprocityMapEquiv`, `General.lean:236`);
- at a finite place $v$ of $K$ and a prime $w$ of $L$ over $v$ with ramification index $1$, it sends the idele that is a uniformizer of $K_v$ at $v$ and $1$ elsewhere to the arithmetic Frobenius at $w$ (`ideleSymbol_finiteEmbedding_eq_arithFrobAt`, `GlobalReciprocity/Frobenius.lean:96`, from `localSymbol_eq_arithFrobAt` at line 80).

### The definitions it depends on

- The idele group (`IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean:12`) is the group of units of the adele ring of Mathlib, with the topology of units.
- The idele class group (same file, line 65) is the quotient of the idele group by the image of $K^\times$ (`diagonal`, line 51), with the quotient topology. This is the same group, the same subgroup and the same topology as `IdeleClassGroup (𝓞 K) K` of Mathlib at the project pin. riemann-lean has its own copy because its Mathlib pin is older.
- The embedding of $K_v^\times$ into the ideles (`finiteEmbedding`, same file, line 140) puts an element at $v$ and $1$ at every other place. This is `IdeleGroup.ofAdicCompletion` of Mathlib.
- The Galois group is the group of $K$-algebra automorphisms of the abstract field $L$.
- The Frobenius is `arithFrobAt` of Mathlib (`Mathlib/RingTheory/Frobenius.lean`). I found no other definition of it in `GroundTheory/`.
- A uniformizer is an element of $K_v$ of order $1$ for the normalized valuation (`ord`, `lean/src/GroundTheory/LocalFields/UnitsBasic.lean:144`).
- The norm on ideles (`ideleNorm`, `IdeleGroups/IdeleNorms/BaseChange.lean:170`) is the algebra norm of the adele ring of $L$ over the adele ring of $K$. The norm on idele classes (`ideleClassNorm`, line 207) is the map that it induces.

### Comparison with the project statement

`Langlands.IsArtinMap` in `Langlands/Statements/ClassField.lean` asks for three properties of a homomorphism $C_K \to \mathrm{Gal}(L/K)$. It is continuous. It is surjective. At each prime $w$ of $L$ that is unramified over a finite place $v$ of $K$, the inverse of the image of a uniformizer of $K_v$ is an arithmetic Frobenius at $w$. So the project map sends a uniformizer to a geometric Frobenius.

The riemann-lean map sends a uniformizer to the arithmetic Frobenius. The two normalizations differ by an inverse. $\mathrm{Gal}(L/K)$ is commutative, so $x \mapsto \mathrm{rec}_{L/K}(x)^{-1}$ is a homomorphism. It is continuous and surjective, and it has the same kernel. It sends a uniformizer to a geometric Frobenius.

The riemann-lean result is stronger than `GlobalReciprocity` in two ways. It identifies the kernel with the norm group. Its map is the product of the local symbols, so the compatibility with local class field theory is part of the construction. The project states this compatibility only at S2.

The hypotheses differ in these points:

- riemann-lean takes any number field $L$ with a $K$-algebra structure. The project takes an intermediate field of a fixed algebraic closure $\overline{K}$. The project case is a special case.
- riemann-lean asks for Galois with a commutative Galois group. The project asks for `IsAbelianGalois`. These are the same.
- riemann-lean asks for ramification index $1$ at a height one prime of $\mathcal{O}_L$. The project asks for `Algebra.IsUnramifiedAt` at a maximal ideal of $\mathcal{O}_L$. Unramified implies ramification index $1$.
- riemann-lean asks for order $1$. The project asks for `IsUniformizer`, an irreducible element of $\mathcal{O}_{K_v}$. These are the same. The project already proves one direction in `valued_eq_exp_neg_one_of_isUniformizer` (`Langlands/Bridge/NYLLGlobal.lean`).

### What a bridge needs

1. Give $L$ the `NumberField` instance, and get Galois and commutativity from `IsAbelianGalois`.
2. Show that the riemann-lean idele class group and the Mathlib one are equal. I expect that this holds by definition, after the two pins agree.
3. Define the Artin map as the pointwise inverse of `reciprocityMap`.
4. Take continuity and surjectivity from riemann-lean.
5. For the Frobenius condition, turn the maximal ideal $w$ into a height one prime, get ramification index $1$ from unramified, get order $1$ from `IsUniformizer`, and match the two embeddings of $K_v^\times$. Then the Mathlib lemma that `arithFrobAt` is an arithmetic Frobenius closes the goal.

### Result

The riemann-lean result implies `GlobalReciprocity`, after an inverse. This confirms the relation in 05.6. The same check for the NYLL port uses the geometric map of NYLL with no change (`Langlands/Bridge/NYLLGlobal.lean`). So the two external sources agree with the project normalization through different maps, and this is consistent: NYLL has both maps, and riemann-lean has the arithmetic one.

## 2. The kernel and the existence theorem

### What riemann-lean proves

`ker_reciprocityMap` (`General.lean:201`) says that the kernel of $\mathrm{rec}_{L/K}$ is the image of the norm map $C_L \to C_K$.

`exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex` (`ExistenceTheorem/ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini.lean:103`) is the existence theorem. Let $N$ be an open subgroup of finite index of $C_K$. Then there is a number field $L$, in the same universe as $K$, abelian Galois over $K$, such that the image of the norm map $C_L \to C_K$ is $N$. The proof goes through a cyclotomic extension and Kummer theory.

### Comparison with the project statement

`Langlands.GlobalExistence` says this. Let $U$ be an open subgroup of finite index of $C_K$. Then there is an intermediate field $L$ of $\overline{K}$, finite abelian over $K$, and a map with the properties of `IsArtinMap`, whose kernel is $U$.

The two riemann-lean results together give the project statement. Take $L$ from the existence theorem. The kernel of $\mathrm{rec}_{L/K}$ is the norm group, which is $N$. The pointwise inverse has the same kernel. The riemann-lean form is stronger, because it names the kernel as a norm group. The project statement does not mention global norms.

The one difference is the model of $L$. riemann-lean gives an abstract field. The project needs a subfield of $\overline{K}$.

### What a bridge needs

1. Embed the abstract $L$ into $\overline{K}$ and take the image $L'$. There is a $K$-isomorphism $L \cong L'$.
2. Show that $L$ and $L'$ have the same norm group in $C_K$. The riemann-lean norm goes through the base change of adeles, so this step needs the compatibility of that base change with an isomorphism. The NYLL bridge has the same step ("isomorphic extensions have the same norm group").
3. Use the bridge of section 1 for $L'$.

### Result

The riemann-lean results imply `GlobalExistence`. The statements have the same content.

## 3. Tate's thesis

### What riemann-lean proves

`completedLFunction_eq_rootNumber_mul` (`TateThesis/HeckeTheoremFE.lean:70`) is the functional equation. Let $\chi$ be a Hecke character of $K$ in the riemann-lean sense and let $s$ be a complex number. Then the completed L-function of $\chi$ at $s$ is the root number of $\chi$ times the completed L-function of $\chi^{-1}$ at $1 - s$. There is one hypothesis. If $\chi = \lVert \cdot \rVert^{i\tau}$ for a real $\tau$, then $s$ is not $-i\tau$ and not $1 - i\tau$.

Other results in the same files complete the picture:

- the completed L-function is entire if $\chi$ is not of the form $\lVert \cdot \rVert^{i\tau}$ (`TateThesis/HeckeTheorem.lean:27`);
- if $\chi = \lVert \cdot \rVert^{i\tau}$, it is differentiable away from $-i\tau$ and $1 - i\tau$ (line 68), it has simple poles there (lines 72 and 88), and the residue at $1 - i\tau$ is not zero (line 102);
- $W(\chi) W(\chi^{-1}) = 1$ (`rootNumber_mul_rootNumber_inv`, `HeckeTheoremFE.lean:104`).

### The definitions it depends on

- A Hecke character (`TateThesis/HeckeChar.lean:15`) is a continuous homomorphism from $C_K$ to the unit circle. So riemann-lean covers only unitary characters.
- The conductor (`HeckeChar.lean:184`) is $\prod_v \mathfrak{p}_v^{a_v}$, where $a_v$ (`conductorExponentAt`, `TateThesis/Conductor.lean:179`) is the least $m$ such that $\chi_v$ is trivial on the $m$-th unit group. This is the definition of the project.
- The finite L-function (`TateThesis/HeckeLFunction.lean:363`) is a Dirichlet series over the nonzero integral ideals. The coefficient of an ideal prime to the conductor is the value of the ideal character, and the other coefficients are $0$ (line 273). On $\mathrm{Re}(s) > 1$ it is the Euler product over the primes that do not divide the conductor (`LFunction_hasProd`, line 443). The value of the ideal character at a prime $\mathfrak{p}_v$ is $\chi_v(\varpi_v)$ for a uniformizer $\varpi_v$ (`HeckeChar.lean:261`). So the local factor is $(1 - \chi_v(\varpi_v) N(v)^{-s})^{-1}$, which is the convention of the project. It is not the inverse convention.
- The archimedean parameters (`TateThesis/EulerFactorsArch.lean:193` and line 203) are, at each infinite place $w$, an integer $n_w$ and a real $\tau_w$ with $\chi_w(x) = (\iota(x)/\lvert\iota(x)\rvert)^{n_w} \lvert\iota(x)\rvert^{m_w i \tau_w}$, where $m_w$ is $1$ or $2$. At a real place $n_w$ is $0$ or $1$. riemann-lean proves that they exist and are unique for unitary characters (line 139, and `TateThesis/ArchCharsUnitary.lean:59`). This is `Langlands.HeckeCharacter.IsArchimedeanParameter` with $t_w = i\tau_w$.
- The Gamma factor (`TateThesis/EulerFactors.lean:22`, `EulerFactorsArch.lean:221`) is the product of $\Gamma_\mathbb{R}(s + i\tau_w + n_w)$ over the real places and $\Gamma_\mathbb{C}(s + i\tau_w + \lvert n_w \rvert / 2)$ over the complex places. This is `Langlands.gammaFactor` with $t_w = i\tau_w$.
- The number $A(\chi) = \lvert d_K \rvert N(\mathfrak{f}_\chi)$ (`TateThesis/HeckeTheoremScaling.lean:45`) satisfies $A(\chi^{-1}) = A(\chi)$ (line 51).
- The completed L-function (`HeckeTheoremFE.lean:19`) is defined on all of $\mathbb{C}$. It is $A(\chi)^{s/2}$ times $\pi^{-r_2}$ times the continued Tate zeta integral of a test function that depends on $\chi$ (`tateZeta`, `TateThesis/TateMain.lean:334`). On $\mathrm{Re}(s) > 1$ it is $A(\chi)^{s/2} \, \Gamma(s, \chi) \, L(s, \chi)$ (`completedLFunction_eq`, `HeckeTheoremFE.lean:27`).
- The root number (`HeckeTheoremFE.lean:49`) is an explicit expression: a Fourier constant at a finite idele of norm ideal $\mathfrak{f}_\chi \mathfrak{d}_K$, times the value of $\chi$ at that idele, times $A(\chi)^{1/2}$.
- The idele norm (`ideleModule`, `IdeleGroups/IdeleNorms.lean:88`) is the product of the local normalized absolute values. The project's `ideleNorm` uses the norm of Mathlib on the adele ring, which is also the product of the local norms (`AdeleRing.norm_apply_of_isUnit` in Mathlib).

### Comparison with the project statement

`Langlands.HeckeFunctionalEquationAt K` in `Langlands/Statements/Hecke.lean` takes any continuous homomorphism $\chi : C_K \to \mathbb{C}^\times$, with archimedean parameters $(n, t)$ for $\chi$ and $(n', t')$ for $\chi^{-1}$. It asks for a real $\sigma$ with $\lvert \chi \rvert = \lVert \cdot \rVert^\sigma$, meromorphic functions $\Lambda$ and $\Lambda'$ that agree with $\Gamma \cdot L$ for $\chi$ and $\chi^{-1}$ on the half planes of convergence, and a number $W$ with $\lvert W \rvert = 1$, such that $\Lambda(s) = W (\lvert d_K \rvert N(\mathfrak{f}_\chi))^{1/2 - s - \sigma} \Lambda'(1 - s)$ for every $s$. It also asks that $\Lambda$ is entire, or that $\chi = \lVert \cdot \rVert^{s_0}$ and $\Lambda$ has simple poles at $-s_0$ and $1 - s_0$ only.

The points of comparison:

- **Scope.** riemann-lean covers only unitary characters. This is the case $\sigma = 0$ of the project statement. So on this point the riemann-lean result is weaker. Every $\chi$ is $\chi_0 \lVert \cdot \rVert^\sigma$ with $\chi_0$ unitary, and then $L(s, \chi) = L(s + \sigma, \chi_0)$ and the Gamma factors shift in the same way. The exponent $1/2 - s - \sigma$ of the project statement is the result of this shift. So the general case follows from the unitary case.
- **Normalization of $\Lambda$.** The riemann-lean $\Lambda$ has the extra factor $A(\chi)^{s/2}$. Write $\Lambda_{RL}(s, \chi) = A^{s/2} \Lambda_P(s, \chi)$ and use $A(\chi^{-1}) = A(\chi)$. Then the riemann-lean equation becomes $\Lambda_P(s, \chi) = W_{RL}(\chi) A^{1/2 - s} \Lambda_P(1 - s, \chi^{-1})$. This is the project equation with $\sigma = 0$ and $W = W_{RL}(\chi)$.
- **Root number.** By the line above, the two root numbers are equal for unitary $\chi$. This confirms the relation in 05.6. For general $\chi$, the project $W$ is the riemann-lean root number of $\chi_0$.
- **$\lvert W \rvert = 1$.** The project asks for it. riemann-lean proves $W(\chi) W(\chi^{-1}) = 1$. I did not find a proof of $\lvert W(\chi) \rvert = 1$ in `GroundTheory/GlobalFields/TateThesis`. For unitary $\chi$, $\chi^{-1} = \bar\chi$. So $\lvert W \rvert = 1$ follows from $W(\bar\chi) = \overline{W(\chi)}$. That follows from the functional equation and the symmetry $\Lambda(\bar s, \bar\chi) = \overline{\Lambda(s, \chi)}$. `TateThesis/HeckeTheoremConj.lean` has the Gamma part of this symmetry.
- **Analytic continuation.** riemann-lean defines $\Lambda$ everywhere and proves that it is entire, or differentiable away from two simple poles. The project asks for a meromorphic function that agrees with the Euler product on a half plane. A bridge must prove meromorphy and the order $-1$ at the poles from the riemann-lean limits.
- **Values at the poles.** riemann-lean excludes the two poles from the equation. The project asks for the equation at every $s$ and lets the values at the poles be free. The poles of $\Lambda$ at $-s_0$ and $1 - s_0$ pair with the poles of $\Lambda'$ at $1 + s_0$ and $s_0$ under $s \mapsto 1 - s$. So a bridge can choose the values at the poles to make the equation hold.
- **The L-function.** The project L-function is a product over all finite places, with factor $1$ at the ramified places. The riemann-lean L-function is a Dirichlet series with an Euler product on $\mathrm{Re}(s) > 1$. A bridge must match the two products. It must also show that `IsUnramifiedAt` means "$v$ does not divide the conductor" (`not_dvd_conductor_iff`, `HeckeChar.lean:197`), that the project uniformizer from $K$ has order $1$ in $K_v$, and that the two conductors are equal.
- **Archimedean parameters.** The project takes them as hypotheses. riemann-lean chooses them. A bridge needs their uniqueness to show that the two Gamma factors are equal, also after the shift by $\sigma$.
- **Idele norm.** A bridge must show that `ideleModule` of riemann-lean and the Mathlib norm are equal on ideles. Both are products of local norms. The check must confirm that the two Mathlib pins use the same local norm on $K_v$.

### Result

The riemann-lean result implies `HeckeFunctionalEquationAt K` for every number field $K$, after the work in the list above. The largest parts are the reduction to unitary characters, the proof of $\lvert W \rvert = 1$, and meromorphy. The root numbers are equal. The riemann-lean result is weaker in scope (unitary characters only). It is stronger in content, because it gives the root number as an explicit expression and gives the continuation as a function.

The project proves `HeckeFunctionalEquationAt ℚ` in `Langlands/Hecke/Rational.lean`. It proves the statement for every number field $K$ as `Langlands.heckeFunctionalEquation` in `Langlands/Tate/HeckeShiftRamifiedAssembly.lean`. A bridge in the cross-check package would not change this. Langlands does not import that package (05.6), so a bridge there is a test of meaning and not a proof of the project.

## Why the cross-check package is not built

The decision is: the project does not build the package `langlands-crosscheck` for riemann-lean now. This file replaces it. This differs from the plan in 05.6 and Q-07, which say "built but not distributed". The reasons follow.

1. **No licence.** The Lean files of riemann-lean have no licence. `NOTICE.md` of the copy says that the copyright stays with the author and that the copy grants no licence. Spec 05.3 lets the project read, cite and compare names. It does not let the project copy a line into a repository of the project.
2. **The bridge rule needs a copy.** Spec 06.4 says that each external statement is copied word for word into the bridge file, with its source commit. This copy is what makes an upstream change show as a failed comparison. For riemann-lean the copy would be in the cross-check package, and the package is a repository of the project. So a bridge that follows 06.4 breaks 05.3. A bridge without the copy loses the check that 06.4 asks for.
3. **The build makes copies.** A build of the package compiles the riemann-lean files and keeps the compiled files in the cache of the weekly run. The licence would have to allow this too.
4. **Two toolchains.** riemann-lean is on Lean v4.33.1 with Mathlib `0df444a3`. The project is on v4.35.0. A Lake package has one toolchain. A package on v4.33.1 cannot import `Langlands`, so it would need a second copy of the project statements on the old pin. That copy can drift from the real statements. To move riemann-lean to v4.35.0 is to modify it, which needs a licence.
5. **Size.** riemann-lean has 175,187 files and 17,374,215 lines (05.3). Each of the files read here imports all of Mathlib. Spec 05.4 says that a dependency of this size makes CI impossible on a normal runner. I did not measure the import closure of the three results.

Reasons 1 to 3 decide the matter. Reasons 4 and 5 are costs that a licence would let the project solve with the porting rule of 05.4.

## What will change the decision

A licence from the author will change the decision. This is option (a) of question Q-07 in spec 16: ask for Apache-2.0 for `GroundTheory/` and `ReciprocityTheory/`. With such a licence, the project will do these steps:

1. Copy the three statements word for word into bridge files, with the commit above, as 06.4 asks.
2. Prove the bridges of sections 1 to 3, in the cross-check package on v4.33.1, or after a port to v4.35.0 by the rules of 05.4.
3. Record the result in the fidelity battery (F2 of 06.3).

Until then, this file is the cross-check. If the riemann-lean copy moves to a new commit, the comparison above must be done again for the new commit.
