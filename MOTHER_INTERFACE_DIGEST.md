# Mother Interface Digest

Snapshot: `main` after PR #20, commit `2c52d7f` (2026-07-06).

Audience: `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

This digest lists the small, source-honest pieces this satellite can provide
to the mother repo. It is an interface and benchmark digest only. It makes no
claim about 4D Yang-Mills, mass gap, OS/Wightman reconstruction, source
construction, `hRpoly`, or the continuum theory.

## Recommended Imports

For the stable contract surface:

```lean
import Interfaces
```

For the complete 2D sandbox barrel, including the Witten-zeta benchmark:

```lean
import Lean2dYangMills
```

Do not import `Lean2dYangMills/Frontier/*` from the mother repo. Frontier
branches may contain deliberate `sorry` statements and are tracked in
`HYPOTHESIS_FRONTIER.md`.

## Stable Contract

Implemented in `Lean2dYangMills/Interfaces.lean`, re-exported by root
`Interfaces.lean`.

Heat-kernel/character interface:

```lean
abbrev Lean2dYangMills.SU2 : Type
structure Lean2dYangMills.CharacterTable (G : Type u)
def Lean2dYangMills.heatKernelTerm
def Lean2dYangMills.heatKernelCharacterSeries
structure Lean2dYangMills.HeatKernelCharacterPackage (G : Type u) [Group G]
theorem Lean2dYangMills.heatKernel_character_series_converges
theorem Lean2dYangMills.heatKernel_character_series_eq
theorem Lean2dYangMills.heatKernel_conj_invariant
def Lean2dYangMills.heatKernel_semigroup_statement
```

Finite lattice/Migdal interface:

```lean
structure Lean2dYangMills.FiniteLatticeTheory (G : Type u) [Group G]
structure Lean2dYangMills.PlaquetteSubdivision
structure Lean2dYangMills.MigdalSelfSimilarityPackage
theorem Lean2dYangMills.migdal_self_similarity
```

Plane-loop area-law interface:

```lean
structure Lean2dYangMills.PlaneSimpleLoopTheory
def Lean2dYangMills.areaLawValue
theorem Lean2dYangMills.areaLawValue_zero_area
structure Lean2dYangMills.ExactAreaLawPackage
theorem Lean2dYangMills.simpleLoop_areaLaw_exact
theorem Lean2dYangMills.simpleLoop_stringTension_nonnegative
```

Continuum and Witten-zeta interfaces:

```lean
structure Lean2dYangMills.ContinuumLimitPackage
theorem Lean2dYangMills.continuum_limit_statement
structure Lean2dYangMills.WittenZetaData
def Lean2dYangMills.wittenZetaTerm
def Lean2dYangMills.wittenZetaSeries
def Lean2dYangMills.genusZetaArgument
structure Lean2dYangMills.WittenZetaPackage
structure Lean2dYangMills.WittenZetaSurfacePackage
theorem Lean2dYangMills.wittenZeta_converges
theorem Lean2dYangMills.wittenZeta_eq_tsum
theorem Lean2dYangMills.surfacePartitionFunction_eq_wittenZeta
```

These contract theorems project explicit fields from packages. Supplying a
package is supplying the hard mathematical input; this repo does not hide
those inputs as axioms.

## Unconditional Benchmarks On Main

Witten-zeta/Riemann-zeta bridge, in `Lean2dYangMills/WittenZetaSU2.lean`:

```lean
def Lean2dYangMills.su2WittenZetaData
theorem Lean2dYangMills.summable_su2WittenZetaTerm
def Lean2dYangMills.su2WittenZetaPackage
theorem Lean2dYangMills.su2_wittenZetaSeries_eq_riemannZeta
theorem Lean2dYangMills.genusZetaArgument_re
theorem Lean2dYangMills.one_lt_genusZetaArgument_re
def Lean2dYangMills.su2ZeroAreaSurfaceModel
theorem Lean2dYangMills.su2ZeroArea_partition_eq_riemannZeta
```

Interpretation: for the SU(2) representation dimensions `1, 2, 3, ...`, the
Witten-zeta series is identified with Mathlib's `riemannZeta` on `1 < s.re`.
The zero-area genus model is a consumer test where the partition function is
defined as the representation-dimension series. This does not close the
positive-area analytic surface Yang-Mills partition function.

M0 convergence engine, in `Lean2dYangMills/ConvergenceEngine.lean`:

```lean
theorem Lean2dYangMills.summable_pow_mul_exp_neg
theorem Lean2dYangMills.summable_pow_mul_exp_neg_casimir
```

Trivial heat-kernel and area-law consumer tests, current through PR #20, in
`Lean2dYangMills/TrivialModel.lean`:

```lean
def Lean2dYangMills.trivialHeatKernelPackage
theorem Lean2dYangMills.trivialHeatKernelPackage_semigroup
theorem Lean2dYangMills.trivialHeatKernelCharacterSeries_converges
theorem Lean2dYangMills.trivialHeatKernelCharacterSeries_eq_one
theorem Lean2dYangMills.trivialHeatKernel_conj_invariant
def Lean2dYangMills.trivialPlaneSimpleLoopTheory
def Lean2dYangMills.trivialExactAreaLawPackage
theorem Lean2dYangMills.trivialSimpleLoop_areaLaw_exact
theorem Lean2dYangMills.trivialSimpleLoop_stringTension_nonnegative
theorem Lean2dYangMills.trivialAreaLawValue_zero_area
```

Interpretation: these are zero-content interface oracles over `PUnit`. They
show that `HeatKernelCharacterPackage` and `ExactAreaLawPackage` can be
consumed with all fields discharged in a one-point model. They do not prove
the SU(2) heat kernel, a physical plane-loop area law, or any continuum
statement. `trivialHeatKernelCharacterSeries_eq_one` is a consumer check for
the public `heatKernel_character_series_eq` wrapper specialized to the
trivial package. `trivialHeatKernelCharacterSeries_converges` is the matching
consumer check for the public `heatKernel_character_series_converges` wrapper.
`trivialHeatKernel_conj_invariant` is the matching consumer check for the
public `heatKernel_conj_invariant` wrapper.
`trivialSimpleLoop_stringTension_nonnegative` is the matching consumer check
for the public `simpleLoop_stringTension_nonnegative` wrapper over the
trivial exact-area-law package.
`trivialAreaLawValue_zero_area` is a consumer check for the public
`areaLawValue_zero_area` API lemma.

Area-law API normalization, in `Lean2dYangMills/Interfaces.lean`:

```lean
theorem Lean2dYangMills.areaLawValue_zero_area
```

Interpretation: this is a definitional consumer lemma for the public
`areaLawValue` function under the explicit hypothesis `T.area C = 0`. It does
not supply an `ExactAreaLawPackage` and does not prove any nontrivial Wilson
expectation identity.

## Explicitly Open Inputs

Still carried as hypotheses for real gauge models:

- SU(2) heat-kernel character expansion equality and semigroup.
- Migdal plaquette-subdivision self-similarity.
- Positive-area surface partition functions.
- Exact simple-loop area law for nontrivial or physical loop models.
- Continuum limit statements.

Current frontier branch `frontier/M0-su2` records the next M0 targets:

- `su2CharacterChebyshev_one`.
- `abs_su2CharacterChebyshev_le`.
- `summable_su2HeatKernelTerm`.
- `exists_su2HeatKernelPackage`.

The next useful small theorem is the Weyl/spectral bound behind
`abs_su2CharacterChebyshev_le`.

