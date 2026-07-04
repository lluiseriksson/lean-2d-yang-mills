# Public Interfaces

The parent repository imports:

```lean
import Interfaces
```

Re-exported by `Interfaces.lean` and implemented in `Lean2dYangMills/Interfaces.lean`.

## Concrete Group Alias

```lean
abbrev Lean2dYangMills.SU2 : Type
abbrev Lean2dYangMills.SU2CharacterTable : Type
abbrev Lean2dYangMills.SU2HeatKernelPackage : Type
```

`SU2` is `Matrix.specialUnitaryGroup (Fin 2) Complex` at the pinned Mathlib commit.

## Heat Kernel And Characters

```lean
structure Lean2dYangMills.CharacterTable (G : Type u)

def Lean2dYangMills.heatKernelTerm
def Lean2dYangMills.heatKernelCharacterSeries

structure Lean2dYangMills.HeatKernelCharacterPackage (G : Type u) [Group G]

theorem Lean2dYangMills.heatKernel_character_series_converges
theorem Lean2dYangMills.heatKernel_character_series_eq
theorem Lean2dYangMills.heatKernel_conj_invariant
def Lean2dYangMills.heatKernel_semigroup_statement
```

`CharacterTable.heatWeight t lam` is the explicit data slot for the intended factor
`exp(-t * C2(lam))`. This keeps the public interface light until the Casimir/heat-kernel layer is proved.

## Migdal Self-Similarity

```lean
structure Lean2dYangMills.FiniteLatticeTheory (G : Type u) [Group G]
structure Lean2dYangMills.PlaquetteSubdivision
structure Lean2dYangMills.MigdalSelfSimilarityPackage

theorem Lean2dYangMills.migdal_self_similarity
```

## Exact Area Law

```lean
structure Lean2dYangMills.PlaneSimpleLoopTheory

def Lean2dYangMills.areaLawValue
theorem Lean2dYangMills.areaLawValue_zero_area

structure Lean2dYangMills.ExactAreaLawPackage

theorem Lean2dYangMills.simpleLoop_areaLaw_exact
theorem Lean2dYangMills.simpleLoop_stringTension_nonnegative
```

## Continuum Limit

```lean
structure Lean2dYangMills.ContinuumLimitPackage

theorem Lean2dYangMills.continuum_limit_statement
```

## Witten Zeta And Surfaces

```lean
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

`WittenZetaData.zetaTerm s lam` is the explicit data slot for the intended factor
`dim(lam)^(-s)`.

## Breaking Changes

Any signature change in `Interfaces.lean` is breaking and must be announced in this file and in the PR description.
