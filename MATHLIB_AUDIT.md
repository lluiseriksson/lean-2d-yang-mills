# Mathlib Audit

Date: 2026-07-03

Pinned environment copied from the parent repository:

- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`

Audit method: cloned the pinned Mathlib commit locally and searched for the required primitives before adding Lean code.

## Reusable In Mathlib

- `Matrix.specialUnitaryGroup` exists in `Mathlib.LinearAlgebra.UnitaryGroup`. It is an algebraic `Submonoid` of matrices satisfying unitarity and determinant one, with a `Group` instance for the subtype. This is enough to name `SU2 := Matrix.specialUnitaryGroup (Fin 2) Complex`.
- Matrix topology support exists in `Mathlib.Topology.Instances.Matrix`, including continuity of trace and determinant.
- Haar measure exists abstractly in `Mathlib.MeasureTheory.Measure.Haar.Basic`, including `haarMeasure`, `haar`, and `IsHaarMeasure` infrastructure for locally compact Hausdorff topological groups.
- Finite-dimensional representation and character infrastructure exists in `Mathlib.RepresentationTheory.FDRep` and `Mathlib.RepresentationTheory.Character`. In particular, Mathlib has `FDRep.character` and finite-group character orthogonality.
- Infinite sums and summability tools exist in `Mathlib.Analysis.Normed.Group.InfiniteSum` and related files.
- Complex powers and zeta infrastructure exist in `Mathlib.Analysis.SpecialFunctions.Pow.Real` and `Mathlib.NumberTheory.LSeries.RiemannZeta`.

## Not Found In Mathlib

- No formal Peter-Weyl theorem for compact Lie groups.
- No classification of irreducible representations of `SU(2)` by highest weight, no `SU2` character table, and no Casimir eigenvalue package.
- No compact Lie group heat kernel with character expansion
  `K_t(g) = sum_lambda dim(lambda) * chi_lambda(g) * exp(-t * C2(lambda))`.
- No formal Migdal heat-kernel subdivision/self-similarity theorem for finite lattices.
- No formal 2D Yang-Mills continuum construction in the sense of Driver, Levy, or Sengupta.
- No formal exact Wilson loop area law for simple planar loops in 2D Yang-Mills.
- No formal Witten zeta function for compact Lie groups and no theorem identifying it with the genus-`g` partition function.

## Consequence For This Repo

The first `main` layer must be conditional. It may define:

- the concrete type alias `SU2`;
- abstract character-table and heat-kernel packages;
- finite lattice and Migdal self-similarity interfaces;
- exact area-law packages;
- continuum-limit packages;
- Witten-zeta and surface-partition packages.

The first interface keeps the intended factors `exp(-t * C2(lambda))` and `dim(lambda)^(-s)` as explicit data fields (`heatWeight`, `zetaTerm`) to avoid importing unproved analytic infrastructure.

But it must not assert any of the hard analytic statements unconditionally. Those statements are represented as fields of explicit structures and projected by theorem wrappers.

## Upstream Candidates

Potential Mathlib upstream work, once proved generally:

- normalized Haar probability measure for compact groups as a convenient API layer;
- compact group character tables and class functions;
- Peter-Weyl statements for compact Hausdorff groups or compact Lie groups;
- `SU(2)` irreducible representation classification and character/Casimir formulae;
- Witten zeta definitions and convergence criteria for compact semisimple Lie groups.
