# Hypothesis Frontier

Date: 2026-07-13

## Supersession note: concrete SU(2) closure

The historical ledger below records how the project reached the Haar/canonical
measure bridge.  Its statements that general Weyl consumers, concrete
convolution, M1, or the simple-loop M2 coefficient remain open are superseded
by the following unconditional concrete theorems on `main`:

- `su2FirstRailMassMeasure_eq_uniform`;
- `integral_su2Haar_orbit_character_general`;
- `su2CharacterChebyshev_convolution`;
- `su2HeatKernel_convolution`;
- `su2Migdal_subdivision_invariant`;
- `su2_exact_simpleLoop_areaLaw`;
- `su2PlanarCellulationAmplitude_eq_heatKernel`;
- `su2TreePlanarExactAreaLawPackage`;
- `SU2FaceEliminationSchedule.exists_schedule_of_connected_graph`;
- `SU2FaceEliminationSchedule.amplitude_eq_of_valid_schedules`;
- `SU2ConnectedDiskCellulation.amplitude_eq_heatKernel`;
- `su2ConnectedDiskExactAreaLawPackage`;
- `su2ThreeSpokeGaugeFix_measurePreserving`;
- `su2ThreeSpoke_unreducedIntegral_eq_gaugeFixedIntegral`;
- `su2ThreeSpoke_unreducedIntegral_eq_heatKernel`.

The generic hypothesis packages remain useful interfaces, but none of the
conclusions above is obtained by projecting a field from such a package.  The
finite oriented disk-cellulation reduction is now global for every connected
dual graph at the explicitly defined post-gauge-fixed level.  Existence and
independence of the elimination schedule are theorems, including in the
presence of dual cycles.  For the concrete three-spoke disk with three-cycle
dual, equality with the unreduced triple product-Haar edge integral is now a
theorem derived from an explicit measure-preserving gauge fixing.  The
remaining planar frontier is the corresponding product-Haar equivalence for
an arbitrary connected finite disk, followed by comparison with embedded
planar isotopy classes.  Continuum construction and the positive-area
higher-genus layer also remain open.  The detailed pre-closure history is
retained below for provenance only.

## Main Branch Status

- Lean `sorry`: 0 intended.
- Project-local `axiom`: 0 intended.
- Hard analytic inputs: carried only as explicit fields of structures in `Lean2dYangMills/Interfaces.lean`.

## Authoritative area-law distinction

The programme's previously published, machine-checked Wilson-loop result is a
volume-uniform strong-coupling *bound* for finite-lattice `SU(N_c)` gauge theory,
obtained by cluster expansion, Kotecky--Preiss convergence, and rooted-tree
majorants. It is prior work and must be cited as such.

M2 in this repository is mathematically different: it asks for the exact
two-dimensional `SU(2)` heat-kernel identity for simple planar loops, derived
through Weyl integration, character convolution, edge integration, and Migdal
subdivision invariance. The earlier bound neither discharges nor supplies a
nontrivial `ExactAreaLawPackage` here. This clarification changes claim
architecture, not theorem content.

## Closed facts on `main` through PR #44

Concrete SU(2) character layer (current post-PR #44 work):

- `su2_apply_one_one_eq_conj_apply_zero_zero`: the defining matrix has
  `g₁₁ = conj(g₀₀)`, derived from determinant one and unitarity through the
  two-by-two adjugate.
- `su2_norm_apply_zero_zero_le_one` and `su2_half_trace_eq_ofReal_re`: the
  Chebyshev argument `tr(g)/2` is real and lies in `[-1,1]`.
- `abs_chebyshevU_real_le_of_mem_Icc`: the sharp bound
  `|U_n(x)| <= n+1` on `[-1,1]`, including the endpoint cases.
- `abs_su2CharacterChebyshev_le`: the concrete SU(2) Weyl character bound,
  with no spectral hypothesis.
- `summable_su2HeatKernelTerm`: unconditional pointwise summability of the
  SU(2) heat-kernel character series for every positive heat time.
- `tendstoUniformly_su2HeatKernelCharacterSeries` and
  `continuous_su2HeatKernelCharacterSeries`: the Casimir majorant gives
  uniform convergence on the whole gauge group and continuity of the sum.
- `su2HeatKernelCharacterSeries_conj_invariant`: unconditional class-function
  invariance of the concrete series.
- `intervalIntegral_chebyshevU_mul_chebyshevU_sin_sq`: exact SU(2)
  class-character orthogonality in Weyl angle coordinates,
  `integral U_n(cos theta) U_m(cos theta) sin(theta)^2 = pi/2 delta_nm`.
- `su2HaarProb`: an internally constructed normalized Haar probability
  measure on Mathlib's concrete SU(2), with compactness and topological-group
  instances proved in the satellite.
- `integral_su2CharacterChebyshev_eq_zero_of_odd`: the first concrete Haar
  selector; every odd character has zero Haar mean by translation with `-I`.
- `integral_su2_normSq_zero_zero` and `integral_su2_re_zero_zero_sq`: exact
  normalized Haar moments `E|g₀₀|² = 1/2` and `E(Re g₀₀)² = 1/4`, proved by
  explicit SU(2) translation symmetries.
- `integral_su2FundamentalCharacter_re_sq`: the first nontrivial Schur
  normalization, `∫χ₁² = 1`.
- `integral_su2CharacterChebyshev_two_eq_zero`: the first even Haar selector,
  `∫χ₂ = 0`, obtained from the exact coordinate moment.
- `su2Hadamard` and `integral_su2_odd_mixed_fourth_cancel`: a concrete
  forty-five-degree SU(2) translation and the exact cancellation needed for
  the fourth-moment binomial step. This is infrastructure toward `∫χ₄=0`;
  it is not yet the all-order Weyl pushforward theorem.
- `su2EquivRowSphere` and `su2HomeomorphRowSphere`: unconditional algebraic
  and topological identifications
  `SU(2) ≃ {(a,b) : ℂ² // |a|²+|b|²=1}`. The inverse matrix is constructed
  explicitly and proved special unitary.
- `su2RowSphereHaar`, `measurePreserving_su2ToRowSphere`, and
  `measurePreserving_su2RowSphereLeft`: Haar is transported through that
  homeomorphism to a probability measure on the unit 3-sphere, and the
  transported measure is proved invariant under the full SU(2) action.
- `rowSphereHomeomorphMetricSphere`, `su2CanonicalSphereProbability`, and
  `su2CanonicalRowSphereMeasure`: the coordinate sphere is now identified
  with the exact L2 metric-sphere type consumed by `Measure.toSphere`; the
  canonical finite spherical measure is normalized and pulled back to the
  same type as transported Haar.
- `su2AmbientLeftLinearIsometryEquiv`, `su2MetricSphereLeft`, and
  `rowSphereToMetricSphere_su2RowSphereLeft`: for every `h : SU(2)`, the
  induced action on `L²(ℂ × ℂ)` is proved to be a real-linear isometric
  equivalence, its restriction preserves the metric sphere, and that
  restriction is exactly the transported group action.
- `measurePreserving_linearIsometryUnitSphereMap` and
  `measurePreserving_su2MetricSphereLeft_toSphere`: any ambient measure
  preserved by a real-linear isometry induces a preserved `toSphere` measure;
  in particular the full SU(2) action preserves canonical spherical volume.
- `su2CanonicalPullback_eq_su2HaarProb` and
  `su2RowSphereHaar_eq_su2CanonicalRowSphereMeasure`: after normalization and
  transport back to SU(2), uniqueness of Haar closes the literal equality of
  transported Haar and canonical spherical probability. No measure bridge
  remains open; the next M0 obstruction is general Weyl pushforward.

Current audited base commit: PR #44 at `main` commit `71422d8`.

PR #29 was a digest/status refresh after PR #28; it did not add or rename Lean
theorems.

PR #34 was a digest/status refresh after PR #33; it did not add or rename Lean
theorems.

PR #35 was a digest/status refresh after PR #34; it did not add or rename Lean
theorems.

PR #40 was a digest/status refresh after PR #37; it did not add or rename Lean
theorems.

PR #41 was a digest/status refresh after PR #40; it did not add or rename Lean
theorems.

PR #42 was a digest/status refresh after PR #41; it did not add or rename Lean
theorems.

PR #43 was a digest/status refresh after PR #42; it did not add or rename Lean
theorems.

PR #44 was a digest/status refresh after PR #43; it did not add or rename Lean
theorems.

Witten zeta layer (`WittenZetaSU2.lean`) — milestone M4 convergence closed:

- `su2WittenZetaData`: SU(2) dimensions `1, 2, 3, ...` with terms `(n+1)^(-s)`.
- `summable_su2WittenZetaTerm`: convergence for `1 < Re s`.
- `su2WittenZetaPackage`: `WittenZetaPackage` instantiated with
  `zeta := riemannZeta`, BOTH hypothesis fields discharged — the first fully
  unconditional package instance of this repository.
- `su2_wittenZetaSeries_eq_riemannZeta`: **the Witten zeta function of SU(2)
  IS the Riemann zeta function** on the convergence half-plane.
- `su2ZeroAreaSurfaceModel`, `su2ZeroArea_partition_eq_wittenZetaSeries`,
  `su2ZeroArea_wittenZetaSeries_converges` (PR #26 consumer check for the
  public `wittenZeta_converges` wrapper),
  `su2ZeroArea_surfacePartitionSeries_summable` (consumer check for the
  public `surfacePartitionFunction_summable` wrapper), and
  `su2ZeroArea_partition_eq_riemannZeta`: zero-area genus-g partition
  functions are consumed through the public M4 surface wrapper; the public
  `wittenZeta_converges` wrapper supplies convergence at the genus argument
  `2g-2`; the public surface summability wrapper exposes the same package
  field; and the same series is identified with `zeta(2g-2)` (the partition
  function is DEFINED as the series in this topological-limit model — a
  declared consumer test).

Convergence engine (`ConvergenceEngine.lean`) — the M0 analytic engine:

- `summable_pow_mul_exp_neg`: `(n+1)^k exp(-t n)` summable for `t > 0`.
- `summable_pow_mul_exp_neg_casimir`: the Casimir-decay variant
  `(n+1)^k exp(-t n(n+2)/4)`.
- `summable_su2_dim_sq_exp_neg_casimir`: the `k = 2` specialization
  `((n+1)^2) exp(-t n(n+2)/4)`, useful after a future Weyl bound reduces
  SU(2) heat-kernel terms to dimension-square Casimir decay. This does not
  construct the SU(2) heat kernel or character table.

Consumer test (`TrivialModel.lean`):

- `trivialHeatKernelPackage`: `HeatKernelCharacterPackage` with EVERY field
  a theorem; its semigroup proposition is the honest convolution law,
  stated and proved (`trivialHeatKernelPackage_semigroup`).
- `trivialHeatKernelCharacterSeries_converges`: consumer check that the public
  `heatKernel_character_series_converges` wrapper applies to the trivial
  model's character series.
- `trivialHeatKernelCharacterSeries_eq_one`: consumer check that the public
  `heatKernel_character_series_eq` wrapper reduces the trivial model's
  character series to `1`.
- `trivialHeatKernel_conj_invariant`: consumer check that the public
  `heatKernel_conj_invariant` wrapper applies to the trivial heat kernel.
- `trivialExactAreaLawPackage`: `ExactAreaLawPackage` for a one-loop,
  zero-area model with EVERY field discharged; the public M2 wrapper is
  exercised by `trivialSimpleLoop_areaLaw_exact`.
- `trivialSimpleLoop_stringTension_nonnegative`: consumer check that the
  public `simpleLoop_stringTension_nonnegative` wrapper applies to the
  trivial exact-area-law package.
- `trivialSimpleLoop_area_nonnegative`: consumer check that the explicit
  `ExactAreaLawPackage.area_nonnegative` field is available through the public
  `simpleLoop_area_nonnegative` wrapper for the trivial exact-area-law package.
- `trivialSimpleLoop_wilsonExpectation_zero_area`: consumer check that the
  public `simpleLoop_wilsonExpectation_zero_area` wrapper combines an exact
  area-law package with an explicit zero-area hypothesis to reduce the Wilson
  expectation to `1`.
- `trivialAreaLawValue_zero_area`: consumer check that the public
  `areaLawValue_zero_area` API lemma reduces the trivial model's area-law
  value to `1`.

Area-law API normalization (`Interfaces.lean`):

- `areaLawValue_zero_area`: definitional lemma proving `areaLawValue T C = 1`
  from the explicit hypothesis `T.area C = 0`. It is only public-interface
  glue and does not discharge `ExactAreaLawPackage.*`.
- `simpleLoop_area_nonnegative`: public-interface glue projecting the explicit
  `ExactAreaLawPackage.area_nonnegative` field. It does not discharge an
  `ExactAreaLawPackage` for any nontrivial model.
- `simpleLoop_wilsonExpectation_zero_area`: conditional public-interface glue
  combining an already supplied `ExactAreaLawPackage` with an explicit
  zero-area hypothesis. It does not supply the package or prove a physical
  area law.

## Explicit Hypothesis Packages (unchanged, still open for real models)

- `HeatKernelCharacterPackage.*` for SU(2): summability, tsum equality,
  conjugation invariance, semigroup law.
- `MigdalSelfSimilarityPackage.self_similarity`.
- `ExactAreaLawPackage.*`.
- `ContinuumLimitPackage.convergence`.
- `WittenZetaSurfacePackage` at positive area (the zero-area model above
  does not close the analytic M4).

## Frontier obligations (branch `frontier/M0-su2`, statement-first, sorried)

Former `Frontier/SU2Character.lean` obligations:

- `su2CharacterChebyshev`, `su2CharacterTable`,
  `su2CharacterChebyshev_one`, `abs_su2CharacterChebyshev_le`, and
  `summable_su2HeatKernelTerm` are now closed on `main` without `sorry`.
- The analytic angle-coordinate orthogonality is closed. The remaining M0
  obstruction is the group-theoretic Weyl integration/pushforward theorem
  identifying the normalized `sin(theta)^2 dtheta` measure with the class
  pushforward of SU(2) Haar for all class functions (the odd-character sector
  is already closed directly), followed by the full matrix-coefficient
  convolution theorem. These are needed to replace the weak
  `heatKernel_semigroup : Prop` interface by a concrete equality.

## Distance To Goal

M4's convergence layer is closed and identifies the Riemann bridge
unconditionally. M0 now has its concrete character definition, sharp Weyl
bound, uniform heat-series convergence, angular orthogonality, normalized
Haar measure, the exact canonical-sphere/Haar measure bridge, all odd Haar
selectors, and the first even selector. What remains for M0 is the general
Haar/Weyl pushforward theorem and
matrix-coefficient orthogonality needed for the semigroup. M1 (Migdal), M2
(area law), M3 (continuum) remain open as before.

Any branch that introduces `sorry` must be named `frontier/*` and must
update this file with exact theorem names and remaining assumptions.
