import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.Complex

/-!
# Public interfaces for the 2D Yang-Mills sandbox

This file is intentionally conditional.  The difficult analytic statements are
fields of explicit packages, and the exported theorems only project those
fields.  This keeps the parent repository's import surface stable without
turning missing mathematics into axioms.
-/

noncomputable section

open scoped BigOperators

namespace Lean2dYangMills

universe u v w

/-- Concrete first gauge group for the sandbox: `SU(2)` as Mathlib's special unitary group.

Mathlib source: `Mathlib.LinearAlgebra.UnitaryGroup`.
-/
abbrev SU2 : Type :=
  Matrix.specialUnitaryGroup (Fin 2) Complex

/-- Abstract irreducible-character data for a compact gauge group.

The intended `SU(2)` instance is the highest-weight table with dimensions
`n + 1`, characters `chi_n`, and quadratic Casimir values.  This file does not
construct that table.

Reference target: Migdal (1975, Sov. Phys. JETP 42, 413-418) and Driver
(1989, Commun. Math. Phys. 123, 575-616), where the heat-kernel formulation is
the 2D lattice/continuum bridge.
-/
structure CharacterTable (G : Type u) where
  Label : Type v
  dim : Label -> Nat
  dim_pos : forall lam : Label, 0 < dim lam
  char : Label -> G -> Complex
  casimir : Label -> Real
  heatWeight : Real -> Label -> Complex

/-- One summand in the formal compact-group heat-kernel character expansion.

The field `T.heatWeight t lam` is intended to be `exp(-t * C2(lam))`; it is
kept as data until the Casimir/heat-kernel layer is formalized.
-/
def heatKernelTerm {G : Type u} (T : CharacterTable.{u, v} G) (t : Real) (g : G)
    (lam : T.Label) : Complex :=
  (T.dim lam : Complex) * T.char lam g * T.heatWeight t lam

/-- The formal heat-kernel character series `sum dim(lambda) chi_lambda(g) exp(-t C2(lambda))`. -/
def heatKernelCharacterSeries {G : Type u} (T : CharacterTable.{u, v} G) (t : Real) (g : G) :
    Complex :=
  tsum fun lam : T.Label => heatKernelTerm T t g lam

/-- Conditional heat-kernel package.

Supplying this structure is exactly supplying the hard M0 analytic input:
convergence of the character expansion, equality with the heat kernel, class
invariance, and the convolution semigroup statement.

References: Migdal (1975, Sov. Phys. JETP 42, 413-418); Driver (1989,
Commun. Math. Phys. 123, 575-616).
-/
structure HeatKernelCharacterPackage (G : Type u) [Group G] where
  table : CharacterTable.{u, v} G
  heatKernel : Real -> G -> Complex
  heatKernel_summable :
    forall {t : Real}, 0 < t -> forall g : G, Summable (heatKernelTerm table t g)
  heatKernel_eq_tsum :
    forall {t : Real}, 0 < t -> forall g : G,
      heatKernel t g = heatKernelCharacterSeries table t g
  heatKernel_conj_invariant :
    forall {t : Real}, 0 < t -> forall x g : G, heatKernel t (x * g * x⁻¹) = heatKernel t g
  heatKernel_semigroup : Prop

abbrev SU2CharacterTable :=
  CharacterTable.{0, 0} SU2

abbrev SU2HeatKernelPackage :=
  HeatKernelCharacterPackage.{0, 0} SU2

/-- Convergence of the heat-kernel character expansion, conditional on the package.

Reference target: Migdal (1975, Sov. Phys. JETP 42, 413-418), exactness in
two dimensions; Driver (1989, Commun. Math. Phys. 123, 575-616), lattice and
continuum expectations.
-/
theorem heatKernel_character_series_converges {G : Type u} [Group G]
    (P : HeatKernelCharacterPackage.{u, v} G) {t : Real} (ht : 0 < t) (g : G) :
    Summable (heatKernelTerm P.table t g) :=
  P.heatKernel_summable ht g

/-- Equality between the heat kernel and its character series, conditional on the package.

Reference target: Driver (1989, Commun. Math. Phys. 123, 575-616).
-/
theorem heatKernel_character_series_eq {G : Type u} [Group G]
    (P : HeatKernelCharacterPackage.{u, v} G) {t : Real} (ht : 0 < t) (g : G) :
    P.heatKernel t g = heatKernelCharacterSeries P.table t g :=
  P.heatKernel_eq_tsum ht g

/-- Heat-kernel class-function invariance, conditional on the package. -/
theorem heatKernel_conj_invariant {G : Type u} [Group G]
    (P : HeatKernelCharacterPackage.{u, v} G) {t : Real} (ht : 0 < t) (x g : G) :
    P.heatKernel t (x * g * x⁻¹) = P.heatKernel t g :=
  P.heatKernel_conj_invariant ht x g

/-- The heat-kernel convolution semigroup proposition carried by the package. -/
def heatKernel_semigroup_statement {G : Type u} [Group G]
    (P : HeatKernelCharacterPackage.{u, v} G) : Prop :=
  P.heatKernel_semigroup

/-- Minimal finite-lattice expectation interface for heat-kernel Yang-Mills.

This deliberately avoids committing to a graph encoding before the parent
Peter-Weyl/Haar layer is shared.
-/
structure FiniteLatticeTheory (G : Type u) [Group G] where
  Lattice : Type v
  Observable : Lattice -> Type w
  expectation : (L : Lattice) -> Observable L -> Complex

/-- A plaquette subdivision map between two finite lattices. -/
structure PlaquetteSubdivision {G : Type u} [Group G] (T : FiniteLatticeTheory.{u, v, w} G) where
  coarse : T.Lattice
  fine : T.Lattice
  pullObservable : T.Observable coarse -> T.Observable fine

/-- Conditional Migdal self-similarity package for finite heat-kernel lattices.

Reference target: Migdal (1975, Sov. Phys. JETP 42, 413-418), where the
recursion relation becomes exact in two dimensions.
-/
structure MigdalSelfSimilarityPackage {G : Type u} [Group G]
    (T : FiniteLatticeTheory.{u, v, w} G) where
  self_similarity :
    forall (S : PlaquetteSubdivision T) (O : T.Observable S.coarse),
      T.expectation S.fine (S.pullObservable O) = T.expectation S.coarse O

/-- Invariance of finite-lattice expectations under plaquette subdivision, conditional on M1. -/
theorem migdal_self_similarity {G : Type u} [Group G] {T : FiniteLatticeTheory.{u, v, w} G}
    (P : MigdalSelfSimilarityPackage T) (S : PlaquetteSubdivision T)
    (O : T.Observable S.coarse) :
    T.expectation S.fine (S.pullObservable O) = T.expectation S.coarse O :=
  P.self_similarity S O

/-- Data for a simple planar Wilson-loop area-law statement. -/
structure PlaneSimpleLoopTheory where
  Loop : Type u
  area : Loop -> Real
  wilsonExpectation : Loop -> Complex
  stringTension : Real

/-- The expected exact area-law value `exp(-sigma * area(C))`. -/
def areaLawValue (T : PlaneSimpleLoopTheory.{u}) (C : T.Loop) : Complex :=
  Complex.exp (((-T.stringTension * T.area C : Real) : Complex))

/-- A zero-area loop has area-law value `1`, by the definition of
`areaLawValue`. This is a definitional API lemma, not a physical area-law
theorem. -/
theorem areaLawValue_zero_area (T : PlaneSimpleLoopTheory.{u}) {C : T.Loop}
    (hC : T.area C = 0) :
    areaLawValue T C = 1 := by
  simp [areaLawValue, hC]

/-- Conditional exact area-law package for simple planar loops.

The string tension is explicit as the field `T.stringTension`; this file does
not compute it from an `SU(2)` Casimir.

This package is intended to be instantiated by the exact two-dimensional
heat-kernel/Migdal construction.  The Eriksson programme's earlier
volume-uniform strong-coupling Wilson-loop inequality is a different theorem:
it uses cluster expansion and Kotecky--Preiss convergence for finite-lattice
`SU(N_c)` gauge theory.  That bound must not be imported as a nontrivial
instance of this exact-identity package.

Reference target: Driver (1989, Commun. Math. Phys. 123, 575-616), plane loop
expectations; Sengupta (1997, Mem. Amer. Math. Soc. 126, no. 600), compact
surface gauge theory; Levy (2003, Mem. Amer. Math. Soc. 166, no. 790), compact
surface Yang-Mills measure.
-/
structure ExactAreaLawPackage (T : PlaneSimpleLoopTheory.{u}) where
  area_nonnegative : forall C : T.Loop, 0 <= T.area C
  stringTension_nonnegative : 0 <= T.stringTension
  wilson_eq_areaLaw : forall C : T.Loop, T.wilsonExpectation C = areaLawValue T C

/-- Exact simple-loop Wilson area law, conditional on M2. -/
theorem simpleLoop_areaLaw_exact {T : PlaneSimpleLoopTheory.{u}}
    (P : ExactAreaLawPackage T) (C : T.Loop) :
    T.wilsonExpectation C = areaLawValue T C :=
  P.wilson_eq_areaLaw C

/-- Nonnegativity of the explicit string tension carried by the area-law package. -/
theorem simpleLoop_stringTension_nonnegative {T : PlaneSimpleLoopTheory.{u}}
    (P : ExactAreaLawPackage T) : 0 <= T.stringTension :=
  P.stringTension_nonnegative

/-- Nonnegativity of the explicit loop area carried by the area-law package. -/
theorem simpleLoop_area_nonnegative {T : PlaneSimpleLoopTheory.{u}}
    (P : ExactAreaLawPackage T) (C : T.Loop) : 0 <= T.area C :=
  P.area_nonnegative C

/-- A zero-area loop in an exact area-law package has Wilson expectation `1`.

This is conditional interface glue: the package supplies the exact area law,
and the caller supplies the zero-area hypothesis. -/
theorem simpleLoop_wilsonExpectation_zero_area {T : PlaneSimpleLoopTheory.{u}}
    (P : ExactAreaLawPackage T) {C : T.Loop} (hC : T.area C = 0) :
    T.wilsonExpectation C = 1 := by
  rw [simpleLoop_areaLaw_exact P C, areaLawValue_zero_area T hC]

/-- Statements-first continuum limit package.

Reference target: Driver (1989, Commun. Math. Phys. 123, 575-616); Levy
(2003, Mem. Amer. Math. Soc. 166, no. 790); Sengupta (1997, Mem. Amer. Math.
Soc. 126, no. 600).
-/
structure ContinuumLimitPackage where
  LatticeState : Type u
  ContinuumState : Type v
  Observable : Type w
  convergesTo : (Nat -> LatticeState) -> ContinuumState -> Prop
  latticeExpectation : LatticeState -> Observable -> Complex
  continuumExpectation : ContinuumState -> Observable -> Complex
  convergence :
    forall (a : Nat -> LatticeState) (A : ContinuumState) (O : Observable),
      convergesTo a A ->
        Filter.Tendsto (fun n : Nat => latticeExpectation (a n) O)
          Filter.atTop (nhds (continuumExpectation A O))

/-- Lattice-to-continuum convergence statement, conditional on M3. -/
theorem continuum_limit_statement (P : ContinuumLimitPackage.{u, v, w})
    (a : Nat -> P.LatticeState) (A : P.ContinuumState) (O : P.Observable)
    (h : P.convergesTo a A) :
    Filter.Tendsto (fun n : Nat => P.latticeExpectation (a n) O)
      Filter.atTop (nhds (P.continuumExpectation A O)) :=
  P.convergence a A O h

/-- Representation dimensions used to define the Witten zeta series. -/
structure WittenZetaData where
  Label : Type u
  dim : Label -> Nat
  dim_pos : forall lam : Label, 0 < dim lam
  zetaTerm : Complex -> Label -> Complex

/-- One summand of the Witten zeta series.

The field `Z.zetaTerm s lam` is intended to be `dim(lam)^(-s)`. It is data
for now, rather than importing the full complex-power API into the interface
layer.
-/
def wittenZetaTerm (Z : WittenZetaData.{u}) (s : Complex) (lam : Z.Label) : Complex :=
  Z.zetaTerm s lam

/-- The formal Witten zeta series `sum_lambda dim(lambda)^(-s)`. -/
def wittenZetaSeries (Z : WittenZetaData.{u}) (s : Complex) : Complex :=
  tsum fun lam : Z.Label => wittenZetaTerm Z s lam

/-- The usual genus argument `2g - 2` for the Witten zeta bridge. -/
def genusZetaArgument (genus : Nat) : Complex :=
  (((2 : Int) * (genus : Int) - 2 : Int) : Complex)

/-- Conditional Witten zeta package.

Reference target: Witten (1991, Commun. Math. Phys. 141, 153-209); Zagier
(1994, First European Congress of Mathematics, Vol. II, 497-512).
-/
structure WittenZetaPackage (Z : WittenZetaData.{u}) where
  zeta : Complex -> Complex
  zeta_summable :
    forall {s : Complex}, 1 < s.re -> Summable (wittenZetaTerm Z s)
  zeta_eq_tsum :
    forall {s : Complex}, 1 < s.re -> zeta s = wittenZetaSeries Z s

/-- Convergence of the Witten zeta series in the supplied half-plane. -/
theorem wittenZeta_converges {Z : WittenZetaData.{u}} (P : WittenZetaPackage Z)
    {s : Complex} (hs : 1 < s.re) :
    Summable (wittenZetaTerm Z s) :=
  P.zeta_summable hs

/-- Equality between the Witten zeta function and its representation-dimension series. -/
theorem wittenZeta_eq_tsum {Z : WittenZetaData.{u}} (P : WittenZetaPackage Z)
    {s : Complex} (hs : 1 < s.re) :
    P.zeta s = wittenZetaSeries Z s :=
  P.zeta_eq_tsum hs

/-- Conditional package for the appearance of Witten zeta in surface partition functions.

Reference target: Witten (1991, Commun. Math. Phys. 141, 153-209) and
Sengupta (1997, Mem. Amer. Math. Soc. 126, no. 600).
-/
structure WittenZetaSurfacePackage (Z : WittenZetaData.{u}) where
  Surface : Type v
  partitionFunction : Surface -> Complex
  zetaArgument : Surface -> Complex
  partition_summable : forall S : Surface, Summable (wittenZetaTerm Z (zetaArgument S))
  partition_eq_zeta :
    forall S : Surface, partitionFunction S = wittenZetaSeries Z (zetaArgument S)

/-- Summability of the surface partition-function representation series,
conditional on M4. -/
theorem surfacePartitionFunction_summable {Z : WittenZetaData.{u}}
    (P : WittenZetaSurfacePackage Z) (S : P.Surface) :
    Summable (wittenZetaTerm Z (P.zetaArgument S)) :=
  P.partition_summable S

/-- Surface partition function as a Witten-zeta representation series, conditional on M4. -/
theorem surfacePartitionFunction_eq_wittenZeta {Z : WittenZetaData.{u}}
    (P : WittenZetaSurfacePackage Z) (S : P.Surface) :
    P.partitionFunction S = wittenZetaSeries Z (P.zetaArgument S) :=
  P.partition_eq_zeta S

end Lean2dYangMills
