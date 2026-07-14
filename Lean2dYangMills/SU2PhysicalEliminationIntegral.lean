import Lean2dYangMills.SU2PhysicalEliminationSchedule

/-!
# Haar coordinates for iterated physical elimination

The physical boundary chart integrates over an arbitrary finite subtype of
chords.  The elimination certificate identifies that type with `Fin n`.
Here the identification is consumed at the level of the actual conditioned
integral, and the last `Fin` coordinate is split off as one Haar variable.
These are the measure-theoretic coordinates required for induction by the
local Migdal move.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- Splitting the last coordinate of a finite SU(2) family preserves literal
product Haar. -/
theorem su2SplitLastEquiv_measurePreserving (n : Nat) :
    MeasurePreserving (su2SplitLastEquiv n)
      (su2FiniteProductHaar (Fin (n + 1)))
      (su2HaarProb.prod (su2FiniteProductHaar (Fin n))) := by
  change MeasurePreserving
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => SU2)
      (Fin.last n))
    (Measure.pi (fun _ : Fin (n + 1) => su2HaarProb))
    (su2HaarProb.prod
      (Measure.pi (fun _ : Fin n => su2HaarProb)))
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => su2HaarProb) (Fin.last n)

/-- Integral form of the last-coordinate split. -/
theorem su2FiniteProductHaar_integral_splitLast (n : Nat)
    (f : (Fin (n + 1) -> SU2) -> Complex) :
    (∫ x, f x ∂su2FiniteProductHaar (Fin (n + 1))) =
      ∫ p : SU2 × (Fin n -> SU2),
        f ((su2SplitLastEquiv n).symm p)
        ∂(su2HaarProb.prod (su2FiniteProductHaar (Fin n))) := by
  have hinv : MeasurePreserving (su2SplitLastEquiv n).symm
      (su2HaarProb.prod (su2FiniteProductHaar (Fin n)))
      (su2FiniteProductHaar (Fin (n + 1))) :=
    MeasurePreserving.symm (su2SplitLastEquiv n)
      (su2SplitLastEquiv_measurePreserving n)
  exact (hinv.integral_comp' f).symm

/-- Last-coordinate splitting with the untouched coordinates placed first,
the order needed for a pointwise application of the local Migdal integral. -/
def su2SplitLastRestFirstEquiv (n : Nat) :
    (Fin (n + 1) -> SU2) ≃ᵐ ((Fin n -> SU2) × SU2) :=
  (su2SplitLastEquiv n).trans MeasurableEquiv.prodComm

theorem su2SplitLastRestFirstEquiv_measurePreserving (n : Nat) :
    MeasurePreserving (su2SplitLastRestFirstEquiv n)
      (su2FiniteProductHaar (Fin (n + 1)))
      ((su2FiniteProductHaar (Fin n)).prod su2HaarProb) := by
  exact Measure.measurePreserving_swap.comp
    (su2SplitLastEquiv_measurePreserving n)

/-- **Fubini in physical-elimination order.**  The final coordinate is the
inner Haar integral, while all earlier coordinates remain fixed outside. -/
theorem su2FiniteProductHaar_integral_iteratedLast (n : Nat)
    (f : (Fin (n + 1) -> SU2) -> Complex)
    (hf : Integrable f (su2FiniteProductHaar (Fin (n + 1)))) :
    (∫ z, f z ∂su2FiniteProductHaar (Fin (n + 1))) =
      ∫ r : Fin n -> SU2,
        ∫ x : SU2,
          f ((su2SplitLastRestFirstEquiv n).symm (r, x))
          ∂su2HaarProb
        ∂su2FiniteProductHaar (Fin n) := by
  let E := su2SplitLastRestFirstEquiv n
  have hinv : MeasurePreserving E.symm
      ((su2FiniteProductHaar (Fin n)).prod su2HaarProb)
      (su2FiniteProductHaar (Fin (n + 1))) :=
    MeasurePreserving.symm E
      (su2SplitLastRestFirstEquiv_measurePreserving n)
  have hcomp : Integrable (fun p => f (E.symm p))
      ((su2FiniteProductHaar (Fin n)).prod su2HaarProb) :=
    hinv.integrable_comp_of_integrable hf
  calc
    (∫ z, f z ∂su2FiniteProductHaar (Fin (n + 1))) =
        ∫ p, f (E.symm p)
          ∂((su2FiniteProductHaar (Fin n)).prod su2HaarProb) := by
      exact (hinv.integral_comp' f).symm
    _ = ∫ r : Fin n -> SU2,
          ∫ x : SU2, f (E.symm (r, x)) ∂su2HaarProb
          ∂su2FiniteProductHaar (Fin n) := by
      exact integral_prod (fun p => f (E.symm p)) hcomp

namespace SU2FiniteDiskCellulation.RootedSpanningTree

variable {C : SU2FiniteDiskCellulation}
  (T : C.RootedSpanningTree)

/-- The insertion of chord coordinates with all tree edges fixed to one is
continuous. -/
@[fun_prop]
theorem continuous_gaugeFixedEdgeConfiguration :
    Continuous T.gaugeFixedEdgeConfiguration := by
  refine continuous_pi fun e => ?_
  unfold gaugeFixedEdgeConfiguration
  split
  · exact continuous_const
  · exact continuous_apply _

end SU2FiniteDiskCellulation.RootedSpanningTree

namespace SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart

variable {P : SU2BoundaryDiskCellulation}
  (B : P.AdaptiveBoundaryGaugeChart)

local instance continuousChordEdgeDecidableEq :
    DecidableEq B.ChordEdge := Classical.decEq _

@[fun_prop]
theorem continuous_chordWithAnchorOne : Continuous B.chordWithAnchorOne := by
  unfold chordWithAnchorOne chordSplitEquiv su2PiSplitAtEquiv
  change Continuous (fun r =>
    (Homeomorph.funSplitAt SU2 B.boundaryChord).symm (1, r))
  exact (Homeomorph.funSplitAt SU2 B.boundaryChord).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

@[fun_prop]
theorem continuous_chordExteriorPrefix : Continuous B.chordExteriorPrefix := by
  unfold chordExteriorPrefix
  apply P.connected.cellulation.continuous_dartHolonomy_comp
  exact B.tree.continuous_gaugeFixedEdgeConfiguration.comp
    B.continuous_chordWithAnchorOne

@[fun_prop]
theorem continuous_chordExteriorSuffix : Continuous B.chordExteriorSuffix := by
  unfold chordExteriorSuffix
  apply P.connected.cellulation.continuous_dartHolonomy_comp
  exact B.tree.continuous_gaugeFixedEdgeConfiguration.comp
    B.continuous_chordWithAnchorOne

/-- For fixed physical exterior holonomy, reconstruction of all chord
coordinates through the adaptive boundary chart is continuous. -/
theorem continuous_chordBoundaryEquiv_symm_const (g : SU2) :
    Continuous (fun r => B.chordBoundaryEquiv.symm (r, g)) := by
  unfold chordBoundaryEquiv boundaryHolonomyShearEquiv chordSplitEquiv
    su2PiSplitAtEquiv
  change Continuous (fun r =>
    (Homeomorph.funSplitAt SU2 B.boundaryChord).symm
      ((if P.connected.cellulation.halfEdgeSide B.anchorDart = true
        then B.chordExteriorSuffix r * g⁻¹ * B.chordExteriorPrefix r
        else (B.chordExteriorPrefix r)⁻¹ * g *
          (B.chordExteriorSuffix r)⁻¹), r))
  apply (Homeomorph.funSplitAt SU2 B.boundaryChord).symm.continuous.comp
  by_cases hs :
      P.connected.cellulation.halfEdgeSide B.anchorDart = true
  · simp [hs]
    constructor <;> fun_prop
  · simp [hs]
    constructor <;> fun_prop

end SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart

namespace SU2PhysicalBoundaryEliminationChart

variable {P : SU2BoundaryDiskCellulation}
  (D : SU2PhysicalBoundaryEliminationChart P)

local instance integralEdgeDecidableEq :
    DecidableEq P.connected.cellulation.Edge := Classical.decEq _

local instance integralChordEdgeDecidableEq :
    DecidableEq D.boundary.ChordEdge := Classical.decEq _

/-- Evaluating the inverse relabelling on the chord assigned to step `i`
recovers coordinate `i` literally. -/
theorem internalCoordinateEquiv_symm_apply_stepChord
    (x : Fin D.elimination.n -> SU2) (i : Fin D.elimination.n) :
    D.internalCoordinateEquiv.symm x (D.stepChord i) = x i := by
  have h := D.internalCoordinateEquiv_apply
    (D.internalCoordinateEquiv.symm x) i
  rw [D.internalCoordinateEquiv.apply_symm_apply] at h
  exact h.symm

/-- Inverting the boundary shear changes only the distinguished exterior
chord; every internal chord retains its supplied coordinate. -/
theorem chordBoundaryEquiv_symm_apply_other
    (r : D.OtherChord -> SU2) (g : SU2) (e : D.OtherChord) :
    D.boundary.chordBoundaryEquiv.symm (r, g) e.1 = r e := by
  let y := D.boundary.chordBoundaryEquiv.symm (r, g)
  have h := D.boundary.chordBoundaryEquiv.apply_symm_apply (r, g)
  have he := congrArg (fun p => p.1 e) h
  change (D.boundary.chordBoundaryEquiv y).1 e = r e at he
  change y e.1 = r e
  calc
    y e.1 = (D.boundary.chordSplitEquiv y).1 e := by
      exact (su2PiSplitAtEquiv_apply_fst D.boundary.boundaryChord y e).symm
    _ = (D.boundary.chordBoundaryEquiv y).1 e := by
      rw [D.boundary.chordBoundaryEquiv_apply_fst]
    _ = r e := he

/-- **Physical coordinate identity.**  Step coordinate `i` is exactly the
value of the original physical edge selected by that Migdal step in the
conditioned gauge-fixed configuration. -/
theorem conditionedGaugeFixed_selectedEdge
    (g : SU2) (x : Fin D.elimination.n -> SU2)
    (i : Fin D.elimination.n) :
    D.boundary.tree.gaugeFixedEdgeConfiguration
        (D.boundary.chordBoundaryEquiv.symm
          (D.internalCoordinateEquiv.symm x, g))
        (D.elimination.selectedEdge i) = x i := by
  change D.boundary.tree.gaugeFixedEdgeConfiguration
      (D.boundary.chordBoundaryEquiv.symm
        (D.internalCoordinateEquiv.symm x, g))
      (D.stepChord i).1.1 = x i
  rw [D.boundary.tree.gaugeFixedEdgeConfiguration_chord]
  rw [D.chordBoundaryEquiv_symm_apply_other]
  exact D.internalCoordinateEquiv_symm_apply_stepChord x i

/-- Every fixed-boundary slice is continuous in its internal chord
coordinates. -/
theorem continuous_conditionedChordDensity (g : SU2) :
    Continuous (D.boundary.conditionedChordDensity g) := by
  unfold SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.conditionedChordDensity
    SU2EdgeConnectedDiskCellulation.chordGaugeFixedDensity
  exact P.toSU2EdgeConnectedDiskCellulation.continuous_edgeHeatKernelDensity.comp
    (D.boundary.tree.continuous_gaugeFixedEdgeConfiguration.comp
      (D.boundary.continuous_chordBoundaryEquiv_symm_const g))

/-- Compactness of finite SU(2) products makes every fixed-boundary slice
Bochner integrable, not merely almost-everywhere integrable. -/
theorem integrable_conditionedChordDensity (g : SU2) :
    Integrable (D.boundary.conditionedChordDensity g)
      (su2FiniteProductHaar D.OtherChord) := by
  exact integrable_of_continuous_compact
    (D.continuous_conditionedChordDensity g)

/-- Conditioned chord density after relabelling every internal physical chord
by its unique elimination step. -/
def indexedConditionedChordDensity (g : SU2)
    (x : Fin D.elimination.n -> SU2) : Complex :=
  D.boundary.conditionedChordDensity g
    (D.internalCoordinateEquiv.symm x)

/-- Integrability survives the Haar-preserving relabelling by elimination
steps. -/
theorem integrable_indexedConditionedChordDensity (g : SU2) :
    Integrable (D.indexedConditionedChordDensity g)
      (su2FiniteProductHaar (Fin D.elimination.n)) := by
  have hinv : MeasurePreserving D.internalCoordinateEquiv.symm
      (su2FiniteProductHaar (Fin D.elimination.n))
      (su2FiniteProductHaar D.OtherChord) :=
    MeasurePreserving.symm D.internalCoordinateEquiv
      D.internalCoordinateEquiv_measurePreserving
  exact hinv.integrable_comp_of_integrable
    (D.integrable_conditionedChordDensity g)

/-- The actual conditioned chord integral is exactly the integral of the
step-indexed density over `Fin n` product Haar. -/
theorem conditionedChordIntegral_eq_indexedIntegral (g : SU2) :
    D.boundary.conditionedChordIntegral g =
      ∫ x, D.indexedConditionedChordDensity g x
        ∂su2FiniteProductHaar (Fin D.elimination.n) := by
  change (∫ r, D.boundary.conditionedChordDensity g r
      ∂su2FiniteProductHaar D.OtherChord) =
    ∫ x, D.boundary.conditionedChordDensity g
      (D.internalCoordinateEquiv.symm x)
      ∂su2FiniteProductHaar (Fin D.elimination.n)
  have hinv : MeasurePreserving D.internalCoordinateEquiv.symm
      (su2FiniteProductHaar (Fin D.elimination.n))
      (su2FiniteProductHaar D.OtherChord) :=
    MeasurePreserving.symm D.internalCoordinateEquiv
      D.internalCoordinateEquiv_measurePreserving
  exact (hinv.integral_comp'
    (D.boundary.conditionedChordDensity g)).symm

end SU2PhysicalBoundaryEliminationChart

end Lean2dYangMills
