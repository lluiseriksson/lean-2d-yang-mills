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

namespace SU2PhysicalBoundaryEliminationChart

variable {P : SU2BoundaryDiskCellulation}
  (D : SU2PhysicalBoundaryEliminationChart P)

local instance integralEdgeDecidableEq :
    DecidableEq P.connected.cellulation.Edge := Classical.decEq _

local instance integralChordEdgeDecidableEq :
    DecidableEq D.boundary.ChordEdge := Classical.decEq _

/-- Conditioned chord density after relabelling every internal physical chord
by its unique elimination step. -/
def indexedConditionedChordDensity (g : SU2)
    (x : Fin D.elimination.n -> SU2) : Complex :=
  D.boundary.conditionedChordDensity g
    (D.internalCoordinateEquiv.symm x)

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
