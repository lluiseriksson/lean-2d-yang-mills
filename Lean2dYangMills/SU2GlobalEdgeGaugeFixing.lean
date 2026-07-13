import Lean2dYangMills.SU2RootedTreeGaugeFixing
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Global edge coordinates for finite disk cellulations

This module upgrades a certified rooted spanning tree from a statement about
vertex variables to a literal change of variables on every original edge.
The physical edges are partitioned into the `V - 1` selected tree edges and
their complementary chord edges.  Tree-edge orientations are aligned with
the parent-to-child construction order, and the resulting product-Haar
splitting is proved measure preserving.

The second stage reconstructs rooted vertex potentials from the oriented tree
increments and gauge-transforms every chord.  This gives one measurable
equivalence

`SU2^Edge ≃ SU2^(V - {root}) × SU2^(Edge - Tree)`

with literal preservation of the corresponding normalized product Haar
measures.  No planar elimination schedule is used in this construction.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- Bi-invariance and normalization make inversion preserve the normalized
SU(2) Haar probability. -/
instance instIsInvInvariantSU2HaarProbGlobalEdge :
    Measure.IsInvInvariant su2HaarProb where
  inv_eq_self := by
    let ν : Measure SU2 := su2HaarProb.inv
    haveI : IsProbabilityMeasure ν := by
      constructor
      change (Measure.map Inv.inv su2HaarProb) Set.univ = 1
      rw [Measure.map_apply measurable_inv MeasurableSet.univ]
      simp
    have hν := Measure.isMulInvariant_eq_smul_of_compactSpace ν su2HaarProb
    have hu := congrArg (fun μ : Measure SU2 => μ Set.univ) hν
    have hc : ν.haarScalarFactor su2HaarProb = 1 := by
      simpa [ENNReal.smul_def] using hu.symm
    rw [hc] at hν
    have hOne : (1 : ENNReal) • su2HaarProb = su2HaarProb := by
      ext s hs
      simp
    exact hν.trans hOne

namespace SU2FiniteDiskCellulation

/-- The fixed orientation used by an original edge coordinate. -/
def canonicalEdgeDart (C : SU2FiniteDiskCellulation) (e : C.Edge) :
    C.HalfEdge :=
  C.edgeDarts (e, false)

/-- The group value carried by an oriented half-edge.  The `false` dart uses
the stored physical edge coordinate and the reverse dart uses its inverse. -/
def edgeValue (C : SU2FiniteDiskCellulation) (U : C.Edge -> SU2)
    (h : C.HalfEdge) : SU2 :=
  if C.halfEdgeSide h = true then (U (C.edgeOfHalfEdge h))⁻¹
  else U (C.edgeOfHalfEdge h)

/-- Vertex gauge action on every original physical edge, expressed in the
cellulation's canonical (`false`) orientation. -/
def gaugeTransform (C : SU2FiniteDiskCellulation) (U : C.Edge -> SU2)
    (g : C.Vertex -> SU2) : C.Edge -> SU2 := fun e =>
  g (C.source (C.canonicalEdgeDart e)) * U e *
    (g (C.target (C.canonicalEdgeDart e)))⁻¹

/-- Gauge covariance holds on both orientations of every physical edge. -/
theorem edgeValue_gaugeTransform (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (g : C.Vertex -> SU2) (h : C.HalfEdge) :
    C.edgeValue (C.gaugeTransform U g) h =
      g (C.source h) * C.edgeValue U h * (g (C.target h))⁻¹ := by
  rcases hp : C.edgeDarts.symm h with ⟨e, b⟩
  have hh : h = C.edgeDarts (e, b) := by
    rw [← hp]
    exact (C.edgeDarts.apply_symm_apply h).symm
  subst h
  cases b
  · simp [edgeValue, edgeOfHalfEdge, halfEdgeSide, gaugeTransform,
      canonicalEdgeDart]
  · have hrev0 : C.reverse (C.edgeDarts (e, false)) =
        C.edgeDarts (e, true) := by
      simpa using C.reverse_edgeDarts e false
    have hrev1 : C.reverse (C.edgeDarts (e, true)) =
        C.edgeDarts (e, false) := by
      simpa using C.reverse_edgeDarts e true
    simp [edgeValue, edgeOfHalfEdge, halfEdgeSide, gaugeTransform,
      canonicalEdgeDart, target, hrev0, hrev1, mul_assoc]

end SU2FiniteDiskCellulation

namespace SU2FiniteDiskCellulation.RootedSpanningTree

variable {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree)

local instance : DecidableEq C.Edge := Classical.decEq C.Edge

/-- Edges outside the selected primal spanning tree. -/
abbrev ChordEdge := {e : C.Edge // e ∉ Set.range T.treeEdge}

/-- The exact partition of physical edges into the injective tree-edge image
and its complement. -/
def edgePartitionEquiv : (Fin T.n ⊕ T.ChordEdge) ≃ C.Edge :=
  (Equiv.sumCongr
      (Equiv.ofInjective T.treeEdge T.treeEdge_injective)
      (Equiv.refl T.ChordEdge)).trans
    (Equiv.Set.sumCompl (Set.range T.treeEdge))

@[simp]
theorem edgePartitionEquiv_apply_tree (i : Fin T.n) :
    T.edgePartitionEquiv (Sum.inl i) = T.treeEdge i := by
  rfl

@[simp]
theorem edgePartitionEquiv_apply_chord (e : T.ChordEdge) :
    T.edgePartitionEquiv (Sum.inr e) = e.1 := by
  rfl

/-- Split all original edge variables into tree-edge coordinates and chord
coordinates. -/
def edgeSplitEquiv :
    (C.Edge -> SU2) ≃ᵐ ((Fin T.n -> SU2) × (T.ChordEdge -> SU2)) :=
  let partition := T.edgePartitionEquiv
  (su2VertexRelabelEquiv partition).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin T.n ⊕ T.ChordEdge => SU2))

@[simp]
theorem edgeSplitEquiv_apply_tree (U : C.Edge -> SU2) (i : Fin T.n) :
    (T.edgeSplitEquiv U).1 i = U (T.treeEdge i) := by
  change U (T.edgePartitionEquiv (Sum.inl i)) = U (T.treeEdge i)
  rw [T.edgePartitionEquiv_apply_tree]

@[simp]
theorem edgeSplitEquiv_apply_chord (U : C.Edge -> SU2)
    (e : T.ChordEdge) :
    (T.edgeSplitEquiv U).2 e = U e.1 := by
  change U (T.edgePartitionEquiv (Sum.inr e)) = U e.1
  rw [T.edgePartitionEquiv_apply_chord]

/-- The raw edge partition preserves normalized product Haar. -/
theorem edgeSplitEquiv_measurePreserving :
    MeasurePreserving T.edgeSplitEquiv
      (su2FiniteProductHaar C.Edge)
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge)) := by
  let partition := T.edgePartitionEquiv
  have hrelabel : MeasurePreserving
      (su2VertexRelabelEquiv partition).symm
      (su2FiniteProductHaar C.Edge)
      (su2FiniteProductHaar (Fin T.n ⊕ T.ChordEdge)) :=
    MeasurePreserving.symm (su2VertexRelabelEquiv partition)
      (su2VertexRelabel_measurePreserving partition)
  have hsplit : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin T.n ⊕ T.ChordEdge => SU2))
      (su2FiniteProductHaar (Fin T.n ⊕ T.ChordEdge))
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge)) := by
    simpa [su2FiniteProductHaar] using
      (measurePreserving_sumPiEquivProdPi
        (fun _ : Fin T.n ⊕ T.ChordEdge => su2HaarProb))
  simpa [edgeSplitEquiv, partition] using hsplit.comp hrelabel

/-- Align each selected tree edge with its certified parent-to-child dart.
If the cellulation's canonical orientation is opposite, invert that one Haar
coordinate. -/
def treeOrientationEquiv :
    (Fin T.n -> SU2) ≃ᵐ (Fin T.n -> SU2) where
  toEquiv :=
    { toFun := fun u i =>
        if C.halfEdgeSide (T.treeDart i) = true then (u i)⁻¹ else u i
      invFun := fun u i =>
        if C.halfEdgeSide (T.treeDart i) = true then (u i)⁻¹ else u i
      left_inv := by
        intro u
        ext i
        by_cases hi : C.halfEdgeSide (T.treeDart i) = true <;>
          simp [hi]
      right_inv := by
        intro u
        ext i
        by_cases hi : C.halfEdgeSide (T.treeDart i) = true <;>
          simp [hi] }
  measurable_toFun := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    change Measurable (fun u : Fin T.n -> SU2 =>
      if C.halfEdgeSide (T.treeDart i) = true then (u i)⁻¹ else u i)
    by_cases hi : C.halfEdgeSide (T.treeDart i) = true
    · simpa only [hi, if_true, Function.comp_apply] using
        measurable_inv.comp (measurable_pi_apply i)
    · simpa only [hi, if_false] using (measurable_pi_apply i)
  measurable_invFun := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    change Measurable (fun u : Fin T.n -> SU2 =>
      if C.halfEdgeSide (T.treeDart i) = true then (u i)⁻¹ else u i)
    by_cases hi : C.halfEdgeSide (T.treeDart i) = true
    · simpa only [hi, if_true, Function.comp_apply] using
        measurable_inv.comp (measurable_pi_apply i)
    · simpa only [hi, if_false] using (measurable_pi_apply i)

/-- Orientation alignment preserves the tree-edge product Haar measure. -/
theorem treeOrientationEquiv_measurePreserving :
    MeasurePreserving T.treeOrientationEquiv
      (su2FiniteProductHaar (Fin T.n))
      (su2FiniteProductHaar (Fin T.n)) := by
  have hpi := measurePreserving_pi
    (fun _ : Fin T.n => su2HaarProb)
    (fun _ : Fin T.n => su2HaarProb)
    (f := fun i x =>
      if C.halfEdgeSide (T.treeDart i) = true then x⁻¹ else x)
    (fun i => by
      by_cases hi : C.halfEdgeSide (T.treeDart i) = true
      · simpa only [hi, if_true] using
          Measure.measurePreserving_inv su2HaarProb
      · simpa only [hi, if_false] using
          MeasurePreserving.id su2HaarProb)
  simpa [treeOrientationEquiv, su2FiniteProductHaar] using hpi

/-- Split all edges and orient the `V - 1` tree variables from parent to
child. -/
def orientedEdgeSplitEquiv :
    (C.Edge -> SU2) ≃ᵐ ((Fin T.n -> SU2) × (T.ChordEdge -> SU2)) :=
  T.edgeSplitEquiv.trans
    (MeasurableEquiv.prodCongr T.treeOrientationEquiv
      (MeasurableEquiv.refl (T.ChordEdge -> SU2)))

@[simp]
theorem orientedEdgeSplitEquiv_apply_tree (U : C.Edge -> SU2)
    (i : Fin T.n) :
    (T.orientedEdgeSplitEquiv U).1 i =
      if C.halfEdgeSide (T.treeDart i) = true then
        (U (T.treeEdge i))⁻¹ else U (T.treeEdge i) := by
  change
    (if C.halfEdgeSide (T.treeDart i) = true then
      ((T.edgeSplitEquiv U).1 i)⁻¹ else (T.edgeSplitEquiv U).1 i) = _
  rw [T.edgeSplitEquiv_apply_tree]

@[simp]
theorem orientedEdgeSplitEquiv_apply_chord (U : C.Edge -> SU2)
    (e : T.ChordEdge) :
    (T.orientedEdgeSplitEquiv U).2 e = U e.1 := by
  change (T.edgeSplitEquiv U).2 e = U e.1
  rw [T.edgeSplitEquiv_apply_chord]

theorem orientedEdgeSplitEquiv_measurePreserving :
    MeasurePreserving T.orientedEdgeSplitEquiv
      (su2FiniteProductHaar C.Edge)
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge)) := by
  have horient := T.treeOrientationEquiv_measurePreserving.prod
    (MeasurePreserving.id (su2FiniteProductHaar T.ChordEdge))
  exact horient.comp T.edgeSplitEquiv_measurePreserving

/-- Insert the fixed root value `1` before the `V - 1` oriented tree
increments. -/
def rootedIncrementConfiguration (a : Fin T.n -> SU2) :
    Fin (T.n + 1) -> SU2 :=
  Fin.cases 1 a

/-- Reconstruct all vertex potentials, with root fixed to `1`, by applying
the inverse of the triangular rooted-tree coordinate map. -/
def rootedPotential (a : Fin T.n -> SU2) : Fin (T.n + 1) -> SU2 :=
  T.order.coordinateEquiv.symm (T.rootedIncrementConfiguration a)

theorem measurable_rootedIncrementConfiguration :
    Measurable T.rootedIncrementConfiguration := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  refine Fin.cases measurable_const (fun j => ?_) i
  exact measurable_pi_apply j

theorem measurable_rootedPotential : Measurable T.rootedPotential := by
  exact T.order.coordinateEquiv.symm.measurable.comp
    T.measurable_rootedIncrementConfiguration

/-- The reconstructed potential realizes every oriented tree increment
exactly. -/
theorem rootedPotential_parent_inv_mul_child
    (a : Fin T.n -> SU2) (i : Fin T.n) :
    (T.rootedPotential a (T.order.parentIndex i))⁻¹ *
        T.rootedPotential a (Fin.succ i) = a i := by
  let y := T.rootedIncrementConfiguration a
  have h := congrFun (T.order.coordinateEquiv.apply_symm_apply y) (Fin.succ i)
  rw [T.order.coordinateEquiv_apply_succ] at h
  simpa [rootedPotential, y, rootedIncrementConfiguration] using h

/-- The vertex potential expressed on the literal cellulation vertex type. -/
def vertexPotential (a : Fin T.n -> SU2) (v : C.Vertex) : SU2 :=
  T.rootedPotential a (T.vertexOrder.symm v)

theorem measurable_vertexPotential (v : C.Vertex) :
    Measurable (fun a : Fin T.n -> SU2 => T.vertexPotential a v) := by
  exact (measurable_pi_apply (T.vertexOrder.symm v)).comp
    T.measurable_rootedPotential

/-- Gauge-transform every chord by the rooted potentials reconstructed from
the tree increments. -/
def gaugeChord (a : Fin T.n -> SU2) (u : T.ChordEdge -> SU2) :
    T.ChordEdge -> SU2 := fun e =>
  T.vertexPotential a (C.source (C.canonicalEdgeDart e.1)) * u e *
    (T.vertexPotential a (C.target (C.canonicalEdgeDart e.1)))⁻¹

/-- Inverse transformation on chord coordinates. -/
def ungaugeChord (a : Fin T.n -> SU2) (x : T.ChordEdge -> SU2) :
    T.ChordEdge -> SU2 := fun e =>
  (T.vertexPotential a (C.source (C.canonicalEdgeDart e.1)))⁻¹ * x e *
    T.vertexPotential a (C.target (C.canonicalEdgeDart e.1))

@[simp]
theorem ungaugeChord_gaugeChord (a : Fin T.n -> SU2)
    (u : T.ChordEdge -> SU2) :
    T.ungaugeChord a (T.gaugeChord a u) = u := by
  ext e
  simp [ungaugeChord, gaugeChord, mul_assoc]

@[simp]
theorem gaugeChord_ungaugeChord (a : Fin T.n -> SU2)
    (x : T.ChordEdge -> SU2) :
    T.gaugeChord a (T.ungaugeChord a x) = x := by
  ext e
  simp [ungaugeChord, gaugeChord, mul_assoc]

/-- The global triangular gauge shear on tree increments and all chord
variables. -/
def chordGaugeEquiv :
    ((Fin T.n -> SU2) × (T.ChordEdge -> SU2)) ≃ᵐ
      ((Fin T.n -> SU2) × (T.ChordEdge -> SU2)) where
  toEquiv :=
    { toFun := fun p => (p.1, T.gaugeChord p.1 p.2)
      invFun := fun p => (p.1, T.ungaugeChord p.1 p.2)
      left_inv := by
        rintro ⟨a, u⟩
        simp
      right_inv := by
        rintro ⟨a, x⟩
        simp }
  measurable_toFun := by
    refine measurable_fst.prodMk (measurable_pi_iff.mpr fun e => ?_)
    have hs : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) =>
          T.vertexPotential p.1
            (C.source (C.canonicalEdgeDart e.1))) :=
      (T.measurable_vertexPotential
        (C.source (C.canonicalEdgeDart e.1))).comp measurable_fst
    have hu : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) => p.2 e) :=
      (measurable_pi_apply e).comp measurable_snd
    have ht : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) =>
          T.vertexPotential p.1
            (C.target (C.canonicalEdgeDart e.1))) :=
      (T.measurable_vertexPotential
        (C.target (C.canonicalEdgeDart e.1))).comp measurable_fst
    simpa only [gaugeChord] using
      continuous_mul.measurable2 (continuous_mul.measurable2 hs hu)
        (measurable_inv.comp ht)
  measurable_invFun := by
    refine measurable_fst.prodMk (measurable_pi_iff.mpr fun e => ?_)
    have hs : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) =>
          T.vertexPotential p.1
            (C.source (C.canonicalEdgeDart e.1))) :=
      (T.measurable_vertexPotential
        (C.source (C.canonicalEdgeDart e.1))).comp measurable_fst
    have hx : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) => p.2 e) :=
      (measurable_pi_apply e).comp measurable_snd
    have ht : Measurable (fun p :
        (Fin T.n -> SU2) × (T.ChordEdge -> SU2) =>
          T.vertexPotential p.1
            (C.target (C.canonicalEdgeDart e.1))) :=
      (T.measurable_vertexPotential
        (C.target (C.canonicalEdgeDart e.1))).comp measurable_fst
    simpa only [ungaugeChord] using
      continuous_mul.measurable2
        (continuous_mul.measurable2 (measurable_inv.comp hs) hx) ht

/-- For fixed tree increments, the simultaneous left-right transformation of
all chords preserves their product Haar measure. -/
theorem gaugeChord_measurePreserving (a : Fin T.n -> SU2) :
    MeasurePreserving (T.gaugeChord a)
      (su2FiniteProductHaar T.ChordEdge)
      (su2FiniteProductHaar T.ChordEdge) := by
  let left : T.ChordEdge -> SU2 := fun e =>
    T.vertexPotential a (C.source (C.canonicalEdgeDart e.1))
  let right : T.ChordEdge -> SU2 := fun e =>
    (T.vertexPotential a (C.target (C.canonicalEdgeDart e.1)))⁻¹
  have hleft := measurePreserving_mul_left
    (su2FiniteProductHaar T.ChordEdge) left
  have hright := measurePreserving_mul_right
    (su2FiniteProductHaar T.ChordEdge) right
  simpa [gaugeChord, left, right, Function.comp_def] using
    hright.comp hleft

/-- The global chord shear preserves tree-product-Haar times chord-product-
Haar. -/
theorem chordGaugeEquiv_measurePreserving :
    MeasurePreserving T.chordGaugeEquiv
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge))
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge)) := by
  have hmeas : Measurable (Function.uncurry T.gaugeChord) := by
    exact T.chordGaugeEquiv.measurable_toFun.snd
  have hskew := (MeasurePreserving.id
      (su2FiniteProductHaar (Fin T.n))).skew_product
    (μc := su2FiniteProductHaar T.ChordEdge)
    (μd := su2FiniteProductHaar T.ChordEdge)
    (g := T.gaugeChord) hmeas
    (ae_of_all _ fun a => (T.gaugeChord_measurePreserving a).map_eq)
  simpa [chordGaugeEquiv] using hskew

/-- The requested edge-space equivalence: all original edge variables are
replaced by `V - 1` rooted tree coordinates and one coordinate for every
non-tree edge. -/
def globalEdgeGaugeEquiv :
    (C.Edge -> SU2) ≃ᵐ ((Fin T.n -> SU2) × (T.ChordEdge -> SU2)) :=
  T.orientedEdgeSplitEquiv.trans T.chordGaugeEquiv

@[simp]
theorem globalEdgeGaugeEquiv_apply_tree (U : C.Edge -> SU2)
    (i : Fin T.n) :
    (T.globalEdgeGaugeEquiv U).1 i =
      if C.halfEdgeSide (T.treeDart i) = true then
        (U (T.treeEdge i))⁻¹ else U (T.treeEdge i) := by
  simp [globalEdgeGaugeEquiv, chordGaugeEquiv]

/-- The first output block is literally the original edge value in each
certified parent-to-child orientation. -/
theorem globalEdgeGaugeEquiv_apply_tree_eq_edgeValue (U : C.Edge -> SU2)
    (i : Fin T.n) :
    (T.globalEdgeGaugeEquiv U).1 i = C.edgeValue U (T.treeDart i) := by
  rw [T.globalEdgeGaugeEquiv_apply_tree]
  rfl

@[simp]
theorem globalEdgeGaugeEquiv_apply_chord (U : C.Edge -> SU2)
    (e : T.ChordEdge) :
    (T.globalEdgeGaugeEquiv U).2 e =
      T.gaugeChord (T.globalEdgeGaugeEquiv U).1
        (fun c => U c.1) e := by
  change T.gaugeChord (T.orientedEdgeSplitEquiv U).1
      (T.orientedEdgeSplitEquiv U).2 e =
    T.gaugeChord (T.orientedEdgeSplitEquiv U).1 (fun c => U c.1) e
  congr 1

/-- Edge configuration with every tree edge fixed to the identity and every
chord equal to its reduced coordinate. -/
def gaugeFixedEdgeConfiguration (x : T.ChordEdge -> SU2) : C.Edge -> SU2 :=
  fun e => if he : e ∈ Set.range T.treeEdge then 1 else x ⟨e, he⟩

@[simp]
theorem gaugeFixedEdgeConfiguration_tree (x : T.ChordEdge -> SU2)
    (i : Fin T.n) :
    T.gaugeFixedEdgeConfiguration x (T.treeEdge i) = 1 := by
  simp [gaugeFixedEdgeConfiguration, Set.mem_range]

@[simp]
theorem gaugeFixedEdgeConfiguration_chord (x : T.ChordEdge -> SU2)
    (e : T.ChordEdge) :
    T.gaugeFixedEdgeConfiguration x e.1 = x e := by
  simp [gaugeFixedEdgeConfiguration, e.2]

/-- The global equivalence is genuine spanning-tree gauge fixing: applying
the reconstructed vertex gauge to the original edge configuration produces
exactly the configuration with tree edges equal to `1` and chord edges equal
to the second output block. -/
theorem gaugeTransform_eq_gaugeFixedEdgeConfiguration (U : C.Edge -> SU2) :
    C.gaugeTransform U
        (T.vertexPotential (T.globalEdgeGaugeEquiv U).1) =
      T.gaugeFixedEdgeConfiguration (T.globalEdgeGaugeEquiv U).2 := by
  funext e
  by_cases he : e ∈ Set.range T.treeEdge
  · rcases he with ⟨i, rfl⟩
    let a := (T.globalEdgeGaugeEquiv U).1
    let g : C.Vertex -> SU2 := T.vertexPotential a
    have ha : C.edgeValue U (T.treeDart i) = a i := by
      exact (T.globalEdgeGaugeEquiv_apply_tree_eq_edgeValue U i).symm
    have hinc := T.rootedPotential_parent_inv_mul_child a i
    have hedge := C.edgeValue_gaugeTransform U g (T.treeDart i)
    have hsource : g (C.source (T.treeDart i)) =
        T.rootedPotential a (T.order.parentIndex i) := by
      simp [g, vertexPotential]
    have htarget : g (C.target (T.treeDart i)) =
        T.rootedPotential a (Fin.succ i) := by
      simp [g, vertexPotential]
    have hone : C.edgeValue (C.gaugeTransform U g) (T.treeDart i) = 1 := by
      rw [hedge, hsource, htarget, ha, ← hinc]
      simp
    rw [T.gaugeFixedEdgeConfiguration_tree]
    change C.gaugeTransform U g (T.treeEdge i) = 1
    by_cases hs : C.halfEdgeSide (T.treeDart i) = true
    · have hinv : (C.gaugeTransform U g (T.treeEdge i))⁻¹ = 1 := by
        simpa [edgeValue, treeEdge, hs] using hone
      exact inv_eq_one.mp hinv
    · simpa [edgeValue, treeEdge, hs] using hone
  · let c : T.ChordEdge := ⟨e, he⟩
    simp only [gaugeFixedEdgeConfiguration, dif_neg he]
    change C.gaugeTransform U
        (T.vertexPotential (T.globalEdgeGaugeEquiv U).1) e =
      (T.globalEdgeGaugeEquiv U).2 c
    rw [T.globalEdgeGaugeEquiv_apply_chord U c]
    rfl

/-- The full edge-space equivalence preserves literal normalized product
Haar. -/
theorem globalEdgeGaugeEquiv_measurePreserving :
    MeasurePreserving T.globalEdgeGaugeEquiv
      (su2FiniteProductHaar C.Edge)
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge)) :=
  T.chordGaugeEquiv_measurePreserving.comp
    T.orientedEdgeSplitEquiv_measurePreserving

end SU2FiniteDiskCellulation.RootedSpanningTree

namespace SU2FiniteDiskCellulation

/-- Ordered holonomy of the first `n` darts in the `next`-orbit of `h`. -/
def dartHolonomy (C : SU2FiniteDiskCellulation) (U : C.Edge -> SU2)
    (h : C.HalfEdge) : Nat -> SU2
  | 0 => 1
  | n + 1 => C.dartHolonomy U h n * C.edgeValue U ((C.next ^ n) h)

theorem source_next_pow_succ (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) (n : Nat) :
    C.source ((C.next ^ (n + 1)) h) =
      C.target ((C.next ^ n) h) := by
  simpa [pow_succ'] using C.next_source ((C.next ^ n) h)

/-- Open-path covariance: the only uncancelled gauge factors occur at the two
endpoints of the ordered dart path. -/
theorem dartHolonomy_gaugeTransform (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (g : C.Vertex -> SU2)
    (h : C.HalfEdge) (n : Nat) :
    C.dartHolonomy (C.gaugeTransform U g) h n =
      g (C.source h) * C.dartHolonomy U h n *
        (g (C.source ((C.next ^ n) h)))⁻¹ := by
  induction n with
  | zero => simp [dartHolonomy]
  | succ n ih =>
      rw [dartHolonomy, dartHolonomy, ih,
        C.edgeValue_gaugeTransform U g ((C.next ^ n) h)]
      rw [C.source_next_pow_succ h n]
      simp [mul_assoc]

/-- A closed dart orbit transforms by conjugation at its base vertex. -/
theorem dartHolonomy_gaugeTransform_of_closed
    (C : SU2FiniteDiskCellulation) (U : C.Edge -> SU2)
    (g : C.Vertex -> SU2) (h : C.HalfEdge) (n : Nat)
    (hclosed : (C.next ^ n) h = h) :
    C.dartHolonomy (C.gaugeTransform U g) h n =
      g (C.source h) * C.dartHolonomy U h n *
        (g (C.source h))⁻¹ := by
  rw [C.dartHolonomy_gaugeTransform U g h n, hclosed]

end SU2FiniteDiskCellulation

/-- A connected finite disk cellulation equipped with the well-formed primal
and facial data needed by the unreduced edge model.  The older cellulation
record intentionally did not assert that every bounded face had a boundary;
this record makes that physical condition explicit and gives a once-around
enumeration rather than silently using an arbitrary multiple of a face
cycle. -/
structure SU2EdgeConnectedDiskCellulation where
  connected : SU2ConnectedDiskCellulation
  primal_connected : connected.cellulation.primalGraph.Connected
  faceBoundaryLength : connected.cellulation.Face -> Nat
  faceBoundaryLength_pos : ∀ f, 0 < faceBoundaryLength f
  faceBoundaryStart : connected.cellulation.Face ->
    connected.cellulation.HalfEdge
  faceBoundaryStart_face : ∀ f,
    connected.cellulation.face (faceBoundaryStart f) = some f
  faceBoundary_closed : ∀ f,
    (connected.cellulation.next ^ faceBoundaryLength f)
      (faceBoundaryStart f) = faceBoundaryStart f
  faceBoundary_complete : ∀ f h,
    connected.cellulation.face h = some f ->
      ∃ k : Fin (faceBoundaryLength f),
        (connected.cellulation.next ^ (k : Nat))
          (faceBoundaryStart f) = h
  faceBoundary_nodup : ∀ f (i j : Fin (faceBoundaryLength f)),
    (connected.cellulation.next ^ (i : Nat)) (faceBoundaryStart f) =
      (connected.cellulation.next ^ (j : Nat)) (faceBoundaryStart f) ->
        i = j

namespace SU2EdgeConnectedDiskCellulation

local instance edgeDecidableEq (P : SU2EdgeConnectedDiskCellulation) :
    DecidableEq P.connected.cellulation.Edge :=
  Classical.decEq P.connected.cellulation.Edge

/-- Original-edge configuration space of the well-formed cellulation. -/
abbrev EdgeConfiguration (P : SU2EdgeConnectedDiskCellulation) :=
  P.connected.cellulation.Edge -> SU2

/-- The once-around facial holonomy, simultaneously defined for every
bounded face from the certified boundary enumeration. -/
def faceHolonomy (P : SU2EdgeConnectedDiskCellulation)
    (U : P.EdgeConfiguration) (f : P.connected.cellulation.Face) : SU2 :=
  P.connected.cellulation.dartHolonomy U (P.faceBoundaryStart f)
    (P.faceBoundaryLength f)

/-- Every facial holonomy transforms by conjugation at its chosen boundary
basepoint. -/
theorem faceHolonomy_gaugeTransform
    (P : SU2EdgeConnectedDiskCellulation) (U : P.EdgeConfiguration)
    (g : P.connected.cellulation.Vertex -> SU2)
    (f : P.connected.cellulation.Face) :
    P.faceHolonomy (P.connected.cellulation.gaugeTransform U g) f =
      g (P.connected.cellulation.source (P.faceBoundaryStart f)) *
        P.faceHolonomy U f *
      (g (P.connected.cellulation.source (P.faceBoundaryStart f)))⁻¹ := by
  exact P.connected.cellulation.dartHolonomy_gaugeTransform_of_closed
    U g (P.faceBoundaryStart f) (P.faceBoundaryLength f)
    (P.faceBoundary_closed f)

/-- Simultaneous version: the complete vector of face holonomies is changed
only by one conjugation per chosen face basepoint. -/
theorem allFaceHolonomies_gaugeTransform
    (P : SU2EdgeConnectedDiskCellulation) (U : P.EdgeConfiguration)
    (g : P.connected.cellulation.Vertex -> SU2) :
    (fun f => P.faceHolonomy (P.connected.cellulation.gaugeTransform U g) f) =
      fun f =>
        g (P.connected.cellulation.source (P.faceBoundaryStart f)) *
          P.faceHolonomy U f *
        (g (P.connected.cellulation.source (P.faceBoundaryStart f)))⁻¹ := by
  funext f
  exact P.faceHolonomy_gaugeTransform U g f

/-- The underlying primal-connected cellulation has a certified rooted
spanning tree and hence the global edge-space equivalence. -/
theorem nonempty_rootedSpanningTree (P : SU2EdgeConnectedDiskCellulation) :
    Nonempty P.connected.cellulation.RootedSpanningTree :=
  P.connected.cellulation.exists_rootedSpanningTree_of_primal_connected
    P.primal_connected

/-- Every well-formed connected edge cellulation admits an explicit global
edge gauge equivalence preserving product Haar. -/
theorem exists_globalEdgeGaugeEquiv_measurePreserving
    (P : SU2EdgeConnectedDiskCellulation) :
    ∃ T : P.connected.cellulation.RootedSpanningTree,
      MeasurePreserving T.globalEdgeGaugeEquiv
        (su2FiniteProductHaar P.connected.cellulation.Edge)
        ((su2FiniteProductHaar (Fin T.n)).prod
          (su2FiniteProductHaar T.ChordEdge)) := by
  obtain ⟨T⟩ := P.nonempty_rootedSpanningTree
  exact ⟨T, T.globalEdgeGaugeEquiv_measurePreserving⟩

/-- Unreduced heat-kernel density on all original edge variables. -/
def edgeHeatKernelDensity (P : SU2EdgeConnectedDiskCellulation)
    (U : P.EdgeConfiguration) : Complex :=
  ∏ f : P.connected.cellulation.Face,
    su2HeatKernel (P.connected.cellulation.faceArea f) (P.faceHolonomy U f)

/-- The full edge density is gauge invariant because every facial holonomy is
conjugated and the heat kernel is a class function. -/
theorem edgeHeatKernelDensity_gaugeTransform
    (P : SU2EdgeConnectedDiskCellulation) (U : P.EdgeConfiguration)
    (g : P.connected.cellulation.Vertex -> SU2) :
    P.edgeHeatKernelDensity (P.connected.cellulation.gaugeTransform U g) =
      P.edgeHeatKernelDensity U := by
  unfold edgeHeatKernelDensity
  apply Finset.prod_congr rfl
  intro f _
  rw [P.faceHolonomy_gaugeTransform U g f]
  exact su2HeatKernel_conj_invariant
    (P.connected.cellulation.faceArea f)
    (g (P.connected.cellulation.source (P.faceBoundaryStart f)))
    (P.faceHolonomy U f)

/-- Density on the chord variables after fixing every tree edge to `1`. -/
def chordGaugeFixedDensity (P : SU2EdgeConnectedDiskCellulation)
    (T : P.connected.cellulation.RootedSpanningTree)
    (x : T.ChordEdge -> SU2) : Complex :=
  P.edgeHeatKernelDensity (T.gaugeFixedEdgeConfiguration x)

/-- After inverse substitution through the global edge equivalence, the
unreduced density is independent of all `V - 1` tree/gauge coordinates. -/
theorem edgeHeatKernelDensity_globalEdgeFactorization
    (P : SU2EdgeConnectedDiskCellulation)
    (T : P.connected.cellulation.RootedSpanningTree)
    (p : (Fin T.n -> SU2) × (T.ChordEdge -> SU2)) :
    P.edgeHeatKernelDensity (T.globalEdgeGaugeEquiv.symm p) =
      P.chordGaugeFixedDensity T p.2 := by
  let U := T.globalEdgeGaugeEquiv.symm p
  let g : P.connected.cellulation.Vertex -> SU2 := T.vertexPotential p.1
  have hcoords := T.globalEdgeGaugeEquiv.apply_symm_apply p
  have hfixed := T.gaugeTransform_eq_gaugeFixedEdgeConfiguration U
  change P.edgeHeatKernelDensity U =
    P.edgeHeatKernelDensity (T.gaugeFixedEdgeConfiguration p.2)
  have hgauge : P.edgeHeatKernelDensity
      (P.connected.cellulation.gaugeTransform U g) =
        P.edgeHeatKernelDensity U :=
    P.edgeHeatKernelDensity_gaugeTransform U g
  rw [hcoords] at hfixed
  exact hgauge.symm.trans (congrArg P.edgeHeatKernelDensity hfixed)

/-- Integral of the unreduced density over every original physical edge. -/
def unreducedEdgeIntegral (P : SU2EdgeConnectedDiskCellulation) : Complex :=
  ∫ U, P.edgeHeatKernelDensity U
    ∂su2FiniteProductHaar P.connected.cellulation.Edge

/-- Integral after global spanning-tree gauge fixing. -/
def chordGaugeFixedIntegral (P : SU2EdgeConnectedDiskCellulation)
    (T : P.connected.cellulation.RootedSpanningTree) : Complex :=
  ∫ x, P.chordGaugeFixedDensity T x
    ∂su2FiniteProductHaar T.ChordEdge

/-- **Unreduced-edge reduction.**  For every certified rooted spanning tree,
the original `SU2^Edge` Haar integral is exactly the chord integral; all
`V - 1` gauge coordinates have been removed, with no residual volume factor
because Haar is normalized. -/
theorem unreducedEdgeIntegral_eq_chordGaugeFixedIntegral
    (P : SU2EdgeConnectedDiskCellulation)
    (T : P.connected.cellulation.RootedSpanningTree) :
    P.unreducedEdgeIntegral = P.chordGaugeFixedIntegral T := by
  have hinv : MeasurePreserving T.globalEdgeGaugeEquiv.symm
      ((su2FiniteProductHaar (Fin T.n)).prod
        (su2FiniteProductHaar T.ChordEdge))
      (su2FiniteProductHaar P.connected.cellulation.Edge) :=
    MeasurePreserving.symm T.globalEdgeGaugeEquiv
      T.globalEdgeGaugeEquiv_measurePreserving
  calc
    P.unreducedEdgeIntegral =
        ∫ p, P.edgeHeatKernelDensity (T.globalEdgeGaugeEquiv.symm p)
          ∂((su2FiniteProductHaar (Fin T.n)).prod
            (su2FiniteProductHaar T.ChordEdge)) := by
      exact (hinv.integral_comp' P.edgeHeatKernelDensity).symm
    _ = ∫ p, P.chordGaugeFixedDensity T p.2
          ∂((su2FiniteProductHaar (Fin T.n)).prod
            (su2FiniteProductHaar T.ChordEdge)) := by
      apply integral_congr_ae
      exact ae_of_all _ (P.edgeHeatKernelDensity_globalEdgeFactorization T)
    _ = ∫ x, P.chordGaugeFixedDensity T x
          ∂su2FiniteProductHaar T.ChordEdge := by
      rw [integral_fun_snd]
      simp
    _ = P.chordGaugeFixedIntegral T := rfl

end SU2EdgeConnectedDiskCellulation

end Lean2dYangMills
