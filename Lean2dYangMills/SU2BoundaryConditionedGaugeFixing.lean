import Lean2dYangMills.SU2GlobalEdgeGaugeFixing
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod

/-!
# Boundary-conditioned global gauge fixing

The fully integrated edge functional is a scalar.  The physical disk
amplitude instead retains the exterior holonomy.  This module introduces the
missing type-correct boundary object.  It begins with a certified once-around
exterior cycle and then exposes that holonomy as an explicit Haar coordinate
of a compatible gauge-fixed chord chart.

No equality with the recursive elimination amplitude is postulated here.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

set_option maxHeartbeats 1200000

/-- A well-formed edge cellulation whose exterior face is also supplied with
one once-around enumeration.  Physical edge injectivity is stronger than dart
injectivity: it excludes traversing the two orientations of one edge at two
different positions of the exterior word. -/
structure SU2BoundaryDiskCellulation extends SU2EdgeConnectedDiskCellulation where
  exteriorBoundaryLength : Nat
  exteriorBoundaryLength_pos : 0 < exteriorBoundaryLength
  exteriorBoundaryStart : connected.cellulation.HalfEdge
  exteriorBoundaryStart_face :
    connected.cellulation.face exteriorBoundaryStart = none
  exteriorBoundary_closed :
    (connected.cellulation.next ^ exteriorBoundaryLength)
      exteriorBoundaryStart = exteriorBoundaryStart
  exteriorBoundary_complete : ∀ h,
    connected.cellulation.face h = none ->
      ∃ k : Fin exteriorBoundaryLength,
        (connected.cellulation.next ^ (k : Nat)) exteriorBoundaryStart = h
  exteriorBoundary_edge_injective :
    Function.Injective (fun k : Fin exteriorBoundaryLength =>
      connected.cellulation.edgeOfHalfEdge
        ((connected.cellulation.next ^ (k : Nat)) exteriorBoundaryStart))

namespace SU2FiniteDiskCellulation

/-- Reading a path from its first dart agrees with the accumulator-oriented
definition used by `dartHolonomy`. -/
theorem dartHolonomy_succ_start (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (h : C.HalfEdge) (n : Nat) :
    C.dartHolonomy U h (n + 1) =
      C.edgeValue U h * C.dartHolonomy U (C.next h) n := by
  induction n with
  | zero => simp [dartHolonomy]
  | succ n ih =>
      rw [dartHolonomy, ih, dartHolonomy]
      have hpow : (C.next ^ (n + 1)) h = (C.next ^ n) (C.next h) := by
        simp [pow_succ]
      rw [hpow, mul_assoc]

/-- Measurability of an oriented edge value in a measurable family of edge
configurations. -/
theorem measurable_edgeValue_comp (C : SU2FiniteDiskCellulation)
    {X : Type} [MeasurableSpace X] (U : X -> C.Edge -> SU2)
    (hU : Measurable U) (h : C.HalfEdge) :
    Measurable (fun x => C.edgeValue (U x) h) := by
  unfold edgeValue
  split
  · exact measurable_inv.comp
      ((measurable_pi_apply (C.edgeOfHalfEdge h)).comp hU)
  · exact (measurable_pi_apply (C.edgeOfHalfEdge h)).comp hU

/-- Measurability of every finite path holonomy. -/
theorem measurable_dartHolonomy_comp (C : SU2FiniteDiskCellulation)
    {X : Type} [MeasurableSpace X] (U : X -> C.Edge -> SU2)
    (hU : Measurable U) (h : C.HalfEdge) (n : Nat) :
    Measurable (fun x => C.dartHolonomy (U x) h n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact continuous_mul.measurable2 ih
        (C.measurable_edgeValue_comp U hU ((C.next ^ n) h))

/-- Two configurations with equal oriented values along a finite path have
equal path holonomy. -/
theorem dartHolonomy_congr (C : SU2FiniteDiskCellulation)
    (U V : C.Edge -> SU2) (h : C.HalfEdge) (n : Nat)
    (heq : ∀ k : Fin n,
      C.edgeValue U ((C.next ^ (k : Nat)) h) =
        C.edgeValue V ((C.next ^ (k : Nat)) h)) :
    C.dartHolonomy U h n = C.dartHolonomy V h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dartHolonomy, dartHolonomy]
      have hprefix := ih (fun k => heq ⟨k, Nat.lt_succ_of_lt k.isLt⟩)
      rw [hprefix]
      exact congrArg _ (heq ⟨n, Nat.lt_succ_self n⟩)

end SU2FiniteDiskCellulation

namespace SU2RootedTreeOrder

/-- The rooted-tree coordinate change leaves the root coordinate unchanged. -/
theorem coordinateEquiv_apply_zero : {n : Nat} ->
    (tree : SU2RootedTreeOrder n) -> (x : Fin (n + 1) -> SU2) ->
      tree.coordinateEquiv x 0 = x 0
  | 0, .root, _ => rfl
  | n + 1, .grow tree parent, x => by
      have hzero : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
      rw [hzero, coordinateEquiv_grow_apply_castSucc]
      exact tree.coordinateEquiv_apply_zero _

end SU2RootedTreeOrder

namespace SU2FiniteDiskCellulation.RootedSpanningTree

/-- The reconstructed potential is normalized to one at the root. -/
theorem rootedPotential_root
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree)
    (a : Fin T.n -> SU2) : T.rootedPotential a 0 = 1 := by
  have h := congrFun
    (T.order.coordinateEquiv.apply_symm_apply
      (T.rootedIncrementConfiguration a)) 0
  rw [T.order.coordinateEquiv_apply_zero] at h
  simpa [rootedPotential, rootedIncrementConfiguration] using h

end SU2FiniteDiskCellulation.RootedSpanningTree

/-- Split one selected coordinate from a finite SU(2) configuration, placing
the remaining coordinates first and the selected coordinate second. -/
def su2PiSplitAtEquiv {I : Type} [Fintype I] [DecidableEq I] (i : I) :
    (I -> SU2) ≃ᵐ ({j : I // j ≠ i} -> SU2) × SU2 :=
  (Homeomorph.funSplitAt SU2 i).toMeasurableEquiv.trans
    MeasurableEquiv.prodComm

@[simp]
theorem su2PiSplitAtEquiv_apply_fst {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (x : I -> SU2) (j : {j : I // j ≠ i}) :
    (su2PiSplitAtEquiv i x).1 j = x j := by
  rfl

@[simp]
theorem su2PiSplitAtEquiv_apply_snd {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (x : I -> SU2) :
    (su2PiSplitAtEquiv i x).2 = x i := by
  rfl

@[simp]
theorem su2PiSplitAtEquiv_symm_apply_other
    {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (r : {j : I // j ≠ i} -> SU2) (u : SU2)
    (j : {j : I // j ≠ i}) :
    (su2PiSplitAtEquiv i).symm (r, u) j = r j := by
  have h := (su2PiSplitAtEquiv i).apply_symm_apply (r, u)
  exact congrFun (congrArg Prod.fst h) j

@[simp]
theorem su2PiSplitAtEquiv_symm_apply_selected
    {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (r : {j : I // j ≠ i} -> SU2) (u : SU2) :
    (su2PiSplitAtEquiv i).symm (r, u) i = u := by
  have h := (su2PiSplitAtEquiv i).apply_symm_apply (r, u)
  exact congrArg Prod.snd h

/-- The coordinate split preserves the literal finite product Haar measure. -/
theorem su2PiSplitAtEquiv_measurePreserving
    {I : Type} [Fintype I] [DecidableEq I] (i : I) :
    MeasurePreserving (su2PiSplitAtEquiv i)
      (su2FiniteProductHaar I)
      ((su2FiniteProductHaar {j : I // j ≠ i}).prod su2HaarProb) := by
  let e : Option {j : I // j ≠ i} ≃ I := Equiv.optionSubtypeNe i
  have hrelabel :=
    (measurePreserving_piCongrLeft (fun _ : I => su2HaarProb) e).symm
  have hoptionInv : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option {j : I // j ≠ i} => SU2)).symm
      ((su2FiniteProductHaar {j : I // j ≠ i}).prod su2HaarProb)
      (su2FiniteProductHaar (Option {j : I // j ≠ i})) := by
    refine ⟨(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : I // j ≠ i} => SU2)).symm.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {j : I // j ≠ i} => su2HaarProb)
  simpa [su2PiSplitAtEquiv, Homeomorph.funSplitAt,
    Homeomorph.piSplitAt, MeasurableEquiv.prodComm,
    MeasurableEquiv.piCongrLeft, MeasurableEquiv.piOptionEquivProd,
    Equiv.optionSubtypeNe] using hoptionInv.symm.comp hrelabel

namespace SU2BoundaryDiskCellulation

abbrev EdgeConfiguration (P : SU2BoundaryDiskCellulation) :=
  P.connected.cellulation.Edge -> SU2

/-- Exterior holonomy retained by the conditioned disk functional. -/
def exteriorHolonomy (P : SU2BoundaryDiskCellulation)
    (U : P.EdgeConfiguration) : SU2 :=
  P.connected.cellulation.dartHolonomy U P.exteriorBoundaryStart
    P.exteriorBoundaryLength

/-- The exterior holonomy transforms by conjugation at its chosen basepoint. -/
theorem exteriorHolonomy_gaugeTransform
    (P : SU2BoundaryDiskCellulation) (U : P.EdgeConfiguration)
    (g : P.connected.cellulation.Vertex -> SU2) :
    P.exteriorHolonomy (P.connected.cellulation.gaugeTransform U g) =
      g (P.connected.cellulation.source P.exteriorBoundaryStart) *
        P.exteriorHolonomy U *
        (g (P.connected.cellulation.source P.exteriorBoundaryStart))⁻¹ := by
  exact P.connected.cellulation.dartHolonomy_gaugeTransform_of_closed
    U g P.exteriorBoundaryStart P.exteriorBoundaryLength
      P.exteriorBoundary_closed

/-- The physical edge carrying the first exterior dart. -/
def exteriorAnchorEdge (P : SU2BoundaryDiskCellulation) :
    P.connected.cellulation.Edge :=
  P.connected.cellulation.edgeOfHalfEdge P.exteriorBoundaryStart

/-- Zeroth position in the nonempty exterior word. -/
def exteriorBoundaryZero (P : SU2BoundaryDiskCellulation) :
    Fin P.exteriorBoundaryLength :=
  ⟨0, P.exteriorBoundaryLength_pos⟩

/-- No later dart in the certified exterior word uses the anchor edge. -/
theorem exteriorAnchorEdge_ne_later
    (P : SU2BoundaryDiskCellulation)
    (k : Fin P.exteriorBoundaryLength) (hk : k ≠ P.exteriorBoundaryZero) :
    P.connected.cellulation.edgeOfHalfEdge
        ((P.connected.cellulation.next ^ (k : Nat))
          P.exteriorBoundaryStart) ≠
      P.exteriorAnchorEdge := by
  intro h
  apply hk
  apply P.exteriorBoundary_edge_injective
  simpa [exteriorAnchorEdge, exteriorBoundaryZero] using h

/-- A rooted spanning-tree chart compatible with the exterior coordinate.
The root is the exterior basepoint and the anchor edge is retained as a chord.
Existence for every physical disk is the remaining combinatorial tree--cotree
problem; once such a chart is supplied, the conditioned measure theory below
contains no further topological assumption. -/
structure BoundaryGaugeChart (P : SU2BoundaryDiskCellulation) where
  tree : P.connected.cellulation.RootedSpanningTree
  root_eq_exterior_source :
    tree.vertexOrder 0 =
      P.connected.cellulation.source P.exteriorBoundaryStart
  anchor_not_tree : P.exteriorAnchorEdge ∉ Set.range tree.treeEdge

namespace BoundaryGaugeChart

variable {P : SU2BoundaryDiskCellulation} (B : P.BoundaryGaugeChart)

abbrev ChordEdge := B.tree.ChordEdge

/-- The distinguished chord that will be replaced by exterior holonomy. -/
def boundaryChord : B.ChordEdge :=
  ⟨P.exteriorAnchorEdge, B.anchor_not_tree⟩

abbrev OtherChord := {e : B.ChordEdge // e ≠ B.boundaryChord}

local instance edgeDecidableEq :
    DecidableEq P.connected.cellulation.Edge := Classical.decEq _

local instance chordEdgeDecidableEq : DecidableEq B.ChordEdge := Classical.decEq _

/-- Euler's disk relation and the spanning-tree edge partition leave exactly
one chord coordinate per bounded face. -/
theorem card_chordEdge_eq_card_face :
    Fintype.card B.ChordEdge =
      Fintype.card P.connected.cellulation.Face := by
  have hV : Fintype.card P.connected.cellulation.Vertex = B.tree.n + 1 := by
    simpa using Fintype.card_congr B.tree.vertexOrder.symm
  have hE : Fintype.card P.connected.cellulation.Edge =
      B.tree.n + Fintype.card B.ChordEdge := by
    calc
      Fintype.card P.connected.cellulation.Edge =
          Fintype.card (Fin B.tree.n ⊕ B.ChordEdge) :=
        Fintype.card_congr B.tree.edgePartitionEquiv.symm
      _ = B.tree.n + Fintype.card B.ChordEdge := by simp
  have hEuler := P.connected.cellulation.euler_disk
  rw [hV, hE] at hEuler
  omega

/-- After retaining the exterior coordinate, the number of variables still
integrated is exactly `F - 1`, matching a face-elimination schedule. -/
theorem card_otherChord_eq_card_face_sub_one :
    Fintype.card B.OtherChord =
      Fintype.card P.connected.cellulation.Face - 1 := by
  rw [← B.card_chordEdge_eq_card_face]
  classical
  simp [OtherChord, Fintype.card_subtype_compl]

/-- Gauge-fixed exterior holonomy as a function of all chord coordinates. -/
def chordExteriorHolonomy (x : B.ChordEdge -> SU2) : SU2 :=
  P.exteriorHolonomy (B.tree.gaugeFixedEdgeConfiguration x)

/-- Split the anchor chord from all other chord variables. -/
def chordSplitEquiv :
    (B.ChordEdge -> SU2) ≃ᵐ (B.OtherChord -> SU2) × SU2 :=
  su2PiSplitAtEquiv B.boundaryChord

/-- Reinsert all non-anchor chords while setting the anchor coordinate to one. -/
def chordWithAnchorOne (r : B.OtherChord -> SU2) : B.ChordEdge -> SU2 :=
  B.chordSplitEquiv.symm (r, 1)

@[simp]
theorem chordWithAnchorOne_other (r : B.OtherChord -> SU2)
    (e : B.OtherChord) :
    B.chordWithAnchorOne r e = r e := by
  exact su2PiSplitAtEquiv_symm_apply_other B.boundaryChord r 1 e

@[simp]
theorem chordWithAnchorOne_boundary (r : B.OtherChord -> SU2) :
    B.chordWithAnchorOne r B.boundaryChord = 1 := by
  exact su2PiSplitAtEquiv_symm_apply_selected B.boundaryChord r 1

/-- Tail of the exterior word after removing its first, anchor-edge factor. -/
def chordExteriorTail (r : B.OtherChord -> SU2) : SU2 :=
  P.connected.cellulation.dartHolonomy
    (B.tree.gaugeFixedEdgeConfiguration (B.chordWithAnchorOne r))
    (P.connected.cellulation.next P.exteriorBoundaryStart)
    (P.exteriorBoundaryLength - 1)

theorem measurable_gaugeFixedEdgeConfiguration :
    Measurable B.tree.gaugeFixedEdgeConfiguration := by
  refine measurable_pi_iff.mpr (fun e => ?_)
  unfold SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration
  split
  · exact measurable_const
  · exact measurable_pi_apply _

theorem measurable_chordWithAnchorOne : Measurable B.chordWithAnchorOne := by
  exact B.chordSplitEquiv.symm.measurable.comp
    (measurable_id.prodMk measurable_const)

theorem measurable_chordExteriorTail : Measurable B.chordExteriorTail := by
  apply P.connected.cellulation.measurable_dartHolonomy_comp
  exact B.measurable_gaugeFixedEdgeConfiguration.comp
    B.measurable_chordWithAnchorOne

/-- Replacing only the anchor coordinate by one leaves every other physical
edge of the gauge-fixed configuration unchanged. -/
theorem gaugeFixed_chordWithAnchorOne_eq_of_ne_anchor
    (x : B.ChordEdge -> SU2)
    {e : P.connected.cellulation.Edge} (he : e ≠ P.exteriorAnchorEdge) :
    B.tree.gaugeFixedEdgeConfiguration
        (B.chordWithAnchorOne (B.chordSplitEquiv x).1) e =
      B.tree.gaugeFixedEdgeConfiguration x e := by
  by_cases ht : e ∈ Set.range B.tree.treeEdge
  · simp [SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
      ht]
  · let c : B.ChordEdge := ⟨e, ht⟩
    have hc : c ≠ B.boundaryChord := by
      intro h
      apply he
      exact congrArg Subtype.val h
    let oc : B.OtherChord := ⟨c, hc⟩
    simp only [SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
      ht, dite_false]
    change B.chordWithAnchorOne (B.chordSplitEquiv x).1 c = x c
    calc
      B.chordWithAnchorOne (B.chordSplitEquiv x).1 c =
          (B.chordSplitEquiv x).1 oc := by
            exact B.chordWithAnchorOne_other _ oc
      _ = x c := by
        exact su2PiSplitAtEquiv_apply_fst B.boundaryChord x oc

/-- The tail is independent of the anchor coordinate. -/
theorem chordExteriorTail_eq
    (x : B.ChordEdge -> SU2) :
    P.connected.cellulation.dartHolonomy
        (B.tree.gaugeFixedEdgeConfiguration x)
        (P.connected.cellulation.next P.exteriorBoundaryStart)
        (P.exteriorBoundaryLength - 1) =
      B.chordExteriorTail (B.chordSplitEquiv x).1 := by
  unfold chordExteriorTail
  apply P.connected.cellulation.dartHolonomy_congr
  intro k
  have hk : (k : Nat) < P.exteriorBoundaryLength - 1 := k.isLt
  have hklt : (k : Nat) + 1 < P.exteriorBoundaryLength := by
    have hpos := P.exteriorBoundaryLength_pos
    omega
  let j : Fin P.exteriorBoundaryLength := ⟨(k : Nat) + 1, hklt⟩
  have hj0 : j ≠ P.exteriorBoundaryZero := by
    intro h
    have := congrArg Fin.val h
    simp [j, exteriorBoundaryZero] at this
  have hedge :
      P.connected.cellulation.edgeOfHalfEdge
          ((P.connected.cellulation.next ^ (k : Nat))
            (P.connected.cellulation.next P.exteriorBoundaryStart)) ≠
        P.exteriorAnchorEdge := by
    have hpow :
        (P.connected.cellulation.next ^ (k : Nat))
            (P.connected.cellulation.next P.exteriorBoundaryStart) =
          (P.connected.cellulation.next ^ ((k : Nat) + 1))
            P.exteriorBoundaryStart := by
      simp [pow_succ]
    rw [hpow]
    exact P.exteriorAnchorEdge_ne_later j hj0
  unfold SU2FiniteDiskCellulation.edgeValue
  split
  · rw [B.gaugeFixed_chordWithAnchorOne_eq_of_ne_anchor x hedge]
  · rw [B.gaugeFixed_chordWithAnchorOne_eq_of_ne_anchor x hedge]

/-- The exterior holonomy is the oriented anchor chord followed by a tail
depending only on the other chords. -/
theorem chordExteriorHolonomy_eq_anchor_mul_tail
    (x : B.ChordEdge -> SU2) :
    B.chordExteriorHolonomy x =
      (if P.connected.cellulation.halfEdgeSide P.exteriorBoundaryStart = true
        then (x B.boundaryChord)⁻¹ else x B.boundaryChord) *
        B.chordExteriorTail (B.chordSplitEquiv x).1 := by
  unfold chordExteriorHolonomy SU2BoundaryDiskCellulation.exteriorHolonomy
  have hlen : P.exteriorBoundaryLength =
      (P.exteriorBoundaryLength - 1) + 1 := by
    have hpos := P.exteriorBoundaryLength_pos
    omega
  rw [hlen, P.connected.cellulation.dartHolonomy_succ_start]
  rw [B.chordExteriorTail_eq x]
  unfold SU2FiniteDiskCellulation.edgeValue boundaryChord exteriorAnchorEdge
  have hanchor :
      B.tree.gaugeFixedEdgeConfiguration x P.exteriorAnchorEdge =
        x B.boundaryChord := by
    simpa [boundaryChord, SU2BoundaryDiskCellulation.exteriorAnchorEdge] using
      B.tree.gaugeFixedEdgeConfiguration_chord x B.boundaryChord
  by_cases hs :
      P.connected.cellulation.halfEdgeSide P.exteriorBoundaryStart = true
  · simp only [hs, if_pos, inv_inj, mul_right_cancel_iff]
    simpa [boundaryChord, SU2BoundaryDiskCellulation.exteriorAnchorEdge] using
      B.tree.gaugeFixedEdgeConfiguration_chord x B.boundaryChord
  · simp only [hs, mul_right_cancel_iff]
    simpa [boundaryChord, SU2BoundaryDiskCellulation.exteriorAnchorEdge] using
      B.tree.gaugeFixedEdgeConfiguration_chord x B.boundaryChord

/-- Replace the anchor chord by the exterior holonomy while retaining every
other chord.  The inverse is explicit on both possible orientations of the
anchor dart. -/
def boundaryHolonomyShearEquiv :
    ((B.OtherChord -> SU2) × SU2) ≃ᵐ ((B.OtherChord -> SU2) × SU2) where
  toEquiv :=
    { toFun := fun p =>
        (p.1,
          (if P.connected.cellulation.halfEdgeSide
                P.exteriorBoundaryStart = true
            then p.2⁻¹ else p.2) * B.chordExteriorTail p.1)
      invFun := fun p =>
        (p.1,
          if P.connected.cellulation.halfEdgeSide
                P.exteriorBoundaryStart = true
            then B.chordExteriorTail p.1 * p.2⁻¹
            else p.2 * (B.chordExteriorTail p.1)⁻¹)
      left_inv := by
        rintro ⟨r, u⟩
        by_cases hs :
            P.connected.cellulation.halfEdgeSide
                P.exteriorBoundaryStart = true
        · simp [hs]
        · simp [hs, mul_assoc]
      right_inv := by
        rintro ⟨r, g⟩
        by_cases hs :
            P.connected.cellulation.halfEdgeSide
                P.exteriorBoundaryStart = true
        · simp [hs, mul_assoc]
        · simp [hs, mul_assoc] }
  measurable_toFun := by
    refine measurable_fst.prodMk ?_
    have ht : Measurable (fun p : (B.OtherChord -> SU2) × SU2 =>
        B.chordExteriorTail p.1) :=
      B.measurable_chordExteriorTail.comp measurable_fst
    by_cases hs :
        P.connected.cellulation.halfEdgeSide P.exteriorBoundaryStart = true
    · simp only [hs, if_true]
      exact continuous_mul.measurable2 (measurable_inv.comp measurable_snd) ht
    · simp only [hs]
      exact continuous_mul.measurable2 measurable_snd ht
  measurable_invFun := by
    refine measurable_fst.prodMk ?_
    have ht : Measurable (fun p : (B.OtherChord -> SU2) × SU2 =>
        B.chordExteriorTail p.1) :=
      B.measurable_chordExteriorTail.comp measurable_fst
    by_cases hs :
        P.connected.cellulation.halfEdgeSide P.exteriorBoundaryStart = true
    · simp only [hs, if_true]
      exact continuous_mul.measurable2 ht (measurable_inv.comp measurable_snd)
    · simp only [hs]
      exact continuous_mul.measurable2 measurable_snd (measurable_inv.comp ht)

@[simp]
theorem boundaryHolonomyShearEquiv_apply_fst
    (p : (B.OtherChord -> SU2) × SU2) :
    (B.boundaryHolonomyShearEquiv p).1 = p.1 := rfl

/-- The shear is Haar preserving: conditionally on all other chords, its
second coordinate is inversion (possibly) followed by a Haar translation. -/
theorem boundaryHolonomyShearEquiv_measurePreserving :
    MeasurePreserving B.boundaryHolonomyShearEquiv
      ((su2FiniteProductHaar B.OtherChord).prod su2HaarProb)
      ((su2FiniteProductHaar B.OtherChord).prod su2HaarProb) := by
  have hmeas : Measurable (Function.uncurry (fun r : B.OtherChord -> SU2 =>
      fun u : SU2 =>
        (if P.connected.cellulation.halfEdgeSide
              P.exteriorBoundaryStart = true
          then u⁻¹ else u) * B.chordExteriorTail r)) :=
    B.boundaryHolonomyShearEquiv.measurable_toFun.snd
  have hskew := (MeasurePreserving.id
      (su2FiniteProductHaar B.OtherChord)).skew_product
    (μc := su2HaarProb) (μd := su2HaarProb)
    (g := fun r : B.OtherChord -> SU2 => fun u : SU2 =>
      (if P.connected.cellulation.halfEdgeSide
            P.exteriorBoundaryStart = true
        then u⁻¹ else u) * B.chordExteriorTail r)
    hmeas (ae_of_all _ fun r => by
      by_cases hs :
          P.connected.cellulation.halfEdgeSide
              P.exteriorBoundaryStart = true
      · have hcomp := (measurePreserving_mul_right su2HaarProb
            (B.chordExteriorTail r)).comp
            (Measure.measurePreserving_inv su2HaarProb)
        simpa [hs, Function.comp_def] using hcomp.map_eq
      · simpa [hs] using
          (measurePreserving_mul_right su2HaarProb
            (B.chordExteriorTail r)).map_eq)
  simpa [boundaryHolonomyShearEquiv] using hskew

/-- The complete boundary chart: all non-anchor chords followed by the
retained exterior holonomy. -/
def chordBoundaryEquiv :
    (B.ChordEdge -> SU2) ≃ᵐ (B.OtherChord -> SU2) × SU2 :=
  B.chordSplitEquiv.trans B.boundaryHolonomyShearEquiv

@[simp]
theorem chordBoundaryEquiv_apply_fst (x : B.ChordEdge -> SU2) :
    (B.chordBoundaryEquiv x).1 = (B.chordSplitEquiv x).1 := rfl

@[simp]
theorem chordBoundaryEquiv_apply_snd (x : B.ChordEdge -> SU2) :
    (B.chordBoundaryEquiv x).2 = B.chordExteriorHolonomy x := by
  rw [B.chordExteriorHolonomy_eq_anchor_mul_tail]
  rfl

theorem chordBoundaryEquiv_measurePreserving :
    MeasurePreserving B.chordBoundaryEquiv
      (su2FiniteProductHaar B.ChordEdge)
      ((su2FiniteProductHaar B.OtherChord).prod su2HaarProb) := by
  exact B.boundaryHolonomyShearEquiv_measurePreserving.comp
    (su2PiSplitAtEquiv_measurePreserving B.boundaryChord)

/-- Gauge-fixed density with exterior holonomy retained at the prescribed
value `g`.  Only the remaining chord variables are integrated. -/
def conditionedChordDensity (g : SU2) (r : B.OtherChord -> SU2) : Complex :=
  P.toSU2EdgeConnectedDiskCellulation.chordGaugeFixedDensity B.tree
    (B.chordBoundaryEquiv.symm (r, g))

/-- The boundary-conditioned chord integral. -/
def conditionedChordIntegral (g : SU2) : Complex :=
  ∫ r, B.conditionedChordDensity g r
    ∂su2FiniteProductHaar B.OtherChord

/-- The original-edge density in the boundary chart.  The first block is the
`V - 1` pure-gauge coordinates, the second block contains all physical chord
coordinates except the exterior holonomy, and `g` is that retained holonomy. -/
def conditionedEdgeDensity (g : SU2)
    (p : (Fin B.tree.n -> SU2) × (B.OtherChord -> SU2)) : Complex :=
  P.toSU2EdgeConnectedDiskCellulation.edgeHeatKernelDensity
    (B.tree.globalEdgeGaugeEquiv.symm
      (p.1, B.chordBoundaryEquiv.symm (p.2, g)))

/-- Boundary-conditioned original-edge integral in the explicit disintegration
chart.  It retains `g`; it does not integrate the exterior variable away. -/
def conditionedEdgeIntegral (g : SU2) : Complex :=
  ∫ p, B.conditionedEdgeDensity g p
    ∂((su2FiniteProductHaar (Fin B.tree.n)).prod
      (su2FiniteProductHaar B.OtherChord))

/-- Pointwise factorization: after gauge fixing, the conditioned original-edge
density is independent of all pure-gauge coordinates. -/
theorem conditionedEdgeDensity_eq_conditionedChordDensity
    (g : SU2) (p : (Fin B.tree.n -> SU2) × (B.OtherChord -> SU2)) :
    B.conditionedEdgeDensity g p = B.conditionedChordDensity g p.2 := by
  exact P.toSU2EdgeConnectedDiskCellulation.edgeHeatKernelDensity_globalEdgeFactorization B.tree
      (p.1, B.chordBoundaryEquiv.symm (p.2, g))

/-- **First conditioned bridge.**  For every retained exterior holonomy, the
original-edge integral equals the gauge-fixed chord integral.  This is the
type-correct boundary analogue of the fully integrated scalar reduction. -/
theorem conditionedEdgeIntegral_eq_conditionedChordIntegral (g : SU2) :
    B.conditionedEdgeIntegral g = B.conditionedChordIntegral g := by
  calc
    B.conditionedEdgeIntegral g =
        ∫ p, B.conditionedChordDensity g p.2
          ∂((su2FiniteProductHaar (Fin B.tree.n)).prod
            (su2FiniteProductHaar B.OtherChord)) := by
      apply integral_congr_ae
      exact ae_of_all _ (B.conditionedEdgeDensity_eq_conditionedChordDensity g)
    _ = ∫ r, B.conditionedChordDensity g r
          ∂su2FiniteProductHaar B.OtherChord := by
      rw [integral_fun_snd]
      simp
    _ = B.conditionedChordIntegral g := rfl

/-- Global edge coordinates with exterior holonomy as the final coordinate. -/
def globalBoundaryEdgeEquiv :
    P.EdgeConfiguration ≃ᵐ
      (Fin B.tree.n -> SU2) × ((B.OtherChord -> SU2) × SU2) :=
  B.tree.globalEdgeGaugeEquiv.trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Fin B.tree.n -> SU2))
      B.chordBoundaryEquiv)

@[simp]
theorem globalBoundaryEdgeEquiv_apply_gauge (U : P.EdgeConfiguration) :
    (B.globalBoundaryEdgeEquiv U).1 =
      (B.tree.globalEdgeGaugeEquiv U).1 := rfl

/-- Product Haar disintegrates into normalized gauge Haar, the remaining
chord Haar variables, and one final normalized Haar exterior coordinate. -/
theorem globalBoundaryEdgeEquiv_measurePreserving :
    MeasurePreserving B.globalBoundaryEdgeEquiv
      (su2FiniteProductHaar P.connected.cellulation.Edge)
      ((su2FiniteProductHaar (Fin B.tree.n)).prod
        ((su2FiniteProductHaar B.OtherChord).prod su2HaarProb)) := by
  have hprod : MeasurePreserving
      (Prod.map (id : (Fin B.tree.n -> SU2) -> (Fin B.tree.n -> SU2))
        B.chordBoundaryEquiv)
      ((su2FiniteProductHaar (Fin B.tree.n)).prod
        (su2FiniteProductHaar B.ChordEdge))
      ((su2FiniteProductHaar (Fin B.tree.n)).prod
        ((su2FiniteProductHaar B.OtherChord).prod su2HaarProb)) :=
    (MeasurePreserving.id (su2FiniteProductHaar (Fin B.tree.n))).prod
      B.chordBoundaryEquiv_measurePreserving
  have hcomp := hprod.comp B.tree.globalEdgeGaugeEquiv_measurePreserving
  simpa [globalBoundaryEdgeEquiv, MeasurableEquiv.prodCongr,
    Function.comp_def] using hcomp

/-- The rooted gauge used by the global chart is the identity at the exterior
basepoint, so it preserves the exterior holonomy literally, not merely up to
conjugacy. -/
theorem exteriorHolonomy_globalGaugeFix
    (U : P.EdgeConfiguration) :
    P.exteriorHolonomy
        (P.connected.cellulation.gaugeTransform U
          (B.tree.vertexPotential (B.tree.globalEdgeGaugeEquiv U).1)) =
      P.exteriorHolonomy U := by
  rw [P.exteriorHolonomy_gaugeTransform]
  have hroot :
      B.tree.vertexPotential (B.tree.globalEdgeGaugeEquiv U).1
          (P.connected.cellulation.source P.exteriorBoundaryStart) = 1 := by
    rw [← B.root_eq_exterior_source]
    simp [SU2FiniteDiskCellulation.RootedSpanningTree.vertexPotential,
      B.tree.rootedPotential_root]
  rw [hroot]
  simp

/-- In particular, the second block of the global gauge equivalence retains
the original exterior holonomy. -/
theorem chordExteriorHolonomy_globalEdgeGaugeEquiv
    (U : P.EdgeConfiguration) :
    B.chordExteriorHolonomy (B.tree.globalEdgeGaugeEquiv U).2 =
      P.exteriorHolonomy U := by
  rw [chordExteriorHolonomy]
  rw [← B.tree.gaugeTransform_eq_gaugeFixedEdgeConfiguration U]
  exact B.exteriorHolonomy_globalGaugeFix U

/-- The final coordinate of the global chart is the physical exterior
holonomy of the original, unfixed edge configuration. -/
@[simp]
theorem globalBoundaryEdgeEquiv_apply_exterior (U : P.EdgeConfiguration) :
    (B.globalBoundaryEdgeEquiv U).2.2 = P.exteriorHolonomy U := by
  calc
    (B.globalBoundaryEdgeEquiv U).2.2 =
        (B.chordBoundaryEquiv (B.tree.globalEdgeGaugeEquiv U).2).2 := rfl
    _ = B.chordExteriorHolonomy (B.tree.globalEdgeGaugeEquiv U).2 :=
      B.chordBoundaryEquiv_apply_snd _
    _ = P.exteriorHolonomy U :=
      B.chordExteriorHolonomy_globalEdgeGaugeEquiv U

end BoundaryGaugeChart

end SU2BoundaryDiskCellulation

end Lean2dYangMills
