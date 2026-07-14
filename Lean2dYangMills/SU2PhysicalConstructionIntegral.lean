import Lean2dYangMills.SU2PhysicalConstructionFold
import Lean2dYangMills.SU2PhysicalEliminationIntegral

/-!
# Integral coordinates for the global physical construction fold

For the left-associated physical construction, the old prefix must be
integrated before the final leaf edge.  We record the corresponding Fubini
formula and define the simultaneous assignment of all selected physical edge
coordinates.  The assignment is exact on every selected edge and leaves every
other original edge untouched.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- Fubini with the old `Fin n` prefix as the inner integral and the final
coordinate as the outer Haar integral. -/
theorem su2FiniteProductHaar_integral_iteratedPrefix (n : Nat)
    (f : (Fin (n + 1) -> SU2) -> Complex)
    (hf : Integrable f (su2FiniteProductHaar (Fin (n + 1)))) :
    (∫ z, f z ∂su2FiniteProductHaar (Fin (n + 1))) =
      ∫ x : SU2,
        ∫ r : Fin n -> SU2,
          f ((su2SplitLastEquiv n).symm (x, r))
          ∂su2FiniteProductHaar (Fin n)
        ∂su2HaarProb := by
  let E := su2SplitLastEquiv n
  have hinv : MeasurePreserving E.symm
      (su2HaarProb.prod (su2FiniteProductHaar (Fin n)))
      (su2FiniteProductHaar (Fin (n + 1))) :=
    MeasurePreserving.symm E (su2SplitLastEquiv_measurePreserving n)
  have hcomp : Integrable (fun p => f (E.symm p))
      (su2HaarProb.prod (su2FiniteProductHaar (Fin n))) :=
    hinv.integrable_comp_of_integrable hf
  calc
    (∫ z, f z ∂su2FiniteProductHaar (Fin (n + 1))) =
        ∫ p, f (E.symm p)
          ∂(su2HaarProb.prod (su2FiniteProductHaar (Fin n))) := by
      exact (hinv.integral_comp' f).symm
    _ = ∫ x : SU2,
          ∫ r : Fin n -> SU2, f (E.symm (x, r))
            ∂su2FiniteProductHaar (Fin n)
          ∂su2HaarProb := by
      exact integral_prod (fun p => f (E.symm p)) hcomp

namespace SU2PhysicalConstructionData

variable {P : SU2EdgeConnectedDiskCellulation}

/-- Assign all physical elimination coordinates, recursively setting the
last selected edge and then the old prefix.  Distinctness makes the order
irrelevant extensionally, but this order matches the construction fold. -/
def assign : {n : Nat} -> {tree : SU2RootedTreeOrder n} ->
    (D : SU2PhysicalConstructionData P tree) ->
    P.EdgeConfiguration ->
    (Fin n -> SU2) -> P.EdgeConfiguration
  | 0, .root, _, U, _ => U
  | n + 1, .grow tree parent, D, U, x =>
      let M := D.lastMerge
      let Ulast := P.connected.cellulation.edgeInsert M.selectedEdge
        (fun e => U e) (x (Fin.last n))
      D.prefixData.assign Ulast (fun i => x (Fin.castSucc i))

/-- An edge outside the selected range is unchanged by the simultaneous
physical-coordinate assignment. -/
theorem assign_of_not_mem_range : {n : Nat} ->
    {tree : SU2RootedTreeOrder n} ->
    (D : SU2PhysicalConstructionData P tree) ->
    (U : P.EdgeConfiguration) ->
    (x : Fin n -> SU2) ->
    (e : P.connected.cellulation.Edge) ->
    e ∉ Set.range (fun i : Fin n => (D.merge i).selectedEdge) ->
      D.assign U x e = U e
  | 0, .root, _, U, _, e, _ => rfl
  | n + 1, .grow tree parent, D, U, x, e, hnot => by
      let M := D.lastMerge
      let Ulast := P.connected.cellulation.edgeInsert M.selectedEdge
        (fun e => U e) (x (Fin.last n))
      have hprefix : e ∉ Set.range
          (fun i : Fin n => (D.prefixData.merge i).selectedEdge) := by
        intro h
        apply hnot
        rw [← D.range_prefix_insert_last]
        exact Set.mem_insert_iff.mpr (Or.inr h)
      have hlast : e ≠ M.selectedEdge := by
        intro h
        apply hnot
        rw [← D.range_prefix_insert_last]
        exact Set.mem_insert_iff.mpr (Or.inl h)
      change D.prefixData.assign Ulast
        (fun i => x (Fin.castSucc i)) e = U e
      rw [D.prefixData.assign_of_not_mem_range Ulast
        (fun i => x (Fin.castSucc i)) e hprefix]
      exact P.connected.cellulation.edgeInsert_other M.selectedEdge
        (fun e => U e) (x (Fin.last n)) hlast

/-- Every selected original physical edge receives literally its indexed
construction coordinate. -/
theorem assign_selectedEdge : {n : Nat} ->
    {tree : SU2RootedTreeOrder n} ->
    (D : SU2PhysicalConstructionData P tree) ->
    (U : P.EdgeConfiguration) ->
    (x : Fin n -> SU2) -> (i : Fin n) ->
      D.assign U x (D.merge i).selectedEdge = x i
  | 0, .root, _, _, _, i => Fin.elim0 i
  | n + 1, .grow tree parent, D, U, x, i => by
      let M := D.lastMerge
      let Ulast := P.connected.cellulation.edgeInsert M.selectedEdge
        (fun e => U e) (x (Fin.last n))
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hprefix : M.selectedEdge ∉ Set.range
            (fun j : Fin n => (D.prefixData.merge j).selectedEdge) := by
          intro h
          obtain ⟨j, hj⟩ := h
          have hedge : (D.merge (Fin.castSucc j)).selectedEdge =
              (D.merge (Fin.last n)).selectedEdge := by
            simpa [M] using hj
          have hidx := D.selectedEdge_injective hedge
          have hv := congrArg (fun k : Fin (n + 1) => k.val) hidx
          simp at hv
          omega
        change D.prefixData.assign Ulast
          (fun j => x (Fin.castSucc j)) M.selectedEdge = x (Fin.last n)
        rw [D.prefixData.assign_of_not_mem_range Ulast
          (fun j => x (Fin.castSucc j)) M.selectedEdge hprefix]
        exact P.connected.cellulation.edgeInsert_selected M.selectedEdge
          (fun e => U e) (x (Fin.last n))
      · change D.prefixData.assign Ulast
          (fun k => x (Fin.castSucc k))
          (D.prefixData.merge j).selectedEdge = x (Fin.castSucc j)
        exact D.prefixData.assign_selectedEdge Ulast
          (fun k => x (Fin.castSucc k)) j

/-- The original product of face heat kernels, indexed in physical
construction order and evaluated on the simultaneous assignment. -/
def density {n : Nat} {tree : SU2RootedTreeOrder n}
    (D : SU2PhysicalConstructionData P tree)
    (U : P.EdgeConfiguration) (x : Fin n -> SU2) : Complex :=
  ∏ i : Fin (n + 1),
    su2HeatKernel (P.connected.cellulation.faceArea (D.label i))
      (P.faceHolonomy (D.assign U x) (D.label i))

/-- Joint continuity of the simultaneous physical-coordinate assignment in
the untouched base configuration and all selected coordinates. -/
theorem continuous_assign : {n : Nat} ->
    {tree : SU2RootedTreeOrder n} ->
    (D : SU2PhysicalConstructionData P tree) ->
    Continuous (fun p : P.EdgeConfiguration × (Fin n -> SU2) =>
      D.assign p.1 p.2)
  | 0, .root, _ => continuous_fst
  | n + 1, .grow tree parent, D => by
      let M := D.lastMerge
      have hUlast : Continuous
          (fun p : P.EdgeConfiguration × (Fin (n + 1) -> SU2) =>
            P.connected.cellulation.edgeInsert M.selectedEdge
              (fun e => p.1 e) (p.2 (Fin.last n))) := by
        refine continuous_pi fun e => ?_
        by_cases he : e = M.selectedEdge
        · simp [SU2FiniteDiskCellulation.edgeInsert, he]
          exact (continuous_apply (Fin.last n)).comp continuous_snd
        · simp [SU2FiniteDiskCellulation.edgeInsert, he]
          exact (continuous_apply e).comp continuous_fst
      have hprefix : Continuous
          (fun p : P.EdgeConfiguration × (Fin (n + 1) -> SU2) =>
            fun i : Fin n => p.2 (Fin.castSucc i)) := by
        refine continuous_pi fun i => ?_
        exact (continuous_apply (Fin.castSucc i)).comp continuous_snd
      have hcomp := D.prefixData.continuous_assign.comp
        (hUlast.prodMk hprefix)
      simpa [assign, M] using hcomp

/-- Continuity in all selected coordinates for a fixed untouched base
configuration. -/
theorem continuous_assign_fixed {n : Nat}
    {tree : SU2RootedTreeOrder n}
    (D : SU2PhysicalConstructionData P tree) (U : P.EdgeConfiguration) :
    Continuous (D.assign U) := by
  exact D.continuous_assign.comp (continuous_const.prodMk continuous_id)

/-- The construction-ordered physical face density is continuous. -/
theorem continuous_density {n : Nat} {tree : SU2RootedTreeOrder n}
    (D : SU2PhysicalConstructionData P tree) (U : P.EdgeConfiguration) :
    Continuous (D.density U) := by
  unfold density
  refine continuous_finset_prod Finset.univ fun i _ => ?_
  exact (continuous_su2HeatKernelCharacterSeries
    (P.connected.cellulation.faceArea_pos (D.label i))).comp
      ((P.continuous_faceHolonomy (D.label i)).comp
        (D.continuous_assign_fixed U))

/-- Compactness of the finite SU(2) coordinate product gives integrability
of every construction density. -/
theorem integrable_density {n : Nat} {tree : SU2RootedTreeOrder n}
    (D : SU2PhysicalConstructionData P tree) (U : P.EdgeConfiguration) :
    Integrable (D.density U) (su2FiniteProductHaar (Fin n)) := by
  exact integrable_of_continuous_compact (D.continuous_density U)

/-- No edge of the newly attached final face was selected by an earlier
construction step. -/
theorem lastFace_edge_ne_prefixSelected {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent))
    (i : Fin n) (h : P.connected.cellulation.HalfEdge)
    (hh : h ∈ P.faceDartWord (D.label (Fin.last (n + 1)))) :
    P.connected.cellulation.edgeOfHalfEdge h ≠
      (D.prefixData.merge i).selectedEdge := by
  intro hedge
  let Mi := D.merge (Fin.castSucc i)
  have hface := P.face_of_mem_faceDartWord
    (D.label (Fin.last (n + 1))) h hh
  have hedge' : P.connected.cellulation.edgeOfHalfEdge h =
      P.connected.cellulation.edgeOfHalfEdge Mi.dart := by
    simpa [Mi] using hedge
  rcases P.connected.cellulation.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge'
      with hsame | hrev
  · rw [hsame, Mi.dart_face] at hface
    have hidx := D.label_injective (Option.some.inj hface)
    have hv := congrArg (fun k : Fin (n + 2) => k.val) hidx
    simp [Mi, SU2RootedTreeOrder.parentIndex] at hv
    have hlt := tree.parentIndex_lt_child i
    omega
  · rw [hrev, Mi.reverse_face] at hface
    have hidx := D.label_injective (Option.some.inj hface)
    have hv := congrArg (fun k : Fin (n + 2) => k.val) hidx
    simp [Mi] at hv
    omega

/-- Hence assigning all old-prefix coordinates leaves the new face holonomy
unchanged. -/
theorem lastFaceHolonomy_assign_prefix {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent))
    (U : P.EdgeConfiguration) (r : Fin n -> SU2) :
    P.faceHolonomy (D.prefixData.assign U r)
        (D.label (Fin.last (n + 1))) =
      P.faceHolonomy U (D.label (Fin.last (n + 1))) := by
  unfold SU2EdgeConnectedDiskCellulation.faceHolonomy
  apply P.connected.cellulation.dartHolonomy_congr
  intro k
  let h := (P.connected.cellulation.next ^ (k : Nat))
    (P.faceBoundaryStart (D.label (Fin.last (n + 1))))
  have hh : h ∈ P.faceDartWord (D.label (Fin.last (n + 1))) := by
    rw [SU2EdgeConnectedDiskCellulation.faceDartWord,
      SU2FiniteDiskCellulation.dartWord, List.mem_ofFn]
    exact ⟨k, rfl⟩
  have hnot : P.connected.cellulation.edgeOfHalfEdge h ∉ Set.range
      (fun i : Fin n => (D.prefixData.merge i).selectedEdge) := by
    intro hm
    obtain ⟨i, hi⟩ := hm
    exact D.lastFace_edge_ne_prefixSelected i h hh hi.symm
  have heq := D.prefixData.assign_of_not_mem_range U r
    (P.connected.cellulation.edgeOfHalfEdge h) hnot
  unfold SU2FiniteDiskCellulation.edgeValue
  split <;> rw [heq]

/-- Exact factorization of a grown construction density into its old prefix
and the single new face. -/
theorem density_grow_split {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent))
    (U : P.EdgeConfiguration) (x : Fin (n + 1) -> SU2) :
    D.density U x =
      D.prefixData.density
        (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
          (fun e => U e) (x (Fin.last n)))
        (fun i => x (Fin.castSucc i)) *
      su2HeatKernel
        (P.connected.cellulation.faceArea (D.label (Fin.last (n + 1))))
        (P.faceHolonomy
          (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
            (fun e => U e) (x (Fin.last n)))
          (D.label (Fin.last (n + 1)))) := by
  unfold density
  rw [Fin.prod_univ_castSucc]
  let Ulast := P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
    (fun e => U e) (x (Fin.last n))
  change
    (∏ i : Fin (n + 1),
      su2HeatKernel
        (P.connected.cellulation.faceArea (D.label (Fin.castSucc i)))
        (P.faceHolonomy
          (D.prefixData.assign Ulast (fun j => x (Fin.castSucc j)))
          (D.label (Fin.castSucc i)))) *
      su2HeatKernel
        (P.connected.cellulation.faceArea (D.label (Fin.last (n + 1))))
        (P.faceHolonomy
          (D.prefixData.assign Ulast (fun j => x (Fin.castSucc j)))
          (D.label (Fin.last (n + 1)))) = _
  rw [D.lastFaceHolonomy_assign_prefix Ulast
    (fun j => x (Fin.castSucc j))]
  rfl

/-- Assigning old-prefix coordinates commutes with insertion of the new edge:
the new edge remains the distinguished coordinate and all other edges carry
the prefix-assigned base configuration. -/
theorem prefix_assign_edgeInsert {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent))
    (U : P.EdgeConfiguration) (r : Fin n -> SU2) (x : SU2) :
    D.prefixData.assign
        (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
          (fun e => U e) x) r =
      P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
        (fun e => D.prefixData.assign
          (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
            (fun e' => U e') 1) r e) x := by
  funext e
  have hlive : D.lastMerge.selectedEdge ∉ Set.range
      (fun i : Fin n => (D.prefixData.merge i).selectedEdge) := by
    intro h
    obtain ⟨i, hi⟩ := h
    have hedge : (D.merge (Fin.castSucc i)).selectedEdge =
        (D.merge (Fin.last n)).selectedEdge := by
      simpa using hi
    have hidx := D.selectedEdge_injective hedge
    have hv := congrArg (fun k : Fin (n + 1) => k.val) hidx
    simp at hv
    omega
  by_cases he : e = D.lastMerge.selectedEdge
  · subst e
    rw [D.prefixData.assign_of_not_mem_range _ r _ hlive]
    simp
  · rw [P.connected.cellulation.edgeInsert_other
      D.lastMerge.selectedEdge _ x he]
    by_cases hsel : e ∈ Set.range
        (fun i : Fin n => (D.prefixData.merge i).selectedEdge)
    · obtain ⟨i, hi⟩ := hsel
      change (D.prefixData.merge i).selectedEdge = e at hi
      change D.prefixData.assign
          (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
            (fun e' => U e') x) r e =
        D.prefixData.assign
          (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
            (fun e' => U e') 1) r e
      calc
        _ = D.prefixData.assign
            (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
              (fun e' => U e') x) r
              (D.prefixData.merge i).selectedEdge := by rw [hi]
        _ = r i := D.prefixData.assign_selectedEdge _ r i
        _ = D.prefixData.assign
            (P.connected.cellulation.edgeInsert D.lastMerge.selectedEdge
              (fun e' => U e') 1) r
              (D.prefixData.merge i).selectedEdge :=
          (D.prefixData.assign_selectedEdge _ r i).symm
        _ = _ := by rw [hi]
    · rw [D.prefixData.assign_of_not_mem_range _ r e hsel,
        D.prefixData.assign_of_not_mem_range _ r e hsel]
      rw [P.connected.cellulation.edgeInsert_other
          D.lastMerge.selectedEdge _ x he,
        P.connected.cellulation.edgeInsert_other
          D.lastMerge.selectedEdge _ 1 he]

end SU2PhysicalConstructionData

namespace SU2DualRootedEliminationTree

variable {P : SU2EdgeConnectedDiskCellulation}

/-- Reindexing by the face-order equivalence identifies the construction
density with the actual unreduced edge heat-kernel density. -/
theorem edgeHeatKernelDensity_assign_eq_constructionDensity
    (T : SU2DualRootedEliminationTree P)
    (U : P.EdgeConfiguration) (x : Fin T.n -> SU2) :
    P.edgeHeatKernelDensity (T.constructionData.assign U x) =
      T.constructionData.density U x := by
  unfold SU2EdgeConnectedDiskCellulation.edgeHeatKernelDensity
    SU2PhysicalConstructionData.density
  exact (Fintype.prod_equiv T.faceOrder
    (fun i : Fin (T.n + 1) =>
      su2HeatKernel
        (P.connected.cellulation.faceArea (T.constructionData.label i))
        (P.faceHolonomy (T.constructionData.assign U x)
          (T.constructionData.label i)))
    (fun f : P.connected.cellulation.Face =>
      su2HeatKernel (P.connected.cellulation.faceArea f)
        (P.faceHolonomy (T.constructionData.assign U x) f))
    (fun _ => rfl)).symm

end SU2DualRootedEliminationTree

namespace SU2PhysicalBoundaryEliminationChart

variable {P : SU2BoundaryDiskCellulation}
  (D : SU2PhysicalBoundaryEliminationChart P)

local instance constructionIntegralEdgeDecidableEq :
    DecidableEq P.connected.cellulation.Edge := Classical.decEq _

local instance constructionIntegralChordEdgeDecidableEq :
    DecidableEq D.boundary.ChordEdge := Classical.decEq _

/-- Every exterior edge other than the adaptive anchor belongs to the primal
tree.  Otherwise it would define an `OtherChord`, hence one of the selected
internal physical edges, contradicting exterior-edge exclusion. -/
theorem exteriorEdge_mem_tree_of_ne_anchor
    (j : Fin P.exteriorBoundaryLength)
    (hj : j ≠ D.boundary.anchorIndex) :
    P.connected.cellulation.edgeOfHalfEdge
        ((P.connected.cellulation.next ^ (j : Nat))
          P.exteriorBoundaryStart) ∈ Set.range D.boundary.tree.treeEdge := by
  classical
  let e := P.connected.cellulation.edgeOfHalfEdge
    ((P.connected.cellulation.next ^ (j : Nat)) P.exteriorBoundaryStart)
  by_contra htree
  let c : D.boundary.ChordEdge := ⟨e, htree⟩
  have hc : c ≠ D.boundary.boundaryChord := by
    intro h
    have hedge : e = D.boundary.anchorEdge := congrArg Subtype.val h
    exact D.boundary.exteriorEdge_ne_anchorEdge j hj hedge
  let oc : D.OtherChord := ⟨c, hc⟩
  obtain ⟨i, hi⟩ := D.stepChord_bijective.2 oc
  have hedge : D.elimination.selectedEdge i = e := by
    have hv := congrArg (fun q : D.OtherChord => q.1.1) hi
    simpa [SU2PhysicalBoundaryEliminationChart.stepChord, oc, c] using hv
  exact D.elimination.selectedEdge_ne_exteriorEdge i j hedge

/-- With the anchor removed, every edge in the exterior prefix is gauge-fixed
to the identity. -/
theorem chordExteriorPrefix_eq_one (r : D.OtherChord -> SU2) :
    D.boundary.chordExteriorPrefix r = 1 := by
  unfold SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.chordExteriorPrefix
  apply P.connected.cellulation.dartHolonomy_eq_one_of_edgeValue_eq_one
  intro k
  let j : Fin P.exteriorBoundaryLength :=
    ⟨(k : Nat), lt_trans k.isLt D.boundary.anchorIndex.isLt⟩
  have hj : j ≠ D.boundary.anchorIndex := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [j] at hv
    omega
  have htree := D.exteriorEdge_mem_tree_of_ne_anchor j hj
  simp [SU2FiniteDiskCellulation.edgeValue,
    SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
    j, htree]

/-- The same identity holds for the exterior suffix after the anchor. -/
theorem chordExteriorSuffix_eq_one (r : D.OtherChord -> SU2) :
    D.boundary.chordExteriorSuffix r = 1 := by
  unfold SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.chordExteriorSuffix
  apply P.connected.cellulation.dartHolonomy_eq_one_of_edgeValue_eq_one
  intro k
  have hjlt : (D.boundary.anchorIndex : Nat) + 1 + (k : Nat) <
      P.exteriorBoundaryLength := by
    have ha := D.boundary.anchorIndex.isLt
    have hk := k.isLt
    omega
  let j : Fin P.exteriorBoundaryLength :=
    ⟨(D.boundary.anchorIndex : Nat) + 1 + (k : Nat), hjlt⟩
  have hj : j ≠ D.boundary.anchorIndex := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [j] at hv
    omega
  have htree := D.exteriorEdge_mem_tree_of_ne_anchor j hj
  have hpow :
      (P.connected.cellulation.next ^ (k : Nat))
          ((P.connected.cellulation.next ^
            ((D.boundary.anchorIndex : Nat) + 1))
            P.exteriorBoundaryStart) =
        (P.connected.cellulation.next ^ (j : Nat))
          P.exteriorBoundaryStart := by
    dsimp [j]
    change
      (P.connected.cellulation.next ^ (k : Nat) *
          P.connected.cellulation.next ^
            ((D.boundary.anchorIndex : Nat) + 1))
          P.exteriorBoundaryStart =
        (P.connected.cellulation.next ^
          ((D.boundary.anchorIndex : Nat) + 1 + (k : Nat)))
          P.exteriorBoundaryStart
    rw [← pow_add]
    congr 2
    omega
  rw [hpow]
  simp [SU2FiniteDiskCellulation.edgeValue,
    SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
    htree]

/-- Consequently the reconstructed anchor coordinate depends only on the
retained physical exterior holonomy, never on an internal chord coordinate. -/
theorem chordBoundaryEquiv_symm_apply_boundary
    (r : D.OtherChord -> SU2) (g : SU2) :
    D.boundary.chordBoundaryEquiv.symm (r, g)
        D.boundary.boundaryChord =
      if P.connected.cellulation.halfEdgeSide D.boundary.anchorDart = true
      then g⁻¹ else g := by
  unfold SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.chordBoundaryEquiv
  change D.boundary.chordSplitEquiv.symm
      (D.boundary.boundaryHolonomyShearEquiv.symm (r, g))
        D.boundary.boundaryChord = _
  unfold SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.chordSplitEquiv
  rw [su2PiSplitAtEquiv_symm_apply_selected]
  change (if P.connected.cellulation.halfEdgeSide D.boundary.anchorDart = true
    then D.boundary.chordExteriorSuffix r * g⁻¹ *
      D.boundary.chordExteriorPrefix r
    else (D.boundary.chordExteriorPrefix r)⁻¹ * g *
      (D.boundary.chordExteriorSuffix r)⁻¹) = _
  rw [D.chordExteriorPrefix_eq_one r, D.chordExteriorSuffix_eq_one r]
  simp

/-- The actual fixed-boundary gauge configuration in physical elimination
coordinates. -/
def conditionedConfiguration (g : SU2)
    (x : Fin D.elimination.n -> SU2) : P.EdgeConfiguration :=
  D.boundary.tree.gaugeFixedEdgeConfiguration
    (D.boundary.chordBoundaryEquiv.symm
      (D.internalCoordinateEquiv.symm x, g))

@[simp] theorem conditionedConfiguration_selectedEdge
    (g : SU2) (x : Fin D.elimination.n -> SU2)
    (i : Fin D.elimination.n) :
    D.conditionedConfiguration g x (D.elimination.selectedEdge i) = x i :=
  D.conditionedGaugeFixed_selectedEdge g x i

/-- Away from the selected physical range, a fixed-boundary configuration is
independent of every internal elimination coordinate. -/
theorem conditionedConfiguration_eq_of_not_mem_range
    (g : SU2) (x y : Fin D.elimination.n -> SU2)
    (e : P.connected.cellulation.Edge)
    (hnot : e ∉ Set.range D.elimination.selectedEdge) :
    D.conditionedConfiguration g x e = D.conditionedConfiguration g y e := by
  classical
  by_cases ht : e ∈ Set.range D.boundary.tree.treeEdge
  · simp [conditionedConfiguration,
      SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
      ht]
  · let c : D.boundary.ChordEdge := ⟨e, ht⟩
    by_cases hc : c = D.boundary.boundaryChord
    · have hx := D.chordBoundaryEquiv_symm_apply_boundary
          (D.internalCoordinateEquiv.symm x) g
      have hy := D.chordBoundaryEquiv_symm_apply_boundary
          (D.internalCoordinateEquiv.symm y) g
      simp only [conditionedConfiguration,
        SU2FiniteDiskCellulation.RootedSpanningTree.gaugeFixedEdgeConfiguration,
        ht, dite_false]
      change D.boundary.chordBoundaryEquiv.symm
          (D.internalCoordinateEquiv.symm x, g) c =
        D.boundary.chordBoundaryEquiv.symm
          (D.internalCoordinateEquiv.symm y, g) c
      rw [hc, hx, hy]
    · let oc : D.OtherChord := ⟨c, hc⟩
      obtain ⟨i, hi⟩ := D.stepChord_bijective.2 oc
      have hedge : D.elimination.selectedEdge i = e := by
        have hv := congrArg (fun q : D.OtherChord => q.1.1) hi
        simpa [SU2PhysicalBoundaryEliminationChart.stepChord, oc, c] using hv
      exact False.elim (hnot ⟨i, hedge⟩)

/-- **Global configuration bridge.**  The conditioned gauge-fixed
configuration is obtained from its all-one internal slice by assigning the
selected physical coordinates simultaneously. -/
theorem conditionedConfiguration_eq_assign_one
    (g : SU2) (x : Fin D.elimination.n -> SU2) :
    D.conditionedConfiguration g x =
      D.elimination.constructionData.assign
        (D.conditionedConfiguration g (fun _ => 1)) x := by
  funext e
  by_cases hsel : e ∈ Set.range D.elimination.selectedEdge
  · obtain ⟨i, rfl⟩ := hsel
    rw [D.conditionedConfiguration_selectedEdge]
    exact (D.elimination.constructionData.assign_selectedEdge
      (D.conditionedConfiguration g (fun _ => 1)) x i).symm
  · rw [D.elimination.constructionData.assign_of_not_mem_range
      (D.conditionedConfiguration g (fun _ => 1)) x e hsel]
    exact D.conditionedConfiguration_eq_of_not_mem_range g x
      (fun _ => 1) e hsel

/-- **Density bridge.**  The real boundary-conditioned chord density is
literally the construction-ordered physical face density on the fixed
all-one internal slice. -/
theorem indexedConditionedChordDensity_eq_constructionDensity
    (g : SU2) (x : Fin D.elimination.n -> SU2) :
    D.indexedConditionedChordDensity g x =
      D.elimination.constructionData.density
        (D.conditionedConfiguration g (fun _ => 1)) x := by
  unfold indexedConditionedChordDensity
    SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.conditionedChordDensity
    SU2EdgeConnectedDiskCellulation.chordGaugeFixedDensity
  change P.toSU2EdgeConnectedDiskCellulation.edgeHeatKernelDensity
      (D.conditionedConfiguration g x) = _
  rw [D.conditionedConfiguration_eq_assign_one g x]
  exact D.elimination.edgeHeatKernelDensity_assign_eq_constructionDensity
    (D.conditionedConfiguration g (fun _ => 1)) x

end SU2PhysicalBoundaryEliminationChart

end Lean2dYangMills
