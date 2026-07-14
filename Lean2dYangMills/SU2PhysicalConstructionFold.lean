import Lean2dYangMills.SU2PhysicalBlockGrowth
import Lean2dYangMills.SU2PhysicalEliminationSchedule

/-!
# Folding the physical construction tree into one global word block

The rooted dual tree is construction ordered: a root face is followed by one
new leaf at each step.  This module packages the data needed by that order and
builds the corresponding aggregate physical word block.  The recursive state
records exactly the faces already attached, exactly the physical edges already
eliminated, duplicate-freeness of the current word, and positivity of its area.
-/

noncomputable section

namespace Lean2dYangMills

/-- Physical face labels and cyclic merges carried by an abstract rooted
construction order.  Injectivity of labels prevents face reuse; injectivity
of selected edges prevents integration-coordinate reuse. -/
structure SU2PhysicalConstructionData
    (P : SU2EdgeConnectedDiskCellulation) {n : Nat}
    (tree : SU2RootedTreeOrder n) where
  label : Fin (n + 1) -> P.connected.cellulation.Face
  label_injective : Function.Injective label
  merge : ∀ i : Fin n,
    SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P
      (label (tree.parentIndex i)) (label (Fin.succ i))
  selectedEdge_injective : Function.Injective
    (fun i : Fin n => (merge i).selectedEdge)

namespace SU2PhysicalConstructionData

variable {P : SU2EdgeConnectedDiskCellulation}

/-- Restrict construction data for a grown tree to its old prefix. -/
def prefixData {n : Nat} {tree : SU2RootedTreeOrder n}
    {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) :
    SU2PhysicalConstructionData P tree where
  label := fun i => D.label (Fin.castSucc i)
  label_injective := by
    intro i j h
    have hij : Fin.castSucc i = Fin.castSucc j := D.label_injective h
    apply Fin.ext
    exact congrArg (fun k : Fin (n + 2) => k.val) hij
  merge := fun i =>
    let M := D.merge (Fin.castSucc i)
    { dart := M.dart
      dart_face := by
        simpa [SU2RootedTreeOrder.parentIndex] using M.dart_face
      reverse_face := by
        simpa using M.reverse_face
      firstBefore := M.firstBefore
      firstAfter := M.firstAfter
      first_word := by
        simpa [SU2RootedTreeOrder.parentIndex] using M.first_word
      secondBefore := M.secondBefore
      secondAfter := M.secondAfter
      second_word := by
        simpa using M.second_word }
  selectedEdge_injective := by
    intro i j h
    have hc : (D.merge (Fin.castSucc i)).selectedEdge =
        (D.merge (Fin.castSucc j)).selectedEdge := by
      simpa only [SU2EdgeConnectedDiskCellulation.CyclicFaceMerge.selectedEdge]
        using h
    have hij := D.selectedEdge_injective hc
    apply Fin.ext
    exact congrArg (fun k : Fin (n + 1) => k.val) hij

/-- The final physical merge in a nontrivial construction order. -/
def lastMerge {n : Nat} {tree : SU2RootedTreeOrder n}
    {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) :
    SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P
      (D.label (Fin.castSucc parent)) (D.label (Fin.last (n + 1))) := by
  let M := D.merge (Fin.last n)
  exact
    { dart := M.dart
      dart_face := by
        simpa [SU2RootedTreeOrder.parentIndex] using M.dart_face
      reverse_face := by
        simpa using M.reverse_face
      firstBefore := M.firstBefore
      firstAfter := M.firstAfter
      first_word := by
        simpa [SU2RootedTreeOrder.parentIndex] using M.first_word
      secondBefore := M.secondBefore
      secondAfter := M.secondAfter
      second_word := by
        simpa using M.second_word }

@[simp] theorem prefixData_label {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) (i : Fin (n + 1)) :
    D.prefixData.label i = D.label (Fin.castSucc i) := rfl

@[simp] theorem prefixData_merge_selectedEdge {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) (i : Fin n) :
    (D.prefixData.merge i).selectedEdge =
      (D.merge (Fin.castSucc i)).selectedEdge := rfl

@[simp] theorem lastMerge_selectedEdge {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) :
    D.lastMerge.selectedEdge = (D.merge (Fin.last n)).selectedEdge := rfl

/-- Splitting the final construction index separates the new face from the
faces of the old prefix. -/
theorem image_prefix_insert_last {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) :
    insert (D.label (Fin.last (n + 1)))
        (Finset.univ.image D.prefixData.label) =
      Finset.univ.image D.label := by
  classical
  ext f
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last (n + 1), rfl⟩
    · exact ⟨Fin.castSucc i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases (Or.inl rfl) (fun j => ?_) i
    exact Or.inr ⟨j, rfl⟩

/-- Likewise, the final selected edge adjoins one point to the range of the
old physical elimination coordinates. -/
theorem range_prefix_insert_last {n : Nat}
    {tree : SU2RootedTreeOrder n} {parent : Fin (n + 1)}
    (D : SU2PhysicalConstructionData P (.grow tree parent)) :
    insert D.lastMerge.selectedEdge
        (Set.range (fun i : Fin n => (D.prefixData.merge i).selectedEdge)) =
      Set.range (fun i : Fin (n + 1) => (D.merge i).selectedEdge) := by
  ext e
  simp only [Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last n, by simp⟩
    · exact ⟨Fin.castSucc i, by simp⟩
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases (Or.inl ?_) (fun j => Or.inr ⟨j, ?_⟩) i
    · simp
    · simp

end SU2PhysicalConstructionData

namespace SU2DualRootedEliminationTree

variable {P : SU2EdgeConnectedDiskCellulation}

/-- Forget only the face-order surjectivity of a physical elimination tree;
the remaining data are exactly those consumed by the construction fold. -/
def constructionData (T : SU2DualRootedEliminationTree P) :
    SU2PhysicalConstructionData P T.order where
  label := T.faceOrder
  label_injective := T.faceOrder.injective
  merge := T.merge
  selectedEdge_injective := T.selectedEdge_injective

end SU2DualRootedEliminationTree

/-- Certified output of folding a physical construction prefix. -/
structure SU2PhysicalConstructionState
    (P : SU2EdgeConnectedDiskCellulation) {n : Nat}
    {tree : SU2RootedTreeOrder n}
    (D : SU2PhysicalConstructionData P tree) where
  eliminated : Set P.connected.cellulation.Edge
  block : P.PhysicalWordBlock eliminated
  faces_eq : block.faces = Finset.univ.image D.label
  eliminated_eq : eliminated = Set.range (fun i : Fin n => (D.merge i).selectedEdge)
  word_nodup : block.word.Nodup
  area_pos : 0 < block.area

namespace SU2PhysicalConstructionState

variable {P : SU2EdgeConnectedDiskCellulation}

/-- Fold a construction-ordered physical dual tree into one certified global
word block.  Every recursive call consumes precisely the old prefix; the last
merge then attaches the unique new face along the unique new physical edge. -/
def build : {n : Nat} -> (tree : SU2RootedTreeOrder n) ->
    (D : SU2PhysicalConstructionData P tree) ->
      SU2PhysicalConstructionState P D
  | 0, .root, D =>
      { eliminated := ∅
        block :=
          SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singleton
            (D.label 0)
        faces_eq := by
          classical
          ext f
          simp [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singleton,
            SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt]
        eliminated_eq := by
          ext e
          simp
        word_nodup := P.faceDartWord_nodup (D.label 0)
        area_pos := by
          simpa [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area,
            SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singleton,
            SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt]
            using P.connected.cellulation.faceArea_pos (D.label 0) }
  | n + 1, .grow tree parent, D => by
      let oldD := D.prefixData
      let S := build tree oldD
      let M := D.lastMerge
      have hparent : D.label (Fin.castSucc parent) ∈ S.block.faces := by
        rw [S.faces_eq]
        exact Finset.mem_image.mpr ⟨parent, Finset.mem_univ parent, rfl⟩
      have hchild : D.label (Fin.last (n + 1)) ∉ S.block.faces := by
        rw [S.faces_eq]
        intro h
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
        have hidx : Fin.castSucc i = Fin.last (n + 1) :=
          D.label_injective hi
        have hv := congrArg (fun k : Fin (n + 2) => k.val) hidx
        simp at hv
        omega
      have hlive : M.selectedEdge ∉ S.eliminated := by
        rw [S.eliminated_eq]
        intro h
        obtain ⟨i, hi⟩ := h
        have hedge : (D.merge (Fin.castSucc i)).selectedEdge =
            (D.merge (Fin.last n)).selectedEdge := by
          simpa [oldD, M] using hi
        have hidx := D.selectedEdge_injective hedge
        have hv := congrArg (fun k : Fin (n + 1) => k.val) hidx
        simp at hv
        omega
      let newBlock := M.grow S.block hparent hlive
      exact
        { eliminated := insert M.selectedEdge S.eliminated
          block := newBlock
          faces_eq := by
            rw [show newBlock.faces = insert (D.label (Fin.last (n + 1)))
                S.block.faces by
              simpa [newBlock, M] using
                (M.grow_faces S.block hparent hlive)]
            rw [S.faces_eq]
            exact D.image_prefix_insert_last
          eliminated_eq := by
            rw [S.eliminated_eq]
            exact D.range_prefix_insert_last
          word_nodup := by
            exact M.grow_nodup S.block hparent hlive hchild S.word_nodup
          area_pos := by
            have hadd := M.grow_area S.block hparent hlive hchild
            change 0 < newBlock.area
            rw [show newBlock.area =
                S.block.area + P.connected.cellulation.faceArea
                  (D.label (Fin.last (n + 1))) by
              simpa [newBlock, M] using hadd]
            exact add_pos S.area_pos
              (P.connected.cellulation.faceArea_pos
                (D.label (Fin.last (n + 1)))) }

end SU2PhysicalConstructionState

namespace SU2DualRootedEliminationTree

variable {P : SU2EdgeConnectedDiskCellulation}

/-- The global word-block state constructed from an actual physical dual
elimination tree. -/
def constructionState (T : SU2DualRootedEliminationTree P) :
    SU2PhysicalConstructionState P T.constructionData :=
  SU2PhysicalConstructionState.build T.order T.constructionData

/-- The final block contains every bounded face exactly once. -/
theorem constructionState_faces_eq_univ
    (T : SU2DualRootedEliminationTree P) :
    T.constructionState.block.faces = Finset.univ := by
  rw [T.constructionState.faces_eq]
  exact Finset.image_univ_of_surjective T.faceOrder.surjective

/-- The state has consumed precisely the physical edges selected by the
dual construction tree. -/
theorem constructionState_eliminated_eq_range
    (T : SU2DualRootedEliminationTree P) :
    T.constructionState.eliminated = Set.range T.selectedEdge := by
  exact T.constructionState.eliminated_eq

/-- No dart is duplicated in the final physical boundary word. -/
theorem constructionState_word_nodup
    (T : SU2DualRootedEliminationTree P) :
    T.constructionState.block.word.Nodup :=
  T.constructionState.word_nodup

/-- The aggregate block area is literally the total area of the original
cellulation. -/
theorem constructionState_area_eq_totalArea
    (T : SU2DualRootedEliminationTree P) :
    T.constructionState.block.area = P.connected.cellulation.totalArea := by
  rw [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area,
    T.constructionState_faces_eq_univ]
  rfl

end SU2DualRootedEliminationTree

end Lean2dYangMills
