import Lean2dYangMills.SU2PhysicalWordBlocks

/-!
# Migdal elimination for arbitrary physical word blocks

The original local elimination theorem is stated for two facial words.  The
global induction instead encounters words produced by earlier splices.  This
module proves the same Haar integral identity for two arbitrary cyclic words,
provided the selected physical edge occurs only at the distinguished dart and
its reverse.  The output is literally the evaluation of `mergedWord`.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

namespace SU2FiniteDiskCellulation.CyclicDartWordMerge

variable {C : SU2FiniteDiskCellulation}
  {dart : C.HalfEdge} {first second : List C.HalfEdge}
  (M : C.CyclicDartWordMerge dart first second)

private abbrev selectedEdge : C.Edge := C.edgeOfHalfEdge dart

/-- Evaluation of the first current block with its selected coordinate
exposed at the distinguished dart. -/
theorem eval_first_edgeInsert
    (havoid : ∀ k ∈ M.firstBefore ++ M.firstAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (r : {e : C.Edge // e ≠ C.edgeOfHalfEdge dart} -> SU2) (x : SU2) :
    C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) first =
      C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r 1)
          M.firstBefore *
        (if C.halfEdgeSide dart = true then x⁻¹ else x) *
        C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r 1)
          M.firstAfter := by
  calc
    C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) first =
        C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x)
          (M.firstBefore ++ dart :: M.firstAfter) :=
      congrArg (C.evalDartWord
        (C.edgeInsert (C.edgeOfHalfEdge dart) r x)) M.first_word
    _ = _ := by
      rw [C.evalDartWord_append, C.evalDartWord_cons]
      rw [C.evalDartWord_edgeInsert_independent
          (C.edgeOfHalfEdge dart) r x 1 M.firstBefore
          (fun k hk => havoid k (List.mem_append_left _ hk))]
      rw [C.evalDartWord_edgeInsert_independent
          (C.edgeOfHalfEdge dart) r x 1 M.firstAfter
          (fun k hk => havoid k (List.mem_append_right _ hk))]
      unfold SU2FiniteDiskCellulation.edgeValue
      split <;> simp [SU2FiniteDiskCellulation.edgeInsert, mul_assoc]

/-- Evaluation of the second current block exposes the inverse orientation of
the same selected physical coordinate. -/
theorem eval_second_edgeInsert
    (havoid : ∀ k ∈ M.secondBefore ++ M.secondAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (r : {e : C.Edge // e ≠ C.edgeOfHalfEdge dart} -> SU2) (x : SU2) :
    C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) second =
      C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r 1)
          M.secondBefore *
        (if C.halfEdgeSide dart = true then x else x⁻¹) *
        C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r 1)
          M.secondAfter := by
  calc
    C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) second =
        C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x)
          (M.secondBefore ++ C.reverse dart :: M.secondAfter) :=
      congrArg (C.evalDartWord
        (C.edgeInsert (C.edgeOfHalfEdge dart) r x)) M.second_word
    _ = _ := by
      rw [C.evalDartWord_append, C.evalDartWord_cons]
      rw [C.evalDartWord_edgeInsert_independent
          (C.edgeOfHalfEdge dart) r x 1 M.secondBefore
          (fun k hk => havoid k (List.mem_append_left _ hk))]
      rw [C.evalDartWord_edgeInsert_independent
          (C.edgeOfHalfEdge dart) r x 1 M.secondAfter
          (fun k hk => havoid k (List.mem_append_right _ hk))]
      unfold SU2FiniteDiskCellulation.edgeValue
      rw [C.halfEdgeSide_reverse, C.edgeOfHalfEdge_reverse]
      by_cases hs : C.halfEdgeSide dart = true
      · simp [hs, SU2FiniteDiskCellulation.edgeInsert, mul_assoc]
      · have hb : C.halfEdgeSide dart = false := Bool.eq_false_iff.mpr hs
        simp [hb, SU2FiniteDiskCellulation.edgeInsert, mul_assoc]

/-- **Reusable physical Migdal transition.**  Two arbitrary current blocks
merge after integrating their shared physical edge.  The new heat-kernel time
is the sum of block areas and its argument is the canonical spliced word. -/
theorem integrate_edge_merge
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (havoidFirst : ∀ k ∈ M.firstBefore ++ M.firstAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (havoidSecond : ∀ k ∈ M.secondBefore ++ M.secondAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (r : {e : C.Edge // e ≠ C.edgeOfHalfEdge dart} -> SU2) :
    (∫ x : SU2,
      su2HeatKernel s
          (C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) first) *
        su2HeatKernel t
          (C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r x) second)
      ∂su2HaarProb) =
      su2HeatKernel (s + t)
        (C.evalDartWord (C.edgeInsert (C.edgeOfHalfEdge dart) r 1)
          M.mergedWord) := by
  simp_rw [M.eval_first_edgeInsert havoidFirst,
    M.eval_second_edgeInsert havoidSecond]
  rw [M.eval_mergedWord]
  by_cases hside : C.halfEdgeSide dart = true
  · simp only [hside, if_true]
    exact su2Migdal_eliminate_cyclic_neg_pos hs ht _ _ _ _
  · simp only [hside]
    exact su2Migdal_eliminate_cyclic_pos_neg hs ht _ _ _ _

end SU2FiniteDiskCellulation.CyclicDartWordMerge

namespace SU2EdgeConnectedDiskCellulation.PhysicalWordBlock

variable {P : SU2EdgeConnectedDiskCellulation}
  {eliminated : Set P.connected.cellulation.Edge}

/-- Block-level form of the physical Migdal transition.  It consumes the
global block invariant directly: disjoint face sets add their areas, while
the integrated density becomes the heat kernel of the merged block word. -/
theorem integrate_merge
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word)
    (hdisjoint : Disjoint first.faces second.faces)
    (hareaFirst : 0 < first.area) (hareaSecond : 0 < second.area)
    (havoidFirst : ∀ k ∈
      (SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond).firstBefore ++
        (SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond).firstAfter,
      P.connected.cellulation.edgeOfHalfEdge k ≠
        P.connected.cellulation.edgeOfHalfEdge dart)
    (havoidSecond : ∀ k ∈
      (SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond).secondBefore ++
        (SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond).secondAfter,
      P.connected.cellulation.edgeOfHalfEdge k ≠
        P.connected.cellulation.edgeOfHalfEdge dart)
    (r : {e : P.connected.cellulation.Edge //
      e ≠ P.connected.cellulation.edgeOfHalfEdge dart} -> SU2) :
    (∫ x : SU2,
      su2HeatKernel first.area
          (P.connected.cellulation.evalDartWord
            (P.connected.cellulation.edgeInsert
              (P.connected.cellulation.edgeOfHalfEdge dart) r x)
            first.word) *
        su2HeatKernel second.area
          (P.connected.cellulation.evalDartWord
            (P.connected.cellulation.edgeInsert
              (P.connected.cellulation.edgeOfHalfEdge dart) r x)
            second.word)
      ∂su2HaarProb) =
      su2HeatKernel (merge first second hfirst hsecond).area
        (P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert
            (P.connected.cellulation.edgeOfHalfEdge dart) r 1)
          (merge first second hfirst hsecond).word) := by
  rw [area_merge_of_disjoint first second hfirst hsecond hdisjoint]
  exact
    (SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond).integrate_edge_merge
      hareaFirst hareaSecond havoidFirst havoidSecond r

end SU2EdgeConnectedDiskCellulation.PhysicalWordBlock

end Lean2dYangMills
