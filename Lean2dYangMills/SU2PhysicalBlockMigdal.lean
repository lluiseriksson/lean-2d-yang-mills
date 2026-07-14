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

/-- For duplicate-free disjoint block words, the distinguished occurrence is
the only occurrence of the selected physical edge in the first word. -/
theorem first_fragments_avoid_of_nodup_disjoint
    (hfirstNodup : first.Nodup) (hdisjoint : List.Disjoint first second) :
    ∀ k ∈ M.firstBefore ++ M.firstAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart := by
  have hn := hfirstNodup
  rw [M.first_word, List.nodup_middle] at hn
  have hnot : dart ∉ M.firstBefore ++ M.firstAfter :=
    (List.nodup_cons.mp hn).1
  intro k hk hedge
  rcases C.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge with hsame | hreverse
  · exact hnot (hsame ▸ hk)
  · have hkFirst : k ∈ first := by
      rw [M.first_word]
      rcases List.mem_append.mp hk with hkbefore | hkafter
      · simp [hkbefore]
      · simp [hkafter]
    have hkSecond : k ∈ second := by
      rw [M.second_word, hreverse]
      simp
    exact (List.disjoint_left.mp hdisjoint) hkFirst hkSecond

/-- The symmetric uniqueness statement for the reverse distinguished dart in
the second word. -/
theorem second_fragments_avoid_of_nodup_disjoint
    (hsecondNodup : second.Nodup) (hdisjoint : List.Disjoint first second) :
    ∀ k ∈ M.secondBefore ++ M.secondAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart := by
  have hn := hsecondNodup
  rw [M.second_word, List.nodup_middle] at hn
  have hnot : C.reverse dart ∉ M.secondBefore ++ M.secondAfter :=
    (List.nodup_cons.mp hn).1
  intro k hk hedge
  rcases C.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge with hsame | hreverse
  · have hkFirst : k ∈ first := by
      rw [M.first_word, hsame]
      simp
    have hkSecond : k ∈ second := by
      rw [M.second_word]
      rcases List.mem_append.mp hk with hkbefore | hkafter
      · simp [hkbefore]
      · simp [hkafter]
    exact (List.disjoint_left.mp hdisjoint) hkFirst hkSecond
  · exact hnot (hreverse ▸ hk)

/-- Canonical splicing preserves duplicate-freeness when the two input words
are themselves duplicate-free and disjoint. -/
theorem nodup_mergedWord_of_nodup_disjoint
    (hfirstNodup : first.Nodup) (hsecondNodup : second.Nodup)
    (hdisjoint : List.Disjoint first second) :
    M.mergedWord.Nodup := by
  have hnFirst := hfirstNodup
  rw [M.first_word, List.nodup_middle] at hnFirst
  have hnFirstRot : (M.firstAfter ++ M.firstBefore).Nodup :=
    List.nodup_append_comm.mp (List.nodup_cons.mp hnFirst).2
  have hnSecond := hsecondNodup
  rw [M.second_word, List.nodup_middle] at hnSecond
  have hnSecondRot : (M.secondAfter ++ M.secondBefore).Nodup :=
    List.nodup_append_comm.mp (List.nodup_cons.mp hnSecond).2
  have hrotDisjoint : List.Disjoint
      (M.firstAfter ++ M.firstBefore) (M.secondAfter ++ M.secondBefore) := by
    rw [List.disjoint_left]
    intro k hkFirst hkSecond
    have hkFirstFull : k ∈ first := by
      rw [M.first_word]
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hkFirst with hkAfter | hkBefore
      · exact Or.inr (Or.inr hkAfter)
      · exact Or.inl hkBefore
    have hkSecondFull : k ∈ second := by
      rw [M.second_word]
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hkSecond with hkAfter | hkBefore
      · exact Or.inr (Or.inr hkAfter)
      · exact Or.inl hkBefore
    exact (List.disjoint_left.mp hdisjoint) hkFirstFull hkSecondFull
  simpa only [mergedWord, List.append_assoc] using
    hnFirstRot.append hnSecondRot hrotDisjoint

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

/-- Migdal elimination with no separately supplied fragment conditions:
duplicate-free disjoint input words force those conditions automatically. -/
theorem integrate_edge_merge_of_nodup_disjoint
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (hfirstNodup : first.Nodup) (hsecondNodup : second.Nodup)
    (hdisjoint : List.Disjoint first second)
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
  exact M.integrate_edge_merge hs ht
    (M.first_fragments_avoid_of_nodup_disjoint hfirstNodup hdisjoint)
    (M.second_fragments_avoid_of_nodup_disjoint hsecondNodup hdisjoint) r

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

/-- Duplicate-freeness is preserved by merging disjoint physical blocks. -/
theorem nodup_merge
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word)
    (hfaces : Disjoint first.faces second.faces)
    (hfirstNodup : first.word.Nodup) (hsecondNodup : second.word.Nodup) :
    (merge first second hfirst hsecond).word.Nodup := by
  let M := SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond
  exact M.nodup_mergedWord_of_nodup_disjoint hfirstNodup hsecondNodup
    (word_disjoint_of_faces_disjoint first second hfaces)

/-- Fully discharged block transition: positivity, disjoint face support and
duplicate-free words suffice; no fragment-avoidance premise remains. -/
theorem integrate_merge_of_nodup
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word)
    (hfaces : Disjoint first.faces second.faces)
    (hareaFirst : 0 < first.area) (hareaSecond : 0 < second.area)
    (hfirstNodup : first.word.Nodup) (hsecondNodup : second.word.Nodup)
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
  rw [area_merge_of_disjoint first second hfirst hsecond hfaces]
  let M := SU2FiniteDiskCellulation.CyclicDartWordMerge.ofMem hfirst hsecond
  exact M.integrate_edge_merge_of_nodup_disjoint hareaFirst hareaSecond
    hfirstNodup hsecondNodup
    (word_disjoint_of_faces_disjoint first second hfaces) r

end SU2EdgeConnectedDiskCellulation.PhysicalWordBlock

end Lean2dYangMills
