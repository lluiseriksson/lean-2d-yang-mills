import Lean2dYangMills.SU2CyclicEdgeElimination

/-!
# Persistent cyclic words under physical edge elimination

The local Migdal move removes one dart and its reverse from two cyclic words.
The remaining boundary is the cyclic splice `B A D C`.  This module isolates
that combinatorics from the original facial words and proves the invariant
needed for global iteration: every dart carried by a different physical edge
survives the splice, and no new dart is introduced.
-/

noncomputable section

namespace Lean2dYangMills

namespace SU2FiniteDiskCellulation

/-- Splitting data for two arbitrary cyclic dart words along the two
orientations of one physical edge. -/
structure CyclicDartWordMerge (C : SU2FiniteDiskCellulation)
    (dart : C.HalfEdge) (first second : List C.HalfEdge) where
  firstBefore : List C.HalfEdge
  firstAfter : List C.HalfEdge
  first_word : first = firstBefore ++ dart :: firstAfter
  secondBefore : List C.HalfEdge
  secondAfter : List C.HalfEdge
  second_word : second = secondBefore ++ C.reverse dart :: secondAfter

namespace CyclicDartWordMerge

variable {C : SU2FiniteDiskCellulation}
  {dart : C.HalfEdge} {first second : List C.HalfEdge}
  (M : C.CyclicDartWordMerge dart first second)

/-- Boundary word left after cancelling the selected dart pair.  Its order is
the one produced by the cyclic Migdal identity. -/
def mergedWord : List C.HalfEdge :=
  M.firstAfter ++ M.firstBefore ++ M.secondAfter ++ M.secondBefore

/-- Evaluation of the spliced word is exactly the four-factor expression
appearing on the right-hand side of the local physical Migdal move. -/
theorem eval_mergedWord (U : C.Edge -> SU2) :
    C.evalDartWord U M.mergedWord =
      (C.evalDartWord U M.firstAfter *
          C.evalDartWord U M.firstBefore) *
        (C.evalDartWord U M.secondAfter *
          C.evalDartWord U M.secondBefore) := by
  simp only [mergedWord, C.evalDartWord_append]
  simp only [mul_assoc]

/-- A splice introduces no darts: every output dart came from one of the two
input words. -/
theorem mem_first_or_second_of_mem_mergedWord
    {k : C.HalfEdge} (hk : k ∈ M.mergedWord) :
    k ∈ first ∨ k ∈ second := by
  rw [mergedWord] at hk
  simp only [List.mem_append] at hk
  rcases hk with ((hfa | hfb) | hsa) | hsb
  · left
    rw [M.first_word]
    simp [hfa]
  · left
    rw [M.first_word]
    simp [hfb]
  · right
    rw [M.second_word]
    simp [hsa]
  · right
    rw [M.second_word]
    simp [hsb]

/-- A dart on any physical edge other than the selected one survives the
splice.  This is the forward persistence lemma used at every later
elimination step. -/
theorem mem_mergedWord_of_mem_of_edge_ne
    {k : C.HalfEdge}
    (hedge : C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (hk : k ∈ first ∨ k ∈ second) :
    k ∈ M.mergedWord := by
  have hk_ne_dart : k ≠ dart := by
    intro h
    exact hedge (congrArg C.edgeOfHalfEdge h)
  have hk_ne_reverse : k ≠ C.reverse dart := by
    intro h
    apply hedge
    rw [h, C.edgeOfHalfEdge_reverse]
  rw [mergedWord]
  simp only [List.mem_append]
  rcases hk with hkfirst | hksecond
  · rw [M.first_word] at hkfirst
    simp only [List.mem_append, List.mem_cons] at hkfirst
    rcases hkfirst with hbefore | heq | hafter
    · simp [hbefore]
    · exact (hk_ne_dart heq).elim
    · simp [hafter]
  · rw [M.second_word] at hksecond
    simp only [List.mem_append, List.mem_cons] at hksecond
    rcases hksecond with hbefore | heq | hafter
    · simp [hbefore]
    · exact (hk_ne_reverse heq).elim
    · simp [hafter]

/-- Exact persistence away from the eliminated physical edge. -/
theorem mem_mergedWord_iff_of_edge_ne
    {k : C.HalfEdge}
    (hedge : C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart) :
    k ∈ M.mergedWord ↔ k ∈ first ∨ k ∈ second := by
  exact ⟨M.mem_first_or_second_of_mem_mergedWord,
    M.mem_mergedWord_of_mem_of_edge_ne hedge⟩

/-- If the selected physical edge occurs only through the distinguished dart
pair in the input words, it is completely absent from the spliced word. -/
theorem mergedWord_avoids_selectedEdge
    (hfirst : ∀ k ∈ M.firstBefore ++ M.firstAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart)
    (hsecond : ∀ k ∈ M.secondBefore ++ M.secondAfter,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart) :
    ∀ k ∈ M.mergedWord,
      C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart := by
  intro k hk
  rw [mergedWord] at hk
  simp only [List.mem_append] at hk
  rcases hk with ((hfa | hfb) | hsa) | hsb
  · exact hfirst k (List.mem_append_right _ hfa)
  · exact hfirst k (List.mem_append_left _ hfb)
  · exact hsecond k (List.mem_append_right _ hsa)
  · exact hsecond k (List.mem_append_left _ hsb)

end CyclicDartWordMerge

end SU2FiniteDiskCellulation

namespace SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

variable {P : SU2EdgeConnectedDiskCellulation}
  {f g : P.connected.cellulation.Face}
  (M : SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P f g)

/-- Forget the original face labels while retaining the exact cyclic splits.
This is the base case consumed by the global word-block induction. -/
def toCyclicDartWordMerge :
    P.connected.cellulation.CyclicDartWordMerge M.dart
      (P.faceDartWord f) (P.faceDartWord g) where
  firstBefore := M.firstBefore
  firstAfter := M.firstAfter
  first_word := M.first_word
  secondBefore := M.secondBefore
  secondAfter := M.secondAfter
  second_word := M.second_word

/-- The physical two-face splice removes the selected edge completely. -/
theorem mergedWord_avoids_selectedEdge (hfg : f ≠ g) :
    ∀ k ∈ M.toCyclicDartWordMerge.mergedWord,
      P.connected.cellulation.edgeOfHalfEdge k ≠ M.selectedEdge := by
  exact M.toCyclicDartWordMerge.mergedWord_avoids_selectedEdge
    (M.first_fragments_avoid_edge hfg)
    (M.second_fragments_avoid_edge hfg)

end SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

end Lean2dYangMills
