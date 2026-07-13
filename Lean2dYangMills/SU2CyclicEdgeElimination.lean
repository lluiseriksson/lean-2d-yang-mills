import Lean2dYangMills.SU2GlobalEdgeGaugeFixing

/-!
# Cyclic elimination of a shared physical edge

The local Migdal theorem is usually written with the integrated variable at
the end of one face word and the beginning of the other.  A genuine
cellulation presents the shared dart at arbitrary cyclic positions.  The two
theorems below remove that artificial ordering assumption using only the class
property of the heat kernel, then invoke the already proved concrete Migdal
move.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

namespace SU2FiniteDiskCellulation

theorem face_next_pow (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) (n : Nat) :
    C.face ((C.next ^ n) h) = C.face h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, C.face_next, ih]

@[simp]
theorem halfEdgeSide_reverse (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) :
    C.halfEdgeSide (C.reverse h) = !(C.halfEdgeSide h) := by
  rcases hp : C.edgeDarts.symm h with ⟨e, b⟩
  have hh : h = C.edgeDarts (e, b) := by
    rw [← hp]
    exact (C.edgeDarts.apply_symm_apply h).symm
  subst h
  simp [halfEdgeSide, C.reverse_edgeDarts]

/-- The literal ordered dart word read from a face-cycle successor orbit. -/
def dartWord (C : SU2FiniteDiskCellulation) (h : C.HalfEdge)
    (n : Nat) : List C.HalfEdge :=
  List.ofFn (fun k : Fin n => (C.next ^ (k : Nat)) h)

/-- Evaluate an oriented dart word in physical edge coordinates. -/
def evalDartWord (C : SU2FiniteDiskCellulation) (U : C.Edge -> SU2)
    (w : List C.HalfEdge) : SU2 :=
  (w.map (C.edgeValue U)).prod

theorem evalDartWord_append (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (u v : List C.HalfEdge) :
    C.evalDartWord U (u ++ v) =
      C.evalDartWord U u * C.evalDartWord U v := by
  simp [evalDartWord]

theorem evalDartWord_cons (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (h : C.HalfEdge) (w : List C.HalfEdge) :
    C.evalDartWord U (h :: w) =
      C.edgeValue U h * C.evalDartWord U w := by
  simp [evalDartWord]

/-- Insert one distinguished physical-edge coordinate into the product of all
remaining coordinates. -/
def edgeInsert (C : SU2FiniteDiskCellulation) (e : C.Edge)
    (r : {e' : C.Edge // e' ≠ e} -> SU2) (x : SU2) : C.Edge -> SU2 :=
  by
    classical
    exact fun e' => if he : e' = e then x else r ⟨e', he⟩

@[simp]
theorem edgeInsert_selected (C : SU2FiniteDiskCellulation) (e : C.Edge)
    (r : {e' : C.Edge // e' ≠ e} -> SU2) (x : SU2) :
    C.edgeInsert e r x e = x := by
  simp [edgeInsert]

theorem edgeInsert_other (C : SU2FiniteDiskCellulation) (e : C.Edge)
    (r : {e' : C.Edge // e' ≠ e} -> SU2) (x : SU2)
    {e' : C.Edge} (he' : e' ≠ e) :
    C.edgeInsert e r x e' = r ⟨e', he'⟩ := by
  simp [edgeInsert, he']

theorem edgeValue_edgeInsert_of_ne (C : SU2FiniteDiskCellulation)
    (e : C.Edge) (r : {e' : C.Edge // e' ≠ e} -> SU2) (x : SU2)
    (h : C.HalfEdge) (hh : C.edgeOfHalfEdge h ≠ e) :
    C.edgeValue (C.edgeInsert e r x) h =
      if C.halfEdgeSide h = true
        then (r ⟨C.edgeOfHalfEdge h, hh⟩)⁻¹
        else r ⟨C.edgeOfHalfEdge h, hh⟩ := by
  unfold edgeValue
  split <;> simp [edgeInsert, hh]

theorem evalDartWord_edgeInsert_independent
    (C : SU2FiniteDiskCellulation) (e : C.Edge)
    (r : {e' : C.Edge // e' ≠ e} -> SU2) (x y : SU2)
    (w : List C.HalfEdge)
    (hw : ∀ h ∈ w, C.edgeOfHalfEdge h ≠ e) :
    C.evalDartWord (C.edgeInsert e r x) w =
      C.evalDartWord (C.edgeInsert e r y) w := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      rw [C.evalDartWord_cons, C.evalDartWord_cons]
      have hh := hw h (by simp)
      rw [C.edgeValue_edgeInsert_of_ne e r x h hh,
        C.edgeValue_edgeInsert_of_ne e r y h hh]
      congr 1
      exact ih (fun k hk => hw k (by simp [hk]))

/-- The word model is definitionally faithful to the path-holonomy model used
by the edge-cellulation density. -/
theorem evalDartWord_dartWord (C : SU2FiniteDiskCellulation)
    (U : C.Edge -> SU2) (h : C.HalfEdge) (n : Nat) :
    C.evalDartWord U (C.dartWord h n) = C.dartHolonomy U h n := by
  induction n with
  | zero => simp [dartWord, evalDartWord, dartHolonomy]
  | succ n ih =>
      rw [dartWord, List.ofFn_succ']
      rw [evalDartWord, List.map_concat, List.prod_concat]
      change C.evalDartWord U (C.dartWord h n) *
          C.edgeValue U ((C.next ^ n) h) = C.dartHolonomy U h (n + 1)
      rw [ih]
      rfl

end SU2FiniteDiskCellulation

namespace SU2EdgeConnectedDiskCellulation

/-- The certified once-around word of a bounded face. -/
def faceDartWord (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face) :
    List P.connected.cellulation.HalfEdge :=
  P.connected.cellulation.dartWord (P.faceBoundaryStart f)
    (P.faceBoundaryLength f)

theorem eval_faceDartWord (P : SU2EdgeConnectedDiskCellulation)
    (U : P.EdgeConfiguration) (f : P.connected.cellulation.Face) :
    P.connected.cellulation.evalDartWord U (P.faceDartWord f) =
      P.faceHolonomy U f := by
  exact P.connected.cellulation.evalDartWord_dartWord U
    (P.faceBoundaryStart f) (P.faceBoundaryLength f)

/-- Every certified dart of a bounded face occurs in its once-around word. -/
theorem mem_faceDartWord_of_face
    (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face)
    (h : P.connected.cellulation.HalfEdge)
    (hh : P.connected.cellulation.face h = some f) :
    h ∈ P.faceDartWord f := by
  obtain ⟨k, hk⟩ := P.faceBoundary_complete f h hh
  rw [faceDartWord, SU2FiniteDiskCellulation.dartWord, List.mem_ofFn]
  exact ⟨k, hk⟩

theorem face_of_mem_faceDartWord
    (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face)
    (h : P.connected.cellulation.HalfEdge)
    (hh : h ∈ P.faceDartWord f) :
    P.connected.cellulation.face h = some f := by
  rw [faceDartWord, SU2FiniteDiskCellulation.dartWord, List.mem_ofFn] at hh
  obtain ⟨k, rfl⟩ := hh
  rw [P.connected.cellulation.face_next_pow]
  exact P.faceBoundaryStart_face f

/-- The once-around certification makes the literal facial word duplicate
free. -/
theorem faceDartWord_nodup (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face) :
    (P.faceDartWord f).Nodup := by
  rw [faceDartWord, SU2FiniteDiskCellulation.dartWord, List.nodup_ofFn]
  intro i j hij
  exact P.faceBoundary_nodup f i j hij

/-- A selected dart splits its facial cyclic word into the fragments before
and after that unique occurrence. -/
theorem exists_faceDartWord_split
    (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face)
    (h : P.connected.cellulation.HalfEdge)
    (hh : P.connected.cellulation.face h = some f) :
    ∃ before after,
      P.faceDartWord f = before ++ h :: after := by
  exact List.mem_iff_append.mp (P.mem_faceDartWord_of_face f h hh)

/-- Concrete cyclic-word data extracted from one dual adjacency. -/
structure CyclicFaceMerge
    (P : SU2EdgeConnectedDiskCellulation)
    (f g : P.connected.cellulation.Face) where
  dart : P.connected.cellulation.HalfEdge
  dart_face : P.connected.cellulation.face dart = some f
  reverse_face :
    P.connected.cellulation.face (P.connected.cellulation.reverse dart) = some g
  firstBefore : List P.connected.cellulation.HalfEdge
  firstAfter : List P.connected.cellulation.HalfEdge
  first_word : P.faceDartWord f = firstBefore ++ dart :: firstAfter
  secondBefore : List P.connected.cellulation.HalfEdge
  secondAfter : List P.connected.cellulation.HalfEdge
  second_word : P.faceDartWord g = secondBefore ++
    P.connected.cellulation.reverse dart :: secondAfter

theorem exists_cyclicFaceMerge_of_dualAdj
    (P : SU2EdgeConnectedDiskCellulation)
    {f g : P.connected.cellulation.Face}
    (hfg : P.connected.cellulation.dualAdj f g) :
    Nonempty (CyclicFaceMerge P f g) := by
  obtain ⟨_, h, hhf, hhg⟩ := hfg
  obtain ⟨fb, fa, hfw⟩ := P.exists_faceDartWord_split f h hhf
  obtain ⟨gb, ga, hgw⟩ :=
    P.exists_faceDartWord_split g (P.connected.cellulation.reverse h) hhg
  exact ⟨⟨h, hhf, hhg, fb, fa, hfw, gb, ga, hgw⟩⟩

namespace CyclicFaceMerge

variable {P : SU2EdgeConnectedDiskCellulation}
  {f g : P.connected.cellulation.Face} (M : CyclicFaceMerge P f g)

theorem first_fragments_avoid_edge (hfg : f ≠ g) :
    ∀ k ∈ M.firstBefore ++ M.firstAfter,
      P.connected.cellulation.edgeOfHalfEdge k ≠
        P.connected.cellulation.edgeOfHalfEdge M.dart := by
  have hn := P.faceDartWord_nodup f
  rw [M.first_word, List.nodup_middle] at hn
  have hnot : M.dart ∉ M.firstBefore ++ M.firstAfter :=
    (List.nodup_cons.mp hn).1
  intro k hk hedge
  rcases P.connected.cellulation.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge with
    hsame | hrev
  · subst k
    exact hnot hk
  · have hkmem : k ∈ P.faceDartWord f := by
      rw [M.first_word]
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hk with hkb | hka
      · exact Or.inl hkb
      · exact Or.inr (Or.inr hka)
    have hkface := P.face_of_mem_faceDartWord f k hkmem
    rw [hrev, M.reverse_face] at hkface
    exact hfg (Option.some.inj hkface).symm

theorem second_fragments_avoid_edge (hfg : f ≠ g) :
    ∀ k ∈ M.secondBefore ++ M.secondAfter,
      P.connected.cellulation.edgeOfHalfEdge k ≠
        P.connected.cellulation.edgeOfHalfEdge M.dart := by
  have hn := P.faceDartWord_nodup g
  rw [M.second_word, List.nodup_middle] at hn
  have hnot : P.connected.cellulation.reverse M.dart ∉
      M.secondBefore ++ M.secondAfter :=
    (List.nodup_cons.mp hn).1
  intro k hk hedge
  rcases P.connected.cellulation.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge with
    hsame | hrev
  · have hkrev : k = P.connected.cellulation.reverse
        (P.connected.cellulation.reverse M.dart) := by
      rw [P.connected.cellulation.reverse_involutive M.dart]
      exact hsame
    have hkmem : k ∈ P.faceDartWord g := by
      rw [M.second_word]
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hk with hkb | hka
      · exact Or.inl hkb
      · exact Or.inr (Or.inr hka)
    have hkface := P.face_of_mem_faceDartWord g k hkmem
    rw [hsame, M.dart_face] at hkface
    exact hfg (Option.some.inj hkface)
  · exact hnot (hrev ▸ hk)

abbrev selectedEdge : P.connected.cellulation.Edge :=
  P.connected.cellulation.edgeOfHalfEdge M.dart

abbrev RemainingEdge :=
  {e : P.connected.cellulation.Edge // e ≠ M.selectedEdge}

/-- The four cyclic fragments are independent of the selected edge
coordinate. -/
theorem first_faceHolonomy_edgeInsert
    (hfg : f ≠ g) (r : M.RemainingEdge -> SU2) (x : SU2) :
    P.faceHolonomy
        (P.connected.cellulation.edgeInsert M.selectedEdge r x) f =
      P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
          M.firstBefore *
        (if P.connected.cellulation.halfEdgeSide M.dart = true
          then x⁻¹ else x) *
        P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
          M.firstAfter := by
  rw [← P.eval_faceDartWord, M.first_word,
    P.connected.cellulation.evalDartWord_append,
    P.connected.cellulation.evalDartWord_cons]
  have hav := M.first_fragments_avoid_edge hfg
  rw [P.connected.cellulation.evalDartWord_edgeInsert_independent
      M.selectedEdge r x 1 M.firstBefore
      (fun k hk => hav k (List.mem_append_left _ hk))]
  rw [P.connected.cellulation.evalDartWord_edgeInsert_independent
      M.selectedEdge r x 1 M.firstAfter
      (fun k hk => hav k (List.mem_append_right _ hk))]
  unfold SU2FiniteDiskCellulation.edgeValue
  split <;> simp [SU2FiniteDiskCellulation.edgeInsert, mul_assoc]

theorem second_faceHolonomy_edgeInsert
    (hfg : f ≠ g) (r : M.RemainingEdge -> SU2) (x : SU2) :
    P.faceHolonomy
        (P.connected.cellulation.edgeInsert M.selectedEdge r x) g =
      P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
          M.secondBefore *
        (if P.connected.cellulation.halfEdgeSide M.dart = true
          then x else x⁻¹) *
        P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
          M.secondAfter := by
  rw [← P.eval_faceDartWord, M.second_word,
    P.connected.cellulation.evalDartWord_append,
    P.connected.cellulation.evalDartWord_cons]
  have hav := M.second_fragments_avoid_edge hfg
  rw [P.connected.cellulation.evalDartWord_edgeInsert_independent
      M.selectedEdge r x 1 M.secondBefore
      (fun k hk => hav k (List.mem_append_left _ hk))]
  rw [P.connected.cellulation.evalDartWord_edgeInsert_independent
      M.selectedEdge r x 1 M.secondAfter
      (fun k hk => hav k (List.mem_append_right _ hk))]
  unfold SU2FiniteDiskCellulation.edgeValue
  rw [P.connected.cellulation.halfEdgeSide_reverse,
    P.connected.cellulation.edgeOfHalfEdge_reverse]
  by_cases hs : P.connected.cellulation.halfEdgeSide M.dart = true
  · simp [hs, SU2FiniteDiskCellulation.edgeInsert, mul_assoc]
  · have hb : P.connected.cellulation.halfEdgeSide M.dart = false :=
      Bool.eq_false_iff.mpr hs
    simp [hb, SU2FiniteDiskCellulation.edgeInsert, mul_assoc]

end CyclicFaceMerge

end SU2EdgeConnectedDiskCellulation

/-- Eliminate a shared edge occurring positively in the first cyclic face
word and negatively in the second.  `a,b,c,d` are the four word fragments on
the two sides of the selected occurrences. -/
theorem su2Migdal_eliminate_cyclic_pos_neg
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (a b c d : SU2) :
    (∫ x : SU2,
      su2HeatKernel s (a * x * b) *
        su2HeatKernel t (c * x⁻¹ * d) ∂su2HaarProb) =
      su2HeatKernel (s + t) ((b * a) * (d * c)) := by
  calc
    (∫ x : SU2,
        su2HeatKernel s (a * x * b) *
          su2HeatKernel t (c * x⁻¹ * d) ∂su2HaarProb) =
        ∫ x : SU2,
          su2HeatKernel s ((b * a) * x) *
            su2HeatKernel t (x⁻¹ * (d * c)) ∂su2HaarProb := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change su2HeatKernel s (a * x * b) *
            su2HeatKernel t (c * x⁻¹ * d) =
          su2HeatKernel s ((b * a) * x) *
            su2HeatKernel t (x⁻¹ * (d * c))
        rw [su2HeatKernel_mul_comm s (a * x) b]
        rw [su2HeatKernel_mul_comm t (c * x⁻¹) d]
        simp only [← mul_assoc]
        rw [su2HeatKernel_mul_comm t (d * c) x⁻¹]
        simp only [mul_assoc]
    _ = su2HeatKernel (s + t) ((b * a) * (d * c)) :=
      su2Migdal_twoFace_merge hs ht (b * a) (d * c)

/-- The orientation-reversed local move.  It has the same merged cyclic word
as the positive-negative case. -/
theorem su2Migdal_eliminate_cyclic_neg_pos
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (a b c d : SU2) :
    (∫ x : SU2,
      su2HeatKernel s (a * x⁻¹ * b) *
        su2HeatKernel t (c * x * d) ∂su2HaarProb) =
      su2HeatKernel (s + t) ((b * a) * (d * c)) := by
  calc
    (∫ x : SU2,
        su2HeatKernel s (a * x⁻¹ * b) *
          su2HeatKernel t (c * x * d) ∂su2HaarProb) =
        ∫ x : SU2,
          su2HeatKernel s ((b * a) * x⁻¹) *
            su2HeatKernel t (x * (d * c)) ∂su2HaarProb := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change su2HeatKernel s (a * x⁻¹ * b) *
            su2HeatKernel t (c * x * d) =
          su2HeatKernel s ((b * a) * x⁻¹) *
            su2HeatKernel t (x * (d * c))
        rw [su2HeatKernel_mul_comm s (a * x⁻¹) b]
        rw [su2HeatKernel_mul_comm t (c * x) d]
        simp only [← mul_assoc]
        rw [su2HeatKernel_mul_comm t (d * c) x]
        simp only [mul_assoc]
    _ = su2HeatKernel (s + t) ((b * a) * (d * c)) :=
      su2Migdal_twoFace_merge_reversed hs ht (b * a) (d * c)

namespace SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

variable {P : SU2EdgeConnectedDiskCellulation}
  {f g : P.connected.cellulation.Face}
  (M : SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P f g)

/-- **Physical local elimination.** Integrating the actual edge selected by a
dual adjacency merges the two genuine facial heat-kernel factors.  No choice
of cyclic start or stored edge orientation is assumed. -/
theorem integrate_selected_edge
    (hfg : f ≠ g) (r : M.RemainingEdge -> SU2) :
    (∫ x : SU2,
      su2HeatKernel (P.connected.cellulation.faceArea f)
          (P.faceHolonomy
            (P.connected.cellulation.edgeInsert M.selectedEdge r x) f) *
        su2HeatKernel (P.connected.cellulation.faceArea g)
          (P.faceHolonomy
            (P.connected.cellulation.edgeInsert M.selectedEdge r x) g)
        ∂su2HaarProb) =
      su2HeatKernel
        (P.connected.cellulation.faceArea f +
          P.connected.cellulation.faceArea g)
        ((P.connected.cellulation.evalDartWord
              (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
              M.firstAfter *
            P.connected.cellulation.evalDartWord
              (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
              M.firstBefore) *
          (P.connected.cellulation.evalDartWord
              (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
              M.secondAfter *
            P.connected.cellulation.evalDartWord
              (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
              M.secondBefore)) := by
  simp_rw [M.first_faceHolonomy_edgeInsert hfg,
    M.second_faceHolonomy_edgeInsert hfg]
  by_cases hs : P.connected.cellulation.halfEdgeSide M.dart = true
  · simp only [hs, if_true]
    exact su2Migdal_eliminate_cyclic_neg_pos
      (P.connected.cellulation.faceArea_pos f)
      (P.connected.cellulation.faceArea_pos g) _ _ _ _
  · simp only [hs]
    exact su2Migdal_eliminate_cyclic_pos_neg
      (P.connected.cellulation.faceArea_pos f)
      (P.connected.cellulation.faceArea_pos g) _ _ _ _

end SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

end Lean2dYangMills
