import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Lean2dYangMills.SU2Character

/-!
# Normalized Haar probability measure on concrete SU(2)

This file gives the standalone 2D repository the compactness, topological
group, and normalized Haar instances it previously only referenced through
the mother Yang--Mills programme.  The compactness proof is the SU(2)
specialization of the entry-box argument used there.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory Matrix Set TopologicalSpace

instance instMeasurableSpaceMatrixTwo :
    MeasurableSpace (Matrix (Fin 2) (Fin 2) Complex) := by
  change MeasurableSpace (Fin 2 -> Fin 2 -> Complex)
  infer_instance

instance instBorelSpaceMatrixTwo :
    BorelSpace (Matrix (Fin 2) (Fin 2) Complex) := by
  change BorelSpace (Fin 2 -> Fin 2 -> Complex)
  infer_instance

instance instMeasurableSpaceSU2 : MeasurableSpace SU2 := inferInstance

instance instBorelSpaceSU2 : BorelSpace SU2 := inferInstance

private def su2EntryBox : Set (Matrix (Fin 2) (Fin 2) Complex) :=
  {A | forall i j, ‖A i j‖ <= 1}

private theorem isCompact_su2EntryBox : IsCompact su2EntryBox := by
  have heq : su2EntryBox = Set.pi Set.univ (fun _ : Fin 2 =>
      Set.pi Set.univ (fun _ : Fin 2 => Metric.closedBall (0 : Complex) 1)) := by
    ext A
    constructor
    · intro h i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using h i j
    · intro h i j
      simpa [Metric.mem_closedBall, dist_zero_right] using
        h i (Set.mem_univ _) j (Set.mem_univ _)
  rw [heq]
  exact isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1

private theorem specialUnitaryGroup_two_subset_entryBox :
    (↑(Matrix.specialUnitaryGroup (Fin 2) Complex) :
      Set (Matrix (Fin 2) (Fin 2) Complex)) ⊆ su2EntryBox := by
  intro A hA i j
  exact entry_norm_bound_of_unitary (mem_specialUnitaryGroup_iff.mp hA).1 i j

private theorem isClosed_unitaryGroup_two :
    IsClosed (↑(Matrix.unitaryGroup (Fin 2) Complex) :
      Set (Matrix (Fin 2) (Fin 2) Complex)) := by
  change IsClosed (↑(unitary (Matrix (Fin 2) (Fin 2) Complex)) :
    Set (Matrix (Fin 2) (Fin 2) Complex))
  exact isClosed_unitary

private theorem isClosed_det_two_eq_one :
    IsClosed ({A : Matrix (Fin 2) (Fin 2) Complex | A.det = 1}) :=
  isClosed_singleton.preimage (by fun_prop)

theorem isClosed_specialUnitaryGroup_two :
    IsClosed (↑(Matrix.specialUnitaryGroup (Fin 2) Complex) :
      Set (Matrix (Fin 2) (Fin 2) Complex)) := by
  have heq : (↑(Matrix.specialUnitaryGroup (Fin 2) Complex) :
      Set (Matrix (Fin 2) (Fin 2) Complex)) =
      ↑(Matrix.unitaryGroup (Fin 2) Complex) ∩ {A | A.det = 1} := by
    ext A
    exact mem_specialUnitaryGroup_iff
  rw [heq]
  exact isClosed_unitaryGroup_two.inter isClosed_det_two_eq_one

theorem isCompact_specialUnitaryGroup_two :
    IsCompact (↑(Matrix.specialUnitaryGroup (Fin 2) Complex) :
      Set (Matrix (Fin 2) (Fin 2) Complex)) :=
  isCompact_su2EntryBox.of_isClosed_subset
    isClosed_specialUnitaryGroup_two
    specialUnitaryGroup_two_subset_entryBox

instance instCompactSpaceSU2 : CompactSpace SU2 :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup_two

noncomputable instance instIsTopologicalGroupSU2 : IsTopologicalGroup SU2 where
  continuous_mul :=
    Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
      (fun p => mul_mem p.1.2 p.2.2)
  continuous_inv :=
    Continuous.subtype_mk (continuous_star.comp continuous_subtype_val)
      (fun M => (M⁻¹).2)

/-- The whole compact group, bundled as the normalization set for Haar. -/
def su2PositiveCompacts : PositiveCompacts SU2 where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp [interior_univ]

/-- Normalized Haar probability measure on Mathlib's concrete SU(2). -/
def su2HaarProb : Measure SU2 :=
  Measure.haarMeasure su2PositiveCompacts

instance instIsProbabilityMeasureSU2 : IsProbabilityMeasure su2HaarProb := by
  constructor
  have h := @Measure.haarMeasure_self SU2 _ _ _ _ _ su2PositiveCompacts
  simpa [su2HaarProb, su2PositiveCompacts] using h

/-- The nontrivial central element `-I` of SU(2). -/
def su2CenterNegOne : SU2 := by
  refine ⟨-(1 : Matrix (Fin 2) (Fin 2) Complex), ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    simp
  · simp [Matrix.det_fin_two]

/-- Left multiplication by the central element is matrix negation. -/
theorem coe_su2CenterNegOne_mul (g : SU2) :
    ((su2CenterNegOne * g : SU2) : Matrix (Fin 2) (Fin 2) Complex) =
      -(g : Matrix (Fin 2) (Fin 2) Complex) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2CenterNegOne, Matrix.mul_apply, Fin.sum_univ_two]

/-- Parity action of the center on every Chebyshev character. -/
theorem su2CharacterChebyshev_centerNegOne_mul (n : Nat) (g : SU2) :
    su2CharacterChebyshev n (su2CenterNegOne * g) =
      ((n : Int).negOnePow : Complex) * su2CharacterChebyshev n g := by
  unfold su2CharacterChebyshev
  rw [show Matrix.trace
      (((su2CenterNegOne * g : SU2) : Matrix (Fin 2) (Fin 2) Complex)) =
        -Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) by
      rw [coe_su2CenterNegOne_mul]
      simp]
  rw [show -Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) / 2 =
      -(Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) / 2) by ring]
  exact Polynomial.Chebyshev.U_eval_neg (R := Complex) n _

/-- Continuous SU(2) characters are Haar integrable on the compact group. -/
theorem integrable_su2CharacterChebyshev (n : Nat) :
    Integrable (su2CharacterChebyshev n) su2HaarProb :=
  (continuous_su2CharacterChebyshev n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

instance instIsMulLeftInvariantSU2HaarProb : su2HaarProb.IsMulLeftInvariant := by
  unfold su2HaarProb
  infer_instance

/-- First unconditional Haar-selection rule: every odd SU(2) character has
zero Haar mean. -/
theorem integral_su2CharacterChebyshev_eq_zero_of_odd
    {n : Nat} (hn : Odd n) :
    (∫ g : SU2, su2CharacterChebyshev n g ∂su2HaarProb) = 0 := by
  have hinv := integral_mul_left_eq_self (μ := su2HaarProb)
    (su2CharacterChebyshev n) su2CenterNegOne
  have hodd : Odd (n : Int) := (Int.odd_coe_nat n).mpr hn
  have hsign : (n : Int).negOnePow = -1 := Int.negOnePow_odd _ hodd
  have hsignC : ((n : Int).negOnePow : Complex) = -1 := by
    rw [hsign]
    norm_num
  simp_rw [su2CharacterChebyshev_centerNegOne_mul, hsignC, neg_one_mul] at hinv
  rw [integral_neg] at hinv
  have htwo : (2 : Complex) *
      (∫ g : SU2, su2CharacterChebyshev n g ∂su2HaarProb) = 0 := by
    linear_combination -hinv
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The fundamental SU(2) character has zero Haar mean. -/
theorem integral_su2FundamentalCharacter_eq_zero :
    (∫ g : SU2, su2CharacterChebyshev 1 g ∂su2HaarProb) = 0 :=
  integral_su2CharacterChebyshev_eq_zero_of_odd (by exact odd_one)

/-- Diagonal phase rotation `diag(i,-i)` in SU(2). -/
def su2PhaseI : SU2 := by
  refine ⟨!![Complex.I, 0; 0, -Complex.I], ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [Matrix.det_fin_two]

/-- Quarter-turn matrix exchanging the two row coordinates. -/
def su2QuarterTurn : SU2 := by
  refine ⟨!![0, -1; 1, 0], ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [Matrix.det_fin_two]

theorem su2PhaseI_mul_apply_zero_zero (g : SU2) :
    ((su2PhaseI * g : SU2) : Matrix (Fin 2) (Fin 2) Complex) 0 0 =
      Complex.I * (g : Matrix (Fin 2) (Fin 2) Complex) 0 0 := by
  simp [su2PhaseI, Matrix.mul_apply, Fin.sum_univ_two]

theorem su2QuarterTurn_mul_apply_zero_zero (g : SU2) :
    ((su2QuarterTurn * g : SU2) : Matrix (Fin 2) (Fin 2) Complex) 0 0 =
      star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) := by
  rw [show ((su2QuarterTurn * g : SU2) : Matrix (Fin 2) (Fin 2) Complex) 0 0 =
      -(g : Matrix (Fin 2) (Fin 2) Complex) 1 0 by
    simp [su2QuarterTurn, Matrix.mul_apply, Fin.sum_univ_two]]
  rw [su2_apply_one_zero_eq_neg_conj_apply_zero_one]
  simp

/-- Every continuous real-valued observable on compact SU(2) is Haar
integrable. -/
theorem integrable_continuous_su2_real {f : SU2 -> Real} (hf : Continuous f) :
    Integrable f su2HaarProb :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_su2_entry (i j : Fin 2) :
    Continuous (fun g : SU2 =>
      (g : Matrix (Fin 2) (Fin 2) Complex) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- Haar symmetry exchanges the squared norms of the two entries in the
first row. -/
theorem integral_su2_normSq_zero_zero_eq_zero_one :
    (∫ g : SU2,
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) ∂su2HaarProb) =
    ∫ g : SU2,
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) ∂su2HaarProb := by
  have hinv := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun g : SU2 =>
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0))
    su2QuarterTurn
  symm
  simpa [su2QuarterTurn_mul_apply_zero_zero, Complex.star_def,
    Complex.normSq_conj] using hinv

/-- Exact first coordinate moment of normalized SU(2) Haar. -/
theorem integral_su2_normSq_zero_zero :
    (∫ g : SU2,
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) ∂su2HaarProb) =
      1 / 2 := by
  have hA : Integrable (fun g : SU2 =>
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0)) su2HaarProb :=
    integrable_continuous_su2_real (by
      simp_rw [Complex.normSq_apply]
      exact ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).mul
        (Complex.continuous_re.comp (continuous_su2_entry 0 0))).add
        ((Complex.continuous_im.comp (continuous_su2_entry 0 0)).mul
          (Complex.continuous_im.comp (continuous_su2_entry 0 0))))
  have hB : Integrable (fun g : SU2 =>
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1)) su2HaarProb :=
    integrable_continuous_su2_real (by
      simp_rw [Complex.normSq_apply]
      exact ((Complex.continuous_re.comp (continuous_su2_entry 0 1)).mul
        (Complex.continuous_re.comp (continuous_su2_entry 0 1))).add
        ((Complex.continuous_im.comp (continuous_su2_entry 0 1)).mul
          (Complex.continuous_im.comp (continuous_su2_entry 0 1))))
  have hrow :
      (∫ g : SU2,
        (Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) +
          Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1))
        ∂su2HaarProb) = ∫ _g : SU2, (1 : Real) ∂su2HaarProb := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall su2_normSq_row_zero
  rw [integral_add hA hB] at hrow
  simp at hrow
  rw [← integral_su2_normSq_zero_zero_eq_zero_one] at hrow
  linarith

theorem su2PhaseI_mul_apply_zero_zero_re (g : SU2) :
    (((su2PhaseI * g : SU2) : Matrix (Fin 2) (Fin 2) Complex) 0 0).re =
      -((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im := by
  rw [su2PhaseI_mul_apply_zero_zero]
  simp [Complex.mul_re]

/-- Haar phase symmetry equates the real and imaginary second moments of the
upper-left entry. -/
theorem integral_su2_re_sq_eq_im_sq :
    (∫ g : SU2,
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 ∂su2HaarProb) =
    ∫ g : SU2,
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im ^ 2 ∂su2HaarProb := by
  have hinv := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun g : SU2 =>
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2) su2PhaseI
  simp_rw [su2PhaseI_mul_apply_zero_zero_re] at hinv
  simpa using hinv.symm

/-- Exact real-coordinate second moment of normalized SU(2) Haar. -/
theorem integral_su2_re_zero_zero_sq :
    (∫ g : SU2,
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 ∂su2HaarProb) =
      1 / 4 := by
  have hRe : Integrable (fun g : SU2 =>
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2) su2HaarProb :=
    integrable_continuous_su2_real
      ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).pow 2)
  have hIm : Integrable (fun g : SU2 =>
      ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im ^ 2) su2HaarProb :=
    integrable_continuous_su2_real
      ((Complex.continuous_im.comp (continuous_su2_entry 0 0)).pow 2)
  have hsplit :
      (∫ g : SU2,
        (((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 +
          ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im ^ 2) ∂su2HaarProb) =
      1 / 2 := by
    rw [← integral_su2_normSq_zero_zero]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by
      change ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 +
          ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im ^ 2 =
        Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0)
      rw [Complex.normSq_apply]
      ring
  rw [integral_add hRe hIm] at hsplit
  rw [← integral_su2_re_sq_eq_im_sq] at hsplit
  linarith

/-- Fundamental-character Schur normalization at the first nontrivial order. -/
theorem integral_su2FundamentalCharacter_re_sq :
    (∫ g : SU2, (su2CharacterChebyshev 1 g).re ^ 2 ∂su2HaarProb) = 1 := by
  calc
    (∫ g : SU2, (su2CharacterChebyshev 1 g).re ^ 2 ∂su2HaarProb) =
        ∫ g : SU2,
          4 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 ∂su2HaarProb := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun g => by
              change (su2CharacterChebyshev 1 g).re ^ 2 =
                4 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2
              rw [su2FundamentalCharacter_eq_two_mul_re]
              norm_num
              ring
    _ = 4 * (∫ g : SU2,
          ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 ∂su2HaarProb) := by
            rw [integral_const_mul]
    _ = 1 := by rw [integral_su2_re_zero_zero_sq]; norm_num

/-- The first even nontrivial SU(2) character has zero normalized Haar mean.
Together with the odd selector, this is the first genuinely even Haar
orthogonality checkpoint. -/
theorem integral_su2CharacterChebyshev_two_eq_zero :
    (∫ g : SU2, su2CharacterChebyshev 2 g ∂su2HaarProb) = 0 := by
  calc
    (∫ g : SU2, su2CharacterChebyshev 2 g ∂su2HaarProb) =
        ∫ g : SU2,
          (((4 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 - 1 : Real)) :
            Complex) ∂su2HaarProb := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall su2CharacterChebyshev_two
    _ = ((∫ g : SU2,
          (4 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 - 1 : Real)
          ∂su2HaarProb : Real) : Complex) := integral_complex_ofReal
    _ = ((4 * (∫ g : SU2,
          ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2
          ∂su2HaarProb) - 1 : Real) : Complex) := by
            congr 1
            rw [integral_sub]
            · rw [integral_const_mul]
              simp
            · exact (integrable_continuous_su2_real
                ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).pow 2)).const_mul 4
            · fun_prop
    _ = 0 := by rw [integral_su2_re_zero_zero_sq]; norm_num

end Lean2dYangMills
