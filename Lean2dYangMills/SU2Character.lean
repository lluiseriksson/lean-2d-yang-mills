import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Polynomial
import Lean2dYangMills.Interfaces
import Lean2dYangMills.ConvergenceEngine

/-!
# Concrete SU(2) characters and heat-kernel summability

The `(n+1)`-dimensional `SU(2)` character is represented by the Chebyshev
polynomial of the second kind evaluated at half the matrix trace.  This file
contains only unconditional declarations.  In particular, the Weyl character
bound is an explicit hypothesis of the summability bridge until it is proved
for Mathlib's concrete `Matrix.specialUnitaryGroup`.
-/

noncomputable section

namespace Lean2dYangMills

/-- Elementary multiple-angle bound used to control Chebyshev characters
without dividing by `sin theta`. -/
theorem abs_sin_nat_mul_le (n : Nat) (theta : Real) :
    |Real.sin ((n : Real) * theta)| <= (n : Real) * |Real.sin theta| := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
      calc
        |Real.sin ((n : Real) * theta) * Real.cos theta +
            Real.cos ((n : Real) * theta) * Real.sin theta|
            <= |Real.sin ((n : Real) * theta) * Real.cos theta| +
              |Real.cos ((n : Real) * theta) * Real.sin theta| := abs_add_le _ _
        _ = |Real.sin ((n : Real) * theta)| * |Real.cos theta| +
              |Real.cos ((n : Real) * theta)| * |Real.sin theta| := by
                rw [abs_mul, abs_mul]
        _ <= |Real.sin ((n : Real) * theta)| + |Real.sin theta| := by
              nlinarith [Real.abs_cos_le_one theta,
                Real.abs_cos_le_one ((n : Real) * theta),
                abs_nonneg (Real.sin ((n : Real) * theta)),
                abs_nonneg (Real.sin theta)]
        _ <= (n : Real) * |Real.sin theta| + |Real.sin theta| := by
              gcongr
        _ = ((n : Real) + 1) * |Real.sin theta| := by ring

/-- Sharp Chebyshev bound on the real unit interval. -/
theorem abs_chebyshevU_real_le_of_mem_Icc (n : Nat) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    |(Polynomial.Chebyshev.U Real (n : Int)).eval x| <= (n : Real) + 1 := by
  let theta := Real.arccos x
  have hcos : Real.cos theta = x := Real.cos_arccos hx.1 hx.2
  by_cases hsin : Real.sin theta = 0
  · have hends : x = 1 ∨ x = -1 := by
      rw [← hcos]
      exact Real.sin_eq_zero_iff_cos_eq.mp hsin
    rcases hends with rfl | rfl
    · rw [Polynomial.Chebyshev.U_eval_one]
      rw [abs_of_nonneg]
      · rfl
      · positivity
    · rw [Polynomial.Chebyshev.U_eval_neg_one]
      have hn : 0 <= (n : Real) + 1 := by positivity
      simp [abs_mul, abs_of_nonneg hn]
  · have hid := Polynomial.Chebyshev.U_real_cos theta (n : Int)
    rw [hcos] at hid
    have hcast : (((n : Int) : Real) + 1) = ((n + 1 : Nat) : Real) := by
      norm_num
    have hprod :
        |(Polynomial.Chebyshev.U Real (n : Int)).eval x| * |Real.sin theta| <=
          ((n : Real) + 1) * |Real.sin theta| := by
      calc
        |(Polynomial.Chebyshev.U Real (n : Int)).eval x| * |Real.sin theta|
            = |(Polynomial.Chebyshev.U Real (n : Int)).eval x * Real.sin theta| := by
                rw [abs_mul]
        _ = |Real.sin ((((n : Int) : Real) + 1) * theta)| := by rw [hid]
        _ = |Real.sin (((n + 1 : Nat) : Real) * theta)| := by rw [hcast]
        _ <= ((n + 1 : Nat) : Real) * |Real.sin theta| :=
              abs_sin_nat_mul_le (n + 1) theta
        _ = ((n : Real) + 1) * |Real.sin theta| := by norm_num
    exact le_of_mul_le_mul_right hprod (abs_pos.mpr hsin)

/-- Complex-coefficient form of the sharp Chebyshev bound, evaluated on a
real point of the unit interval. -/
theorem norm_chebyshevU_complex_ofReal_le (n : Nat) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    ‖(Polynomial.Chebyshev.U Complex (n : Int)).eval (x : Complex)‖ <=
      (n : Real) + 1 := by
  rw [← Polynomial.Chebyshev.complex_ofReal_eval_U, Complex.norm_real]
  exact abs_chebyshevU_real_le_of_mem_Icc n x hx

/-- The concrete Chebyshev formula for the `(n+1)`-dimensional SU(2)
character. -/
def su2CharacterChebyshev (n : Nat) (g : SU2) : Complex :=
  (Polynomial.Chebyshev.U Complex (n : Int)).eval
    ((Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex)) / 2)

/-- The SU(2) character data with Casimir `n(n+2)/4`. -/
def su2CharacterTable : SU2CharacterTable where
  Label := Nat
  dim := fun n => n + 1
  dim_pos := fun n => Nat.succ_pos n
  char := su2CharacterChebyshev
  casimir := fun n => ((n : Real) * ((n : Real) + 2)) / 4
  heatWeight := fun t n =>
    ((Real.exp (-t * (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex)

/-- Character at the identity equals the representation dimension. -/
theorem su2CharacterChebyshev_one (n : Nat) :
    su2CharacterChebyshev n 1 = ((n : Complex) + 1) := by
  rw [su2CharacterChebyshev]
  simp [Polynomial.Chebyshev.U_eval_one]

/-- For a special unitary matrix, the classical adjugate is its
conjugate-transpose. -/
theorem su2_adjugate_eq_star (g : SU2) :
    Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) Complex) =
      star (g : Matrix (Fin 2) (Fin 2) Complex) := by
  let A : Matrix (Fin 2) (Fin 2) Complex := g
  have hdet : A.det = 1 := g.prop.2
  have hAdjMul : Matrix.adjugate A * A = 1 := by
    rw [Matrix.adjugate_mul, hdet]
    simp
  have hMulStar : A * star A = 1 := g.prop.1.2
  change Matrix.adjugate A = star A
  calc
    Matrix.adjugate A = Matrix.adjugate A * 1 := by simp
    _ = Matrix.adjugate A * (A * star A) := by rw [hMulStar]
    _ = (Matrix.adjugate A * A) * star A := by rw [Matrix.mul_assoc]
    _ = star A := by rw [hAdjMul, Matrix.one_mul]

/-- In the defining two-dimensional representation of `SU(2)`, the lower
right entry is the complex conjugate of the upper left entry. -/
theorem su2_apply_one_one_eq_conj_apply_zero_zero (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) Complex) 1 1 =
      star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) := by
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) Complex => M 0 0)
    (su2_adjugate_eq_star g)
  simpa [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose] using hentry

/-- The lower-left entry is minus the conjugate of the upper-right entry. -/
theorem su2_apply_one_zero_eq_neg_conj_apply_zero_one (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) Complex) 1 0 =
      -star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) := by
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) Complex => M 1 0)
    (su2_adjugate_eq_star g)
  have hentry' :
      -(g : Matrix (Fin 2) (Fin 2) Complex) 1 0 =
        star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) := by
    simpa [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose] using hentry
  exact neg_eq_iff_eq_neg.mp hentry'

/-- Every entry of the defining unitary representation has norm at most one;
we record the entry needed for the trace estimate. -/
theorem su2_norm_apply_zero_zero_le_one (g : SU2) :
    ‖(g : Matrix (Fin 2) (Fin 2) Complex) 0 0‖ <= 1 := by
  let A : Matrix (Fin 2) (Fin 2) Complex := g
  have hunitary : A * star A = 1 := g.prop.1.2
  have hrow := congrArg (fun M : Matrix (Fin 2) (Fin 2) Complex => M 0 0) hunitary
  have hrowC :
      A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] using hrow
  rw [Complex.star_def, Complex.mul_conj, Complex.mul_conj] at hrowC
  have hrowR := congrArg Complex.re hrowC
  have hnormSq : Complex.normSq (A 0 0) <= 1 := by
    norm_num at hrowR
    nlinarith [Complex.normSq_nonneg (A 0 1)]
  rw [Complex.normSq_eq_norm_sq] at hnormSq
  have hnorm_nonneg : 0 <= ‖A 0 0‖ := norm_nonneg _
  change ‖A 0 0‖ <= 1
  nlinarith

/-- The first row of the defining SU(2) matrix has unit norm. -/
theorem su2_normSq_row_zero (g : SU2) :
    Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) +
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) = 1 := by
  let A : Matrix (Fin 2) (Fin 2) Complex := g
  have hunitary : A * star A = 1 := g.prop.1.2
  have hrow := congrArg (fun M : Matrix (Fin 2) (Fin 2) Complex => M 0 0) hunitary
  have hrowC :
      A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] using hrow
  rw [Complex.star_def, Complex.mul_conj, Complex.mul_conj] at hrowC
  exact_mod_cast hrowC

/-- Half the trace of an `SU(2)` matrix is the real part of its upper-left
entry, viewed as a complex number. -/
theorem su2_half_trace_eq_ofReal_re (g : SU2) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) / 2 =
      (((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re : Complex) := by
  rw [Matrix.trace_fin_two, su2_apply_one_one_eq_conj_apply_zero_zero]
  rw [Complex.star_def]
  apply Complex.ext
  · simp
  · simp

/-- The fundamental Chebyshev character is twice the real part of the
upper-left matrix entry. -/
theorem su2FundamentalCharacter_eq_two_mul_re (g : SU2) :
    su2CharacterChebyshev 1 g =
      ((2 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re : Real) : Complex) := by
  unfold su2CharacterChebyshev
  rw [su2_half_trace_eq_ofReal_re]
  simp [Polynomial.Chebyshev.U_one]

/-- The first even nontrivial character is the quadratic real-coordinate
observable `4 (Re g₀₀)² - 1`. -/
theorem su2CharacterChebyshev_two (g : SU2) :
    su2CharacterChebyshev 2 g =
      (((4 * ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re ^ 2 - 1 : Real)) :
        Complex) := by
  unfold su2CharacterChebyshev
  rw [su2_half_trace_eq_ofReal_re]
  change (Polynomial.Chebyshev.U Complex 2).eval
      (((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re : Complex) = _
  rw [Polynomial.Chebyshev.U_two]
  simp

/-- The Chebyshev argument `tr(g)/2` lies in the closed unit interval on
the real axis. -/
theorem norm_su2_half_trace_le_one (g : SU2) :
    ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) / 2‖ <= 1 := by
  rw [su2_half_trace_eq_ofReal_re, Complex.norm_real]
  exact (Complex.abs_re_le_norm _).trans (su2_norm_apply_zero_zero_le_one g)

/-- **Concrete SU(2) Weyl bound.**  The `(n+1)`-dimensional character is
bounded in norm by its dimension, with no representation-theory package
assumed. -/
theorem abs_su2CharacterChebyshev_le (n : Nat) (g : SU2) :
    ‖su2CharacterChebyshev n g‖ <= (n : Real) + 1 := by
  rw [su2CharacterChebyshev, su2_half_trace_eq_ofReal_re]
  apply norm_chebyshevU_complex_ofReal_le
  have h := norm_su2_half_trace_le_one g
  rw [su2_half_trace_eq_ofReal_re, Complex.norm_real] at h
  exact abs_le.mp h

/-- Matrix trace is invariant under conjugation by the concrete `SU(2)`
group operation. -/
theorem su2_trace_conj (x g : SU2) :
    Matrix.trace
        ((x * g * x⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) Complex) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex) := by
  change Matrix.trace
      (((x : Matrix (Fin 2) (Fin 2) Complex) *
        (g : Matrix (Fin 2) (Fin 2) Complex)) *
        ((x⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) Complex)) = _
  rw [Matrix.trace_mul_cycle]
  have hx := congrArg Subtype.val (inv_mul_cancel x)
  change
    ((x⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) Complex) *
        (x : Matrix (Fin 2) (Fin 2) Complex) = 1 at hx
  rw [hx, Matrix.one_mul]

/-- Every concrete Chebyshev character is a class function. -/
theorem su2CharacterChebyshev_conj_invariant (n : Nat) (x g : SU2) :
    su2CharacterChebyshev n (x * g * x⁻¹) = su2CharacterChebyshev n g := by
  unfold su2CharacterChebyshev
  rw [su2_trace_conj]

/-- Continuity of every concrete SU(2) character. -/
theorem continuous_su2CharacterChebyshev (n : Nat) :
    Continuous (su2CharacterChebyshev n) := by
  unfold su2CharacterChebyshev
  apply (Polynomial.Chebyshev.U Complex (n : Int)).continuous.comp
  have htrace : Continuous (fun g : SU2 =>
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex)) := by
    unfold Matrix.trace
    fun_prop
  fun_prop

/-- Every summand of the concrete SU(2) heat-kernel expansion is conjugation
invariant. -/
theorem su2HeatKernelTerm_conj_invariant
    (n : Nat) (t : Real) (x g : SU2) :
    heatKernelTerm su2CharacterTable t (x * g * x⁻¹) n =
      heatKernelTerm su2CharacterTable t g n := by
  change
    ((n + 1 : Nat) : Complex) * su2CharacterChebyshev n (x * g * x⁻¹) * _ =
      ((n + 1 : Nat) : Complex) * su2CharacterChebyshev n g * _
  rw [su2CharacterChebyshev_conj_invariant]

/-- The concrete SU(2) character series is a class function. -/
theorem su2HeatKernelCharacterSeries_conj_invariant
    (t : Real) (x g : SU2) :
    heatKernelCharacterSeries su2CharacterTable t (x * g * x⁻¹) =
      heatKernelCharacterSeries su2CharacterTable t g := by
  unfold heatKernelCharacterSeries
  apply tsum_congr
  exact fun n => su2HeatKernelTerm_conj_invariant n t x g

/-- Width-independent positive majorant for the concrete SU(2) heat-kernel
series. -/
def su2HeatKernelMajorant (t : Real) (n : Nat) : Real :=
  ((n : Real) + 1) ^ 2 *
    Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4)

/-- The SU(2) heat-kernel majorant is summable for every positive heat time. -/
theorem summable_su2HeatKernelMajorant {t : Real} (ht : 0 < t) :
    Summable (su2HeatKernelMajorant t) :=
  summable_su2_dim_sq_exp_neg_casimir ht

/-- Uniform norm domination of every SU(2) heat-kernel summand. -/
theorem norm_su2HeatKernelTerm_le_majorant
    (t : Real) (n : Nat) (g : SU2) :
    ‖heatKernelTerm su2CharacterTable t g n‖ <= su2HeatKernelMajorant t n := by
  change
    ‖(((n + 1 : Nat) : Complex) * su2CharacterChebyshev n g *
      ((Real.exp (-t * (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex))‖ <= _
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  push_cast
  unfold su2HeatKernelMajorant
  calc
    ((n : Real) + 1) * ‖su2CharacterChebyshev n g‖ *
        Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4))
        <= ((n : Real) + 1) * ((n : Real) + 1) *
          Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) := by
            gcongr
            exact abs_su2CharacterChebyshev_le n g
    _ = ((n : Real) + 1) ^ 2 *
          Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4) := by ring_nf

/-- Continuity of each concrete heat-kernel summand. -/
theorem continuous_su2HeatKernelTerm (t : Real) (n : Nat) :
    Continuous (fun g : SU2 => heatKernelTerm su2CharacterTable t g n) := by
  change Continuous (fun g : SU2 =>
    ((n + 1 : Nat) : Complex) * su2CharacterChebyshev n g * _)
  exact (continuous_const.mul (continuous_su2CharacterChebyshev n)).mul continuous_const

/-- **Uniform convergence on the whole compact gauge group.** -/
theorem tendstoUniformly_su2HeatKernelCharacterSeries {t : Real} (ht : 0 < t) :
    TendstoUniformly
      (fun N : Nat => fun g : SU2 =>
        ∑ n ∈ Finset.range N, heatKernelTerm su2CharacterTable t g n)
      (fun g : SU2 => heatKernelCharacterSeries su2CharacterTable t g)
      Filter.atTop := by
  apply tendstoUniformly_tsum_nat (summable_su2HeatKernelMajorant ht)
  exact fun n g => norm_su2HeatKernelTerm_le_majorant t n g

/-- The concrete SU(2) heat-kernel character series is continuous for every
positive heat time. -/
theorem continuous_su2HeatKernelCharacterSeries {t : Real} (ht : 0 < t) :
    Continuous (heatKernelCharacterSeries su2CharacterTable t) := by
  apply continuous_tsum
  · exact continuous_su2HeatKernelTerm t
  · exact summable_su2HeatKernelMajorant ht
  · exact fun n g => norm_su2HeatKernelTerm_le_majorant t n g

/-- The already-proved Casimir convergence engine yields pointwise
heat-kernel summability as soon as the concrete Weyl bound is supplied. -/
theorem summable_su2HeatKernelTerm_of_weylBound
    {t : Real} (ht : 0 < t) (g : SU2)
    (hWeyl : forall n : Nat, ‖su2CharacterChebyshev n g‖ <= (n : Real) + 1) :
    Summable (heatKernelTerm su2CharacterTable t g) := by
  have hmajor := summable_su2_dim_sq_exp_neg_casimir ht
  apply Summable.of_norm_bounded (g := fun n : Nat =>
    ((n : Real) + 1) ^ 2 *
      Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4)) hmajor
  intro n
  change
    ‖(((n + 1 : Nat) : Complex) * su2CharacterChebyshev n g *
      ((Real.exp (-t * (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex))‖ <=
      ((n : Real) + 1) ^ 2 *
        Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4)
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  push_cast
  calc
    ((n : Real) + 1) * ‖su2CharacterChebyshev n g‖ *
        Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4))
        <= ((n : Real) + 1) * ((n : Real) + 1) *
          Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) := by
            gcongr
            exact hWeyl n
    _ = ((n : Real) + 1) ^ 2 *
          Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4) := by ring_nf

/-- Unconditional pointwise convergence of the concrete SU(2) heat-kernel
character expansion for every positive heat time. -/
theorem summable_su2HeatKernelTerm {t : Real} (ht : 0 < t) (g : SU2) :
    Summable (heatKernelTerm su2CharacterTable t g) :=
  summable_su2HeatKernelTerm_of_weylBound ht g
    (fun n => abs_su2CharacterChebyshev_le n g)

end Lean2dYangMills
