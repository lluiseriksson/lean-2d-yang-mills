import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Lean2dYangMills.SU2Character

/-!
# SU(2) class-character orthogonality in Weyl angle coordinates

This file proves the analytic orthogonality identity underlying the SU(2)
Weyl integration formula.  It does not identify the resulting angle integral
with Mathlib's Haar measure on `Matrix.specialUnitaryGroup`; that pushforward
identity remains the group-theoretic frontier.
-/

noncomputable section

open scoped Interval

namespace Lean2dYangMills

open intervalIntegral

/-- A nonzero integral frequency has zero cosine integral over `[0, pi]`. -/
theorem integral_cos_int_mul_zero (k : Int) (hk : k ≠ 0) :
    (∫ theta : Real in 0..Real.pi, Real.cos ((k : Real) * theta)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos)
    (Int.cast_ne_zero.mpr hk)]
  simp

/-- Orthogonality of distinct positive integer sine modes on `[0, pi]`. -/
theorem integral_sin_natSucc_mul_sin_natSucc_of_ne
    {n m : Nat} (hnm : n ≠ m) :
    (∫ theta : Real in 0..Real.pi,
      Real.sin (((n + 1 : Nat) : Real) * theta) *
        Real.sin (((m + 1 : Nat) : Real) * theta)) = 0 := by
  have hsub : ((n + 1 : Int) - (m + 1 : Int)) ≠ 0 := by omega
  have hadd : ((n + 1 : Int) + (m + 1 : Int)) ≠ 0 := by omega
  have hpoint : (fun theta : Real =>
      Real.sin (((n + 1 : Nat) : Real) * theta) *
        Real.sin (((m + 1 : Nat) : Real) * theta)) =
      (fun theta : Real =>
        (Real.cos ((((n + 1 : Int) - (m + 1 : Int)) : Int) * theta) -
          Real.cos ((((n + 1 : Int) + (m + 1 : Int)) : Int) * theta)) / 2) := by
    funext theta
    push_cast
    rw [show ((n : Real) + 1 - ((m : Real) + 1)) * theta =
        ((n : Real) + 1) * theta - ((m : Real) + 1) * theta by ring]
    rw [show ((n : Real) + 1 + ((m : Real) + 1)) * theta =
        ((n : Real) + 1) * theta + ((m : Real) + 1) * theta by ring]
    rw [Real.cos_sub, Real.cos_add]
    ring
  rw [hpoint, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun theta : Real =>
      Real.cos ((((n + 1 : Int) - (m + 1 : Int)) : Int) * theta))).intervalIntegrable
        0 Real.pi)
    ((by fun_prop : Continuous (fun theta : Real =>
      Real.cos ((((n + 1 : Int) + (m + 1 : Int)) : Int) * theta))).intervalIntegrable
        0 Real.pi)]
  rw [integral_cos_int_mul_zero _ hsub, integral_cos_int_mul_zero _ hadd]
  simp

/-- Norm of every positive integer sine mode on `[0, pi]`. -/
theorem integral_sin_natSucc_sq (n : Nat) :
    (∫ theta : Real in 0..Real.pi,
      Real.sin (((n + 1 : Nat) : Real) * theta) ^ 2) = Real.pi / 2 := by
  have htwo : ((2 : Int) * (n + 1 : Int)) ≠ 0 := by omega
  have hpoint : (fun theta : Real =>
      Real.sin (((n + 1 : Nat) : Real) * theta) ^ 2) =
      (fun theta : Real =>
        (1 - Real.cos ((((2 : Int) * (n + 1 : Int)) : Int) * theta)) / 2) := by
    funext theta
    push_cast
    rw [show (2 : Real) * ((n : Real) + 1) * theta =
        2 * (((n : Real) + 1) * theta) by ring]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (((n : Real) + 1) * theta)]
  rw [hpoint, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 Real.pi)
    ((by fun_prop : Continuous (fun theta : Real =>
      Real.cos ((((2 : Int) * (n + 1 : Int)) : Int) * theta))).intervalIntegrable
        0 Real.pi)]
  rw [integral_cos_int_mul_zero _ htwo]
  simp

/-- **SU(2) class-character orthogonality in Weyl angle coordinates.** -/
theorem intervalIntegral_chebyshevU_mul_chebyshevU_sin_sq (n m : Nat) :
    (∫ theta : Real in 0..Real.pi,
      (Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
        (Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta) *
        Real.sin theta ^ 2) =
      if n = m then Real.pi / 2 else 0 := by
  have hpoint : (fun theta : Real =>
      (Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
        (Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta) *
        Real.sin theta ^ 2) =
      (fun theta : Real =>
        Real.sin (((n + 1 : Nat) : Real) * theta) *
          Real.sin (((m + 1 : Nat) : Real) * theta)) := by
    funext theta
    have hn := Polynomial.Chebyshev.U_real_cos theta (n : Int)
    have hm := Polynomial.Chebyshev.U_real_cos theta (m : Int)
    have hn' :
        (Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
          Real.sin theta = Real.sin (((n + 1 : Nat) : Real) * theta) := by
      convert hn using 1
      norm_num
    have hm' :
        (Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta) *
          Real.sin theta = Real.sin (((m + 1 : Nat) : Real) * theta) := by
      convert hm using 1
      norm_num
    calc
      (Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
          (Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta) *
          Real.sin theta ^ 2
          = ((Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
              Real.sin theta) *
            ((Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta) *
              Real.sin theta) := by ring
      _ = _ := by rw [hn', hm']
  rw [hpoint]
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl]
    simpa [pow_two] using integral_sin_natSucc_sq n
  · rw [if_neg hnm]
    exact integral_sin_natSucc_mul_sin_natSucc_of_ne hnm

end Lean2dYangMills
