import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Convergence engine for dimension-weighted heat-kernel series

The M0 character expansion of the SU(2) heat kernel has terms bounded by
`(n+1)^k * exp(-t * n)`-type quantities.  This file proves the summability
engine those bounds feed, with no representation theory: polynomial weights
against exponential decay are summable for every `t > 0`.

Reference target: Migdal (1975, Sov. Phys. JETP 42, 413-418) heat-kernel
weights; Driver (1989, Commun. Math. Phys. 123, 575-616).
-/

namespace Lean2dYangMills

/-- Polynomial-times-exponential summability: for `t > 0` and every `k`,
`Σ (n+1)^k exp(-t n) < ∞`.  This is the convergence engine for the M0
heat-kernel character expansion. -/
theorem summable_pow_mul_exp_neg {t : Real} (ht : 0 < t) (k : Nat) :
    Summable (fun n : Nat => ((n : Real) + 1) ^ k * Real.exp (-t * n)) := by
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : Summable (fun n : Nat => (n : Real) ^ k * Real.exp (-t) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have h1 : Summable
      (fun n : Nat => ((n + 1 : Nat) : Real) ^ k * Real.exp (-t) ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr h0
  have h2 := h1.mul_left (Real.exp t)
  refine h2.congr fun n => ?_
  have e1 : Real.exp t * Real.exp (-t) ^ (n + 1) = Real.exp (-t * n) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc Real.exp t * (((n + 1 : Nat) : Real) ^ k * Real.exp (-t) ^ (n + 1))
      = ((n + 1 : Nat) : Real) ^ k
          * (Real.exp t * Real.exp (-t) ^ (n + 1)) := by ring
    _ = ((n : Real) + 1) ^ k * Real.exp (-t * n) := by
        rw [e1]
        push_cast
        ring

/-- Variant with the Casimir-style quadratic decay `exp(-t n (n+2) / 4)`:
dominated by the linear-decay engine. -/
theorem summable_pow_mul_exp_neg_casimir {t : Real} (ht : 0 < t) (k : Nat) :
    Summable (fun n : Nat =>
      ((n : Real) + 1) ^ k * Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_pow_mul_exp_neg (t := t / 4) (by linarith) k)
  have hn : (n : Real) ≤ (n : Real) * ((n : Real) + 2) := by
    nlinarith [Nat.cast_nonneg (α := Real) n]
  have key : t * (n : Real) ≤ t * ((n : Real) * ((n : Real) + 2)) :=
    mul_le_mul_of_nonneg_left hn ht.le
  have hbase : Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4)
      ≤ Real.exp (-(t / 4) * n) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpow : (0 : Real) ≤ ((n : Real) + 1) ^ k := by positivity
  exact mul_le_mul_of_nonneg_left hbase hpow

end Lean2dYangMills
