import Mathlib
import Lean2dYangMills.Interfaces
import Lean2dYangMills.ConvergenceEngine

/-!
# Frontier: the SU(2) character table via Chebyshev polynomials

Statement-first targets for the real M0.  The character of the
`(n+1)`-dimensional irreducible representation of `SU(2)` is the Chebyshev
polynomial of the second kind evaluated at half the trace:
`χ_n(g) = U_n(tr(g)/2)`.  Mathlib has `Polynomial.Chebyshev.U`, so the
DEFINITION is available today; the theorems below are the frontier.  Every
`sorry` is tracked in `HYPOTHESIS_FRONTIER.md`; NEVER merge to `main`.

References: Migdal (1975); Driver (1989); standard SU(2) character theory,
e.g. Bump, "Lie Groups", Proposition 22.2.
-/

noncomputable section

namespace Lean2dYangMills

/-- The SU(2) character of the `(n+1)`-dimensional irrep, defined through
the Chebyshev polynomial of the second kind at half the trace. -/
def su2CharacterChebyshev (n : Nat) (g : SU2) : Complex :=
  (Polynomial.Chebyshev.U Complex (n : Int)).eval
    ((Matrix.trace (g : Matrix (Fin 2) (Fin 2) Complex)) / 2)

/-- The SU(2) character table with Casimir `n(n+2)/4` and heat weights
`exp(-t n(n+2)/4)`. -/
def su2CharacterTable : SU2CharacterTable where
  Label := Nat
  dim := fun n => n + 1
  dim_pos := fun n => Nat.succ_pos n
  char := su2CharacterChebyshev
  casimir := fun n => ((n : Real) * ((n : Real) + 2)) / 4
  heatWeight := fun t n =>
    ((Real.exp (-t * (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex)

/-- Character at the identity equals the dimension: `U_n(1) = n + 1`. -/
theorem su2CharacterChebyshev_one (n : Nat) :
    su2CharacterChebyshev n 1 = ((n : Complex) + 1) := by
  sorry

/-- Weyl bound: characters are bounded by the dimension.  The spectral
input is that SU(2) elements have unit-circle eigenvalues, hence
`|tr g| ≤ 2`. -/
theorem abs_su2CharacterChebyshev_le (n : Nat) (g : SU2) :
    ‖su2CharacterChebyshev n g‖ ≤ (n : Real) + 1 := by
  sorry

/-- M0 target: summability of the SU(2) heat-kernel character expansion for
every `t > 0` and every group element.  Route: the Weyl bound above feeds
`summable_pow_mul_exp_neg_casimir` (already proved on main). -/
theorem summable_su2HeatKernelTerm {t : Real} (ht : 0 < t) (g : SU2) :
    Summable (heatKernelTerm su2CharacterTable t g) := by
  sorry

/-- M0 target, package form: the SU(2) heat-kernel package exists with the
kernel defined by its character series and the semigroup proposition stated
via character orthogonality. -/
theorem exists_su2HeatKernelPackage :
    Nonempty SU2HeatKernelPackage := by
  sorry

end Lean2dYangMills
