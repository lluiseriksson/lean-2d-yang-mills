import Lean2dYangMills.Interfaces
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Witten zeta function of SU(2) is the Riemann zeta function

The irreducible representations of `SU(2)` have dimensions `1, 2, 3, ...`,
so the Witten zeta series `Σ_λ dim(λ)^{-s}` is literally `Σ_{n≥1} n^{-s}`.
This file closes milestone M4's convergence layer unconditionally:
`su2WittenZetaPackage` instantiates `WittenZetaPackage` with
`zeta := riemannZeta`, discharging both hypothesis fields.  This is the
Riemann bridge of the satellite: the surface partition functions of 2D
Yang-Mills at zero area are special values of the Riemann zeta function.

Only the dimension data of `SU(2)` is used (no matrix representation theory
is needed for the zeta layer), so this closure does not anticipate the
shared Peter-Weyl layer.

References: Witten (1991, Commun. Math. Phys. 141, 153-209), Section 4;
Zagier (1994, First European Congress of Mathematics, Vol. II, 497-512).
-/

noncomputable section

namespace Lean2dYangMills

/-- SU(2) representation-dimension data: `dim(n) = n + 1`, zeta term
`(n+1)^{-s}`. -/
def su2WittenZetaData : WittenZetaData where
  Label := Nat
  dim := fun n => n + 1
  dim_pos := fun n => Nat.succ_pos n
  zetaTerm := fun s n => ((n : Complex) + 1) ^ (-s)

@[simp]
theorem su2WittenZetaTerm_eq (s : Complex) (n : Nat) :
    wittenZetaTerm su2WittenZetaData s n = ((n : Complex) + 1) ^ (-s) :=
  rfl

/-- Convergence of the SU(2) Witten zeta series for `1 < Re s`. -/
theorem summable_su2WittenZetaTerm {s : Complex} (hs : 1 < s.re) :
    Summable (wittenZetaTerm su2WittenZetaData s) := by
  have h0 : Summable (fun n : Nat => 1 / (n : Complex) ^ s) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  have h1 : Summable (fun n : Nat => 1 / ((n + 1 : Nat) : Complex) ^ s) :=
    (summable_nat_add_iff 1).mpr h0
  refine h1.congr fun n => ?_
  simp [wittenZetaTerm, su2WittenZetaData, Complex.cpow_neg, one_div]

/-- **The SU(2) Witten zeta package, with `zeta := riemannZeta`.**  Both
hypothesis fields are theorems: the first fully unconditional instance of a
package in this repository. -/
def su2WittenZetaPackage : WittenZetaPackage su2WittenZetaData where
  zeta := riemannZeta
  zeta_summable := fun hs => summable_su2WittenZetaTerm hs
  zeta_eq_tsum := by
    intro s hs
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact tsum_congr fun n => by
      simp [wittenZetaTerm, su2WittenZetaData, Complex.cpow_neg, one_div]

/-- **The Witten zeta function of SU(2) IS the Riemann zeta function** on
the convergence half-plane. -/
theorem su2_wittenZetaSeries_eq_riemannZeta {s : Complex} (hs : 1 < s.re) :
    wittenZetaSeries su2WittenZetaData s = riemannZeta s :=
  (wittenZeta_eq_tsum su2WittenZetaPackage hs).symm

/-- The genus argument `2g - 2` has real part `2g - 2`. -/
theorem genusZetaArgument_re (g : Nat) :
    (genusZetaArgument g).re = 2 * (g : Real) - 2 := by
  unfold genusZetaArgument
  rw [Complex.intCast_re]
  push_cast
  ring

/-- Genus at least two puts the genus argument in the convergence
half-plane. -/
theorem one_lt_genusZetaArgument_re {g : Nat} (hg : 2 ≤ g) :
    1 < (genusZetaArgument g).re := by
  rw [genusZetaArgument_re]
  have h : (2 : Real) ≤ (g : Real) := by exact_mod_cast hg
  linarith

/-- The zero-area (topological) limit of 2D Yang-Mills on closed genus-`g`
surfaces, `2 ≤ g`: the partition function is DEFINED as the
representation-dimension series, so the package equality is definitional —
this instance is a consumer test of the M4 interface, but its
`partition_summable` field is genuine convergence content.  The analytic M4
(heat-kernel partition functions at positive area converging to this as the
area tends to zero) remains open and is stated on the frontier. -/
def su2ZeroAreaSurfaceModel : WittenZetaSurfacePackage su2WittenZetaData where
  Surface := {g : Nat // 2 ≤ g}
  partitionFunction := fun S =>
    wittenZetaSeries su2WittenZetaData (genusZetaArgument S.1)
  zetaArgument := fun S => genusZetaArgument S.1
  partition_summable := fun S =>
    summable_su2WittenZetaTerm (one_lt_genusZetaArgument_re S.2)
  partition_eq_zeta := fun _ => rfl

/-- Consumer theorem: the public M4 surface-partition wrapper applies to the
zero-area SU(2) genus model. -/
theorem su2ZeroArea_partition_eq_wittenZetaSeries (S : {g : Nat // 2 ≤ g}) :
    su2ZeroAreaSurfaceModel.partitionFunction S
      = wittenZetaSeries su2WittenZetaData (genusZetaArgument S.1) := by
  change su2ZeroAreaSurfaceModel.partitionFunction S
    = wittenZetaSeries su2WittenZetaData (su2ZeroAreaSurfaceModel.zetaArgument S)
  exact surfacePartitionFunction_eq_wittenZeta su2ZeroAreaSurfaceModel S

/-- Consumer theorem: the public M4 Witten-zeta convergence wrapper applies
to the zero-area SU(2) genus model's zeta argument. -/
theorem su2ZeroArea_wittenZetaSeries_converges (S : {g : Nat // 2 ≤ g}) :
    Summable (wittenZetaTerm su2WittenZetaData (genusZetaArgument S.1)) :=
  wittenZeta_converges su2WittenZetaPackage (one_lt_genusZetaArgument_re S.2)

/-- Consumer theorem: the public M4 surface summability wrapper applies to
the zero-area SU(2) genus model. -/
theorem su2ZeroArea_surfacePartitionSeries_summable (S : {g : Nat // 2 ≤ g}) :
    Summable
      (wittenZetaTerm su2WittenZetaData (su2ZeroAreaSurfaceModel.zetaArgument S)) :=
  surfacePartitionFunction_summable su2ZeroAreaSurfaceModel S

/-- Zero-area genus-`g` partition functions are special values of the
Riemann zeta function: `Z_g = ζ(2g - 2)`. -/
theorem su2ZeroArea_partition_eq_riemannZeta (S : {g : Nat // 2 ≤ g}) :
    su2ZeroAreaSurfaceModel.partitionFunction S
      = riemannZeta (genusZetaArgument S.1) :=
  su2_wittenZetaSeries_eq_riemannZeta (one_lt_genusZetaArgument_re S.2)

end Lean2dYangMills
