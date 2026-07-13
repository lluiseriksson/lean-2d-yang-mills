import Lean2dYangMills.SU2Conjugacy
import Lean2dYangMills.SU2ClassHeatKernel

/-!
# Concrete group convolution on SU(2)

This file starts the translated (rather than merely class-sector) Haar
convolution layer.  The first theorem closes Schur convolution for the
fundamental character by an explicit quaternion-coordinate calculation.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace Lean2dYangMills

open Matrix MeasureTheory Set

def su2Convolution (f q : SU2 -> Complex) (g : SU2) : Complex :=
  ∫ x : SU2, f x * q (x⁻¹ * g) ∂su2HaarProb

private def su2A (g : SU2) : Real := g.1 0 0 |>.re
private def su2B (g : SU2) : Real := g.1 0 0 |>.im
private def su2C (g : SU2) : Real := g.1 0 1 |>.re
private def su2D (g : SU2) : Real := g.1 0 1 |>.im

private theorem su2PhaseI_mul_B (g : SU2) :
    su2B (su2PhaseI * g) = su2A g := by
  rw [su2B, su2A, su2PhaseI_mul_apply_zero_zero]
  simp [Complex.mul_im]

private theorem integral_su2A_mul_su2B :
    (∫ x : SU2, su2A x * su2B x ∂su2HaarProb) = 0 := by
  have hinv := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun x : SU2 => su2A x * su2B x) su2PhaseI
  have htrans : (fun x : SU2 => su2A (su2PhaseI * x) * su2B (su2PhaseI * x)) =
      (fun x : SU2 => -(su2A x * su2B x)) := by
    funext x
    rw [show su2A (su2PhaseI * x) = -su2B x by
      exact su2PhaseI_mul_apply_zero_zero_re x]
    rw [su2PhaseI_mul_B]
    ring
  rw [htrans, integral_neg] at hinv
  linarith

private theorem integral_su2A_mul_su2C :
    (∫ x : SU2, su2A x * su2C x ∂su2HaarProb) = 0 := by
  have hinv := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun x : SU2 => su2A x * su2C x) su2QuarterTurn
  have htrans :
      (fun x : SU2 => su2A (su2QuarterTurn * x) * su2C (su2QuarterTurn * x)) =
        (fun x : SU2 => -(su2A x * su2C x)) := by
    funext x
    rw [show su2A (su2QuarterTurn * x) = su2C x by
      exact su2QuarterTurn_mul_apply_zero_zero_re x]
    rw [show su2C (su2QuarterTurn * x) = -su2A x by
      exact su2QuarterTurn_mul_apply_zero_one_re x]
    ring
  rw [htrans, integral_neg] at hinv
  linarith

private theorem su2PhaseI_mul_D (g : SU2) :
    su2D (su2PhaseI * g) = su2C g := by
  simp [su2D, su2C, su2PhaseI, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_im]

private theorem su2QuarterTurn_mul_D (g : SU2) :
    su2D (su2QuarterTurn * g) = su2B g := by
  rw [su2D, su2B]
  simp [su2QuarterTurn, Matrix.mul_apply, Fin.sum_univ_two]
  rw [su2_apply_one_one_eq_conj_apply_zero_zero]
  simp

private theorem integral_su2A_mul_su2D :
    (∫ x : SU2, su2A x * su2D x ∂su2HaarProb) = 0 := by
  let q : SU2 -> Real := fun x => su2B x * su2C x
  have hphase := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun x : SU2 => su2A x * su2D x) su2PhaseI
  have hquarter := integral_mul_left_eq_self (μ := su2HaarProb)
    (fun x : SU2 => su2A x * su2D x) su2QuarterTurn
  have hp : (fun x : SU2 => su2A (su2PhaseI * x) * su2D (su2PhaseI * x)) =
      (fun x : SU2 => -q x) := by
    funext x
    rw [show su2A (su2PhaseI * x) = -su2B x by
      exact su2PhaseI_mul_apply_zero_zero_re x]
    rw [su2PhaseI_mul_D]
    dsimp [q]
    ring
  have hq : (fun x : SU2 => su2A (su2QuarterTurn * x) *
      su2D (su2QuarterTurn * x)) = q := by
    funext x
    rw [show su2A (su2QuarterTurn * x) = su2C x by
      exact su2QuarterTurn_mul_apply_zero_zero_re x]
    rw [su2QuarterTurn_mul_D]
    dsimp [q]
    ring
  rw [hp, integral_neg] at hphase
  rw [hq] at hquarter
  linarith

private theorem su2HalfTrace_inv_mul (x g : SU2) :
    su2HalfTrace (x⁻¹ * g) =
      su2A x * su2A g + su2B x * su2B g +
        su2C x * su2C g + su2D x * su2D g := by
  rw [su2HalfTrace]
  change ((star x.1 * g.1) 0 0).re = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show (star x.1) 0 0 = star (x.1 0 0) by
    simp [Matrix.star_eq_conjTranspose],
    show (star x.1) 0 1 = -x.1 0 1 by
      simp [Matrix.star_eq_conjTranspose,
        su2_apply_one_zero_eq_neg_conj_apply_zero_one]]
  rw [su2_apply_one_zero_eq_neg_conj_apply_zero_one]
  have hx00 : star (x.1 0 0) =
      ({ re := su2A x, im := -su2B x } : Complex) := rfl
  have hg01 : star (g.1 0 1) =
      ({ re := su2C g, im := -su2D g } : Complex) := rfl
  rw [hx00, hg01]
  simp [su2A, su2B, su2C, su2D, Complex.mul_re]
  ring

theorem su2FundamentalCharacter_convolution (g : SU2) :
    su2Convolution (su2CharacterChebyshev 1) (su2CharacterChebyshev 1) g =
      (1 / 2 : Complex) * su2CharacterChebyshev 1 g := by
  rw [su2Convolution]
  have hpoint : (fun x : SU2 =>
      su2CharacterChebyshev 1 x * su2CharacterChebyshev 1 (x⁻¹ * g)) =
      (fun x : SU2 => (((4 * su2A x *
        (su2A x * su2A g + su2B x * su2B g +
          su2C x * su2C g + su2D x * su2D g) : Real)) : Complex)) := by
    funext x
    rw [su2FundamentalCharacter_eq_two_mul_re,
      su2FundamentalCharacter_eq_two_mul_re]
    rw [show ((x⁻¹ * g : SU2).1 0 0).re = su2HalfTrace (x⁻¹ * g) by rfl,
      su2HalfTrace_inv_mul]
    norm_cast
    unfold su2A su2B su2C su2D
    ring
  rw [hpoint, integral_complex_ofReal]
  have hA2 : (∫ x : SU2, su2A x ^ 2 ∂su2HaarProb) = 1 / 4 := by
    exact integral_su2_re_zero_zero_sq
  have hAB := integral_su2A_mul_su2B
  have hAC := integral_su2A_mul_su2C
  have hAD := integral_su2A_mul_su2D
  have hcontA : Integrable (fun x : SU2 => su2A x ^ 2) su2HaarProb := by
    exact integrable_continuous_su2_real
      ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).pow 2)
  have hcontAB : Integrable (fun x : SU2 => su2A x * su2B x) su2HaarProb := by
    exact integrable_continuous_su2_real
      ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).mul
        (Complex.continuous_im.comp (continuous_su2_entry 0 0)))
  have hcontAC : Integrable (fun x : SU2 => su2A x * su2C x) su2HaarProb := by
    exact integrable_continuous_su2_real
      ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).mul
        (Complex.continuous_re.comp (continuous_su2_entry 0 1)))
  have hcontAD : Integrable (fun x : SU2 => su2A x * su2D x) su2HaarProb := by
    exact integrable_continuous_su2_real
      ((Complex.continuous_re.comp (continuous_su2_entry 0 0)).mul
        (Complex.continuous_im.comp (continuous_su2_entry 0 1)))
  rw [show (fun x : SU2 => 4 * su2A x *
      (su2A x * su2A g + su2B x * su2B g +
        su2C x * su2C g + su2D x * su2D g)) =
      (fun x : SU2 =>
        (4 * su2A g) * su2A x ^ 2 +
        (4 * su2B g) * (su2A x * su2B x) +
        (4 * su2C g) * (su2A x * su2C x) +
        (4 * su2D g) * (su2A x * su2D x)) by
      funext x; ring]
  have hIAint := hcontA.const_mul (4 * su2A g)
  have hIBint := hcontAB.const_mul (4 * su2B g)
  have hICint := hcontAC.const_mul (4 * su2C g)
  have hIDint := hcontAD.const_mul (4 * su2D g)
  have hreal : (∫ x : SU2,
      (4 * su2A g) * su2A x ^ 2 +
        (4 * su2B g) * (su2A x * su2B x) +
        (4 * su2C g) * (su2A x * su2C x) +
        (4 * su2D g) * (su2A x * su2D x) ∂su2HaarProb) = su2A g := by
    rw [show (fun x : SU2 =>
        (4 * su2A g) * su2A x ^ 2 +
          (4 * su2B g) * (su2A x * su2B x) +
          (4 * su2C g) * (su2A x * su2C x) +
          (4 * su2D g) * (su2A x * su2D x)) =
        (fun x => (4 * su2A g) * su2A x ^ 2) +
          (fun x => (4 * su2B g) * (su2A x * su2B x)) +
          (fun x => (4 * su2C g) * (su2A x * su2C x)) +
          (fun x => (4 * su2D g) * (su2A x * su2D x)) by rfl]
    rw [integral_add' ((hIAint.add hIBint).add hICint) hIDint,
      integral_add' (hIAint.add hIBint) hICint,
      integral_add' hIAint hIBint,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, hA2, hAB, hAC, hAD]
    ring
  rw [hreal]
  rw [su2FundamentalCharacter_eq_two_mul_re]
  dsimp [su2A]
  push_cast
  ring

/-- The fundamental irreducible sector of the SU(2) heat-kernel density. -/
def su2FundamentalFaceDensity (t : Real) (g : SU2) : Complex :=
  2 * su2ClassHeatWeight t 1 * su2CharacterChebyshev 1 g

/-- A genuine translated two-face Migdal merge in the first nontrivial
irreducible sector.  The shared variable occurs as `x` and `x⁻¹ g`, and the
proof consumes the concrete group convolution theorem above. -/
theorem su2Migdal_twoFace_fundamental_merge (s t : Real) (g : SU2) :
    (∫ x : SU2,
      su2FundamentalFaceDensity s x *
        su2FundamentalFaceDensity t (x⁻¹ * g) ∂su2HaarProb) =
      su2FundamentalFaceDensity (s + t) g := by
  rw [show (fun x : SU2 =>
      su2FundamentalFaceDensity s x *
        su2FundamentalFaceDensity t (x⁻¹ * g)) =
      (fun x : SU2 =>
        (4 * su2ClassHeatWeight s 1 * su2ClassHeatWeight t 1) *
          (su2CharacterChebyshev 1 x *
            su2CharacterChebyshev 1 (x⁻¹ * g))) by
      funext x
      simp [su2FundamentalFaceDensity]
      ring]
  calc
    (∫ x : SU2,
        (4 * su2ClassHeatWeight s 1 * su2ClassHeatWeight t 1) *
          (su2CharacterChebyshev 1 x *
            su2CharacterChebyshev 1 (x⁻¹ * g)) ∂su2HaarProb) =
        (4 * su2ClassHeatWeight s 1 * su2ClassHeatWeight t 1) *
          su2Convolution (su2CharacterChebyshev 1)
            (su2CharacterChebyshev 1) g :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := by
      rw [su2FundamentalCharacter_convolution]
      calc
        4 * su2ClassHeatWeight s 1 * su2ClassHeatWeight t 1 *
            (1 / 2 * su2CharacterChebyshev 1 g) =
            2 * (su2ClassHeatWeight s 1 * su2ClassHeatWeight t 1) *
              su2CharacterChebyshev 1 g := by ring
        _ = 2 * su2ClassHeatWeight (s + t) 1 *
              su2CharacterChebyshev 1 g := by
          rw [su2ClassHeatWeight_add]
        _ = su2FundamentalFaceDensity (s + t) g := rfl

end Lean2dYangMills
