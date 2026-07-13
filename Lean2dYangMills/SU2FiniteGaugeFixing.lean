import Lean2dYangMills.SU2EdgeGaugeFixing
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-valence product-Haar gauge fixing

This module replaces the two physical coordinates in the three-spoke example
by an arbitrary finite family.  For a finite type `I`, it constructs the
triangular change of variables

`(x, y) ↦ (x, fun i => x⁻¹ * y i)`

on `SU2 × (I -> SU2)`, proves that it preserves normalized Haar on every
coordinate, and derives a general integral-elimination theorem for densities
that lose the first coordinate after the inverse substitution.

This is a uniform gauge fixing at one vertex of arbitrary finite valence.  It
is deliberately not advertised as the still-open global spanning-tree gauge
fixing for every vertex of an arbitrary disk cellulation.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- Normalized product Haar on an arbitrary finite family of SU(2) variables. -/
def su2FiniteProductHaar (I : Type) [Fintype I] : Measure (I -> SU2) :=
  Measure.pi (fun _ : I => su2HaarProb)

instance instIsProbabilityMeasureSU2FiniteProductHaar
    (I : Type) [Fintype I] :
    IsProbabilityMeasure (su2FiniteProductHaar I) := by
  unfold su2FiniteProductHaar
  infer_instance

instance instIsMulLeftInvariantSU2FiniteProductHaar
    (I : Type) [Fintype I] :
    Measure.IsMulLeftInvariant (su2FiniteProductHaar I) := by
  unfold su2FiniteProductHaar
  infer_instance

/-- Product Haar on one anchor variable and an arbitrary finite family of
incident edge variables. -/
def su2FiniteStarHaar (I : Type) [Fintype I] :
    Measure (SU2 × (I -> SU2)) :=
  su2HaarProb.prod (su2FiniteProductHaar I)

instance instIsProbabilityMeasureSU2FiniteStarHaar
    (I : Type) [Fintype I] :
    IsProbabilityMeasure (su2FiniteStarHaar I) := by
  unfold su2FiniteStarHaar
  infer_instance

instance instIsMulLeftInvariantSU2FiniteStarHaar
    (I : Type) [Fintype I] :
    Measure.IsMulLeftInvariant (su2FiniteStarHaar I) := by
  unfold su2FiniteStarHaar
  infer_instance

/-- The diagonal gauge action at the common vertex. -/
def su2FiniteStarDiagonalLeft (I : Type) [Fintype I]
    (u : SU2) (p : SU2 × (I -> SU2)) : SU2 × (I -> SU2) :=
  (u * p.1, fun i => u * p.2 i)

/-- The diagonal action itself preserves the finite product Haar measure. -/
theorem su2FiniteStarDiagonalLeft_measurePreserving
    (I : Type) [Fintype I] (u : SU2) :
    MeasurePreserving (su2FiniteStarDiagonalLeft I u)
      (su2FiniteStarHaar I) (su2FiniteStarHaar I) := by
  simpa [su2FiniteStarDiagonalLeft] using
    (measurePreserving_mul_left (su2FiniteStarHaar I)
      (u, fun _ : I => u))

/-- Simultaneous triangular gauge fixing at a vertex of finite valence. -/
def su2FiniteStarGaugeFixEquiv (I : Type) [Fintype I] :
    (SU2 × (I -> SU2)) ≃ᵐ (SU2 × (I -> SU2)) where
  toEquiv :=
    { toFun := fun p => (p.1, fun i => p.1⁻¹ * p.2 i)
      invFun := fun p => (p.1, fun i => p.1 * p.2 i)
      left_inv := by
        rintro ⟨x, y⟩
        ext <;> simp
      right_inv := by
        rintro ⟨x, y⟩
        ext <;> simp }
  measurable_toFun := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    exact continuous_mul.measurable2
      (measurable_inv.comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd)
  measurable_invFun := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    exact continuous_mul.measurable2 measurable_fst
      ((measurable_pi_apply i).comp measurable_snd)

/-- The arbitrary-finite-valence triangular change of variables preserves the
literal product of normalized Haar probabilities. -/
theorem su2FiniteStarGaugeFix_measurePreserving
    (I : Type) [Fintype I] :
    MeasurePreserving (su2FiniteStarGaugeFixEquiv I)
      (su2FiniteStarHaar I) (su2FiniteStarHaar I) := by
  unfold su2FiniteStarHaar
  have hmeas : Measurable (Function.uncurry
      (fun x : SU2 => fun y : I -> SU2 => fun i => x⁻¹ * y i)) := by
    refine measurable_pi_lambda _ fun i => ?_
    exact continuous_mul.measurable2
      (measurable_inv.comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd)
  have hskew := (MeasurePreserving.id su2HaarProb).skew_product
    (μc := su2FiniteProductHaar I)
    (μd := su2FiniteProductHaar I)
    (g := fun x : SU2 => fun y : I -> SU2 => fun i => x⁻¹ * y i)
    hmeas (ae_of_all _ fun x => by
      simpa [su2FiniteProductHaar] using
        (measurePreserving_mul_left
          (su2FiniteProductHaar I) (fun _ : I => x⁻¹)).map_eq)
  simpa only [id_eq, su2FiniteStarGaugeFixEquiv] using hskew

/-- General finite-valence gauge-coordinate elimination.  If an unreduced
density becomes independent of the anchor coordinate after inverse gauge
substitution, its original product-Haar integral is exactly the integral of
the reduced density over the remaining finite family. -/
theorem su2FiniteStar_integral_eq_gaugeFixed
    (I : Type) [Fintype I]
    (F : SU2 × (I -> SU2) -> Complex) (f : (I -> SU2) -> Complex)
    (hfactor : ∀ p,
      F ((su2FiniteStarGaugeFixEquiv I).symm p) = f p.2) :
    (∫ p, F p ∂su2FiniteStarHaar I) =
      ∫ y, f y ∂su2FiniteProductHaar I := by
  have hinv : MeasurePreserving (su2FiniteStarGaugeFixEquiv I).symm
      (su2FiniteStarHaar I) (su2FiniteStarHaar I) :=
    MeasurePreserving.symm (su2FiniteStarGaugeFixEquiv I)
      (su2FiniteStarGaugeFix_measurePreserving I)
  calc
    (∫ p, F p ∂su2FiniteStarHaar I) =
        ∫ p, F ((su2FiniteStarGaugeFixEquiv I).symm p)
          ∂su2FiniteStarHaar I := by
      exact (hinv.integral_comp' F).symm
    _ = ∫ p, f p.2 ∂su2FiniteStarHaar I := by
      apply integral_congr_ae
      exact ae_of_all _ hfactor
    _ = ∫ y, f y ∂su2FiniteProductHaar I := by
      unfold su2FiniteStarHaar
      rw [integral_fun_snd]
      simp

/-- A diagonal-gauge-invariant density automatically satisfies the
factorization premise: its finite product-Haar integral is obtained by fixing
the anchor edge to the identity and integrating only the relative variables. -/
theorem su2FiniteStar_integral_eq_identitySlice
    (I : Type) [Fintype I]
    (F : SU2 × (I -> SU2) -> Complex)
    (hdiag : ∀ (u : SU2) (p : SU2 × (I -> SU2)),
      F (su2FiniteStarDiagonalLeft I u p) = F p) :
    (∫ p, F p ∂su2FiniteStarHaar I) =
      ∫ y, F (1, y) ∂su2FiniteProductHaar I := by
  apply su2FiniteStar_integral_eq_gaugeFixed I F (fun y => F (1, y))
  rintro ⟨u, y⟩
  simpa [su2FiniteStarGaugeFixEquiv, su2FiniteStarDiagonalLeft] using
    (hdiag u (1, y))

end Lean2dYangMills
