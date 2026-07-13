import Lean2dYangMills.SU2FiniteCellulation
import Mathlib.MeasureTheory.Group.Prod

/-!
# A genuine product-Haar gauge fixing for a cyclic three-face disk

This module starts from three original spoke-edge variables `x,y,z`.  With
fixed boundary arcs `a,b,c`, the three face holonomies are

`x*a*y⁻¹`, `y*b*z⁻¹`, and `z*c*x⁻¹`.

The corresponding face-dual graph is a three-cycle.  Simultaneous left
multiplication of the three spokes is the gauge action at the interior vertex.
The change of variables

`(x,y,z) ↦ (x, x⁻¹*y, x⁻¹*z)`

is constructed as a measurable equivalence and proved to preserve the actual
triple product of normalized SU(2) Haar measure.  The density becomes
independent of the first (pure-gauge) coordinate, after which two concrete
Migdal integrations collapse the original edge integral to one heat kernel.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

set_option maxHeartbeats 800000

/-- The previously constructed homeomorphism `SU(2) ≃ S³` transports the
second-countable topology needed for joint Borel measurability. -/
instance instSecondCountableTopologySU2GaugeFixing :
    SecondCountableTopology SU2 :=
  su2HomeomorphRowSphere.secondCountableTopology

/-- Joint multiplication on concrete SU(2) is Borel measurable. -/
instance instMeasurableMulTwoSU2GaugeFixing : MeasurableMul₂ SU2 where
  measurable_mul := continuous_mul.measurable

/-- The face-dual graph of the three-spoke disk.  On three vertices the
complete graph is exactly the three-cycle: every pair of distinct faces
shares one of the spoke edges. -/
def su2ThreeSpokeFaceDual : SimpleGraph (Fin 3) := ⊤

@[simp] theorem su2ThreeSpokeFaceDual_adj_iff (i j : Fin 3) :
    su2ThreeSpokeFaceDual.Adj i j ↔ i ≠ j := by
  simp [su2ThreeSpokeFaceDual]

theorem su2ThreeSpokeFaceDual_connected :
    su2ThreeSpokeFaceDual.Connected := by
  simp [su2ThreeSpokeFaceDual]

/-- Product Haar on the three original spoke edges, parenthesized as
`x × (y × z)`. -/
def su2ThreeEdgeHaar : Measure (SU2 × (SU2 × SU2)) :=
  su2HaarProb.prod (su2HaarProb.prod su2HaarProb)

/-- Product Haar on the two physical coordinates left after fixing the
interior-vertex gauge. -/
def su2TwoEdgeHaar : Measure (SU2 × SU2) :=
  su2HaarProb.prod su2HaarProb

instance instIsFiniteMeasureSU2TwoEdgeHaar :
    IsFiniteMeasure su2TwoEdgeHaar := by
  unfold su2TwoEdgeHaar
  infer_instance

instance instIsFiniteMeasureSU2ThreeEdgeHaar :
    IsFiniteMeasure su2ThreeEdgeHaar := by
  unfold su2ThreeEdgeHaar
  infer_instance

/-- The explicit triangular gauge-fixing equivalence. -/
def su2ThreeSpokeGaugeFixEquiv :
    (SU2 × (SU2 × SU2)) ≃ᵐ (SU2 × (SU2 × SU2)) where
  toEquiv :=
    { toFun := fun p =>
        (p.1, (p.1⁻¹ * p.2.1, p.1⁻¹ * p.2.2))
      invFun := fun p =>
        (p.1, (p.1 * p.2.1, p.1 * p.2.2))
      left_inv := by
        rintro ⟨x, y, z⟩
        simp
      right_inv := by
        rintro ⟨x, y, z⟩
        simp }
  measurable_toFun := by
    have hx : Measurable (fun p : SU2 × (SU2 × SU2) => p.1⁻¹) :=
      measurable_inv.comp measurable_fst
    have hy : Measurable (fun p : SU2 × (SU2 × SU2) => p.2.1) :=
      measurable_fst.comp measurable_snd
    have hz : Measurable (fun p : SU2 × (SU2 × SU2) => p.2.2) :=
      measurable_snd.comp measurable_snd
    exact measurable_fst.prodMk
      ((continuous_mul.measurable2 hx hy).prodMk
        (continuous_mul.measurable2 hx hz))
  measurable_invFun := by
    have hy : Measurable (fun p : SU2 × (SU2 × SU2) => p.2.1) :=
      measurable_fst.comp measurable_snd
    have hz : Measurable (fun p : SU2 × (SU2 × SU2) => p.2.2) :=
      measurable_snd.comp measurable_snd
    exact measurable_fst.prodMk
      ((continuous_mul.measurable2 measurable_fst hy).prodMk
        (continuous_mul.measurable2 measurable_fst hz))

/-- The triangular three-spoke gauge fixing preserves the genuine product
Haar measure.  This is derived from Haar invariance by the skew-product
theorem; it is not a certificate field. -/
theorem su2ThreeSpokeGaugeFix_measurePreserving :
    MeasurePreserving su2ThreeSpokeGaugeFixEquiv
      su2ThreeEdgeHaar su2ThreeEdgeHaar := by
  unfold su2ThreeEdgeHaar
  have h : MeasurePreserving
      (fun p : SU2 × (SU2 × SU2) =>
        (p.1, (p.1⁻¹ * p.2.1, p.1⁻¹ * p.2.2)))
      (su2HaarProb.prod (su2HaarProb.prod su2HaarProb))
      (su2HaarProb.prod (su2HaarProb.prod su2HaarProb)) := by
    have hmeas : Measurable (Function.uncurry
        (fun x : SU2 => fun yz : SU2 × SU2 =>
          (x⁻¹ * yz.1, x⁻¹ * yz.2))) := by
      have hx : Measurable
          (fun p : SU2 × (SU2 × SU2) => p.1⁻¹) :=
        measurable_inv.comp measurable_fst
      have hy : Measurable
          (fun p : SU2 × (SU2 × SU2) => p.2.1) :=
        measurable_fst.comp measurable_snd
      have hz : Measurable
          (fun p : SU2 × (SU2 × SU2) => p.2.2) :=
        measurable_snd.comp measurable_snd
      exact (continuous_mul.measurable2 hx hy).prodMk
        (continuous_mul.measurable2 hx hz)
    have hskew := (MeasurePreserving.id su2HaarProb).skew_product
      (μc := su2HaarProb.prod su2HaarProb)
      (μd := su2HaarProb.prod su2HaarProb)
      (g := fun x : SU2 => fun yz : SU2 × SU2 =>
        (x⁻¹ * yz.1, x⁻¹ * yz.2)) hmeas (ae_of_all _ fun x => by
        simpa using
          (measurePreserving_mul_left
            (su2HaarProb.prod su2HaarProb) (x⁻¹, x⁻¹)).map_eq)
    simpa only [id_eq] using hskew
  simpa [su2ThreeSpokeGaugeFixEquiv] using h

/-- The concrete heat kernel is a class function. -/
theorem su2HeatKernel_conj_invariant
    (t : Real) (x g : SU2) :
    su2HeatKernel t (x * g * x⁻¹) = su2HeatKernel t g :=
  su2HeatKernelCharacterSeries_conj_invariant t x g

/-- Cyclic interchange inside a class function. -/
theorem su2HeatKernel_mul_comm (t : Real) (a b : SU2) :
    su2HeatKernel t (a * b) = su2HeatKernel t (b * a) := by
  have h := su2HeatKernel_conj_invariant t a (b * a)
  simpa [mul_assoc] using h

/-- The two-face Migdal move with the shared edge occurring in the opposite
orientation.  It is derived from the already proved concrete Migdal theorem
using only conjugation invariance and commutativity of scalar multiplication. -/
theorem su2Migdal_twoFace_merge_reversed
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (a b : SU2) :
    (∫ x : SU2,
      su2HeatKernel s (a * x⁻¹) * su2HeatKernel t (x * b)
        ∂su2HaarProb) =
      su2HeatKernel (s + t) (a * b) := by
  calc
    (∫ x : SU2,
        su2HeatKernel s (a * x⁻¹) * su2HeatKernel t (x * b)
          ∂su2HaarProb) =
        ∫ x : SU2,
          su2HeatKernel t (b * x) * su2HeatKernel s (x⁻¹ * a)
            ∂su2HaarProb := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change su2HeatKernel s (a * x⁻¹) * su2HeatKernel t (x * b) =
          su2HeatKernel t (b * x) * su2HeatKernel s (x⁻¹ * a)
        rw [su2HeatKernel_mul_comm t x b,
          su2HeatKernel_mul_comm s a x⁻¹]
        exact mul_comm _ _
    _ = su2HeatKernel (t + s) (b * a) :=
      su2Migdal_twoFace_merge ht hs b a
    _ = su2HeatKernel (s + t) (a * b) := by
      rw [add_comm]
      exact (su2HeatKernel_mul_comm (s + t) a b).symm

/-- Original, unreduced density on the three spoke-edge variables. -/
def su2ThreeSpokeUnreducedDensity
    (t₁ t₂ t₃ : Real) (a b c : SU2)
    (p : SU2 × (SU2 × SU2)) : Complex :=
  su2HeatKernel t₁ (p.1 * a * p.2.1⁻¹) *
    su2HeatKernel t₂ (p.2.1 * b * p.2.2⁻¹) *
      su2HeatKernel t₃ (p.2.2 * c * p.1⁻¹)

/-- Density on the two physical variables after fixing the common
interior-vertex gauge. -/
def su2ThreeSpokeGaugeFixedDensity
    (t₁ t₂ t₃ : Real) (a b c : SU2)
    (p : SU2 × SU2) : Complex :=
  su2HeatKernel t₁ (a * p.1⁻¹) *
    su2HeatKernel t₂ (p.1 * b * p.2⁻¹) *
      su2HeatKernel t₃ (p.2 * c)

/-- After applying the inverse change of variables, the original density is
independent of the pure-gauge coordinate. -/
theorem su2ThreeSpoke_density_gaugeFactorization
    (t₁ t₂ t₃ : Real) (a b c : SU2)
    (p : SU2 × (SU2 × SU2)) :
    su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c
        (su2ThreeSpokeGaugeFixEquiv.symm p) =
      su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c p.2 := by
  rcases p with ⟨u, y, z⟩
  simp only [su2ThreeSpokeGaugeFixEquiv,
    su2ThreeSpokeUnreducedDensity, su2ThreeSpokeGaugeFixedDensity]
  have h₁ := su2HeatKernel_conj_invariant t₁ u (a * y⁻¹)
  have h₂ := su2HeatKernel_conj_invariant t₂ u (y * b * z⁻¹)
  have h₃ := su2HeatKernel_conj_invariant t₃ u (z * c)
  rw [← h₁, ← h₂, ← h₃]
  simp [mul_assoc]

/-- The gauge-fixed density is continuous at positive face times. -/
theorem continuous_su2ThreeSpokeGaugeFixedDensity
    {t₁ t₂ t₃ : Real} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (a b c : SU2) :
    Continuous (su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c) := by
  unfold su2ThreeSpokeGaugeFixedDensity su2HeatKernel
  exact (((continuous_su2HeatKernelCharacterSeries ht₁).comp (by fun_prop)).mul
    ((continuous_su2HeatKernelCharacterSeries ht₂).comp (by fun_prop))).mul
      ((continuous_su2HeatKernelCharacterSeries ht₃).comp (by fun_prop))

/-- A continuous complex-valued function on a compact second-countable Borel
space is integrable against every finite measure. -/
theorem integrable_of_continuous_compact
    {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [CompactSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X -> Complex}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hf.norm.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun x => ?_)
  exact hM (Set.mem_image_of_mem _ (Set.mem_univ x))

theorem integrable_su2ThreeSpokeGaugeFixedDensity
    {t₁ t₂ t₃ : Real} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (a b c : SU2) :
    Integrable (su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c)
      su2TwoEdgeHaar := by
  exact integrable_of_continuous_compact
    (continuous_su2ThreeSpokeGaugeFixedDensity ht₁ ht₂ ht₃ a b c)

/-- Two physical Haar integrations collapse the three gauge-fixed faces to a
single heat kernel at the summed area. -/
theorem su2ThreeSpoke_gaugeFixedIntegral_eq_heatKernel
    {t₁ t₂ t₃ : Real} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (a b c : SU2) :
    (∫ p : SU2 × SU2,
      su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c p
        ∂su2TwoEdgeHaar) =
      su2HeatKernel (t₁ + t₂ + t₃) (a * b * c) := by
  rw [su2TwoEdgeHaar, integral_prod _
    (integrable_su2ThreeSpokeGaugeFixedDensity ht₁ ht₂ ht₃ a b c)]
  change (∫ x : SU2, ∫ y : SU2,
      su2HeatKernel t₁ (a * x⁻¹) *
        su2HeatKernel t₂ (x * b * y⁻¹) *
          su2HeatKernel t₃ (y * c) ∂su2HaarProb ∂su2HaarProb) = _
  calc
    (∫ x : SU2, ∫ y : SU2,
        su2HeatKernel t₁ (a * x⁻¹) *
          su2HeatKernel t₂ (x * b * y⁻¹) *
            su2HeatKernel t₃ (y * c) ∂su2HaarProb ∂su2HaarProb) =
      ∫ x : SU2,
        su2HeatKernel t₁ (a * x⁻¹) *
          su2HeatKernel (t₂ + t₃) (x * b * c) ∂su2HaarProb := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        simp only [mul_assoc]
        calc
          (∫ y : SU2,
              su2HeatKernel t₁ (a * x⁻¹) *
                (su2HeatKernel t₂ (x * (b * y⁻¹)) *
                  su2HeatKernel t₃ (y * c)) ∂su2HaarProb) =
              su2HeatKernel t₁ (a * x⁻¹) *
                ∫ y : SU2,
                  su2HeatKernel t₂ (x * (b * y⁻¹)) *
                    su2HeatKernel t₃ (y * c) ∂su2HaarProb :=
            integral_const_mul _ _
          _ = su2HeatKernel t₁ (a * x⁻¹) *
                su2HeatKernel (t₂ + t₃) (x * (b * c)) := by
            congr 1
            simpa [mul_assoc] using
              (su2Migdal_twoFace_merge_reversed ht₂ ht₃ (x * b) c)
    _ = su2HeatKernel (t₁ + t₂ + t₃) (a * b * c) := by
      simpa [add_assoc, mul_assoc] using
        (su2Migdal_twoFace_merge_reversed ht₁ (add_pos ht₂ ht₃) a (b * c))

/-- **Product-Haar gauge-fixing equivalence.** The integral over all three
original spoke-edge variables equals the two-coordinate reduced integral.
The proof uses the measure-preserving equivalence and exact factorization of
the density; neither equality is assumed in a package. -/
theorem su2ThreeSpoke_unreducedIntegral_eq_gaugeFixedIntegral
    (t₁ t₂ t₃ : Real) (a b c : SU2) :
    (∫ p : SU2 × (SU2 × SU2),
      su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c p
        ∂su2ThreeEdgeHaar) =
      ∫ q : SU2 × SU2,
        su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c q
          ∂su2TwoEdgeHaar := by
  have hinv : MeasurePreserving su2ThreeSpokeGaugeFixEquiv.symm
      su2ThreeEdgeHaar su2ThreeEdgeHaar :=
    MeasurePreserving.symm su2ThreeSpokeGaugeFixEquiv
      su2ThreeSpokeGaugeFix_measurePreserving
  calc
    (∫ p : SU2 × (SU2 × SU2),
        su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c p
          ∂su2ThreeEdgeHaar) =
      ∫ p : SU2 × (SU2 × SU2),
        su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c
          (su2ThreeSpokeGaugeFixEquiv.symm p) ∂su2ThreeEdgeHaar := by
        exact (hinv.integral_comp'
          (su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c)).symm
    _ = ∫ p : SU2 × (SU2 × SU2),
        su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c p.2
          ∂su2ThreeEdgeHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun p =>
        su2ThreeSpoke_density_gaugeFactorization t₁ t₂ t₃ a b c p
    _ = ∫ q : SU2 × SU2,
        su2ThreeSpokeGaugeFixedDensity t₁ t₂ t₃ a b c q
          ∂su2TwoEdgeHaar := by
      rw [su2ThreeEdgeHaar, su2TwoEdgeHaar, integral_fun_snd]
      simp

/-- The original three-edge product-Haar integral for the cyclic three-face
disk has the exact one-face value. -/
theorem su2ThreeSpoke_unreducedIntegral_eq_heatKernel
    {t₁ t₂ t₃ : Real} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht₃ : 0 < t₃)
    (a b c : SU2) :
    (∫ p : SU2 × (SU2 × SU2),
      su2ThreeSpokeUnreducedDensity t₁ t₂ t₃ a b c p
        ∂su2ThreeEdgeHaar) =
      su2HeatKernel (t₁ + t₂ + t₃) (a * b * c) := by
  rw [su2ThreeSpoke_unreducedIntegral_eq_gaugeFixedIntegral]
  exact su2ThreeSpoke_gaugeFixedIntegral_eq_heatKernel ht₁ ht₂ ht₃ a b c

end Lean2dYangMills
