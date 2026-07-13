import Lean2dYangMills.SU2HeatSemigroup
import Lean2dYangMills.SU2ExactAreaLaw

/-!
# Kernel dependency audit for the exact SU(2) Migdal closure

This module is imported by the public root so that a clean CI build prints the
axiom dependencies of every principal endpoint in the closure chain.
-/

namespace Lean2dYangMills

#print axioms su2FirstRailMoment_recurrence
#print axioms su2FirstRailMoment_eq
#print axioms su2FirstRailMassMeasure_eq_uniform
#print axioms intervalIntegral_chebyshevU_product_formula
#print axioms integral_su2FirstEntryMass_eq_unitInterval
#print axioms integral_su2Haar_orbit_character_general
#print axioms integral_su2CharacterReal_mul_translate
#print axioms su2CharacterChebyshev_convolution
#print axioms su2HeatKernelPartial_convolution
#print axioms su2HeatKernel_convolution
#print axioms su2Migdal_twoFace_merge
#print axioms su2Migdal_subdivision_invariant
#print axioms su2_exact_simpleLoop_areaLaw

end Lean2dYangMills
