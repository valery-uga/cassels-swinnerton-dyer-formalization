import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.VoisinQuotientAmbientChart
import AllCharacteristics.GradedAwayMap
import Mathlib.RingTheory.Localization.Basic

/-! SOURCE ONLY / UNVERIFIED. Actual homogeneous projective chart kernels
preserve intersection and sum of ENTIRE ideals. The intersection is proved
by actual degree-zero homogeneous fractions and common denominator clearing,
not by applying map_inf to the surjective dehomogenization map. No radical,
exactness, reducedness, component, field extension or cohomology premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- In a genuine degree-one homogeneous localization, a zero fraction has
an annihilating power of its actual distinguished homogeneous denominator.
No non-zero-divisor or reduced-ring assumption is needed. -/
theorem homogeneousDegreeOneAway_mk_eq_zero_iff001
    {T V : Type*} [CommRing T] [SetLike V T] [AddSubgroupClass V T]
    (G : ℕ → V) [GradedRing G] (f : T) (hf : f ∈ G 1)
    (n : ℕ) (r : T) (hr : r ∈ G (n • 1)) :
    Away.mk G hf n r hr = 0 ↔ ∃ m : ℕ, f ^ m * r = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hzero⟩
    obtain ⟨m, rfl⟩ := ha
    exact ⟨m, hzero⟩
  · rintro ⟨m, hzero⟩
    exact ⟨⟨f ^ m, ⟨m, rfl⟩⟩, hzero⟩

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The literal actual projective quotient map kills the native homogeneous
fraction r/X_j^n exactly when some X_j-power times its original numerator
belongs to the ENTIRE original homogeneous ideal. Quotient zero divisors
are retained, and the actual chart map is never replaced. -/
theorem actualHomogeneousAmbientChartMap_mk_eq_zero_iff_power_mem001
    (I : HomogeneousIdeal PS) (j : Fin 4) (n : ℕ)
    (r : MvPolynomial (Fin 4) K) (hr : r ∈ PS (n • 1)) :
    quotientAmbientChartMap I j
      (Away.mk PS (show X j ∈ PS 1 from isHomogeneous_X K j) n r hr) = 0 ↔
      ∃ m : ℕ, X j ^ m * r ∈ I.toIdeal := by
  let hx : X j ∈ PS 1 := isHomogeneous_X K j
  let hy : coordinate I j ∈ grading I 1 := coordinate_mem I j
  change AllCharacteristics.gradedAwayMapOfEq (quotientGradedRingHom I)
      (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)
      (Away.mk PS hx n r hr) = 0 ↔ _
  rw [AllCharacteristics.gradedAwayMapOfEq_mk (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j) hx hy n r hr]
  rw [homogeneousDegreeOneAway_mk_eq_zero_iff001]
  change (∃ m : ℕ, (Ideal.Quotient.mk I.toIdeal (X j)) ^ m *
    Ideal.Quotient.mk I.toIdeal r = 0) ↔ _
  simp only [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-- Genuine kernel intersection for the SAME actual native ambient chart
maps. A shared power mA+mB clears both denominators, so the original
numerator lies in BOTH whole ideals. No arbitrary ideal map_inf is used. -/
theorem actualHomogeneousAmbientChartKernel_inf001
    (A B : HomogeneousIdeal PS) (j : Fin 4) :
    RingHom.ker (quotientAmbientChartMap (A ⊓ B) j) =
      RingHom.ker (quotientAmbientChartMap A j) ⊓
        RingHom.ker (quotientAmbientChartMap B j) := by
  ext x
  obtain ⟨n, r, hr, rfl⟩ := Away.mk_surjective PS
    (show X j ∈ PS 1 from isHomogeneous_X K j) x
  change quotientAmbientChartMap (A ⊓ B) j (Away.mk PS
      (show X j ∈ PS 1 from isHomogeneous_X K j) n r hr) = 0 ↔
    quotientAmbientChartMap A j (Away.mk PS
      (show X j ∈ PS 1 from isHomogeneous_X K j) n r hr) = 0 ∧
    quotientAmbientChartMap B j (Away.mk PS
      (show X j ∈ PS 1 from isHomogeneous_X K j) n r hr) = 0
  rw [actualHomogeneousAmbientChartMap_mk_eq_zero_iff_power_mem001,
    actualHomogeneousAmbientChartMap_mk_eq_zero_iff_power_mem001,
    actualHomogeneousAmbientChartMap_mk_eq_zero_iff_power_mem001]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨m, hm.1⟩, ⟨m, hm.2⟩⟩
  · rintro ⟨⟨mA, hA⟩, ⟨mB, hB⟩⟩
    refine ⟨mA + mB, ?_⟩
    change X j ^ (mA + mB) * r ∈ A.toIdeal ∧
      X j ^ (mA + mB) * r ∈ B.toIdeal
    constructor
    · rw [pow_add, mul_comm (X j ^ mA) (X j ^ mB), mul_assoc]
      exact A.toIdeal.mul_mem_left (X j ^ mB) hA
    · rw [pow_add, mul_assoc]
      exact B.toIdeal.mul_mem_left (X j ^ mA) hB

/-- Genuine kernel sum for actual ambient chart maps. Whole-ideal chart
image is already constructed by the existing actual chart producer; sum
preservation of ideal image is valid for every ring map. -/
theorem actualHomogeneousAmbientChartKernel_sup001
    (A B : HomogeneousIdeal PS) (j : Fin 4) :
    RingHom.ker (quotientAmbientChartMap (A ⊔ B) j) =
      RingHom.ker (quotientAmbientChartMap A j) ⊔
        RingHom.ker (quotientAmbientChartMap B j) := by
  rw [quotientAmbientChartMap_ker_eq_ideal_image (A ⊔ B) j,
    quotientAmbientChartMap_ker_eq_ideal_image A j,
    quotientAmbientChartMap_ker_eq_ideal_image B j]
  change (A.toIdeal ⊔ B.toIdeal).map (ambientChartEvaluation j) =
    A.toIdeal.map (ambientChartEvaluation j) ⊔ B.toIdeal.map (ambientChartEvaluation j)
  rw [Ideal.map_sup]

/-- The dehomogenization image intersection is valid for these actual
HOMOGENEOUS ideals, because the preceding genuine homogeneous fraction
proof derives it. This lemma does not assert map_inf for arbitrary ideals. -/
theorem homogeneousAmbientChartEvaluation_map_inf001
    (A B : HomogeneousIdeal PS) (j : Fin 4) :
    (A ⊓ B).toIdeal.map (ambientChartEvaluation j) =
      A.toIdeal.map (ambientChartEvaluation j) ⊓
        B.toIdeal.map (ambientChartEvaluation j) := by
  rw [← quotientAmbientChartMap_ker_eq_ideal_image (A ⊓ B) j,
    ← quotientAmbientChartMap_ker_eq_ideal_image A j,
    ← quotientAmbientChartMap_ker_eq_ideal_image B j]
  exact actualHomogeneousAmbientChartKernel_inf001 A B j

end PfaffianDescent
