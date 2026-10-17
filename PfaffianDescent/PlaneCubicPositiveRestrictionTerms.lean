import PfaffianDescent.VoisinHypersurfacePositiveTwist
import PfaffianDescent.VoisinHypersurfaceCrossingTwist
import Mathlib.Tactic

/-! SOURCE ONLY / UNCHECKED. The actual ambient P2 restriction sequence
for EVERY positive degree, including the mixed-sign degrees1/2. All
term comparisons are proved from the native sequence, not supplied. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal existing positive/crossing restriction maps, with no changed
coefficient object or transported scalar action. -/
def planeCubicPositiveRestrictionSequence
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) :
    ShortComplex (Proj PS).Modules :=
  if hd : 3 ≤ d then
    hypersurfacePositiveTwistRestrictionSequence F hF (d - 3)
  else hypersurfaceCrossingTwistRestrictionSequence F hF (3 - d) (Nat.sub_le 3 d)

theorem planeCubicPositiveRestrictionSequence_shortExact
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) :
    (planeCubicPositiveRestrictionSequence F hF d).ShortExact := by
  unfold planeCubicPositiveRestrictionSequence
  split_ifs with hd
  · exact hypersurfacePositiveTwistRestrictionSequence_shortExact F hF hF0 (d - 3)
  · exact hypersurfaceCrossingTwistRestrictionSequence_shortExact F hF hF0
      (3 - d) (Nat.sub_le 3 d)

/-- The middle coefficient is the actual positive twist O_P2(d). -/
theorem planeCubicPositiveRestrictionSequence_middle
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) :
    (planeCubicPositiveRestrictionSequence F hF d).X₂ = positiveSheafOfModules PS d := by
  unfold planeCubicPositiveRestrictionSequence
  split_ifs with hd
  · change positiveSheafOfModules PS (d - 3 + 3) = positiveSheafOfModules PS d
    rw [Nat.sub_add_cancel hd]
  · change positiveSheafOfModules PS (3 - (3 - d)) = positiveSheafOfModules PS d
    have hindex : 3 - (3 - d) = d := by omega
    rw [hindex]

/-- The quotient coefficient is the actual closed pushforward of O_E(d),
with the original immersion of the SAME cubic into the SAME P2. -/
theorem planeCubicPositiveRestrictionSequence_quotient
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) :
    (planeCubicPositiveRestrictionSequence F hF d).X₃ =
      (Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d) := by
  unfold planeCubicPositiveRestrictionSequence
  split_ifs with hd
  · change (Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) (d - 3 + 3)) = _
    rw [Nat.sub_add_cancel hd]
  · change (Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) (3 - (3 - d))) = _
    have hindex : 3 - (3 - d) = d := by omega
    rw [hindex]

theorem planeCubicPositiveRestrictionSequence_first_of_three_le
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : 3 ≤ d) :
    (planeCubicPositiveRestrictionSequence F hF d).X₁ =
      positiveSheafOfModules PS (d - 3) := by
  simp only [planeCubicPositiveRestrictionSequence, dif_pos hd]
  rfl

theorem planeCubicPositiveRestrictionSequence_first_of_lt_three
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : d < 3) :
    (planeCubicPositiveRestrictionSequence F hF d).X₁ = sheafOfModules PS (3 - d) := by
  simp only [planeCubicPositiveRestrictionSequence, dif_neg (Nat.not_le.mpr hd)]
  rfl

/-- Exactly the low negative degrees −1/−2 arise for positive d<3. -/
theorem planeCubicPositiveRestrictionSequence_low_negative_degree_bound
    (d : ℕ) (hd : 1 ≤ d) : 3 - d ≤ 2 := by omega

end PfaffianDescent.ProjectivePlaneNative
