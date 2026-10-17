import PfaffianDescent.VoisinMixedTwistLocal
import PfaffianDescent.VoisinPositiveDifferenceLocal

/-!
# Ambient term identifications for the positively twisted cubic sequence

These are the two ambient tensor identifications obtained by tensoring
`O(-6) → O(-3)` with `O(5)`.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace ProjectiveNegativeTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- The left ambient term after tensoring the cubic restriction sequence by
`O(5)` is `O(-1)`. -/
noncomputable def quotientNegativePositiveDifferenceIso_five_six
    (I : HomogeneousIdeal 𝒜) :
    schemeModuleTensor (sheafOfModules (grading I) 6)
      (positiveSheafOfModules (grading I) 5) ≅
      sheafOfModules (grading I) 1 := by
  let 𝓑 := grading I
  let h56 : 5 ≤ 6 := by omega
  letI : IsIso (positiveNegativeDifferencePairing 𝓑 5 6 h56) :=
    quotientPositiveNegativeDifferencePairing_five_six_isIso I
  exact schemeModuleTensorSymmetry (sheafOfModules 𝓑 6)
    (positiveSheafOfModules 𝓑 5) ≪≫
      asIso (positiveNegativeDifferencePairing 𝓑 5 6 h56)

/-- The middle ambient term after tensoring the cubic restriction sequence by
`O(5)` is `O(2)`. -/
noncomputable def quotientNegativePositiveDifferenceIso_five_three
    (I : HomogeneousIdeal 𝒜) :
    schemeModuleTensor (sheafOfModules (grading I) 3)
      (positiveSheafOfModules (grading I) 5) ≅
      positiveSheafOfModules (grading I) 2 := by
  let 𝓑 := grading I
  let h53 : 3 ≤ 5 := by omega
  letI : IsIso (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53) :=
    quotientPositiveNegativePositiveDifferencePairing_five_three_isIso I
  exact schemeModuleTensorSymmetry (sheafOfModules 𝓑 3)
    (positiveSheafOfModules 𝓑 5) ≪≫
      asIso (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53)

/-- On the cubic hypersurface itself, `O_S(5) ⊗ O_S(-3)` is `O_S(2)`.
This is the intrinsic surface-side factor of the remaining pushforward
comparison. -/
noncomputable def hypersurfacePositiveNegativePositiveDifferenceIso_five_three
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d) :
    schemeModuleTensor
      (positiveSheafOfModules (grading (equationIdeal p hp)) 5)
      (sheafOfModules (grading (equationIdeal p hp)) 3) ≅
      positiveSheafOfModules (grading (equationIdeal p hp)) 2 := by
  let I := equationIdeal p hp
  let 𝓑 := grading I
  let h53 : 3 ≤ 5 := by omega
  letI : IsIso (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53) :=
    quotientPositiveNegativePositiveDifferencePairing_five_three_isIso I
  exact asIso (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53)

set_option linter.style.haveILetI false in
/-- The actual negative cubic hypersurface restriction sequence stays short
exact after tensoring on the right by `O(5)` on projective three-space.  Its
first two terms are identified above with `O(-1)` and `O(2)`. -/
theorem p3HypersurfaceNegativeThreeTensorPositiveFive_shortExact
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    ((hypersurfaceTwistRestrictionSequence p hp 3).map
      (schemeModuleTensorRight
        (positiveSheafOfModules
          (MvPolynomial.homogeneousSubmodule (Fin 4) K) 5))).ShortExact := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  letI : PreservesFiniteLimits
      (schemeModuleTensorRight (positiveSheafOfModules PS 5)) :=
    p3PositiveTwist_tensorRight_preservesFiniteLimits K 5 (by omega)
  letI : PreservesFiniteColimits
      (schemeModuleTensorRight (positiveSheafOfModules PS 5)) :=
    p3PositiveTwist_tensorRight_preservesFiniteColimits K 5 (by omega)
  exact (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3).map_of_exact
    (schemeModuleTensorRight (positiveSheafOfModules PS 5))

end ProjectiveNegativeTwist
end PfaffianDescent
