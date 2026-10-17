import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-!
# Removing the cubic Serre twist

The positive/negative projective-twist equivalence sends the three terms of
the positively twisted closed-immersion ideal sequence back to their
untwisted models.  The quotient-map square is the naturality square of the
equivalence counit.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial IdealSheafDataModule
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {sigma : Type} [Field K]
local notation "PS" => MvPolynomial.homogeneousSubmodule sigma K

/- The degree-`m` inverse-twist equivalence used in the Serre construction. -/
noncomputable abbrev quotientInverseTwistEquivalence
    (I : HomogeneousIdeal PS) (m : ℕ) :
    (scheme I).Modules ≌ (scheme I).Modules :=
  quotientTwistTensorRightEquivalence_all I m

/- After removing the positive twist, the middle object of the twisted ideal
sequence is the tensor unit. -/
noncomputable def quotientInverseTwistMiddleIso
    (I : HomogeneousIdeal PS) {Z : Scheme.{u}}
    (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ) :
    (quotientInverseTwistEquivalence I m).functor.obj
        (closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) m)).X₂ ≅
      SheafOfModules.unit (scheme I).ringCatSheaf :=
  (quotientInverseTwistEquivalence I m).counitIso.app
    (SheafOfModules.unit (scheme I).ringCatSheaf)

/- After removing the positive twist, the quotient object is the ordinary
pushforward of the finite subscheme's structure sheaf. -/
noncomputable def quotientInverseTwistTargetIso
    (I : HomogeneousIdeal PS) {Z : Scheme.{u}}
    (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ) :
    (quotientInverseTwistEquivalence I m).functor.obj
        (closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) m)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  (quotientInverseTwistEquivalence I m).counitIso.app
    ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf))

/- The tensor unit is sent to the intrinsic negative twist. -/
noncomputable def quotientInverseTwistUnitIso
    (I : HomogeneousIdeal PS) (m : ℕ) :
    (quotientInverseTwistEquivalence I m).functor.obj
        (SheafOfModules.unit (scheme I).ringCatSheaf) ≅
      sheafOfModules (grading I) m :=
  schemeModuleTensorUnitLeftIso (sheafOfModules (grading I) m)

/- Removing the positive twist carries the twisted quotient map to the
ordinary quotient map.  This is precisely naturality of the equivalence
counit. -/
theorem quotientInverseTwist_idealSequence_g_square
    (I : HomogeneousIdeal PS) {Z : Scheme.{u}}
    (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ) :
    (quotientInverseTwistEquivalence I m).functor.map
          (closedImmersionIdealTwistSequence i
            (positiveSheafOfModules (grading I) m)).g ≫
        (quotientInverseTwistTargetIso I i m).hom =
      (quotientInverseTwistMiddleIso I i m).hom ≫
        (closedImmersionModulePushforwardSequence i).g := by
  exact (quotientInverseTwistEquivalence I m).counitIso.hom.naturality
    (closedImmersionModulePushforwardSequence i).g

end PfaffianDescent.ProjectiveNegativeTwist
