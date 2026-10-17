import PfaffianDescent.CubicClosedPointSerreExtension
import AllCharacteristics.ClosedPointAlgebra
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Serre extension for an original closed point of residue degree eleven

All categorical Ext-existence instances, the actual residue-field algebra,
finite dimension, separability and the point's closed immersion are constructed
from the scheme and its original closed point.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u

/-- The proved enough-injectives theorem supplies native scheme Ext groups. -/
theorem schemeModules_hasExt (X : Scheme.{u}) : HasExt.{u} X.Modules := by
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  exact hasExt_of_enoughInjectives _

/-- Local module Ext groups in the universe used by actual stalk comparison. -/
theorem moduleCatStalk_hasExt (R : Type u) [CommRing R] :
    HasExt.{u+1} (ModuleCat.{u} R) :=
  hasExt_of_enoughInjectives _

end PfaffianDescent

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The original degree-eleven closed point gives an actual Serre sequence.
No algebraic-coordinate, trace, or Ext-existence hypothesis is supplied. -/
theorem cubicClosedDegreeElevenPointSerreExtension_exists_sequence
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 11) :
    let i := (hypersurface p hp).fromSpecResidueField x.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp x.2
    letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ e : SerreExtensionSequenceData (hypersurface p hp)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)),
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp)
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) e
          (schemeModules_hasExt (hypersurface p hp)))
        (show 1 + 1 = 2 by omega) ≠ 0 := by
  let i := (hypersurface p hp).fromSpecResidueField x.1
  letI hClosed : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp x.2
  letI hExt : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  letI hExtStalk : HasExt.{u+1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default))) :=
    moduleCatStalk_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  letI hAlg : Algebra K ((hypersurface p hp).residueField x.1) :=
    pointAlgebra (hypersurfaceToBase p hp) x.1
  letI hFin : Module.Finite K ((hypersurface p hp).residueField x.1) :=
    closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  have hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom
        (algebraMap K ((hypersurface p hp).residueField x.1))) :=
    (pointAlgebra_spec (hypersurfaceToBase p hp) x.1).symm
  have hL : Module.finrank K ((hypersurface p hp).residueField x.1) = 11 :=
    (closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) x).trans hx
  exact @cubicClosedPointSerreExtension_exists_sequence_of_smooth K _ p hp hp0 _
    ((hypersurface p hp).residueField x.1) _ hAlg hFin inferInstance i hClosed hi
    hExtAmbient hExt hExtStalk hL

end PfaffianDescent.ProjectiveNegativeTwist
