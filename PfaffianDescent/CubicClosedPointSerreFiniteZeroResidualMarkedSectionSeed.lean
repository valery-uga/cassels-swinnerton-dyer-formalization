import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleStalkOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedStalkRetraction
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedSectionOpen

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen_mem_of_field_fiber
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y) (y : Y)
    [IsNoetherianRing (Z.presheaf.stalk (j y))]
    (hf : IsField (Z.presheaf.stalk (j y) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map
        (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y))) :
    y ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
  apply cubicClosedPointSerreFiniteZeroResidual_mem_etaleOpen_of_formallyEtale_stalk g (j y)
  letI := (g.stalkMap (j y)).hom.toAlgebra
  letI : Algebra.Etale (Y.presheaf.stalk (g (j y))) (Z.presheaf.stalk (j y)) :=
    cubicClosedPointSerreFiniteZeroResidual_markedStalk_etale_of_field_fiber g j hj y hf
  change Algebra.FormallyEtale (Y.presheaf.stalk (g (j y))) (Z.presheaf.stalk (j y))
  infer_instance

end PfaffianDescent
