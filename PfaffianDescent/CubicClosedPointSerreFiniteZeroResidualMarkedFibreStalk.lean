import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleOpenFibreStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedSectionOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_markedFibreSection
    {Z Y T : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (s : T ⟶ Y) : T ⟶ pullback g s :=
  pullback.lift (s ≫ j) (𝟙 _) (by simp only [Category.assoc, hj, Category.comp_id, Category.id_comp])

theorem cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_stalk_isField
    {E : Type u} [Field E] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (s : Spec (.of E) ⟶ Y) (c : Spec (.of E))
    (hc : s c ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j) :
    IsField ((pullback g s).presheaf.stalk
      (cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j hj s c)) := by
  apply cubicClosedPointSerreFiniteZeroResidual_etaleOpen_fibre_stalk_isField g s
  change ((cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j hj s) ≫
    pullback.fst g s) c ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  simp only [cubicClosedPointSerreFiniteZeroResidual_markedFibreSection, pullback.lift_fst]
  exact hc

end PfaffianDescent
