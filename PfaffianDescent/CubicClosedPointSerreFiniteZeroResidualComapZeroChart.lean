import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap
    {A T : Scheme.{u}} (I : A.IdealSheafData) (v : T ⟶ A) :
    (I.comap v).subscheme ⟶ I.subscheme :=
  (I.comapIso v).hom ≫ pullback.snd v I.subschemeι

instance cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap_isOpenImmersion
    {A T : Scheme.{u}} (I : A.IdealSheafData) (v : T ⟶ A) [IsOpenImmersion v] :
    IsOpenImmersion (cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap I v) := by
  dsimp [cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap]
  infer_instance

theorem cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap_comp
    {A T : Scheme.{u}} (I : A.IdealSheafData) (v : T ⟶ A) :
    cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap I v ≫ I.subschemeι =
      (I.comap v).subschemeι ≫ v := by
  simp only [cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap, Category.assoc,
    ← pullback.condition, I.comapIso_hom_fst_assoc]

theorem cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap_range
    {A T : Scheme.{u}} (I : A.IdealSheafData) (v : T ⟶ A) :
    Set.range (cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap I v) =
      I.subschemeι ⁻¹' Set.range v := by
  rw [cubicClosedPointSerreFiniteZeroResidual_comapZeroChartMap, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (I.comapIso v).hom.surjective, Set.image_univ,
    Scheme.Pullback.range_snd]

end PfaffianDescent
