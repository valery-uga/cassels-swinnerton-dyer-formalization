import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedParameterChartFlat

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal_range
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    {E : Scheme.{u}} (m : E ⟶ (lineProjOpenCover K).X ij.2) :
    Set.range (cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C ij m) =
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) ⁻¹' Set.range m := by
  rcases ij with ⟨i, b⟩
  change C.ι at i
  change Set.range (pullback.map ((C.U i).ι ≫ f)
    ((m ≫ (lineProjOpenCover K).f b) ≫ projectiveLineProjToBase K)
    ((C.U i).ι ≫ f) ((lineProjOpenCover K).f b ≫ projectiveLineProjToBase K)
    (𝟙 _) m (𝟙 _) (by simp) (by simp [Category.assoc])) =
      (pullback.snd ((C.U i).ι ≫ f)
        ((lineProjOpenCover K).f b ≫ projectiveLineProjToBase K)) ⁻¹' Set.range m
  rw [Scheme.Pullback.range_map]
  simp

end PfaffianDescent
