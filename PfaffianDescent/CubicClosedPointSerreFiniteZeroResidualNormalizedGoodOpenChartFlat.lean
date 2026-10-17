import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedParameterChartFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpenChartZero

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpenChart_flat
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover (hypersurfaceToBase p hp) C).I₀)
    {E : Scheme.{u}} [IsAffine E] [IsDomain Γ(E, ⊤)] [IsPrincipalIdealRing Γ(E, ⊤)]
    (m : E ⟶ (lineProjOpenCover K).X ij.2) [IsOpenImmersion m]
    (hr : Set.range (m ≫ (lineProjOpenCover K).f ij.2) ⊆
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          (hypersurfaceToBase p hp) C seed).ker.subschemeι ≫
            projectiveLineAmbientToLine K (hypersurfaceToBase p hp))) :
    Flat ((cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal
      (hypersurfaceToBase p hp) C seed ij m).subschemeι ≫
        pullback.snd ((C.U ij.1).ι ≫ hypersurfaceToBase p hp)
          ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K)) := by
  rcases ij with ⟨i, b⟩
  change C.ι at i
  let f := hypersurfaceToBase p hp
  let I := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    f C seed).ker
  let π := projectiveLineAmbientToLine K f
  let u := cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C (i, b) m
  let v := u ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b)
  let r := m ≫ (lineProjOpenCover K).f (i, b).2
  let q := pullback.snd ((C.U (i, b).1).ι ≫ f) (r ≫ projectiveLineProjToBase K)
  have hv : v ≫ π = q ≫ r := by
    have hcover := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C (i, b)
    calc
      v ≫ π = u ≫ ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) ≫ π) :=
        Category.assoc _ _ _
      _ = u ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, b) ≫
          (lineProjOpenCover K).f b) := congrArg (fun a => u ≫ a) hcover
      _ = q ≫ r := by
        dsimp only [u, cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal,
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart]
        simp [Category.assoc, pullback.map, q, r, SerreExtensionRankTwoAffineCover.openCover]
  have hI : I.comap v = cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal f C seed (i, b) m := by
    dsimp only [I, v, cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal]
    rw [Scheme.IdealSheafData.comap_comp,
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap]
  have hq := cubicClosedPointSerreFiniteZeroResidual_comap_zero_locallyQuasiFinite_of_range_goodOpen
    I π v r q hv hr
  rw [hI] at hq
  letI := hq
  exact cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChart_flat p hp hp0 C seed (i, b) m

end PfaffianDescent
