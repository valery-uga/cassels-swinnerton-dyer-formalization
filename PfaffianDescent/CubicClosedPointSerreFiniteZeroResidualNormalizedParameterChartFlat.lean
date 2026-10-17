import PfaffianDescent.SerreExtensionPencilProjectiveLine
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeProductLineFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeProductNoetherian
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffinePairComap

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

 def cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    {E : Scheme.{u}} (m : E ⟶ (lineProjOpenCover K).X ij.2) :
    pullback ((C.U ij.1).ι ≫ f)
      ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K) ⟶
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij :=
  pullback.map _ _ _ _ (𝟙 _) m (𝟙 _) (by simp [SerreExtensionRankTwoAffineCover.openCover]) (by simp [Category.assoc])

instance cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal_isOpenImmersion
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    {E : Scheme.{u}} (m : E ⟶ (lineProjOpenCover K).X ij.2) [IsOpenImmersion m] :
    IsOpenImmersion (cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C ij m) := by
  dsimp [cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal]
  infer_instance

def cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    {E : Scheme.{u}} (m : E ⟶ (lineProjOpenCover K).X ij.2) :
    (pullback ((C.U ij.1).ι ≫ f)
      ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K)).IdealSheafData :=
  (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij).comap
    (cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C ij m)

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChart_flat
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover (hypersurfaceToBase p hp) C).I₀)
    {E : Scheme.{u}} [IsAffine E] [IsDomain Γ(E, ⊤)] [IsPrincipalIdealRing Γ(E, ⊤)]
    (m : E ⟶ (lineProjOpenCover K).X ij.2) [IsOpenImmersion m]
    [LocallyQuasiFinite ((cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal
      (hypersurfaceToBase p hp) C seed ij m).subschemeι ≫
        pullback.snd ((C.U ij.1).ι ≫ hypersurfaceToBase p hp)
          ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K))] :
    Flat ((cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal
      (hypersurfaceToBase p hp) C seed ij m).subschemeι ≫
        pullback.snd ((C.U ij.1).ι ≫ hypersurfaceToBase p hp)
          ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K)) := by
  letI : IsAffine (C.U ij.1 : Scheme.{u}) := C.affine ij.1
  let f := hypersurfaceToBase p hp
  let U : (hypersurface p hp).affineOpens := ⟨C.U ij.1, C.affine ij.1⟩
  let r := m ≫ (lineProjOpenCover K).f ij.2
  let T := pullback (U.1.ι ≫ f) (r ≫ projectiveLineProjToBase K)
  let u := cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartToOriginal f C ij m
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates f C seed ij).2
  letI : IsNoetherianRing Γ(T, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_affineProduct_sections_noetherian
      f U (r ≫ projectiveLineProjToBase K)
  letI : LocallyQuasiFinite ((I.comap u).subschemeι ≫
      pullback.snd (U.1.ι ≫ f) (r ≫ projectiveLineProjToBase K)) := by
    change LocallyQuasiFinite ((cubicClosedPointSerreFiniteZeroResidual_normalizedParameterChartIdeal
      (hypersurfaceToBase p hp) C seed ij m).subschemeι ≫
        pullback.snd ((C.U ij.1).ι ≫ hypersurfaceToBase p hp)
          ((m ≫ (lineProjOpenCover K).f ij.2) ≫ projectiveLineProjToBase K))
    infer_instance
  apply cubicClosedPointSerreFiniteZeroResidual_nativeProduct_pair_zero_flat_over_projectiveLine
    p hp hp0 U r (I.comap u) (u.appTop a) (u.appTop b)
  exact cubicClosedPointSerreFiniteZeroResidual_affinePair_comap_top u I a b
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates f C seed ij)

end PfaffianDescent
