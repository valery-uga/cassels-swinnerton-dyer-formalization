import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedGoodOpenPointChart
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualRestrictStalkFlat

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpen_flat
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    let I := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      (hypersurfaceToBase p hp) C seed).ker
    let g := I.subschemeι ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
    Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) := by
  let I := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    (hypersurfaceToBase p hp) C seed).ker
  let g := I.subschemeι ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen g
  change Flat (g ∣_ V)
  apply Flat.of_stalkMap
  intro z
  obtain ⟨T, j, hj, hflat, ⟨w, hw⟩⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpen_flat_chart_at_point p hp hp0 C seed z.1 z.2
  letI := hj
  letI := hflat
  have hg : (g.stalkMap z.1).hom.Flat :=
    (congrArg (fun a : I.subscheme => (g.stalkMap a).hom.Flat) hw).mp
      (cubicClosedPointSerreFiniteZeroResidual_stalk_flat_of_open_chart g j w)
  exact cubicClosedPointSerreFiniteZeroResidual_restrict_stalk_flat g V z hg

end PfaffianDescent
