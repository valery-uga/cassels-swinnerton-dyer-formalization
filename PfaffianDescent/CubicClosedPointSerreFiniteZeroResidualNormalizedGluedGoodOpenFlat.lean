import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedGoodOpenFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpenSourceIso

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_flat
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    letI := SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      (hypersurfaceToBase p hp) C seed
    let g := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      (hypersurfaceToBase p hp) C seed ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
    Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) := by
  let f := hypersurfaceToBase p hp
  let i := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f C seed
  let π := projectiveLineAmbientToLine K f
  letI := SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine f C seed
  letI : IsClosedImmersion i :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient f C seed
  let eI := asIso i.toImage
  let g := i.imageι ≫ π
  letI : Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedGoodOpen_flat p hp hp0 C seed
  have hfac : eI.hom ≫ g = i ≫ π := by
    dsimp only [eI, asIso_hom, g]
    rw [← Category.assoc, i.toImage_imageι]
  have hV : cubicClosedPointSerreFiniteZeroResidual_goodOpen (i ≫ π) =
      cubicClosedPointSerreFiniteZeroResidual_goodOpen g := by
    simpa only [hfac] using cubicClosedPointSerreFiniteZeroResidual_goodOpen_comp_iso g eI
  have hflat := cubicClosedPointSerreFiniteZeroResidual_flat_restrict_comp_iso
    g eI (cubicClosedPointSerreFiniteZeroResidual_goodOpen g)
  rw [hfac] at hflat
  change Flat ((i ≫ π) ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen (i ≫ π))
  rw [hV]
  exact hflat

end PfaffianDescent
