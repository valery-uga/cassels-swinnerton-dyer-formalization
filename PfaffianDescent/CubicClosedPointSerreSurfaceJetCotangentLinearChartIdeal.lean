import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineClosedFiber
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealTwist
import PfaffianDescent.RelativeClosedImmersionIdealBaseChange

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal Spec(Away ell) common-chart morphism into the actual projective surface. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    Spec (CommRingCat.of (Away (grading I) (ell : CoordinateRing I))) ⟶ scheme I :=
  (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 (by decide : 0 < 1)).inv ≫
    (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι

instance cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism_isOpenImmersion
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    IsOpenImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) := by
  unfold cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism
  infer_instance

/-- Restriction retains the ACTUAL eleven-point ideal as the actual ideal of its
literal fibre-product immersion into the common affine chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartIdealBaseChangeIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    (Scheme.Modules.pullback
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
    IdealSheafDataModule.closedImmersionModule
      (pullback.fst (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) i) := by
  let f := cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell
  letI : IsIso (closedImmersionIdealBaseChangeHom f i) :=
    isIso_flatClosedImmersionIdealBaseChangeHom_general f i
  exact asIso (closedImmersionIdealBaseChangeHom f i)

/-- The actual restriction square preserves the original ideal inclusion. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChartIdealBaseChangeIso_toUnit
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartIdealBaseChangeIso I ell i).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) i) =
    (Scheme.Modules.pullback
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) :=
  closedImmersionIdealBaseChangeHom_toUnit _ i

/-- The literal affine H of the SAME original closed subscheme on the common chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    Ideal (Away (grading I) (ell : CoordinateRing I)) :=
  RingHom.ker (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap
    (pullback.fst (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) i))

/-- Actual common-chart restriction of the actual original ideal is tilde of its actual H. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartIdealTildeIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    (Scheme.Modules.pullback
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
    (tilde.functor (CommRingCat.of (Away (grading I) (ell : CoordinateRing I)))).obj
      (ModuleCat.of (Away (grading I) (ell : CoordinateRing I))
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartIdeal I ell i)) :=
  cubicClosedPointSerreSurfaceJetCotangent_linearChartIdealBaseChangeIso I ell i ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionTildeIso
      (pullback.fst (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) i)

end PfaffianDescent
