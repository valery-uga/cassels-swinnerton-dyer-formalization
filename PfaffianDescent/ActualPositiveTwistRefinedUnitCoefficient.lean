import PfaffianDescent.ActualPositiveTwistChartSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSectionChartCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRefinedSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartFunction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

/- SOURCE ONLY / UNVERIFIED. The SAME actual chart basis determines the
module-unit and section coefficients, including literal Spec(Away) refinement. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualPositiveTwistChartUnitCoefficient_eq
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ)
    (y : Γ(positiveSheafOfModules (grading I) m,
      Proj.basicOpen (grading I) (ell : CoordinateRing I))) :
    schemeModuleLocalUnitSectionAddEquiv
      (Proj.basicOpen (grading I) (ell : CoordinateRing I))
      (positiveSheafOfModules (grading I) m)
      (actualPositiveTwistChartUnitIso I ell m) y =
      actualPositiveTwistChartSectionCoefficient I ell m y := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let T := positiveSheafOfModules (grading I) m
  letI := actualPositiveTwistChartBasisInvHom_isIso I ell m
  let e := asIso ((Scheme.Modules.restrictFunctor U.ι).map
    (actualPositiveTwistChartBasisInvHom I ell m))
  have he : actualPositiveTwistChartUnitIso I ell m ≪≫
      (Scheme.Modules.restrictUnitIso U.ι).symm = e.symm := by
    let v := Scheme.Modules.restrictUnitIso U.ι
    change (e.symm ≪≫ v) ≪≫ v.symm = e.symm
    exact (Iso.trans_assoc e.symm v v.symm).trans
      ((congrArg (fun z => e.symm ≪≫ z) (Iso.self_symm_id v)).trans
        (Iso.trans_refl e.symm))
  unfold schemeModuleLocalUnitSectionAddEquiv
  rw [he]
  change schemeModuleLocalSectionAddEquiv U T (SheafOfModules.unit (scheme I).ringCatSheaf)
      e.symm y =
    (schemeModuleLocalSectionAddEquiv U (SheafOfModules.unit (scheme I).ringCatSheaf) T e).symm y
  rfl

lemma actualPositiveTwistChartUnitHomogeneousCoefficient
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (a : grading I m) :
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso
          (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).inv ≫
        (Scheme.Modules.restrictFunctor
          (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
          ((positiveSheafOfModules (grading I) m).unitHomEquiv.symm
            (positiveGlobalSectionOfHomogeneous (grading I) m a)) ≫
        (actualPositiveTwistChartUnitIso I ell m).hom) =
    (Proj.basicOpen (grading I) (ell : CoordinateRing I)).topIso.inv
      ((Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.2 m (a : CoordinateRing I) (by simpa using a.property))) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let T := positiveSheafOfModules (grading I) m
  let s := positiveGlobalSectionOfHomogeneous (grading I) m a
  let y : Γ(T, U) := s.val (op U)
  have hSection := cubicClosedPointSerreSurfaceJetCotangent_sectionChartCoefficient
    U T (actualPositiveTwistChartUnitIso I ell m) s
  have hCoefficient :
      schemeModuleLocalUnitSectionAddEquiv U T
          (actualPositiveTwistChartUnitIso I ell m) y =
        actualPositiveTwistChartSectionCoefficient I ell m y :=
    actualPositiveTwistChartUnitCoefficient_eq I ell m y
  have hFraction : actualPositiveTwistChartSectionCoefficient I ell m y =
      (Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.2 m (a : CoordinateRing I)
          (by simpa using a.property)) :=
    actualPositiveTwistChartSectionCoefficient_homogeneousFamily I ell m a
  exact hSection.trans
    (congrArg (fun z : Γ(SheafOfModules.unit (scheme I).ringCatSheaf, U) =>
      U.topIso.inv z) (hCoefficient.trans hFraction))

lemma actualPositiveTwistRefinedHomogeneousCoefficient
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (a : grading I m) :
    let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
    let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.property Nat.zero_lt_one
    let T := positiveSheafOfModules (grading I) m
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (e.inv ≫ U.ι)).inv ≫
        (Scheme.Modules.restrictFunctor (e.inv ≫ U.ι)).map
          (T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) m a)) ≫
        (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
          (actualPositiveTwistChartUnitIso I ell m)).hom) =
    (affineGlobalSectionsUnitLinearEquiv
      (A := Away (grading I) (ell : CoordinateRing I))).symm
        (Away.mk (grading I) ell.property m (a : CoordinateRing I) (by simpa using a.property)) := by
  dsimp only
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.property Nat.zero_lt_one
  let T := positiveSheafOfModules (grading I) m
  change unitEndomorphismValue
    ((Scheme.Modules.restrictUnitIso (e.inv ≫ U.ι)).inv ≫
      (Scheme.Modules.restrictFunctor (e.inv ≫ U.ι)).map
        (T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) m a)) ≫
      ((Scheme.Modules.restrictFunctorComp e.inv U.ι).app T).hom ≫
      (Scheme.Modules.restrictFunctor e.inv).map (actualPositiveTwistChartUnitIso I ell m).hom ≫
      (Scheme.Modules.restrictUnitIso e.inv).hom) = _
  have hRefined := cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoefficient
    e.inv U.ι T (actualPositiveTwistChartUnitIso I ell m)
    (T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) m a))
  have hCoefficient := actualPositiveTwistChartUnitHomogeneousCoefficient I ell m a
  exact hRefined.trans
    ((congrArg (fun z => e.inv.appTop z) hCoefficient).trans
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartFunction I ell _))

end PfaffianDescent
