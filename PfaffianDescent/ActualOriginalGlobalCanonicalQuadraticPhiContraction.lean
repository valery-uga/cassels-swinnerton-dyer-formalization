import PfaffianDescent.ActualOriginalPositiveTwoPointContraction
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhi

/- SOURCE ONLY / UNVERIFIED. The genuinely GLOBAL Phi contracts to the
same genuinely GLOBAL untwisted conormal map on the original point fiber.
The original native O2 point trivialization is internally constructed.
No desired Phi/native-chart identification is an input or asserted here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalGlobalCanonicalQuadraticPhi_contract
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let L := (hypersurface p hp).residueField P.1
    let T := (Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) 2)
    let e := actualOriginalPositiveTwoPointTrivialization p hp P hP
    let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
    (moduleSpecΓFunctor (R := .of L)).map
      ((actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) 2).hom ≫
        (actualPointTwistUntwistIso
          ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials (toBase I))) T e).hom)
      (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q)
      ((moduleSpecΓFunctor (R := .of L)).map
        ((actualPositiveTwistPullbackTensorIso I q (closedImmersionModule q) 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj
            (closedImmersionModule q)) T e).hom)
        (actualModulePointSectionClass q M
          (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s))) := by
  dsimp only
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let L := (hypersurface p hp).residueField P.1
  let T := (Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) 2)
  let e := actualOriginalPositiveTwoPointTrivialization p hp P hP
  let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
  let G := moduleSpecΓFunctor (R := .of L)
  let z := actualModulePointSectionClass q M
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
  change G.map
    ((actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj
        (schemeRelativeDifferentials (toBase I))) T e).hom)
    (G.map (actualGlobalPositiveTwistConormalDifferentialMap I q 2) z) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  have h := actualOriginalPositiveTwoPointContraction_square p hp P hP
  change actualGlobalPositiveTwistConormalDifferentialMap I q 2 ≫
    ((actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj
        (schemeRelativeDifferentials (toBase I))) T e).hom) =
    (actualPositiveTwistPullbackTensorIso I q (closedImmersionModule q) 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj
        (closedImmersionModule q)) T e).hom ≫
      actualGlobalClosedConormalDifferentialMap (toBase I) q at h
  rw [h]
  simp only [Functor.map_comp, ModuleCat.comp_apply, G, z, I, q, L, T, e, M]
  rfl

end PfaffianDescent
