import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationSchemeIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientSerre
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalSectionsFieldDimension
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalSectionsBaseCongr

/-! # Actual global sections transported to the literal coefficient cubic -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceCubicCoefficientGlobalSectionsIso
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (M : (hypersurface p hp).Modules) :
    SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))).obj M) ≃ₗ[F]
    SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj M) := by
  let e := hypersurfaceBaseChangeIso (algebraMap K F) p hp
  let g := schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp)
  let q := schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp)
  let z := cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv q e
    ((Scheme.Modules.pullback g).obj M)
  have hq : e.hom ≫ q =
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) :=
    hypersurfaceBaseChangeIso_hom_snd (algebraMap K F) p hp
  let em : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj M :=
    (Scheme.Modules.pullbackComp e.hom g).app M ≪≫
      (Scheme.Modules.pullbackCongr
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection
          (algebraMap K F) p hp)).app M
  have z' : SchemeModuleGlobalSectionsOver q ((Scheme.Modules.pullback g).obj M) ≃ₗ[F]
      SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback g).obj M)) := by
    exact z.trans (serreIncidenceGlobalSectionsBaseCongr _ _ hq _)
  exact z'.trans (cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv _ em)

end PfaffianDescent
