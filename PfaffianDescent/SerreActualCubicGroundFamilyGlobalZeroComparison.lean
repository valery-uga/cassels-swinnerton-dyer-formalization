import PfaffianDescent.SerreActualCubicGroundFamilyLocalZeroComparison
import PfaffianDescent.SerreActualPairChartAffineRefinement

/-! The actual old and new cubic universal zero families have equal ideals
after pullback to the common surface--kernel-plane family. The paired affine
cover supplies all local chart factorizations internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_global_zero_comparison
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : SchemeModuleFiniteFreeAffineCover e.E I)
    (B : SchemeModuleFiniteFreeAffineCover
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M : (hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F))).Modules :=
    (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  let U := B.projectiveSectionOpenCover x M
  let V := A.projectiveSectionOpenCover (hypersurfaceToBase p hp) e.E
  let n := serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG
  let o := serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG
  serreActualPairChart_comap_eq U V n o
    (B.projectiveSectionLocalZeroGluedToAmbient x M).ker
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E).ker
    (fun k => serreActualCubicGroundFamily_local_zero_comparison
      p hp e C h9 A B G H hHG
      ((serreActualPairChartAffineCover U V n o).f k)
      k.1.2 k.1.1 (serreActualPairChartRightMap U V n o k)
      (serreActualPairChartLeftMap U V n o k)
      (serreActualPairChartRightMap_factor U V n o k)
      (serreActualPairChartLeftMap_factor U V n o k))

end PfaffianDescent
