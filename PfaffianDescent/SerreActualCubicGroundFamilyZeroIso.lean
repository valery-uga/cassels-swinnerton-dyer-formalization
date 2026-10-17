import PfaffianDescent.SerreActualCubicGroundFamilyGlobalZeroComparison
import PfaffianDescent.SerreActualClosedPullbackZeroIso

/-! The actual pulled cubic universal zero families are isomorphic over the
common surface--kernel-plane family. The equality of their defining ideals
is supplied by the native global comparison, not an additional premise. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (A : SchemeModuleFiniteFreeAffineCover e.E I)
variable (B : SchemeModuleFiniteFreeAffineCover
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
variable (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
variable (hHG : H * G = 1)

def serreActualCubicGroundFamily_zeroIso :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    pullback (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
        (B.projectiveSectionLocalZeroGluedToAmbient x M) ≅
      pullback (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
        (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
  exact serreActualClosedPullbackZeroIso _ _ _ _
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG)

@[reassoc]
theorem serreActualCubicGroundFamily_zeroIso_hom_fst :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    (serreActualCubicGroundFamily_zeroIso p hp e C h9 A B G H hHG).hom ≫
        pullback.fst (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
          (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      pullback.fst (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
        (B.projectiveSectionLocalZeroGluedToAmbient x M) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
  exact serreActualClosedPullbackZeroIso_hom_fst _ _ _ _
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG)

end PfaffianDescent
