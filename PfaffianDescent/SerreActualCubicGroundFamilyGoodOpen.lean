import PfaffianDescent.SerreActualCubicGroundFamilyGlobalZeroComparison
import PfaffianDescent.SerreActualClosedPullbackZeroGoodOpen

/-! Equality of the actual finite-fibre parameter opens for the original and
coefficient-cubic zero families. All closed/proper and comparison data are
derived internally. The proof type is inferred from the checked comparison. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_goodOpen_eq
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
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  let a := pullback.snd x
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
  let n := serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG
  let o := serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG
  let newZero := B.projectiveSectionLocalZeroGluedToAmbient x M
  let oldZero := A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E
  serreActualClosedPullbackZero_goodOpen_eq newZero oldZero n o
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) a

end PfaffianDescent
