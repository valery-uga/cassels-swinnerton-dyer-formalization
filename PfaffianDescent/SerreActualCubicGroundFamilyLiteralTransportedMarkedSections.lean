import PfaffianDescent.SerreActualChosenMarkedSections
import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSeed

/-! Construct the literal transported sections in one small record.
No support-field or rank-chart instance is part of this stage. -/
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
variable {Cfg : Scheme.{u}}

@[irreducible]
def serreActualCubicGroundFamily_oldSeed_literalTransportedMarked_sections :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase x M
  let zero := B.projectiveSectionLocalZeroGluedToAmbient x M
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  letI := serreSectionUniversalZeroToParameters_isProper x M B
  fun {E : Type u} [Field E]
    (bE : Spec (.of E) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      bE ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    =>
    let m := serreActualGroundFamily_oldSeed_commonMarkedSection
      (hypersurfaceToBase p hp) x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      bE cfg marked hm s hsp
    let hmNew := serreActualGroundFamily_oldSeed_commonMarkedSection_toParameter
      (hypersurfaceToBase p hp) x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      bE cfg marked hm s hsp
    let δ := serreActualGroundFamily_transportedChosenMarked
      x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) pp
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
      (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG) zero
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) bE m
    let hδ := serreActualGroundFamily_transportedChosenMarked_toParameter
      x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) pp
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
      (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG) zero
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) bE m hmNew
    SerreActualChosenMarkedSections.mk
      (x := x) (pp := pp) (zero := zero)
      (t := bE ≫ serreActualCubicGroundKernelParameters p hp e C h9 G H hHG) δ hδ

end PfaffianDescent
