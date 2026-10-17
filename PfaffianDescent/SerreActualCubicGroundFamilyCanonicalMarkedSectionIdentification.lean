import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewCanonicalMarkedStalk

/-! Identify the actual canonical marked section with the literal transported
section used by the checked new incidence-seed constructor. -/
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
variable {U Cfg : Scheme.{u}}
variable (b : U ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))

/-- This is a derived identity of the actual sections, not a coordinate
certificate input. Only the wrapper definitions of the same two fibre
isomorphisms and the same old marked section are unfolded. -/
@[irreducible]
def serreActualCubicGroundFamily_canonicalNewMarkedSection_eq_literalTransported :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  fun (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : U ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      b ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (i : Fin 3) =>
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
      b cfg marked hm s hsp
    (show serreActualCubicGroundFamily_oldSeed_toCanonicalNewMarkedSection
        p hp e C h9 A B G H hHG b cfg marked hm s hsp i =
      serreActualGroundFamily_transportedChosenMarked
        x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
        (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
        (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
        (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
        (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
        (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
        (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
        (B.projectiveSectionLocalZeroGluedToAmbient x M)
        (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
        (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
        (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG)
        b m i from by
      simp only [serreActualCubicGroundFamily_oldSeed_toCanonicalNewMarkedSection,
        serreActualCubicGroundFamily_oldSeedToCommonFibreIso,
        serreActualGroundFamily_oldSeed_commonMarkedSection,
        serreActualGroundFamily_transportedChosenMarked,
        serreActualCubicGroundFamily_chosenOldToCanonicalNewIso,
        serreActualCubicGroundFamily_parameterChangeIso,
        serreActualCubicGroundFamily_chosenNewFibreIso,
        serreActualGroundFamily_oldToCanonicalChosenFibreIso,
        m, x, M, Iso.trans_hom, Iso.symm_hom, Category.assoc])

end PfaffianDescent
