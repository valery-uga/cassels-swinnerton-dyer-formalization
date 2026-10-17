import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedCanonicalFinite
import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSeed
import PfaffianDescent.SerreActualChosenFibreGoodIncidenceSeed

/-! An old finite-good seed supplies finite-good membership of the actual new
marked incidence seed at the same chosen ground parameter. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem serreActualFiniteSupport_isFinite_of_isProper
    {X Y : Scheme.{u}} [Finite X] (f : X ⟶ Y) [IsProper f] : IsFinite f := by
  letI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

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

/-- Finiteness of the chosen canonical fibre is derived from the actual old
good seed. The new seed and all three transported marked sections are exactly
the checked constructor's sections, with no new open-membership premise. -/
@[irreducible]
def serreActualCubicGroundFamily_oldGoodSeed_toNewMarkedSeed_mem_goodOpen :=
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
    (hs : s (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        (serreThreePointSectionIncidenceZeroFamily cfg (hypersurfaceToBase p hp)
          (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
          marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))) =>
    let t := bE ≫ serreActualCubicGroundKernelParameters p hp e C h9 G H hHG
    letI : Finite (pullback (zero ≫ pullback.snd x pp) t : Scheme.{u}) :=
      serreActualCubicGroundFamily_oldGoodSeed_canonicalNewFibre_finite
        p hp e C h9 A B G H hHG bE cfg marked hm s hsp hs
    letI : IsFinite (pullback.snd (zero ≫ pullback.snd x pp) t) :=
      serreActualFiniteSupport_isFinite_of_isProper _
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
    serreActualChosenFibre_incidenceSeed_mem_goodOpen x pp zero t δ hδ

end PfaffianDescent
