import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedSectionsStalk
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedSectionsSurface
import PfaffianDescent.SerreActualChosenMarkedSectionsCompatibility

/-! The index is the exact section record,
so proof bundling cannot choose a different section or parameter. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

structure SerreActualChosenMarkedSectionFacts
    {F E : Type u} [Field F] [Field E]
    {X P Z Y : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) (tE : Spec (.of E) ⟶ P)
    (d : SerreActualChosenMarkedSections x pp zero tE) (n : Fin 3)
    (f : X ⟶ Y) (original : Spec (.of E) ⟶ Y) : Prop where
  stalk : IsField ((pullback (zero ≫ pullback.snd x pp) tE).presheaf.stalk
    ((d.δ n) (IsLocalRing.closedPoint E)))
  originalSurface : serreActualChosenFibre_marked x pp zero tE d.δ n ≫ f = original

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
def serreActualCubicGroundFamily_oldSeed_literalTransportedMarked_sectionFacts :=
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
      cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
        marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (cA : Spec (.of E) ⟶ Cfg)
    (hcfg : s ≫ serreThreePointSectionIncidenceToConfiguration cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) = cA)
    (n : Fin 3) =>
    let d := serreActualCubicGroundFamily_oldSeed_literalTransportedMarked_sections
      p hp e C h9 A B G H hHG bE cfg marked hm s hsp
    let tE := bE ≫ serreActualCubicGroundKernelParameters p hp e C h9 G H hHG
    let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp
    let π := serreThreePointSectionIncidenceToConfiguration cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
    let hSurface := serreActualCubicGroundFamily_oldSeed_literalTransportedMarked_sections_surface_original
      p hp e C h9 A B G H hHG bE cfg marked hm s hsp n
    show SerreActualChosenMarkedSectionFacts x pp zero tE d n f (cA ≫ marked n) from
    ⟨serreActualCubicGroundFamily_oldSeed_literalTransportedMarked_sections_stalk_isField
        p hp e C h9 A B G H hHG bE cfg marked hm s hsp hs n,
      serreActualChosenMarkedSections_surface_original_of_configuration
        x pp zero tE d f π s cA (marked n) n hSurface hcfg⟩

end PfaffianDescent
