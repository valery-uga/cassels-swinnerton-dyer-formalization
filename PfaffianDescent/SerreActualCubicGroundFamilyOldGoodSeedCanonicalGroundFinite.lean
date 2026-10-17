import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedCanonicalFinite
import PfaffianDescent.SerreActualCanonicalChosenGroundFibreFinite

/-! The actual old finite-good seed supplies finiteness of the new canonical
fibre over the chosen original ground field, not just its splitting field. -/
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

/-- Finiteness descends at the actual same rational ground parameter. The
extension fibre's finiteness is constructed from the old good seed internally. -/
@[irreducible]
def serreActualCubicGroundFamily_oldGoodSeed_canonicalGroundFibre_isFinite :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  letI := serreSectionUniversalZeroToParameters_isProper
    (hypersurfaceToBase p hp) e.E A
  fun {E : Type u} [Field E] [Algebra F E]
    (b : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ b) ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (hs : s (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        (serreThreePointSectionIncidenceZeroFamily cfg (hypersurfaceToBase p hp)
          (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
          marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))) =>
    letI := serreSectionUniversalZeroToParameters_isProper x M B
    letI := serreActualCubicGroundFamily_oldGoodSeed_canonicalNewFibre_finite
      p hp e C h9 A B G H hHG
      (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ b) cfg marked hm s hsp hs
    serreActualCanonicalChosenGroundFibre_isFinite (E := E)
      (B.projectiveSectionLocalZeroGluedToAmbient x M ≫
        pullback.snd x (schemeModuleGlobalSectionsProjectiveParametersToBase x M))
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG) b

end PfaffianDescent
