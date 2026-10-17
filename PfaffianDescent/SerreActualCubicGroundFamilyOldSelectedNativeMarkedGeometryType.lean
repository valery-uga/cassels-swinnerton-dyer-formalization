import PfaffianDescent.SerreActualCubicGroundFamilyOldSelectedNativeGoodMembership
import PfaffianDescent.SerreActualChosenMarkedResidualGeometry
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedCanonicalMarked
import PfaffianDescent.SerreActualGroundFamilyLiteralMarkedSurfaceOriginal
import PfaffianDescent.CubicConfigurationOrderedFieldCoefficientMarkedIdentification
import PfaffianDescent.SerreActualChosenMarkedParameterAssociationPointSurface
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedStalk
import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedNewMarkedGoodOpen
import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSupportAvoidance
import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupport

/-! Actual old selected incidence data give residual eight at the same native
G/H/qF. All new marked field/support/finite-good data are constructed internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_oldSelectedSeed_nativeMarkedResidualGeometryType
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (ι : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion ι]
    (hι : ι ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist ι (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank] : Type u :=
  let F := (cubicConfigurationBase p hp 3).functionField
  let E := Rk.residueField (genericPoint Rk)
  letI : Algebra K F := a.hom.toAlgebra
  let cA := Rk.fromSpecResidueField (genericPoint Rk)
  let c := cA ≫ aRank
  let cfg := aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom
  let marked : Fin 3 → (Rk ⟶ hypersurface p hp) := fun k =>
    aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 k).left
  let hm : ∀ k, marked k ≫ hypersurfaceToBase p hp = cfg := fun k => by
    simp only [marked, cfg, Category.assoc, orderedFamilyCoordinate_toBase,
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).w]
  let A := serreIncidenceRankTwoAffineCover e C
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E
  let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp ι e C
  let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp ι e C
  let B := serreIncidenceRankTwoAffineCover e' C'
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase x M
  let zero := B.projectiveSectionLocalZeroGluedToAmbient x M
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  letI := serreSectionUniversalZeroToParameters_isProper x M B
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules := schemeModules_hasExt _
  let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : IsFinite (D₃.val.subschemeι ≫ x) := D₃.property.1
  letI : Field Γ(D₃.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  letI : Algebra F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ x)
  letI : FiniteDimensional F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ x)
  let j₃ := finiteSubschemeDatumSpecMap x D₃
  let hj₃ := finiteSubschemeDatumSpecMap_toBase x D₃
  let h3 : finrank F Γ(D₃.val.subscheme, ⊤) = 3 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank x D₃
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp
  ∀ (β : F →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) = c ≫ configurationQuotientMap (equationIdeal p hp) 3)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F) (hHG : H * G = 1)
    (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (hqF : qF ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) = 𝟙 _),
    letI : Algebra F E := β.toAlgebra
    let r := Spec.map (CommRingCat.ofHom (algebraMap F E))
    let bE := r ≫ qF
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      bE ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (hcfg : s ≫ serreThreePointSectionIncidenceToConfiguration cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) = cA)
    (hgood : s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen
      (serreThreePointSectionIncidenceZeroFamily cfg (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
        marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)))
    (hmarked : s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen
      cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)),
    SerreActualChosenMarkedResidualGeometry
      (E := E) (L := Γ(D₃.val.subscheme, ⊤)) x pp zero
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp ι)
      j₃ (bE ≫ serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)

end PfaffianDescent
