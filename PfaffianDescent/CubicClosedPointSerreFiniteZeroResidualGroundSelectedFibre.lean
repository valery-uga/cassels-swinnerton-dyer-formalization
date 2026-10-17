import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedSupportFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedRingField
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalChosenCoverResidual
import PfaffianDescent.CubicFiniteFieldDatumSerreExtension

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- Residual eight on the SAME coefficient cubic, pulled canonical Serre bundle,
and unordered generic-three datum. Field structures, degrees and finiteness of
both supports are derived internally. The chosen parameter is unchanged. -/
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelected_fibre_rank_eleven
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    let F := (cubicConfigurationBase p hp 3).functionField
    letI := a.hom.toAlgebra
    let P := p.map a.hom
    let hP := hp.map a.hom
    let base := hypersurfaceToBase P hP
    let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp i e C
    let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp i e C
    let M : (hypersurface P hP).Modules := e'.E
    letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver base M) :=
      cubicClosedPointSerreFiniteZeroResidual_groundSelected_globalFiniteDimensional p hp hp0 a ha i hi hL e C
    let i' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp i
    let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
    letI : Field Γ(D₃.val.subscheme, ⊤) :=
      cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
        (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
    let j₃ := finiteSubschemeDatumSpecMap base D₃
    ∀ {E : Type u} [Field E] [Algebra F E] {B : Scheme.{u}}
      (cfg : B ⟶ Spec (.of F))
      (marked : Fin 3 → (B ⟶ hypersurface P hP))
      (hm : ∀ n, marked n ≫ base = cfg),
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e' C'
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    ∀ (t : Spec (.of F) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      t ≫ pp = 𝟙 _ →
      ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_goodOpen g ⊓
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked hm zero →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i' →
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint Γ(D₃.val.subscheme, ⊤)) →
      let z := zero ≫ pullback.snd base pp
      let c := pullback.snd z t
      IsFinite c ∧ (∀ x, c.finrank x = 11) := by
  let F := (cubicConfigurationBase p hp 3).functionField
  letI := a.hom.toAlgebra
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 3
  let P := p.map a.hom
  let hP := hp.map a.hom
  let base := hypersurfaceToBase P hP
  let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp i e C
  let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp i e C
  let M : (hypersurface P hP).Modules := e'.E
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver base M) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelected_globalFiniteDimensional p hp hp0 a ha i hi hL e C
  let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : IsFinite (D₃.val.subschemeι ≫ base) := D₃.property.1
  letI : Field Γ(D₃.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  letI : Algebra F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ base)
  letI : FiniteDimensional F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ base)
  let j₃ := finiteSubschemeDatumSpecMap base D₃
  have hj₃ := finiteSubschemeDatumSpecMap_toBase base D₃
  have h3 : Module.finrank F Γ(D₃.val.subscheme, ⊤) = 3 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank base D₃
  dsimp only
  intro E hE hFE B cfg marked hm t ht s hW hsp n hout hpoint
  exact cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_fibre_rank_eleven
    p hp hp0 a ha i hi hL e C j₃ hj₃ h3 cfg marked hm t ht s hW hsp n hout hpoint

end PfaffianDescent.ProjectiveNegativeTwist
