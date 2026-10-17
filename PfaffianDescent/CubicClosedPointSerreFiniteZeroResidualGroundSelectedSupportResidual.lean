import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedDimension
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
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_residual_eight
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
    ∀ {L₃ : Type u} [Field L₃] [Algebra F L₃] [FiniteDimensional F L₃]
      (j₃ : Spec (.of L₃) ⟶ hypersurface P hP) [IsClosedImmersion j₃]
      (hj₃ : j₃ ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F L₃)))
      (hL₃ : Module.finrank F L₃ = 3),
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
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint L₃) →
      ∃ R : FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range j₃) ∧
        EffectiveZeroCycle.degree base (finiteSubschemeDatumCycle base R) = 8 := by
  let F := (cubicConfigurationBase p hp 3).functionField
  letI := a.hom.toAlgebra
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 3
  let P := p.map a.hom
  let hP := hp.map a.hom
  let base := hypersurfaceToBase P hP
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp
  let Z := pullback f i
  let q := pullback.fst f i ≫ base
  letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
  letI : IsAffine Z := isAffine_of_isAffineHom q
  letI : Field Γ(Z, ⊤) := cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupportField p hp hp0 a ha i hi
  letI : Algebra F Γ(Z, ⊤) := finiteSchemeCoefficientAlgebra q
  letI : FiniteDimensional F Γ(Z, ⊤) := finiteSchemeCoefficient_finite q
  let i' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp i
  have hi' : i' ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Z, ⊤))) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupport_toBase p hp a i hi
  have h11 : Module.finrank F Γ(Z, ⊤) = 11 :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupport_degree p hp hp0 a ha i hi hL
  let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp i e C
  let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp i e C
  let M : (hypersurface P hP).Modules := e'.E
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver base M) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelected_globalFiniteDimensional p hp hp0 a ha i hi hL e C
  letI : Smooth base := smooth_cubicConfigurationGenericCoefficientChange p hp 3 a
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).ringCatSheaf) :=
    (show HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules from inferInstance)
  letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
  letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface P hP).presheaf.stalk (i' default))) := moduleCatStalk_hasExt _
  dsimp only
  intro L₃ hL₃Field hL₃Alg hL₃Fin j₃ hL₃Closed hj₃ h3 E hE hFE B cfg marked hm t ht s hW hsp n hout hpoint
  obtain ⟨R, hR⟩ := cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_residual_eight_of_rankTwoCover
    F P hP (cubicConfigurationCoefficientChange_ne_zero p hp 3 a hp0)
    i' e' hi' h11 C' j₃ hj₃ h3 cfg marked hm t ht s hW hsp n hout hpoint
  exact ⟨R, hR, finiteSubschemeDatumCycle_degree base R⟩

end PfaffianDescent.ProjectiveNegativeTwist
