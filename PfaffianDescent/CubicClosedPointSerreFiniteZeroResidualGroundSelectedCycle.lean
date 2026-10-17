import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelected
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedFibre

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- The SAME chosen parameter has finite zero of degree eleven and an actual
disjoint residual datum of degree eight, with its effective cycle. Both support
fields and degrees are derived from the original cubic data. -/
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelected_finite_eleven_residual_cycle_eight
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
      let q := pullback.snd z t
      IsFinite q ∧ (∀ x, q.finrank x = 11) ∧
      ∃ R : FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range D₃.val.subschemeι) ∧
        EffectiveZeroCycle.degree base (finiteSubschemeDatumCycle base R) = 8 := by
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
  let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : Field Γ(D₃.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  dsimp only
  intro E hE hFE B cfg marked hm t ht s hW hsp n hout hpoint
  have hf := cubicClosedPointSerreFiniteZeroResidual_groundSelected_fibre_rank_eleven
    p hp hp0 a ha i hi hL e C cfg marked hm t ht s hW hsp n hout hpoint
  have hR := cubicClosedPointSerreFiniteZeroResidual_groundSelected_residual_eight
    p hp hp0 a ha i hi hL e C cfg marked hm t ht s hW hsp n hout hpoint
  exact ⟨hf.1, hf.2, hR⟩

end PfaffianDescent.ProjectiveNegativeTwist
