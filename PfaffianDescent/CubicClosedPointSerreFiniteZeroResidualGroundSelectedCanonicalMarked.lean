import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedSupportCanonicalMarkedResidual
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

theorem cubicClosedPointSerreFiniteZeroResidual_disjoint_canonicalSpec_nativeSupport
    {F : Type u} [Field F] {X : Scheme.{u}} (x : X ⟶ Spec (.of F))
    (D : FiniteSubschemeDatum x 3) (R : FiniteSubschemeDatum x 8)
    (h : Disjoint (Set.range R.val.subschemeι) (Set.range (finiteSubschemeDatumSpecMap x D))) :
    Disjoint (Set.range R.val.subschemeι) (Set.range D.val.subschemeι) := by
  simpa only [range_finiteSubschemeDatumSpecMap_eq_range_subschemeι] using h

/-- Residual eight on the SAME coefficient cubic, pulled canonical Serre bundle,
and unordered generic-three datum. Field structures, degrees and finiteness of
both supports are derived internally. The chosen parameter is unchanged.
Only finite-good membership is required; marked simplicity is supplied at the
literal canonical field-stalk endpoint rather than by a new relative marked-open. -/
@[irreducible]
def cubicClosedPointSerreFiniteZeroResidual_groundSelected_canonical_marked_residual_eight
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
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :=
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
  let i' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp i
  let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : IsFinite (D₃.val.subschemeι ≫ base) := D₃.property.1
  letI : Field Γ(D₃.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  letI : Algebra F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ base)
  letI : FiniteDimensional F Γ(D₃.val.subscheme, ⊤) := finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ base)
  let j₃ := finiteSubschemeDatumSpecMap base D₃
  let hj₃ := finiteSubschemeDatumSpecMap_toBase base D₃
  let h3 : Module.finrank F Γ(D₃.val.subscheme, ⊤) = 3 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank base D₃
  fun {E : Type u} [Field E] [Algebra F E] {B : Scheme.{u}}
    (cfg : B ⟶ Spec (.of F))
    (marked : Fin 3 → (B ⟶ hypersurface P hP))
    (hm : ∀ n, marked n ≫ base = cfg) =>
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e' C'
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    fun (t : Spec (.of F) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M)
      (ht : t ≫ pp = 𝟙 _)
      (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero)
      (hW : s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g)
      (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)
      (n : Fin 3)
      (hout : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i')
      (hpoint : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint Γ(D₃.val.subscheme, ⊤)))
      (y : (pullback (zero ≫ pullback.snd base pp)
        (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) : Scheme))
      (hy : IsField ((pullback (zero ≫ pullback.snd base pp)
        (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)).presheaf.stalk y))
      (hySurface : (pullback.fst (zero ≫ pullback.snd base pp)
        (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) ≫ zero ≫ pullback.fst base pp) y =
        j₃ (IsLocalRing.closedPoint Γ(D₃.val.subscheme, ⊤))) =>
      let H := cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_canonical_marked_residual_eight
        (E := E) (L₃ := Γ(D₃.val.subscheme, ⊤)) p hp hp0 a ha i hi hL e C j₃ hj₃ h3 cfg marked hm
        t ht s hW hsp n hout hpoint y hy hySurface
      H.elim (fun R hR => Exists.intro R (And.intro
        (cubicClosedPointSerreFiniteZeroResidual_disjoint_canonicalSpec_nativeSupport base D₃ R hR.1) hR.2))

end PfaffianDescent.ProjectiveNegativeTwist
