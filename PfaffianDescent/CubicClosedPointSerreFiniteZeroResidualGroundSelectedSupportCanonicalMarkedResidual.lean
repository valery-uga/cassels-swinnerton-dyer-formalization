import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedDimension
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChosenCanonicalMarkedResidual
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
and unordered generic-three datum. The literal canonical marked stalk replaces
new relative marked-open membership. Field structures, degrees and finiteness of
both supports are derived internally. The chosen parameter is unchanged. -/
@[irreducible]
def cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_canonical_marked_residual_eight
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
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] := by
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
  exact fun {L₃ : Type u} [Field L₃] [Algebra F L₃] [FiniteDimensional F L₃]
    (j₃ : Spec (.of L₃) ⟶ hypersurface P hP) [IsClosedImmersion j₃]
    (hj₃ : j₃ ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F L₃)))
    (h3 : Module.finrank F L₃ = 3)
    {E : Type u} [Field E] [Algebra F E] {B : Scheme.{u}}
    (cfg : B ⟶ Spec (.of F)) (marked : Fin 3 → (B ⟶ hypersurface P hP))
    (hm : ∀ n, marked n ≫ base = cfg) =>
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e' C'
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI := serreSectionUniversalZeroToParameters_isProper base M D
    fun t ht s hW hsp n hout hpoint y hy hySurface =>
      let H := cubicClosedPointSerreFiniteZeroResidual_chosen_canonical_marked_residual_eight
        (E := E) (L₃ := L₃) F P hP (cubicConfigurationCoefficientChange_ne_zero p hp 3 a hp0)
        i' e' hi' h11 C' j₃ hj₃ h3 cfg marked hm t ht s hW hsp n hout hpoint y hy hySurface
      H.elim (fun R hR => Exists.intro R
        (And.intro hR (finiteSubschemeDatumCycle_degree base R)))

end PfaffianDescent.ProjectiveNegativeTwist
