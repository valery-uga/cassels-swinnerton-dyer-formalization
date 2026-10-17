import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientCanonicalSerre
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicGenericSupportAlgebra
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalDimension
import AllCharacteristics.VoisinGenericCubicPoint
import Mathlib.Algebra.CharZero.Infinite

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
variable {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
  [FiniteDimensional K L]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)]
  [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
  [IsIntegral (cubicConfigurationBase p hp 3)]
  (a : CommRingCat.of K ⟶ (cubicConfigurationBase p hp 3).functionField)
  (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
  (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
  (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The field structure is derived from the actual retained support, not supplied. -/
def cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupportField :
    Field Γ(pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i, ⊤) :=
  (serreIncidenceCubic_generic_support_coefficient_field_degree p hp hp0 3 a ha i hi).1.toField

include hp0 ha in
/-- The canonical source has the native coefficient action and the original degree. -/
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupport_degree
    (hL : Module.finrank K L = 11) :
    letI := a.hom.toAlgebra
    let q := pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
    letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
    letI := finiteSchemeCoefficientAlgebra q
    Module.finrank (cubicConfigurationBase p hp 3).functionField
      Γ(pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i, ⊤) = 11 := by
  exact (serreIncidenceCubic_generic_support_coefficient_field_degree p hp hp0 3 a ha i hi).2.trans hL

/-- The SAME canonical spectrum point is over the literal new ground field. -/
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelectedSupport_toBase :
    letI := a.hom.toAlgebra
    let q := pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
    letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
    letI := finiteSchemeCoefficientAlgebra q
    cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp i ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) =
      Spec.map (CommRingCat.ofHom (algebraMap (cubicConfigurationBase p hp 3).functionField
        Γ(pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i, ⊤))) := by
  letI := a.hom.toAlgebra
  let q := pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i ≫
    hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
  letI := finiteSchemeCoefficientAlgebra q
  letI : IsAffine (pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i) :=
    isAffine_of_isAffineHom q
  simpa only [cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint, q,
    Category.assoc] using (finiteSchemeCoefficient_spec q).symm

include hp0 in
/-- The actual unordered generic-three datum is a field, internally. -/
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField :
    IsField Γ((cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subscheme, ⊤) := by
  letI : GeometricallyIntegral (hypersurfaceToBase p hp) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left :=
    isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral (hypersurfaceToBase p hp) 3
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := by
    change IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left
    infer_instance
  exact cubicConfigurationGenericFiniteSubscheme_isField p hp 3 a ha (0 : Fin 3)

end PfaffianDescent.ProjectiveNegativeTwist
