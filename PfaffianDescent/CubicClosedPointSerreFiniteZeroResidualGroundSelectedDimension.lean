import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedSupport
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
theorem cubicClosedPointSerreFiniteZeroResidual_groundSelected_globalFiniteDimensional
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
    FiniteDimensional F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp i e C).E) := by
  letI := a.hom.toAlgebra
  exact serreIncidenceCubicCoefficientGlobalSections_finiteDimensional p hp e C

end PfaffianDescent.ProjectiveNegativeTwist
