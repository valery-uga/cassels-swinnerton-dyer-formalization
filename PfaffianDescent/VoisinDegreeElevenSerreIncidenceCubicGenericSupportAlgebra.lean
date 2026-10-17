import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicSupportAlgebra
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicGenericTensorField

/-! # Original geometry derives the actual retained generic support coefficient field -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubic_generic_support_coefficient_field_degree
    {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L] [Module.Finite K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    letI := a.hom.toAlgebra
    let D := pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i
    let q := pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp) i ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
    letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
    letI := finiteSchemeCoefficientAlgebra q
    IsField Γ(D, ⊤) ∧ Module.finrank (cubicConfigurationBase p hp n).functionField Γ(D, ⊤) =
      Module.finrank K L := by
  letI := a.hom.toAlgebra
  exact serreIncidenceCubicSupport_coefficient_field_degree p hp i hi
    (serreIncidenceCubic_generic_tensor_isField (L := L) p hp hp0 n a ha)

end PfaffianDescent
