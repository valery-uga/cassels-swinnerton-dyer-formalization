import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericTensorField
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceConfigurationGeometric
import PfaffianDescent.VoisinGenericCubicResidual

/-! # Native retained support field over the literal unordered cubic configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubic_generic_tensor_isField
    {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L] [Module.Finite K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n) :
    letI := a.hom.toAlgebra
    IsField (L ⊗[K] (cubicConfigurationBase p hp n).functionField) := by
  letI : GeometricallyIntegral (hypersurfaceToBase p hp) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hp0
  letI : GeometricallyIntegral (cubicConfigurationToBase p hp n) :=
    serreIncidenceConfiguration_quotient_geometricallyIntegral
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) n
  exact serreIncidenceGeometric_generic_tensor_isField (L := L)
    (cubicConfigurationToBase p hp n) a ha

end PfaffianDescent
