import AllCharacteristics.ProjectiveBaseChange
import PfaffianDescent.CorayComponentFiniteGaloisDefinition
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.Algebraic.Integral

/-! Actual algebraic field coefficient projection transports finite closed
geometric bad loci to finite closed loci over the original field. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective coefficient projection for an algebraic field
extension is integral. Thus the image of any constructed finite closed locus
is finite closed over original K, and the original complementary open pulls
inside the geometric complementary open. No closed-image premise is supplied. -/
theorem algebraicField_projectiveCoefficientProjection_integral_finiteClosedImage001
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :
    let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
    let g := projectiveCoefficientMap (algebraMap K E) I J rfl
    IsIntegralHom g ∧
      ∀ S : Set (scheme J), IsClosed S → S.Finite →
        IsClosed (g '' S) ∧ (g '' S).Finite ∧
          g ⁻¹' (g '' S)ᶜ ⊆ Sᶜ := by
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
  let g := projectiveCoefficientMap (algebraMap K E) I J rfl
  let b := Spec.map (CommRingCat.ofHom (algebraMap K E))
  have hb : IsIntegralHom b :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  letI : IsIntegralHom g :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom.{u})
      (isPullback_projectiveCoefficientMap (algebraMap K E) I J rfl).flip hb
  refine ⟨inferInstance, ?_⟩
  intro S hClosed hFinite
  refine ⟨g.isClosedMap S hClosed, hFinite.image g, ?_⟩
  intro x hx hS
  exact hx ⟨x, hS, rfl⟩

end PfaffianDescent.Coray
