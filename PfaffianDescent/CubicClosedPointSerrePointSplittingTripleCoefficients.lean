import PfaffianDescent.CubicClosedPointSerrePointSplittingComponentAlgebra

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingUliftReindex {E : Type u} [Field E] (n : ℕ) :
    (ULift.{u} (Fin n) → E) ≃ₗ[E] (Fin n → E) where
  toFun v i := v (ULift.up i)
  invFun v i := v i.down
  left_inv v := by funext i; cases i; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q]
variable (e : (∐ fun _ : ULift.{u} (Fin 3) ↦ Spec (.of E)) ≅
  pullback q (Spec.map (CommRingCat.ofHom (algebraMap F E))))
variable (he : e.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
  AllCharacteristics.constantCoverToBase (ULift.{u} (Fin 3)) (Spec (.of E)))

def pointSplittingFiniteTripleCoefficientEquiv :
    letI := finiteSchemeCoefficientAlgebra q
    (E ⊗[F] Γ(D, ⊤)) ≃ₗ[E] (Fin 3 → E) := by
  letI := finiteSchemeCoefficientAlgebra q
  exact (pointSplittingFiniteCoordinateAlgEquiv q 3 e he).toLinearEquiv ≪≫ₗ
    pointSplittingUliftReindex 3

theorem pointSplittingFiniteTripleCoefficientEquiv_one_tmul (a : Γ(D, ⊤)) :
    letI := finiteSchemeCoefficientAlgebra q
    pointSplittingFiniteTripleCoefficientEquiv q e he (1 ⊗ₜ[F] a) =
      fun k => pointSplittingFiniteComponentAlgHom q 3 e he (ULift.up k) a := by
  letI := finiteSchemeCoefficientAlgebra q
  funext k
  exact pointSplittingFiniteCoordinateAlgEquiv_one_tmul q 3 e he a (ULift.up k)

end PfaffianDescent
