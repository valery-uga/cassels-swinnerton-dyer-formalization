import PfaffianDescent.CubicConfigurationGenericCoefficientTransport
import PfaffianDescent.FiniteSchemeAlgebra
import AllCharacteristics.ProjectiveConfigurationGenericSplitFiber

/-! Actual labeled components of the canonical finite configuration,
constructed directly from its ordered field point. This works for any
configuration length, including the native eleven-point interpolation field.
-/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
variable [hB : IsIntegral (cubicConfigurationBase p hp n)]

local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).toScheme := hB

variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
variable (β : (cubicConfigurationBase p hp n).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp n).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp n)) =
  c ≫ configurationQuotientMap (equationIdeal p hp) n)

def cubicConfigurationOrderedFieldComponentPoint (k : Fin n) :
    Spec (.of E) ⟶ (projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subscheme :=
  projectiveConfigurationOrderedGenericComponentPoint
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n c β hβ k

theorem cubicConfigurationOrderedFieldComponentPoint_toBase (k : Fin n) :
    cubicConfigurationOrderedFieldComponentPoint p hp n c β hβ k ≫
      cubicConfigurationGenericFiniteBaseMap p hp n = Spec.map (CommRingCat.ofHom β) := by
  exact projectiveConfigurationOrderedGenericComponentPoint_toBase
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n c β hβ k

theorem cubicConfigurationOrderedFieldComponentPoint_toSurface (k : Fin n) :
    cubicConfigurationOrderedFieldComponentPoint p hp n c β hβ k ≫
      (projectiveConfigurationGenericFiniteSubscheme
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subschemeι ≫
      CategoryTheory.Limits.pullback.fst
        (CategoryTheory.Limits.pullback.snd (hypersurfaceToBase p hp)
          (cubicConfigurationToBase p hp n))
        (cubicConfigurationGenericBaseMap p hp n) ≫
      CategoryTheory.Limits.pullback.fst (hypersurfaceToBase p hp)
        (cubicConfigurationToBase p hp n) =
      (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left := by
  exact projectiveConfigurationOrderedGenericComponentPoint_toAmbientProjective
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n c β hβ k

variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
  cubicConfigurationToBase p hp n)

def cubicConfigurationOrderedFieldCoefficientChangedComponentPoint (k : Fin n) :
    Spec (.of E) ⟶ (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme :=
  cubicConfigurationOrderedFieldComponentPoint p hp n c β hβ k ≫
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha).inv

theorem cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toBase (k : Fin n) :
    cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp n c β hβ a ha k ≫
      cubicConfigurationCoefficientChangedBaseMap p hp n a ha =
        Spec.map (CommRingCat.ofHom β) := by
  unfold cubicConfigurationOrderedFieldCoefficientChangedComponentPoint
  rw [Category.assoc, cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase]
  exact cubicConfigurationOrderedFieldComponentPoint_toBase p hp n c β hβ k

theorem cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toMarkedPoint (k : Fin n) :
    cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp n c β hβ a ha k ≫
      cubicConfigurationCoefficientChangedAmbientMap p hp n a ha =
    ((c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ≫
      hypersurfaceToAmbient p hp := by
  unfold cubicConfigurationOrderedFieldCoefficientChangedComponentPoint
  rw [Category.assoc, cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_ambientMap]
  have hpoint := cubicConfigurationOrderedFieldComponentPoint_toSurface p hp n c β hβ k
  exact congrArg (fun f => f ≫ hypersurfaceToAmbient p hp) hpoint

end PfaffianDescent
