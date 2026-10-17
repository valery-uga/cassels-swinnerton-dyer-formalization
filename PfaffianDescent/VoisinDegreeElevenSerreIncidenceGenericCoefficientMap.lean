import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGeometricFunctionField
import Mathlib.AlgebraicGeometry.Stalk

/-! # The actual generic coefficient map is the structural germ map -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGenericCoefficientMap_spec
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (base : X ⟶ Spec (.of K)) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    Spec.map (CommRingCat.ofHom
      ((X.germToFunctionField ⊤).hom.comp (schemeOpenBaseRingHom base ⊤))) =
      X.fromSpecStalk (genericPoint X) ≫ base := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  calc
    _ = Spec.map (CommRingCat.ofHom (affineFunctionHom base) ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial) := by
      congr 1
      ext k
      change X.germToFunctionField ⊤ (schemeOpenBaseRingHom base ⊤ k) =
        X.germToFunctionField ⊤ (affineFunctionHom base k)
      rw [schemeOpenBaseRingHom_top_apply]
    _ = _ := by
      rw [Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc]
      exact congrArg (fun t => X.fromSpecStalk (genericPoint X) ≫ t)
        (from_affineFunctionHom base)

theorem serreIncidenceGenericCoefficientMap_eq
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (base : X ⟶ Spec (.of K)) (a : CommRingCat.of K ⟶ X.functionField)
    (ha : Spec.map a = X.fromSpecStalk (genericPoint X) ≫ base) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    a.hom = (X.germToFunctionField ⊤).hom.comp (schemeOpenBaseRingHom base ⊤) := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  exact ha.trans (serreIncidenceGenericCoefficientMap_spec base).symm

end PfaffianDescent
