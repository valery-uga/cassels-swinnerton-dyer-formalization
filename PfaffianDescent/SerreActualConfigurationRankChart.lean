import PfaffianDescent.SerreActualEvaluationConfiguration
import PfaffianDescent.SerreActualEvaluationAffineChart
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMinorChart

/-! Output data for an actual configuration chart with a native unit
six-column minor. This predicate contains the actual marked morphisms. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def SerreActualConfigurationRankChart
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9) : Prop :=
    ∃ (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
      (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme),
      IsAffine A ∧ IsOpenImmersion a ∧ IsIntegral A ∧
      (∀ i, markedA i ≫ (C.U (chart i)).ι =
        (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 i).left) ∧
      ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
        IsUnit (Matrix.det (Matrix.submatrix
          (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m))

theorem serreActualConfigurationRankChart_of_witnesses
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
    (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hAffine : IsAffine A) (hOpen : IsOpenImmersion a) (hInt : IsIntegral A)
    (hmarked : ∀ i, markedA i ≫ (C.U (chart i)).ι =
      (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
        (orderedFamilyCoordinate base 3 i).left)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m))) :
    SerreActualConfigurationRankChart base e C h9 :=
  ⟨A, a, chart, markedA, hAffine, hOpen, hInt, hmarked, m, hm⟩

end PfaffianDescent
