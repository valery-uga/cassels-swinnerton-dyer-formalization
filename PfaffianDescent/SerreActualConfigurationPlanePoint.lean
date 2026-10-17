import PfaffianDescent.SerreActualConfigurationRankPoint
import PfaffianDescent.SerreActualConfigurationPlaneFactory

/-! The actual plane incidence retains its original rank witness point. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def SerreActualConfigurationPlaneDataAtPoint
    {F E : Type u} [Field F] [Field E] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (r : Fin 3 → (Spec (.of E) ⟶ X)) : Prop :=
    ∃ (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
      (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
      (cA : Spec (.of E) ⟶ A)
      (hmarked : ∀ i, (markedA i ≫ (C.U (chart i)).ι) ≫ base =
        a ≫ (orderedFamilyConfigurationOver base 3).hom)
      (hAffine : IsAffine A),
      IsOpenImmersion a ∧ IsIntegral A ∧
      (∀ i, markedA i ≫ (C.U (chart i)).ι =
        (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 i).left) ∧
      (∀ i, (cA ≫ markedA i) ≫ (C.U (chart i)).ι = r i) ∧
      ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
        IsUnit (Matrix.det (Matrix.submatrix
          (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m)) ∧
        letI := hAffine
        SerreActualConfigurationPlaneAtChart base e C
          (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart markedA hmarked

theorem serreActualConfigurationPlaneDataAtPoint_of_rank_chart
    {F E : Type u} [Field F] [Field E] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hdata : SerreActualConfigurationRankChartAtPoint base e C h9 r) :
    SerreActualConfigurationPlaneDataAtPoint base e C h9 r := by
  obtain ⟨A, a, chart, markedA, cA, hAffine, hOpen, hInt, hmarked, hpoints, m, hm⟩ := hdata
  letI : IsAffine A := hAffine
  have hmarkedBase : ∀ i, (markedA i ≫ (C.U (chart i)).ι) ≫ base =
      a ≫ (orderedFamilyConfigurationOver base 3).hom := by
    intro i
    calc
      (markedA i ≫ (C.U (chart i)).ι) ≫ base =
          ((a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
            (orderedFamilyCoordinate base 3 i).left) ≫ base :=
        congrArg (fun f => f ≫ base) (hmarked i)
      _ = (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          ((orderedFamilyCoordinate base 3 i).left ≫ base) := Category.assoc _ _ _
      _ = (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyPowerOver base 3).hom :=
        congrArg (fun f => (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫ f)
          (orderedFamilyCoordinate base 3 i).w
      _ = a ≫ (orderedFamilyConfigurationOver base 3).hom := Category.assoc _ _ _
  have hplane : SerreActualConfigurationPlaneAtChart base e C
      (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart markedA hmarkedBase :=
    serreIncidenceNativeSerre_exists_plane base e C h9
      (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart markedA hmarkedBase m hm
  exact ⟨A, a, chart, markedA, cA, hmarkedBase, hAffine, hOpen, hInt,
    hmarked, hpoints, m, hm, hplane⟩

end PfaffianDescent
