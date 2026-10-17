import PfaffianDescent.SerreActualConfigurationPlaneData

/-! The native actual rank chart constructs the literal plane incidence
with its actual open configuration projection. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualConfigurationPlaneData_of_rank_chart
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (hdata : SerreActualConfigurationRankChart base e C h9) :
    SerreActualConfigurationPlaneData base e C h9 := by
  obtain ⟨A, a, chart, markedA, hAffine, hOpen, hInt, hmarked, m, hm⟩ := hdata
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
  exact ⟨A, a, chart, markedA, hmarkedBase, hAffine, hOpen, hInt, hmarked, m, hm, hplane⟩

end PfaffianDescent
