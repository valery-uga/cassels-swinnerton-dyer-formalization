import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalSectionsFieldFrame

/-! # Native finite dimensionality and rank of the field-extended section space -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGlobalSectionsField_finiteDimensional
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))] :
    FiniteDimensional L (SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback (schemeFieldBaseChangeToOriginal (L := L) base)).obj
        (show X.Modules from e.E))) :=
  Module.Finite.of_basis (serreIncidenceGlobalSectionsFieldBasis (L := L) base e C)

theorem serreIncidenceGlobalSectionsField_finrank
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))] :
    Module.finrank L (SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback (schemeFieldBaseChangeToOriginal (L := L) base)).obj
        (show X.Modules from e.E))) =
      Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) := by
  rw [Module.finrank_eq_card_basis (serreIncidenceGlobalSectionsFieldBasis (L := L) base e C),
    Fintype.card_fin]

end PfaffianDescent
