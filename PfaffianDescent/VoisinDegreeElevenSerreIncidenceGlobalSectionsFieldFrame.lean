import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix
import PfaffianDescent.VoisinFiniteFreeAffineCoverFromLocal

/-! # Native global section frame of a Serre bundle after field extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGlobalSectionsFieldBaseChange_bijective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))] :
    Function.Bijective (schemeModuleGlobalSectionsFieldBaseChangeLinearMap
      (L := L) base (show X.Modules from e.E)) := by
  apply globalSectionsFieldBaseChangeLinearMap_bijective_of_localTrivializations
    base (show X.Modules from e.E) (ULift.{u} (Fin 2))
  intro x
  have hx : x ∈ (⨆ i, C.U i) := by rw [C.covers]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨C.U i, hi, C.affine i, ⟨C.trivialization i⟩⟩

def serreIncidenceGlobalSectionsFieldFrame
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))] :=
  schemeModuleGlobalSectionsFieldBaseChangeLinearEquiv (L := L) base
    (show X.Modules from e.E) (serreIncidenceGlobalSectionsFieldBaseChange_bijective base e C)

theorem serreIncidenceGlobalSectionsFieldFrame_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (v : L ⊗[K] SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) :
    serreIncidenceGlobalSectionsFieldFrame (L := L) base e C v =
      schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base
        (show X.Modules from e.E) v := rfl

def serreIncidenceGlobalSectionsFieldBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))] :=
  ((Module.finBasis K (SchemeModuleGlobalSectionsOver base
    (show X.Modules from e.E))).baseChange L).map
      (serreIncidenceGlobalSectionsFieldFrame (L := L) base e C)

end PfaffianDescent
