import PfaffianDescent.VoisinDegreeElevenSerreIncidenceTrivializingChart
import PfaffianDescent.SerreExtensionFoundation

/-! # The nine-section relative matrix for an actual rank-two Serre bundle -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The native Serre affine cover supplies the general finite-free cover,
with its literal rank-two trivializations. -/
def serreIncidenceRankTwoAffineCover
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SchemeModuleFiniteFreeAffineCover (show X.Modules from e.E) (ULift.{u} (Fin 2)) where
  ι := C.ι
  U := C.U
  covers := C.covers
  affine := C.affine
  trivialization := C.trivialization

/-- An actual basis of the nine-dimensional global-section space. -/
def serreIncidenceNineGlobalSections
    {F : Type u} [Field F] {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X M)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9) :
    Fin 9 → e.E.sections := fun i =>
  e.E.unitHomEquiv (Module.finBasisOfFinrankEq F
    (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) h9 i)

/-- The native six-by-nine matrix on the common trivializing configuration
open, built internally from the actual Serre cover and an actual section basis. -/
def serreIncidenceNativeRelativeEvaluationMatrix
    {F : Type u} [Field F] {X B : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (marked : Fin 3 → (B ⟶ X)) (chart : Fin 3 → C.ι) :
    Matrix (Fin 3 × ULift.{u} (Fin 2)) (Fin 9)
      Γ((serreThreePointTrivializingOpen
        (serreIncidenceRankTwoAffineCover e C) marked chart).toScheme, ⊤) :=
  serreThreePointRelativeEvaluationMatrix
    (serreIncidenceRankTwoAffineCover e C) chart
    (serreThreePointTrivializingMarked
      (serreIncidenceRankTwoAffineCover e C) marked chart)
    (serreIncidenceNineGlobalSections base e h9)

end PfaffianDescent
