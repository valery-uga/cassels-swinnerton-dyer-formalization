import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeProductCoefficients
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceBundleCoordinates

/-! # Exact identification of the canonical and rank-nine native matrices -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGlobalBasisEvaluationMatrix_eq_native
    {F : Type u} [Field F] {X A : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (r : Fin 3 × ULift.{u} (Fin 2)) (k : Fin 9) :
    serreIncidenceGlobalBasisEvaluationMatrix base (show X.Modules from e.E)
      (serreIncidenceRankTwoAffineCover e C) chart markedA r ((finCongr h9).symm k) =
      serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA r k := by
  unfold serreIncidenceNativeAffineEvaluationMatrix serreThreePointRelativeEvaluationMatrix
  rw [serreIncidenceNineGlobalSections_eq_finBasis]
  rfl

end PfaffianDescent
