import PfaffianDescent.SerreActualGroundFamilyChosenMarkedSeed

/-! The literal chosen marked sections, before field, support, or residual
geometry is attached. This small record retains their exact parameter. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

structure SerreActualChosenMarkedSections
    {S X P Z U : Scheme.{u}}
    (x : X ⟶ S) (pp : P ⟶ S) (zero : Z ⟶ pullback x pp)
    (t : U ⟶ P) where
  δ : Fin 3 → (U ⟶ pullback (zero ≫ pullback.snd x pp) t)
  hδ : ∀ n, δ n ≫ pullback.snd (zero ≫ pullback.snd x pp) t = 𝟙 _

end PfaffianDescent
