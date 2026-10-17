import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationTensor

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {A K : Type u} [CommRing A] [Field K]
set_option backward.isDefEq.respectTransparency false

/-- The actual affine ideal-section point-evaluation map, formed from the literal
sheaf pullback unit and actual Gamma pushforward comparison. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap
    (g : A →+* K) (H : Ideal A) :
    ModuleCat.of A H ⟶
      (ModuleCat.restrictScalars g).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
            ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A H)))) :=
  (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app (ModuleCat.of A H) ≫
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom g))).unit.app
        ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A H))) ≫
    (affineGammaPushforwardNatIso (CommRingCat.ofHom g)).hom.app _

/-- Literal actual point evaluation is 1 tensor h in the native fibre coordinate. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap_apply
    (g : A →+* K) (H : Ideal A) (a : H) :
    letI : Algebra A K := g.toAlgebra
    cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv g H
      ((cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap g H).hom a) =
    1 ⊗ₜ[A] a := by
  letI : Algebra A K := g.toAlgebra
  have h := congrArg (fun f => f.hom a)
    (cubicClosedPointSerreSurfaceJetCotangent_affineEvaluation_tensor_unit
      (CommRingCat.ofHom g) (ModuleCat.of A H))
  exact h

end PfaffianDescent
