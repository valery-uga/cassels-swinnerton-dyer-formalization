import Mathlib.AlgebraicGeometry.Pullbacks

/-! The actual map of surface--parameter products induced by two maps over
the same coefficient change. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u

variable {X Y P Q B C : Scheme.{u}}
variable (x : X ⟶ B) (p : P ⟶ B) (y : Y ⟶ C) (q : Q ⟶ C)
variable (f : X ⟶ Y) (g : P ⟶ Q) (k : B ⟶ C)
variable (hf : f ≫ y = x ≫ k) (hg : g ≫ q = p ≫ k)

def serreActualSurfaceParameterMap : pullback x p ⟶ pullback y q :=
  pullback.lift (pullback.fst x p ≫ f) (pullback.snd x p ≫ g) (by
    calc
      (pullback.fst x p ≫ f) ≫ y = (pullback.fst x p ≫ x) ≫ k :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun a => pullback.fst x p ≫ a) hf).trans
            (Category.assoc _ _ _).symm)
      _ = (pullback.snd x p ≫ p) ≫ k :=
        congrArg (fun a => a ≫ k) pullback.condition
      _ = (pullback.snd x p ≫ g) ≫ q :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun a => pullback.snd x p ≫ a) hg.symm).trans
            (Category.assoc _ _ _).symm))

@[reassoc]
theorem serreActualSurfaceParameterMap_surface :
    serreActualSurfaceParameterMap x p y q f g k hf hg ≫ pullback.fst y q =
      pullback.fst x p ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem serreActualSurfaceParameterMap_parameters :
    serreActualSurfaceParameterMap x p y q f g k hf hg ≫ pullback.snd y q =
      pullback.snd x p ≫ g :=
  pullback.lift_snd _ _ _

end PfaffianDescent
