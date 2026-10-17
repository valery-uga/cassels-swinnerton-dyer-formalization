import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- An equality to the original whole open makes its original inclusion an isomorphism. -/
lemma nativeOpenInclusion_isIso_of_eq_top300
    {X : Scheme.{u}} (U : X.Opens) (hU : U = ⊤) :
    IsIso (Scheme.Opens.ι (X := X) U) := by
  subst U
  change IsIso X.topIso.hom
  infer_instance

end PfaffianDescent
