import PfaffianDescent.ActualRelativeDifferentialSectionLeibniz

/- SOURCE ONLY / UNVERIFIED. Additivity of the genuinely sheafified D. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K : Type u} [CommRing K] {X : Scheme.{u}}

lemma actualRelativeDifferentialSection_add
    (g : X ⟶ Spec (.of K)) (U : X.Opens) (a b : Γ(X, U)) :
    actualRelativeDifferentialSection g U (a + b) =
      actualRelativeDifferentialSection g U a + actualRelativeDifferentialSection g U b := by
  let eta := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (schemeRelativeDifferentialsPresheaf g)).app (op U)
  change eta ((schemeRelativeDifferentialsPresheafDerivation g).d (a + b)) = _
  exact (congrArg (fun z => eta z)
    ((schemeRelativeDifferentialsPresheafDerivation g).d.map_add a b)).trans
      (eta.hom.map_add _ _)

lemma actualRelativeDifferentialSection_zero
    (g : X ⟶ Spec (.of K)) (U : X.Opens) :
    actualRelativeDifferentialSection g U 0 = 0 := by
  have h := actualRelativeDifferentialSection_add g U (0 : Γ(X, U)) 0
  have h0 : actualRelativeDifferentialSection g U 0 =
      actualRelativeDifferentialSection g U 0 + actualRelativeDifferentialSection g U 0 := by
    simpa only [zero_add] using h
  have h' : actualRelativeDifferentialSection g U 0 + actualRelativeDifferentialSection g U 0 =
      actualRelativeDifferentialSection g U 0 + 0 := h0.symm.trans (add_zero _).symm
  exact add_left_cancel h'

end PfaffianDescent
