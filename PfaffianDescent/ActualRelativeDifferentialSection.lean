import PfaffianDescent.SchemeRelativeDifferentialsSheaf

/- SOURCE ONLY / UNVERIFIED. Actual universal differential sections in
the genuinely constructed Ω sheaf, retaining the original ring section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [CommRing k] {X : Scheme.{u}}

def actualRelativeDifferentialSection
    (g : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (r : Γ(X, U)) :
    (schemeRelativeDifferentials g).val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (schemeRelativeDifferentialsPresheaf g)).app (op U)
      ((schemeRelativeDifferentialsPresheafDerivation g).d r)

lemma actualRelativeDifferentialSection_restrict
    (g : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (hVU : V ≤ U) (r : Γ(X, U)) :
    (schemeRelativeDifferentials g).val.map (homOfLE hVU).op
      (actualRelativeDifferentialSection g U r) =
        actualRelativeDifferentialSection g V (X.presheaf.map (homOfLE hVU).op r) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (schemeRelativeDifferentialsPresheaf g)
  have h := PresheafOfModules.naturality_apply η (homOfLE hVU).op
    ((schemeRelativeDifferentialsPresheafDerivation g).d r)
  have h' : η.app (op V)
      ((schemeRelativeDifferentialsPresheaf g).map (homOfLE hVU).op
        ((schemeRelativeDifferentialsPresheafDerivation g).d r)) =
      (schemeRelativeDifferentials g).val.map (homOfLE hVU).op
        (η.app (op U) ((schemeRelativeDifferentialsPresheafDerivation g).d r)) := h
  exact h'.symm.trans (congrArg (fun t => η.app (op V) t)
    ((schemeRelativeDifferentialsPresheafDerivation g).d_map (homOfLE hVU).op r).symm)

end PfaffianDescent
