import PfaffianDescent.ActualRelativeDifferentialSection

/- SOURCE ONLY / UNVERIFIED. Leibniz in the GENUINELY sheafified relative
Omega, for actual sections on any open of the SAME scheme. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [CommRing K] {X : Scheme.{u}}

lemma actualRelativeDifferentialSection_leibniz
    (g : X ⟶ Spec (.of K)) (U : X.Opens) (a r : Γ(X, U)) :
    letI : Module Γ(X, U) ((schemeRelativeDifferentials g).val.obj (op U)) :=
      ((schemeRelativeDifferentials g).val.obj (op U)).isModule
    actualRelativeDifferentialSection g U (a * r) =
      a • actualRelativeDifferentialSection g U r +
        r • actualRelativeDifferentialSection g U a := by
  letI : Module Γ(X, U) ((schemeRelativeDifferentials g).val.obj (op U)) :=
    ((schemeRelativeDifferentials g).val.obj (op U)).isModule
  let eta := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (schemeRelativeDifferentialsPresheaf g)).app (op U)
  change eta ((schemeRelativeDifferentialsPresheafDerivation g).d (a * r)) = _
  rw [(schemeRelativeDifferentialsPresheafDerivation g).d_mul, map_add]
  congr 1
  · exact eta.hom.map_smul a ((schemeRelativeDifferentialsPresheafDerivation g).d r)
  · exact eta.hom.map_smul r ((schemeRelativeDifferentialsPresheafDerivation g).d a)

end PfaffianDescent
