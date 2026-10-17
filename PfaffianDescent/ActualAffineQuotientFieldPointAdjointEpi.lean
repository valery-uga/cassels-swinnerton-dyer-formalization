import PfaffianDescent.ActualAffineQuotientPointAdjointGamma
import PfaffianDescent.ActualAffineSheafEpiFromGamma

/- SOURCE ONLY / UNVERIFIED. ACTUAL sheaf adjoint Epi on an affine chart.
All target counit/point map/Gamma surjectivity facts are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem actualAffineQuotientFieldPointLineAdjoint_epi
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hquot : Function.Surjective rho) (M : ModuleCat R)
    (ell : (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
        ((tilde.functor (CommRingCat.of R)).obj M)) →ₗ[L] L)
    (hell : Function.Surjective ell) :
    Epi (actualFieldPointLineAdjoint (Spec.map (CommRingCat.ofHom rho))
      ((tilde.functor (CommRingCat.of R)).obj M) ell) := by
  let phi := CommRingCat.ofHom rho
  let q := Spec.map phi
  let O := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  letI : IsIso ((Scheme.Modules.pushforward q).obj O).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward phi O
  exact actualAffineSheafMap_epi_of_gamma_surjective _
    (actualAffineQuotientFieldPointLineAdjoint_gamma_surjective rho hquot M ell hell)

end PfaffianDescent
