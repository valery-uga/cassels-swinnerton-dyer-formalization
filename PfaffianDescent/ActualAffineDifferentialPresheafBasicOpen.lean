import PfaffianDescent.AffineKaehlerBasicOpenComparison
import PfaffianDescent.AffineSchemeBaseScalarPresheafFormula

/- SOURCE ONLY / UNVERIFIED. This identifies objects of the GENUINE
scheme differential presheaf, not an independently chosen algebra presheaf. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- On every actual principal open, the actual scheme differential PRESHEAF
has its canonical localization comparison to the affine Kähler module SHEAF.
Its naturality and global sheafification comparison are separate obligations. -/
def actualAffineDifferentialPresheafBasicOpenEquiv (f : R) :
    (schemeRelativeDifferentialsPresheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj
        (op (PrimeSpectrum.basicOpen f)) ≃ₗ[
          Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)]
      Γ(affineKaehlerModuleSheaf (k := k) (R := R), PrimeSpectrum.basicOpen f) := by
  letI : Algebra R Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f) :=
    inferInstanceAs
      (Algebra R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))))
  change CommRingCat.KaehlerDifferential
    ((schemeBaseScalarPresheafMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app
        (op (PrimeSpectrum.basicOpen f))) ≃ₗ[_] _
  let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
  let h := affineSchemeBaseScalarPresheafMap_app (k := k) (R := R)
    (PrimeSpectrum.basicOpen f)
  let e := eqToIso (congrArg
    (fun s : CommRingCat.of k ⟶ CommRingCat.of A => CommRingCat.KaehlerDifferential s) h)
  exact e.toLinearEquiv.trans (affineKaehlerBasicOpenEquiv (k := k) f)

end PfaffianDescent
