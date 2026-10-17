import PfaffianDescent.ActualAffineDifferentialSheafComparisonHom

/- SOURCE ONLY / UNVERIFIED. The genuinely glued affine comparison
retains its canonical map on every actual principal chart. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

lemma actualAffineDifferentialPresheafToTilde_basic_apply
    (f : R) (x : (schemeRelativeDifferentialsPresheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj
        (op (PrimeSpectrum.basicOpen f))) :
    ((actualAffineDifferentialPresheafToTilde (k := k) (R := R)).app
      (op (PrimeSpectrum.basicOpen f))) x =
        actualAffineDifferentialPresheafBasicOpenEquiv (k := k) f x := by
  let P := schemeRelativeDifferentialsPresheaf (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let N := affineKaehlerModuleSheaf (k := k) (R := R)
  let Ns : TopCat.Sheaf AddCommGrpCat (Spec (CommRingCat.of R)) := ⟨N.presheaf, N.isSheaf⟩
  change (TopCat.Sheaf.restrictHomEquivHom P.presheaf Ns
    PrimeSpectrum.isBasis_basic_opens actualAffineDifferentialBasicOpenComparison).app
      (op (PrimeSpectrum.basicOpen f)) x = _
  rw [TopCat.Sheaf.extend_hom_app]
  rfl

end PfaffianDescent
