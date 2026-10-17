import PfaffianDescent.ActualAffineDifferentialSheafComparisonHom
import PfaffianDescent.BasiswiseBijectiveModuleSheafification

/- SOURCE ONLY / UNVERIFIED. Actual affine differential sheaf comparison
is an Iso; every basis comparison and its bijectivity are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

lemma actualAffineDifferentialPresheafToTilde_basic_bijective (f : R) :
    Function.Bijective
      ((actualAffineDifferentialPresheafToTilde (k := k) (R := R)).app
        (op (PrimeSpectrum.basicOpen f))) := by
  let P := schemeRelativeDifferentialsPresheaf
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let N := affineKaehlerModuleSheaf (k := k) (R := R)
  let Ns : TopCat.Sheaf AddCommGrpCat (Spec (CommRingCat.of R)) :=
    ⟨N.presheaf, N.isSheaf⟩
  change Function.Bijective
    ((TopCat.Sheaf.restrictHomEquivHom P.presheaf Ns
      PrimeSpectrum.isBasis_basic_opens actualAffineDifferentialBasicOpenComparison).app
        (op (PrimeSpectrum.basicOpen f)))
  rw [TopCat.Sheaf.extend_hom_app]
  exact (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) f).bijective

lemma actualAffineDifferentialSheafToTilde_isIso :
    IsIso (actualAffineDifferentialSheafToTilde (k := k) (R := R)) := by
  let X := Spec (CommRingCat.of R)
  let a := actualAffineDifferentialPresheafToTilde (k := k) (R := R)
  letI := moduleSheafification_map_isIso_of_basiswise_bijective a
    (PrimeSpectrum.basicOpen (R := R)) PrimeSpectrum.isBasis_basic_opens
    actualAffineDifferentialPresheafToTilde_basic_bijective
  unfold actualAffineDifferentialSheafToTilde
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The genuine relative differential scheme-module is the ordinary Kähler
module sheaf on an actual affine spectrum, with its actual structure map. -/
def actualAffineDifferentialSheafIso :
    schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≅
        affineKaehlerModuleSheaf (k := k) (R := R) := by
  letI := actualAffineDifferentialSheafToTilde_isIso (k := k) (R := R)
  exact asIso (actualAffineDifferentialSheafToTilde (k := k) (R := R))

end PfaffianDescent
