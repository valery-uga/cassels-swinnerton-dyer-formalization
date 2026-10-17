import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import PfaffianDescent.NativeAlgebraSpecFinitePresentation307

/-! Pass from genuine localized R-algebra formal smoothness to the native
Spec stalk map and its actual geometric smooth locus. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem nativeSpec_stalk_formallySmooth_of_localization316
    (q : PrimeSpectrum A) (h : Algebra.FormallySmooth R (Localization.AtPrime q.asIdeal)) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R A))).stalkMap q).hom.FormallySmooth := by
  let p := q.asIdeal.comap (algebraMap R A)
  letI : q.asIdeal.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have hs : Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := R)
      (A := Localization.AtPrime p) (B := Localization.AtPrime q.asIdeal)).mp h
  apply (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R A)) q)).mpr
  change (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)).FormallySmooth
  exact RingHom.formallySmooth_algebraMap.mpr hs

theorem nativeSpec_mem_smoothLocus_of_localization316
    [Algebra.FinitePresentation R A] (q : PrimeSpectrum A)
    (h : Algebra.FormallySmooth R (Localization.AtPrime q.asIdeal)) :
    letI := nativeAlgebraSpecProjection_locallyOfFinitePresentation307 R A
    q ∈ (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := by
  letI := nativeAlgebraSpecProjection_locallyOfFinitePresentation307 R A
  exact (Scheme.Hom.mem_smoothLocus).mpr
    (nativeSpec_stalk_formallySmooth_of_localization316 R A q h)

end PfaffianDescent
end
