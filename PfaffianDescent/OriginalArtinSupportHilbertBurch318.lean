import PfaffianDescent.ArtinTensorSemilocalResidue318
import PfaffianDescent.ArtinSemilocalHilbertBurch318

/-!
Construct Hilbert--Burch on the canonical semilocal
neighborhood of the whole original finite-flat family. Its actual residue
map, coefficient kernel, finite maximal spectrum and residual local surface
properties are conclusions of the previous constructions.
-/
noncomputable section
namespace PfaffianDescent
open Matrix LinearMap
open AllCharacteristics.HilbertSurfaceDraft
universe u

def originalArtinSupport318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsArtinianRing S] (J : Ideal A) [Module.Finite S (A ⧸ J)] :
    Finset (MaximalSpectrum A) := by
  letI : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite S _
  exact actualArtinianQuotientSupport001 J

def originalArtinResidueSupport318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S]
    (J : Ideal A) [Module.Finite S (A ⧸ J)] :
    Finset (MaximalSpectrum (artinTensorResidueRing318 S A)) := by
  letI := artinTensorResidueQuotient_artinian318 S A J
  exact actualArtinianQuotientSupport001 (J.map (artinTensorResidueMap318 S A))

abbrev originalArtinSemilocalRing318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsArtinianRing S] (J : Ideal A) [Module.Finite S (A ⧸ J)] :=
  Localization (finiteSupportDenominators001 (originalArtinSupport318 S A J))

/-- The only surface inputs concern the ACTUAL original residual support.
All semilocality, residue comparison and presentation data are constructed. -/
theorem exists_originalArtinSupport_hilbertBurch_resolution318
    (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [Algebra.FiniteType S A]
    [Module.Flat S A] (J : Ideal A)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)] [Nontrivial (A ⧸ J)]
    (hreg : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal))
    (hdim : ∀ Q ∈ originalArtinResidueSupport318 S A J,
      ringKrullDim (Localization.AtPrime Q.asIdeal) = 2) :
    ∃ (m : ℕ) (M : Matrix (Option (Fin m)) (Fin m)
        (originalArtinSemilocalRing318 S A J)),
      Function.Injective M.mulVecLin ∧
      J.map (algebraMap A (originalArtinSemilocalRing318 S A J)) =
        Ideal.span (Set.range (hilbertBurchCofactors318 M)) ∧
      LinearMap.range M.mulVecLin = LinearMap.ker
        (rowFunctional008 (hilbertBurchCofactors318 M)) := by
  letI : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite S _
  let A₀ := artinTensorResidueRing318 S A
  let π := artinTensorResidueMap318 S A
  have hπ : Function.Surjective π := artinTensorResidueMap_surjective318 S A
  have hker : RingHom.ker π = (IsLocalRing.maximalIdeal S).map (algebraMap S A) :=
    artinTensorResidueMap_ker318 S A
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal S) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  obtain ⟨hπnil, hqker⟩ := semilocalResidueMap_coefficient_ker318
    (IsLocalRing.maximalIdeal S) hnil π hπ hker (actualArtinianQuotientSupport001 J)
  letI : IsNoetherianRing A₀ := artinTensorResidueRing_noetherian318 S A
  letI : IsArtinianRing (A₀ ⧸ J.map π) := artinTensorResidueQuotient_artinian318 S A J
  let L := originalArtinSemilocalRing318 S A J
  let L₀ := Localization (finiteSupportDenominators001
    (residueFiniteSupport318 π hπ hπnil (actualArtinianQuotientSupport001 J)))
  let q : L →+* L₀ := semilocalResidueMap318 π hπ hπnil
    (actualArtinianQuotientSupport001 J)
  have hq : Function.Surjective q := semilocalResidueMap_surjective318 π hπ hπnil _
  obtain ⟨hnoeth, hfiniteMax, hsurface⟩ :=
    actualSupportResidueLocalization_surfaceProperties318 π hπ hπnil J hreg hdim
  letI : IsNoetherianRing L₀ := hnoeth
  letI : Finite (MaximalSpectrum L₀) := hfiniteMax
  obtain ⟨hflat, hqflat, hqfinite⟩ := actualSupportLocalization_originalFiniteFlat318 (S := S) J
  letI : Module.Flat S L := hflat
  letI : Module.Flat S (L ⧸ J.map (algebraMap A L)) := hqflat
  letI : Module.Finite S (L ⧸ J.map (algebraMap A L)) := hqfinite
  exact AllCharacteristics.exists_actual_artin_semilocal_hilbertBurch_resolution318
    (S := S) (A := L) (A₀ := L₀) (hFlat := hflat) q hq hqker (fun P hP => (hsurface P hP).1) (fun P hP => (hsurface P hP).2)
    (J.map (algebraMap A L)) (hFlatQ := hqflat) (hFiniteQ := hqfinite)

end PfaffianDescent
end
