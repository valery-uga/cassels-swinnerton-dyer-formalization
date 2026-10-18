import Mathlib.RingTheory.Spectrum.Prime.Topology
import PfaffianDescent.FiniteSupportSemilocalBasisSpreading
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Maps

/-!
Construct the finite support
from the actual whole Artinian quotient, and prove that every denominator
used for semilocal matrix assembly avoids the entire subscheme.
-/

noncomputable section
namespace PfaffianDescent
universe u
set_option autoImplicit false

def quotientMaximalSupportPoint001
    {R : Type u} [CommRing R] (J : Ideal R) (q : MaximalSpectrum (R ⧸ J)) :
    MaximalSpectrum R :=
  ⟨q.asIdeal.comap (Ideal.Quotient.mk J),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩

/-- The finite set records ALL points of the actual Artinian quotient,
including nonreduced local factors; no reduced-support substitute occurs. -/
def actualArtinianQuotientSupport001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)] :
    Finset (MaximalSpectrum R) := by
  classical
  letI : Fintype (MaximalSpectrum (R ⧸ J)) := Fintype.ofFinite _
  exact Finset.univ.image (quotientMaximalSupportPoint001 J)

theorem actualArtinianQuotientSupport_nonempty001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    [Nontrivial (R ⧸ J)] : (actualArtinianQuotientSupport001 J).Nonempty := by
  classical
  letI : Fintype (MaximalSpectrum (R ⧸ J)) := Fintype.ofFinite _
  let q : MaximalSpectrum (R ⧸ J) := Classical.choice inferInstance
  refine ⟨quotientMaximalSupportPoint001 J q, ?_⟩
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩

/-- A semilocal denominator avoids EVERY point of the whole quotient.
Artinianity supplies maximality of each prime point; the quotient itself
is retained, with all its nilpotents. -/
theorem actualArtinianQuotientSupport_denominator_notMem001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (r : R) (hr : r ∈ finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) (z : PrimeSpectrum (R ⧸ J)) :
    Ideal.Quotient.mk J r ∉ z.asIdeal := by
  classical
  letI : Fintype (MaximalSpectrum (R ⧸ J)) := Fintype.ofFinite _
  letI : z.asIdeal.IsPrime := z.isPrime
  let q : MaximalSpectrum (R ⧸ J) := ⟨z.asIdeal, inferInstance⟩
  have hq : quotientMaximalSupportPoint001 J q ∈
      actualArtinianQuotientSupport001 J :=
    Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  exact hr (quotientMaximalSupportPoint001 J q) hq

/-- Consequently the actual quotient's ENTIRE affine source lies in the
principal open selected by matrix spreading. -/
theorem actualArtinianQuotientSupport_range_basicOpen001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (r : R) (hr : r ∈ finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) ⊆ PrimeSpectrum.basicOpen r := by
  rintro _ ⟨z, rfl⟩
  exact actualArtinianQuotientSupport_denominator_notMem001 J r hr z

end PfaffianDescent
end
