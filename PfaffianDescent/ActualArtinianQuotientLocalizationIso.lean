import PfaffianDescent.ActualArtinianQuotientSupport
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
Finite-support localization
preserves the whole quotient algebra, hence also its finite-flat rank.
The unit property and canonical quotient equivalence are derived here;
they are not support-preservation assumptions.
-/

noncomputable section
namespace PfaffianDescent
universe u
set_option autoImplicit false

theorem actualArtinianQuotientSupport_denominator_isUnit001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (r : R) (hr : r ∈ finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) :
    IsUnit (Ideal.Quotient.mk J r) := by
  apply Ideal.span_singleton_eq_top.mp
  by_contra hproper
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({Ideal.Quotient.mk J r} : Set (R ⧸ J))) hproper
  letI : Q.IsMaximal := hQ
  exact actualArtinianQuotientSupport_denominator_notMem001 J r hr
    (⟨Q, inferInstance⟩ : PrimeSpectrum (R ⧸ J))
    (hle (Ideal.subset_span (Set.mem_singleton _)))

/-- Localizing away from ANY subset of the finite-support denominators
gives the original quotient algebra itself, with its nilpotents and base
action.  The equivalence is the canonical quotient algebra map. -/
def actualArtinianQuotientLocalizationIso001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (S : Submonoid R) (hS : S ≤ finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) :
    (R ⧸ J) ≃ₐ[R] (Localization S ⧸ J.map (algebraMap R (Localization S))) := by
  let T := Algebra.algebraMapSubmonoid (R ⧸ J) S
  have hT : T ≤ IsUnit.submonoid (R ⧸ J) := by
    rintro x ⟨r, hr, rfl⟩
    exact actualArtinianQuotientSupport_denominator_isUnit001 J r (hS hr)
  exact (IsLocalization.atUnits (R ⧸ J) T hT).restrictScalars R

/-- In particular the actual semilocal quotient is the original finite
family algebra, rather than its reduction or a localization of its
individual components. -/
def actualArtinianQuotientSemilocalIso001
    {R : Type u} [CommRing R] (J : Ideal R) [IsArtinianRing (R ⧸ J)] :
    (R ⧸ J) ≃ₐ[R]
      (Localization (finiteSupportDenominators001 (actualArtinianQuotientSupport001 J)) ⧸
        J.map (algebraMap R
          (Localization (finiteSupportDenominators001 (actualArtinianQuotientSupport001 J))))) :=
  actualArtinianQuotientLocalizationIso001 J _ le_rfl

end PfaffianDescent
end
