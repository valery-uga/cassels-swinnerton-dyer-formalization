import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
set_option autoImplicit false

/-- Actual Noether normalization and an injective original-K field map
derive ring dimension≤1. No normalization/dimension certificate is supplied. -/
theorem finiteTypeRing_injective_field_trdeg_le_one_dimensionLEOne001
    {K R E : Type u} [Field K] [CommRing R] [Field E]
    [Algebra K R] [Algebra K E] [Algebra.FiniteType K R]
    (i : R →ₐ[K] E) (hi : Function.Injective i)
    (hTrdeg : Algebra.trdeg K E ≤ 1) : Ring.DimensionLEOne R := by
  letI : IsDomain R := Function.Injective.isDomain i hi
  obtain ⟨s, g, hg, hIntegral⟩ := exists_integral_inj_algHom_of_fg K R
  have hEmbedding : Function.Injective (i.comp g) := hi.comp hg
  have hCard := (_root_.trdeg_le_of_injective (i.comp g) hEmbedding).trans hTrdeg
  have hsCard : (s : Cardinal.{u}) ≤ 1 := by
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
      Cardinal.lift_natCast] using hCard
  have hs : s ≤ 1 := by exact_mod_cast hsCard
  let P := MvPolynomial (Fin s) K
  have hPdim : ringKrullDim P ≤ 1 := by
    dsimp only [P]
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
    simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]
    exact_mod_cast hs
  letI : Ring.KrullDimLE 1 P := Ring.krullDimLE_iff.mpr hPdim
  letI : Ring.DimensionLEOne P :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  letI : Algebra P R := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral P R := algebraMap_isIntegral_iff.mp hIntegral
  exact Ring.DimensionLEOne.of_isIntegral P R

/-- The actual section-to-stalk localization propagates the derived affine
ring bound to the SAME scheme stalks. No new scalar action is installed. -/
theorem integralScheme_affineOpen_dimensionLEOne_stalk001
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Ring.DimensionLEOne Γ(X, U)] (x : U) :
    Ring.DimensionLEOne (X.presheaf.stalk x.1) := by
  let A := Γ(X, U)
  let R := X.presheaf.stalk x.1
  let J := (hU.primeIdealOf x).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf x).isPrime
  letI : Algebra A R := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime R J := hU.isLocalization_stalk x
  exact Ring.DimensionLEOne.localization R J.primeCompl_le_nonZeroDivisors

end PfaffianDescent.Coray
