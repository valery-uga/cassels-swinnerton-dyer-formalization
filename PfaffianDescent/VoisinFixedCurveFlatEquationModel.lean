import PfaffianDescent.VoisinFixedCurveEquationSpread
import PfaffianDescent.VoisinGenericGradeBaseChange

/-!
# A flat fixed-curve model carrying its generic equations

A prime divisor on the generic cubic first spreads as a homogeneous ideal.
Generic freeness then gives a flat proper projective curve family on one
principal open of the configuration base.  The equations of the generic
curve can be cleared over the *same* open and placed in the contracted ideal
of that family, so their vanishing is compatible with field-valued points.

This produces a relative curve, not a ground-field divisor class.  To use the
fixed-linear-system avoidance endpoint, one still must identify the generic
divisor class with a line bundle on the original ground-field cubic and
compare its section and point evaluations after base change.
-/

namespace PfaffianDescent

open MvPolynomial CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- A prime fixed curve on the generic cubic has a flat proper projective
model on a principal open, with the same generic fibre and Hilbert function.
Any finite same-degree list of its equations is represented in that model by
homogeneous equations after multiplication by one nonzero denominator. -/
theorem exists_flat_prime_fixedCurve_model_with_equations
    {A F : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal)
    {k n : ℕ} (q : Fin k → MvPolynomial (Fin 4) F)
    (hq : ∀ i, q i ∈ C.toIdeal)
    (hdegree : ∀ i, (q i).IsHomogeneous n) :
    ∃ e : A, e ≠ 0 ∧
      ∃ φ : Localization.Away e →+* F,
        Function.Injective φ ∧
        (∀ a : A, φ (algebraMap A (Localization.Away e) a) =
          algebraMap A F a) ∧
        ∃ J : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) (Localization.Away e)),
          J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal ∧
          J.toIdeal.IsPrime ∧
          Module.Flat (Localization.Away e) (CoordinateRing J) ∧
          (∀ d : ℕ, ∀ z : PrimeSpectrum (Localization.Away e),
            Module.rankAtStalk (grading J d) z =
              Module.finrank F (grading C d)) ∧
          AlgebraicGeometry.Flat (toBase J) ∧
          AlgebraicGeometry.IsProper (toBase J) ∧
          AlgebraicGeometry.LocallyOfFinitePresentation (toBase J) ∧
          (∃ i : scheme J ⟶
              hypersurface (MvPolynomial.map
                (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))),
            AlgebraicGeometry.IsClosedImmersion i ∧
            i ≫ hypersurfaceToBase
                (MvPolynomial.map (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))) = toBase J) ∧
          Nonempty (scheme C ≅
            pullback (toBase J)
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) ∧
          ∃ δ : Localization.Away e, δ ≠ 0 ∧
            ∀ j : Fin k,
              ∃ g : MvPolynomial (Fin 4) (Localization.Away e),
                g ∈ J.toIdeal ∧ g.IsHomogeneous n ∧
                  MvPolynomial.map φ g = MvPolynomial.C (φ δ) * q j := by
  classical
  obtain ⟨e, he, φ, hφ, hcomp, J, hJ, hprimeJ, hflat,
    _hpieces, _hprojective, hHilbert, _haway, hproj, hproper,
    hlfp, i, hi, hibase, hgeneric⟩ :=
    exists_flat_primeProjectiveCurve_genericFiber_hilbert_model_in_cubic
      m p hp C hprime hpC
  letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
  letI : Algebra (Localization.Away e) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away e) F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI : IsFractionRing (Localization.Away e) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers e) (Localization.Away e) F
  have hcontract : ∀ g : MvPolynomial (Fin 4) (Localization.Away e),
      g ∈ J.toIdeal ↔ MvPolynomial.map (algebraMap (Localization.Away e) F) g ∈
        C.toIdeal := by
    intro g
    rw [hJ]
    rfl
  have hqfin : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      q j ∈ C.toIdeal := by
    intro j _
    exact hq j
  obtain ⟨δ, hδ, hclear⟩ :=
    exists_finite_homogeneousModel_equations_common_denominator
      (A := Localization.Away e) (F := F) (ι := Fin k)
      C J hcontract (Finset.univ : Finset (Fin k)) q hqfin
  refine ⟨e, he, φ, hφ, hcomp, J, hJ, hprimeJ, hflat,
    hHilbert, hproj, hproper, hlfp, ⟨i, hi, hibase⟩,
    hgeneric, δ, hδ, ?_⟩
  intro j
  obtain ⟨g, hgJ, hclearG⟩ := hclear j (Finset.mem_univ j)
  refine ⟨g, hgJ, ?_, ?_⟩
  · exact polynomial_denominator_clear_isHomogeneous
      (q j) g δ n (hdegree j) hclearG
  · exact hclearG

end PfaffianDescent
