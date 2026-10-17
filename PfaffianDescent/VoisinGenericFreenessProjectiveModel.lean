import PfaffianDescent.VoisinGenericFreenessContraction
import PfaffianDescent.VoisinHomogeneousIdealGenericSpreading
import AllCharacteristics.ProjectiveUnitCoefficientFlatness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# A flat coordinate-ring model inside the cubic family

The contracted generic ideal gives a projective model with the intended
generic fibre. For a prime generic curve, its defining ideal remains prime.
The coordinate algebra and projective morphism are flat on a principal open.
-/

namespace PfaffianDescent

open MvPolynomial
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

/-- Each homogeneous piece of a polynomial-quotient coordinate ring is a
finite module over the coefficient ring. -/
theorem coordinateRing_homogeneousPiece_finite
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (n : ℕ) : Module.Finite R (grading J n) := by
  let H := homogeneousSubmodule (Fin 4) R n
  letI : Module.Finite R H :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 4) R n)
  let q : H →ₗ[R] grading J n :=
    ((Ideal.Quotient.mkₐ R J.toIdeal).toLinearMap.comp H.subtype).codRestrict
      (grading J n) (by
        intro x
        change (Ideal.Quotient.mkₐ R J.toIdeal).toLinearMap x.1 ∈ grading J n
        exact ⟨x.1, x.2, rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨p, hp, hpy⟩ := y.2
    refine ⟨⟨p, hp⟩, ?_⟩
    exact Subtype.ext hpy
  exact Module.Finite.of_surjective q hq

/-- Each homogeneous piece of a flat coordinate ring is flat over the
coefficient ring, since the grading makes it a direct summand. -/
theorem coordinateRing_homogeneousPiece_flat
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (n : ℕ) :
    Module.Flat R (grading J n) := by
  letI := gradedRing J
  let r : CoordinateRing J →ₗ[R] grading J n :=
    (DFinsupp.lapply n).comp (DirectSum.decomposeLinearEquiv (grading J)).toLinearMap
  apply Module.Flat.of_retract (grading J n).subtype r
  apply LinearMap.ext
  intro x
  change (DirectSum.decomposeLinearEquiv (grading J) (x : CoordinateRing J)) n = x
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  simp

/-- Over a Noetherian coefficient ring, a flat homogeneous piece is finite
projective. -/
theorem coordinateRing_homogeneousPiece_projective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (n : ℕ) :
    Module.Projective R (grading J n) := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.FinitePresentation R (grading J n) :=
    Module.finitePresentation_of_finite R (grading J n)
  letI : Module.Flat R (grading J n) :=
    coordinateRing_homogeneousPiece_flat J n
  exact Module.Flat.projective_of_finitePresentation

/-- In a flat projective model over an integral base, the rank of every
homogeneous coordinate piece is constant across the base. -/
theorem coordinateRing_homogeneousPiece_rankAtStalk_constant
    {R : Type u} [CommRing R] [IsDomain R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (n : ℕ)
    (p q : PrimeSpectrum R) :
    Module.rankAtStalk (grading J n) p =
      Module.rankAtStalk (grading J n) q := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.Flat R (grading J n) :=
    coordinateRing_homogeneousPiece_flat J n
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  calc
    Module.rankAtStalk (grading J n) p =
        Module.rankAtStalk (grading J n) η :=
      (Module.rankAtStalk_eq_of_le_of_finite_of_flat (grading J n)
        (show η ≤ p from bot_le)).symm
    _ = Module.rankAtStalk (grading J n) q :=
      Module.rankAtStalk_eq_of_le_of_finite_of_flat (grading J n)
        (show η ≤ q from bot_le)

/-- The common stalk rank of a homogeneous piece equals its dimension after
extension to the fraction field. -/
theorem coordinateRing_homogeneousPiece_rank_eq_genericFinrank
    {R F : Type u} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (n : ℕ)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (grading J n) p =
      Module.finrank F (F ⊗[R] grading J n) := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.Flat R (grading J n) :=
    coordinateRing_homogeneousPiece_flat J n
  let ηR : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let ηF : PrimeSpectrum F := ⟨⊥, inferInstance⟩
  have hcomap : ηF.comap (algebraMap R F) = ηR := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective (algebraMap R F)
      (IsFractionRing.injective R F)
  calc
    Module.rankAtStalk (grading J n) p =
        Module.rankAtStalk (grading J n) ηR :=
      coordinateRing_homogeneousPiece_rankAtStalk_constant J n p ηR
    _ = Module.rankAtStalk (F ⊗[R] grading J n) ηF := by
      rw [Module.rankAtStalk_baseChange, hcomap]
    _ = Module.finrank F (F ⊗[R] grading J n) := by
      exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := F)
        (M := F ⊗[R] grading J n)) ηF

/-- Localizing the flat homogeneous coordinate algebra at a projective
coordinate remains flat over the coefficient ring. The chart algebra is
the degree-zero subring of this localization. -/
theorem coordinateRing_away_coordinate_flat
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (j : Fin 4) :
    Module.Flat R (Localization.Away (coordinate J j)) := by
  exact Localization.flat (CoordinateRing J) (Submonoid.powers (coordinate J j))

/-- A prime curve in the generic cubic has a prime projective model inside
the cubic after restricting to a nonempty principal open. Its coordinate
ring is flat over the open, and its generic fibre is the original curve. -/
theorem exists_flat_primeProjectiveCurve_genericFiber_model_in_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
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
          (∀ n : ℕ,
            Module.Flat (Localization.Away e) (grading J n)) ∧
          (∀ n : ℕ,
            Module.Projective (Localization.Away e) (grading J n)) ∧
          (∀ n : ℕ, ∀ p q : PrimeSpectrum (Localization.Away e),
            Module.rankAtStalk (grading J n) p =
              Module.rankAtStalk (grading J n) q) ∧
          (∀ j : Fin 4,
            Module.Flat (Localization.Away e)
              (Localization.Away (coordinate J j))) ∧
          AlgebraicGeometry.Flat (toBase J) ∧
          AlgebraicGeometry.IsProper (toBase J) ∧
          AlgebraicGeometry.LocallyOfFinitePresentation (toBase J) ∧
          ∃ i : scheme J ⟶
              hypersurface (MvPolynomial.map (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))),
            AlgebraicGeometry.IsClosedImmersion i ∧
            i ≫ hypersurfaceToBase
                (MvPolynomial.map (algebraMap A (Localization.Away e)) p)
                (hp.map (algebraMap A (Localization.Away e))) = toBase J ∧
            Nonempty (scheme C ≅
              pullback (toBase J) (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨e, he, φ, hφ, hcomp, J, hJ, _, hflat, hproj, hgeneric⟩ :=
    exists_flat_homogeneous_contracted_model_after_away (A := A) m C
  let ψ : A →+* Localization.Away e := algebraMap A (Localization.Away e)
  have hpJ : MvPolynomial.map ψ p ∈ J.toIdeal := by
    rw [hJ]
    change MvPolynomial.map φ (MvPolynomial.map ψ p) ∈ C.toIdeal
    rw [MvPolynomial.map_map]
    have hcompRing : φ.comp ψ = algebraMap A F := by
      ext a
      exact hcomp a
    rw [hcompRing]
    exact hpC
  letI : C.toIdeal.IsPrime := hprime
  letI : J.toIdeal.IsPrime := hJ ▸ Ideal.IsPrime.comap (MvPolynomial.map φ)
  have hpieces : ∀ n : ℕ,
      Module.Flat (Localization.Away e) (grading J n) := by
    letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
    intro n
    exact coordinateRing_homogeneousPiece_flat J n
  have hprojective : ∀ n : ℕ,
      Module.Projective (Localization.Away e) (grading J n) := by
    letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
    intro n
    exact coordinateRing_homogeneousPiece_projective J n
  have hconstant : ∀ n : ℕ, ∀ p q : PrimeSpectrum (Localization.Away e),
      Module.rankAtStalk (grading J n) p =
        Module.rankAtStalk (grading J n) q := by
    letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
    letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
    intro n p q
    exact coordinateRing_homogeneousPiece_rankAtStalk_constant J n p q
  have haway : ∀ j : Fin 4,
      Module.Flat (Localization.Away e)
        (Localization.Away (coordinate J j)) := by
    letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
    intro j
    exact coordinateRing_away_coordinate_flat J j
  refine ⟨e, he, φ, hφ, hcomp, J, hJ, inferInstance, hflat, hpieces, hprojective,
    hconstant,
    haway, hproj,
    inferInstance,
    homogeneousModel_locallyOfFinitePresentation J,
    homogeneousModelToCubic (MvPolynomial.map ψ p) (hp.map ψ) J hpJ,
    homogeneousModelToCubic_closedImmersion _ _ J hpJ,
    homogeneousModelToCubic_toBase _ _ J hpJ, hgeneric⟩

end PfaffianDescent
