import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealLinearChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The inverse native chart map carries the literal away fraction to the
literal structure-sheaf section on Spec(Away ell). -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChartFunction
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (a : Away (grading I) (ell : CoordinateRing I)) :
    (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
      Nat.zero_lt_one).inv.appTop
      ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).topIso.inv
        ((ProjectiveSpectrum.Proj.awayToSection (grading I)
          (ell : CoordinateRing I)).hom a)) =
    (affineGlobalSectionsUnitLinearEquiv
      (A := Away (grading I) (ell : CoordinateRing I))).symm a := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  let v := (Scheme.ΓSpecIso
    (CommRingCat.of (Away (grading I) (ell : CoordinateRing I)))).inv a
  have hh : e.hom.appTop v = U.topIso.inv
      ((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom a) := by
    change (Proj.basicOpenToSpec (grading I) (ell : CoordinateRing I)).app ⊤ v = _
    rw [Proj.basicOpenToSpec_app_top]
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (fun z => U.topIso.inv
      ((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom z))
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso
        (CommRingCat.of (Away (grading I) (ell : CoordinateRing I)))) a)
  have hc : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp
  have hv := congrArg (fun m => m.hom v) hc
  change e.inv.appTop _ = v
  exact (congrArg (fun z => e.inv.appTop z) hh).symm.trans hv

end PfaffianDescent
