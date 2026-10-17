import PfaffianDescent.FinitePolynomialPositiveGlobalSections
import PfaffianDescent.AmbientBottomProjectiveIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackIso
import PfaffianDescent.SchemeModuleGlobalSectionsTop

noncomputable section
namespace PfaffianDescent.ProjectiveLineNative
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule Bool K
local notation "L" => (⊥ : HomogeneousIdeal PS)

/-- Restriction along a genuine scheme isomorphism identifies actual top sections. -/
def actualIsoRestrictionTopSectionsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    Γ(M, ⊤) ≅ Γ((Scheme.Modules.restrictFunctor f).obj M, ⊤) := by
  have htop : f ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  exact ((M.restrictAppIso f ⊤) ≪≫
    (M.presheaf.mapIso (eqToIso htop).op).symm).symm

/-- The original Bool bottom quotient pulls the actual polynomial positive twist to its own twist. -/
def actualLineBottomPositivePullbackIso (m : ℕ) :
    (Scheme.Modules.pullback (quotientProjMap L)).obj
      (positiveSheafOfModules PS m) ≅ positiveSheafOfModules (grading L) m :=
  cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackIso
    PS (grading L) (quotientGradedRingHom L)
    (irrelevant_le_map_quotientGradedRingHom L)
    mvPolynomial_irrelevant_le_span_degreeOne_small
    (gradedSurjective_irrelevant_le_span_degreeOne PS (grading L)
      (quotientGradedRingHom L) (quotientGradedRingHom_surjective L)
      mvPolynomial_irrelevant_le_span_degreeOne_small) m

/-- Actual top sections on the manuscript's Bool quotient line, using its literal positive twist. -/
def actualLinePositiveTopSectionsIso (m : ℕ) :
    Γ(positiveSheafOfModules PS m, ⊤) ≅
      Γ(positiveSheafOfModules (grading L) m, ⊤) := by
  let q := quotientProjMap L
  letI : IsIso q := (ambientBottomProjectiveIso (R := K) (σ := Bool)).isIso_hom
  let e : (Scheme.Modules.restrictFunctor q).obj
      (positiveSheafOfModules PS m) ≅ positiveSheafOfModules (grading L) m :=
    (Scheme.Modules.restrictFunctorIsoPullback q).app (positiveSheafOfModules PS m) ≪≫
      actualLineBottomPositivePullbackIso K m
  exact actualIsoRestrictionTopSectionsIso q (positiveSheafOfModules PS m) ≪≫
    ((Scheme.Modules.toPresheaf (scheme L)).mapIso e).app (op ⊤)

/-- No surjectivity premise: all actual global sections on the original quotient line
are homogeneous polynomials, transported by its canonical native restriction Iso. -/
def actualLineHomogeneousSectionsEquiv (m : ℕ) :
    PS m ≃ (positiveSheafOfModules (grading L) m).sections :=
  (ProjectiveFiniteNative.finitePolynomialHomogeneousSectionsEquiv
    (σ := Bool) K m).trans
  ((schemeModuleSectionsEquivTop (positiveSheafOfModules PS m)).trans
    ((Equiv.ofBijective (actualLinePositiveTopSectionsIso K m).hom
      (ConcreteCategory.bijective_of_isIso (actualLinePositiveTopSectionsIso K m).hom)).trans
      (schemeModuleSectionsEquivTop (positiveSheafOfModules (grading L) m)).symm))

/-- The actual morphism-valued H0 with the ORIGINAL line-to-Spec(K) scalar action. -/
def actualLineHomogeneousHZeroEquiv (m : ℕ) :
    PS m ≃ SchemeModuleGlobalSectionsOver (toBase L)
      (positiveSheafOfModules (grading L) m) :=
  (actualLineHomogeneousSectionsEquiv K m).trans
    (schemeModuleGlobalSectionsOverEquivSections (toBase L)
      (positiveSheafOfModules (grading L) m)).symm

/-- The constructed bijection is compatible with literal restriction on every open,
not merely its underlying polynomial dimension. -/
theorem actualLineHomogeneousSectionsEquiv_restrict
    (m : ℕ) (p : PS m) (U : (scheme L).Opens) :
    PresheafOfModules.sections.eval (actualLineHomogeneousSectionsEquiv K m p) (op U) =
      (positiveSheafOfModules (grading L) m).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        ((actualLinePositiveTopSectionsIso K m).hom
          (PresheafOfModules.sections.eval
            (positiveGlobalSectionOfHomogeneous PS m p) (op ⊤))) := by
  rfl

/-- In particular the same bijection respects BOTH original Bool coordinate charts. -/
theorem actualLineHomogeneousSectionsEquiv_chart
    (m : ℕ) (p : PS m) (b : Bool) :
    PresheafOfModules.sections.eval (actualLineHomogeneousSectionsEquiv K m p)
        (op (quotientCoordinateOpen L b)) =
      (positiveSheafOfModules (grading L) m).presheaf.map
        (homOfLE (show quotientCoordinateOpen L b ≤ ⊤ from le_top)).op
        ((actualLinePositiveTopSectionsIso K m).hom
          (PresheafOfModules.sections.eval
            (positiveGlobalSectionOfHomogeneous PS m p) (op ⊤))) :=
  actualLineHomogeneousSectionsEquiv_restrict K m p (quotientCoordinateOpen L b)

/-- The requested cubic-degree endpoint on exactly the manuscript's projective line. -/
def actualLineCubicHomogeneousHZeroEquiv :
    PS 3 ≃ SchemeModuleGlobalSectionsOver (toBase L)
      (positiveSheafOfModules (grading L) 3) :=
  actualLineHomogeneousHZeroEquiv K 3

end PfaffianDescent.ProjectiveLineNative
end
