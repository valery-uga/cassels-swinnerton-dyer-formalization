import PfaffianDescent.ActualPositiveTwistChartSectionCoefficient
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-! Actual positive-twist chart denominators, retaining the original canonical
homogeneous section map and native coefficient trivialization. No eventual
GLOBAL surjectivity or H1 vanishing is a premise or conclusion here.
SOURCE ONLY UNVERIFIED; root owns compilation and acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual twist section, divided by its actual chart basis, in the OWN
homogeneous Away ring. Both maps are the existing canonical chart maps. -/
def actualPositiveChartCoefficientAway
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ)
    (s : Γ(positiveSheafOfModules (grading I) m,
      Proj.basicOpen (grading I) (ell : CoordinateRing I))) :
    Away (grading I) (ell : CoordinateRing I) :=
  (Proj.basicOpenIsoAway (grading I) (ell : CoordinateRing I) ell.property
    (by decide : 0 < (1 : ℕ))).inv
      (show Γ(scheme I, Proj.basicOpen (grading I) (ell : CoordinateRing I)) from
        actualPositiveTwistChartSectionCoefficient I ell m s)

/-- Every actual native twist-chart section has a genuine homogeneous
numerator and power denominator in the same coordinate quotient. -/
theorem actualPositiveChartCoefficient_exists_homogeneousFraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ)
    (s : Γ(positiveSheafOfModules (grading I) m,
      Proj.basicOpen (grading I) (ell : CoordinateRing I))) :
    ∃ (k : ℕ) (a : grading I k),
      (show Γ(scheme I, Proj.basicOpen (grading I) (ell : CoordinateRing I)) from
        actualPositiveTwistChartSectionCoefficient I ell m s) =
      (Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.property k (a : CoordinateRing I)
          (by simpa only [smul_eq_mul, mul_one] using a.property)) := by
  let e := Proj.basicOpenIsoAway (grading I) (ell : CoordinateRing I) ell.property
    (by decide : 0 < (1 : ℕ))
  let c : Γ(scheme I, Proj.basicOpen (grading I) (ell : CoordinateRing I)) :=
    show Γ(scheme I, Proj.basicOpen (grading I) (ell : CoordinateRing I)) from
      actualPositiveTwistChartSectionCoefficient I ell m s
  let z : Away (grading I) (ell : CoordinateRing I) := e.inv c
  obtain ⟨k, a, ha, hrep⟩ := Away.mk_surjective (grading I) ell.property z
  let a' : grading I k := ⟨a, by simpa only [smul_eq_mul, mul_one] using ha⟩
  refine ⟨k, a', ?_⟩
  have hrep' : Away.mk (grading I) ell.property k (a' : CoordinateRing I)
      (by simpa only [smul_eq_mul, mul_one] using a'.property) = z := hrep
  calc
    c = e.hom z := (ConcreteCategory.congr_hom e.inv_hom_id c).symm
    _ = e.hom (Away.mk (grading I) ell.property k (a' : CoordinateRing I)
        (by simpa only [smul_eq_mul, mul_one] using a'.property)) :=
      congrArg (fun v : Away (grading I) (ell : CoordinateRing I) => e.hom v) hrep'.symm

/-- The actual original homogeneous-section map has its exact q/ell^m
chart coefficient. This is a derived formula, not a compatibility premise. -/
theorem actualPositiveChartCoefficientAway_canonicalSection
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (a : grading I m) :
    actualPositiveChartCoefficientAway I ell m
      ((positiveSheafOfModules (grading I) m).presheaf.map
        (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤
          from le_top)).op
        (show Γ(positiveSheafOfModules (grading I) m, ⊤) from
          positiveHomogeneousTopSectionLinearMap I m a)) =
      Away.mk (grading I) ell.property m (a : CoordinateRing I)
        (by simpa only [smul_eq_mul, mul_one] using a.property) := by
  let e := Proj.basicOpenIsoAway (grading I) (ell : CoordinateRing I) ell.property
    (by decide : 0 < (1 : ℕ))
  let z := Away.mk (grading I) ell.property m (a : CoordinateRing I)
    (by simpa only [smul_eq_mul, mul_one] using a.property)
  have hcoeff := actualPositiveTwistChartSectionCoefficient_fraction I ell m a
  have hcoeff' :
      (show Γ(scheme I, Proj.basicOpen (grading I) (ell : CoordinateRing I)) from
        actualPositiveTwistChartSectionCoefficient I ell m
          ((positiveSheafOfModules (grading I) m).presheaf.map
            (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤
              from le_top)).op
            (PresheafOfModules.sections.eval
              (positiveGlobalSectionOfHomogeneous (grading I) m a) (op ⊤)))) =
      e.hom z := hcoeff
  exact (congrArg (fun c : Γ(scheme I,
    Proj.basicOpen (grading I) (ell : CoordinateRing I)) => e.inv c) hcoeff').trans
      (ConcreteCategory.congr_hom e.hom_inv_id z)

/-- Each actual chart coefficient admits clearing by every sufficiently
large chart-coordinate power, with the numerator in the exact same grade. -/
theorem actualPositiveChartCoefficientAway_eventually_powerCleared
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ)
    (s : Γ(positiveSheafOfModules (grading I) m,
      Proj.basicOpen (grading I) (ell : CoordinateRing I))) :
    ∀ᶠ n in Filter.atTop, ∃ a : grading I n,
      algebraMap (CoordinateRing I) (Localization.Away (ell : CoordinateRing I))
        (a : CoordinateRing I) =
      (ell : CoordinateRing I) ^ n •
        (actualPositiveChartCoefficientAway I ell m s).val := by
  have h := Away.eventually_smul_mem ell.property
    (actualPositiveChartCoefficientAway I ell m s)
  filter_upwards [h] with n hn
  obtain ⟨a, ha, heq⟩ := hn
  exact ⟨⟨a, by simpa only [smul_eq_mul, mul_one, SetLike.mem_coe] using ha⟩, heq⟩

/-- For a fixed actual original-K global section, one actual exponent bound
clears its coefficients on all four standard coordinate charts. The bound
may depend on this section; uniform Serre surjectivity is not presumed. -/
theorem actualPositiveGlobalSection_fourChartCoefficients_powerCleared
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (m : ℕ)
    (s : SchemeModuleOpenSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) m) ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : Fin 4,
      ∃ a : grading I n,
        algebraMap (CoordinateRing I) (Localization.Away (coordinate I j))
          (a : CoordinateRing I) =
        (coordinate I j) ^ n •
          (actualPositiveChartCoefficientAway I
            ⟨coordinate I j, coordinate_mem I j⟩ m
            ((positiveSheafOfModules (grading I) m).presheaf.map
              (homOfLE (show Proj.basicOpen (grading I) (coordinate I j) ≤ ⊤
                from le_top)).op
              (show Γ(positiveSheafOfModules (grading I) m, ⊤) from s))).val := by
  apply Filter.eventually_atTop.mp
  apply Filter.eventually_all.mpr
  intro j
  exact actualPositiveChartCoefficientAway_eventually_powerCleared I
    ⟨coordinate I j, coordinate_mem I j⟩ m
    ((positiveSheafOfModules (grading I) m).presheaf.map
      (homOfLE (show Proj.basicOpen (grading I) (coordinate I j) ≤ ⊤ from le_top)).op
      (show Γ(positiveSheafOfModules (grading I) m, ⊤) from s))

end PfaffianDescent.Coray
