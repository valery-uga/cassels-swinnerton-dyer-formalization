import PfaffianDescent.PlanePositiveTwistGlobalSections
import PfaffianDescent.PlaneAmbientGroundScalarValues
import PfaffianDescent.CorayPlaneCubicHilbertFunction
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! SOURCE ONLY / UNVERIFIED. The actual raw ambient PS grading, its actual
structure map, and its actual positive-twist sheaf are used throughout.
No quotient-by-zero grading or externally supplied global equivalence. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist PlaneLaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 3) K

/-- The actual ambient coefficient map has literal scalar-fraction values. -/
theorem p2AmbientBaseScalar_value (c : K) (x : ProjectiveSpectrum.top PS) :
    ((affineFunctionHom (ambientToBase (R := K) (σ := Fin 3)) c).1
      ⟨x, trivial⟩).val =
      Localization.mk (C c : MvPolynomial (Fin 3) K)
        (1 : (positivePointIdeal PS x).primeCompl) := by
  exact p2BaseMap_scalar_value K c x

/-- Homogeneous polynomials give K-linear top sections of actual O(m). -/
def p2HomogeneousTopSectionLinearMap (m : ℕ) :
    PS m →ₗ[K]
      SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m) ⊤ where
  toFun p := PresheafOfModules.sections.eval
    (positiveGlobalSectionOfHomogeneous PS m p) (op ⊤)
  map_add' p q := by
    apply Subtype.ext
    funext x
    change Localization.mk ((p : MvPolynomial (Fin 3) K) + q)
        (1 : (positivePointIdeal PS x.1).primeCompl) =
      Localization.mk (p : MvPolynomial (Fin 3) K) 1 +
        Localization.mk (q : MvPolynomial (Fin 3) K) 1
    exact (Localization.add_mk_self (p : MvPolynomial (Fin 3) K) 1
      (q : MvPolynomial (Fin 3) K)).symm
  map_smul' c p := by
    apply Subtype.ext
    funext x
    change Localization.mk ((c • p : PS m) : MvPolynomial (Fin 3) K)
        (1 : (positivePointIdeal PS x.1).primeCompl) =
      ((schemeOpenBaseRingHom (ambientToBase (R := K) (σ := Fin 3)) ⊤ c).1 x).val *
        Localization.mk (p : MvPolynomial (Fin 3) K) 1
    rw [schemeOpenBaseRingHom_top_apply]
    have hp : ((c • p : PS m) : MvPolynomial (Fin 3) K) =
        C c * (p : MvPolynomial (Fin 3) K) := by
      exact Algebra.smul_def c (p : MvPolynomial (Fin 3) K)
    rw [hp, p2AmbientBaseScalar_value K c x.1]
    rw [Localization.mk_mul]
    congr 2
    ext
    simp

/-- Actual morphism-valued global sections, with the actual ambient K action. -/
def p2HomogeneousGlobalSectionLinearMap (m : ℕ) :
    PS m →ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop
    (ambientToBase (R := K) (σ := Fin 3))
    (positiveSheafOfModules PS m)).symm.toLinearMap.comp
      (p2HomogeneousTopSectionLinearMap K m)

/-- Injectivity on the actual raw grading follows from the proved Laurent
chart formula, rather than an assumed polynomial/section comparison. -/
theorem p2HomogeneousGlobalSectionLinearMap_injective (m : ℕ) :
    Function.Injective (p2HomogeneousGlobalSectionLinearMap K m) := by
  intro p q h
  have htop : p2HomogeneousTopSectionLinearMap K m p =
      p2HomogeneousTopSectionLinearMap K m q :=
    (schemeModuleGlobalSectionsLinearEquivOpenTop
      (ambientToBase (R := K) (σ := Fin 3))
      (positiveSheafOfModules PS m)).symm.injective h
  have hsec : positiveGlobalSectionOfHomogeneous PS m p =
      positiveGlobalSectionOfHomogeneous PS m q :=
    (schemeModuleSectionsEquivTop (positiveSheafOfModules PS m)).injective htop
  have hL := congrArg (fun s => p2PositiveTwistGlobalChartLaurent K m s 0) hsec
  rw [p2PositiveTwistGlobalChartLaurent_of_homogeneous,
    p2PositiveTwistGlobalChartLaurent_of_homogeneous] at hL
  exact Subtype.ext (polynomialToLaurent_injective (K := K) hL)

theorem p2HomogeneousGlobalSectionLinearMap_surjective (m : ℕ) :
    Function.Surjective (p2HomogeneousGlobalSectionLinearMap K m) := by
  have ht : Function.Surjective (p2HomogeneousTopSectionLinearMap K m) :=
    (schemeModuleSectionsEquivTop (positiveSheafOfModules PS m)).surjective.comp
      (p2_positiveGlobalSectionOfHomogeneous_surjective K m)
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop
    (ambientToBase (R := K) (σ := Fin 3))
    (positiveSheafOfModules PS m)).symm.surjective.comp ht

/-- Internally derived actual ambient O(m) global equivalence. -/
def p2HomogeneousGlobalSectionsLinearEquiv (m : ℕ) :
    PS m ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m) :=
  LinearEquiv.ofBijective (p2HomogeneousGlobalSectionLinearMap K m)
    ⟨p2HomogeneousGlobalSectionLinearMap_injective K m,
      p2HomogeneousGlobalSectionLinearMap_surjective K m⟩

/-- Actual native O(m) global sections are finite for the ORIGINAL
ambient structure morphism, because the constructed homogeneous map is onto. -/
theorem p2PositiveTwistGlobalSections_finite (m : ℕ) :
    Module.Finite K
      (SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m)) :=
  Module.Finite.of_surjective (p2HomogeneousGlobalSectionLinearMap K m)
    (p2HomogeneousGlobalSectionLinearMap_surjective K m)

/-- Actual native O(m) global sections have their genuine monomial rank,
with the ORIGINAL ambient K-action and no grade-as-H0 premise. -/
theorem p2PositiveTwistGlobalSections_finrank (m : ℕ) :
    Module.finrank K
      (SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m)) = (m + 2).choose 2 := by
  rw [← (p2HomogeneousGlobalSectionsLinearEquiv K m).finrank_eq]
  exact Coray.threeVariable_homogeneous_finrank m

/-- Literal top-open sections carry the independently defined SAME ambient
action; both their finiteness and native dimension are derived. -/
theorem p2PositiveTwistTopSections_finite_finrank (m : ℕ) :
    Module.Finite K
      (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m) ⊤) ∧
    Module.finrank K
      (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m) ⊤) = (m + 2).choose 2 := by
  let e := schemeModuleGlobalSectionsLinearEquivOpenTop
    (ambientToBase (R := K) (σ := Fin 3)) (positiveSheafOfModules PS m)
  letI : Module.Finite K
      (SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 3))
        (positiveSheafOfModules PS m)) := p2PositiveTwistGlobalSections_finite K m
  refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, ?_⟩
  rw [← e.finrank_eq, p2PositiveTwistGlobalSections_finrank K m]

end PfaffianDescent.ProjectivePlaneNative
