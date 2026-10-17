import PfaffianDescent.P3PositiveTwistGlobalSections
import PfaffianDescent.VoisinProjectiveThreeGlobalFunctions
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! SOURCE ONLY / UNVERIFIED. The actual raw ambient PS grading, its actual
structure map, and its actual positive-twist sheaf are used throughout.
No quotient-by-zero grading or externally supplied global equivalence. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective LaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual ambient coefficient map has literal scalar-fraction values. -/
theorem p3AmbientBaseScalar_value (c : K) (x : ProjectiveSpectrum.top PS) :
    ((affineFunctionHom (ambientToBase (R := K) (σ := Fin 4)) c).1
      ⟨x, trivial⟩).val =
      Localization.mk (C c : MvPolynomial (Fin 4) K)
        (1 : (positivePointIdeal PS x).primeCompl) := by
  change ((affineFunctionHom (p3BaseMap K) c).1 ⟨x, trivial⟩).val = _
  rw [← p3GlobalFunctionScalar_eq_affineFunctionHom K c]
  exact p3GlobalFunctionScalar_value K c x

/-- Homogeneous polynomials give K-linear top sections of actual O(m). -/
def p3HomogeneousTopSectionLinearMap (m : ℕ) :
    PS m →ₗ[K]
      SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS m) ⊤ where
  toFun p := PresheafOfModules.sections.eval
    (positiveGlobalSectionOfHomogeneous PS m p) (op ⊤)
  map_add' p q := by
    apply Subtype.ext
    funext x
    change Localization.mk ((p : MvPolynomial (Fin 4) K) + q)
        (1 : (positivePointIdeal PS x.1).primeCompl) =
      Localization.mk (p : MvPolynomial (Fin 4) K) 1 +
        Localization.mk (q : MvPolynomial (Fin 4) K) 1
    exact (Localization.add_mk_self (p : MvPolynomial (Fin 4) K) 1
      (q : MvPolynomial (Fin 4) K)).symm
  map_smul' c p := by
    apply Subtype.ext
    funext x
    change Localization.mk ((c • p : PS m) : MvPolynomial (Fin 4) K)
        (1 : (positivePointIdeal PS x.1).primeCompl) =
      ((schemeOpenBaseRingHom (ambientToBase (R := K) (σ := Fin 4)) ⊤ c).1 x).val *
        Localization.mk (p : MvPolynomial (Fin 4) K) 1
    rw [schemeOpenBaseRingHom_top_apply]
    have hp : ((c • p : PS m) : MvPolynomial (Fin 4) K) =
        C c * (p : MvPolynomial (Fin 4) K) := by
      exact Algebra.smul_def c (p : MvPolynomial (Fin 4) K)
    rw [hp, p3AmbientBaseScalar_value K c x.1]
    rw [Localization.mk_mul]
    congr 2
    ext
    simp

/-- Actual morphism-valued global sections, with the actual ambient K action. -/
def p3HomogeneousGlobalSectionLinearMap (m : ℕ) :
    PS m →ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS m) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop
    (ambientToBase (R := K) (σ := Fin 4))
    (positiveSheafOfModules PS m)).symm.toLinearMap.comp
      (p3HomogeneousTopSectionLinearMap K m)

/-- Injectivity on the actual raw grading follows from the proved Laurent
chart formula, rather than an assumed polynomial/section comparison. -/
theorem p3HomogeneousGlobalSectionLinearMap_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (p3HomogeneousGlobalSectionLinearMap K m) := by
  intro p q h
  have htop : p3HomogeneousTopSectionLinearMap K m p =
      p3HomogeneousTopSectionLinearMap K m q :=
    (schemeModuleGlobalSectionsLinearEquivOpenTop
      (ambientToBase (R := K) (σ := Fin 4))
      (positiveSheafOfModules PS m)).symm.injective h
  have hsec : positiveGlobalSectionOfHomogeneous PS m p =
      positiveGlobalSectionOfHomogeneous PS m q :=
    (schemeModuleSectionsEquivTop (positiveSheafOfModules PS m)).injective htop
  have hL := congrArg (fun s => p3PositiveTwistGlobalChartLaurent K m hm s 0) hsec
  rw [p3PositiveTwistGlobalChartLaurent_of_homogeneous,
    p3PositiveTwistGlobalChartLaurent_of_homogeneous] at hL
  exact Subtype.ext (polynomialToLaurent_injective (K := K) hL)

theorem p3HomogeneousGlobalSectionLinearMap_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (p3HomogeneousGlobalSectionLinearMap K m) := by
  have ht : Function.Surjective (p3HomogeneousTopSectionLinearMap K m) :=
    (schemeModuleSectionsEquivTop (positiveSheafOfModules PS m)).surjective.comp
      (p3_positiveGlobalSectionOfHomogeneous_surjective K m hm)
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop
    (ambientToBase (R := K) (σ := Fin 4))
    (positiveSheafOfModules PS m)).symm.surjective.comp ht

/-- Internally derived actual ambient O(m) global equivalence. -/
def p3HomogeneousGlobalSectionsLinearEquiv (m : ℕ) (hm : 0 < m) :
    PS m ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS m) :=
  LinearEquiv.ofBijective (p3HomogeneousGlobalSectionLinearMap K m)
    ⟨p3HomogeneousGlobalSectionLinearMap_injective K m hm,
      p3HomogeneousGlobalSectionLinearMap_surjective K m hm⟩

end PfaffianDescent.ProjectiveNegativeTwist
