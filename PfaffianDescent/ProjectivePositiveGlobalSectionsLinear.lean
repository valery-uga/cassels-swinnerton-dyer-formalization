import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-!
# Homogeneous elements as linear global sections

The fraction `q/1` construction respects the scalar action furnished by
the actual structure morphism to the ground field. On a nonempty integral
projective scheme, it is injective: evaluation at any projective point
lands in a localization of the domain.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics HomogeneousProjective

universe u

variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous coordinate element, as a ground-field-linear section on
the top open of projective space modulo a homogeneous ideal. -/
noncomputable def positiveHomogeneousTopSectionLinearMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (m : ℕ) :
    grading I m →ₗ[K]
      SchemeModuleOpenSectionsOver (toBase I)
        (positiveSheafOfModules (grading I) m) ⊤ where
  toFun q := PresheafOfModules.sections.eval
    (positiveGlobalSectionOfHomogeneous (grading I) m q) (op ⊤)
  map_add' q r := by
    apply Subtype.ext
    funext x
    change Localization.mk ((q : CoordinateRing I) + (r : CoordinateRing I))
        (1 : (positivePointIdeal (grading I) x.1).primeCompl) =
      Localization.mk (q : CoordinateRing I) 1 +
        Localization.mk (r : CoordinateRing I) 1
    exact (Localization.add_mk_self (q : CoordinateRing I) 1
      (r : CoordinateRing I)).symm
  map_smul' a q := by
    change PresheafOfModules.sections.eval
        (positiveGlobalSectionOfHomogeneous (grading I) m (a • q)) (op ⊤) =
      schemeOpenBaseRingHom (toBase I) ⊤ a •
        PresheafOfModules.sections.eval
          (positiveGlobalSectionOfHomogeneous (grading I) m q) (op ⊤)
    rw [schemeOpenBaseRingHom_top_apply]
    exact positiveGlobalSection_eval_smul_degree I m a q

/-- Homogeneous coordinate elements define morphism-valued global sections
linearly over the actual ground field. -/
noncomputable def positiveHomogeneousGlobalSectionLinearMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (m : ℕ) :
    grading I m →ₗ[K]
      SchemeModuleGlobalSectionsOver (toBase I)
        (positiveSheafOfModules (grading I) m) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
    (positiveSheafOfModules (grading I) m)).symm.toLinearMap.comp
      (positiveHomogeneousTopSectionLinearMap I m)

/-- Equality of two homogeneous positive-twist sections implies equality of
their fractions in the localization at every projective point. This also
applies to nonreduced and reducible projective schemes. -/
theorem positiveGlobalSectionOfHomogeneous_eq_imp_pointwise_localization_eq
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ) (q r : grading I m)
    (h : positiveGlobalSectionOfHomogeneous (grading I) m q =
      positiveGlobalSectionOfHomogeneous (grading I) m r) :
    ∀ x : ProjectiveSpectrum.top (grading I),
      (Localization.mk (q : CoordinateRing I) 1 :
        PositiveFiber (grading I) x) =
      Localization.mk (r : CoordinateRing I) 1 := by
  intro x
  let ev : (positiveSheafOfModules (grading I) m).sections →
      PositiveFiber (grading I) x := fun s =>
    (positiveSectionValue (grading I) m (op ⊤)
      (PresheafOfModules.sections.eval s (op ⊤)) ⟨x, trivial⟩).1
  exact (positiveSectionValue_positiveGlobalSectionOfHomogeneous
    (grading I) m q x).symm.trans
      ((congrArg ev h).trans
        (positiveSectionValue_positiveGlobalSectionOfHomogeneous
          (grading I) m r x))

/-- The concrete pointwise criterion for equality of homogeneous
positive-twist sections. -/
theorem positiveGlobalSectionOfHomogeneous_eq_iff_pointwise_localization_eq
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ) (q r : grading I m) :
    positiveGlobalSectionOfHomogeneous (grading I) m q =
        positiveGlobalSectionOfHomogeneous (grading I) m r ↔
      ∀ x : ProjectiveSpectrum.top (grading I),
        (Localization.mk (q : CoordinateRing I) 1 :
          PositiveFiber (grading I) x) =
        Localization.mk (r : CoordinateRing I) 1 := by
  constructor
  · exact positiveGlobalSectionOfHomogeneous_eq_imp_pointwise_localization_eq I m q r
  · intro h
    apply PresheafOfModules.sections_ext
    intro U
    apply Subtype.ext
    funext y
    exact h y.1

/-- There are no invisible homogeneous coordinate elements on a nonempty
integral projective scheme. -/
theorem positiveGlobalSectionOfHomogeneous_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsDomain (CoordinateRing I)] [Nonempty (scheme I)] (m : ℕ) :
    Function.Injective (positiveGlobalSectionOfHomogeneous (grading I) m) := by
  classical
  let x : ProjectiveSpectrum.top (grading I) :=
    Classical.choice (show Nonempty (scheme I) from inferInstance)
  intro q r h
  let ev : (positiveSheafOfModules (grading I) m).sections →
      PositiveFiber (grading I) x := fun s =>
    (positiveSectionValue (grading I) m (op ⊤)
      (PresheafOfModules.sections.eval s (op ⊤)) ⟨x, trivial⟩).1
  have he : (Localization.mk (q : CoordinateRing I) 1 : PositiveFiber (grading I) x) =
      Localization.mk (r : CoordinateRing I) 1 :=
    (positiveSectionValue_positiveGlobalSectionOfHomogeneous (grading I) m q x).symm.trans
      ((congrArg ev h).trans
        (positiveSectionValue_positiveGlobalSectionOfHomogeneous (grading I) m r x))
  letI : (positivePointIdeal (grading I) x).IsPrime :=
    ProjectiveSpectrum.isPrime x
  apply Subtype.ext
  apply IsLocalization.injective (PositiveFiber (grading I) x)
    (positivePointIdeal (grading I) x).primeCompl_le_nonZeroDivisors
  simpa only [Localization.mk_one_eq_algebraMap] using he

/-- Injectivity also holds for the linear map to top-open sections. -/
theorem positiveHomogeneousTopSectionLinearMap_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsDomain (CoordinateRing I)] [Nonempty (scheme I)] (m : ℕ) :
    Function.Injective (positiveHomogeneousTopSectionLinearMap I m) := by
  intro q r h
  apply positiveGlobalSectionOfHomogeneous_injective I m
  apply (schemeModuleSectionsEquivTop
    (positiveSheafOfModules (grading I) m)).injective
  exact h

/-- Injectivity of homogeneous sections transfers to the ground-field-linear
map into actual morphism-valued global sections. -/
theorem positiveHomogeneousGlobalSectionLinearMap_injective_of_sections_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ)
    (hsec : Function.Injective
      (positiveGlobalSectionOfHomogeneous (grading I) m)) :
    Function.Injective (positiveHomogeneousGlobalSectionLinearMap I m) := by
  intro q r h
  apply hsec
  apply (schemeModuleSectionsEquivTop
    (positiveSheafOfModules (grading I) m)).injective
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
    (positiveSheafOfModules (grading I) m)).symm.injective h

/-- Injectivity for morphism-valued global sections. -/
theorem positiveHomogeneousGlobalSectionLinearMap_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsDomain (CoordinateRing I)] [Nonempty (scheme I)] (m : ℕ) :
    Function.Injective (positiveHomogeneousGlobalSectionLinearMap I m) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
    (positiveSheafOfModules (grading I) m)).symm.injective.comp
      (positiveHomogeneousTopSectionLinearMap_injective I m)

/-- If the fraction construction generates all global sections, its linear
version is surjective too. -/
theorem positiveHomogeneousGlobalSectionLinearMap_surjective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (m : ℕ)
    (h : Function.Surjective
      (positiveGlobalSectionOfHomogeneous (grading I) m)) :
    Function.Surjective (positiveHomogeneousGlobalSectionLinearMap I m) := by
  have ht : Function.Surjective (positiveHomogeneousTopSectionLinearMap I m) :=
    (schemeModuleSectionsEquivTop
      (positiveSheafOfModules (grading I) m)).surjective.comp h
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
    (positiveSheafOfModules (grading I) m)).symm.surjective.comp ht

end PfaffianDescent.ProjectiveNegativeTwist
