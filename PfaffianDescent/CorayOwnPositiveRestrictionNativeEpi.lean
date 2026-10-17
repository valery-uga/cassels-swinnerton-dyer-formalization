import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackIso
import PfaffianDescent.CorayCartierCanonicalProjectionFormula
import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero
import PfaffianDescent.HomogeneousQuotientMap

/-! SOURCE ONLY. The actual Fin-4 quotient restriction factors through the
genuine native ideal-twist quotient and is Epi. No surjectivity, exactness,
IsIso, frame, or rank certificate is an original input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual polynomial quotient degree-one generation derives invertibility
of the actual positive-twist pullback adjunct. -/
lemma ownQuotientPositiveGradedPullbackHom_isIso
    (C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCD : C.toIdeal ≤ D.toIdeal) (m : ℕ) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
      (grading C) (grading D) (gradedQuotientMap C D hCD)
      (gradedSurjective_irrelevant_le (gradedQuotientMap C D hCD)
        (gradedQuotientMap_surjective C D hCD)) m) := by
  apply cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_isIso
  · exact gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading C)
      (quotientGradedRingHom C) (quotientGradedRingHom_surjective C)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  · exact gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading D)
      (quotientGradedRingHom D) (quotientGradedRingHom_surjective D)
      mvPolynomial_irrelevant_le_span_degreeOne_small

/-- Whole actual restriction is the actual adjunction unit followed by
the pushforward of its own adjunct, by the adjunction identity. -/
lemma ownQuotientPositiveRestriction_eq_unit_comp
    (C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCD : C.toIdeal ≤ D.toIdeal) (m : ℕ) :
    let f := gradedQuotientMap C D hCD
    let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D hCD)
    gradedRingHomPositiveTwistToPushforward (grading C) (grading D) f hf m =
      (Scheme.Modules.pullbackPushforwardAdjunction (schemeQuotientMap C D hCD)).unit.app
        (positiveSheafOfModules (grading C) m) ≫
      (Scheme.Modules.pushforward (schemeQuotientMap C D hCD)).map
        (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
          (grading C) (grading D) f hf m) := by
  dsimp only
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (schemeQuotientMap C D hCD)
  exact ((adj.homEquiv _ _).apply_symm_apply _).symm

/-- Factorization through the SAME canonical tensor quotient and its
native fiber projection. All maps are original actual maps. -/
theorem ownQuotientPositiveRestriction_eq_nativeFiberFactor
    (C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCD : C.toIdeal ≤ D.toIdeal) (m : ℕ) :
    let i := schemeQuotientMap C D hCD
    letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D hCD
    let T := positiveSheafOfModules (grading C) m
    let f := gradedQuotientMap C D hCD
    let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D hCD)
    gradedRingHomPositiveTwistToPushforward (grading C) (grading D) f hf m =
      (schemeModuleTensorUnitLeftIso T).inv ≫
        (closedImmersionIdealTwistSequence i T).g ≫
        schemeModuleCanonicalFiberProjection i T ≫
        (Scheme.Modules.pushforward i).map
          (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
            (grading C) (grading D) f hf m) := by
  dsimp only
  let i := schemeQuotientMap C D hCD
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D hCD
  let T := positiveSheafOfModules (grading C) m
  let e := schemeModuleTensorUnitLeftIso T
  let S := closedImmersionIdealTwistSequence i T
  let f := gradedQuotientMap C D hCD
  let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D hCD)
  let P := Scheme.Modules.pushforward i
  let c := cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
    (grading C) (grading D) f hf m
  let pr := schemeModuleCanonicalFiberProjection i T
  have hp := schemeModuleCanonicalFiberProjection_unit_square i T
  change S.g ≫ pr = e.hom ≫
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T at hp
  change gradedRingHomPositiveTwistToPushforward (grading C) (grading D) f hf m =
    e.inv ≫ S.g ≫ pr ≫ P.map c
  calc
    _ = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫ P.map c :=
      ownQuotientPositiveRestriction_eq_unit_comp C D hCD m
    _ = e.inv ≫ (S.g ≫ pr) ≫ P.map c := by
      rw [hp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := by simp only [Category.assoc]

/-- The whole actual graded restriction is Epi. Short exactness of the
actual ideal-twist quotient and both comparison isomorphisms are derived. -/
theorem ownQuotientPositiveRestriction_epi
    (C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCD : C.toIdeal ≤ D.toIdeal) (m : ℕ) :
    let f := gradedQuotientMap C D hCD
    let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D hCD)
    Epi (gradedRingHomPositiveTwistToPushforward (grading C) (grading D) f hf m) := by
  dsimp only
  let i := schemeQuotientMap C D hCD
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D hCD
  let T := positiveSheafOfModules (grading C) m
  let S := closedImmersionIdealTwistSequence i T
  let f := gradedQuotientMap C D hCD
  let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D hCD)
  let c := cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
    (grading C) (grading D) f hf m
  let pr := schemeModuleCanonicalFiberProjection i T
  letI : Epi S.g := (quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact C i m).epi_g
  letI : IsIso c := ownQuotientPositiveGradedPullbackHom_isIso C D hCD m
  letI : IsIso pr := schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne
    i T (actualComponent_positiveTwist_locallyRankOne C m)
  rw [ownQuotientPositiveRestriction_eq_nativeFiberFactor C D hCD m]
  infer_instance

end PfaffianDescent.Coray
end
