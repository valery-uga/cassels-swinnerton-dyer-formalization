import PfaffianDescent.ActualPositiveGradedHomogeneousSectionPullback
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.CorayCartierCanonicalProjectionFormula
import PfaffianDescent.CorayActualWholeIdealTwistRankOne172
import PfaffianDescent.HomogeneousQuotientMap

/-! Actual homogeneous quotient-ideal elements lie in the SAME native
ideal-twist restriction kernel. Whole ideals and all nonnegative degrees
are retained. No H0 dictionary or vanishing certificate is an input.
SOURCE ONLY: compiler acceptance remains pending. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing linear map is literally the homogeneous-section morphism. -/
lemma planeHomogeneousGlobalSectionLinearMap_apply
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (d : ℕ) (a : grading I d) :
    positiveHomogeneousGlobalSectionLinearMap I d a =
      (positiveSheafOfModules (grading I) d).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) d a) := by
  change (positiveSheafOfModules (grading I) d).unitHomEquiv.symm
      ((schemeModuleSectionsEquivTop (positiveSheafOfModules (grading I) d)).symm
        ((schemeModuleSectionsEquivTop (positiveSheafOfModules (grading I) d))
          (positiveGlobalSectionOfHomogeneous (grading I) d a))) = _
  rw [Equiv.symm_apply_apply]

/-- Ideal membership in the literal quotient ideal kills the SAME graded
quotient coordinate, without radicalization or saturation. -/
lemma wholePlaneQuotientIdeal_coordinate_eq_zero
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (a : CoordinateRing I)
    (ha : a ∈ J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) :
    coordinateQuotientMap I J hIJ a = 0 := by
  obtain ⟨p, hp, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I.toIdeal)
      Ideal.Quotient.mk_surjective).mp ha
  rw [coordinateQuotientMap_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

/-- The actual graded positive restriction adjunct is an Iso, derived
internally from polynomial degree-one generation in BOTH quotient rings. -/
lemma planeQuotientPositiveGradedPullbackHom_isIso
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
      (grading I) (grading J) (gradedQuotientMap I J hIJ)
      (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
        (gradedQuotientMap_surjective I J hIJ)) d) := by
  apply cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_isIso
  · exact gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 3) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  · exact gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 3) K) (grading J)
      (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
      mvPolynomial_irrelevant_le_span_degreeOne_small

/-- The pushforward comparison is the unit followed by the pushforward
of its actual pullback adjunct. This is the genuine adjunction identity. -/
lemma planeQuotientPositivePushforward_eq_unit_comp
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    let f := gradedQuotientMap I J hIJ
    let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective I J hIJ)
    gradedRingHomPositiveTwistToPushforward (grading I) (grading J) f hf d =
      (Scheme.Modules.pullbackPushforwardAdjunction (schemeQuotientMap I J hIJ)).unit.app
        (positiveSheafOfModules (grading I) d) ≫
      (Scheme.Modules.pushforward (schemeQuotientMap I J hIJ)).map
        (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
          (grading I) (grading J) f hf d) := by
  dsimp only
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (schemeQuotientMap I J hIJ)
  exact ((adj.homEquiv _ _).apply_symm_apply _).symm

/-- A literal whole quotient-ideal homogeneous element is killed by the
SAME native tensor ideal sequence quotient map. This derives, rather than
assumes, the section-level kernel condition. -/
theorem wholePlaneQuotientIdeal_homogeneousSection_nativeRestriction_zero
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) (a : grading I d)
    (ha : (a : CoordinateRing I) ∈ J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    positiveHomogeneousGlobalSectionLinearMap I d a ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules (grading I) d)).inv ≫
      (closedImmersionIdealTwistSequence (schemeQuotientMap I J hIJ)
        (positiveSheafOfModules (grading I) d)).g = 0 := by
  let i := schemeQuotientMap I J hIJ
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I J hIJ
  let T := positiveSheafOfModules (grading I) d
  let f := gradedQuotientMap I J hIJ
  let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective I J hIJ)
  let c := cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
    (grading I) (grading J) f hf d
  let P := Scheme.Modules.pushforward i
  let s := positiveHomogeneousGlobalSectionLinearMap I d a
  let e := schemeModuleTensorUnitLeftIso T
  let S := closedImmersionIdealTwistSequence i T
  let pr := schemeModuleCanonicalFiberProjection i T
  letI : IsIso pr := schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne
    i T (planePositiveTwist_locallyRankOne172 I d)
  letI : IsIso c := planeQuotientPositiveGradedPullbackHom_isIso I J hIJ d
  have ha0 : (⟨f a, f.map_mem a.property⟩ : grading J d) = 0 :=
    Subtype.ext (wholePlaneQuotientIdeal_coordinate_eq_zero I J hIJ a ha)
  have hb : s ≫ gradedRingHomPositiveTwistToPushforward
      (grading I) (grading J) f hf d = 0 := by
    let g : Proj (grading J) ⟶ Proj (grading I) := Proj.map f hf
    let F : (Proj (grading J)).Modules ⥤ (Proj (grading I)).Modules :=
      Scheme.Modules.pushforward g
    let TJ : (Proj (grading J)).Modules := positiveSheafOfModules (grading J) d
    let t : SheafOfModules.unit (Proj (grading J)).ringCatSheaf ⟶ TJ :=
      TJ.unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading J) d ⟨f a, f.map_mem a.property⟩)
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit g
    have hs : s = T.unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) d a) :=
      planeHomogeneousGlobalSectionLinearMap_apply I d a
    have ht : t = 0 :=
      (planeHomogeneousGlobalSectionLinearMap_apply J d
        ⟨f a, f.map_mem a.property⟩).symm.trans
        ((congrArg (fun b : grading J d => positiveHomogeneousGlobalSectionLinearMap J d b)
          ha0).trans (map_zero (positiveHomogeneousGlobalSectionLinearMap J d)))
    calc
      _ = T.unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading I) d a) ≫
          gradedRingHomPositiveTwistToPushforward (grading I) (grading J) f hf d :=
        congrArg (fun v : SheafOfModules.unit (Proj (grading I)).ringCatSheaf ⟶ T =>
          v ≫ gradedRingHomPositiveTwistToPushforward (grading I) (grading J) f hf d) hs
      _ = q ≫ F.map t :=
        actualPositiveGradedHomogeneousSection_pushforward (grading I) (grading J) f hf d a
      _ = q ≫ F.map (0 : SheafOfModules.unit (Proj (grading J)).ringCatSheaf ⟶ TJ) :=
        congrArg (fun v : SheafOfModules.unit (Proj (grading J)).ringCatSheaf ⟶ TJ =>
          q ≫ F.map v) ht
      _ = q ≫ (0 : F.obj (SheafOfModules.unit (Proj (grading J)).ringCatSheaf) ⟶ F.obj TJ) :=
        congrArg (fun v : F.obj (SheafOfModules.unit (Proj (grading J)).ringCatSheaf) ⟶ F.obj TJ =>
          q ≫ v) (F.map_zero _ _)
      _ = 0 := comp_zero
  apply (cancel_mono (pr ≫ P.map c)).mp
  rw [zero_comp]
  change (s ≫ e.inv ≫ S.g) ≫ (pr ≫ P.map c) = 0
  have hp := schemeModuleCanonicalFiberProjection_unit_square i T
  change S.g ≫ pr = e.hom ≫
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T at hp
  calc
    _ = s ≫ e.inv ≫ (S.g ≫ pr) ≫ P.map c := by simp only [Category.assoc]
    _ = s ≫ e.inv ≫ (e.hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T) ≫ P.map c := by
      rw [hp]
    _ = s ≫ ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫ P.map c) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = s ≫ gradedRingHomPositiveTwistToPushforward (grading I) (grading J) f hf d := by
      rw [← planeQuotientPositivePushforward_eq_unit_comp I J hIJ d]
    _ = 0 := hb

end PfaffianDescent.Coray
end
