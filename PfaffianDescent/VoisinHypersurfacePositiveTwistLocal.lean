import PfaffianDescent.VoisinHypersurfacePositiveTwist
import PfaffianDescent.GradedSurjection
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SheafificationTensorComparison
import PfaffianDescent.SchemeModuleTensorInverseContraction

/-!
# Local positive twists on a projective hypersurface

This file supplies the degree-one chart input which transfers the positive
twist construction from projective space to a projective hypersurface.
-/

noncomputable section
namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
namespace ProjectiveNegativeTwist

variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒢 : ℕ → ρ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]

/-- A surjective graded map transfers degree-one generation of the irrelevant
ideal to its target. -/
theorem gradedSurjective_irrelevant_le_span_degreeOne
    (f : 𝒢 →+*ᵍ ℋ) (hf : Function.Surjective f)
    (hspan : (HomogeneousIdeal.irrelevant 𝒢).toIdeal ≤
      Ideal.span (Set.range (fun g : 𝒢 1 => (g : A)))) :
    (HomogeneousIdeal.irrelevant ℋ).toIdeal ≤
      Ideal.span (Set.range (fun h : ℋ 1 => (h : B))) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn b hb
  obtain ⟨a, ha, hab⟩ := gradedSurjective_homogeneous_lift f hf n b hb
  rw [← hab]
  have haspan : a ∈ Ideal.span (Set.range (fun g : 𝒢 1 => (g : A))) :=
    hspan (HomogeneousIdeal.mem_irrelevant_of_mem 𝒢 hn ha)
  have hmap : (Ideal.span (Set.range (fun g : 𝒢 1 => (g : A)))).map
      f.toRingHom ≤ Ideal.span (Set.range (fun h : ℋ 1 => (h : B))) := by
    rw [Ideal.map_span]
    apply Ideal.span_mono
    rintro _ ⟨g, ⟨g', rfl⟩, rfl⟩
    exact ⟨⟨f g', f.2 g'.2⟩, rfl⟩
  exact hmap (Ideal.mem_map_of_mem f.toRingHom haspan)

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- Every positive twist of a homogeneous polynomial quotient is locally the
unit module on each of its homogeneous basic opens. -/
noncomputable def quotientPositiveTwistUnitIso_on_basicOpen
    (I : HomogeneousIdeal 𝒜) {d : ℕ} (s : grading I d) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen (grading I) (s : CoordinateRing I)).ι).obj
        (positiveSheafOfModules (grading I) d) ≅
      SheafOfModules.unit
        ((homogeneousBasicOpen (grading I) (s : CoordinateRing I) : Scheme).ringCatSheaf) :=
  restrictPositiveTwistUnitIso_on_basicOpen (grading I) s
    (gradedSurjective_irrelevant_le_span_degreeOne 𝒜 (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small)

/-- The standard coordinate open of a homogeneous projective quotient. -/
noncomputable def quotientCoordinateOpen
    (I : HomogeneousIdeal 𝒜) (j : σ) : (Proj (grading I)).Opens :=
  homogeneousBasicOpen (grading I) (coordinate I j)

/-- The quotient coordinate opens cover its projective scheme. -/
theorem quotientCoordinateOpen_iSup
    (I : HomogeneousIdeal 𝒜) :
    ⨆ j : σ, quotientCoordinateOpen I j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact (irrelevant_eq_coordinateIdeal I).le

/-- The intrinsic positive degree-one twist of a homogeneous quotient is the
unit module on each standard coordinate chart. -/
noncomputable def quotientCoordinatePositiveOneTwistUnitIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    (Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (positiveSheafOfModules (grading I) 1) ≅
      SheafOfModules.unit ((quotientCoordinateOpen I j : Scheme).ringCatSheaf) :=
  quotientPositiveTwistUnitIso_on_basicOpen I
    ⟨coordinate I j, coordinate_mem I j⟩

/-- Every intrinsic positive twist is the unit module on each standard
coordinate chart. -/
noncomputable def quotientCoordinatePositiveTwistUnitIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ) :
    (Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit ((quotientCoordinateOpen I j : Scheme).ringCatSheaf) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  induction m with
  | zero =>
      exact F.mapIso (positiveZeroTwistIso 𝓑) ≪≫
        (F.mapIso (unitIsoZeroTwist 𝓑)).symm ≪≫
          Scheme.Modules.restrictUnitIso U.ι
  | succ m ihm =>
      letI : IsIso (F.map (positiveMulHomogeneous 𝓑 s m)) :=
        restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s m hspan
      exact (asIso (F.map (positiveMulHomogeneous 𝓑 s m))).symm ≪≫ ihm

/-- The intrinsic negative degree-one twist of a homogeneous quotient is the
unit module on each standard coordinate chart. -/
noncomputable def quotientCoordinateNegativeOneTwistUnitIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    (Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (sheafOfModules (grading I) 1) ≅
      SheafOfModules.unit ((quotientCoordinateOpen I j : Scheme).ringCatSheaf) := by
  let F := Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι
  let s : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  letI : IsIso (F.map (mulHomogeneous (grading I) s 0)) :=
    restrict_mulHomogeneous_isIso_on_basicOpen (grading I) s 0
      (gradedSurjective_irrelevant_le_span_degreeOne 𝒜 (grading I)
        (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
        mvPolynomial_irrelevant_le_span_degreeOne_small)
  exact asIso (F.map (mulHomogeneous (grading I) s 0)) ≪≫
    (F.mapIso (unitIsoZeroTwist (grading I))).symm ≪≫
    Scheme.Modules.restrictUnitIso (quotientCoordinateOpen I j).ι

/-- Every intrinsic negative twist is the unit module on each standard
coordinate chart. -/
noncomputable def quotientCoordinateNegativeTwistUnitIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ) :
    (Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit ((quotientCoordinateOpen I j : Scheme).ringCatSheaf) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  induction m with
  | zero =>
      exact (F.mapIso (unitIsoZeroTwist 𝓑)).symm ≪≫
        Scheme.Modules.restrictUnitIso U.ι
  | succ m ihm =>
      letI : IsIso (F.map (mulHomogeneous 𝓑 s m)) :=
        restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s m hspan
      exact asIso (F.map (mulHomogeneous 𝓑 s m)) ≪≫ ihm

/-- On a quotient coordinate chart, the sheafification--tensor comparison is invertible for every positive twist. -/
theorem quotientCoordinatePositiveTwistComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ)
    (P : PresheafOfModules ((quotientCoordinateOpen I j : Scheme).ringCatSheaf).obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (positiveSheafOfModules (grading I) m))) := by
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit P
  exact quotientCoordinatePositiveTwistUnitIso_all I j m
/-- On a quotient coordinate chart, the sheafification--tensor comparison is invertible for every negative twist. -/
theorem quotientCoordinateNegativeTwistComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ)
    (P : PresheafOfModules ((quotientCoordinateOpen I j : Scheme).ringCatSheaf).obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (sheafOfModules (grading I) m))) := by
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit P
  exact quotientCoordinateNegativeTwistUnitIso_all I j m

/-- On the over-site of a quotient coordinate chart, the generic
sheafification--tensor comparison is invertible for every positive twist. -/
theorem quotientCoordinatePositiveTwistOverComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ)
    (P : PresheafOfModules (Proj (grading I)).ringCatSheaf.obj) :
    IsIso (SheafOfModules.commRingSheafTensorSheafificationRightComparison
      (SheafOfModules.commRingSheafOver (Proj (grading I)).sheaf
        (quotientCoordinateOpen I j))
      ((PresheafOfModules.pushforward
        (𝟙 ((Proj (grading I)).ringCatSheaf.over
          (quotientCoordinateOpen I j)).obj)).obj P)
      ((SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf
        (quotientCoordinateOpen I j)).obj
        (positiveSheafOfModules (grading I) m))) := by
  apply SheafOfModules.overFunctor_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j)
    (quotientCoordinatePositiveTwistUnitIso_all I j m)

/-- On the over-site of a quotient coordinate chart, the generic
sheafification--tensor comparison is invertible for every negative twist. -/
theorem quotientCoordinateNegativeTwistOverComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ)
    (P : PresheafOfModules (Proj (grading I)).ringCatSheaf.obj) :
    IsIso (SheafOfModules.commRingSheafTensorSheafificationRightComparison
      (SheafOfModules.commRingSheafOver (Proj (grading I)).sheaf
        (quotientCoordinateOpen I j))
      ((PresheafOfModules.pushforward
        (𝟙 ((Proj (grading I)).ringCatSheaf.over
          (quotientCoordinateOpen I j)).obj)).obj P)
      ((SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf
        (quotientCoordinateOpen I j)).obj
        (sheafOfModules (grading I) m))) := by
  apply SheafOfModules.overFunctor_commRingSheafTensorSheafificationRightComparison_isIso_of_iso_unit
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j)
    (quotientCoordinateNegativeTwistUnitIso_all I j m)

/-- On each standard coordinate chart, the tensor product of intrinsic
positive and negative degree-one twists is the unit module. -/
noncomputable def quotientCoordinatePositiveNegativeTensorUnitIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    (Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).obj
        (schemeModuleTensor (positiveSheafOfModules (grading I) 1)
          (sheafOfModules (grading I) 1)) ≅
      SheafOfModules.unit ((quotientCoordinateOpen I j : Scheme).ringCatSheaf) := by
  let U := quotientCoordinateOpen I j
  let E := Scheme.Modules.overEquiv U
  let F := SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf U
  let R := SheafOfModules.commRingSheafOver (Proj (grading I)).sheaf U
  let ePos := overFunctorIsoUnit_of_restrictIsoUnit U
    (quotientCoordinatePositiveOneTwistUnitIso I j)
  let eNeg := overFunctorIsoUnit_of_restrictIsoUnit U
    (quotientCoordinateNegativeOneTwistUnitIso I j)
  let eUnitOver := PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U
    (Iso.refl (SheafOfModules.unit (Proj (grading I)).ringCatSheaf))
  let n := Scheme.Modules.overFunctorEquiv U
  let uIso : E.functor.obj
      (SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf R)) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (E.functor.mapIso eUnitOver).symm ≪≫
      n.app (SheafOfModules.unit (Proj (grading I)).ringCatSheaf) ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  exact schemeModuleTensorRestrictOverIso U
    (positiveSheafOfModules (grading I) 1) (sheafOfModules (grading I) 1) ≪≫
    E.functor.mapIso
      ((SheafOfModules.commRingSheafTensorRightIsoUnit R eNeg).app
        (F.obj (positiveSheafOfModules (grading I) 1))) ≪≫
    E.functor.mapIso ePos ≪≫ uIso

/-- On every coordinate chart of a homogeneous quotient, the canonical pairing
between its positive and negative degree-one twists is an isomorphism. -/
theorem quotientCoordinatePositiveNegativePairing_isIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativePairing (grading I) 1)) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  letI : IsIso (F.map (positiveMulHomogeneous 𝓑 s 0)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s 0 hspan
  letI : IsIso (F.map (mulHomogeneous 𝓑 s 0)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s 0 hspan
  letI : IsIso (positiveNegativePairing 𝓑 0) :=
    positiveNegativePairing_zero_isIso 𝓑
  letI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous 𝓑 s 0)
      (𝟙 (sheafOfModules 𝓑 1)))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous 𝓑 s 0) (𝟙 (sheafOfModules 𝓑 1))
  letI : IsIso (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 0))
      (mulHomogeneous 𝓑 s 0))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (𝟙 (positiveSheafOfModules 𝓑 0)) (mulHomogeneous 𝓑 s 0)
  have h := congrArg F.map (positiveNegativePairing_mul_naturality 𝓑 s 0)
  rw [F.map_comp, F.map_comp] at h
  haveI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous 𝓑 s 0)
      (𝟙 (sheafOfModules 𝓑 1))) ≫
      F.map (positiveNegativePairing 𝓑 1)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (F.map (schemeModuleTensorMap (positiveMulHomogeneous 𝓑 s 0)
      (𝟙 (sheafOfModules 𝓑 1))))
    (F.map (positiveNegativePairing 𝓑 1))

/-- On a coordinate chart of a homogeneous quotient, the canonical pairing
between the degree-`m` positive and negative twists is an isomorphism for every
nonnegative `m`. -/
theorem quotientCoordinatePositiveNegativePairing_isIso_all
    (I : HomogeneousIdeal 𝒜) (j : σ) (m : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativePairing (grading I) m)) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  induction m with
  | zero =>
      letI : IsIso (positiveNegativePairing 𝓑 0) :=
        positiveNegativePairing_zero_isIso 𝓑
      exact inferInstance
  | succ m ihm =>
      letI : IsIso (F.map (positiveMulHomogeneous 𝓑 s m)) := by
        exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s m hspan
      letI : IsIso (F.map (mulHomogeneous 𝓑 s m)) := by
        exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s m hspan
      letI : IsIso (F.map (positiveNegativePairing 𝓑 m)) := ihm
      letI : IsIso (F.map (schemeModuleTensorMap
          (positiveMulHomogeneous 𝓑 s m)
          (𝟙 (sheafOfModules 𝓑 (m + 1))))) := by
        exact restrict_schemeModuleTensorMap_isIso_of_isIso U
          (positiveMulHomogeneous 𝓑 s m) (𝟙 (sheafOfModules 𝓑 (m + 1)))
      letI : IsIso (F.map (schemeModuleTensorMap
          (𝟙 (positiveSheafOfModules 𝓑 m))
          (mulHomogeneous 𝓑 s m))) := by
        exact restrict_schemeModuleTensorMap_isIso_of_isIso U
          (𝟙 (positiveSheafOfModules 𝓑 m)) (mulHomogeneous 𝓑 s m)
      have h := congrArg F.map (positiveNegativePairing_mul_naturality 𝓑 s m)
      rw [F.map_comp, F.map_comp] at h
      haveI : IsIso (F.map (schemeModuleTensorMap
          (positiveMulHomogeneous 𝓑 s m)
          (𝟙 (sheafOfModules 𝓑 (m + 1)))) ≫
          F.map (positiveNegativePairing 𝓑 (m + 1))) := by
        rw [h]
        infer_instance
      exact IsIso.of_isIso_comp_left
        (F.map (schemeModuleTensorMap (positiveMulHomogeneous 𝓑 s m)
          (𝟙 (sheafOfModules 𝓑 (m + 1)))))
        (F.map (positiveNegativePairing 𝓑 (m + 1)))

/-- A universe-lifted coordinate index for a projective polynomial quotient. -/
abbrev QuotientCoordinateIndex := ULift.{u} σ

/-- The quotient coordinate cover with its index in the ambient universe. -/
noncomputable def quotientCoordinateOpenLifted
    (I : HomogeneousIdeal 𝒜) (j : QuotientCoordinateIndex (σ := σ)) :
    (Proj (grading I)).Opens := quotientCoordinateOpen I j.down

/-- The lifted quotient coordinate family remains a cover. -/
theorem quotientCoordinateOpenLifted_iSup
    (I : HomogeneousIdeal 𝒜) :
    ⨆ j : QuotientCoordinateIndex (σ := σ), quotientCoordinateOpenLifted I j = ⊤ := by
  simpa [quotientCoordinateOpenLifted] using quotientCoordinateOpen_iSup I

/- The global sheafification--tensor comparison is invertible for every
positive twist on a homogeneous polynomial quotient. -/
theorem quotientPositiveTwistComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ)
    (P : PresheafOfModules (Proj (grading I)).ringCatSheaf.obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      (positiveSheafOfModules (grading I) m)) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop U hU
  intro j
  apply restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
  dsimp [U, quotientCoordinateOpenLifted]
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveTwistUnitIso_all I j.down m)

/- The global sheafification--tensor comparison is invertible for every
negative twist on a homogeneous polynomial quotient. -/
theorem quotientNegativeTwistComparison_isIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ)
    (P : PresheafOfModules (Proj (grading I)).ringCatSheaf.obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      (sheafOfModules (grading I) m)) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop U hU
  intro j
  apply restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
  dsimp [U, quotientCoordinateOpenLifted]
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinateNegativeTwistUnitIso_all I j.down m)

/-- The intrinsic positive and negative degree-one twists of a homogeneous
quotient are globally inverse under their canonical pairing. -/
theorem quotientPositiveNegativePairing_isIso (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativePairing (grading I) 1) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let F : ∀ j : QuotientCoordinateIndex (σ := σ),
      (Proj (grading I)).Modules ⥤
        SheafOfModules ((Proj (grading I)).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ j, IsIso ((F j).map (positiveNegativePairing (grading I) 1)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      letI : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativePairing (grading I) 1)) :=
        quotientCoordinatePositiveNegativePairing_isIso I j.down
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down) (positiveNegativePairing (grading I) 1)
  exact hF.isIso (positiveNegativePairing (grading I) 1)

/-- The intrinsic positive and negative degree-`m` twists of a homogeneous
quotient are globally inverse under their canonical pairing. -/
theorem quotientPositiveNegativePairing_isIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    IsIso (positiveNegativePairing (grading I) m) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let F : ∀ j : QuotientCoordinateIndex (σ := σ),
      (Proj (grading I)).Modules ⥤
        SheafOfModules ((Proj (grading I)).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ j, IsIso ((F j).map (positiveNegativePairing (grading I) m)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      letI : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativePairing (grading I) m)) :=
        quotientCoordinatePositiveNegativePairing_isIso_all I j.down m
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down) (positiveNegativePairing (grading I) m)
  exact hF.isIso (positiveNegativePairing (grading I) m)

/-- The canonical pairing packages the intrinsic negative degree-one twist
as an object-level tensor inverse to the positive twist on a homogeneous
polynomial quotient. -/
noncomputable def quotientPositiveNegativeTensorInverseIso
    (I : HomogeneousIdeal 𝒜) :
    schemeModuleTensor (positiveSheafOfModules (grading I) 1)
      (sheafOfModules (grading I) 1) ≅
      SheafOfModules.unit (Proj (grading I)).ringCatSheaf := by
  letI : IsIso (positiveNegativePairing (grading I) 1) :=
    quotientPositiveNegativePairing_isIso I
  exact asIso (positiveNegativePairing (grading I) 1) ≪≫
    (unitIsoZeroTwist (grading I)).symm

/-- The canonical pairing packages every intrinsic negative degree-`m` twist
as an object-level tensor inverse to the positive degree-`m` twist. -/
noncomputable def quotientPositiveNegativeTensorInverseIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    schemeModuleTensor (positiveSheafOfModules (grading I) m)
      (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Proj (grading I)).ringCatSheaf := by
  letI : IsIso (positiveNegativePairing (grading I) m) :=
    quotientPositiveNegativePairing_isIso_all I m
  exact asIso (positiveNegativePairing (grading I) m) ≪≫
    (unitIsoZeroTwist (grading I)).symm

/-- The reverse-order tensor product of the intrinsic negative and positive
 degree-`m` twists is also canonically the unit module. -/
noncomputable def quotientNegativePositiveTensorInverseIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    schemeModuleTensor (sheafOfModules (grading I) m)
      (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Proj (grading I)).ringCatSheaf :=
  schemeModuleTensorSymmetry (sheafOfModules (grading I) m)
    (positiveSheafOfModules (grading I) m) ≪≫
  quotientPositiveNegativeTensorInverseIso_all I m

/- Every left tensor of the raw positive--negative pairing becomes invertible
after sheafification.  This is the second compatibility needed to turn the
object-level inverse twists into an equivalence of module categories. -/
theorem quotientPositiveNegativePairingRaw_tensor_isIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ)
    (M : (Proj (grading I)).Modules) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (Proj (grading I)).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          (schemeModuleTensorPairingRaw
            (positiveSheafOfModules (grading I) m)
            (sheafOfModules (grading I) m)
            (quotientPositiveNegativeTensorInverseIso_all I m)))) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  apply schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop U hU
  · intro j
    dsimp [U, quotientCoordinateOpenLifted]
    exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down m)
  · intro j
    dsimp [U, quotientCoordinateOpenLifted]
    exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinateNegativeTwistUnitIso_all I j.down m)

/- Every left tensor of the reverse raw negative--positive pairing becomes
invertible after sheafification. -/
theorem quotientNegativePositivePairingRaw_tensor_isIso_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ)
    (M : (Proj (grading I)).Modules) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (Proj (grading I)).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
          (schemeModuleTensorPairingRaw
            (sheafOfModules (grading I) m)
            (positiveSheafOfModules (grading I) m)
            (quotientNegativePositiveTensorInverseIso_all I m)))) := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  apply schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop U hU
  · intro j
    dsimp [U, quotientCoordinateOpenLifted]
    exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinateNegativeTwistUnitIso_all I j.down m)
  · intro j
    dsimp [U, quotientCoordinateOpenLifted]
    exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down m)

/- Tensoring on the right by the intrinsic positive degree-`m` twist is an
equivalence, with inverse given by the intrinsic negative degree-`m` twist. -/
noncomputable def quotientTwistTensorRightEquivalence_all
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    (Proj (grading I)).Modules ≌ (Proj (grading I)).Modules :=
  schemeModuleTensorRightEquivalenceOfInversePairings
    (positiveSheafOfModules (grading I) m)
    (sheafOfModules (grading I) m)
    (quotientPositiveNegativeTensorInverseIso_all I m)
    (quotientNegativePositiveTensorInverseIso_all I m)
    (fun M => quotientNegativeTwistComparison_isIso_all I m
      (PresheafOfModules.Monoidal.tensorObj M.val
        (positiveSheafOfModules (grading I) m).val))
    (quotientPositiveNegativePairingRaw_tensor_isIso_all I m)
    (fun M => quotientPositiveTwistComparison_isIso_all I m
      (PresheafOfModules.Monoidal.tensorObj M.val
        (sheafOfModules (grading I) m).val))
    (quotientNegativePositivePairingRaw_tensor_isIso_all I m)

/-- Tensoring by the intrinsic positive degree-one twist of a homogeneous
polynomial quotient preserves finite limits. -/
theorem quotientPositiveOne_tensorRight_preservesFiniteLimits
    (I : HomogeneousIdeal 𝒜) :
    PreservesFiniteLimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) 1)) := by
  apply schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveOneTwistUnitIso I j.down)

/-- Tensoring by the intrinsic positive degree-one twist of a homogeneous
polynomial quotient preserves finite colimits. -/
theorem quotientPositiveOne_tensorRight_preservesFiniteColimits
    (I : HomogeneousIdeal 𝒜) :
    PreservesFiniteColimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) 1)) := by
  apply schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveOneTwistUnitIso I j.down)

/-- Tensoring by any intrinsic positive twist of a homogeneous polynomial
quotient preserves finite limits. -/
theorem quotientPositiveTwist_tensorRight_preservesFiniteLimits
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    PreservesFiniteLimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) m)) := by
  apply schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveTwistUnitIso_all I j.down m)

/-- Tensoring by any intrinsic positive twist of a homogeneous polynomial
quotient preserves finite colimits. -/
theorem quotientPositiveTwist_tensorRight_preservesFiniteColimits
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    PreservesFiniteColimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) m)) := by
  apply schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveTwistUnitIso_all I j.down m)

/-- The ideal-sheaf sequence of every closed subscheme of a homogeneous
projective quotient remains short exact after tensoring with its intrinsic
positive twist.  This records the local-triviality argument in the precise
form used by the degree-eleven Serre construction. -/
theorem quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact
    (I : HomogeneousIdeal 𝒜) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (grading I)) [IsClosedImmersion i] (m : ℕ) :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) m)).ShortExact := by
  let : PreservesFiniteLimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) m)) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits I m
  let : PreservesFiniteColimits
      (schemeModuleTensorRight (positiveSheafOfModules (grading I) m)) :=
    quotientPositiveTwist_tensorRight_preservesFiniteColimits I m
  exact closedImmersionIdealTwistSequence_shortExact i
    (positiveSheafOfModules (grading I) m)

/-- Tensoring by any intrinsic negative twist of a homogeneous polynomial
quotient preserves finite limits. -/
theorem quotientNegativeTwist_tensorRight_preservesFiniteLimits
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    PreservesFiniteLimits
      (schemeModuleTensorRight (sheafOfModules (grading I) m)) := by
  apply schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinateNegativeTwistUnitIso_all I j.down m)

/-- Tensoring by any intrinsic negative twist of a homogeneous polynomial
quotient preserves finite colimits. -/
theorem quotientNegativeTwist_tensorRight_preservesFiniteColimits
    (I : HomogeneousIdeal 𝒜) (m : ℕ) :
    PreservesFiniteColimits
      (schemeModuleTensorRight (sheafOfModules (grading I) m)) := by
  apply schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit
    (quotientCoordinateOpenLifted I) (by
      rw [Opens.coversTop_iff]
      exact quotientCoordinateOpenLifted_iSup I)
  intro j
  exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
    (quotientCoordinateNegativeTwistUnitIso_all I j.down m)

end ProjectiveNegativeTwist
end PfaffianDescent
