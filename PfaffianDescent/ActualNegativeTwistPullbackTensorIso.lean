import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import PfaffianDescent.CubicClosedPointSerreTensorStalkGeneratorIso
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso

/-! SOURCE ONLY / UNVERIFIED. Negative twists have genuine global maps to
unit that are invertible on coordinate opens. These derive the actual
negative-factor pullback tensor comparison, without a supplied Iso premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplication by the m-th coordinate power, from native O(-m) to O. -/
def actualNegativeTwistChartUnitHom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    sheafOfModules (grading I) m ⟶ SheafOfModules.unit (scheme I).ringCatSheaf := by
  induction m with
  | zero => exact (unitIsoZeroTwist (grading I)).inv
  | succ m ihm =>
      exact mulHomogeneous (grading I) ⟨coordinate I j, coordinate_mem I j⟩ m ≫ ihm

set_option backward.isDefEq.respectTransparency false in
theorem actualNegativeTwistChartUnitHom_restrict_isIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (actualNegativeTwistChartUnitHom I j m)) := by
  let F := Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι
  let s : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading I 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  induction m with
  | zero =>
      change IsIso (F.map (unitIsoZeroTwist (grading I)).inv)
      infer_instance
  | succ m ihm =>
      letI : IsIso (F.map (mulHomogeneous (grading I) s m)) :=
        restrict_mulHomogeneous_isIso_on_basicOpen (grading I) s m hspan
      letI : IsIso (F.map (actualNegativeTwistChartUnitHom I j m)) := ihm
      change IsIso (F.map (mulHomogeneous (grading I) s m ≫
        actualNegativeTwistChartUnitHom I j m))
      rw [F.map_comp]
      infer_instance

/- The dual direction of the ordinary generator argument: genuine maps
N→O that are locally invertible also reduce comparison to its unit case. -/
set_option backward.isDefEq.respectTransparency false in
private theorem pullbackTensorMap_isIso_of_cogenerators
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    [IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (SheafOfModules.unit Y.ringCatSheaf))]
    (hgen : ∀ x : X, ∃ (U : Y.Opens) (g : N ⟶ SheafOfModules.unit Y.ringCatSheaf),
      f x ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N) := by
  apply schemeModuleMap_isIso_of_stalk
  intro x
  obtain ⟨U, g, hxU, hg⟩ := hgen x
  letI := hg
  let V := f ⁻¹ᵁ U
  let xv : V := ⟨x, hxU⟩
  let P := Scheme.Modules.pullback f
  let S := schemeModuleStalkModuleFunctor X x
  let a := P.map (schemeModuleTensorMap (𝟙 M) g)
  let b := schemeModuleTensorMap (P.map (𝟙 M)) (P.map g)
  let c := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (SheafOfModules.unit Y.ringCatSheaf)
  let d := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N
  letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (schemeModuleTensorMap (𝟙 M) g)) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U (𝟙 M) g
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map a) :=
    cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso f U V le_rfl
      (schemeModuleTensorMap (𝟙 M) g)
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (P.map g)) :=
    cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso f U V le_rfl g
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map b) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso V (P.map (𝟙 M)) (P.map g)
  letI : IsIso (S.map a) :=
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V xv a
  letI : IsIso (S.map b) :=
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V xv b
  have h : a ≫ c = d ≫ b :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f (𝟙 M) g
  have hS : S.map a ≫ S.map c = S.map d ≫ S.map b := by
    simpa only [Functor.map_comp] using congrArg S.map h
  letI : IsIso (S.map d ≫ S.map b) := by
    rw [← hS]
    infer_instance
  exact IsIso.of_isIso_comp_right (S.map d) (S.map b)

set_option backward.isDefEq.respectTransparency false in
theorem actualNegativeTwist_pullbackTensorMap_isIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (sheafOfModules (grading I) m)) := by
  letI := cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  apply pullbackTensorMap_isIso_of_cogenerators
  intro x
  have hx : f x ∈ ⨆ j : Fin 4, quotientCoordinateOpen I j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨quotientCoordinateOpen I j, actualNegativeTwistChartUnitHom I j m, hj,
    actualNegativeTwistChartUnitHom_restrict_isIso I j m⟩

def actualNegativeTwistPullbackTensorIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (schemeModuleTensor M (sheafOfModules (grading I) m)) ≅
      schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj (sheafOfModules (grading I) m)) := by
  letI := actualNegativeTwist_pullbackTensorMap_isIso I f M m
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (sheafOfModules (grading I) m))

lemma actualNegativeTwistPullbackTensorIso_hom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    (actualNegativeTwistPullbackTensorIso I f M m).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (sheafOfModules (grading I) m) := rfl

end PfaffianDescent
