import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! # Actual inverse-twist tensor equivalence on projective three-space

The positive and negative sheaves are the native projective twist models.
Their actual pairing is invertible on the coordinate cover, and the local
units supply the tensor/sheafification compatibility needed for an equivalence.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem p3CoordinatePositiveNegativePairing_isIso (j : Fin 4) (m : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (positiveNegativePairing PS m)) := by
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := p3Coordinate K j
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : MvPolynomial (Fin 4) K))) :=
    (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨p3Coordinate K i, rfl⟩))
  induction m with
  | zero =>
      letI : IsIso (positiveNegativePairing PS 0) := positiveNegativePairing_zero_isIso PS
      exact inferInstance
  | succ m ihm =>
      letI : IsIso (F.map (positiveMulHomogeneous PS s m)) :=
        restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s m hspan
      letI : IsIso (F.map (mulHomogeneous PS s m)) :=
        restrict_mulHomogeneous_isIso_on_basicOpen PS s m hspan
      letI : IsIso (F.map (positiveNegativePairing PS m)) := ihm
      letI : IsIso (F.map (schemeModuleTensorMap
          (positiveMulHomogeneous PS s m) (𝟙 (sheafOfModules PS (m + 1))))) :=
        restrict_schemeModuleTensorMap_isIso_of_isIso U
          (positiveMulHomogeneous PS s m) (𝟙 (sheafOfModules PS (m + 1)))
      letI : IsIso (F.map (schemeModuleTensorMap
          (𝟙 (positiveSheafOfModules PS m)) (mulHomogeneous PS s m))) :=
        restrict_schemeModuleTensorMap_isIso_of_isIso U
          (𝟙 (positiveSheafOfModules PS m)) (mulHomogeneous PS s m)
      have h := congrArg F.map (positiveNegativePairing_mul_naturality PS s m)
      rw [F.map_comp, F.map_comp] at h
      haveI : IsIso (F.map (schemeModuleTensorMap
          (positiveMulHomogeneous PS s m) (𝟙 (sheafOfModules PS (m + 1)))) ≫
          F.map (positiveNegativePairing PS (m + 1))) := by
        rw [h]
        infer_instance
      exact IsIso.of_isIso_comp_left
        (F.map (schemeModuleTensorMap (positiveMulHomogeneous PS s m)
          (𝟙 (sheafOfModules PS (m + 1)))))
        (F.map (positiveNegativePairing PS (m + 1)))

theorem p3PositiveNegativePairing_isIso (m : ℕ) :
    IsIso (positiveNegativePairing PS m) := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U
      (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map (positiveNegativePairing PS m)) := fun j => by
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (p3StandardOpen (K := K) j.down).ι).map (positiveNegativePairing PS m)) :=
      p3CoordinatePositiveNegativePairing_isIso K j.down m
    exact overFunctorMap_isIso_of_restrictMap_isIso
      (p3StandardOpen (K := K) j.down) (positiveNegativePairing PS m)
  exact hF.isIso (positiveNegativePairing PS m)

def p3PositiveNegativeTensorInverseIso (m : ℕ) :
    schemeModuleTensor (positiveSheafOfModules PS m) (sheafOfModules PS m) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf := by
  letI := p3PositiveNegativePairing_isIso K m
  exact asIso (positiveNegativePairing PS m) ≪≫ (unitIsoZeroTwist PS).symm

def p3NegativePositiveTensorInverseIso (m : ℕ) :
    schemeModuleTensor (sheafOfModules PS m) (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
  schemeModuleTensorSymmetry _ _ ≪≫ p3PositiveNegativeTensorInverseIso K m

private def positiveLocalUnit (j : P3CoordinateIndex) (m : ℕ) :=
  overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) j.down)
    (p3PositiveTwistOpenIsoUnit K (p3StandardOpen (K := K) j.down) j.down le_rfl m)

private def negativeLocalUnit (j : P3CoordinateIndex) (m : ℕ) :=
  overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) j.down)
    (p3NegativeTwistOpenIsoUnit K (p3StandardOpen (K := K) j.down) j.down le_rfl m)

private theorem positiveComparison (m : ℕ)
    (P : PresheafOfModules (Proj PS).ringCatSheaf.obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      (positiveSheafOfModules PS m)) := by
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop
    (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
  intro j
  apply restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
  exact positiveLocalUnit K j m

private theorem negativeComparison (m : ℕ)
    (P : PresheafOfModules (Proj PS).ringCatSheaf.obj) :
    IsIso (schemeModuleTensorSheafificationRightComparison P
      (sheafOfModules PS m)) := by
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop
    (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
  intro j
  apply restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
  exact negativeLocalUnit K j m

/-- Tensoring by the actual negative twist, with the actual positive twist
as inverse. This has no supplied inverse-pairing or exactness premise. -/
def p3TwistTensorRightEquivalence (m : ℕ) : (Proj PS).Modules ≌ (Proj PS).Modules :=
  schemeModuleTensorRightEquivalenceOfInversePairings
    (positiveSheafOfModules PS m) (sheafOfModules PS m)
    (p3PositiveNegativeTensorInverseIso K m) (p3NegativePositiveTensorInverseIso K m)
    (fun M => negativeComparison K m (PresheafOfModules.Monoidal.tensorObj
      M.val (positiveSheafOfModules PS m).val))
    (fun M => schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop
      (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
      M _ _ (p3PositiveNegativeTensorInverseIso K m)
      (fun j => positiveLocalUnit K j m) (fun j => negativeLocalUnit K j m))
    (fun M => positiveComparison K m (PresheafOfModules.Monoidal.tensorObj
      M.val (sheafOfModules PS m).val))
    (fun M => schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop
      (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
      M _ _ (p3NegativePositiveTensorInverseIso K m)
      (fun j => negativeLocalUnit K j m) (fun j => positiveLocalUnit K j m))

end PfaffianDescent.ProjectiveNegativeTwist
