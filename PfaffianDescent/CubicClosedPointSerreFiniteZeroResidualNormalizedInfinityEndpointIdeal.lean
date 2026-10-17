import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointIdeal
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativePullbackCoordinate
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineIdealComap

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedLiftCoordinate_pullback
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij : (C.projectiveLineOpenCover f).I₀) (k : ULift.{u} (Fin 2)) :
    sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
      (C.projectiveLineLocalFreeIso f ij) (C.projectiveLineLocalLiftSection f seed ij) k =
    (C.projectiveLineOpenCover_toLocalScheme f ij).appTop
      (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
        (localFreeIsoOfOver (C.U ij.1) (ULift.{u} (Fin 2)) (C.trivialization ij.1))
        (restrictSectionToOpen (C.U ij.1) seed.lift) k) := by
  exact cubicClosedPointSerreFiniteZeroResidual_native_pullback_coordinate
    (C.projectiveLineOpenCover_toLocalScheme f ij) _ _ _ k

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpointChart_sectionCoordinate
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (k : ULift.{u} (Fin 2)) :
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i true).appTop
      (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
        (C.projectiveLineLocalFreeIso f (i, true))
        (C.projectiveLineNormalizedLocalPencilSection f seed (i, true)) k) =
    sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
      (localFreeIsoOfOver (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i))
      (restrictSectionToOpen (C.U i) seed.lift) k := by
  rw [C.projectiveLineNormalizedLocalPencilCoordinate_of_eq_true f seed (i, true) rfl k,
    C.unitEndomorphismValue_projectiveLineLocalCoordinateCoefficient f (i, true)]
  have hu : unitEndomorphismValue (𝟙 (SheafOfModules.unit
      ((C.projectiveLineOpenCover f).X (i, true)).ringCatSheaf)) = 1 := by
    simp [unitEndomorphismValue, unitSectionAtTop]
  rw [hu, one_mul, map_add, map_mul,
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_coordinate,
    zero_mul, zero_add,
    cubicClosedPointSerreFiniteZeroResidual_normalizedLiftCoordinate_pullback]
  have hq := congrArg (fun a : (C.U i : Scheme.{u}) ⟶ C.U i => a.appTop.hom)
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toSurface f C i true)
  rw [Scheme.Hom.comp_appTop] at hq
  exact RingHom.congr_fun hq _

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpointChart_ideal
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    (C.projectiveLineNormalizedLocalPencilZeroIdeal f seed (i, true)).comap
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i true) =
    C.localPencilZeroIdeal e seed i 0 (𝟙 _) := by
  letI : IsAffine (C.U i : Scheme.{u}) := C.affine i
  letI : IsAffine ((C.projectiveLineOpenCover f).X (i, true)) := inferInstance
  rw [C.projectiveLineNormalizedLocalPencilZeroIdeal_eq_twoCoordinates f seed,
    cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap,
    Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_singleton]
  rw [cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpointChart_sectionCoordinate,
    cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpointChart_sectionCoordinate,
    C.localPencilZeroIdeal_zero_one e seed]
  unfold localSectionZeroIdealOfOver
  exact (sectionZeroIdealOfFreeIso_ulift_fin_two_eq _ _).symm

end
end PfaffianDescent
