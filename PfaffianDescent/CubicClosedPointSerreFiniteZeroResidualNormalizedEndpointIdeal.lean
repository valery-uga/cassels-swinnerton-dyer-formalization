import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointChart
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

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedCanonicalCoordinate_pullback
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (C.projectiveLineOpenCover f).I₀) (k : ULift.{u} (Fin 2)) :
    sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
      (C.projectiveLineLocalFreeIso f ij) (C.projectiveLineLocalCanonicalSection f ij) k =
    (C.projectiveLineOpenCover_toLocalScheme f ij).appTop
      (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
        (localFreeIsoOfOver (C.U ij.1) (ULift.{u} (Fin 2)) (C.trivialization ij.1))
        (restrictSectionToOpen (C.U ij.1) e.canonicalSection) k) := by
  exact cubicClosedPointSerreFiniteZeroResidual_native_pullback_coordinate
    (C.projectiveLineOpenCover_toLocalScheme f ij) _ _ _ k

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_sectionCoordinate
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (k : ULift.{u} (Fin 2)) :
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i false).appTop
      (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
        (C.projectiveLineLocalFreeIso f (i, false))
        (C.projectiveLineNormalizedLocalPencilSection f seed (i, false)) k) =
    sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
      (localFreeIsoOfOver (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i))
      (restrictSectionToOpen (C.U i) e.canonicalSection) k := by
  rw [C.projectiveLineNormalizedLocalPencilCoordinate_of_eq_false f seed (i, false) rfl k,
    C.unitEndomorphismValue_projectiveLineLocalCoordinateCoefficient f (i, false)]
  have hu : unitEndomorphismValue (𝟙 (SheafOfModules.unit
      ((C.projectiveLineOpenCover f).X (i, false)).ringCatSheaf)) = 1 := by
    simp [unitEndomorphismValue, unitSectionAtTop]
  rw [hu, one_mul, map_add, map_mul,
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_coordinate,
    zero_mul, add_zero,
    cubicClosedPointSerreFiniteZeroResidual_normalizedCanonicalCoordinate_pullback]
  have hq := congrArg (fun a : (C.U i : Scheme.{u}) ⟶ C.U i => a.appTop.hom)
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toSurface f C i false)
  rw [Scheme.Hom.comp_appTop] at hq
  exact RingHom.congr_fun hq _

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_ideal
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    (C.projectiveLineNormalizedLocalPencilZeroIdeal f seed (i, false)).comap
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i false) =
    C.localPencilZeroIdeal e seed i (𝟙 _) 0 := by
  letI : IsAffine (C.U i : Scheme.{u}) := C.affine i
  letI : IsAffine ((C.projectiveLineOpenCover f).X (i, false)) := inferInstance
  rw [C.projectiveLineNormalizedLocalPencilZeroIdeal_eq_twoCoordinates f seed,
    cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap,
    Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_singleton]
  rw [cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_sectionCoordinate,
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_sectionCoordinate,
    C.localPencilZeroIdeal_one_zero e seed]
  unfold localSectionZeroIdealOfOver
  exact (sectionZeroIdealOfFreeIso_ulift_fin_two_eq _ _).symm

end
end PfaffianDescent
