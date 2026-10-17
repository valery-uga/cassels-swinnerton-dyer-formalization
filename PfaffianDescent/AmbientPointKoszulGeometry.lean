import PfaffianDescent.PointGlobalTraceP3CoordinateKoszul
import PfaffianDescent.IdealSheafModule
import AllCharacteristics.AmbientChartPresentation
import Mathlib.Data.Fin.VecNotation

/-! # The actual standard point and augmentation on projective three-space

The point is constructed by evaluating the actual `X0` chart at
`[1,0,0,0]`. Its augmentation is the canonical structure-sheaf restriction
map of that closed immersion. We also verify monomorphy of the actual
leftmost global Koszul differential.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The normalized vector defining the standard coordinate point. -/
def ambientPointKoszul_vector : Fin 4 → K := ![1, 0, 0, 0]

/-- Evaluation at the standard point on the actual `X0` ambient chart. -/
def ambientPointKoszul_chartMap : Away PS (X (0 : Fin 4)) →+* K :=
  AllCharacteristics.GradedChart.liftCoordinateOne PS (X (0 : Fin 4))
    (eval₂Hom (RingHom.id K) (ambientPointKoszul_vector K)) (by simp [ambientPointKoszul_vector])

/-- The chart evaluation preserves the coefficient field. -/
theorem ambientPointKoszul_chartMap_base (a : K) :
    ambientPointKoszul_chartMap K
      (AllCharacteristics.GradedChart.baseMap PS (z := X (0 : Fin 4)) a) = a :=
  (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap PS (X (0 : Fin 4))
    (eval₂Hom (RingHom.id K) (ambientPointKoszul_vector K)) _ a).trans
      (eval₂Hom_C _ _ a)

/-- Normalized projective coordinates have the values `[1,0,0,0]`. -/
theorem ambientPointKoszul_chartMap_coordinate (i : Fin 4) :
    ambientPointKoszul_chartMap K (ambientChartCoordinate (R := K) 0 i) =
      ambientPointKoszul_vector K i :=
  (AllCharacteristics.GradedChart.liftCoordinateOne_normalized PS (X (0 : Fin 4))
    (eval₂Hom (RingHom.id K) (ambientPointKoszul_vector K)) _
    (isHomogeneous_X K 0) (X i) (isHomogeneous_X K i)).trans
      (eval₂Hom_X' _ _ i)

/-- The actual standard rational point `[1,0,0,0]` of `P3`. -/
def ambientPointKoszul_point : Spec (.of K) ⟶ Proj PS :=
  Spec.map (CommRingCat.ofHom (ambientPointKoszul_chartMap K)) ≫
    Proj.awayι PS (X (0 : Fin 4)) (isHomogeneous_X K 0) (by decide : 0 < 1)

set_option backward.isDefEq.respectTransparency false in
/-- The standard point is a section of the coefficient structure map. -/
theorem ambientPointKoszul_point_toBase :
    ambientPointKoszul_point K ≫ ambientToBase = 𝟙 (Spec (.of K)) := by
  unfold ambientPointKoszul_point ambientToBase
  rw [Category.assoc, ← Category.assoc
    (Proj.awayι PS (X (0 : Fin 4)) (isHomogeneous_X K 0) (by decide : 0 < 1)),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  have h : (ambientPointKoszul_chartMap K).comp
      (AllCharacteristics.GradedChart.baseMap PS (z := X (0 : Fin 4))) =
        RingHom.id K := by
    ext a
    exact ambientPointKoszul_chartMap_base K a
  change Spec.map (CommRingCat.ofHom ((ambientPointKoszul_chartMap K).comp
    (AllCharacteristics.GradedChart.baseMap PS (z := X (0 : Fin 4))))) = _
  rw [h]
  exact Spec.map_id _

/-- The actual coordinate point is a closed immersion. -/
instance ambientPointKoszul_point_isClosedImmersion :
    IsClosedImmersion (ambientPointKoszul_point K) :=
  isClosedImmersion_of_comp_eq_id ambientToBase (ambientPointKoszul_point K)
    (ambientPointKoszul_point_toBase K)

/-- The standard point lies in the point-containing `X0` chart. -/
theorem ambientPointKoszul_point_mem_basicOpen (x : Spec (.of K)) :
    ambientPointKoszul_point K x ∈ Proj.basicOpen PS (X (0 : Fin 4)) := by
  rw [← Proj.opensRange_awayι PS (X (0 : Fin 4))
    (isHomogeneous_X K 0) (by decide : 0 < 1)]
  exact ⟨_, rfl⟩

/-- The actual point structure sheaf pushed forward to `P3`. -/
abbrev ambientPointKoszul_pointModule : (Proj PS).Modules :=
  (Scheme.Modules.pushforward (ambientPointKoszul_point K)).obj
    (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)

/-- The actual augmentation `O -> i_* K` is closed-immersion restriction. -/
def ambientPointKoszul_augmentation :
    SheafOfModules.unit (Proj PS).ringCatSheaf ⟶ ambientPointKoszul_pointModule K :=
  IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (ambientPointKoszul_point K)

/-- The actual point augmentation is epimorphic. -/
instance ambientPointKoszul_augmentation_epi : Epi (ambientPointKoszul_augmentation K) := by
  unfold ambientPointKoszul_augmentation
  infer_instance

namespace ProjectiveNegativeTwist

/-- The actual leftmost coordinate Koszul differential is a monomorphism. -/
theorem ambientPointKoszul_first_mono :
    Mono (pointGlobalTraceP3CoordinateKoszulFirst K) := by
  haveI : Mono (pointGlobalTraceP3CoordinateMul K 1 2) :=
    mulHomogeneous_mono PS ⟨X (1 : Fin 4), isHomogeneous_X K 1⟩ (by simp) 2
  have h : pointGlobalTraceP3CoordinateKoszulFirst K ≫
      biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3) =
        pointGlobalTraceP3CoordinateMul K 1 2 := by
    simp [pointGlobalTraceP3CoordinateKoszulFirst]
  haveI : Mono (pointGlobalTraceP3CoordinateKoszulFirst K ≫
      biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3)) := h ▸ inferInstance
  exact mono_of_mono (pointGlobalTraceP3CoordinateKoszulFirst K)
    (biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3))

end ProjectiveNegativeTwist
end PfaffianDescent
