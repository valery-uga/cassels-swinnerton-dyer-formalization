import PfaffianDescent.ActualQuarticTensorFullBaseSchemeTransport
import PfaffianDescent.FourTangentIntrinsicFullBaseAlternative
import PfaffianDescent.IntrinsicFullQuadraticBaseIso
import PfaffianDescent.GroundTwistedCubicPresentationTransport

/-! Assembly helper for a derived full-system equality. In the finite branch
the comparison is replaced by the canonical lift of the ORIGINAL embedding,
so the conclusion retains that embedding exactly. Geometric callers must
derive hW; it is not a public replacement for the original-Z hypotheses. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module Matrix
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace QuarticNet

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicFullQuadraticBase_embedded_alternative_of_skew_system_map
    {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hW : (intrinsicFullQuadraticSystem i).map
      (linearSubstitutionEquiv M hM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem
        (fourTangentDualToProjective (skewTangentDirections a b c d e f) ≫
          quotientProjMap ⊥)) :
    (∃ l : Z ⟶ scheme (intrinsicFullQuadraticBaseIdeal i),
      IsIso l ∧ l ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal i) = i) ∨
      GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal i) := by
  let U := skewTangentDirections a b c d e f
  let q := fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  let B := intrinsicFullQuadraticBaseIdeal i
  let C := intrinsicFullQuadraticBaseIdeal q
  let eBC := intrinsicFullQuadraticBaseSchemeIso_of_system_map i q M hM hW
  have hBC : eBC.hom ≫ toBase C = toBase B :=
    intrinsicFullQuadraticBaseSchemeIso_of_system_map_toBase i q M hM hW
  have hIdeal : B.toIdeal.map (linearSubstitution M).toRingHom = C.toIdeal :=
    (intrinsicFullQuadraticBaseIdeal_map_of_system_map i q M hM hW).symm
  rcases fourTangent_intrinsicFullQuadraticBase_embedded_alternative
      a b c d e f ha hb hc hd he hf with ⟨l, hl, hfac⟩ | hTwisted
  · apply Or.inl
    letI := hl
    have hqbase : q ≫ ambientToBase =
        Spec.map (CommRingCat.ofHom (algebraMap K (FourTangentDualAlgebra K))) := by
      rw [Category.assoc, quotientProjMap_toBase]
      exact linearNormalizedPointAt_toBase _ _ _ _ _ _
    letI : IsFinite (q ≫ ambientToBase) := by
      rw [hqbase]
      exact (IsFinite.SpecMap_iff _).mpr
        (RingHom.finite_algebraMap.mpr inferInstance)
    have hlbase : l ≫ toBase C = q ≫ ambientToBase := by
      calc
        l ≫ toBase C = (l ≫ quotientProjMap C) ≫ ambientToBase := by
          rw [Category.assoc, quotientProjMap_toBase]
        _ = q ≫ ambientToBase := congrArg (fun r => r ≫ ambientToBase) hfac
    have hCbase : toBase C = inv l ≫ (q ≫ ambientToBase) := by
      calc
        toBase C = inv l ≫ (l ≫ toBase C) := by
          rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
        _ = inv l ≫ (q ≫ ambientToBase) := congrArg (fun r => inv l ≫ r) hlbase
    letI : IsFinite (toBase C) := by rw [hCbase]; infer_instance
    letI : IsFinite (toBase B) := by rw [← hBC]; infer_instance
    let lOriginal := IsClosedImmersion.lift (quotientProjMap B) i
      (intrinsicFullQuadraticBaseIdeal_ker_le i)
    have hlOriginal : IsIso lOriginal :=
      intrinsicFullQuadraticBase_originalLift_isIso i hZ
    exact ⟨lOriginal, hlOriginal, IsClosedImmersion.lift_fac _ _ _⟩
  · apply Or.inr
    exact GroundTwistedCubicPresentation.of_coordinate_image
      (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM.ne_zero) hIdeal hTwisted

end QuarticNet
end PfaffianDescent
