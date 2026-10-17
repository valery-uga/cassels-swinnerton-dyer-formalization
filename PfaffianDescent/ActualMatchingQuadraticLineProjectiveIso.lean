import PfaffianDescent.IdempotentTwoKernelFrame
import PfaffianDescent.CoordinateMatchingProjectiveLineIso
import PfaffianDescent.ProjectiveLinearCoordinateAmbientSquare

/-! SOURCE ONLY, UNVERIFIED. Construct an actual E-line/P1 Iso from the
SAME E/P derived by matching. All frame data and exact ambient squares are
derived; there is no assumed lift of the original K-coordinate frame. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem intermediateMatchingLine_projectiveLine_iso
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E),
      matchingEdgeProjectorMatrix C = P ∧
      ∃ e : scheme (projectorLineIdeal P) ≅ Proj (homogeneousSubmodule (Fin 2) E),
        e.hom ≫ ambientToBase (R := E) (σ := Fin 2) = toBase (projectorLineIdeal P) ∧
        e.inv ≫ quotientProjMap (projectorLineIdeal P) =
          (coordinateMatchingLineP1Iso E).inv ≫
            quotientProjMap (coordinateMatchingLineIdeal (K := E) false) ≫
            (linearCoordinateChangeAmbientIso (basisCoordinateMatrix C)⁻¹
              (Matrix.isUnit_nonsing_inv_det (basisCoordinateMatrix C) (basisCoordinateMatrix_isUnit C))).hom := by
  classical
  obtain ⟨C, hC⟩ := intermediateMatchingLine_has_projectiveFrame E P B hP
  let M := basisCoordinateMatrix C
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit C
  have hN : IsUnit M⁻¹.det := Matrix.isUnit_nonsing_inv_det M hM
  let I := coordinateMatchingLineIdeal (K := E) false
  let J := projectorLineIdeal P
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M⁻¹ hN).toRingHom := by
    change (projectorLineIdeal P).toIdeal =
      (coordinateMatchingLineIdeal (K := E) false).toIdeal.map
        (linearSubstitutionEquiv M⁻¹ hN).toRingHom
    rw [← hC]
    exact projectorLineIdeal_eq_originalMatchingLine C
  let a := linearCoordinateChangeSchemeIso M⁻¹ hN I J hIJ
  let b := coordinateMatchingLineP1Iso E
  let e := a.symm ≪≫ b
  have haBase : a.hom ≫ toBase J = toBase I :=
    linearCoordinateChangeSchemeIso_hom_toBase M⁻¹ hN I J hIJ
  have haInvBase : a.inv ≫ toBase I = toBase J := by
    rw [← haBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have haAmbient : a.hom ≫ quotientProjMap J = quotientProjMap I ≫
      (linearCoordinateChangeAmbientIso M⁻¹ hN).hom :=
    linearCoordinateChangeSchemeIso_hom_toAmbient M⁻¹ hN I J hIJ
  refine ⟨C, hC, e, ?_, ?_⟩
  · change (a.inv ≫ b.hom) ≫ ambientToBase (R := E) (σ := Fin 2) = toBase J
    rw [Category.assoc, coordinateMatchingLineP1Iso_hom_toBase]
    exact haInvBase
  · change (b.inv ≫ a.hom) ≫ quotientProjMap J = _
    rw [Category.assoc, haAmbient]

end PfaffianDescent.QuarticNet
