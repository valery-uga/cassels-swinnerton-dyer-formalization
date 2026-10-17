import PfaffianDescent.BinaryCubicQuadraticSecantResidual
import PfaffianDescent.ActualChosenMatchingGroundSecant
import PfaffianDescent.ActualMatchingQuadraticLineInOriginalCubic
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY / UNVERIFIED. Actual intersection and residual points on
ONE supplied ground frame line. The chosen-point caller derives this frame
from031; no different line or point-only descent theorem is substituted. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective QuarticNet
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

/-- Restrict to the SAME ground line spanned by C0 and C1. -/
def groundFrameLineRestriction (C : Basis (Fin 4) k (Fin 4 → k)) :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 2) k :=
  coordinateLineRestriction.comp (linearSubstitution (basisCoordinateMatrix C))

/-- Actual restriction evaluated over any ground algebra, with no point
comparison certificate. -/
lemma groundFrameLineRestriction_aeval
    {A : Type u} [CommRing A] [Algebra k A]
    (C : Basis (Fin 4) k (Fin 4 → k)) (w : Fin 2 → A)
    (F : MvPolynomial (Fin 4) k) :
    aeval w (groundFrameLineRestriction C F) =
      aeval (fun m => algebraMap k A (C 0 m) * w 0 +
        algebraMap k A (C 1 m) * w 1) F := by
  have h : (aeval w).comp (groundFrameLineRestriction C) =
      aeval (fun m => algebraMap k A (C 0 m) * w 0 +
        algebraMap k A (C 1 m) * w 1) := by
    ext m : 1
    simp [groundFrameLineRestriction, coordinateLineRestriction,
      linearSubstitution_X, linearCoordinate, basisCoordinateMatrix,
      Fin.sum_univ_four, AlgHom.comp_apply]
  exact AlgHom.congr_fun h F

/-- The literal ambient linear residual equation in the ORIGINAL coordinates.
Its inverse-coordinate substitution is the same one defining the line ideal. -/
def groundFrameResidualEquation (C : Basis (Fin 4) k (Fin 4 → k)) (c d s : k) :
    homogeneousSubmodule (Fin 4) k 1 :=
  let L : homogeneousSubmodule (Fin 4) k 1 :=
    d • ⟨X 1, isHomogeneous_X k 1⟩ +
      (c + s * d) • ⟨X 0, isHomogeneous_X k 0⟩
  ⟨linearSubstitution (basisCoordinateMatrix C)⁻¹ L,
    linearSubstitution_homogeneous _ L.property⟩

/-- Coordinates of the residual linear equation on the SAME frame line. -/
lemma groundFrameResidualEquation_aeval
    (C : Basis (Fin 4) k (Fin 4 → k)) (c d s : k) (w : Fin 2 → k) :
    aeval (w 0 • C 0 + w 1 • C 1) (groundFrameResidualEquation C c d s).val =
      aeval w (quadraticSecantResidualLinearFactor c d s) := by
  let M := basisCoordinateMatrix C
  let z : Fin 4 → k := ![w 0, w 1, 0, 0]
  have hMz : M.mulVec z = w 0 • C 0 + w 1 • C 1 := by
    funext m
    simp [M, z, basisCoordinateMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hBack : M⁻¹.mulVec (w 0 • C 0 + w 1 • C 1) = z := by
    rw [← hMz, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (basisCoordinateMatrix_isUnit C), Matrix.one_mulVec]
  change aeval (w 0 • C 0 + w 1 • C 1)
    (linearSubstitution M⁻¹ ((d • X 1) + ((c + s * d) • X 0))) = _
  rw [linearSubstitution_eval, hBack]
  simp [z, quadraticSecantResidualLinearFactor, smul_eq_C_mul]

/-- A nonzero binary vector gives a nonzero vector on this SAME ground line. -/
lemma groundFrameBinaryVector_ne_zero
    (C : Basis (Fin 4) k (Fin 4 → k)) (w : Fin 2 → k) (hw : w ≠ 0) :
    w 0 • C 0 + w 1 • C 1 ≠ 0 := by
  intro h
  have hsum : ∑ i : Fin 4, ![w 0, w 1, 0, 0] i • C i = 0 := by
    simpa [Fin.sum_univ_four] using h
  have hc := Fintype.linearIndependent_iff.mp C.linearIndependent _ hsum
  apply hw
  funext i
  fin_cases i
  · simpa using hc 0
  · simpa using hc 1

/-- The SAME frame line's linear ideal vanishes at every binary vector. -/
lemma groundFrameLineIdeal_le_binaryKernel
    (C : Basis (Fin 4) k (Fin 4 → k)) (w : Fin 2 → k) :
    (projectorLineIdeal (matchingEdgeProjectorMatrix C)).toIdeal ≤
      RingHom.ker (eval₂Hom (RingHom.id k) (w 0 • C 0 + w 1 • C 1)) := by
  let Q := matchingEdgeProjectorMatrix C
  have hQ : Q.mulVec (w 0 • C 0 + w 1 • C 1) = w 0 • C 0 + w 1 • C 1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [Q, matchingEdgeProjectorMatrix_mulVec_basis]
  apply Ideal.span_le.mpr
  rintro p ⟨m, rfl⟩
  change aeval (w 0 • C 0 + w 1 • C 1) (linearCoordinate (1 - Q) m) = 0
  rw [linearCoordinate_eval, Matrix.sub_mulVec, Matrix.one_mulVec, hQ, sub_self]
  rfl

/-- A zero restriction constructs the actual SAME M→S closed immersion,
with its literal original ambient square. -/
theorem groundFrameCubic_zeroRestriction_actualContainedLine
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hZero : groundFrameLineRestriction C F = 0) :
    let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
    ∃ i : scheme M ⟶ hypersurface F hF,
      IsClosedImmersion i ∧ i ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap M := by
  dsimp only
  let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
  have hMem : F ∈ M.toIdeal :=
    originalCubic_mem_matchingProjectorLineIdeal C F hZero
  have hContain : (equationIdeal F hF).toIdeal ≤ M.toIdeal := by
    apply Ideal.span_le.mpr
    rintro p rfl
    exact hMem
  refine ⟨schemeQuotientMap (equationIdeal F hF) M hContain,
    schemeQuotientMap_closedImmersion _ _ _, ?_⟩
  exact schemeQuotientMap_comp_quotientProjMap _ _ _

/-- Actual residual scheme: the SAME ground line, original cubic, and the
literal linear residual factor in ORIGINAL ambient coordinates. -/
def groundFrameResidualIntersectionIdeal
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (c d s : k) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) k) :=
  projectorLineIdeal (matchingEdgeProjectorMatrix C) ⊔ equationIdeal F hF ⊔
    equationIdeal (groundFrameResidualEquation C c d s).val
      (groundFrameResidualEquation C c d s).property

/-- The explicit residual binary root produces a ground point of the ACTUAL
residual intersection scheme. Its maps to SAME M and SAME S agree in the
original ambient scheme. No new line or cubic point is substituted. -/
theorem groundFrameResidual_actualIntersectionPoint
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c d s : k) (w : Fin 2 → k) (hw : w ≠ 0)
    (hCubic : aeval w (groundFrameLineRestriction C F) = 0)
    (hLinear : aeval w (quadraticSecantResidualLinearFactor c d s) = 0) :
    let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
    let N := groundFrameResidualIntersectionIdeal C F hF c d s
    ∃ r : Spec (.of k) ⟶ scheme N,
      r ≫ toBase N = 𝟙 _ ∧
      ∃ rM : Spec (.of k) ⟶ scheme M, ∃ rS : Spec (.of k) ⟶ hypersurface F hF,
        rM ≫ toBase M = 𝟙 _ ∧ rS ≫ hypersurfaceToBase F hF = 𝟙 _ ∧
        rM = r ≫ schemeQuotientMap M N (le_trans le_sup_left le_sup_left) ∧
        rS = r ≫ schemeQuotientMap (equationIdeal F hF) N
          (le_trans le_sup_right le_sup_left) ∧
        rM ≫ quotientProjMap M = rS ≫ quotientProjMap (equationIdeal F hF) := by
  classical
  dsimp only
  let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
  let I := equationIdeal F hF
  let L := groundFrameResidualEquation C c d s
  let J := equationIdeal L.val L.property
  let N := groundFrameResidualIntersectionIdeal C F hF c d s
  let y := w 0 • C 0 + w 1 • C 1
  have hy : y ≠ 0 := groundFrameBinaryVector_ne_zero C w hw
  have hMy := groundFrameLineIdeal_le_binaryKernel C w
  have hFy : aeval y F = 0 := by
    have h := groundFrameLineRestriction_aeval C w F
    have hEval : aeval w (groundFrameLineRestriction C F) = aeval y F := by
      simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply, mul_comm] using h
    exact hEval.symm.trans hCubic
  have hLy : aeval y L.val = 0 :=
    (groundFrameResidualEquation_aeval C c d s w).trans hLinear
  have hIy : I.toIdeal ≤ RingHom.ker (eval₂Hom (RingHom.id k) y) := by
    apply Ideal.span_le.mpr
    rintro p rfl
    exact hFy
  have hJy : J.toIdeal ≤ RingHom.ker (eval₂Hom (RingHom.id k) y) := by
    apply Ideal.span_le.mpr
    rintro p rfl
    exact hLy
  have hNy : N.toIdeal ≤ RingHom.ker (eval₂Hom (RingHom.id k) y) :=
    sup_le (sup_le hMy hIy) hJy
  obtain ⟨r, hr⟩ := point_of_coordinates N (RingHom.id k) y hy (fun p hp => hNy hp)
  have hrBase : r ≫ toBase N = 𝟙 _ := by simpa only [Spec.map_id] using hr
  let rM := r ≫ schemeQuotientMap M N (le_trans le_sup_left le_sup_left)
  let rS := r ≫ schemeQuotientMap I N (le_trans le_sup_right le_sup_left)
  refine ⟨r, hrBase, rM, rS, ?_, ?_, rfl, rfl, ?_⟩
  · dsimp only [rM]
    rw [Category.assoc, schemeQuotientMap_toBase]
    exact hrBase
  · dsimp only [rS]
    rw [Category.assoc, schemeQuotientMap_toBase]
    exact hrBase
  · dsimp only [rM, rS]
    rw [Category.assoc, Category.assoc, schemeQuotientMap_comp_quotientProjMap,
      schemeQuotientMap_comp_quotientProjMap]

end PfaffianDescent
