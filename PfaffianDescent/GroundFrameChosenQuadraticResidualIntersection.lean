import PfaffianDescent.GroundFrameCubicResidualGeometry
import PfaffianDescent.MatchingLineActualCoordinatePoint

/-! SOURCE ONLY / UNVERIFIED. The literal binary residual calculation is
transported to the SAME embedded ground frame line and original cubic.
Connecting the normalized binary root to the arbitrary chosen a of031
remains a separate specified interface; it is not silently assumed complete. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective QuarticNet
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- A point of the actual residual intersection, with SAME-M and SAME-cubic
projections and proved literal ambient equality. -/
def ActualGroundFrameResidualIntersectionPoint
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (c d s : k) : Prop :=
  let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
  let N := groundFrameResidualIntersectionIdeal C F hF c d s
  ∃ r : Spec (.of k) ⟶ scheme N,
    r ≫ toBase N = 𝟙 _ ∧
    ∃ rM : Spec (.of k) ⟶ scheme M, ∃ rS : Spec (.of k) ⟶ hypersurface F hF,
      rM ≫ toBase M = 𝟙 _ ∧ rS ≫ hypersurfaceToBase F hF = 𝟙 _ ∧
      rM = r ≫ schemeQuotientMap M N (le_trans le_sup_left le_sup_left) ∧
      rS = r ≫ schemeQuotientMap (equationIdeal F hF) N
        (le_trans le_sup_right le_sup_left) ∧
      rM ≫ quotientProjMap M = rS ≫ quotientProjMap (equationIdeal F hF)

/-- A contained secant supplies a rational point via its own literal M→S
embedding. Both the line and cubic maps keep the original ambient embedding. -/
theorem groundFrame_zeroRestriction_pointOnSameContainedLine
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hZero : groundFrameLineRestriction C F = 0) :
    let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
    ∃ i : scheme M ⟶ hypersurface F hF,
      IsClosedImmersion i ∧ i ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap M ∧
      ∃ rM : Spec (.of k) ⟶ scheme M, ∃ rS : Spec (.of k) ⟶ hypersurface F hF,
        rM ≫ toBase M = 𝟙 _ ∧ rS ≫ hypersurfaceToBase F hF = 𝟙 _ ∧
        rS = rM ≫ i ∧ rM ≫ quotientProjMap M = rS ≫ quotientProjMap (equationIdeal F hF) := by
  classical
  dsimp only
  let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
  obtain ⟨i, hi, hAmbient⟩ := groundFrameCubic_zeroRestriction_actualContainedLine C F hF hZero
  obtain ⟨rM, hrM⟩ := matchingProjectorLine_has_actual_firstBasisPoint C
  let rS := rM ≫ i
  have hBase : i ≫ hypersurfaceToBase F hF = toBase M := by
    have h := congrArg (fun t => t ≫ ambientToBase (R := k) (σ := Fin 4)) hAmbient
    simpa only [Category.assoc, quotientProjMap_toBase] using h
  refine ⟨i, hi, hAmbient, rM, rS, hrM, ?_, rfl, ?_⟩
  · dsimp only [rS]
    rw [Category.assoc, hBase]
    exact hrM
  · dsimp only [rS]
    rw [Category.assoc, hAmbient]

/-- Genuine factor/intersection endpoint on a FIXED original frame line.
The only root input is the ordinary coordinate value of its specified
quadratic point; no residual/ground-point/intersection certificate is input.
An original-a primitive caller must still derive this normalized root. -/
theorem groundFrame_chosenQuadratic_actualResidualIntersection [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (sigma : E ≃ₐ[k] E)
    (alpha : E) (hAlpha : alpha ≠ sigma alpha)
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hRoot : aeval ![1, alpha] (groundFrameLineRestriction C F) = (0 : E)) :
    ∃ r s c d : k,
      alpha ^ 2 = algebraMap k E r + algebraMap k E s * alpha ∧
      groundFrameLineRestriction C F =
        quadraticSecantBinaryFactor r s * quadraticSecantResidualLinearFactor c d s ∧
      MvPolynomial.map (algebraMap k E) (quadraticSecantBinaryFactor r s) =
        (X 1 - MvPolynomial.C alpha * X 0) * (X 1 - MvPolynomial.C (sigma alpha) * X 0) ∧
      ((groundFrameLineRestriction C F = 0 ∧
        let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
        ∃ i : scheme M ⟶ hypersurface F hF,
          IsClosedImmersion i ∧ i ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap M ∧
          ∃ rM : Spec (.of k) ⟶ scheme M, ∃ rS : Spec (.of k) ⟶ hypersurface F hF,
            rM ≫ toBase M = 𝟙 _ ∧ rS ≫ hypersurfaceToBase F hF = 𝟙 _ ∧
            rS = rM ≫ i ∧
            rM ≫ quotientProjMap M = rS ≫ quotientProjMap (equationIdeal F hF)) ∨
       (groundFrameLineRestriction C F ≠ 0 ∧
        let w : Fin 2 → k := ![d, -(c + s * d)]
        w ≠ 0 ∧ aeval w (quadraticSecantResidualLinearFactor c d s) = 0 ∧
          ActualGroundFrameResidualIntersectionPoint C F hF c d s)) := by
  classical
  have hH : (groundFrameLineRestriction C F).IsHomogeneous 3 :=
    coordinateLineRestriction_homogeneous
      (linearSubstitution_homogeneous (basisCoordinateMatrix C) hF)
  obtain ⟨r, s, c, d, hAlphaSq, hFactor, hSplit, hCase⟩ :=
    binaryCubic_chosenQuadratic_residual hdeg sigma alpha hAlpha
      (groundFrameLineRestriction C F) hH hRoot
  refine ⟨r, s, c, d, hAlphaSq, hFactor, hSplit, ?_⟩
  rcases hCase with hZero | ⟨hNonzero, hw, hLinear, hCubic⟩
  · exact Or.inl ⟨hZero, groundFrame_zeroRestriction_pointOnSameContainedLine C F hF hZero⟩
  · exact Or.inr ⟨hNonzero, hw, hLinear,
      groundFrameResidual_actualIntersectionPoint C F hF c d s
        ![d, -(c + s * d)] hw hCubic hLinear⟩

end PfaffianDescent
