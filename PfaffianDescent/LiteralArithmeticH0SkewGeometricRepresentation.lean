import PfaffianDescent.SingleSupportActualH0SkewTangent
import PfaffianDescent.ActualRescaledTensorWholeEmbeddingSquare
import PfaffianDescent.ActualSuppliedChartTensorEmbedding

/-! SOURCE ONLY, UNVERIFIED. Literal arithmetic skew normalization as a
geometric presentation of the SAME originally supplied scheme. The genuine
H0 hypothesis supplies the row weights. Every source/ambient comparison is
derived, including the chosen original chart permutation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open QuarticNet
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- One actual conjugate frame and nonzero epsilon parameters give skew
representatives of all four double-point components of the actual Z base
change. The true original ambient embedding is retained by both projection
squares. This is an existence theorem, not a claim about every independent
coordinate frame supplied by another caller. -/
theorem singleSupport_actual_H0_skew_geometric_representation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap I)))
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) :
    ∃ (pi : Equiv.Perm (Fin 4))
      (B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
      (U : Fin 4 → Fin 4 → AlgebraicClosure k)
      (S : pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
          (i ≫ toBase I) ≅ Spec (.of (FourTangentDualAlgebra (AlgebraicClosure k))))
      (Q : pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
          (i ≫ toBase I) ⟶ Proj (homogeneousSubmodule (Fin 4) (AlgebraicClosure k))),
      (∀ row, U row row = 0) ∧
      (∀ row col, U row col = -U col row) ∧
      (∀ row, ∃ col, U row col ≠ 0) ∧
      Q ≫ ambientCoefficientMap (algebraMap k (AlgebraicClosure k)) =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
            (i ≫ toBase I) ≫ i ≫ quotientProjMap I ∧
      Q ≫ ambientToBase (R := AlgebraicClosure k) =
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
            (i ≫ toBase I) ∧
      S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := AlgebraicClosure k) pi =
        fourTangentDualToProjective U ≫ quotientProjMap ⊥ ≫
          (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
            (basisCoordinateMatrix_isUnit B)).inv ∧
      ∀ row, ∃ hrow : tangentDualPoint U row row = 1,
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : Fin 4 => DualNumber (AlgebraicClosure k)) row)) ≫
          S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := AlgebraicClosure k) pi =
        ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
          (tangentDualPoint U row) row hrow ≫
          (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
            (basisCoordinateMatrix_isUnit B)).inv := by
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  obtain ⟨j, g, x, eA, b, v, pi, full, hxj, hgen, hbase, hb0, hv0, hv, hpi,
    hxg, hpoint, hx, hs, hcoordinate, hequation, hrow, l, hl, hskew, hscaled⟩ :=
      singleSupport_actual_H0_quadratics_actual_skew_tangents
        I i P hSupport hP hGeom hdim hZ
  let B := conjugateBasis full b hs
  let U0 := conjugateTangentMatrix full b v hs
  let U := rescaleTangentDirections l U0
  let S := actualRescaledQuarticSchemeIso (i ≫ toBase I) eA b full l hl
  let Q := (finiteSchemeActualFieldBaseChangeIso (K := AlgebraicClosure k)
    (i ≫ toBase I)).hom ≫
      ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (fun r => (1 : AlgebraicClosure k) ⊗ₜ[k] x r) j
          (tensor_coordinate_eq_one x j hxj)
  have hdiag : ∀ row, U row row = 0 := by
    intro row
    simp [U, U0, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  have hskewU : ∀ row col, U row col = -U col row := hskew
  have hnonzero : ∀ row, ∃ col, U row col ≠ 0 := by
    intro row
    obtain ⟨col, hcol⟩ := hrow row
    exact ⟨col, (rescaleTangentDirections_nonzero U0 l hl row col).mpr hcol⟩
  obtain ⟨hOriginal, hField⟩ := actualSuppliedChart_tensor_ambient_squares
    (K := AlgebraicClosure k) I i j g hbase hpoint x hxg hxj
  refine ⟨pi, B, U, S, Q, hdiag, hskewU, hnonzero, hOriginal, hField, ?_, ?_⟩
  · exact actualRescaledQuarticSchemeIso_whole_frame_square
      (i ≫ toBase I) eA x j hxj pi hpi b v hx hb0 full hs l hl
  · intro row
    refine ⟨by simp [tangentDualPoint, hdiag], ?_⟩
    exact actualRescaledQuarticSchemeIso_component_frame_square
      (i ≫ toBase I) eA x j hxj pi hpi b v hx hb0 full hs l hl row

end PfaffianDescent
