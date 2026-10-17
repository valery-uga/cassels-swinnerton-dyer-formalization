import PfaffianDescent.CorayAiProjectiveHyperplaneSupport
import PfaffianDescent.CorayAiIntegralCurveProperClosedCut
import PfaffianDescent.CorayBoundedOriginalEvaluationImage
import PfaffianDescent.CorayBoundedOriginalEvaluationNondegenerate

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- In the image-curve branch, a NONZERO original hyperplane cuts the SAME
whole generic image in finitely many closed original ambient points.
Neither image dimension nor the generic-point avoidance is inferred from
nondegeneracy alone: dimension is the branch hypothesis; avoidance is derived. -/
theorem cubicThroughPointBasis_sameImage_hyperplaneCut_finite_closedPoints001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) (hc : c ≠ 0)
    (hDim : ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
      Ring.DimensionLEOne
        ((cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a).presheaf.stalk z)) :
    let i := cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
    (i ⁻¹' basisProjectiveHyperplaneSupport c).Finite ∧
      ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
        i z ∈ basisProjectiveHyperplaneSupport c → IsClosed ({i z} : Set
          (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))) := by
  classical
  let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
  let i := cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
  let t := cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a
  let z := IsLocalRing.closedPoint (hypersurface p hp).functionField
  letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : IsClosedImmersion i :=
    cubicThroughPointBasisEvaluationImageInclusion_isClosedImmersion p hp hp0 n y hpy j b a
  letI : IsLocallyNoetherian
      (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
    projectiveEvaluationAmbient_isLocallyNoetherian m
  letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian i
  let pi := cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a
  letI : IsProper pi := cubicThroughPointBasisEvaluationImageToBase_isProper p hp hp0 n y hpy j b a
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pi
  letI : IsNoetherian C := ⟨⟩
  have hOutside : i (t z) ∉ basisProjectiveHyperplaneSupport c := by
    intro h
    have hFactor := congrArg (fun f => f z)
      (cubicThroughPointBasisGenericPointToImage_factorization p hp hp0 n y hpy j b a)
    change i (t z) = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a z at hFactor
    rw [hFactor] at h
    have hZero := (basisProjectiveHyperplaneSupport_chartPoint_mem_iff001 a
      (cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a) c).mp h
    exact hc ((cubicThroughPointBasisGenericChartMap_linearForm_zero_iff
      p hp hp0 n y hpy j b a c).mp hZero)
  exact integralCurve_proper_closedCut_ambient_closedImages001 C _ i hDim
    (basisProjectiveHyperplaneSupport c) (basisProjectiveHyperplaneSupport_isClosed001 c)
    (t z) hOutside

end PfaffianDescent.Coray
