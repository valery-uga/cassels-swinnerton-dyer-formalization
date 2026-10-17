import PfaffianDescent.CorayOwnCoordinateHilbertDegreeAnyField

/-! SOURCE ONLY. Original minimal-component geometry derives finiteness and
native degree of the SAME supplied coordinate nonvanishing at SAME actual P.
No Infinite, Perfect, geometric integrality or degree/rank certificate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native finite coordinate-section rank is the intrinsic OWN
Hilbert degree over the original field, for the SAME chosen j. -/
theorem selectedProjectiveMinimalComponent_specifiedCoordinateCut_nativeRank_eq_hilbertDegree_anyField
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal) :
    ∃ hfinite : IsFinite (toBase
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))),
      letI := hfinite
      finiteSchemeRank (toBase
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))) =
        actualCurveCoordinateHilbertDegree C := by
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  have hfinite := integralProjectiveComponent_coordinateCut_isFinite C hCmin.isPrime P
    (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
      p q hp hp0 n hq hnot C hCmin.le) j hj
  letI := hfinite
  have hnotC := (coordinate_notMem_at_point_ne_zero_and_notMem_component C P j hj).2
  exact ⟨hfinite, (primeComponent_linearSection_degree_and_eventualIncrement_anyField
    C (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) hnotC).1.symm⟩

end PfaffianDescent.Coray
