import PfaffianDescent.CorayOwnCoordinateCanonicalCutIso
import PfaffianDescent.FiniteProjectivePositiveTwistNativeRankAnyField
import PfaffianDescent.CorayOwnSpecifiedCoordinateCutDegreeAnyField
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact

/-! SOURCE ONLY. The SAME original native coordinate-multiplication
cokernel has H0 rank equal to the OWN coordinate Hilbert degree, over any
field. Canonical sheaf Iso, whole-cut finiteness and degree are derived. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine native whole-cut rank transport through the ORIGINAL canonical
cokernel Iso, with independent original-pi scalar actions on both sides.
The only geometric helper input is finiteness of the actual whole cut. -/
theorem ownCoordinateCokernel_topSections_finite_and_coordinateCutRank_anyField
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ)
    [IsFinite (toBase
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)))] :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) =
        finiteSchemeRank (toBase
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))) := by
  let D := C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
  let i := schemeQuotientMap C D le_sup_left
  let pi := toBase C
  letI : IsFinite (i ≫ pi) := by
    dsimp only [i, pi]
    rw [schemeQuotientMap_toBase]
    infer_instance
  have h := finiteProjectivePushforwardPositiveTwist_topSections_finite_and_nativeRank_anyField
    D (m + 1) pi i
  letI := h.1
  let e := schemeModuleOpenTopIsoLinearEquivOver pi
    (ownCoordinateCokernelWholeCutPositiveTwistIso C j m)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  have he : Module.finrank K (SchemeModuleOpenSectionsOver pi
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) =
      finiteSchemeRank (i ≫ pi) := e.finrank_eq.trans h.2
  simpa only [i, pi, schemeQuotientMap_toBase] using he

/-- Original smooth cubic/p-q/minimal-component geometry supplies finiteness
and degree of the SAME specified coordinate cut internally. The original
native coordinate cokernel's H0 rank is the OWN Hilbert degree, with no
Infinite, Perfect, geometric-integrality, rank, or comparison premise. -/
theorem selectedProjectiveMinimalComponent_ownCoordinateCokernel_topSections_finite_and_hilbertDegree_anyField
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal) (m : ℕ) :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) =
        actualCurveCoordinateHilbertDegree C := by
  obtain ⟨hfinite, hdegree⟩ :=
    selectedProjectiveMinimalComponent_specifiedCoordinateCut_nativeRank_eq_hilbertDegree_anyField
      p q hp hp0 n hq hnot C hCmin P j hj
  letI := hfinite
  have h := ownCoordinateCokernel_topSections_finite_and_coordinateCutRank_anyField C j m
  exact ⟨h.1, h.2.trans hdegree⟩

end PfaffianDescent.Coray
end
