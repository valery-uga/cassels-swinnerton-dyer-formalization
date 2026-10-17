import PfaffianDescent.FourCoordinateVertexActualSchemePresentation
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso

/-! Literal geometric full-base-scheme classification on the originally
supplied four components. The tangent representatives are extracted from
their actual algebras; the skew/nonzero conditions refer to those actual
representatives, and no embedding-comparison certificate is an input. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

def fourCoordinateVertexActualTangentMatrix
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    Fin 4 → Fin 4 → K :=
  Classical.choose (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)

/-- Under the manuscript's skew/full-support tangent conditions, the FULL
intrinsic base scheme is the originally supplied four double points (with
their specified ambient embedding), or an embedded twisted cubic. -/
theorem fourCoordinateVertex_actual_intrinsicFullBase_alternative
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2)
    (hskew : ∀ r s, fourCoordinateVertexActualTangentMatrix Z i hSupport hZ r s =
      -fourCoordinateVertexActualTangentMatrix Z i hSupport hZ s r)
    (hnonzero : ∀ r s, r ≠ s →
      fourCoordinateVertexActualTangentMatrix Z i hSupport hZ r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥)) := by
  let U := fourCoordinateVertexActualTangentMatrix Z i hSupport hZ
  obtain ⟨e, hdiag, hrows, hfac⟩ :=
    Classical.choose_spec (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)
  have hU : U = QuarticNet.skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) :=
    QuarticNet.skew_matrix_eq_parameters U hdiag hskew
  let q := QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  have hAlternative : QuarticNet.IntrinsicFullBaseEmbeddedAlternative q := by
    have h := QuarticNet.fourTangent_intrinsicFullQuadraticBase_embedded_alternative
      (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
      (hnonzero 0 1 (by decide)) (hnonzero 0 2 (by decide))
      (hnonzero 0 3 (by decide)) (hnonzero 1 2 (by decide))
      (hnonzero 1 3 (by decide)) (hnonzero 2 3 (by decide))
    change QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (QuarticNet.fourTangentDualToProjective
        (QuarticNet.skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
          (U 1 2) (U 1 3) (U 2 3)) ≫ quotientProjMap ⊥) at h
    simpa only [← hU] using h
  have hOriginal := QuarticNet.intrinsicFullBase_embedded_alternative_precomp_iso e q hAlternative
  change e.hom ≫ q = Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) at hfac
  change QuarticNet.IntrinsicFullBaseEmbeddedAlternative (e.hom ≫ q) at hOriginal
  simpa only [hfac] using hOriginal

end PfaffianDescent
