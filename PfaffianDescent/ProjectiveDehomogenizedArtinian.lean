import PfaffianDescent.ProjectiveFiniteChartArtinian
import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.AffinePointExt
import AllCharacteristics.PolynomialCoordinateOne
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! FULL homogeneous ideals on projective three-space, expressed on actual
normalized three-variable affine charts. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal normalized chart polynomial map, renamed to three variables. -/
def projectiveDehomogenizedChartMap (j : Fin 4) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  (MvPolynomial.renameEquiv K (finThreeEquivCoordinateComplement j).symm).toAlgHom.comp
    (coordinateOneEvaluation j)

/-- Every homogeneous ideal, with no bound on its number of generators, has
its actual projective chart identified with this dehomogenized quotient. -/
def projectiveDehomogenizedChartEquiv
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    ChartRing I j ≃+*
      (MvPolynomial (Fin 3) K ⧸ I.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom) := by
  let A := coordinateOneIdeal (R := K) j
  let B := I.toIdeal
  let e := coordinateOneQuotientEquiv (R := K) j
  let J := B.map (coordinateOneEvaluation j).toRingHom
  have hmap : (B.map (Ideal.Quotient.mk A)).map e.toRingHom = J := by
    rw [Ideal.map_map]
    apply congrArg (Ideal.map · B)
    apply RingHom.ext
    intro p
    exact coordinateOneQuotientEquiv_mk j p
  let d : ChartRing I j ≃+* (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸ J) :=
    (chartPresentationEquiv I j).symm.trans
      ((Ideal.quotEquivOfEq (show chartPresentationIdeal I j = A ⊔ B by
        change B ⊔ A = A ⊔ B
        exact sup_comm B A)).trans
        ((DoubleQuot.quotQuotEquivQuotSup A B).symm.trans
          (Ideal.quotientEquiv (B.map (Ideal.Quotient.mk A)) J e.toRingEquiv hmap.symm)))
  let r := MvPolynomial.renameEquiv K (finThreeEquivCoordinateComplement j).symm
  have hrename : J.map r.toRingHom =
      I.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom := by
    rw [Ideal.map_map]
    rfl
  exact d.trans (Ideal.quotientEquiv J
    (I.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom)
    r.toRingEquiv hrename.symm)

/-- Finiteness of the FULL projective base locus makes each FULL
three-variable normalized chart quotient Artinian. -/
theorem projectiveDehomogenizedChart_isArtinian_of_finite
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    [IsFinite (toBase I)] (j : Fin 4) :
    IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ I.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom) := by
  letI := projective_chart_isArtinian_of_finite I j
  exact (projectiveDehomogenizedChartEquiv I j).isArtinianRing

/-- Conversely, Artinian normalized chart quotients make the actual projective
scheme finite over the coefficient field. Properness/compactness are intrinsic. -/
theorem projective_isFinite_of_dehomogenizedCharts_isArtinian
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hcharts : ∀ j : Fin 4, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ I.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom)) :
    IsFinite (toBase I) := by
  have hArt : ∀ j : Fin 4, IsArtinianRing (ChartRing I j) := by
    intro j
    letI := hcharts j
    exact (projectiveDehomogenizedChartEquiv I j).symm.isArtinianRing
  letI : IsLocallyArtinian (scheme I) :=
    (isLocallyArtinian_iff_openCover (coordinateOpenCover I).openCover).mpr (by
      intro j
      letI := hArt j
      exact (Scheme.isLocallyArtinianScheme_Spec
        (R := CommRingCat.of (ChartRing I j))).mpr inferInstance)
  letI : CompactSpace (scheme I) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase I)
  letI : IsArtinianScheme (scheme I) := ⟨⟩
  exact isFinite_of_isArtinianScheme_of_locallyOfFiniteType (toBase I)

end PfaffianDescent
