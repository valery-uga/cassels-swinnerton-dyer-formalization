import PfaffianDescent.SingleSupportOriginalH0MatchingRationalSectionCaller
import PfaffianDescent.OriginalDualCoordinatesFullSupportBaseCaller
import PfaffianDescent.IntrinsicFullQuadraticBasePoint
import PfaffianDescent.IntrinsicOriginalTwistedCubicResidualAnyField

/-! SOURCE ONLY. Exhaust the SAME internally extracted original H0 graph.
Missing entries use matching/C4; full support uses actual full-base descent
and the literal contained-or-rank-nine/residual-rank-one twisted proof. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist QuarticNet
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_originalZ_actual_H0_has_section
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    {Z : Scheme.{u}} (i : Z ⟶ scheme (equationIdeal F hF)) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal F hF))] (P : closedPoints (scheme (equationIdeal F hF)))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase (equationIdeal F hF)).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal F hF) ((scheme (equationIdeal F hF)).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap (equationIdeal F hF)))) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase (equationIdeal F hF))
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase (equationIdeal F hF))
    letI := AllCharacteristics.pointAlgebra (toBase (equationIdeal F hF)) P.1
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase (equationIdeal F hF)) = 8) →
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  let I := equationIdeal F hF
  have hClosedOriginal : IsClosedImmersion i := ‹IsClosedImmersion i›
  have hFiniteOriginal : IsFinite (i ≫ toBase I) :=
    ‹IsFinite (i ≫ toBase (equationIdeal F hF))›
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  obtain ⟨j, g, x, eA, b, v, full, l, hxj, hgen, hbase, hb, hvj, hv,
    hxg, hpoint, hx, hl, hrow, hskew, hOne, hZero⟩ :=
    singleSupport_originalZ_actual_H0_matching_rational_section_or_finite
      F hF hF₀ i P hSupport hP hGeom hdim hZ
  let U0 := conjugateTangentMatrix full b v (conjugate_basis_span b full)
  let U := rescaleTangentDirections l U0
  by_cases hMissing : ∃ r s, r ≠ s ∧ U r s = 0
  · rcases hZero hMissing with ⟨hRational, s, hs⟩ | hFinite
    · exact ⟨s, hs⟩
    · letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
          (i ≫ quotientProjMap I))) := hFinite
      exact @sectionFour_section_of_cubic_of_finite_intrinsic_full_quadratic_base
        k _ F hF Z i hClosedOriginal hFiniteOriginal hZ (by
          change IsFinite (toBase (intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)))
          infer_instance)
  · have hnonzero : ∀ r s, r ≠ s → U0 r s ≠ 0 := by
      intro r s hrs hz
      apply hMissing
      refine ⟨r, s, hrs, ?_⟩
      change l r * U0 r s = 0
      rw [hz, mul_zero]
    have hOriginal : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
        Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
      have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase
      have hCoordinates : (fun r => g (chartCoordinate I j r)) = x :=
        funext (fun r => (hxg r).symm)
      have hChart : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
          Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
        simpa only [hCoordinates] using h
      rw [hChart, ← Category.assoc, hpoint, Category.assoc]
    have hBase : intrinsicFullQuadraticBaseIdeal
        (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) =
        intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I) := by
      rw [hOriginal]
      exact intrinsicFullQuadraticBaseIdeal_comp_iso Z.isoSpec.symm (i ≫ quotientProjMap I)
    have hAlt := originalDualCoordinates_any_chart_full_support_fullBase_alternative
      eA x hgen j hxj b v hx hb hvj full l hl hskew hnonzero
    unfold IntrinsicFullBaseEmbeddedAlternative at hAlt
    rw [hBase] at hAlt
    rcases hAlt with ⟨f, hf, hfac⟩ | hTwisted
    · let B := intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)
      letI : IsIso f := hf
      let f' := Z.isoSpec.hom ≫ f
      letI : IsIso f' := inferInstance
      have hfac' : f' ≫ quotientProjMap B = i ≫ quotientProjMap I := by
        calc
          f' ≫ quotientProjMap B = Z.isoSpec.hom ≫
              ambientNormalizedCoordinateChartPoint (F := k) x j hxj := by
            dsimp only [f']
            rw [Category.assoc, hfac]
          _ = i ≫ quotientProjMap I := by rw [hOriginal, Iso.hom_inv_id_assoc]
      have hbase' : f' ≫ toBase B = i ≫ toBase I := by
        rw [← quotientProjMap_toBase B, ← Category.assoc, hfac',
          Category.assoc, quotientProjMap_toBase I]
      have hbaseInv : toBase B = inv f' ≫ (i ≫ toBase I) := by
        rw [← hbase']
        simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      letI : IsFinite (toBase B) := by
        rw [hbaseInv]
        infer_instance
      exact @sectionFour_section_of_cubic_of_finite_intrinsic_full_quadratic_base
        k _ F hF Z i hClosedOriginal hFiniteOriginal hZ (by
          change IsFinite (toBase (intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)))
          infer_instance)
    · exact @sectionFour_section_of_cubic_of_twisted_intrinsic_full_quadratic_base_direct
        k _ F hF Z i hClosedOriginal hFiniteOriginal hZ hTwisted

end PfaffianDescent
