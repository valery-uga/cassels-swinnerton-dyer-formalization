import PfaffianDescent.SingleSupportOriginalOrderH0SkewTangent
import PfaffianDescent.OriginalDualCoordinatesMatchingRationalSectionCaller
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso

/-! SOURCE ONLY. Primitive same-original-Z / actual ideal-sheaf H0 caller.
All chart, field, basis, tangent and nonzero skew weights are extracted from
literal support/rank/H0 hypotheses. Matching and missing-entry conditions
occur only on the derived graph in the conclusion. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist QuarticNet
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem matchingCaller_uniqueNeighbor_missing_entry
    {K : Type u} [Field K] (U : Fin 4 → Fin 4 → K)
    (hOne : ∀ r, ∃! s, U r s ≠ 0) :
    ∃ r s, r ≠ s ∧ U r s = 0 := by
  classical
  by_cases h01 : U 0 1 = 0
  · exact ⟨0, 1, by decide, h01⟩
  · have h02 : U 0 2 = 0 := by
      by_contra h02
      obtain ⟨s, hs, hUnique⟩ := hOne 0
      have he : (1 : Fin 4) = 2 := (hUnique 1 h01).trans (hUnique 2 h02).symm
      exact (by decide : (1 : Fin 4) ≠ 2) he
    exact ⟨0, 2, by decide, h02⟩

theorem singleSupport_originalZ_actual_H0_matching_rational_section_or_finite
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
    ∃ (j : Fin 4) (g : ChartRing (equationIdeal F hF) j →+* Γ(Z, ⊤))
      (x : Fin 4 → Γ(Z, ⊤))
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme (equationIdeal F hF)).residueField P.1))
      (b : Basis (Fin 4) k ((scheme (equationIdeal F hF)).residueField P.1))
      (v : Fin 4 → (scheme (equationIdeal F hF)).residueField P.1)
      (full : Fin 4 ≃ ((scheme (equationIdeal F hF)).residueField P.1 →ₐ[k] AlgebraicClosure k))
      (l : Fin 4 → AlgebraicClosure k),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      g.comp (chartBaseMap (equationIdeal F hF) j) = algebraMap k Γ(Z, ⊤) ∧
      b j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      (∀ r, x r = g (chartCoordinate (equationIdeal F hF) j r)) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal F hF) j = Z.isoSpec.inv ≫ i ∧
      (∀ r, eA (x r) = inl (b r) + inr (v r)) ∧
      (∀ r, l r ≠ 0) ∧
      let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full)
      (∀ r, ∃ s, U r s ≠ 0) ∧
      (∀ r s, l r * U r s = -(l s * U s r)) ∧
      ((∀ r, ∃! s, QuarticNet.rescaleTangentDirections l U r s ≠ 0) →
        Scheme.IsRationalOver (hypersurfaceToBase F hF) ∧
          ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _) ∧
      ((∃ r s, r ≠ s ∧ QuarticNet.rescaleTangentDirections l U r s = 0) →
        (Scheme.IsRationalOver (hypersurfaceToBase F hF) ∧
          ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
        IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
          (i ≫ quotientProjMap (equationIdeal F hF))))) := by
  classical
  let I := equationIdeal F hF
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  obtain ⟨j, g, x, eA, b, v, full, l, hxj, hgen, hbase, hb, hvj, hv,
    hxg, hpoint, hx, hl, hrow, hskew⟩ :=
    singleSupport_actual_H0_original_order_skew_tangents I i P hSupport hP hGeom hdim hZ
  let U := rescaleTangentDirections l
    (conjugateTangentMatrix full b v (conjugate_basis_span b full))
  have hskewU : ∀ r s, U r s = -U s r := hskew
  have hFx : aeval (R := k) x F = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j F
      (show F ∈ I.toIdeal from Ideal.subset_span (Set.mem_singleton _)))
    have hCoordinates : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    rw [hom_eval₂, hbase, hCoordinates, map_zero] at h
    exact h
  have hOriginal : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase
    have hCoordinates : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    have hChart : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
      simpa only [hCoordinates] using h
    rw [hChart, ← Category.assoc, hpoint, Category.assoc]
  refine ⟨j, g, x, eA, b, v, full, l, hxj, hgen, hbase, hb, hvj, hv,
    hxg, hpoint, hx, hl, hrow, hskew, ?_, ?_⟩
  · intro hOne
    have hMissing := matchingCaller_uniqueNeighbor_missing_entry U hOne
    exact originalDualCoordinates_any_chart_matching_rational_and_section
      eA x j hxj b v hx hb hvj hv full F hF hF₀ hFx l hl hskewU hMissing hOne
  · intro hMissing
    have hAlternative := originalDualCoordinates_any_chart_zero_entry_rational_section_or_finite
      eA x j hxj b v hx hb hvj hv full F hF hF₀ hFx l hl hskewU hMissing
    rcases hAlternative with hMatching | hFinite
    · exact Or.inl hMatching
    · have hBase : intrinsicFullQuadraticBaseIdeal
          (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) =
          intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I) := by
        rw [hOriginal]
        exact intrinsicFullQuadraticBaseIdeal_comp_iso Z.isoSpec.symm (i ≫ quotientProjMap I)
      rw [hBase] at hFinite
      exact Or.inr hFinite

end PfaffianDescent
