import PfaffianDescent.CorayOriginalChartGenericCompatibility
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! Actual chart generic fractions and actual original cubic coordinate field
generation. Affine fraction-ring geometry and literal normalized polynomial
chart generation are DERIVED, not input as desired field certificates.
No minimal-degree/rank-two/composition-with-pencil conclusion is claimed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u

/-- EVERY actual function-field value is a ratio of ACTUAL values from any
specified nonempty affine chart. The chart ring, chart isomorphism and
actual generic evaluation are retained literally. -/
theorem affineChartGenericEvaluation_div_surjective
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of R) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange]
    (z : X.functionField) :
    ∃ a b : R, affineChartGenericEvaluation i b ≠ 0 ∧
      affineChartGenericEvaluation i a / affineChartGenericEvaluation i b = z := by
  let U : X.Opens := i.opensRange
  let e : R ≃+* Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of R)).symm ≪≫
      IsOpenImmersion.ΓIsoTop i).commRingCatIsoToRingEquiv
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U (isAffineOpen_opensRange i)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective Γ(X, U) z
  have haEval : affineChartGenericEvaluation i (e.symm a) =
      algebraMap Γ(X, U) X.functionField a := by
    change X.germToFunctionField U (e (e.symm a)) = X.germToFunctionField U a
    rw [RingEquiv.apply_symm_apply]
  have hbEval : affineChartGenericEvaluation i (e.symm b) =
      algebraMap Γ(X, U) X.functionField b := by
    change X.germToFunctionField U (e (e.symm b)) = X.germToFunctionField U b
    rw [RingEquiv.apply_symm_apply]
  refine ⟨e.symm a, e.symm b, ?_, ?_⟩
  · rw [hbEval]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  · rw [haEval, hbEval]
    exact hab

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ACTUAL original normalized cubic chart coordinates generate the
ENTIRE original-pi function field as a field over ORIGINAL K. No coordinate
or function-field-generation certificate is supplied. -/
theorem cubicOriginalChartGenericCoordinates_adjoin_eq_top
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    letI : Algebra K ((hypersurface p hp).functionField) :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    IntermediateField.adjoin K (Set.range (fun i : Fin 4 =>
      (show (hypersurface p hp).functionField from
        @affineChartGenericEvaluation
          (ChartRing (equationIdeal p hp) j)
          (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
          (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
          (chartι (equationIdeal p hp) j)
          (isOpenImmersion_chartι (equationIdeal p hp) j)
          (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
          (chartCoordinate (equationIdeal p hp) j i)))) = ⊤ := by
  letI : Algebra K ((hypersurface p hp).functionField) :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g : ChartRing (equationIdeal p hp) j →+*
      (hypersurface p hp).functionField :=
    @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let E := IntermediateField.adjoin K
    (Set.range (fun i : Fin 4 => g (chartCoordinate (equationIdeal p hp) j i)))
  have hcoef : g.comp (chartBaseMap (equationIdeal p hp) j) =
      schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  have hgen : ∀ a : ChartRing (equationIdeal p hp) j, g a ∈ E := by
    intro a
    obtain ⟨q, rfl⟩ := eval₂_chartCoordinate_surjective (equationIdeal p hp) j a
    change g (q.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) ∈ E
    rw [MvPolynomial.hom_eval₂, hcoef]
    exact MvPolynomial.eval₂_mem
      (fun d hd => E.algebraMap_mem (q.coeff d))
      (fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
  change E = ⊤
  apply top_unique
  intro z hz
  obtain ⟨a, b, hb, hab⟩ := @affineChartGenericEvaluation_div_surjective
    (ChartRing (equationIdeal p hp) j)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange) z
  have hab' : g a / g b = z := hab
  exact hab' ▸ E.div_mem (hgen a) (hgen b)

end PfaffianDescent.Coray
end
