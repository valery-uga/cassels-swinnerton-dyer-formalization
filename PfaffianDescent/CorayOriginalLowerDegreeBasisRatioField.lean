import PfaffianDescent.CorayOriginalChartFunctionFieldGeneration
import PfaffianDescent.CorayLowerDegreeOriginalCoordinateRecovery
import PfaffianDescent.CorayOriginalBasisRatioField

/-! Actual SAME original degree-n basis ratio field is the entire original
function field when there is a genuine nonzero lower-degree through-P
section. The basis is never changed to one at its least nonzero degree.
The minimum-degree branch and native image/rank-two comparison remain open.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Bounded ordinary identity for the exact native Field division. This
retains the original ratio values and does not synthesize a separate Div. -/
private theorem originalLowerDegree_fieldDivision_projection
    {A : Type u} [Field A] (s t : A) :
    @Div.div A
      (@DivInvMonoid.toDiv A
        (@DivisionRing.toDivInvMonoid A
          (@Field.toDivisionRing A (inferInstance : Field A)))) s t = s / t := rfl

/-- Genuine lower-degree through-P existence forces the ACTUAL ORIGINAL
DEGREE-n basis ratio field to be the whole original-pi function field. All
coordinate containment is constructed by padding and multiplication in the
actual point kernel; no generation/image/pencil certificate is a premise. -/
theorem cubicThroughPointOriginalBasisRatioField_eq_top_of_lowerDegree
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (c : Fin m) (a : ℕ) (han : a < n)
    (s : cubicThroughCoordinateSections p hp a y hpy) (hs : s ≠ 0) :
    letI : Algebra K ((hypersurface p hp).functionField) :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    cubicThroughPointOriginalBasisRatioField p hp n y hpy j b c = ⊤ := by
  letI : Algebra K ((hypersurface p hp).functionField) :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  obtain ⟨k, hdegree⟩ : ∃ k : ℕ, n = a + k + 1 :=
    ⟨n - a - 1, by omega⟩
  subst n
  let t : Fin 4 → cubicThroughCoordinateSections p hp (a + k + 1) y hpy :=
    fun i => cubicThroughPointCoordinateMultiple p hp (a + k) y hpy
      (cubicThroughPointCoordinatePadding p hp a k y hpy j s) i
  let g : ChartRing (equationIdeal p hp) j →+*
      (hypersurface p hp).functionField :=
    @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let E := cubicThroughPointOriginalBasisRatioField p hp (a + k + 1) y hpy j b c
  have hrecover := cubicThroughPointGeneric_coordinateMultiples_recover
    p hp hp0 y hpy j a k s hs
  have hcoordinate (i : Fin 4) : g (chartCoordinate (equationIdeal p hp) j i) ∈ E := by
    have hmem := cubicThroughPointGeneric_ratio_mem_originalBasisRatioField
      p hp (a + k + 1) y hpy j hp0 b c (t i) (t j)
    have hvalue :
        @Div.div (hypersurface p hp).functionField
          (@DivInvMonoid.toDiv (hypersurface p hp).functionField
            (@DivisionRing.toDivInvMonoid (hypersurface p hp).functionField
              (@Field.toDivisionRing (hypersurface p hp).functionField
                (inferInstance : Field (hypersurface p hp).functionField))))
          (show (hypersurface p hp).functionField from
            cubicThroughPointGenericLinearEvaluation p hp (a + k + 1) y hpy j (t i))
          (show (hypersurface p hp).functionField from
            cubicThroughPointGenericLinearEvaluation p hp (a + k + 1) y hpy j (t j)) =
        g (chartCoordinate (equationIdeal p hp) j i) := by
      rw [originalLowerDegree_fieldDivision_projection]
      exact hrecover.2 i
    exact hvalue ▸ hmem
  have hle : IntermediateField.adjoin K
      (Set.range (fun i : Fin 4 => g (chartCoordinate (equationIdeal p hp) j i))) ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨i, rfl⟩
    exact hcoordinate i
  have htop : IntermediateField.adjoin K
      (Set.range (fun i : Fin 4 => g (chartCoordinate (equationIdeal p hp) j i))) = ⊤ :=
    cubicOriginalChartGenericCoordinates_adjoin_eq_top p hp j
  change E = ⊤
  exact top_unique (htop ▸ hle)

end PfaffianDescent.Coray
end
