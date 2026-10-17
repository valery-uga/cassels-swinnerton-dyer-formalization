import PfaffianDescent.CorayLinearEvaluationRatioField
import PfaffianDescent.CorayOriginalChartGenericLinearity
import PfaffianDescent.CorayOriginalFunctionFieldTensorDomain
import Mathlib.Tactic.Convert

/-! Source only, unverified. The actual original-pi ground hom defines
 the field of the SAME generic basis coordinate ratios. Native-carrier
 spelling uses the proved identity of the original scalar actions.
 Ratios of any bounded through-P sections lie in it; no image/rank claim follows. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Generic ratio notation uses division inherited from this exact Field,
not a separately synthesized Div structure on the underlying carrier. -/
private theorem fieldDivision_projection {A : Type u} [Field A] (s t : A) :
    @Div.div A
      (@DivInvMonoid.toDiv A
        (@DivisionRing.toDivInvMonoid A
          (@Field.toDivisionRing A (inferInstance : Field A)))) s t = s / t := rfl

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
local notation "NativeFF" => AlgebraicGeometry.Scheme.functionField (hypersurface p hp)
local notation "φ" => schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)

/-- Transport by the accepted identity carrier equivalence, whose
linearity proves the original-pi K action agrees with multiplication by φ. -/
private def cubicThroughPointNativeGenericLinearEvaluation :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    cubicThroughCoordinateSections p hp n y hpy →ₗ[K] NativeFF := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  exact (schemeFunctionFieldOriginalRingLinearEquiv
    (hypersurfaceToBase p hp)).toLinearMap.comp
      (cubicThroughPointGenericLinearEvaluation p hp n y hpy j)

/-- The transported evaluator is identity on the original section value. -/
private theorem cubicThroughPointNativeGenericLinearEvaluation_apply
    (s : cubicThroughCoordinateSections p hp n y hpy) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j s =
      (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j s) := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  rfl

/-- Its scalar coefficients are exactly the original structure hom. -/
private theorem cubicThroughPointNativeGenericLinearEvaluation_smul
    (c : K) (s : cubicThroughCoordinateSections p hp n y hpy) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j (c • s) =
      φ c * cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j s := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  exact ((cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j).map_smul c s).trans
    (Algebra.smul_def c (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j s))

/-- The SAME basis ratio field, with its independently retained original
structure hom and native function-field carrier. No constants action is replaced. -/
def cubicThroughPointOriginalBasisRatioField {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    IntermediateField K NativeFF := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  exact linearEvaluationBasisRatioField
    (K := K) (F := NativeFF)
    (V := cubicThroughCoordinateSections p hp n y hpy) (ι := Fin m)
    b (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j) a

/-- The generator set consists of the literal original basis value
ratios, not a replacement field inferred solely from an isomorphism. -/
private theorem cubicThroughPointOriginalBasisRatioField_eq_adjoin {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a =
      IntermediateField.adjoin K (Set.range (fun i =>
        @Div.div NativeFF (@DivInvMonoid.toDiv NativeFF
          (@DivisionRing.toDivInvMonoid NativeFF
            (@Field.toDivisionRing NativeFF (inferInstance : Field NativeFF))))
          (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j (b i))
          (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j (b a)))) := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  simp only [cubicThroughPointOriginalBasisRatioField, linearEvaluationBasisRatioField,
    cubicThroughPointNativeGenericLinearEvaluation_apply]
  rfl

theorem cubicThroughPointGeneric_normalized_mem_originalBasisRatioField {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (s : cubicThroughCoordinateSections p hp n y hpy) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    @Div.div NativeFF (@DivInvMonoid.toDiv NativeFF
          (@DivisionRing.toDivInvMonoid NativeFF
            (@Field.toDivisionRing NativeFF (inferInstance : Field NativeFF))))
        (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j s)
        (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j (b a)) ∈
      cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  have h := linearEvaluation_normalized_mem_basisRatioField
    (K := K) (F := NativeFF)
    (V := cubicThroughCoordinateSections p hp n y hpy) (ι := Fin m)
    b (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j) a s
  simp only [cubicThroughPointNativeGenericLinearEvaluation_apply] at h
  convert h using 1 <;> rfl

theorem cubicThroughPointGeneric_ratio_mem_originalBasisRatioField {m : ℕ}
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (s t : cubicThroughCoordinateSections p hp n y hpy) :
    letI : Algebra K NativeFF := RingHom.toAlgebra φ
    @Div.div NativeFF (@DivInvMonoid.toDiv NativeFF
          (@DivisionRing.toDivInvMonoid NativeFF
            (@Field.toDivisionRing NativeFF (inferInstance : Field NativeFF))))
        (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j s)
        (show NativeFF from cubicThroughPointGenericLinearEvaluation p hp n y hpy j t) ∈
      cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a := by
  letI : Algebra K NativeFF := RingHom.toAlgebra φ
  let E := schemeFunctionFieldOriginalRingLinearEquiv (hypersurfaceToBase p hp)
  have he : Function.Injective (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j) :=
    E.injective.comp (cubicThroughPointGenericLinearEvaluation_injective
      (p := p) (hp := hp) (n := n) (y := y) (hpy := hpy) (j := j) hp0)
  have ha : cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j (b a) ≠ 0 :=
    (evaluatedBasis_linearIndependent
      (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
      (B := NativeFF) (ι := Fin m)
      b (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j) he).ne_zero a
  have h := linearEvaluation_ratio_mem_basisRatioField
    (K := K) (F := NativeFF)
    (V := cubicThroughCoordinateSections p hp n y hpy) (ι := Fin m)
    b (cubicThroughPointNativeGenericLinearEvaluation p hp n y hpy j) a ha s t
  simp only [cubicThroughPointNativeGenericLinearEvaluation_apply] at h
  convert h using 1 <;> rfl

end
end PfaffianDescent.Coray
end
