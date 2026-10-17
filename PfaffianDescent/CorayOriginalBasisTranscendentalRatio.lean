import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap
import PfaffianDescent.CorayOriginalFunctionFieldTensorDomain
import PfaffianDescent.CorayFiniteSubfieldTensorDegreeOne
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericTensorField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Genuine nonconstant-coordinate prerequisite for the SAME original Coray
basis evaluation. Algebraic constants are derived from actual smooth cubic
geometric integrality and the actual finite generic tensor-field theorem.
Distinct basis coordinate ratios are then transcendental over ORIGINAL K.
This is not an image-dimension-two, differential-rank-two, composition-with-
pencil exclusion, or Bertini statement. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Distinct members of a genuinely linearly independent evaluated family
have a ratio outside the ORIGINAL ground field. This private algebra step
changes no scalar action and assumes no image/rank conclusion. -/
private theorem linearIndependent_ratio_not_mem_ground
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {ι : Type*} (v : ι → F) (hli : LinearIndependent K v)
    (a i : ι) (hi : i ≠ a) :
    v i / v a ∉ (⊥ : IntermediateField K F) := by
  intro hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hval : v i = algebraMap K F c * v a :=
    (div_eq_iff (hli.ne_zero a)).mp hc.symm
  have hsmul : (1 : K) • v i = c • v a := by
    simpa only [one_smul, Algebra.smul_def, map_one, one_mul] using hval
  exact hi (hli.eq_of_smul_apply_eq_smul_apply 1 c i a one_ne_zero hsmul)

section
variable {K : Type u} [Field K]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

include hp0 j in
/-- All algebraic elements of the actual smooth cubic function field are
ORIGINAL K constants. Geometric integrality, the original coefficient
Spec diagram, actual finite simple subfield and tensor field are derived;
no constants-field or tensor-field certificate is supplied. -/
theorem cubicOriginalFunctionField_isAlgebraic_mem_ground
    (x : (hypersurface p hp).functionField) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    IsAlgebraic K x → x ∈ (⊥ : IntermediateField K (hypersurface p hp).functionField) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  intro hx
  let E : IntermediateField K (hypersurface p hp).functionField :=
    IntermediateField.adjoin K {x}
  letI : Module.Finite K E := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  letI : GeometricallyIntegral (hypersurfaceToBase p hp) :=
    PfaffianDescent.geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0
  letI : IsOpenImmersion (chartι (equationIdeal p hp) j) :=
    isOpenImmersion_chartι (equationIdeal p hp) j
  have hbase : Spec.map (CommRingCat.ofHom
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))) =
      (hypersurface p hp).fromSpecStalk (genericPoint (hypersurface p hp)) ≫
        hypersurfaceToBase p hp := by
    rw [← cubicChartGenericEvaluation_coefficient_eq p hp j]
    exact @affineChartGenericEvaluation_coefficient_spec
      K (ChartRing (equationIdeal p hp) j)
      (inferInstance : Field K)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (hypersurfaceToBase p hp) (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
      (chartBaseMap (equationIdeal p hp) j) (chartι_toBase (equationIdeal p hp) j)
  have htensor : IsField (E ⊗[K] (hypersurface p hp).functionField) :=
    PfaffianDescent.serreIncidenceGeometric_generic_tensor_isField
      (L := E) (hypersurfaceToBase p hp)
      (CommRingCat.ofHom (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))) hbase
  have hreverse : IsField ((hypersurface p hp).functionField ⊗[K] E) :=
    (Algebra.TensorProduct.comm K (hypersurface p hp).functionField E).toMulEquiv.isField htensor
  have hdegree : finrank K E = 1 :=
    finite_subfield_finrank_eq_one_of_tensor_isField K E
      (hypersurface p hp).functionField E.val hreverse
  exact IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hdegree

end

section
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

include hp0 in
/-- The ratio of ANY two distinct coordinates of the ACTUAL original basis
is transcendental over original K. The existing identity scalar transport
retains the SAME original structural hom and SAME generic evaluation. -/
theorem cubicThroughPointBasisGenericCoordinates_ratio_transcendental {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a i : Fin m) (hi : i ≠ a) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    Transcendental K
      ((show (hypersurface p hp).functionField from
        cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i) /
       (show (hypersurface p hp).functionField from
        cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a)) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let v : Fin m → (hypersurface p hp).functionField := fun t =>
    (show (hypersurface p hp).functionField from
      cubicThroughPointBasisGenericCoordinates p hp n y hpy j b t)
  let E := schemeFunctionFieldOriginalRingLinearEquiv (hypersurfaceToBase p hp)
  have hli0 := evaluatedBasis_linearIndependent
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)) (ι := Fin m)
    b (cubicThroughPointGenericLinearEvaluation p hp n y hpy j)
    (cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0)
  have hli : LinearIndependent K v :=
    hli0.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)
  intro hAlg
  exact linearIndependent_ratio_not_mem_ground v hli a i hi
    (cubicOriginalFunctionField_isAlgebraic_mem_ground p hp hp0 j (v i / v a) hAlg)

/-- The actual Hilbert window constructs the SAME original-K rational map
with a genuinely transcendental pair of its stored coordinates. No image
surface, rank-two, minimal-degree or GI premise is supplied. -/
theorem exists_bounded_cubicThroughPointEvaluationRationalMap_transcendental_ratio
    [FiniteDimensional K L]
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    ∃ m : ℕ, 5 ≤ m ∧
      ∃ (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
        (a i : Fin m) (f : (hypersurface p hp) ⤏
          scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))),
        i ≠ a ∧
        f.compHom (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) =
          (hypersurfaceToBase p hp).toRationalMap ∧
        f.fromFunctionField = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a ∧
        Transcendental K
          ((show (hypersurface p hp).functionField from
            cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i) /
           (show (hypersurface p hp).functionField from
            cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a)) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  obtain ⟨m, hm, b, a, f, hfbase, hfgeneric⟩ :=
    exists_bounded_cubicThroughPointEvaluationRationalMap p hp hp0 n y hpy j hsize
  letI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hi⟩ := exists_ne a
  exact ⟨m, hm, b, a, i, f, hi, hfbase, hfgeneric,
    cubicThroughPointBasisGenericCoordinates_ratio_transcendental p hp hp0 n y hpy j b a i hi⟩

end
end PfaffianDescent.Coray
end
