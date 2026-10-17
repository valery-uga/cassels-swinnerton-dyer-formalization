import PfaffianDescent.CorayEntireModelIncidenceCycle
import PfaffianDescent.CorayGenericNormalizationOriginalCubicProperMap
import PfaffianDescent.CorayEffectiveCyclePointBound

/-! The actual coefficient-model normalization maps to the original cubic.
The whole residue-weighted cycle has original degree [M:K] times its M-degree.
This is a cycle consumer; construction of the signed-word cycle is separate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [CharZero M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficientModel_normalization_originalCubic_finite_and_cycleDegree001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    [IsIntegral (scheme D)] :
    let X := scheme D
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let f := coefficientComponentToOriginal I D hID
    let j := schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) I hI
    let i := cubicSecondEquationCurveImmersion p q hp n hq
    let rho := nu ≫ (f ≫ (j ≫ i))
    ∃ hfinite : IsFinite rho,
      letI := hfinite
      ∀ z : EffectiveZeroCycle N,
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) (pushforwardCycle rho z) =
          Module.finrank K M * EffectiveZeroCycle.degree (nu ≫ toBase D) z := by
  classical
  let X := scheme D
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let f := coefficientComponentToOriginal I D hID
  let j := schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) I hI
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let rho := nu ≫ (f ≫ (j ≫ i))
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase D)
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : IsClosedImmersion j := schemeQuotientMap_closedImmersion _ I hI
  letI : IsClosedImmersion i := cubicSecondEquationCurveImmersion_isClosedImmersion p q hp n hq
  letI : IsFinite rho := by dsimp only [rho]; infer_instance
  refine ⟨inferInstance, ?_⟩
  intro z
  have hbase : rho ≫ hypersurfaceToBase p hp =
      (nu ≫ toBase D) ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    dsimp only [rho]
    rw [Category.assoc, Category.assoc, Category.assoc,
      cubicSecondEquationCurveImmersion_toBase, schemeQuotientMap_toBase,
      (coefficientComponentToOriginal_finite_and_toBase I D hID).2,
      Category.assoc]
  rw [degree_pushforwardCycle, hbase]
  exact effectiveCycle_originalDegree_eq_modelFieldDegree_mul (nu ≫ toBase D) z

theorem coefficientModel_normalization_cycle_exists_originalCubic_point001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    [IsIntegral (scheme D)] :
    let X := scheme D
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∀ z : EffectiveZeroCycle N,
      Nat.Coprime (Module.finrank K M) 3 →
      Nat.Coprime (EffectiveZeroCycle.degree (nu ≫ toBase D) z) 3 →
      ∃ R : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
          (hypersurfaceToBase p hp).residueDegree R.1 ≤
            Module.finrank K M * EffectiveZeroCycle.degree (nu ≫ toBase D) z := by
  classical
  let X := scheme D
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let rho := nu ≫ (coefficientComponentToOriginal I D hID ≫
    (schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) I hI ≫
      cubicSecondEquationCurveImmersion p q hp n hq))
  dsimp only
  intro z hr hz
  obtain ⟨hfinite, hdegree⟩ :=
    coefficientModel_normalization_originalCubic_finite_and_cycleDegree001 p q hp n hq I hI D hID
  letI : IsFinite rho := hfinite
  have hcop : Nat.Coprime
      (EffectiveZeroCycle.degree (hypersurfaceToBase p hp) (pushforwardCycle rho z)) 3 := by
    rw [hdegree z]
    exact Nat.coprime_mul_iff_left.mpr ⟨hr, hz⟩
  obtain ⟨R, _hR, hRcop, hRbound⟩ := effectiveCycle_coprime_degree_has_bounded_closedPoint
    (hypersurfaceToBase p hp) (pushforwardCycle rho z) hcop
  exact ⟨R, hRcop, hRbound.trans_eq (hdegree z)⟩

end PfaffianDescent.Coray
