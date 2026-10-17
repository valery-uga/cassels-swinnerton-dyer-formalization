import PfaffianDescent.CorayCoefficientNormalizationOriginalCycle
import PfaffianDescent.CorayCoefficientModelOriginalPairInputs
import PfaffianDescent.CorayOwnComponentWordCycle

/-! A nonzero signed-word section on the same coefficient-model normalization
constructs its length cycle and yields a point on the original cubic. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [CharZero M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem selectedOriginalComponent_coefficientModel_wordSection_originalCubic_point001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hD : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    [IsIntegral (scheme D)]
    (hr : Nat.Coprime (Module.finrank K M) 3) :
    let X := scheme D
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase D
    ∀ (ops : List (closedPoints N × Bool)) (theta : ℕ),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) →
      Nat.Coprime theta 3 →
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        ∃ R : closedPoints (hypersurface p hp),
          Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
            (hypersurfaceToBase p hp).residueDegree R.1 ≤ Module.finrank K M * theta := by
  classical
  let X := scheme D
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase D
  dsimp only
  intro ops theta hweight htheta s hs
  obtain ⟨hpM0, hSmooth, hnotM, hDPair⟩ :=
    selectedOriginalMinimalComponent_coefficientMinimalPrime_originalPairInputs001
      p q hp hp0 n hq hnot I hI D hD
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K M)) (hp.map (algebraMap K M))) := hSmooth
  let P : scheme D := Classical.choice inferInstance
  let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  let support := schemeModuleStalkSupport Q
  obtain ⟨hSupport, hPoints, hDegreeInt⟩ :=
    selectedMinimalComponent_genericNormalization_nonzeroWordSection_lengthCycle_degree_eq_weight
      (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M))
      hpM0 n (hq.map (algebraMap K M)) hnotM D hDPair P ops s hs
  let z : EffectiveZeroCycle N := schemeModuleFiniteClosedSupportLengthCycle Q support hSupport hPoints
  have hDegree : EffectiveZeroCycle.degree pi z = theta := by
    have h : (EffectiveZeroCycle.degree pi z : ℤ) = (theta : ℤ) := hDegreeInt.trans hweight
    exact_mod_cast h
  have hCycleCoprime : Nat.Coprime (EffectiveZeroCycle.degree pi z) 3 := by
    rw [hDegree]
    exact htheta
  obtain ⟨R, hRcop, hRbound⟩ := coefficientModel_normalization_cycle_exists_originalCubic_point001
    p q hp n hq I hI.le D hD.le z hr hCycleCoprime
  rw [hDegree] at hRbound
  exact ⟨R, hRcop, hRbound⟩

end PfaffianDescent.Coray
