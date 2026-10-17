import PfaffianDescent.VoisinGenericSelectedEightActualPresentation
import PfaffianDescent.VoisinActualEightIntrinsicIdealEquality

/-! The generic selected eight-point construction and the canonical
finite-algebra construction have the same intrinsic ideal. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem SmoothCompatibleEightCharts.exists_intrinsicIdealEquality
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (w : SmoothCompatibleEightCharts p hp) :
    letI : Smooth (hypersurfaceToBase p hp) := w.smooth
    letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
    letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
    letI : IsIntegral w.U := w.integralU
    letI : IsIntegral w.Q := w.integralQ
    letI : IsOpenImmersion w.i := w.openI
    letI : IsOpenImmersion w.j := w.openJ
    letI : Surjective w.r := w.surjectiveR
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      letI : IsSeparated (hypersurfaceToBase p hp) :=
        isSeparated_homogeneousToBase (equationIdeal p hp)
      letI : IsIntegral (projectiveConfigurationQuotientOpen
        (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
        isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
          p hp w.hpne 8 w.D
      letI : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left :=
        isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
          p hp w.hpne 8 w.D
      ∃ hz : configurationQuotientMap (equationIdeal p hp) 8
          (w.i (genericPoint w.U)) =
        (cubicConfigurationBase p hp 8).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp 8))
          (IsLocalRing.closedPoint
            (cubicConfigurationBase p hp 8).functionField),
        ∃ v : ActualGenericEightPresentation p hp a ha w.i hz,
          let Q := cubicConfigurationBase p hp 8
          let O := (orderedFamilyConfigurationOver
            (hypersurfaceToBase p hp) 8).left
          let bCan := quadraticOrderedLiftFunctionFieldHom p hp
            (w.i (genericPoint w.U)) hz
          let bSel : K →+* O.residueField (w.i (genericPoint w.U)) :=
            (Spec.preimage (openImmersion_genericResidueLift w.i ≫ w.i ≫
              (orderedFamilyConfigurationOver
                (hypersurfaceToBase p hp) 8).hom)).hom
          letI : Algebra Q.functionField
              (O.residueField (w.i (genericPoint w.U))) := bCan.toAlgebra
          letI : Algebra K
              (O.residueField (w.i (genericPoint w.U))) := bSel.toAlgebra
          intrinsicEightPointTripleHomogeneousIdeal
            (p.map bSel) (hp.map bSel)
            (v.canonicalVectors p hp a ha w.i hz) =
          intrinsicEightPointTripleHomogeneousIdeal
            (p.map bSel) (hp.map bSel)
            (v.selectedVectors p hp a ha w.i hz) := by
  dsimp only
  letI : Smooth (hypersurfaceToBase p hp) := w.smooth
  letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
  letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
  letI : IsIntegral w.U := w.integralU
  letI : IsIntegral w.Q := w.integralQ
  letI : IsOpenImmersion w.i := w.openI
  letI : IsOpenImmersion w.j := w.openJ
  letI : Surjective w.r := w.surjectiveR
  intro a ha
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp w.hpne 8 w.D
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp w.hpne 8 w.D
  obtain ⟨hz, ⟨v⟩⟩ := w.exists_actualPresentation p hp a ha
  exact ⟨hz, v, v.intrinsicIdeal_eq p hp a ha w.i hz⟩

end PfaffianDescent
