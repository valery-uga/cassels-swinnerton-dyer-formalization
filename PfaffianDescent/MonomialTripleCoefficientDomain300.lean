import PfaffianDescent.MonomialTripleOverlapLocalization300
import PfaffianDescent.DoubleAwaySchemeIntersection300
import PfaffianDescent.MonomialOverlapPrincipalOpen294

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB : Fin n) (hkB : B kB = 0)

/-- Both original B-chart restrictions coincide on the genuine double localization. -/
lemma monomialTripleOverlapFirstLastCoefficientMap_restrict300 :
    (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB).comp
        (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
          (MonomialOverlapCoefficientAlgebra292 R m n B D kB hkB)) =
      (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB).comp
        (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
          (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)) := by
  apply (cyclicCoefficientWholeIdealChartEquiv287 (A :=
    MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB) B kB R hkB).injective
  calc
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
        (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB)).val :=
      (monomialOverlapClassification_chart300 (R := R) (m := m) (n := n)
        (B := B) (C := D) (kB := kB) (hkB := hkB) _).symm
    _ = (monomialTripleOverlapFirstLast293 B C D
        (universalMonomialTripleOverlap300 R m n B C D kB hkB)).val :=
      congrArg (fun z => z.val)
        (monomialTripleOverlapFirstLastCoefficientMap_classifies300 R m n B C D kB hkB)
    _ = (universalMonomialTripleOverlap300 R m n B C D kB hkB).val.val := rfl
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
        (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB)).val :=
      congrArg (fun z => z.val)
        (monomialTripleOverlapFirstCoefficientMap_classifies300 R m n B C D kB hkB).symm
    _ = _ := monomialOverlapClassification_chart300 (R := R) (m := m) (n := n)
      (B := B) (C := C) (kB := kB) (hkB := hkB) _

/-- The elementary ring-map square is derived from the proved actual representing equivalence. -/
lemma monomialTripleOverlapFirstLastCoefficientMap_baseSquare300 :
    (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB).toRingHom.comp
        (@algebraMap (UniversalCyclicCoefficientAlgebra282 R m n B kB)
          (MonomialOverlapCoefficientAlgebra292 R m n B D kB hkB)
          (@CommRing.toCommSemiring (UniversalCyclicCoefficientAlgebra282 R m n B kB) inferInstance)
          (@CommRing.toCommSemiring (MonomialOverlapCoefficientAlgebra292 R m n B D kB hkB) inferInstance).toSemiring
          inferInstance) =
      (@algebraMap (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
          (@CommRing.toCommSemiring (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB) inferInstance)
          (@CommRing.toCommSemiring (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB) inferInstance).toSemiring
          inferInstance).comp
          (@algebraMap (UniversalCyclicCoefficientAlgebra282 R m n B kB)
          (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
          (@CommRing.toCommSemiring (UniversalCyclicCoefficientAlgebra282 R m n B kB) inferInstance)
          (@CommRing.toCommSemiring (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB) inferInstance).toSemiring
          inferInstance) :=
  congrArg (fun f => f.toRingHom)
    (monomialTripleOverlapFirstLastCoefficientMap_restrict300 R m n B C D kB hkB)

abbrev monomialTripleOverlapScheme300 :=
  Spec (.of (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB))

def monomialTripleOverlapFirstSchemeMap300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ⟶
      Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)) :=
  Spec.map (CommRingCat.ofHom
    (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB).toRingHom)

def monomialTripleOverlapFirstLastSchemeMap300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ⟶
      Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n B D kB hkB)) :=
  Spec.map (CommRingCat.ofHom
    (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB).toRingHom)

/-- The ACTUAL triple domain is the genuine pullback of the two native292/294
overlap immersions into the same original B coefficient affine scheme. -/
lemma monomialTripleOverlap_isPullback300 :
    IsPullback
      (monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB)
      (monomialTripleOverlapFirstLastSchemeMap300 R m n B C D kB hkB)
      (monomialOverlapPrincipalOpenMap294 R m n B C kB hkB)
      (monomialOverlapPrincipalOpenMap294 R m n B D kB hkB) :=
  doubleAwaySpec_isPullback300
    (universalMonomialOverlapDet292 R m n B C kB hkB)
    (universalMonomialOverlapDet292 R m n B D kB hkB)
    (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB).toRingHom
    (monomialTripleOverlapFirstLastCoefficientMap_baseSquare300 R m n B C D kB hkB)

lemma monomialTripleOverlapFirstSchemeMap_isOpenImmersion300 :
    IsOpenImmersion (monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))
    (monomialTripleOverlapDenominator300 R m n B C D kB hkB)

/-- Its image is the exact intersection of the two ORIGINAL B-chart determinant opens. -/
lemma monomialTripleOverlap_baseRange300 :
    Set.range (monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫
      monomialOverlapPrincipalOpenMap294 R m n B C kB hkB) =
      ((PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB) ⊓
        PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B D kB hkB)) :
        Set (PrimeSpectrum (UniversalCyclicCoefficientAlgebra282 R m n B kB))) := by
  have h := doubleAwayBaseSpecMap_range300
    (universalMonomialOverlapDet292 R m n B C kB hkB)
    (universalMonomialOverlapDet292 R m n B D kB hkB)
  rw [doubleAwayBaseSpecMap_factor300] at h
  exact h

end PfaffianDescent
