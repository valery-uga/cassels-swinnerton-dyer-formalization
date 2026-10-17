import PfaffianDescent.MonomialOverlapCoefficientPointTransport300
import PfaffianDescent.MonomialTripleOverlapRotation300

noncomputable section
namespace PfaffianDescent
universe u
/-- Pin the canonical ring superclass dictionaries BEFORE substituting
any quotient coefficient ring or concrete determinant. -/
private def nativeLocalizationScalarImage300
    {A : Type u} [hA : CommRing A] (a x : A) : Localization.Away a :=
  @algebraMap A (Localization.Away a)
    (@CommRing.toCommSemiring A hA)
    (@CommRing.toCommSemiring (Localization.Away a)
      (inferInstance : CommRing (Localization.Away a))).toSemiring
    inferInstance x

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB : Fin n) (hkB : B kB = 0)

/-- Image of the constructed B/D determinant in the SAME B/C coefficient localization. -/
def monomialTripleOverlapDenominator300 :
    MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB :=
  nativeLocalizationScalarImage300
    (universalMonomialOverlapDet292 R m n B C kB hkB)
    (universalMonomialOverlapDet292 R m n B D kB hkB)

/-- Genuine successive localization of the original B coefficient chart at
its two constructed C- and D-basis determinants. -/
abbrev MonomialTripleOverlapCoefficientAlgebra300 :=
  Localization.Away (monomialTripleOverlapDenominator300 R m n B C D kB hkB)

lemma monomialTripleOverlapDenominator_evaluate300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB →ₐ[R] A) :
    monomialWholeIdealChartTransitionDet290 B D
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A p).val =
      p (monomialTripleOverlapDenominator300 R m n B C D kB hkB) := by
  calc
    _ = monomialWholeIdealChartTransitionDet290 B D
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B kB R hkB
          (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
            (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)))) :=
      congrArg (monomialWholeIdealChartTransitionDet290 B D)
        (monomialOverlapClassification_chart300 (R := R) (m := m) (n := n)
          (B := B) (C := C) (kB := kB) (hkB := hkB) p)
    _ = (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
        (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)))
          (universalMonomialOverlapDet292 R m n B D kB hkB) :=
      universalMonomialOverlapDet_evaluate292 R m n B D kB hkB _
    _ = _ := rfl

/-- Every double-localization algebra point is EXACT genuine triple293 data,
with both inverse laws derived from the two original localization universal properties. -/
def monomialTripleOverlapAlgHomEquiv300
    (A : Type u) [CommRing A] [Algebra R A] :
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB →ₐ[R] A) ≃
      MonomialWholeIdealTripleOverlap293 (A := A) B C D :=
  (localizationAlgHomUnitEquiv292 R
    (monomialTripleOverlapDenominator300 R m n B C D kB hkB)
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB) A).trans
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A).subtypeEquiv
      (fun p => by rw [monomialTripleOverlapDenominator_evaluate300]))

lemma monomialTripleOverlapAlgHomEquiv_first300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB →ₐ[R] A) :
    (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p).val =
      monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A
        (p.comp (Algebra.algHom R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB))) := rfl

lemma monomialTripleOverlapAlgHomEquiv_natural300
    {A E : Type u} [CommRing A] [CommRing E] [Algebra R A] [Algebra R E]
    (p : MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB →ₐ[R] A)
    (f : A →ₐ[R] E) :
    monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB E (f.comp p) =
      monomialTripleOverlapMap300 B C D kB hkB f.toRingHom
        (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p) := by
  apply Subtype.ext
  change (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB E (f.comp p)).val =
    monomialWholeIdealChartOverlapMap290 B C kB hkB f.toRingHom
      (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p).val
  rw [monomialTripleOverlapAlgHomEquiv_first300, monomialTripleOverlapAlgHomEquiv_first300]
  change monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB E
      (f.comp (p.comp (Algebra.algHom R
        (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)))) =
    monomialWholeIdealChartOverlapMap290 B C kB hkB f.toRingHom
      (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A
        (p.comp (Algebra.algHom R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB))))
  exact monomialOverlapLocalizationAlgHomEquiv_natural292 R m n B C kB hkB _ f

/-- The actual universal triple point is constructed from the identity algebra map. -/
def universalMonomialTripleOverlap300 :=
  monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
    (AlgHom.id R (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB))

/-- Native map of the SAME B/C overlap ring to the double localization. -/
def monomialTripleOverlapFirstCoefficientMap300 :=
  Algebra.algHom R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)

lemma monomialTripleOverlapFirstCoefficientMap_classifies300 :
    monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
        (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB) =
      (universalMonomialTripleOverlap300 R m n B C D kB hkB).val := by
  have h := monomialTripleOverlapAlgHomEquiv_first300 R m n B C D kB hkB
    (AlgHom.id R (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB))
  rw [AlgHom.id_comp] at h
  exact h.symm

/-- The B/D coefficient map is derived from the SAME original triple point. -/
def monomialTripleOverlapFirstLastCoefficientMap300 :=
  (monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).symm
      (monomialTripleOverlapFirstLast293 B C D
        (universalMonomialTripleOverlap300 R m n B C D kB hkB))

lemma monomialTripleOverlapFirstLastCoefficientMap_classifies300 :
    monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
        (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB) =
      monomialTripleOverlapFirstLast293 B C D
        (universalMonomialTripleOverlap300 R m n B C D kB hkB) :=
  (monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).apply_symm_apply _

end PfaffianDescent
