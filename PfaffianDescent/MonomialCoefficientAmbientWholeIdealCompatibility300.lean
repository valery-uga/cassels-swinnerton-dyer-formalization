import PfaffianDescent.MonomialCoefficientAmbientOverlap300
import PfaffianDescent.NativeIdealComapIso300
import PfaffianDescent.MonomialUniversalWholeFamilyTransition300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (i j : MonomialCoefficientChartIndex300 m n)


private theorem nativePullbackIdealCompatibility_congr300
    {X Y Z : Scheme.{u}} (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f f' : X ⟶ Z) (g g' : Y ⟶ Z) (hf : f = f') (hg : g = g')
    (h : I.comap (pullback.fst f' g') = J.comap (pullback.snd f' g')) :
    I.comap (pullback.fst f g) = J.comap (pullback.snd f g) := by
  cases hf
  cases hg
  exact h

/-- SAME original whole universal quotient embedding kernel on its original polynomial chart. -/
def monomialCoefficientChartWholeIdealSheaf300 :
    (Spec (.of (MvPolynomial (Fin m)
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (universalCyclicWholeAmbientIdeal282 R m n i.monomials i.zeroIndex)))).ker

lemma monomialCoefficientWholeIdeal_firstOverlap_image300 :
    (universalCyclicWholeAmbientIdeal282 R m n i.monomials i.zeroIndex).map
      (MvPolynomial.map (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom) =
    monomialOverlapWholeIdeal294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq := rfl

/-- Original second chart's entire universal ideal has SAME first-overlap image,
proved from actual coefficient classification and original literal ideal reversal. -/
lemma monomialCoefficientWholeIdeal_secondOverlap_image300 :
    (universalCyclicWholeAmbientIdeal282 R m n j.monomials j.zeroIndex).map
      (MvPolynomial.map (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom) =
    monomialOverlapWholeIdeal294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq := by
  let L := MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq
  let f := monomialOverlapForwardCoefficientMap293 R m n j.monomials i.monomials
    j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq
  have h := monomialOverlapClassification_chart300
    (R := R) (m := m) (n := n) (B := j.monomials) (C := i.monomials)
    (kB := j.zeroIndex) (hkB := j.zero_eq) f
  have hi := congrArg (fun x : MonomialWholeIdealChart287 (A := L) j.monomials => x.val) h
  calc
    _ = (cyclicCoefficientWholeIdealChartEquiv287 (A := L) j.monomials j.zeroIndex R j.zero_eq
        (monomialCoefficientSecondOverlapPoint300 R m n i j)).val :=
      (cyclicCoefficientWholeIdealChart_ideal302 R j.monomials j.zeroIndex j.zero_eq _).symm
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n j.monomials i.monomials
        j.zeroIndex j.zero_eq L f).val.val := hi.symm
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
        i.zeroIndex i.zero_eq L (AlgHom.id R L)).val.val :=
      monomialOverlapForwardCoefficientMap_sameIdeal293 R m n j.monomials i.monomials
        j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq
    _ = _ := monomialOverlapClassification_originalWholeIdeal300 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq

/-- Exact WHOLE kernel compatibility on the original polynomial determinant-overlap presentation. -/
lemma monomialCoefficientChartWholeIdeal_overlap_comap300 :
    (monomialCoefficientChartWholeIdealSheaf300 R m n i).comap
      (monomialCoefficientPolynomialOverlapToFirst300 R m n i j) =
    (monomialCoefficientChartWholeIdealSheaf300 R m n j).comap
      (monomialCoefficientPolynomialOverlapToSecond300 R m n i j) :=
  (nativePolynomialIdealImageKernel_comap300
    (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom
    (universalCyclicWholeAmbientIdeal282 R m n i.monomials i.zeroIndex)
    (monomialOverlapWholeIdeal294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialCoefficientWholeIdeal_firstOverlap_image300 R m n i j)).trans
      (nativePolynomialIdealImageKernel_comap300
        (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom
        (universalCyclicWholeAmbientIdeal282 R m n j.monomials j.zeroIndex)
        (monomialOverlapWholeIdeal294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
        (monomialCoefficientWholeIdeal_secondOverlap_image300 R m n i j)).symm

/-- The ORIGINAL native ambient chart pullback has literal whole-ideal compatibility,
transported through its DERIVED original polynomial overlap Iso. -/
lemma monomialCoefficientChartWholeIdeal_nativePullback_comap300 :
    (monomialCoefficientChartWholeIdealSheaf300 R m n i).comap
      (pullback.fst (monomialCoefficientPolynomialChartToAmbient300 R m n i)
        (monomialCoefficientPolynomialChartToAmbient300 R m n j)) =
    (monomialCoefficientChartWholeIdealSheaf300 R m n j).comap
      (pullback.snd (monomialCoefficientPolynomialChartToAmbient300 R m n i)
        (monomialCoefficientPolynomialChartToAmbient300 R m n j)) := by
  apply nativeIdealComapIso_injective300 (monomialCoefficientPolynomialOverlapIso300 R m n i j)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    monomialCoefficientPolynomialOverlapIso_hom_fst300,
    monomialCoefficientPolynomialOverlapIso_hom_snd300]
  exact monomialCoefficientChartWholeIdeal_overlap_comap300 R m n i j

/-- EXACT native open-cover ideal descent input, with all overlap compatibility proved internally. -/
lemma monomialCoefficientChartWholeIdeal_actualOpenCover_comap300
    (i j : ULift.{u} (MonomialCoefficientChartIndex300 m n)) :
    (monomialCoefficientChartWholeIdealSheaf300 R m n i.down).comap
      (pullback.fst ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f i)
        ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f j)) =
    (monomialCoefficientChartWholeIdealSheaf300 R m n j.down).comap
      (pullback.snd ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f i)
        ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f j)) := by
  exact nativePullbackIdealCompatibility_congr300
    (monomialCoefficientChartWholeIdealSheaf300 R m n i.down)
    (monomialCoefficientChartWholeIdealSheaf300 R m n j.down)
    ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f i)
    (monomialCoefficientPolynomialChartToAmbient300 R m n i.down)
    ((monomialCoefficientAmbientPolynomialOpenCover300 R m n).f j)
    (monomialCoefficientPolynomialChartToAmbient300 R m n j.down)
    (monomialCoefficientAmbientPolynomialOpenCover_map300 R m n i)
    (monomialCoefficientAmbientPolynomialOpenCover_map300 R m n j)
    (monomialCoefficientChartWholeIdeal_nativePullback_comap300 R m n i.down j.down)

end PfaffianDescent
