import PfaffianDescent.MonomialPolynomialContainmentCharts310
import PfaffianDescent.NativeCoefficientIdealBaseChange310
import PfaffianDescent.MonomialCoefficientAmbientWholeIdealCompatibility300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (i j : MonomialCoefficientChartIndex300 m n)

/-- The two actual coefficient overlap points classify the same whole ideal. -/
lemma monomialCoefficientOverlapPoints_sameWholeIdeal310 :
    (cyclicMatrixWholeIdealChart287 i.monomials i.zeroIndex
      (cyclicCoefficientPoint283 R m n i.monomials i.zeroIndex
        (monomialCoefficientFirstOverlapPoint300 R m n i j))).val =
    (cyclicMatrixWholeIdealChart287 j.monomials j.zeroIndex
      (cyclicCoefficientPoint283 R m n j.monomials j.zeroIndex
        (monomialCoefficientSecondOverlapPoint300 R m n i j))).val := by
  change (cyclicCoefficientWholeIdealChartEquiv287
      i.monomials i.zeroIndex R i.zero_eq
      (monomialCoefficientFirstOverlapPoint300 R m n i j)).val =
    (cyclicCoefficientWholeIdealChartEquiv287
      j.monomials j.zeroIndex R j.zero_eq
      (monomialCoefficientSecondOverlapPoint300 R m n i j)).val
  rw [cyclicCoefficientWholeIdealChart_ideal302, cyclicCoefficientWholeIdealChart_ideal302]
  exact (monomialCoefficientWholeIdeal_firstOverlap_image300 R m n i j).trans
    (monomialCoefficientWholeIdeal_secondOverlap_image300 R m n i j).symm

/-- Whole coefficient ideals for p=0 agree on the actual original overlap.
This retains the finite equations and nilpotents, rather than just support. -/
lemma monomialPolynomialContainmentCoefficientIdeal_overlap_image310
    (p : MvPolynomial (Fin m) R) :
    (monomialPolynomialContainmentCoefficientIdeal310 R m n p i).map
        (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom =
      (monomialPolynomialContainmentCoefficientIdeal310 R m n p j).map
        (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom := by
  rw [monomialPolynomialContainmentCoefficientIdeal_image310,
    monomialPolynomialContainmentCoefficientIdeal_image310]
  exact cyclicPolynomialContainmentIdeal_eq_of_sameWholeIdeal310
    i.monomials j.monomials i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq _ _
    (monomialCoefficientOverlapPoints_sameWholeIdeal310 R m n i j) _

/-- Native closed coefficient chart retains the exact quotient-kernel ideal. -/
def monomialPolynomialContainmentChartIdealSheaf310
    (p : MvPolynomial (Fin m) R) :
    (Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)))).ker

set_option backward.isDefEq.respectTransparency.types false in
/-- Literal coefficient ideal-sheaf compatibility on the original overlap spectra. -/
lemma monomialPolynomialContainmentChartIdealSheaf_overlap_comap310
    (p : MvPolynomial (Fin m) R) :
    (monomialPolynomialContainmentChartIdealSheaf310 R m n i p).comap
        (monomialCoefficientOverlapToFirst300 R m n i j) =
      (monomialPolynomialContainmentChartIdealSheaf310 R m n j p).comap
        (monomialCoefficientOverlapToSecond300 R m n i j) := by
  change (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)))).ker.comap
      (Spec.map (CommRingCat.ofHom (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom)) =
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p j)))).ker.comap
      (Spec.map (CommRingCat.ofHom (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom))
  exact (nativeCoefficientIdealKernel_comap310 _ _).trans
    ((congrArg (fun K : Ideal (MonomialOverlapCoefficientAlgebra292 R m n
        i.monomials j.monomials i.zeroIndex i.zero_eq) =>
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker)
      (monomialPolynomialContainmentCoefficientIdeal_overlap_image310 R m n i j p)).trans
      (nativeCoefficientIdealKernel_comap310 _ _).symm)

/-- Compatibility on the actual native intersections of the two H charts. -/
lemma monomialPolynomialContainmentChartIdealSheaf_nativePullback_comap310
    (p : MvPolynomial (Fin m) R) :
    (monomialPolynomialContainmentChartIdealSheaf310 R m n i p).comap
        (pullback.fst (monomialCoefficientGluedChartMap300 R m n i)
          (monomialCoefficientGluedChartMap300 R m n j)) =
      (monomialPolynomialContainmentChartIdealSheaf310 R m n j p).comap
        (pullback.snd (monomialCoefficientGluedChartMap300 R m n i)
          (monomialCoefficientGluedChartMap300 R m n j)) := by
  apply nativeIdealComapIso_injective300 (monomialCoefficientOverlap_isPullback300 R m n i j).isoPullback
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    (monomialCoefficientOverlap_isPullback300 R m n i j).isoPullback_hom_fst,
    (monomialCoefficientOverlap_isPullback300 R m n i j).isoPullback_hom_snd]
  exact monomialPolynomialContainmentChartIdealSheaf_overlap_comap310 R m n i j p

/-- Exact actual H-cover descent input, constructed from the original finite equations. -/
lemma monomialPolynomialContainmentChartIdealSheaf_actualOpenCover_comap310
    (p : MvPolynomial (Fin m) R)
    (i j : ULift.{u} (MonomialCoefficientChartIndex300 m n)) :
    (monomialPolynomialContainmentChartIdealSheaf310 R m n i.down p).comap
        (pullback.fst ((monomialCoefficientGluedOpenCover300 R m n).f i)
          ((monomialCoefficientGluedOpenCover300 R m n).f j)) =
      (monomialPolynomialContainmentChartIdealSheaf310 R m n j.down p).comap
        (pullback.snd ((monomialCoefficientGluedOpenCover300 R m n).f i)
          ((monomialCoefficientGluedOpenCover300 R m n).f j)) := by
  change (monomialPolynomialContainmentChartIdealSheaf310 R m n i.down p).comap
      (pullback.fst (monomialCoefficientGluedChartMap300 R m n i.down)
        (monomialCoefficientGluedChartMap300 R m n j.down)) =
    (monomialPolynomialContainmentChartIdealSheaf310 R m n j.down p).comap
      (pullback.snd (monomialCoefficientGluedChartMap300 R m n i.down)
        (monomialCoefficientGluedChartMap300 R m n j.down))
  exact monomialPolynomialContainmentChartIdealSheaf_nativePullback_comap310 R m n i.down j.down p

end PfaffianDescent
end
