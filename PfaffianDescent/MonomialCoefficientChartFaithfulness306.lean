import PfaffianDescent.NativeAffineWholeIdealFaithfulness306
import PfaffianDescent.MonomialWholeIdealTestChartMap303

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}

/-- The original inverse287 chart map recovers every native coefficient point. -/
lemma monomialCoefficientPoint_asTestChartMap306
    (i : MonomialCoefficientChartIndex300 m n)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A) :
    monomialWholeIdealTestChartMap303 R i
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
          i.monomials i.zeroIndex R i.zero_eq p) =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫
        monomialCoefficientGluedChartMap300 R m n i := by
  dsimp only [monomialWholeIdealTestChartMap303]
  rw [Equiv.symm_apply_apply]
  rfl

/-- Two arbitrary original coefficient points, on possibly different charts,
give the same native H-map whenever their entire pulled universal ideals agree.
The equality is derived from287 and the original overlap transition303. -/
lemma monomialCoefficientChartMaps_eq_of_wholeFamily306
    (i j : MonomialCoefficientChartIndex300 m n)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A)
    (q : UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex →ₐ[R] A)
    (h : (cyclicCoefficientUniversalFamilyPullback302 R m n i.monomials i.zeroIndex p).val =
      (cyclicCoefficientUniversalFamilyPullback302 R m n j.monomials j.zeroIndex q).val) :
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫
        monomialCoefficientGluedChartMap300 R m n i =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫
        monomialCoefficientGluedChartMap300 R m n j := by
  have hp := cyclicCoefficientUniversalFamily_classifies302 R
    i.monomials i.zeroIndex i.zero_eq p
  have hq := cyclicCoefficientUniversalFamily_classifies302 R
    j.monomials j.zeroIndex j.zero_eq q
  have hnative := (congrArg Subtype.val hp).symm.trans
    (h.trans (congrArg Subtype.val hq))
  have hideal := monomialWholeIdealNativeFamily_sameIdeal306 i.monomials j.monomials
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      i.monomials i.zeroIndex R i.zero_eq p)
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      j.monomials j.zeroIndex R j.zero_eq q) hnative
  exact (monomialCoefficientPoint_asTestChartMap306 R i p).symm.trans
    ((monomialWholeIdealTestChartMap_sameIdeal303 R i j _ _ hideal).trans
      (monomialCoefficientPoint_asTestChartMap306 R j q))

end PfaffianDescent
end
