import PfaffianDescent.MonomialCoefficientAmbientAtlas300
import PfaffianDescent.MonomialCoefficientOverlapCartesian300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (i j : MonomialCoefficientChartIndex300 m n)

/-- ORIGINAL polynomial spectrum over the actual292 determinant overlap coefficient ring. -/
abbrev monomialCoefficientPolynomialOverlap300 : Scheme.{u} :=
  Spec (.of (MvPolynomial (Fin m)
    (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)))

def monomialCoefficientPolynomialOverlapToFirst300 :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.map (σ := Fin m) (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom))

def monomialCoefficientPolynomialOverlapToSecond300 :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.map (σ := Fin m) (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom))

/-- Genuine original polynomial scalar square on the first chart. -/
lemma monomialCoefficientPolynomialOverlap_first_isPullback300 :
    IsPullback (monomialCoefficientPolynomialOverlapToFirst300 R m n i j)
      (nativePolynomialProjection300
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m)
      (nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
      (monomialCoefficientOverlapToFirst300 R m n i j) := by
  letI : Algebra (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) :=
    (monomialCoefficientFirstOverlapPoint300 R m n i j).toRingHom.toAlgebra
  exact nativePolynomialScalar_isPullback300
    (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m

/-- Genuine second scalar square uses the DERIVED original inverse coefficient map. -/
lemma monomialCoefficientPolynomialOverlap_second_isPullback300 :
    IsPullback (monomialCoefficientPolynomialOverlapToSecond300 R m n i j)
      (nativePolynomialProjection300
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m)
      (nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex) m)
      (monomialCoefficientOverlapToSecond300 R m n i j) := by
  letI : Algebra (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex)
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) :=
    (monomialCoefficientSecondOverlapPoint300 R m n i j).toRingHom.toAlgebra
  exact nativePolynomialScalar_isPullback300
    (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex)
    (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m

/-- Both ORIGINAL polynomial overlap maps have exactly the same image map into actual ambient X. -/
lemma monomialCoefficientPolynomialOverlap_toAmbient300 :
    monomialCoefficientPolynomialOverlapToFirst300 R m n i j ≫
      monomialCoefficientPolynomialChartToAmbient300 R m n i =
    monomialCoefficientPolynomialOverlapToSecond300 R m n i j ≫
      monomialCoefficientPolynomialChartToAmbient300 R m n j := by
  apply pullback.hom_ext
  · change (monomialCoefficientPolynomialOverlapToFirst300 R m n i j ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n i) ≫
        monomialCoefficientAmbientToH300 R m n =
      (monomialCoefficientPolynomialOverlapToSecond300 R m n i j ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n j) ≫
        monomialCoefficientAmbientToH300 R m n
    simp only [Category.assoc, monomialCoefficientPolynomialChartToAmbient_toH300]
    calc
      _ = nativePolynomialProjection300
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m ≫
        monomialCoefficientOverlapToFirst300 R m n i j ≫ monomialCoefficientGluedChartMap300 R m n i := by
        simpa only [Category.assoc] using congrArg
          (fun a => a ≫ monomialCoefficientGluedChartMap300 R m n i)
          (monomialCoefficientPolynomialOverlap_first_isPullback300 R m n i j).w
      _ = nativePolynomialProjection300
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m ≫
        monomialCoefficientOverlapToSecond300 R m n i j ≫ monomialCoefficientGluedChartMap300 R m n j :=
        congrArg (fun a => nativePolynomialProjection300
          (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m ≫ a)
          (monomialCoefficientOverlap_isPullback300 R m n i j).w
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun a => a ≫ monomialCoefficientGluedChartMap300 R m n j)
          (monomialCoefficientPolynomialOverlap_second_isPullback300 R m n i j).w.symm
  · change (monomialCoefficientPolynomialOverlapToFirst300 R m n i j ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n i) ≫
        monomialCoefficientAmbientToGroundAffine300 R m n =
      (monomialCoefficientPolynomialOverlapToSecond300 R m n i j ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n j) ≫
        monomialCoefficientAmbientToGroundAffine300 R m n
    simp only [Category.assoc, monomialCoefficientPolynomialChartToAmbient_toGround300]
    exact (nativePolynomialMap_ground300 m
      (monomialCoefficientFirstOverlapPoint300 R m n i j)).trans
      (nativePolynomialMap_ground300 m (monomialCoefficientSecondOverlapPoint300 R m n i j)).symm

/-- The actual polynomial determinant-overlap presentation is the true ORIGINAL ambient
chart intersection, derived from actual scalar Cartesian squares and native gluing. -/
lemma monomialCoefficientPolynomialOverlap_isPullback300 :
    IsPullback (monomialCoefficientPolynomialOverlapToFirst300 R m n i j)
      (monomialCoefficientPolynomialOverlapToSecond300 R m n i j)
      (monomialCoefficientPolynomialChartToAmbient300 R m n i)
      (monomialCoefficientPolynomialChartToAmbient300 R m n j) :=
  nativeAmbientOverlap_isPullback300
    (monomialCoefficientPolynomialOverlapToFirst300 R m n i j)
    (monomialCoefficientPolynomialOverlapToSecond300 R m n i j)
    (nativePolynomialProjection300
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) m)
    (nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
    (nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n j.monomials j.zeroIndex) m)
    (monomialCoefficientOverlapToFirst300 R m n i j) (monomialCoefficientOverlapToSecond300 R m n i j)
    (monomialCoefficientPolynomialChartToAmbient300 R m n i)
    (monomialCoefficientPolynomialChartToAmbient300 R m n j)
    (monomialCoefficientAmbientToH300 R m n)
    (monomialCoefficientGluedChartMap300 R m n i) (monomialCoefficientGluedChartMap300 R m n j)
    (monomialCoefficientPolynomialOverlap_first_isPullback300 R m n i j)
    (monomialCoefficientPolynomialOverlap_second_isPullback300 R m n i j)
    (monomialCoefficientOverlap_isPullback300 R m n i j)
    (monomialCoefficientPolynomialChart_isPullback300 R m n j)
    (monomialCoefficientPolynomialChartToAmbient_toH300 R m n i)
    (monomialCoefficientPolynomialOverlap_toAmbient300 R m n i j)

/-- Exact native ambient-intersection Iso, retaining both original polynomial projections. -/
def monomialCoefficientPolynomialOverlapIso300 :
    monomialCoefficientPolynomialOverlap300 R m n i j ≅
    pullback (monomialCoefficientPolynomialChartToAmbient300 R m n i)
      (monomialCoefficientPolynomialChartToAmbient300 R m n j) :=
  (monomialCoefficientPolynomialOverlap_isPullback300 R m n i j).isoPullback

lemma monomialCoefficientPolynomialOverlapIso_hom_fst300 :
    (monomialCoefficientPolynomialOverlapIso300 R m n i j).hom ≫ pullback.fst _ _ =
      monomialCoefficientPolynomialOverlapToFirst300 R m n i j :=
  (monomialCoefficientPolynomialOverlap_isPullback300 R m n i j).isoPullback_hom_fst

lemma monomialCoefficientPolynomialOverlapIso_hom_snd300 :
    (monomialCoefficientPolynomialOverlapIso300 R m n i j).hom ≫ pullback.snd _ _ =
      monomialCoefficientPolynomialOverlapToSecond300 R m n i j :=
  (monomialCoefficientPolynomialOverlap_isPullback300 R m n i j).isoPullback_hom_snd

end PfaffianDescent
