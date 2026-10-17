import PfaffianDescent.NativeAmbientPullbackChart300
import PfaffianDescent.NativePolynomialScalarScheme300
import PfaffianDescent.NativeSchemeCoverIsoCharts300
import PfaffianDescent.MonomialCoefficientGluedBase300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-- Native polynomial ring over R, before forming either original quotient. -/
private instance originalMatrixCoefficientPolynomialCommRing300 :
    CommRing (MatrixCoefficientPolynomial280 R m n) :=
  @AddMonoidAlgebra.commRing R (MatrixCoefficientIndex280 m n →₀ ℕ)
    ‹CommRing R› inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- First ORIGINAL quotient ring, with its existing native quotient structure. -/
private instance originalCommutingCoefficientCommRing300 :
    CommRing (CommutingMatrixCoefficientAlgebra280 R m n) :=
  @Ideal.Quotient.commRing (MatrixCoefficientPolynomial280 R m n)
    (originalMatrixCoefficientPolynomialCommRing300 R m n)
    (commutingMatrixIdeal280 R m n)

set_option backward.isDefEq.respectTransparency.types false in
/-- Second ORIGINAL cyclic quotient ring, retaining the literal relation ideal. -/
private instance originalCyclicCoefficientCommRing300
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    CommRing (UniversalCyclicCoefficientAlgebra282 R m n B k) :=
  @Ideal.Quotient.commRing (CommutingMatrixCoefficientAlgebra280 R m n)
    (originalCommutingCoefficientCommRing300 R m n)
    (universalCyclicCoefficientIdeal282 R m n B k)

set_option backward.isDefEq.respectTransparency.types false in
/-- SAME native polynomial ring, with the actual coefficient quotient ring pinned. -/
private instance originalCoefficientPolynomialCommRing300
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    CommRing (MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k)) :=
  @AddMonoidAlgebra.commRing (UniversalCyclicCoefficientAlgebra282 R m n B k)
    (Fin m →₀ ℕ) (originalCyclicCoefficientCommRing300 R m n B k) inferInstance

/-- The original relative affine ambient over the SAME genuinely glued coefficient Scheme. -/
abbrev monomialCoefficientAmbient300 : Scheme.{u} :=
  pullback (monomialCoefficientGluedToBase300 R m n) (nativePolynomialProjection300 R m)

def monomialCoefficientAmbientToH300 :
    monomialCoefficientAmbient300 R m n ⟶ monomialCoefficientGluedScheme300 R m n :=
  pullback.fst _ _

def monomialCoefficientAmbientToGroundAffine300 :
    monomialCoefficientAmbient300 R m n ⟶ Spec (.of (MvPolynomial (Fin m) R)) :=
  pullback.snd _ _

/-- The ORIGINAL polynomial coefficient chart maps into the actual ambient pullback. -/
def monomialCoefficientPolynomialChartToAmbient300 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m)
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex))) ⟶
    monomialCoefficientAmbient300 R m n :=
  nativeAmbientChartLift300 (monomialCoefficientGluedToBase300 R m n)
    (nativePolynomialProjection300 R m) (monomialCoefficientGluedChartMap300 R m n i)
    (monomialCoefficientChartToBase300 R m n i.monomials i.zeroIndex)
    (monomialCoefficientGluedChartMap_toBase300 R m n i)
    (nativePolynomialScalarMap300 R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
    (nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
    (nativePolynomialScalar_isPullback300 R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)

lemma monomialCoefficientPolynomialChartToAmbient_toH300 (i : MonomialCoefficientChartIndex300 m n) :
    monomialCoefficientPolynomialChartToAmbient300 R m n i ≫ monomialCoefficientAmbientToH300 R m n =
    nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m ≫
      monomialCoefficientGluedChartMap300 R m n i :=
  nativeAmbientChartLift_fst300 _ _ _ _ _ _ _ _

lemma monomialCoefficientPolynomialChartToAmbient_toGround300 (i : MonomialCoefficientChartIndex300 m n) :
    monomialCoefficientPolynomialChartToAmbient300 R m n i ≫
      monomialCoefficientAmbientToGroundAffine300 R m n =
    nativePolynomialScalarMap300 R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m :=
  nativeAmbientChartLift_snd300 _ _ _ _ _ _ _ _

/-- Genuine Cartesian chart identification; no atlas/IsIso premise is supplied. -/
lemma monomialCoefficientPolynomialChart_isPullback300 (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialCoefficientPolynomialChartToAmbient300 R m n i)
      (nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
      (monomialCoefficientAmbientToH300 R m n)
      (monomialCoefficientGluedChartMap300 R m n i) :=
  nativeAmbientChartLift_isPullback300 _ _ _ _ _ _ _ _

/-- Exact original polynomial spectrum Iso to the native pulled-back coefficient-cover component. -/
def monomialCoefficientPolynomialChartPullbackIso300 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m)
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex))) ≅
    pullback (monomialCoefficientAmbientToH300 R m n)
      (monomialCoefficientGluedChartMap300 R m n i) :=
  (monomialCoefficientPolynomialChart_isPullback300 R m n i).isoPullback

lemma monomialCoefficientPolynomialChartPullbackIso_hom_fst300 (i : MonomialCoefficientChartIndex300 m n) :
    (monomialCoefficientPolynomialChartPullbackIso300 R m n i).hom ≫ pullback.fst _ _ =
      monomialCoefficientPolynomialChartToAmbient300 R m n i :=
  (monomialCoefficientPolynomialChart_isPullback300 R m n i).isoPullback_hom_fst

lemma monomialCoefficientPolynomialChartPullbackIso_hom_snd300 (i : MonomialCoefficientChartIndex300 m n) :
    (monomialCoefficientPolynomialChartPullbackIso300 R m n i).hom ≫ pullback.snd _ _ =
      nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m :=
  (monomialCoefficientPolynomialChart_isPullback300 R m n i).isoPullback_hom_snd

lemma monomialCoefficientPolynomialChartToAmbient_isOpenImmersion300 (i : MonomialCoefficientChartIndex300 m n) :
    IsOpenImmersion (monomialCoefficientPolynomialChartToAmbient300 R m n i) := by
  letI := monomialCoefficientGluedChartMap_isOpenImmersion300 R m n i
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (monomialCoefficientPolynomialChart_isPullback300 R m n i).flip
    (inferInstance : IsOpenImmersion (monomialCoefficientGluedChartMap300 R m n i))

/-- Native genuine open cover of the actual ambient, by the ORIGINAL coefficient polynomial spectra. -/
def monomialCoefficientAmbientPolynomialOpenCover300 :
    (monomialCoefficientAmbient300 R m n).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300
    ((monomialCoefficientGluedOpenCover300 R m n).pullback₁ (monomialCoefficientAmbientToH300 R m n))
    (fun i => Spec (.of (MvPolynomial (Fin m)
      (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex))))
    (fun i => monomialCoefficientPolynomialChartPullbackIso300 R m n i.down)

lemma monomialCoefficientAmbientPolynomialOpenCover_map300
    (i : ULift.{u} (MonomialCoefficientChartIndex300 m n)) :
    (monomialCoefficientAmbientPolynomialOpenCover300 R m n).f i =
      monomialCoefficientPolynomialChartToAmbient300 R m n i.down := by
  change (monomialCoefficientPolynomialChartPullbackIso300 R m n i.down).hom ≫
    pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialCoefficientGluedChartMap300 R m n i.down) = _
  exact monomialCoefficientPolynomialChartPullbackIso_hom_fst300 R m n i.down

end PfaffianDescent
