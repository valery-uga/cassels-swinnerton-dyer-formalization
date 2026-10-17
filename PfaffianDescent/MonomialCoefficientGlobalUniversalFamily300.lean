import PfaffianDescent.NativeHilbertChartRestrictionDescent300
import PfaffianDescent.MonomialCoefficientAmbientWholeIdealCompatibility300
import PfaffianDescent.CompatibleClosedSubschemeOpenCoverDescent
import PfaffianDescent.NativeAffineUniversalWholeFamily289

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Transport a literal comap through equality of its native chart morphism. -/
private lemma globalFamilyNativeIdealComap_eq_map300
    {X Y : Scheme.{u}} (J : Y.IdealSheafData) {f g : X ⟶ Y} (h : f = g) :
    J.comap f = J.comap g :=
  congrArg (fun a : X ⟶ Y => J.comap a) h
variable (R : Type u) [CommRing R] (m n : ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-- Native polynomial ring over R, before forming either original quotient. -/
private instance globalFamilyMatrixCoefficientPolynomialCommRing300 :
    CommRing (MatrixCoefficientPolynomial280 R m n) :=
  @AddMonoidAlgebra.commRing R (MatrixCoefficientIndex280 m n →₀ ℕ)
    ‹CommRing R› inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- First ORIGINAL quotient ring, with its existing native quotient structure. -/
private instance globalFamilyCommutingCoefficientCommRing300 :
    CommRing (CommutingMatrixCoefficientAlgebra280 R m n) :=
  @Ideal.Quotient.commRing (MatrixCoefficientPolynomial280 R m n)
    (globalFamilyMatrixCoefficientPolynomialCommRing300 R m n)
    (commutingMatrixIdeal280 R m n)

set_option backward.isDefEq.respectTransparency.types false in
/-- Second ORIGINAL cyclic quotient ring, retaining the literal relation ideal. -/
private instance globalFamilyCyclicCoefficientCommRing300
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    CommRing (UniversalCyclicCoefficientAlgebra282 R m n B k) :=
  @Ideal.Quotient.commRing (CommutingMatrixCoefficientAlgebra280 R m n)
    (globalFamilyCommutingCoefficientCommRing300 R m n)
    (universalCyclicCoefficientIdeal282 R m n B k)

set_option backward.isDefEq.respectTransparency.types false in
/-- SAME native polynomial ring, with the actual coefficient quotient ring pinned. -/
private instance globalFamilyCoefficientPolynomialCommRing300
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    CommRing (MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k)) :=
  @AddMonoidAlgebra.commRing (UniversalCyclicCoefficientAlgebra282 R m n B k)
    (Fin m →₀ ℕ) (globalFamilyCyclicCoefficientCommRing300 R m n B k) inferInstance


/-- The exact original289 point ideal is the literal original quotient kernel. -/
private lemma globalFamilyOriginalChartKernel_eq_pointIdeal300
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialCoefficientChartWholeIdealSheaf300 R m n i =
      (universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex).val := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual H-cover component version of the already derived original chart square. -/
private lemma globalFamilyOriginalCoefficientCover_isPullback300
    (i : ULift.{u} (MonomialCoefficientChartIndex300 m n)) :
    IsPullback (monomialCoefficientPolynomialChartToAmbient300 R m n i.down)
      (nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex) m)
      (monomialCoefficientAmbientToH300 R m n)
      ((monomialCoefficientGluedOpenCover300 R m n).f i) := by
  change IsPullback (monomialCoefficientPolynomialChartToAmbient300 R m n i.down)
    (nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex) m)
    (monomialCoefficientAmbientToH300 R m n)
    (monomialCoefficientGluedChartMap300 R m n i.down)
  exact monomialCoefficientPolynomialChart_isPullback300 R m n i.down

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual compatible original universal kernels produce a global whole ideal;
no global ideal or gluing outcome is an input. -/
theorem monomialCoefficientUniversalWholeIdeal_exists300 :
    ∃ J : (monomialCoefficientAmbient300 R m n).IdealSheafData,
      ∀ i : MonomialCoefficientChartIndex300 m n,
        J.comap (monomialCoefficientPolynomialChartToAmbient300 R m n i) =
          (universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex).val := by
  obtain ⟨J, hJ⟩ := compatibleClosedSubschemes_openCover_exists_globalIdeal
    (monomialCoefficientAmbientPolynomialOpenCover300 R m n)
    (fun i => monomialCoefficientChartWholeIdealSheaf300 R m n i.down)
    (monomialCoefficientChartWholeIdeal_actualOpenCover_comap300 R m n)
  refine ⟨J, ?_⟩
  intro i
  have hi := hJ (ULift.up i)
  have hc := globalFamilyNativeIdealComap_eq_map300 J
    (monomialCoefficientAmbientPolynomialOpenCover_map300 R m n (ULift.up i))
  exact hc.symm.trans (hi.trans
    (globalFamilyOriginalChartKernel_eq_pointIdeal300 R m n i))

/-- A chosen global ideal, constructed from the original literal whole ideals. -/
def monomialCoefficientUniversalWholeIdeal300 :
    (monomialCoefficientAmbient300 R m n).IdealSheafData :=
  Classical.choose (monomialCoefficientUniversalWholeIdeal_exists300 R m n)

lemma monomialCoefficientUniversalWholeIdeal_chart300
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (monomialCoefficientPolynomialChartToAmbient300 R m n i) =
      (universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex).val :=
  Classical.choose_spec (monomialCoefficientUniversalWholeIdeal_exists300 R m n) i

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine global finite-flat degree-n embedded family on the SAME H-relative
affine ambient. Original289 supplies all local finite/flat/rank properties internally. -/
def monomialCoefficientGlobalUniversalFamily300 :
    FiniteFlatHilbertPoint195 (monomialCoefficientAmbientToH300 R m n) n :=
  nativeHilbertPointOfChartRestrictions300 (monomialCoefficientAmbientToH300 R m n)
    (monomialCoefficientGluedOpenCover300 R m n)
    (fun i => Spec (.of (MvPolynomial (Fin m)
      (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex))))
    (fun i => monomialCoefficientPolynomialChartToAmbient300 R m n i.down)
    (fun i => nativePolynomialProjection300
      (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex) m)
    (fun i => globalFamilyOriginalCoefficientCover_isPullback300 R m n i) n
    (fun i => universalCyclicAffineHilbertPoint289 R m n i.down.monomials i.down.zeroIndex)
    (monomialCoefficientUniversalWholeIdeal300 R m n)
    (fun i => monomialCoefficientUniversalWholeIdeal_chart300 R m n i.down)

lemma monomialCoefficientGlobalUniversalFamily_ideal300 :
    (monomialCoefficientGlobalUniversalFamily300 R m n).val =
      monomialCoefficientUniversalWholeIdeal300 R m n := rfl

/-- SAME original polynomial-chart pullback is EXACTLY the original289 family,
including its whole ideal, nilpotents, native projection and coefficient action. -/
theorem monomialCoefficientGlobalUniversalFamily_chart300
    (i : MonomialCoefficientChartIndex300 m n) :
    finiteFlatHilbertBaseChange195
      (monomialCoefficientPolynomialChartToAmbient300 R m n i)
      (nativePolynomialProjection300
        (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
      (monomialCoefficientAmbientToH300 R m n)
      (monomialCoefficientGluedChartMap300 R m n i)
      (monomialCoefficientPolynomialChart_isPullback300 R m n i) n
      (monomialCoefficientGlobalUniversalFamily300 R m n) =
      universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex := by
  apply Subtype.ext
  exact monomialCoefficientUniversalWholeIdeal_chart300 R m n i

end PfaffianDescent
end
