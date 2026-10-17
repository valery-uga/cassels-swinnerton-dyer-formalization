import PfaffianDescent.MonomialPolynomialLocusFinitePresentation312
import AllCharacteristics.SmoothPointLifting

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

private lemma nativePolynomialLocusSmoothMapEquality312
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  cases h
  rfl

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

private instance monomialPolynomialLocusToBase_lfp312 :
    LocallyOfFinitePresentation (monomialPolynomialContainmentRepresentingObject312 R m n p).hom :=
  monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 R m n p

private instance monomialPolynomialLocusCoefficientSpec_lfp312
    (i : MonomialCoefficientChartIndex300 m n) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)))) :=
  monomialPolynomialContainmentCoefficientSpec_locallyOfFinitePresentation312 R m n p i

private instance monomialPolynomialLocusCoefficientChart_open312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsOpenImmersion (monomialClosedCoefficientChartToLocus312 R m n p i) :=
  Eq.mp (congrArg
    (fun f : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
      monomialPolynomialContainmentLocus310 R m n p => IsOpenImmersion f)
    (monomialClosedCoefficientLocusOpenCover_map312 R m n p i))
    ((monomialClosedCoefficientLocusOpenCover312 R m n p).map_prop (ULift.up i))

/-- Genuine native smooth open of the ACTUAL constructed polynomial coefficient locus.
No smoothness or LFP outcome is supplied to this definition. -/
def monomialPolynomialContainmentSmoothOpen312 :
    (monomialPolynomialContainmentLocus310 R m n p).Opens :=
  (monomialPolynomialContainmentRepresentingObject312 R m n p).hom.smoothLocus

/-- Exact original base map on that actual smooth open. -/
def monomialPolynomialContainmentSmoothToBase312 :
    (monomialPolynomialContainmentSmoothOpen312 R m n p).toScheme ⟶ Spec (.of R) :=
  (monomialPolynomialContainmentSmoothOpen312 R m n p).ι ≫
    (monomialPolynomialContainmentRepresentingObject312 R m n p).hom

/-- Smoothness is a consequence of the genuine native smooth locus, using
the existing production smooth-on-smooth-locus theorem rather than a new hypothesis. -/
theorem monomialPolynomialContainmentSmoothToBase_smooth312 :
    Smooth (monomialPolynomialContainmentSmoothToBase312 R m n p) :=
  AllCharacteristics.smooth_on_smoothLocus
    (monomialPolynomialContainmentRepresentingObject312 R m n p).hom

/-- Original-point membership is EXACT formal smoothness of the actual native stalk map.
This criterion does not assert that an LCI point already meets it. -/
lemma monomialPolynomialContainmentSmoothOpen_mem_iff312
    (x : monomialPolynomialContainmentLocus310 R m n p) :
    x ∈ monomialPolynomialContainmentSmoothOpen312 R m n p ↔
      (((monomialPolynomialContainmentRepresentingObject312 R m n p).hom.stalkMap x).hom).FormallySmooth :=
  Scheme.Hom.mem_smoothLocus

/-- The global genuine smooth open restricts to the EXACT smooth locus of
original finite-equation quotient scalar maps on each actual coefficient chart. -/
lemma monomialPolynomialContainmentSmoothOpen_chart312
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedCoefficientChartToLocus312 R m n p i ⁻¹ᵁ
        monomialPolynomialContainmentSmoothOpen312 R m n p =
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)))).smoothLocus :=
  by
    letI : LocallyOfFinitePresentation
        (monomialPolynomialContainmentRepresentingObject312 R m n p).hom :=
      monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 R m n p
    letI : IsOpenImmersion (monomialClosedCoefficientChartToLocus312 R m n p i) :=
      monomialPolynomialLocusCoefficientChart_open312 R m n p i
    have hspec := monomialPolynomialContainmentCoefficientSpec_locallyOfFinitePresentation312 R m n p i
    have hcomp : LocallyOfFinitePresentation
        (monomialClosedCoefficientChartToLocus312 R m n p i ≫
          (monomialPolynomialContainmentRepresentingObject312 R m n p).hom) :=
      Eq.mpr (congrArg
        (fun f : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
          Spec (.of R) => LocallyOfFinitePresentation f)
        (monomialPolynomialContainmentChart_toBase312 R m n p i)) hspec
    exact (@Scheme.Hom.preimage_smoothLocus_eq _ _ _
      (monomialClosedCoefficientChartToLocus312 R m n p i)
      (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
      (monomialPolynomialLocusCoefficientChart_open312 R m n p i)
      (monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 R m n p)).trans
        (@nativePolynomialLocusSmoothMapEquality312 _ _ _ _ hcomp hspec
          (monomialPolynomialContainmentChart_toBase312 R m n p i))

end PfaffianDescent
end
