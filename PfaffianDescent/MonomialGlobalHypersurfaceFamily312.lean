import PfaffianDescent.MonomialRestrictedFamilyChartComparison312
import PfaffianDescent.NativeWholeIdealContainment312
import PfaffianDescent.NativeFiniteFlatClosedAmbientFactor312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Original ground affine coordinates of the actual restricted global ambient. -/
def monomialPolynomialContainmentAmbientToGround312 :
    monomialPolynomialContainmentAmbient310 R m n p ⟶ Spec (.of (MvPolynomial (Fin m) R)) :=
  pullback.fst (monomialCoefficientAmbientToH300 R m n)
    (monomialPolynomialContainmentLocusInclusion310 R m n p) ≫
      monomialCoefficientAmbientToGroundAffine300 R m n

set_option backward.isDefEq.respectTransparency.types false in
lemma monomialClosedPolynomialChartToGround312 (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedPolynomialChartToAmbient312 R m n p i ≫
        monomialPolynomialContainmentAmbientToGround312 R m n p =
      nativePolynomialScalarMap300 R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m := by
  exact (Category.assoc
    (monomialClosedPolynomialChartToAmbient312 R m n p i)
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (monomialCoefficientAmbientToGroundAffine300 R m n)).symm.trans
      ((congrArg
        (fun a : Spec (.of (MvPolynomial (Fin m)
            (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) ⟶
              monomialCoefficientAmbient300 R m n =>
          a ≫ monomialCoefficientAmbientToGroundAffine300 R m n)
        (monomialClosedPolynomialChartToAmbient_fst312 R m n p i)).trans
          (fixedBaseTestAmbientMap_toGround305 R m n _ _))

/-- The literal original p=0 whole kernel pulled to the actual restricted ambient. -/
def monomialPolynomialHypersurfaceIdeal312 :
    (monomialPolynomialContainmentAmbient310 R m n p).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap
    (monomialPolynomialContainmentAmbientToGround312 R m n p)

set_option backward.isDefEq.respectTransparency.types false in
lemma monomialPolynomialHypersurfaceIdeal_chart312 (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialHypersurfaceIdeal312 R m n p).comap
        (monomialClosedPolynomialChartToAmbient312 R m n p i) =
      (Spec.map (CommRingCat.ofHom
        (R := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
        (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
        (Ideal.Quotient.mk (Ideal.span
          {MvPolynomial.map
            (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))).ker := by
  have hc := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap_comp
    (monomialClosedPolynomialChartToAmbient312 R m n p i)
    (monomialPolynomialContainmentAmbientToGround312 R m n p)
  have hg := congrArg
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap
    (monomialClosedPolynomialChartToGround312 R m n p i)
  exact hc.symm.trans (hg.trans (nativePolynomialHypersurfaceKernel_comap312 R
    (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m p))

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual whole universal family lies in the literal original hypersurface.
The containment is derived from finite coefficient equations and the actual cover. -/
theorem monomialRestrictedUniversalFamily_hypersurfaceContainment312 :
    monomialPolynomialHypersurfaceIdeal312 R m n p ≤
      (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val := by
  apply wholeIdeal_le_of_openCover_comaps312
    (monomialClosedPolynomialAmbientOpenCover312 R m n p)
  intro k
  change ULift (MonomialCoefficientChartIndex300 m n) at k
  let i := k.down
  have hlocal :
      (monomialPolynomialHypersurfaceIdeal312 R m n p).comap
          (monomialClosedPolynomialChartToAmbient312 R m n p i) ≤
        (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val.comap
          (monomialClosedPolynomialChartToAmbient312 R m n p i) := by
    rw [monomialPolynomialHypersurfaceIdeal_chart312 R m n p i,
      monomialRestrictedUniversalFamily_chartWholeIdeal312 R m n p i]
    change (Spec.map (CommRingCat.ofHom
        (R := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
        (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
        (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map
          (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))).ker ≤
      (Spec.map (CommRingCat.ofHom
        (R := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
        (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
          (monomialPolynomialContainmentChartWholeIdeal310 R m n p i).val)
        (Ideal.Quotient.mk (monomialPolynomialContainmentChartWholeIdeal310 R m n p i).val))).ker
    apply (nativeAffineQuotientKernel_le_iff312 _ _).mpr
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (monomialPolynomialContainmentChartWholeIdeal_contains310 R m n p i)
  exact Eq.mpr
    (congrArg
      (fun f : Spec (.of (MvPolynomial (Fin m)
          (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) ⟶
            monomialPolynomialContainmentAmbient310 R m n p =>
        (monomialPolynomialHypersurfaceIdeal312 R m n p).comap f ≤
          (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val.comap f)
      (monomialClosedPolynomialAmbientOpenCover_map312 R m n p i)) hlocal

/-- Genuine global finite-flat family inside the original p=0 ambient over
its constructed coefficient locus; no factorization or containment premise. -/
def monomialPolynomialHypersurfaceGlobalFamily312 :
    FiniteFlatHilbertPoint195
      ((monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
        monomialPolynomialContainmentAmbientToLocus310 R m n p) n :=
  nativeFiniteFlatPointOfIdealContainment312
    (monomialPolynomialContainmentAmbientToLocus310 R m n p) n
    (monomialPolynomialHypersurfaceIdeal312 R m n p)
    (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p)
    (monomialRestrictedUniversalFamily_hypersurfaceContainment312 R m n p)

/-- Returning from p=0 to the original actual ambient recovers the entire
restricted global universal ideal, including its native embedding. -/
lemma monomialPolynomialHypersurfaceGlobalFamily_ambientIdeal312 :
    (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val.map
        (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι =
      (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val :=
  nativeFiniteFlatPointOfIdealContainment_ambientIdeal312 _ _ _ _ _

end PfaffianDescent
end
