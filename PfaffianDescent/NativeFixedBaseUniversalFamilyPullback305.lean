import PfaffianDescent.FixedBaseTestAmbientMap305
import PfaffianDescent.MonomialCoefficientGlobalUniversalFamily300
import PfaffianDescent.NativeWholeIdealChartFamily302

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeWholeIdealChartCompositeCompare305
    {X Y Z T : Scheme.{u}} (J : X.IdealSheafData)
    (d : Y ⟶ X) (a : Z ⟶ Y) (t : T ⟶ X) (b : Z ⟶ T)
    (I : T.IdealSheafData) (h : a ≫ d = b ≫ t) (ht : J.comap t = I) :
    (J.comap d).comap a = I.comap b := by
  calc
    _ = J.comap (a ≫ d) := (J.comap_comp a d).symm
    _ = J.comap (b ≫ t) := congrArg J.comap h
    _ = (J.comap t).comap b := J.comap_comp b t
    _ = _ := congrArg (fun K : T.IdealSheafData => K.comap b) ht

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)
variable (g : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n)
variable (hg : g ≫ monomialCoefficientGluedToBase300 R m n =
  Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- Reverse construction: native pullback of the ACTUALLY descended universal family along g. -/
def fixedBaseUniversalFamilyPullback305 :
    FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n :=
  finiteFlatHilbertBaseChange195 (fixedBaseTestAmbientMap305 R m n g hg)
    (nativePolynomialProjection300 A m) (monomialCoefficientAmbientToH300 R m n) g
    (fixedBaseTestAmbientMap_isPullback305 R m n g hg) n
    (monomialCoefficientGlobalUniversalFamily300 R m n)

lemma fixedBaseUniversalFamilyPullback_ideal305 :
    (fixedBaseUniversalFamilyPullback305 R m n g hg).val =
      (monomialCoefficientGlobalUniversalFamily300 R m n).val.comap
        (fixedBaseTestAmbientMap305 R m n g hg) := rfl

/-- Canonical coefficient pullback retains exactly the entire universal kernel under the literal polynomial map. -/
lemma cyclicCoefficientUniversalFamilyPullback_ideal305
    {T : Type u} [CommRing T] [Algebra R T]
    (i : MonomialCoefficientChartIndex300 m n)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] T) :
    (cyclicCoefficientUniversalFamilyPullback302 R m n i.monomials i.zeroIndex p).val =
      (universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex).val.comap
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) p.toRingHom))) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Exact native whole-ideal restriction on any original test patch factoring through its coefficient chart. -/
lemma fixedBaseUniversalFamilyPullback_chartIdeal305
    {T : Type u} [CommRing T] [Algebra R T]
    (i : MonomialCoefficientChartIndex300 m n) (f : A →ₐ[R] T)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] T)
    (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n i) :
    (fixedBaseUniversalFamilyPullback305 R m n g hg).val.comap
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom))) =
      (cyclicCoefficientUniversalFamilyPullback302 R m n i.monomials i.zeroIndex p).val := by
  rw [fixedBaseUniversalFamilyPullback_ideal305, cyclicCoefficientUniversalFamilyPullback_ideal305]
  exact nativeWholeIdealChartCompositeCompare305
    (monomialCoefficientGlobalUniversalFamily300 R m n).val
    (fixedBaseTestAmbientMap305 R m n g hg)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)))
    (monomialCoefficientPolynomialChartToAmbient300 R m n i)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) p.toRingHom)))
    (universalCyclicAffineHilbertPoint289 R m n i.monomials i.zeroIndex).val
    (fixedBaseTestAmbientMap_chartFactor305 R m n g hg i f p hf)
    (monomialCoefficientUniversalWholeIdeal_chart300 R m n i)

end PfaffianDescent
