import PfaffianDescent.MonomialRelativeUniversalPullback309
import PfaffianDescent.NativeFixedBaseUniversalFamilyPullback305
import PfaffianDescent.NativeWholeIdealContainment312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeAmbientFirstProjectionCompose312
    {C : Type*} [Category C] {Q P E T A H : C}
    (v : Q ⟶ P) (d : P ⟶ E) (j : E ⟶ H) (q : P ⟶ T)
    (p : Q ⟶ A) (a : A ⟶ T) (g : T ⟶ H)
    (hv : v ≫ q = p ≫ a) (hd : d ≫ j = q ≫ g) :
    (v ≫ d) ≫ j = p ≫ (a ≫ g) :=
  (Category.assoc v d j).trans
    ((congrArg (fun z => v ≫ z) hd).trans
      ((Category.assoc v q g).symm.trans
        ((congrArg (fun z => z ≫ g) hv).trans (Category.assoc p a g))))

private lemma nativeAmbientSecondProjectionCompose312
    {C : Type*} [Category C] {Q P E Y : C}
    (v : Q ⟶ P) (d : P ⟶ E) (j : E ⟶ Y) (s : P ⟶ Y)
    (hd : d ≫ j = s) : (v ≫ d) ≫ j = v ≫ s :=
  (Category.assoc v d j).trans (congrArg (fun z => v ≫ z) hd)

private lemma nativeWholeIdealComposite312 {X Y Z : Scheme.{u}}
    (I : Z.IdealSheafData) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : (I.comap b).comap a = I.comap c :=
  (I.comap_comp a b).symm.trans (congrArg I.comap h)

/-- Whole-kernel factoring is equivalent to vanishing of the whole pulled ideal. -/
lemma nativeWholeIdeal_le_ker_iff_comap_eq_bot312
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I ≤ f.ker ↔ I.comap f = ⊥ := by
  rw [← Scheme.IdealSheafData.map_bot f,
    Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m : ℕ)
variable (T : Over (Spec (.of R))) (a : Spec (.of A) ⟶ T.left)
variable (ha : a ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- Actual polynomial chart above ANY original-base test, constructed from
its affine coefficient map; no affine assumption on the whole test. -/
def nativeRelativePolynomialChartMap312 :
    Spec (.of (MvPolynomial (Fin m) A)) ⟶ pullback T.hom (nativePolynomialProjection300 R m) :=
  nativeAmbientChartLift300 T.hom (nativePolynomialProjection300 R m) a
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) ha
    (nativePolynomialScalarMap300 R A m) (nativePolynomialProjection300 A m)
    (nativePolynomialScalar_isPullback300 R A m)

lemma nativeRelativePolynomialChartMap_toTest312 :
    nativeRelativePolynomialChartMap312 R m T a ha ≫
        relativeHilbertFamily197 (nativePolynomialProjection300 R m) T =
      nativePolynomialProjection300 A m ≫ a :=
  nativeAmbientChartLift_fst300 _ _ _ _ _ _ _ _

lemma nativeRelativePolynomialChartMap_toGround312 :
    nativeRelativePolynomialChartMap312 R m T a ha ≫
        pullback.snd T.hom (nativePolynomialProjection300 R m) =
      nativePolynomialScalarMap300 R A m :=
  nativeAmbientChartLift_snd300 _ _ _ _ _ _ _ _

lemma nativeRelativePolynomialChartMap_isPullback312 :
    IsPullback (nativeRelativePolynomialChartMap312 R m T a ha)
      (nativePolynomialProjection300 A m)
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) a :=
  nativeAmbientChartLift_isPullback300 _ _ _ _ _ _ _ _

variable (n : ℕ) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)

include ha in
lemma nativeRelativePolynomialClassifier_overBase312 :
    (a ≫ g.left) ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  exact (Category.assoc a g.left (monomialCoefficientGluedToBase300 R m n)).trans
    ((congrArg (fun h => a ≫ h) (Over.w g)).trans ha)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original relative ambient map agrees with canonical305 on BOTH projections. -/
lemma nativeRelativePolynomialChartMap_universalAmbient312 :
    nativeRelativePolynomialChartMap312 R m T a ha ≫
        relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g =
      fixedBaseTestAmbientMap305 R m n (a ≫ g.left)
        (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g) := by
  apply pullback.hom_ext
  · have hd : relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g ≫
        monomialCoefficientAmbientToH300 R m n =
      relativeHilbertFamily197 (nativePolynomialProjection300 R m) T ≫ g.left :=
      relativeHilbertAmbientMap_fst197 (nativePolynomialProjection300 R m) g
    exact (nativeAmbientFirstProjectionCompose312
      (nativeRelativePolynomialChartMap312 R m T a ha)
      (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
      (monomialCoefficientAmbientToH300 R m n)
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T)
      (nativePolynomialProjection300 A m) a g.left
      (nativeRelativePolynomialChartMap_toTest312 R m T a ha) hd).trans
        (fixedBaseTestAmbientMap_toH305 R m n _ _).symm
  · have hd : relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g ≫
        monomialCoefficientAmbientToGroundAffine300 R m n =
      pullback.snd T.hom (nativePolynomialProjection300 R m) :=
      relativeHilbertAmbientMap_snd197 (nativePolynomialProjection300 R m) g
    exact (nativeAmbientSecondProjectionCompose312
      (nativeRelativePolynomialChartMap312 R m T a ha)
      (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
      (monomialCoefficientAmbientToGroundAffine300 R m n)
      (pullback.snd T.hom (nativePolynomialProjection300 R m)) hd).trans
        ((nativeRelativePolynomialChartMap_toGround312 R m T a ha).trans
          (fixedBaseTestAmbientMap_toGround305 R m n _ _).symm)

set_option backward.isDefEq.respectTransparency.types false in
lemma nativeRelativePolynomialUniversalPullback_wholeIdeal312 :
    (monomialRelativeUniversalPullback309 R m n T g).val.comap
        (nativeRelativePolynomialChartMap312 R m T a ha) =
      (fixedBaseUniversalFamilyPullback305 R m n (a ≫ g.left)
        (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g)).val := by
  exact nativeWholeIdealComposite312 (monomialCoefficientUniversalWholeIdeal300 R m n)
    (nativeRelativePolynomialChartMap312 R m T a ha)
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
    (fixedBaseTestAmbientMap305 R m n (a ≫ g.left)
      (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g))
    (nativeRelativePolynomialChartMap_universalAmbient312 R m T a ha n g)

end PfaffianDescent
end
