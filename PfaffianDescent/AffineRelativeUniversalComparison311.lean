import PfaffianDescent.AffineRelativePolynomialPresentation309
import PfaffianDescent.MonomialRelativeUniversalPullback309
import PfaffianDescent.NativeAffineHilbertClassification308
import PfaffianDescent.NativeIdealComapIso300

/-! SOURCE ONLY311. Canonical affine presentation, with the original Γ-algebra
action, compares literal relative197 pullback to the checked polynomial308
pullback. No classification, ambient-map equality or ideal equality is supplied
as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Ordinary cancellation before any original native aliases are substituted. -/
private lemma nativePresentedFirstProjection311
    {C : Type*} [Category C] {Q X Y S A H : C}
    (v : Q ⟶ X) (d : X ⟶ Y) (j : Y ⟶ H) (q : X ⟶ S)
    (p : Q ⟶ A) (e : S ≅ A) (g : A ⟶ H)
    (hv : v ≫ q = p ≫ e.inv)
    (hd : d ≫ j = q ≫ (e.hom ≫ g)) : (v ≫ d) ≫ j = p ≫ g := by
  calc
    _ = v ≫ (d ≫ j) := Category.assoc _ _ _
    _ = v ≫ (q ≫ (e.hom ≫ g)) := congrArg (fun k => v ≫ k) hd
    _ = (v ≫ q) ≫ (e.hom ≫ g) := (Category.assoc _ _ _).symm
    _ = (p ≫ e.inv) ≫ (e.hom ≫ g) := congrArg (fun k => k ≫ (e.hom ≫ g)) hv
    _ = p ≫ (e.inv ≫ e.hom ≫ g) := Category.assoc _ _ _
    _ = p ≫ g := congrArg (fun k => p ≫ k) (e.inv_hom_id_assoc g)

/-- Ordinary typed projection composition, with no native rewrite matching. -/
private lemma nativeSecondProjectionComposite311
    {C : Type*} [Category C] {Q X Y G : C}
    (v : Q ⟶ X) (d : X ⟶ Y) (j : Y ⟶ G) (s : X ⟶ G)
    (hd : d ≫ j = s) : (v ≫ d) ≫ j = v ≫ s :=
  (Category.assoc _ _ _).trans (congrArg (fun k => v ≫ k) hd)

/-- Ordinary whole-ideal composition transport before any concrete ambient is substituted. -/
private lemma nativeWholeIdealComposite311 {X Y Z : Scheme.{u}}
    (I : Z.IdealSheafData) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : (I.comap b).comap a = I.comap c :=
  (I.comap_comp a b).symm.trans (congrArg I.comap h)

variable (R : Type u) [CommRing R] {S : Scheme.{u}} [IsAffine S]
variable (f : S ⟶ Spec (.of R)) (m n : ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual affine presentation identifies fixed-base polynomial classifiers with
the native slice morphisms from the SAME test scheme. -/
def actualAffineRelativeHomEquiv311 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    MonomialFixedBaseHom308 R Γ(S, ⊤) m n ≃
      ((Over.mk f) ⟶ monomialCoefficientRepresentingObject309 R m n) := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  refine
    { toFun := fun g => Over.homMk (S.isoSpec.hom ≫ g.val) ?_
      invFun := fun h => ⟨S.isoSpec.inv ≫ h.left, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (S.isoSpec.hom ≫ g.val) ≫ monomialCoefficientGluedToBase300 R m n = f
    rw [Category.assoc, g.property, actualAffineTestCoefficientSpecMap309]
    exact S.isoSpec.hom_inv_id_assoc f
  · change (S.isoSpec.inv ≫ h.left) ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤)))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => S.isoSpec.inv ≫ q) (Over.w h)).trans
        (actualAffineTestCoefficientSpecMap309 R f).symm)
  · intro g
    apply Subtype.ext
    change S.isoSpec.inv ≫ (S.isoSpec.hom ≫ g.val) = g.val
    exact S.isoSpec.inv_hom_id_assoc g.val
  · intro h
    apply Over.OverMorphism.ext
    change S.isoSpec.hom ≫ (S.isoSpec.inv ≫ h.left) = h.left
    exact S.isoSpec.hom_inv_id_assoc h.left

lemma actualAffineRelativeHomEquiv_left311 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    ∀ g : MonomialFixedBaseHom308 R Γ(S, ⊤) m n,
      ((actualAffineRelativeHomEquiv311 R f m n) g).left = S.isoSpec.hom ≫ g.val := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  intro g
  rfl

/-- The original relative affine presentation has its literal ground projection. -/
lemma actualAffineRelativePolynomialChartMap_toGround311 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    actualAffineRelativePolynomialChartMap309 R f m ≫
      pullback.snd f (nativePolynomialProjection300 R m) =
        nativePolynomialScalarMap300 R Γ(S, ⊤) m := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  exact nativeAmbientChartLift_snd300 _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Comparison is proved on BOTH actual pullback projections. -/
lemma actualAffineRelativeUniversalAmbient_comp311 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    ∀ g : MonomialFixedBaseHom308 R Γ(S, ⊤) m n,
      actualAffineRelativePolynomialChartMap309 R f m ≫
        relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m)
          ((actualAffineRelativeHomEquiv311 R f m n) g) =
      fixedBaseTestAmbientMap305 R m n g.val g.property := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  intro g
  let h : Over.mk f ⟶ monomialCoefficientRepresentingObject309 R m n :=
    (actualAffineRelativeHomEquiv311 R f m n) g
  let g0 : Spec (.of Γ(S, ⊤)) ⟶ monomialCoefficientGluedScheme300 R m n := g.val
  let v := actualAffineRelativePolynomialChartMap309 R f m
  let d := relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) h
  apply pullback.hom_ext
  · have hd : d ≫ relativeHilbertFamily197 (nativePolynomialProjection300 R m)
          (monomialCoefficientRepresentingObject309 R m n) =
        relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f) ≫
          (S.isoSpec.hom ≫ g0) :=
      (relativeHilbertAmbientMap_fst197 (nativePolynomialProjection300 R m) h).trans
        (congrArg
          (fun k : S ⟶ monomialCoefficientGluedScheme300 R m n =>
            relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f) ≫ k)
          (actualAffineRelativeHomEquiv_left311 R f m n g))
    exact (nativePresentedFirstProjection311 v d
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m)
        (monomialCoefficientRepresentingObject309 R m n))
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f))
      (nativePolynomialProjection300 Γ(S, ⊤) m) S.isoSpec g0
      (actualAffineRelativePolynomialChartMap_toTest309 R f m) hd).trans
        (fixedBaseTestAmbientMap_toH305 R m n g.val g.property).symm
  · have hd : d ≫ pullback.snd
          (monomialCoefficientRepresentingObject309 R m n).hom
          (nativePolynomialProjection300 R m) =
        pullback.snd (Over.mk f).hom (nativePolynomialProjection300 R m) :=
      relativeHilbertAmbientMap_snd197 (nativePolynomialProjection300 R m)
        (T0 := Over.mk f) (T1 := monomialCoefficientRepresentingObject309 R m n) h
    exact (nativeSecondProjectionComposite311 v d
      (pullback.snd (monomialCoefficientRepresentingObject309 R m n).hom
        (nativePolynomialProjection300 R m))
      (pullback.snd (Over.mk f).hom (nativePolynomialProjection300 R m)) hd).trans
        ((actualAffineRelativePolynomialChartMap_toGround311 R f m).trans
          (fixedBaseTestAmbientMap_toGround305 R m n g.val g.property).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of WHOLE finite-flat points after the actual affine presentation. -/
lemma actualAffineRelativeUniversalPullback_onPolynomialChart311 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    ∀ g : MonomialFixedBaseHom308 R Γ(S, ⊤) m n,
      actualAffineRelativePointOnPolynomialChart309 R f m n
        (monomialRelativeUniversalPullback309 R m n (Over.mk f)
          ((actualAffineRelativeHomEquiv311 R f m n) g)) =
      monomialFixedBasePointPullback308 R m n g := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  intro g
  apply Subtype.ext
  change ((monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m)
        ((actualAffineRelativeHomEquiv311 R f m n) g))).comap
      (actualAffineRelativePolynomialChartMap309 R f m) =
    (monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (fixedBaseTestAmbientMap305 R m n g.val g.property)
  exact nativeWholeIdealComposite311 (monomialCoefficientUniversalWholeIdeal300 R m n)
    (actualAffineRelativePolynomialChartMap309 R f m)
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m)
      ((actualAffineRelativeHomEquiv311 R f m n) g))
    (fixedBaseTestAmbientMap305 R m n g.val g.property)
    (actualAffineRelativeUniversalAmbient_comp311 R f m n g)

/-- Actual presentation reflects whole points, including all nilpotents. -/
lemma actualAffineRelativePointOnPolynomialChart_injective311 :
    Function.Injective (actualAffineRelativePointOnPolynomialChart309 R f m n) := by
  intro P Q he
  apply Subtype.ext
  exact nativeIdealComapIso_injective300 (actualAffineRelativePolynomialAmbientIso309 R f m)
    P.val Q.val (congrArg Subtype.val he)

end PfaffianDescent
end
