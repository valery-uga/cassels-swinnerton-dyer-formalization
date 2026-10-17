import PfaffianDescent.MonomialRelativeContainmentCoefficientCriterion312
import PfaffianDescent.MonomialGlobalHypersurfaceFamily312
import PfaffianDescent.RelativeNativeHilbertRepresentability311
import PfaffianDescent.NativeCommonAffineChartCover306

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
private lemma nativeLocusPullbackBottomTransport312
    {C : Type*} [Category C] {P X Y Z : C}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : IsPullback a b f g) (e : g = g') : IsPullback a b f g' := e ▸ h

private lemma nativeLocusWholeComapComposite312 {X Y Z : Scheme.{u}}
    (I : Z.IdealSheafData) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : (I.comap b).comap a = I.comap c :=
  (I.comap_comp a b).symm.trans (congrArg I.comap h)

private lemma nativeLocusGroundProjectionComposite312
    {C : Type*} [Category C] {X Y Z W : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : X ⟶ Z)
    (h : a ≫ b = d) : a ≫ (b ≫ c) = d ≫ c :=
  (Category.assoc a b c).symm.trans (congrArg (fun z => z ≫ c) h)

private lemma nativeCoefficientChartBaseTransport312
    {C : Type*} [Category C] {X U H B : C}
    (g : X ⟶ H) (a : X ⟶ U) (i : U ⟶ H) (b : H ⟶ B)
    (c : U ⟶ B) (v : X ⟶ B)
    (hg : g ≫ b = v) (hi : i ≫ b = c) (ha : g = a ≫ i) : a ≫ c = v :=
  (congrArg (fun z => a ≫ z) hi.symm).trans
    ((Category.assoc a i b).symm.trans
      ((congrArg (fun z => z ≫ b) ha.symm).trans hg))

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Entire literal original-p=0 ideal on the ambient of ANY original-base test. -/
def monomialRelativePolynomialHypersurfaceIdeal312
    (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (T : Over (Spec (.of R))) :
    (pullback T.hom (nativePolynomialProjection300 R m)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap
    (pullback.snd T.hom (nativePolynomialProjection300 R m))

private lemma monomialRelativeLocusFactor_outerIsPullback312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) :
    IsPullback (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T)
      (monomialCoefficientAmbientToH300 R m n)
      (d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p) := by
  exact nativeLocusPullbackBottomTransport312
    (relativeHilbertAmbientMap_isPullback197 (nativePolynomialProjection300 R m) g) hd.symm

/-- Canonical ambient lift induced by an actual locus factor, for arbitrary tests. -/
def monomialRelativeLocusFactorAmbientMap312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) :
    pullback T.hom (nativePolynomialProjection300 R m) ⟶
      monomialPolynomialContainmentAmbient310 R m n p :=
  nativeCartesianBaseChangeChartMap312
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
    (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) d
    (monomialCoefficientAmbientToH300 R m n)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)
    (monomialRelativeLocusFactor_outerIsPullback312 R m n p T g d hd)

lemma monomialRelativeLocusFactorAmbientMap_fst312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) :
    monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd ≫
        pullback.fst (monomialCoefficientAmbientToH300 R m n)
          (monomialPolynomialContainmentLocusInclusion310 R m n p) =
      relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g :=
  nativeCartesianBaseChangeChartMap_fst312 _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma monomialRelativeLocusFactorAmbientMap_ground312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) :
    monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd ≫
        monomialPolynomialContainmentAmbientToGround312 R m n p =
      pullback.snd T.hom (nativePolynomialProjection300 R m) := by
  exact (nativeLocusGroundProjectionComposite312
    (monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd)
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (monomialCoefficientAmbientToGroundAffine300 R m n)
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
    (monomialRelativeLocusFactorAmbientMap_fst312 R m n p T g d hd)).trans
      (relativeHilbertAmbientMap_snd197 (nativePolynomialProjection300 R m) g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual factoring through the constructed locus implies genuine entire
polynomial containment of the universal pullback on ANY original test. -/
lemma monomialRelativeUniversalContainment_of_locusFactor312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) :
    monomialRelativePolynomialHypersurfaceIdeal312 R m n p T ≤
      (monomialRelativeUniversalPullback309 R m n T g).val := by
  have h := Scheme.IdealSheafData.comap_mono
    (monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd)
    (monomialRestrictedUniversalFamily_hypersurfaceContainment312 R m n p)
  have hleft := nativeLocusWholeComapComposite312
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker
    (monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd)
    (monomialPolynomialContainmentAmbientToGround312 R m n p)
    (pullback.snd T.hom (nativePolynomialProjection300 R m))
    (monomialRelativeLocusFactorAmbientMap_ground312 R m n p T g d hd)
  have hr := congrArg
    (fun I : (monomialPolynomialContainmentAmbient310 R m n p).IdealSheafData =>
      I.comap (monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd))
    (monomialPolynomialContainmentRestrictedUniversalFamily_wholeIdeal310 R m n p)
  have hright := hr.trans (nativeLocusWholeComapComposite312
    (monomialCoefficientUniversalWholeIdeal300 R m n)
    (monomialRelativeLocusFactorAmbientMap312 R m n p T g d hd)
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)
    (monomialRelativeLocusFactorAmbientMap_fst312 R m n p T g d hd))
  exact hleft.symm.le.trans (h.trans hright.le)

set_option backward.isDefEq.respectTransparency.types false in
/-- Converse on arbitrary tests: finite equations are forced locally by
whole polynomial containment; native cover uniqueness gives global factoring.
The common affine H-chart cover and coefficient points are constructed internally. -/
lemma monomialRelativeUniversalContainment_locusKernel312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (h : monomialRelativePolynomialHypersurfaceIdeal312 R m n p T ≤
      (monomialRelativeUniversalPullback309 R m n T g).val) :
    monomialPolynomialContainmentIdeal310 R m n p ≤ g.left.ker := by
  apply (nativeWholeIdeal_le_ker_iff_comap_eq_bot312 _ _).mpr
  obtain ⟨V, hV⟩ := nativeCommonAffineChartCover_exists306
    (monomialCoefficientGluedOpenCover300 R m n) g.left g.left
  apply wholeIdeal_eq_of_openCover_comaps V.openCover
  intro z
  obtain ⟨i, j, a, b, ha, hb⟩ := hV z
  obtain ⟨f, hf⟩ := Spec.map_surjective (V.f z ≫ T.hom)
  let A : Type u := V.X z
  letI : Algebra R A := f.hom.toAlgebra
  have hs : V.f z ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)) := hf.symm
  have haBase : a ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex))) =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    have hg : (V.f z ≫ g.left) ≫ monomialCoefficientGluedToBase300 R m n =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
      (Category.assoc (V.f z) g.left (monomialCoefficientGluedToBase300 R m n)).trans
        ((congrArg (fun k : T.left ⟶ Spec (.of R) => V.f z ≫ k) (Over.w g)).trans hs)
    exact nativeCoefficientChartBaseTransport312 (V.f z ≫ g.left) a
      (monomialCoefficientGluedChartMap300 R m n i.down)
      (monomialCoefficientGluedToBase300 R m n) _ _ hg
      (monomialCoefficientGluedChartMap_toBase300 R m n i.down) ha
  obtain ⟨q, hq⟩ := nativeAffineMapOverBase_algHom_exists306 R
    (C := UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex)
    (T := A) a haBase
  have hchart : V.f z ≫ g.left = Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      monomialCoefficientGluedChartMap300 R m n i.down := by
    exact ha.trans (congrArg
      (fun k : Spec (.of A) ⟶ Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n
          i.down.monomials i.down.zeroIndex)) => k ≫ monomialCoefficientGluedChartMap300 R m n i.down)
      hq.symm)
  have hqContains := monomialRelativeUniversalContainment_coefficientPoint312
    R m n p T g (V.f z) hs i.down q hchart h
  obtain ⟨d, hd⟩ := monomialCoefficientPoint_exists_locusFactor312 R m n p i.down q hqContains
  have hK : monomialPolynomialContainmentIdeal310 R m n p ≤ (V.f z ≫ g.left).ker :=
    (nativeClosedSubschemeFactor_iff312 _ _).mp ⟨d, hd.trans hchart.symm⟩
  have hz := (nativeWholeIdeal_le_ker_iff_comap_eq_bot312 _ _).mp hK
  exact (Scheme.IdealSheafData.comap_comp _ (V.f z) g.left).symm.trans
    (hz.trans (Scheme.IdealSheafData.comap_bot (V.f z)).symm)

/-- Whole polynomial containment is exactly the native global coefficient-locus
kernel condition on ALL original-base test schemes. -/
theorem monomialRelativeUniversalContainment_locusKernel_iff312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    monomialPolynomialContainmentIdeal310 R m n p ≤ g.left.ker ↔
      monomialRelativePolynomialHypersurfaceIdeal312 R m n p T ≤
        (monomialRelativeUniversalPullback309 R m n T g).val := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (nativeClosedSubschemeFactor_iff312 _ _).mpr h
    exact monomialRelativeUniversalContainment_of_locusFactor312 R m n p T g d hd
  · exact monomialRelativeUniversalContainment_locusKernel312 R m n p T g

/-- ALL-test factorization criterion uses literal original-p containment;
no desired coefficient containment or factorization outcome is a premise. -/
theorem monomialRelativeUniversalPullback_locusFactor_iff312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    (∃ d : T.left ⟶ monomialPolynomialContainmentLocus310 R m n p,
      d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p = g.left) ↔
      monomialRelativePolynomialHypersurfaceIdeal312 R m n p T ≤
        (monomialRelativeUniversalPullback309 R m n T g).val :=
  (nativeClosedSubschemeFactor_iff312 _ _).trans
    (monomialRelativeUniversalContainment_locusKernel_iff312 R m n p T g)

/-- The classifier of a contained original197 point factors through the locus,
with the actual coefficient condition DERIVED from its original whole ideal. -/
theorem originalRelativeContainedHilbertPoint_classifier_locusKernel312
    (T : Over (Spec (.of R))) (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n)
    (hp : monomialRelativePolynomialHypersurfaceIdeal312 R m n p T ≤ P.val) :
    monomialPolynomialContainmentIdeal310 R m n p ≤
      (relativeNativeGlobalClassifyingMap311 R m n T hn P).left.ker := by
  apply (monomialRelativeUniversalContainment_locusKernel_iff312 R m n p T _).mpr
  exact hp.trans (congrArg Subtype.val
    (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P)).le

end PfaffianDescent
end
