import PfaffianDescent.NativeRelativePolynomialContainmentChart312
import PfaffianDescent.MonomialRestrictedFamilyChartComparison312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private def nativeKilledIdealAlgHomLift312
    (R C A : Type u) [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (I : Ideal C) (q : C →ₐ[R] A)
    (h : I ≤ RingHom.ker q.toRingHom) : C ⧸ I →ₐ[R] A :=
  Ideal.Quotient.liftₐ I q (fun x hx => h hx)

private lemma nativeKilledIdealAlgHomLift_comp312
    (R C A : Type u) [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (I : Ideal C) (q : C →ₐ[R] A)
    (h : I ≤ RingHom.ker q.toRingHom) :
    (nativeKilledIdealAlgHomLift312 R C A I q h).comp (Ideal.Quotient.mkₐ R I) = q :=
  Ideal.Quotient.liftₐ_comp I q _

private lemma nativeCoefficientSpecComposite312
    {C D A : Type u} [CommRing C] [CommRing D] [CommRing A]
    (f : C →+* D) (g : D →+* A) (h : C →+* A) (hh : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hh]

private lemma nativeCoefficientClosedChartComposite312
    {C : Type*} [Category C] {X Y L H U : C}
    (a : X ⟶ Y) (d : Y ⟶ L) (i : L ⟶ H)
    (q : Y ⟶ U) (c : U ⟶ H) (f : X ⟶ U)
    (hd : d ≫ i = q ≫ c) (hq : a ≫ q = f) : (a ≫ d) ≫ i = f ≫ c :=
  (Category.assoc a d i).trans ((congrArg (fun z => a ≫ z) hd).trans
    ((Category.assoc a q c).symm.trans (congrArg (fun z => z ≫ c) hq)))

private lemma nativeCoefficientWholeComapComposite312 {X Y Z : Scheme.{u}}
    (I : Z.IdealSheafData) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : (I.comap b).comap a = I.comap c :=
  (I.comap_comp a b).symm.trans (congrArg I.comap h)

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

set_option backward.isDefEq.respectTransparency.types false in
/-- Original-p containment in an actual coefficient whole ideal produces
an actual map into the constructed closed locus, with the SAME H map. -/
lemma monomialCoefficientPoint_exists_locusFactor312
    {A : Type u} [CommRing A] [Algebra R A]
    (i : MonomialCoefficientChartIndex300 m n)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A)
    (h : MvPolynomial.map (algebraMap R A) p ∈
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq q).val) :
    ∃ d : Spec (.of A) ⟶ monomialPolynomialContainmentLocus310 R m n p,
      d ≫ monomialPolynomialContainmentLocusInclusion310 R m n p =
        Spec.map (CommRingCat.ofHom q.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n i := by
  have hK := (monomialPolynomialContainmentCoefficientIdeal_le_ker_iff310 R m n p i q).mpr h
  let qb := nativeKilledIdealAlgHomLift312 R
    (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) A
    (monomialPolynomialContainmentCoefficientIdeal310 R m n p i) q hK
  have hq : qb.toRingHom.comp (monomialClosedCoefficientQuotientMap312 R m n p i).toRingHom =
      q.toRingHom := congrArg AlgHom.toRingHom
        (nativeKilledIdealAlgHomLift_comp312 R _ A _ q hK)
  refine ⟨Spec.map (CommRingCat.ofHom
      (R := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) (S := A) qb.toRingHom) ≫
    monomialClosedCoefficientChartToLocus312 R m n p i, ?_⟩
  have hs := nativeCoefficientSpecComposite312
    (monomialClosedCoefficientQuotientMap312 R m n p i).toRingHom qb.toRingHom q.toRingHom hq
  exact nativeCoefficientClosedChartComposite312
    (Spec.map (CommRingCat.ofHom
      (R := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) (S := A) qb.toRingHom))
    (monomialClosedCoefficientChartToLocus312 R m n p i)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)
    (monomialClosedCoefficientQuotientSpec312 R m n p i)
    (monomialCoefficientGluedChartMap300 R m n i)
    (Spec.map (CommRingCat.ofHom q.toRingHom))
    (monomialClosedCoefficientChartToLocus_comp312 R m n p i) hs

set_option backward.isDefEq.respectTransparency.types false in
/-- A contained universal family on ANY original test forces the actual local
finite coefficient equations on every affine coefficient-chart factorization. -/
lemma monomialRelativeUniversalContainment_coefficientPoint312
    {A : Type u} [CommRing A] [Algebra R A]
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (a : Spec (.of A) ⟶ T.left)
    (ha : a ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (i : MonomialCoefficientChartIndex300 m n)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A)
    (hq : a ≫ g.left = Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      monomialCoefficientGluedChartMap300 R m n i)
    (h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker.comap
        (pullback.snd T.hom (nativePolynomialProjection300 R m)) ≤
      (monomialRelativeUniversalPullback309 R m n T g).val) :
    MvPolynomial.map (algebraMap R A) p ∈
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq q).val := by
  have hc := Scheme.IdealSheafData.comap_mono
    (nativeRelativePolynomialChartMap312 R m T a ha) h
  have hleft := (nativeCoefficientWholeComapComposite312
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {p})))).ker
    (nativeRelativePolynomialChartMap312 R m T a ha)
    (pullback.snd T.hom (nativePolynomialProjection300 R m))
    (nativePolynomialScalarMap300 R A m)
    (nativeRelativePolynomialChartMap_toGround312 R m T a ha)).trans
      (nativePolynomialHypersurfaceKernel_comap312 R A m p)
  have hf : Spec.map (CommRingCat.ofHom (AlgHom.id R A).toRingHom) ≫ (a ≫ g.left) =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n i :=
    (congrArg (fun z : Spec (.of A) ⟶ Spec (.of A) => z ≫ (a ≫ g.left))
      (nativeSpecRingId312 A)).trans ((Category.id_comp _).trans hq)
  have hl := fixedBaseUniversalFamilyPullback_chartIdeal305 R m n (a ≫ g.left)
    (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g) i (AlgHom.id R A) q hf
  have hid := congrArg
    (fixedBaseUniversalFamilyPullback305 R m n (a ≫ g.left)
      (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g)).val.comap
    (nativePolynomialSpecId312 R A m)
  have he := hid.trans
    (fixedBaseUniversalFamilyPullback305 R m n (a ≫ g.left)
      (nativeRelativePolynomialClassifier_overBase312 R m T a ha n g)).val.comap_id
  have hclass := congrArg Subtype.val
    (cyclicCoefficientUniversalFamily_classifies302 R (A := A)
      i.monomials i.zeroIndex i.zero_eq q)
  have hright := (nativeRelativePolynomialUniversalPullback_wholeIdeal312 R m T a ha n g).trans
    (he.symm.trans (hl.trans hclass))
  have hI : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.map (algebraMap R A) p})))).ker ≤
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq q).val))).ker :=
    hleft.symm.le.trans (hc.trans hright.le)
  exact (Ideal.span_singleton_le_iff_mem _).mp
    ((nativeAffineQuotientKernel_le_iff312 _ _).mp hI)

end PfaffianDescent
end
