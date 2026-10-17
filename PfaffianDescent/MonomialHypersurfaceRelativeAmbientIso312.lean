import PfaffianDescent.NativeClosedKernelPresentationIso312
import PfaffianDescent.PolynomialHypersurfaceHilbertRepresentability312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeLocusIsoPullbackBottomTransport312
    {C : Type*} [Category C] {P X Y Z : C}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : IsPullback a b f g) (e : g = g') : IsPullback a b f g' := e ▸ h

private lemma nativeLocusIsoWholeComposite312 {X Y Z : Scheme.{u}}
    (I : Z.IdealSheafData) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : (I.comap b).comap a = I.comap c :=
  (I.comap_comp a b).symm.trans (congrArg I.comap h)

private lemma nativeLocusIsoProjectionComposite312
    {C : Type*} [Category C] {P Q X L : C}
    (e : P ⟶ Q) (q : Q ⟶ X) (c : X ⟶ L) (b : Q ⟶ L) (i : P ⟶ X)
    (he : e ≫ q = i) (hb : q ≫ c = b) : e ≫ b = i ≫ c :=
  (congrArg (fun z => e ≫ z) hb.symm).trans
    ((Category.assoc e q c).symm.trans (congrArg (fun z => z ≫ c) he))

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Canonical relative polynomial ambient of the locus maps to SAME native restricted ambient. -/
def monomialRelativeLocusPolynomialAmbientMap312 :
    pullback (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
        (nativePolynomialProjection300 R m) ⟶
      monomialPolynomialContainmentAmbient310 R m n p :=
  monomialRelativeLocusFactorAmbientMap312 R m n p
    (monomialPolynomialContainmentRepresentingObject312 R m n p)
    (monomialPolynomialContainmentRepresentingInclusion312 R m n p)
    (𝟙 (monomialPolynomialContainmentLocus310 R m n p))
    (Category.id_comp (monomialPolynomialContainmentLocusInclusion310 R m n p))

lemma monomialRelativeLocusPolynomialAmbientMap_isPullback312 :
    IsPullback (monomialRelativeLocusPolynomialAmbientMap312 R m n p)
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m)
        (monomialPolynomialContainmentRepresentingObject312 R m n p))
      (monomialPolynomialContainmentAmbientToLocus310 R m n p)
      (𝟙 (monomialPolynomialContainmentLocus310 R m n p)) :=
  nativeCartesianBaseChangeChartMap_isPullback312 _ _ _ _ _
    (nativeLocusIsoPullbackBottomTransport312
      (relativeHilbertAmbientMap_isPullback197 (nativePolynomialProjection300 R m)
        (monomialPolynomialContainmentRepresentingInclusion312 R m n p))
      (Category.id_comp (monomialPolynomialContainmentLocusInclusion310 R m n p)).symm)

/-- Actual relative polynomial ambient comparison is an Iso by identity base change. -/
def monomialRelativeLocusPolynomialAmbientIso312 :
    pullback (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
        (nativePolynomialProjection300 R m) ≅
      monomialPolynomialContainmentAmbient310 R m n p := by
  letI : IsIso (monomialRelativeLocusPolynomialAmbientMap312 R m n p) :=
    (monomialRelativeLocusPolynomialAmbientMap_isPullback312 R m n p).isIso_fst_of_isIso
      (CategoryTheory.IsIso.id _)
  exact asIso (monomialRelativeLocusPolynomialAmbientMap312 R m n p)

lemma monomialRelativeLocusPolynomialAmbientIso_hom_toLocus312 :
    (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom ≫
        monomialPolynomialContainmentAmbientToLocus310 R m n p =
      relativeHilbertFamily197 (nativePolynomialProjection300 R m)
        (monomialPolynomialContainmentRepresentingObject312 R m n p) :=
  (monomialRelativeLocusPolynomialAmbientMap_isPullback312 R m n p).w.trans (Category.comp_id _)

lemma monomialRelativeLocusPolynomialAmbientIso_hom_toGround312 :
    (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom ≫
        monomialPolynomialContainmentAmbientToGround312 R m n p =
      pullback.snd (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
        (nativePolynomialProjection300 R m) :=
  monomialRelativeLocusFactorAmbientMap_ground312 R m n p
    (monomialPolynomialContainmentRepresentingObject312 R m n p)
    (monomialPolynomialContainmentRepresentingInclusion312 R m n p)
    (𝟙 (monomialPolynomialContainmentLocus310 R m n p))
    (Category.id_comp (monomialPolynomialContainmentLocusInclusion310 R m n p))

/-- Entire ambient universal ideals agree under the ACTUAL derived polynomial Iso. -/
lemma monomialRelativeLocusPolynomialAmbientIso_universalWholeIdeal312 :
    (monomialRelativeUniversalPullback309 R m n
      (monomialPolynomialContainmentRepresentingObject312 R m n p)
      (monomialPolynomialContainmentRepresentingInclusion312 R m n p)).val =
    (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val.comap
      (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom :=
  (nativeLocusIsoWholeComposite312 (monomialCoefficientUniversalWholeIdeal300 R m n)
    (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m)
      (monomialPolynomialContainmentRepresentingInclusion312 R m n p))
    (monomialRelativeLocusFactorAmbientMap_fst312 R m n p
    (monomialPolynomialContainmentRepresentingObject312 R m n p)
    (monomialPolynomialContainmentRepresentingInclusion312 R m n p)
    (𝟙 (monomialPolynomialContainmentLocus310 R m n p))
    (Category.id_comp (monomialPolynomialContainmentLocusInclusion310 R m n p)))).symm

/-- The original relative hypersurface test embedding, after the actual ambient
comparison, has exactly the constructed global native hypersurface whole kernel. -/
lemma monomialRelativeHypersurfaceTestEmbedding_compositeKernel312 :
    (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
        (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p) ≫
      (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom).ker =
        monomialPolynomialHypersurfaceIdeal312 R m n p := by
  have hg := nativeLocusIsoWholeComposite312
    (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p).ker
    (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom
    (monomialPolynomialContainmentAmbientToGround312 R m n p)
    (pullback.snd (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
      (nativePolynomialProjection300 R m))
    (monomialRelativeLocusPolynomialAmbientIso_hom_toGround312 R m n p)
  have hk := (relativeClosedAmbientTestMap_kernel313
    (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m)
    (monomialPolynomialContainmentRepresentingObject312 R m n p)).trans hg.symm
  exact (Scheme.Hom.ker_comp _ _).trans
    ((congrArg
      (fun J : (pullback (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
          (nativePolynomialProjection300 R m)).IdealSheafData =>
        J.map (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom) hk).trans
      (nativeWholeIdeal_map_comap_iso313 (monomialRelativeLocusPolynomialAmbientIso312 R m n p)
        (monomialPolynomialHypersurfaceIdeal312 R m n p)))

private instance monomialRelativeHypersurfaceTestEmbedding_compositeClosed312 :
    IsClosedImmersion
      (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
          (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p) ≫
        (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom) := by
  letI := relativeClosedAmbientTestMap_isClosedImmersion313
    (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p)
  infer_instance

/-- The global native original-p=0 ambient is genuinely the LITERAL original
relative197 hypersurface ambient over the actual constructed coefficient locus. -/
def monomialGlobalHypersurfaceRelativeAmbientIso312 :
    (monomialPolynomialHypersurfaceIdeal312 R m n p).subscheme ≅
      pullback (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) :=
  nativeClosedKernelPresentationIso312
    (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
        (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p) ≫
      (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom)
    (monomialPolynomialHypersurfaceIdeal312 R m n p)
    (monomialRelativeHypersurfaceTestEmbedding_compositeKernel312 R m n p).symm

lemma monomialGlobalHypersurfaceRelativeAmbientIso_hom_embedding312 :
    (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom ≫
        (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
            (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p) ≫
          (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom) =
      (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι :=
  nativeClosedKernelPresentationIso_hom_comp312 _ _ _

/-- The derived hypersurface Iso respects the ORIGINAL coefficient-locus base map. -/
lemma monomialGlobalHypersurfaceRelativeAmbientIso_hom_toLocus312 :
    (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom ≫
        relativeHilbertFamily197
          (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m)
          (monomialPolynomialContainmentRepresentingObject312 R m n p) =
      (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
        monomialPolynomialContainmentAmbientToLocus310 R m n p := by
  have hb := (Category.assoc
    (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p))
    (monomialRelativeLocusPolynomialAmbientIso312 R m n p).hom
    (monomialPolynomialContainmentAmbientToLocus310 R m n p)).trans
      ((congrArg
        (fun z => relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
          (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p) ≫ z)
        (monomialRelativeLocusPolynomialAmbientIso_hom_toLocus312 R m n p)).trans
          (relativeClosedAmbientTestMap_toTest313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
            (nativePolynomialProjection300 R m) (monomialPolynomialContainmentRepresentingObject312 R m n p)))
  exact nativeLocusIsoProjectionComposite312
    (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom _ _ _ _
    (monomialGlobalHypersurfaceRelativeAmbientIso_hom_embedding312 R m n p) hb

end PfaffianDescent
end
