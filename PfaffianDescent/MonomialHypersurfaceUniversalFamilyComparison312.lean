import PfaffianDescent.MonomialHypersurfaceRelativeAmbientIso312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeHypersurfaceFamilyMapThree312 {X Y Z W : Scheme.{u}}
    (J : X.IdealSheafData) (e : X ⟶ Y) (q : Y ⟶ Z) (a : Z ⟶ W) :
    ((J.map e).map q).map a = J.map (e ≫ (q ≫ a)) :=
  (congrArg (fun I : Z.IdealSheafData => I.map a) (J.map_comp e q).symm).trans
    ((J.map_comp (e ≫ q) a).symm.trans (congrArg J.map (Category.assoc e q a)))

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Transport of the constructed GLOBAL native hypersurface family to the
LITERAL original relative197 hypersurface ambient, with exact base law. -/
def monomialPolynomialHypersurfaceRelativeUniversalFamily312 :
    FiniteFlatHilbertPoint195
      (relativeHilbertFamily197
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m)
        (monomialPolynomialContainmentRepresentingObject312 R m n p)) n :=
  nativeClosedFiniteFlatPointPush313
    ((monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
      monomialPolynomialContainmentAmbientToLocus310 R m n p)
    (relativeHilbertFamily197
      (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m)
      (monomialPolynomialContainmentRepresentingObject312 R m n p))
    (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom
    (monomialGlobalHypersurfaceRelativeAmbientIso_hom_toLocus312 R m n p) n
    (monomialPolynomialHypersurfaceGlobalFamily312 R m n p)

lemma monomialPolynomialHypersurfaceRelativeUniversalFamily_wholeIdeal312 :
    (monomialPolynomialHypersurfaceRelativeUniversalFamily312 R m n p).val =
      (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val.map
        (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom := rfl

/-- The actual global native family, transported through the DERIVED ambient Iso,
is the genuine representing inverse on the identity coefficient-locus test.
Equality retains the ORIGINAL entire closed hypersurface ideal; no family comparison premise. -/
theorem monomialPolynomialHypersurfaceRelativeUniversalFamily_eqRepresentingInverse312
    (hn : 0 < n) :
    monomialPolynomialHypersurfaceRelativeUniversalFamily312 R m n p =
      (polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn
        (monomialPolynomialContainmentRepresentingObject312 R m n p)).symm
          (𝟙 (monomialPolynomialContainmentRepresentingObject312 R m n p)) := by
  let T := monomialPolynomialContainmentRepresentingObject312 R m n p
  let e := monomialRelativeLocusPolynomialAmbientIso312 R m n p
  let q := relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m) T
  letI : IsClosedImmersion q := relativeClosedAmbientTestMap_isClosedImmersion313
    (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p) (nativePolynomialProjection300 R m) T
  apply Subtype.ext
  apply nativeWholeIdeal_map_closed_injective313 q
  apply nativeWholeIdeal_map_closed_injective313 e.hom
  have hw := congrArg
    (fun J : (pullback T.hom
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m)).IdealSheafData =>
      (J.map q).map e.hom)
    (monomialPolynomialHypersurfaceRelativeUniversalFamily_wholeIdeal312 R m n p)
  have hnativ := hw.trans
    ((nativeHypersurfaceFamilyMapThree312
      (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val
      (monomialGlobalHypersurfaceRelativeAmbientIso312 R m n p).hom q e.hom).trans
        ((congrArg (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val.map
          (monomialGlobalHypersurfaceRelativeAmbientIso_hom_embedding312 R m n p)).trans
            (monomialPolynomialHypersurfaceGlobalFamily_ambientIdeal312 R m n p)))
  have hi := polynomialHypersurfaceHilbertClassificationEquiv_inv_ambientIdeal312
    R m n p hn T (𝟙 T)
  have hid := congrArg Subtype.val
    (congrArg (monomialRelativeUniversalPullback309 R m n T)
      (Category.id_comp (monomialPolynomialContainmentRepresentingInclusion312 R m n p)))
  have hinv := (congrArg (fun J : (pullback T.hom (nativePolynomialProjection300 R m)).IdealSheafData =>
      J.map e.hom) (hi.trans hid)).trans
    ((congrArg (fun J : (pullback T.hom (nativePolynomialProjection300 R m)).IdealSheafData => J.map e.hom)
      (monomialRelativeLocusPolynomialAmbientIso_universalWholeIdeal312 R m n p)).trans
        (nativeWholeIdeal_map_comap_iso313 e
          (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val))
  exact hnativ.trans hinv.symm

end PfaffianDescent
end
