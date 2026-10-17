import PfaffianDescent.MonomialAllTestPolynomialLocusCriterion312
import PfaffianDescent.NativeWholeIdealContainment312
import Mathlib.RingTheory.Ideal.Span

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u v
set_option autoImplicit false

/-- Pullback of entire ideal-sheaf data preserves the actual supremum of equations. -/
private theorem finiteEquationWholeIdeal_comap_iSup001
    {X Y : Scheme.{u}} {ι : Type v} (J : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (⨆ i, J i).comap f = ⨆ i, (J i).comap f :=
  (Scheme.IdealSheafData.map_gc f).l_iSup

/-- Actual affine quotient kernels preserve the supremum of ORIGINAL ring ideals.
The top comparison uses the genuine Gamma-Spec ring isomorphism. -/
private theorem finiteEquationAffineQuotientKernel_iSup001
    {C : Type u} [CommRing C] {ι : Type v} (J : ι → Ideal C) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⨆ i, J i)))).ker =
      ⨆ i, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J i)))).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply,
    nativeSpecMap_kernel_top306, Ideal.mk_ker]
  let e := (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv
  exact e.idealComapOrderIso.map_iSup J

/-- A finite system of ORIGINAL polynomial equations gives its entire quotient
kernel as the actual sum of the principal equation kernels, including nilpotents. -/
private theorem finiteEquationOriginalQuotientKernel_span001
    {C : Type u} [CommRing C] {r : ℕ} (q : Fin r → C) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range q))))).ker =
      ⨆ i, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span ({q i} : Set C))))).ker := by
  rw [Ideal.span_range_eq_iSup]
  exact finiteEquationAffineQuotientKernel_iSup001 (fun i => Ideal.span ({q i} : Set C))

variable (R : Type u) [CommRing R] (m n r : ℕ) (q : Fin r → MvPolynomial (Fin m) R)

/-- Literal finite-equation quotient embedding with the ORIGINAL coefficient ring. -/
def finiteEquationOriginalPolynomialEmbedding001 :
    Spec (.of (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q))) ⟶
      Spec (.of (MvPolynomial (Fin m) R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range q))))

/-- Closedness of the original whole quotient embedding is derived from surjectivity. -/
theorem finiteEquationOriginalPolynomialEmbedding_isClosedImmersion001 :
    IsClosedImmersion (finiteEquationOriginalPolynomialEmbedding001 R m r q) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The original quotient preserves the literal ORIGINAL R structure map. -/
theorem finiteEquationOriginalPolynomialEmbedding_toBase001 :
    finiteEquationOriginalPolynomialEmbedding001 R m r q ≫ nativePolynomialProjection300 R m =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range q)))) := by
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range q)))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin m) R))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The finite-equation coefficient locus ideal on the SAME already constructed H.
Each summand is the existing genuine polynomial containment ideal. -/
def finiteEquationHilbertCoefficientIdeal001 :
    (monomialCoefficientGluedScheme300 R m n).IdealSheafData :=
  ⨆ i : Fin r, monomialPolynomialContainmentIdeal310 R m n (q i)

/-- The actual entire defining ideal inside the ORIGINAL relative test ambient. -/
def finiteEquationRelativeOriginalPolynomialIdeal001 (T : Over (Spec (.of R))) :
    (pullback T.hom (nativePolynomialProjection300 R m)).IdealSheafData :=
  (finiteEquationOriginalPolynomialEmbedding001 R m r q).ker.comap
    (pullback.snd T.hom (nativePolynomialProjection300 R m))

/-- Whole defining ideal equals the sum of the existing original polynomial
ideals on EVERY test scheme, before any coefficient model is substituted. -/
theorem finiteEquationRelativeOriginalPolynomialIdeal_iSup001
    (T : Over (Spec (.of R))) :
    finiteEquationRelativeOriginalPolynomialIdeal001 R m r q T =
      ⨆ i : Fin r, monomialRelativePolynomialHypersurfaceIdeal312 R m n (q i) T := by
  change (finiteEquationOriginalPolynomialEmbedding001 R m r q).ker.comap _ = _
  rw [show (finiteEquationOriginalPolynomialEmbedding001 R m r q).ker =
      ⨆ i : Fin r, (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({q i} : Set (MvPolynomial (Fin m) R)))))).ker from
      finiteEquationOriginalQuotientKernel_span001 q,
    finiteEquationWholeIdeal_comap_iSup001]
  rfl

/-- Genuine ALL-test criterion for the finite-equation closed coefficient locus.
Neither whole containment nor coefficient containment is replaced by a support law. -/
theorem finiteEquationRelativeUniversalContainment_locusKernel_iff001
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    finiteEquationHilbertCoefficientIdeal001 R m n r q ≤ g.left.ker ↔
      finiteEquationRelativeOriginalPolynomialIdeal001 R m r q T ≤
        (monomialRelativeUniversalPullback309 R m n T g).val := by
  change (⨆ i : Fin r, monomialPolynomialContainmentIdeal310 R m n (q i)) ≤ g.left.ker ↔ _
  rw [finiteEquationRelativeOriginalPolynomialIdeal_iSup001 R m n r q T]
  constructor
  · intro h
    apply iSup_le
    intro i
    exact (monomialRelativeUniversalContainment_locusKernel_iff312 R m n (q i) T g).mp
      ((le_iSup (fun j : Fin r => monomialPolynomialContainmentIdeal310 R m n (q j)) i).trans h)
  · intro h
    apply iSup_le
    intro i
    exact (monomialRelativeUniversalContainment_locusKernel_iff312 R m n (q i) T g).mpr
      ((le_iSup (fun j : Fin r => monomialRelativePolynomialHypersurfaceIdeal312 R m n (q j) T) i).trans h)

/-- The classifier of an ACTUAL original finite-flat family factors through the
finite-equation locus; its condition is DERIVED from that family's whole ideal. -/
theorem finiteEquationOriginalContainedHilbertPoint_classifier_locusKernel001
    (T : Over (Spec (.of R))) (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n)
    (hq : finiteEquationRelativeOriginalPolynomialIdeal001 R m r q T ≤ P.val) :
    finiteEquationHilbertCoefficientIdeal001 R m n r q ≤
      (relativeNativeGlobalClassifyingMap311 R m n T hn P).left.ker := by
  apply (finiteEquationRelativeUniversalContainment_locusKernel_iff001 R m n r q T _).mpr
  exact hq.trans (congrArg Subtype.val
    (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P)).le

end PfaffianDescent
