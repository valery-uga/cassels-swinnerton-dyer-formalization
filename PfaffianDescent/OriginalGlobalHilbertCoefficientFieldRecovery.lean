import PfaffianDescent.OriginalGlobalHilbertPhysicalChartRecovery
import PfaffianDescent.OriginalNormalizedPolynomialChosenChartAmbientDictionary
import PfaffianDescent.OriginalNormalizedPolynomialChosenChartInverseRecovery
import PfaffianDescent.OriginalCoefficientProjectiveFamily317

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Ordinary cancellation in the explicit category of types, before the
actual relative Hilbert functor and its dependent object are substituted. -/
private theorem originalCoefficientTypeIso_cancel001
    {A B : Type u} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom (C := Type u) e.hom_inv_id x

/-- Entire chart push/comap, cut before the original coefficient rings and
chosen representer aliases are substituted. The exact separated proof is
an explicit ordinary argument to both actual push operations. -/
private theorem originalCoefficientChosenPush_comap001
    {X B Y W : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (n : ℕ)
    (hSep : IsSeparated F) (T : Over B)
    (Qchosen : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n)
    (Q : Y.IdealSheafData) (e : Y ≅ pullback T.hom (U.ι ≫ F))
    (f : W ≅ pullback T.hom F) (a : Y ⟶ W)
    (hDiagram : e.hom ≫ relativeClosedAmbientTestMap313 U.ι F T = a ≫ f.hom)
    (hTransport : Qchosen.val = Q.comap e.inv)
    [IsClosedImmersion (Q.subschemeι ≫ a)] :
    (@relativeOpenFiniteFlatPointPush315 X B U F n hSep T Qchosen).val.comap f.hom =
      Q.map a := by
  let Qpush := @relativeOpenFiniteFlatPointPush315 X B U F n hSep T Qchosen
  have hPush : Qpush.val = Qchosen.val.map (relativeClosedAmbientTestMap313 U.ι F T) :=
    @relativeOpenFiniteFlatPointPush_wholeIdeal315 X B U F n hSep T Qchosen
  have hPushTransport : Qpush.val =
      (Q.comap e.inv).map (relativeClosedAmbientTestMap313 U.ι F T) :=
    hPush.trans (congrArg (fun I => I.map (relativeClosedAmbientTestMap313 U.ι F T)) hTransport)
  exact (congrArg (fun I => I.comap f.hom) hPushTransport).trans
    (originalPhysicalChartIdealPush_comapAmbientIso001 e f a
      (relativeClosedAmbientTestMap313 U.ι F T) hDiagram Q)

private theorem originalCoefficientChosenChart_baseSeparated001
    {R : Type u} [CommRing R] (r : MvPolynomial (Fin 4) R)
    {d : ℕ} (hr : r.IsHomogeneous d) : IsSeparated (hypersurfaceToBase r hr) :=
  originalNormalizedWholeOpen_separated317 r hr
attribute [local instance] originalCoefficientChosenChart_baseSeparated001

/-- Chosen-chart inversion and the actual ambient Cartesian square recover
EXACTLY the physical original coefficient family after pushing its whole
ideal into the original projective hypersurface. No family equality or
original-P fibre identity is assumed. -/
theorem originalCoefficientChosenChart_physicalWholeIdeal001
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
    (j : Fin 4) (B : Type u) [CommRing B] [Algebra R B]
    (n : ℕ) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] B) :
    (relativeOpenChartClassifiedAmbientPoint001 (hypersurfaceToBase r hr)
      (Proj.basicOpen (grading (equationIdeal r hr))
        (originalNormalizedCoordinateChartIndex001 r hr j).val) n
      (originalPositiveHomogeneousChartIndexRepresentingObject001 (equationIdeal r hr) n hn
        (originalNormalizedCoordinateChartIndex001 r hr j))
      (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal r hr) n hn
        (originalNormalizedCoordinateChartIndex001 r hr j)) (originalNormalizedAffineTest317 R B)
      (originalCoefficientTestClassifyingMap317 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i k ≫
          (originalNormalizedPolynomialChosenChartOverIso001 r hr j n hn).hom)).val.comap
      (originalNormalizedPolynomialPhysicalProjectiveAmbientIso001 r hr B).hom =
        (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val := by
  let T := originalNormalizedAffineTest317 R B
  let Q := originalCoefficientTestPhysicalFamily317 R n r hr j hn i k
  let c := originalCoefficientTestClassifyingMap317 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i k
  let theta := polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) hn
  let E := originalNormalizedAffineTestPointEquiv317 R r hr j B n
  let V := Proj.basicOpen (grading (equationIdeal r hr))
    (originalNormalizedCoordinateChartIndex001 r hr j).val
  let F := hypersurfaceToBase r hr
  have hSep : IsSeparated F := originalNormalizedWholeOpen_separated317 r hr
  let e := originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 r hr j B
  let f := originalNormalizedPolynomialPhysicalProjectiveAmbientIso001 r hr B
  let a := originalNormalizedHypersurfaceChartEmbedding312 (r.map (algebraMap R B))
    (hr.map (algebraMap R B)) j
  let a' := relativeClosedAmbientTestMap313 V.ι F T
  let psi := originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal r hr) n hn
    (originalNormalizedCoordinateChartIndex001 r hr j)
  let Qchosen := psi.inv.app (.op T)
    (c ≫ (originalNormalizedPolynomialChosenChartOverIso001 r hr j n hn).hom)
  have hClassifies : theta.hom.app (.op T) (E Q) = c :=
    originalNormalizedAffinePointOfClassifier_classifies317 R r hr j B n hn c
  have hCancel : theta.inv.app (.op T) (theta.hom.app (.op T) (E Q)) = E Q :=
    originalCoefficientTypeIso_cancel001 (theta.app (.op T)) (E Q)
  have hPolyInv : theta.inv.app (.op T) c = E Q :=
    (congrArg (fun x => theta.inv.app (.op T) x) hClassifies.symm).trans hCancel
  have hInverse := originalNormalizedPolynomialChosenChart_inverseClassifier001 r hr j n hn T c
  have hTransport : Qchosen.val = Q.val.comap e.inv := by
    exact (congrArg Subtype.val hInverse).trans
      ((congrArg (fun x =>
        ((originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 r hr j n).hom.app (.op T) x).val)
        hPolyInv).trans
          (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_wholeIdeal001 r hr j B n Q))
  letI : IsClosedImmersion (Q.val.subschemeι ≫ a) :=
    originalNormalizedAffinePointToProjective_isClosed317 (r.map (algebraMap R B))
      (hr.map (algebraMap R B)) j n Q
  have hFinal := originalCoefficientChosenPush_comap001 F V n hSep T Qchosen Q.val e f a
    (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toProjective001 r hr j B) hTransport
  exact hFinal.trans
    (originalCoefficientTestProjectiveFamily_wholeIdeal317 R n r hr j hn i k).symm


end PfaffianDescent
end
