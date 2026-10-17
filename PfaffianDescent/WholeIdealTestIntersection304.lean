import PfaffianDescent.MonomialWholeIdealTestChartMap303
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

/-- Genuine composition of two coefficient localization actions, before original patch substitution. -/
def twoStageTestCoefficientAlgebra304
    (A S T : Type u) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] : Algebra A T :=
  ((algebraMap S T).comp (algebraMap A S)).toAlgebra

/-- The original fixed-R three-stage action factors through the canonical two-stage A action. -/
lemma twoStageTestCoefficient_scalarTower304
    (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra S T] :
    letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
    letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
    IsScalarTower R A T := by
  letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
  letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- Literal two-stage extension is the same entire ideal under the original composed coefficient map. -/
lemma wholeIdealImage_twoStage304
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] {m : ℕ} (I : Ideal (MvPolynomial (Fin m) A)) :
    letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
    (I.map (MvPolynomial.map (algebraMap A S))).map (MvPolynomial.map (algebraMap S T)) =
      I.map (MvPolynomial.map (algebraMap A T)) := by
  letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
  rw [Ideal.map_map]
  exact congrArg (fun f => I.map f) (RingHom.ext (MvPolynomial.map_map _ _))

/-- The actual two localization Spec maps are the native Spec map of that canonical composition. -/
lemma twoStageTestCoefficientSpecMap304
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] :
    letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
    Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A S)) =
      Spec.map (CommRingCat.ofHom (algebraMap A T)) := by
  letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Both ways of extending the ORIGINAL entire polynomial ideal to an actual tensor intersection agree. -/
lemma wholeIdealImages_tensorIntersection304
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A)) :
    (I.map (MvPolynomial.map (algebraMap A S))).map
        (MvPolynomial.map (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T))) =
      (I.map (MvPolynomial.map (algebraMap A T))).map
        (MvPolynomial.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := T)).toRingHom) := by
  have hl : (MvPolynomial.map (σ := Fin m)
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T))).comp
        (MvPolynomial.map (σ := Fin m) (algebraMap A S)) =
      MvPolynomial.map (σ := Fin m) ((Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T)).comp
        (algebraMap A S)) := RingHom.ext (MvPolynomial.map_map _ _)
  have hr : (MvPolynomial.map (σ := Fin m)
      (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := T)).toRingHom).comp
        (MvPolynomial.map (σ := Fin m) (algebraMap A T)) =
      MvPolynomial.map (σ := Fin m) ((Algebra.TensorProduct.includeRight (R := A) (A := S) (B := T)).toRingHom.comp
        (algebraMap A T)) := RingHom.ext (MvPolynomial.map_map _ _)
  rw [Ideal.map_map, Ideal.map_map, hl, hr,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]

/-- The common tensor-intersection coefficient action is the original fixed-R action through A. -/
lemma tensorTestIntersection_scalarTower304
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra A T] [Algebra R S] [Algebra R T]
    [IsScalarTower R A S] [IsScalarTower R A T] :
    IsScalarTower R A (S ⊗[A] T) := by
  apply IsScalarTower.of_algebraMap_eq'
  change (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T)).comp
      (algebraMap R S) =
    ((Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T)).comp
      (algebraMap A S)).comp (algebraMap R A)
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A S]

/-- Native test-chart maps agree on the actual affine tensor intersection, by whole ideal equality. -/
lemma wholeIdealTestChartMaps_tensorIntersection304
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra A T] [Algebra R S] [Algebra R T]
    [IsScalarTower R A S] [IsScalarTower R A T] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (i j : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := S) i.monomials)
    (y : MonomialWholeIdealChart287 (A := T) j.monomials)
    (hx : x.val = I.map (MvPolynomial.map (algebraMap A S)))
    (hy : y.val = I.map (MvPolynomial.map (algebraMap A T))) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := S) (B := T))) ≫
        monomialWholeIdealTestChartMap303 R i x =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := T)).toRingHom) ≫
        monomialWholeIdealTestChartMap303 R j y := by
  letI : IsScalarTower R A (S ⊗[A] T) := tensorTestIntersection_scalarTower304
  let l : S →ₐ[R] (S ⊗[A] T) :=
    Algebra.TensorProduct.includeLeft (R := A) (S := R) (A := S) (B := T)
  let r : T →ₐ[R] (S ⊗[A] T) :=
    (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := T)).restrictScalars R
  have hI :
      (monomialWholeIdealChartMap287 i.monomials i.zeroIndex i.zero_eq l.toRingHom x).val =
      (monomialWholeIdealChartMap287 j.monomials j.zeroIndex j.zero_eq r.toRingHom y).val := by
    change x.val.map (MvPolynomial.map l.toRingHom) = y.val.map (MvPolynomial.map r.toRingHom)
    rw [hx, hy]
    exact wholeIdealImages_tensorIntersection304 I
  exact (monomialWholeIdealTestChartMap_natural303 R i x l).trans
    ((monomialWholeIdealTestChartMap_sameIdeal303 R i j _ _ hI).trans
      (monomialWholeIdealTestChartMap_natural303 R j y r).symm)

/-- Exact pullback projections, rather than a supplied compatibility statement, give the same law. -/
lemma wholeIdealTestChartMaps_nativePullback304
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra A T] [Algebra R S] [Algebra R T]
    [IsScalarTower R A S] [IsScalarTower R A T] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (i j : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := S) i.monomials)
    (y : MonomialWholeIdealChart287 (A := T) j.monomials)
    (hx : x.val = I.map (MvPolynomial.map (algebraMap A S)))
    (hy : y.val = I.map (MvPolynomial.map (algebraMap A T))) :
    pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (Spec.map (CommRingCat.ofHom (algebraMap A T))) ≫ monomialWholeIdealTestChartMap303 R i x =
    pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (Spec.map (CommRingCat.ofHom (algebraMap A T))) ≫ monomialWholeIdealTestChartMap303 R j y := by
  apply (cancel_epi (pullbackSpecIso A S T).inv).mp
  simpa only [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc,
    AlgHom.toRingHom_eq_coe] using
    (wholeIdealTestChartMaps_tensorIntersection304 I i j x y hx hy)

end PfaffianDescent
