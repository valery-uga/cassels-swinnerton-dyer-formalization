import PfaffianDescent.WholeIdealTestIntersection304
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativePullbackCompatibility_transport304
    {C : Type*} [Category C] [HasPullbacks C] {X Y Z H : C}
    (f f0 : X ⟶ Z) (g g0 : Y ⟶ Z) (hf : f = f0) (hg : g = g0)
    (a : X ⟶ H) (b : Y ⟶ H)
    (h : pullback.fst f0 g0 ≫ a = pullback.snd f0 g0 ≫ b) :
    pullback.fst f g ≫ a = pullback.snd f g ≫ b := by
  cases hf
  cases hg
  exact h

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A)) (U : (Spec (.of A)).AffineOpenCover)
variable [∀ i, Algebra A (U.X i)] [∀ i, Algebra R (U.X i)]
variable [∀ i, IsScalarTower R A (U.X i)]
variable (c : U.I₀ → MonomialCoefficientChartIndex300 m n)
variable (x : ∀ i, MonomialWholeIdealChart287 (A := U.X i) (c i).monomials)
variable (hx : ∀ i, (x i).val = I.map (MvPolynomial.map (algebraMap A (U.X i))))
variable (hf : ∀ i, U.f i = Spec.map (CommRingCat.ofHom (algebraMap A (U.X i))))

include hx hf in
/-- Compatibility is DERIVED on the actual intersections of the given affine test cover. -/
lemma nativeWholeIdealTestCover_compatible304 (i j : U.I₀) :
    pullback.fst (U.f i) (U.f j) ≫ monomialWholeIdealTestChartMap303 R (c i) (x i) =
      pullback.snd (U.f i) (U.f j) ≫ monomialWholeIdealTestChartMap303 R (c j) (x j) :=
  nativePullbackCompatibility_transport304 (U.f i) _ (U.f j) _ (hf i) (hf j) _ _
    (wholeIdealTestChartMaps_nativePullback304 (R := R) (A := A)
      (S := U.X i) (T := U.X j) I (c i) (c j) (x i) (x j) (hx i) (hx j))

/-- Native OpenCover.glueMorphisms consumes the internally derived whole-ideal compatibility. -/
def nativeWholeIdealTestCoverMap304 :
    Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n :=
  U.openCover.glueMorphisms (fun (i : U.I₀) => monomialWholeIdealTestChartMap303 R (c i) (x i))
    (nativeWholeIdealTestCover_compatible304 R I U c x hx hf)

/-- The global map restricts to the SAME original inverse-classifier/chart-inclusion maps. -/
lemma nativeWholeIdealTestCoverMap_chart304 (i : U.I₀) :
    U.f i ≫ nativeWholeIdealTestCoverMap304 R I U c x hx hf =
      monomialWholeIdealTestChartMap303 R (c i) (x i) :=
  U.openCover.ι_glueMorphisms (fun (i : U.I₀) => monomialWholeIdealTestChartMap303 R (c i) (x i))
    (nativeWholeIdealTestCover_compatible304 R I U c x hx hf) i

include hf in
private lemma nativeAffineTestCover_toBase304 (i : U.I₀) :
    U.f i ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (U.X i))) := by
  rw [hf i, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq R A (U.X i)]

/-- This actual global test-family map is over the ORIGINAL Spec R. -/
lemma nativeWholeIdealTestCoverMap_toBase304 :
    nativeWholeIdealTestCoverMap304 R I U c x hx hf ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply U.openCover.hom_ext
  intro i
  change U.I₀ at i
  calc
    _ = (U.f i ≫ nativeWholeIdealTestCoverMap304 R I U c x hx hf) ≫
        monomialCoefficientGluedToBase300 R m n := (Category.assoc _ _ _).symm
    _ = monomialWholeIdealTestChartMap303 R (c i) (x i) ≫
        monomialCoefficientGluedToBase300 R m n := congrArg
      (fun f => f ≫ monomialCoefficientGluedToBase300 R m n)
      (nativeWholeIdealTestCoverMap_chart304 R I U c x hx hf i)
    _ = Spec.map (CommRingCat.ofHom (algebraMap R (U.X i))) :=
      monomialWholeIdealTestChartMap_toBase303 R (c i) (x i)
    _ = _ := (nativeAffineTestCover_toBase304 R U hf i).symm

end PfaffianDescent
