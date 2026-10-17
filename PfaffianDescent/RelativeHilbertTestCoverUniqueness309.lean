import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197
import PfaffianDescent.NativeSchemeCoverIsoCharts300
import PfaffianDescent.WholeIdealOpenCoverUniqueness
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B : Scheme.{u}} (F : X ⟶ B) (T : Over B) (U : T.left.OpenCover.{u})

/-- Original base-cover component as an actual original-base test object. -/
def relativeHilbertTestCoverObject309 (i : U.I₀) : Over B :=
  Over.mk (U.f i ≫ T.hom)

def relativeHilbertTestCoverMap309 (i : U.I₀) : relativeHilbertTestCoverObject309 T U i ⟶ T :=
  Over.homMk (U.f i) rfl

/-- Pull back the genuine test cover and identify its components using derived197 Cartesian squares. -/
def relativeHilbertAmbientTestOpenCover309 : (pullback T.hom F).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300 (U.pullback₁ (relativeHilbertFamily197 F T))
    (fun i => pullback (relativeHilbertTestCoverObject309 T U i).hom F)
    (fun i => (relativeHilbertAmbientMap_isPullback197 F
      (relativeHilbertTestCoverMap309 T U i)).isoPullback)

lemma relativeHilbertAmbientTestOpenCover_map309 (i : U.I₀) :
    (relativeHilbertAmbientTestOpenCover309 F T U).f i =
      relativeHilbertAmbientMap197 F (relativeHilbertTestCoverMap309 T U i) := by
  change (relativeHilbertAmbientMap_isPullback197 F
      (relativeHilbertTestCoverMap309 T U i)).isoPullback.hom ≫
    pullback.fst (relativeHilbertFamily197 F T) (U.f i) = _
  exact (relativeHilbertAmbientMap_isPullback197 F
    (relativeHilbertTestCoverMap309 T U i)).isoPullback_hom_fst

/-- Entire relative finite-flat points are equal when their actual cover restrictions are equal. -/
lemma relativeHilbertPoint_eq_of_testCover309 (n : ℕ)
    (P Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n)
    (h : ∀ i : U.I₀,
      (relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeHilbertTestCoverMap309 T U i).op P =
        (relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeHilbertTestCoverMap309 T U i).op Q) : P = Q := by
  apply Subtype.ext
  apply wholeIdeal_eq_of_openCover_comaps (relativeHilbertAmbientTestOpenCover309 F T U)
  intro i
  have hi := congrArg Subtype.val (h i)
  have hp := congrArg P.val.comap (relativeHilbertAmbientTestOpenCover_map309 F T U i)
  have hq := congrArg Q.val.comap (relativeHilbertAmbientTestOpenCover_map309 F T U i)
  exact hp.trans (hi.trans hq.symm)

/-- The actual affine cover is selected INTERNALLY on an arbitrary test Scheme. -/
lemma relativeHilbertPoint_eq_of_affineRestrictions309 (n : ℕ)
    (P Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n)
    (h : ∀ i : T.left.affineCover.I₀,
      (relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeHilbertTestCoverMap309 T T.left.affineCover i).op P =
        (relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeHilbertTestCoverMap309 T T.left.affineCover i).op Q) : P = Q :=
  relativeHilbertPoint_eq_of_testCover309 F T T.left.affineCover n P Q h

end PfaffianDescent
end
