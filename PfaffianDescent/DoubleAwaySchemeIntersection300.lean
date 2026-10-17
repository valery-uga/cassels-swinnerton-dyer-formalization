import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {A : Type u} [CommRing A] (a b : A)

/-- The ordinary double localization; the original base ring is unchanged. -/
abbrev DoubleAwayCoefficientAlgebra300 :=
  Localization.Away (algebraMap A (Localization.Away a) b)

/-- Its actual structure morphism to the original coefficient affine scheme. -/
def doubleAwayBaseSpecMap300 :
    Spec (.of (DoubleAwayCoefficientAlgebra300 a b)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (DoubleAwayCoefficientAlgebra300 a b)))

lemma doubleAwayBaseSpecMap_factor300 :
    doubleAwayBaseSpecMap300 a b =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away a) (DoubleAwayCoefficientAlgebra300 a b))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) := by
  rw [doubleAwayBaseSpecMap300, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq A (Localization.Away a) (DoubleAwayCoefficientAlgebra300 a b)]

lemma doubleAwayBaseSpecMap_isOpenImmersion300 :
    IsOpenImmersion (doubleAwayBaseSpecMap300 a b) := by
  rw [doubleAwayBaseSpecMap_factor300]
  infer_instance

/-- The double localization is exactly the intersection of the two original determinant opens. -/
lemma doubleAwayBaseSpecMap_range300 :
    Set.range (doubleAwayBaseSpecMap300 a b) =
      ((PrimeSpectrum.basicOpen a ⊓ PrimeSpectrum.basicOpen b) : Set (PrimeSpectrum A)) := by
  letI : IsLocalization.Away (a * b) (DoubleAwayCoefficientAlgebra300 a b) :=
    IsLocalization.Away.mul' (Localization.Away a) (DoubleAwayCoefficientAlgebra300 a b) a b
  exact (PrimeSpectrum.localization_away_comap_range
    (DoubleAwayCoefficientAlgebra300 a b) (a * b)).trans
      (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum A) => (U : Set (PrimeSpectrum A))) (PrimeSpectrum.basicOpen_mul a b))

/-- The native double-localization square is Cartesian once the second
localization's actual ring map is shown to commute with the original base.
The genuine monomial caller derives this elementary map equality internally. -/
lemma doubleAwaySpec_isPullback300
    (g : Localization.Away b →+* DoubleAwayCoefficientAlgebra300 a b)
    (hg : g.comp (algebraMap A (Localization.Away b)) =
      (algebraMap (Localization.Away a) (DoubleAwayCoefficientAlgebra300 a b)).comp
        (algebraMap A (Localization.Away a))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away a) (DoubleAwayCoefficientAlgebra300 a b))))
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) := by
  letI : IsLocalization
      ((Submonoid.powers b).map (algebraMap A (Localization.Away a)))
      (DoubleAwayCoefficientAlgebra300 a b) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization
      (algebraMap A (Localization.Away a)) g hg (Submonoid.powers b))

end PfaffianDescent
