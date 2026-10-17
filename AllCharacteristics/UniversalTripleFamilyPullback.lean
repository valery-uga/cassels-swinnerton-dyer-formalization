import AllCharacteristics.UniversalTripleHypersurfaceMaps
import AllCharacteristics.ProjectiveTriplePairIntersection
import AllCharacteristics.PullbackIntersectionCube

/-!
# Actual intersections of universal overlap families

The common triple hypersurface is the Cartesian intersection of the first and
outer overlap families. Its projection to the last pair supplies the crossing
map used by scheme gluing.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
variable (i j l : Monomials σ d)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- The triple hypersurface is the base change of the first pair-overlap family. -/
theorem isPullback_normalizedTripleToFirstPair :
    IsPullback (normalizedTripleToFirstPair R σ d i j l) (normalizedTripleToBase R σ d i j l)
      (normalizedOverlapToBase R σ d i j)
      (Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I₀ i j l))) :=
  isPullback_projectiveCoefficientMap _ _ _ (normalizedTripleFirstPair_ideal R σ d i j l)

/-- The outer-pair projection preserves the triple coefficient base. -/
theorem normalizedTripleToOuterPair_toBase :
    normalizedTripleToOuterPair R σ d i j l ≫ normalizedOverlapToBase R σ d i l =
      normalizedTripleToBase R σ d i j l ≫
        Spec.map (CommRingCat.ofHom (chartTripleFromOuterPair I₀ i j l)) :=
  projectiveCoefficientMap_toBase _ _ _ (normalizedTripleOuterPair_ideal R σ d i j l)

/-- The actual triple hypersurface is the intersection of two overlap families
inside their common first universal chart family. -/
theorem isPullback_normalizedTripleFirstOuter :
    IsPullback (normalizedTripleToFirstPair R σ d i j l)
      (normalizedTripleToOuterPair R σ d i j l)
      (normalizedOverlapToLeft R σ d i j) (normalizedOverlapToLeft R σ d i l) := by
  refine isPullback_intersection_cube _ _ _ _
    (normalizedTripleToBase R σ d i j l) (normalizedOverlapToBase R σ d i j)
    (normalizedOverlapToBase R σ d i l) (normalizedFamilyToBase R σ d i)
    (Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I₀ i j l)))
    (Spec.map (CommRingCat.ofHom (chartTripleFromOuterPair I₀ i j l)))
    (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ i j)))
    (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ i l)))
    (isPullback_normalizedTripleToFirstPair R σ d i j l)
    (isPullback_chartTripleFirstOuter I₀ i j l)
    (isPullback_normalizedOverlapToLeft R σ d i l)
    (normalizedTripleToOuterPair_toBase R σ d i j l)
    (isPullback_normalizedOverlapToLeft R σ d i j).w ?_
  rw [normalizedTripleToFirstPair_left, normalizedTripleToOuterPair_left]

/-- Identify the triple hypersurface with the actual categorical intersection. -/
noncomputable def normalizedTripleFirstOuterIso :
    normalizedTripleHypersurface R σ d i j l ≅
      pullback (normalizedOverlapToLeft R σ d i j) (normalizedOverlapToLeft R σ d i l) :=
  (isPullback_normalizedTripleFirstOuter R σ d i j l).isoPullback

/-- Map the intersection of two overlaps to the third pair-overlap family. -/
noncomputable def normalizedOverlapCross :
    pullback (normalizedOverlapToLeft R σ d i j) (normalizedOverlapToLeft R σ d i l) ⟶
      normalizedOverlapHypersurface R σ d j l :=
  (normalizedTripleFirstOuterIso R σ d i j l).inv ≫ normalizedTripleToLastPair R σ d i j l

/-- The crossing map agrees with the original first overlap over the middle chart. -/
theorem normalizedOverlapCross_left :
    normalizedOverlapCross R σ d i j l ≫ normalizedOverlapToLeft R σ d j l =
      pullback.fst (normalizedOverlapToLeft R σ d i j) (normalizedOverlapToLeft R σ d i l) ≫
        normalizedOverlapToRight R σ d i j := by
  change ((normalizedTripleFirstOuterIso R σ d i j l).inv ≫
    normalizedTripleToLastPair R σ d i j l) ≫ _ = _
  rw [Category.assoc, normalizedTripleToLastPair_left,
    ← normalizedTripleToFirstPair_right, ← Category.assoc]
  exact congrArg (fun a ↦ a ≫ normalizedOverlapToRight R σ d i j)
    (isPullback_normalizedTripleFirstOuter R σ d i j l).isoPullback_inv_fst

/-- The crossing map agrees with the original outer overlap over the last chart. -/
theorem normalizedOverlapCross_right :
    normalizedOverlapCross R σ d i j l ≫ normalizedOverlapToRight R σ d j l =
      pullback.snd (normalizedOverlapToLeft R σ d i j) (normalizedOverlapToLeft R σ d i l) ≫
        normalizedOverlapToRight R σ d i l := by
  change ((normalizedTripleFirstOuterIso R σ d i j l).inv ≫
    normalizedTripleToLastPair R σ d i j l) ≫ _ = _
  rw [Category.assoc, normalizedTripleToLastPair_right,
    ← normalizedTripleToOuterPair_right, ← Category.assoc]
  exact congrArg (fun a ↦ a ≫ normalizedOverlapToRight R σ d i l)
    (isPullback_normalizedTripleFirstOuter R σ d i j l).isoPullback_inv_snd

end UniversalHomogeneous
end AllCharacteristics
