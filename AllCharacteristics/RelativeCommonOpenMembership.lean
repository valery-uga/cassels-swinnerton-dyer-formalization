import AllCharacteristics.RelativeOrderedMapGeometry
import AllCharacteristics.FieldPointOpenLocus

/-!
# Exact membership in the common-open tuple charts

A point of an ordered power lies in the common-open chart exactly when all
its coordinate points lie in the original open. The reverse implication is
proved using the point's own residue field and the representing tuple map,
so no algebraic closure or separability assumption enters the comparison.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (n : ℕ)

/-- A point belongs to the actual common-open tuple chart precisely when all its coordinates do. -/
theorem mem_orderedFamilyCommonOpen_iff (x : (orderedFamilyPowerOver f n).left) :
    x ∈ orderedFamilyCommonOpen f U n ↔
      ∀ i : Fin n, Over.Hom.left (orderedFamilyCoordinate f n i) x ∈ U := by
  constructor
  · rintro ⟨y, rfl⟩ i
    have hi := congrArg Over.Hom.left
      (orderedFamilyMap_coordinate (U.ι ≫ f) f (Over.homMk U.ι rfl) n i)
    have he := congrArg (fun z ↦ z y) hi
    change Over.Hom.left (orderedFamilyCoordinate f n i)
      (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n) y) =
        U.ι (Over.Hom.left (orderedFamilyCoordinate (U.ι ≫ f) n i) y) at he
    rw [he]
    exact (Over.Hom.left (orderedFamilyCoordinate (U.ι ≫ f) n i) y).property
  · intro hx
    let P := orderedFamilyPowerOver f n
    let K : Type u := P.left.residueField x
    let r : Spec (.of K) ⟶ P.left := P.left.fromSpecResidueField x
    let b : Spec (.of K) ⟶ S := r ≫ P.hom
    let a : Over.mk b ⟶ P := Over.homMk r rfl
    have hr : r (IsLocalRing.closedPoint K) = x := Scheme.fromSpecResidueField_apply _ _
    have hlifts (i : Fin n) : ∃ l : Spec (.of K) ⟶ U.toScheme,
        l ≫ U.ι = r ≫ Over.Hom.left (orderedFamilyCoordinate f n i) := by
      apply (fieldPoint_mem_open_range_iff U.ι
        (r ≫ Over.Hom.left (orderedFamilyCoordinate f n i))).mp
      change Over.Hom.left (orderedFamilyCoordinate f n i) (r (IsLocalRing.closedPoint K)) ∈
        Set.range U.ι
      rw [hr]
      exact ⟨⟨Over.Hom.left (orderedFamilyCoordinate f n i) x, hx i⟩, rfl⟩
    choose l hl using hlifts
    let s (i : Fin n) : Over.mk b ⟶ Over.mk (U.ι ≫ f) := Over.homMk (l i) (by
      change l i ≫ (U.ι ≫ f) = r ≫ P.hom
      rw [← Category.assoc, hl i, Category.assoc, orderedFamilyCoordinate_toBase])
    let t := orderedFamilyTuple (U.ι ≫ f) (Over.mk b) n s
    have ht : t ≫ orderedFamilyCommonOpenPowerMap f U n = a := by
      apply orderedFamilyPower_coordinate_ext f _ n
      intro i
      change (t ≫ orderedFamilyMap (U.ι ≫ f) f (Over.homMk U.ι rfl) n) ≫
        orderedFamilyCoordinate f n i = a ≫ orderedFamilyCoordinate f n i
      rw [Category.assoc, orderedFamilyMap_coordinate, ← Category.assoc]
      change (orderedFamilyTuple (U.ι ≫ f) (Over.mk b) n s ≫
        orderedFamilyCoordinate (U.ι ≫ f) n i) ≫
          (Over.homMk U.ι rfl : Over.mk (U.ι ≫ f) ⟶ Over.mk f) = _
      rw [orderedFamilyTuple_coordinate]
      apply Over.OverMorphism.ext
      exact hl i
    refine ⟨Over.Hom.left t (IsLocalRing.closedPoint K), ?_⟩
    have he := congrArg (fun z : Over.mk b ⟶ P ↦ Over.Hom.left z (IsLocalRing.closedPoint K)) ht
    exact he.trans hr

end AllCharacteristics
