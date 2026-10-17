import Mathlib.CategoryTheory.GlueData
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Gluing from compatible two-sided overlap maps

For monomorphic overlaps, a map from each intersection of two overlaps to
the third overlap, compatible with both projections, gives the rotations and
the cocycle required by categorical gluing. No geometric input is assumed
when this construction is later instantiated: the crossing maps are supplied
by the actual universal triple hypersurfaces.
-/

open CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace OverlapComposition
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {ι : Type v}
variable (U : ι → C) (V : ι → ι → C)
variable (left : ∀ i j, V i j ⟶ U i) (right : ∀ i j, V i j ⟶ U j)
variable (swap : ∀ i j, V i j ⟶ V j i)
variable (hswap : ∀ i j, swap i j ≫ left j i = right i j)
variable (cross : ∀ i j k, pullback (left i j) (left i k) ⟶ V j k)
variable (hcross : ∀ i j k, cross i j k ≫ left j k = pullback.fst (left i j) (left i k) ≫ right i j)

/-- Rotate an intersection of two overlaps using the compatible third-overlap map. -/
noncomputable def rotation (i j k : ι) :
    pullback (left i j) (left i k) ⟶ pullback (left j k) (left j i) :=
  pullback.lift (cross i j k) (pullback.fst (left i j) (left i k) ≫ swap i j) (by
    rw [hcross, Category.assoc, hswap])

local notation "ρ" => rotation U V left right swap hswap cross hcross

/-- The first rotated projection is the supplied third-overlap map. -/
theorem rotation_fst (i j k : ι) :
    ρ i j k ≫ pullback.fst (left j k) (left j i) = cross i j k :=
  pullback.lift_fst _ _ _

/-- The second rotated projection is the original first overlap with its ordering swapped. -/
theorem rotation_snd (i j k : ι) :
    ρ i j k ≫ pullback.snd (left j k) (left j i) =
      pullback.fst (left i j) (left i k) ≫ swap i j :=
  pullback.lift_snd _ _ _

variable (hcrossRight : ∀ i j k, cross i j k ≫ right j k =
  pullback.snd (left i j) (left i k) ≫ right i k)

variable [∀ i j, Mono (left i j)]

include hcrossRight in
/-- Two rotations recover the original second overlap with its ordering swapped. -/
theorem two_rotations_fst (i j k : ι) :
    ρ i j k ≫ ρ j k i ≫ pullback.fst (left k i) (left k j) =
      pullback.snd (left i j) (left i k) ≫ swap i k := by
  apply (cancel_mono (left k i)).mp
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc (ρ j k i), rotation_snd,
    Category.assoc, hswap, ← Category.assoc (ρ i j k), rotation_fst, hcrossRight, hswap]

variable (hinv : ∀ i j, swap i j ≫ swap j i = 𝟙 (V i j))

include hcrossRight hinv in
/-- Three rotations give the identity; compatibility with both overlap projections
is exactly what supplies the gluing cocycle. -/
theorem rotation_cocycle (i j k : ι) :
    ρ i j k ≫ ρ j k i ≫ ρ k i j = 𝟙 (pullback (left i j) (left i k)) := by
  apply (cancel_mono (pullback.snd (left i j) (left i k))).mp
  calc
    (ρ i j k ≫ ρ j k i ≫ ρ k i j) ≫ pullback.snd (left i j) (left i k) =
        (ρ i j k ≫ ρ j k i ≫ pullback.fst (left k i) (left k j)) ≫ swap k i := by
      simp only [Category.assoc, rotation_snd]
    _ = (pullback.snd (left i j) (left i k) ≫ swap i k) ≫ swap k i :=
      congrArg (fun a ↦ a ≫ swap k i)
        (two_rotations_fst U V left right swap hswap cross hcross hcrossRight i j k)
    _ = pullback.snd (left i j) (left i k) := by rw [Category.assoc, hinv, Category.comp_id]
    _ = 𝟙 _ ≫ pullback.snd (left i j) (left i k) := (Category.id_comp _).symm

variable [∀ i, IsIso (left i i)] (hself : ∀ i, swap i i = 𝟙 (V i i))

/-- The supplied two-sided overlaps and crossing maps give complete categorical gluing data. -/
noncomputable def glueData : CategoryTheory.GlueData C where
  J := ι
  U := U
  V := fun p ↦ V p.1 p.2
  f := left
  t := swap
  t_id := hself
  t' := ρ
  t_fac := rotation_snd U V left right swap hswap cross hcross
  cocycle := rotation_cocycle U V left right swap hswap cross hcross hcrossRight hinv

end OverlapComposition
end AllCharacteristics
