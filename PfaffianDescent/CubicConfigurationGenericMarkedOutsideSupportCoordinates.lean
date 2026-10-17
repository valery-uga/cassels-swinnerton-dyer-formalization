import AllCharacteristics.RelativeConfigurationPermutations
import Mathlib.AlgebraicGeometry.FunctionField
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationGenericMarkedOutsideSupport_generic_map_of_open
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : IsOpenMap f) : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  have hr : IsOpen (Set.range f) := by simpa only [Set.image_univ] using hf Set.univ isOpen_univ
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ hr _
  · rw [Set.univ_inter, Set.image_univ]
  · exact PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self (Classical.choice (inferInstance : Nonempty X))⟩

theorem cubicConfigurationGenericMarkedOutsideSupport_coordinate_smooth
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (n : ℕ) (j : Fin n) :
    Smooth (orderedFamilyCoordinate f n j).left := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · change Smooth (pullback.fst f (orderedFamilyPowerOver f n).hom)
      infer_instance
    · letI : Smooth (orderedFamilyCoordinate f n k).left := ih k
      change Smooth (pullback.snd f (orderedFamilyPowerOver f n).hom ≫
        (orderedFamilyCoordinate f n k).left)
      infer_instance

theorem cubicConfigurationGenericMarkedOutsideSupport_rank_coordinate_generic
    {X S A : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsSeparated f]
    [IsIntegral X] [IsIntegral A]
    (a : A ⟶ (orderedFamilyConfigurationOver f 3).left) [IsOpenImmersion a]
    (j : Fin 3) :
    (a ≫ (orderedFamilyConfigurationι f 3).left ≫
      (orderedFamilyCoordinate f 3 j).left) (genericPoint A) = genericPoint X := by
  letI : IsOpenImmersion (orderedFamilyConfigurationι f 3).left := by
    change IsOpenImmersion (orderedFamilyConfigurationOpen f 3).ι
    infer_instance
  letI : Smooth (orderedFamilyCoordinate f 3 j).left :=
    cubicConfigurationGenericMarkedOutsideSupport_coordinate_smooth f 3 j
  let q : A ⟶ X := a ≫ (orderedFamilyConfigurationι f 3).left ≫ (orderedFamilyCoordinate f 3 j).left
  letI : Smooth q := by dsimp [q]; infer_instance
  exact cubicConfigurationGenericMarkedOutsideSupport_generic_map_of_open q q.isOpenMap
end PfaffianDescent
