import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineClosedFibreStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedStalkGerm
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedSectionSeed

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineMarkedSeed_of_field_stalks
    {K : Type u} [Field K] {Z Y : Scheme.{u}} [IsAffine Z] [IsAffine Y]
    (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (i : Spec (.of K) ⟶ Y) [IsClosedImmersion i]
    (hfield : ∀ z : (pullback g i : Scheme), IsField ((pullback g i).presheaf.stalk z))
    (b : Spec (.of K))
    [IsNoetherianRing (Z.presheaf.stalk (j (i b)))] :
    i b ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
  let m : Spec (.of K) ⟶ pullback g i :=
    pullback.lift (i ≫ j) (𝟙 _) (by simp only [Category.assoc, hj, Category.comp_id, Category.id_comp])
  let z : (pullback g i : Scheme) := m b
  have hz : pullback.fst g i z = j (i b) := by
    change (m ≫ pullback.fst g i) b = (i ≫ j) b
    rw [pullback.lift_fst]
  let I := i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩
  have hI : I.map (Y.presheaf.germ ⊤ (i b) trivial).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (i b)) := by
    rw [cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
      i ⟨⊤, isAffineOpen_top Y⟩ b trivial]
    letI : Field ((Spec (.of K)).presheaf.stalk b) :=
      (cubicClosedPointSerreFiniteZeroResidual_specField_stalk_isField b).toField
    apply IsLocalRing.eq_maximalIdeal
    exact RingHom.ker_isMaximal_of_surjective (i.stalkMap b).hom (i.stalkMap_surjective b)
  have hf := hfield z
  letI : Field ((pullback g i).presheaf.stalk z) := hf.toField
  let e := cubicClosedPointSerreFiniteZeroResidual_affineClosedFibre_stalkQuotient g i z
  have hq := cubicClosedPointSerreFiniteZeroResidual_field_of_bijective
    e.symm.toRingHom e.symm.bijective
  rw [hz] at hq
  have hIdeal := cubicClosedPointSerreFiniteZeroResidual_markedStalk_fibre_ideal
    g j hj (i b) I hI
  rw [Ideal.map_map] at hIdeal
  change IsField (Z.presheaf.stalk (j (i b)) ⧸
    I.map ((Z.presheaf.germ ⊤ (j (i b)) trivial).hom.comp g.appTop.hom)) at hq
  rw [hIdeal] at hq
  exact cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen_mem_of_field_fiber
    g j hj (i b) hq

end PfaffianDescent
