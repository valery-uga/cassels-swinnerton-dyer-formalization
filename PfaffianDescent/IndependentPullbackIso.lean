import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Commuting two independent pullbacks

Given maps from a scheme to two bases, base changing along one map and
restricting along the other commute. This is the canonical isomorphism
needed to identify an open equation family's field fibre with the open
subfamily constructed directly in that fibre.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X B P U T : Scheme.{u}}
  (b : X ⟶ B) (p : X ⟶ P) (i : U ⟶ P) (g : T ⟶ B)

/-- Base change along `g` commutes with restriction along `i` for two maps
out of the same scheme. -/
noncomputable def independentPullbackIso :
    pullback (pullback.fst p i ≫ b) g ≅
      pullback (pullback.fst b g ≫ p) i := by
  let L := pullback (pullback.fst p i ≫ b) g
  let R := pullback (pullback.fst b g ≫ p) i
  let lX : L ⟶ X := pullback.fst _ _ ≫ pullback.fst p i
  let lU : L ⟶ U := pullback.fst _ _ ≫ pullback.snd p i
  let lT : L ⟶ T := pullback.snd _ _
  have hlB : lX ≫ b = lT ≫ g := by
    dsimp [lX, lT]
    rw [Category.assoc]
    exact pullback.condition
  let lF : L ⟶ pullback b g := pullback.lift lX lT hlB
  have hlP : lF ≫ pullback.fst b g ≫ p = lU ≫ i := by
    dsimp [lF, lU]
    rw [pullback.lift_fst_assoc]
    rw [Category.assoc]
    exact congrArg (fun z => pullback.fst (pullback.fst p i ≫ b) g ≫ z)
      (pullback.condition : pullback.fst p i ≫ p = pullback.snd p i ≫ i)
  let toR : L ⟶ R := pullback.lift lF lU hlP
  let rX : R ⟶ X := pullback.fst _ _ ≫ pullback.fst b g
  let rT : R ⟶ T := pullback.fst _ _ ≫ pullback.snd b g
  let rU : R ⟶ U := pullback.snd _ _
  have hrP : rX ≫ p = rU ≫ i := by
    dsimp [rX, rU]
    rw [Category.assoc]
    exact pullback.condition
  let rO : R ⟶ pullback p i := pullback.lift rX rU hrP
  have hrB : rO ≫ pullback.fst p i ≫ b = rT ≫ g := by
    dsimp [rO, rT]
    rw [pullback.lift_fst_assoc, Category.assoc]
    exact congrArg (fun z => pullback.fst (pullback.fst b g ≫ p) i ≫ z)
      (pullback.condition : pullback.fst b g ≫ b = pullback.snd b g ≫ g)
  let toL : R ⟶ L := pullback.lift rO rT hrB
  refine ⟨toR, toL, ?_, ?_⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, toR, toL, lF, rO, lX, rX,
          pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · simp only [Category.assoc, toR, toL, lF, rO, lU, rU,
          pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [Category.assoc, toR, toL, lF, rO, lT, rT,
        pullback.lift_snd, pullback.lift_fst_assoc, Category.id_comp]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, toR, toL, lF, rO, lX, rX,
          pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · simp only [Category.assoc, toR, toL, lF, rO, lT, rT,
          pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [Category.assoc, toR, toL, lF, rO, lU, rU,
        pullback.lift_snd, pullback.lift_fst_assoc, Category.id_comp]

/-- The comparison preserves the map to the original family. -/
theorem independentPullbackIso_hom_toX :
    (independentPullbackIso b p i g).hom ≫
        pullback.fst (pullback.fst b g ≫ p) i ≫ pullback.fst b g =
      pullback.fst (pullback.fst p i ≫ b) g ≫ pullback.fst p i := by
  simp [independentPullbackIso, pullback.lift_fst_assoc, pullback.lift_fst]

/-- The comparison preserves the restricted equation parameter. -/
theorem independentPullbackIso_hom_toU :
    (independentPullbackIso b p i g).hom ≫
        pullback.snd (pullback.fst b g ≫ p) i =
      pullback.fst (pullback.fst p i ≫ b) g ≫ pullback.snd p i := by
  simp [independentPullbackIso, pullback.lift_snd]

/-- The comparison preserves the map to the base-change scheme. -/
theorem independentPullbackIso_hom_toT :
    (independentPullbackIso b p i g).hom ≫
        pullback.fst (pullback.fst b g ≫ p) i ≫ pullback.snd b g =
      pullback.snd (pullback.fst p i ≫ b) g := by
  simp [independentPullbackIso, pullback.lift_fst_assoc, pullback.lift_snd]

end PfaffianDescent
