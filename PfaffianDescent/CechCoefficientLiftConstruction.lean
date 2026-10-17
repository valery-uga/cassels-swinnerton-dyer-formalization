import PfaffianDescent.CechCoefficientConnectingCompatibility

/-! # Constructing coefficient lifts and their actual boundary cocycles -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Retain the lift, its boundary cocycle, and both actual coefficient squares. -/
structure CechCoefficientLift (C : ChainComplex A ℕ) (S : ShortComplex A)
    (z : DegreeTwoCocycle (C.d 3 2) (Y := S.X₃)) where
  lift : C.X 2 ⟶ S.X₂
  boundary : DegreeThreeCocycle (C.d 4 3) (Y := S.X₁)
  lift_comp : lift ≫ S.g = z.1
  differential_comp : C.d 3 2 ≫ lift = boundary.1 ≫ S.f

/-- The lift and its degree-three cocycle are constructed from the actual
short exact coefficient sequence and proved source Ext¹ vanishing. -/
theorem exists_cech_coefficient_lift
    (C : ChainComplex A ℕ) (S : ShortComplex A) (hS : S.ShortExact)
    [Subsingleton (Ext.{w} (C.X 2) S.X₁ 1)]
    (z : DegreeTwoCocycle (C.d 3 2) (Y := S.X₃)) :
    Nonempty (CechCoefficientLift C S z) := by
  obtain ⟨l, hl⟩ := hom_postcomp_surjective_of_ext_one_subsingleton (C.X 2) S hS z.1
  change l ≫ S.g = z.1 at hl
  letI : Mono S.f := hS.mono_f
  have hz : (C.d 3 2 ≫ l) ≫ S.g = 0 := by
    rw [Category.assoc, hl]
    exact z.2
  let a : C.X 3 ⟶ S.X₁ := hS.exact.lift (C.d 3 2 ≫ l) hz
  have ha : a ≫ S.f = C.d 3 2 ≫ l := hS.exact.lift_f _ hz
  have hcycle : C.d 4 3 ≫ a = 0 := by
    apply (cancel_mono S.f).1
    rw [Category.assoc, ha, ← Category.assoc, C.d_comp_d 4 3 2, zero_comp, zero_comp]
  exact ⟨{
    lift := l
    boundary := ⟨a, hcycle⟩
    lift_comp := hl
    differential_comp := ha.symm
  }⟩
end PfaffianDescent
