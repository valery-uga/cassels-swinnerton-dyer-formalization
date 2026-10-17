import PfaffianDescent.SectionRepresenterCechHomDifferential

/-! # Actual coefficients of cocycles differing by a boundary -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- A boundary witness computes the corrected coefficient by an explicit
alternating sum of the actual face restrictions. -/
theorem sectionRepresenterCech_boundary_corrected_coefficient
    {ι : Type u} (W : ι → C) (M : SheafOfModules.{u} R)
    (z z' : (sectionRepresenterCechChain R W).X 2 ⟶ M)
    (b : (sectionRepresenterCechChain R W).X 1 ⟶ M)
    (hb : (sectionRepresenterCechChain R W).d 2 1 ≫ b = z - z')
    (f : Fin 3 → ι) :
    let E := (FormalCoproduct.mk _ W).cech
    sectionRepresenterCechHomEquivPi R W M 2 z' f =
      sectionRepresenterCechHomEquivPi R W M 2 z f -
        (show M.val.obj (op (∏ᶜ fun i : Fin 3 => W (f i))) from
          ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
            M.val.map ((E.map (SimplexCategory.δ i).op).φ f).op
              (sectionRepresenterCechHomEquivPi R W M 1 b
                ((E.map (SimplexCategory.δ i).op).f f))) := by
  dsimp only
  let A := sectionRepresenterCechHomAddEquivPi R W M 2
  have h : A ((sectionRepresenterCechChain R W).d 2 1 ≫ b) f = A z f - A z' f := by
    rw [hb, map_sub]
    rfl
  have hd := sectionRepresenterCechHomEquivPi_d R W M 1 b f
  change A z' f = A z f - _
  rw [← hd]
  change A z' f = A z f - A ((sectionRepresenterCechChain R W).d 2 1 ≫ b) f
  rw [h, sub_sub_cancel]
end PfaffianDescent
