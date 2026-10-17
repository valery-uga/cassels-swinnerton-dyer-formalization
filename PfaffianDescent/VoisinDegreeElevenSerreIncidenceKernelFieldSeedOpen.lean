import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelBaseChange

/-! # An actual incidence seed makes the actual kernel-fibre open nonempty -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceKernelFieldOpen_nonempty_of_seed
    {E : Type u} [Field E] {B I P : Scheme.{u}}
    (π : I ⟶ B) (c : Spec (.of E) ⟶ B) (e : P ≅ pullback π c)
    (W : I.Opens) (s : Spec (.of E) ⟶ I) (hs : s ≫ π = c)
    (x : Spec (.of E)) (hx : s x ∈ W) :
    (((e.hom ≫ pullback.fst π c) ⁻¹ᵁ W) : Set P).Nonempty := by
  let z := pullback.lift s (𝟙 _) (by simpa using hs)
  refine ⟨e.inv (z x), ?_⟩
  change (e.hom ≫ pullback.fst π c) (e.inv (z x)) ∈ W
  have he : e.hom (e.inv (z x)) = z x := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rw [Scheme.Hom.comp_apply, he]
  have hz : pullback.fst π c (z x) = s x := by
    rw [← Scheme.Hom.comp_apply]
    change (pullback.lift s (𝟙 _) _ ≫ pullback.fst π c) x = s x
    rw [pullback.lift_fst]
  rw [hz]
  exact hx

end PfaffianDescent
