import Mathlib.AlgebraicGeometry.OpenImmersion

/-! A field point factors through an open whenever one extension-field
point above it does. The lifted point retains its literal specialization. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

variable {F E : Type u} [Field F] [Field E]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (i : Spec (.of F) ⟶ X) (β : F →+* E)
variable (b : Spec (.of E) ⟶ U)
variable (h : Spec.map (CommRingCat.ofHom β) ≫ i = b ≫ j)

include h

theorem fieldPoint_range_subset_of_extension_open_factor :
    Set.range i ⊆ Set.range j := by
  rintro _ ⟨z, rfl⟩
  let e := IsLocalRing.closedPoint E
  refine ⟨b e, ?_⟩
  calc
    j (b e) = (b ≫ j) e := rfl
    _ = (Spec.map (CommRingCat.ofHom β) ≫ i) e :=
      congrArg (fun f : Spec (.of E) ⟶ X => f e) h.symm
    _ = i z := congrArg i (Subsingleton.elim _ _)

def fieldPointOpenLift : Spec (.of F) ⟶ U :=
  IsOpenImmersion.lift j i
    (fieldPoint_range_subset_of_extension_open_factor j i β b h)

@[reassoc] theorem fieldPointOpenLift_fac :
    fieldPointOpenLift j i β b h ≫ j = i :=
  IsOpenImmersion.lift_fac j i
    (fieldPoint_range_subset_of_extension_open_factor j i β b h)

theorem fieldPointOpenLift_extension :
    Spec.map (CommRingCat.ofHom β) ≫ fieldPointOpenLift j i β b h = b := by
  apply (cancel_mono j).mp
  rw [Category.assoc, fieldPointOpenLift_fac]
  exact h

end PfaffianDescent
