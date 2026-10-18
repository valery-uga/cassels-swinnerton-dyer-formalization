import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
Reflect an actual residue unit through a surjective
ring map with nilpotent kernel, without requiring the total ring to be local.
-/

noncomputable section
namespace AllCharacteristics
universe u v

theorem isUnit_of_surjective_nilpotent_reduction318
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π)) (a : A) (ha : IsUnit (π a)) : IsUnit a := by
  let e := π.quotientKerEquivOfSurjective hπ
  have hq : IsUnit (e.symm (π a)) := ha.map e.symm.toMonoidHom
  change IsUnit ((π.quotientKerEquivOfSurjective hπ).symm (π a)) at hq
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply] at hq
  exact (hker.isUnit_quotient_mk_iff).mp hq

end AllCharacteristics
end
