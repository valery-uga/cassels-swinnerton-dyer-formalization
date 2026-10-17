import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Basic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_field_of_bijective
    {K A : Type*} [Field K] [CommRing A] (f : K →+* A)
    (hf : Function.Bijective f) : IsField A := by
  refine ⟨⟨f 0, f 1, fun h => zero_ne_one (hf.1 h)⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨k, rfl⟩ := hf.2 a
  have hk : k ≠ 0 := fun h => ha (h ▸ f.map_zero)
  refine ⟨f k⁻¹, ?_⟩
  rw [← f.map_mul, mul_inv_cancel₀ hk, f.map_one]

theorem cubicClosedPointSerreFiniteZeroResidual_specField_stalk_isField
    {K : Type u} [Field K] (y : Spec (.of K)) :
    IsField ((Spec (.of K)).presheaf.stalk y) := by
  let e := (Spec.stalkIso (.of K) y).commRingCatIsoToRingEquiv
  have hloc : Function.Bijective (algebraMap K (Localization.AtPrime y.asIdeal)) :=
    Field.localization_map_bijective (M := y.asIdeal.primeCompl)
      (by simpa using y.asIdeal.zero_mem)
  exact cubicClosedPointSerreFiniteZeroResidual_field_of_bijective
    (e.symm.toRingHom.comp (algebraMap K (Localization.AtPrime y.asIdeal)))
    (e.symm.bijective.comp hloc)

theorem cubicClosedPointSerreFiniteZeroResidual_unramifiedField_stalk_isField
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    IsField (X.presheaf.stalk x) := by
  let R := (Spec (.of K)).presheaf.stalk (f x)
  letI : Field R :=
    (cubicClosedPointSerreFiniteZeroResidual_specField_stalk_isField (f x)).toField
  letI := (f.stalkMap x).hom.toAlgebra
  letI : Algebra.FormallyUnramified R (X.presheaf.stalk x) := FormallyUnramified.stalkMap f x
  letI : Algebra.EssFiniteType R (X.presheaf.stalk x) := LocallyOfFiniteType.stalkMap f x
  letI : Module.Finite R (X.presheaf.stalk x) :=
    Algebra.FormallyUnramified.finite_of_free R (X.presheaf.stalk x)
  letI : IsArtinianRing (X.presheaf.stalk x) := IsArtinianRing.of_finite R _
  letI : IsReduced (X.presheaf.stalk x) :=
    Algebra.FormallyUnramified.isReduced_of_field R _
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

end PfaffianDescent
