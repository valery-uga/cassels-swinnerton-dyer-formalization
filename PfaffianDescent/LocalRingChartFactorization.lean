import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Cover.Open

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A morphism from a local spectrum factors through any open chart containing its closed point. -/
lemma localRing_morphism_factors_openCover (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (f : Spec (.of R) ⟶ X) :
    ∃ i, ∃ g : Spec (.of R) ⟶ 𝒰.X i, g ≫ 𝒰.f i = f := by
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (f (IsLocalRing.closedPoint R))
  have hr : Set.range f ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map f.continuous).mem_open
      (𝒰.f i).isOpenEmbedding.isOpen_range ⟨y, hy⟩
  exact ⟨i, IsOpenImmersion.lift (𝒰.f i) f hr, IsOpenImmersion.lift_fac _ _ hr⟩

end PfaffianDescent
