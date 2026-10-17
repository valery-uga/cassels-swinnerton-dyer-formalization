import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalStructure

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Étale morphisms are locally quasi-finite, via their affine coordinate maps. -/
lemma etale_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  let φ := (f.appLE U V e).hom
  have hφ : φ.Etale := f.etale_appLE hU hV e
  letI := φ.toAlgebra
  haveI : Algebra.Etale Γ(Y, U) Γ(X, V) := hφ
  change Algebra.QuasiFinite Γ(Y, U) Γ(X, V)
  infer_instance

section
variable {X Y U Z : Scheme.{u}} (f : X ⟶ Y) (i : U ⟶ X)
  [UniversallyClosed f] [IsOpenImmersion i]

/-- Remove the closed image of the complement of an open chart. -/
noncomputable def properTargetOpen : Y.Opens :=
  ⟨(f '' (Set.range i)ᶜ)ᶜ,
    (f.isClosedMap _ (IsOpenImmersion.isOpen_range i).isClosed_compl).isOpen_compl⟩

lemma properTargetOpen_preimage :
    f ⁻¹' (properTargetOpen f i : Set Y) ⊆ Set.range i := by
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

/-- A fiber contained in the chosen chart survives the target shrinking. -/
lemma properTargetOpen_contains_image (g : Z ⟶ Y)
    (h : Set.range (pullback.fst f g) ⊆ Set.range i) :
    Set.range g ⊆ (properTargetOpen f i : Set Y) := by
  intro y hy
  rintro ⟨x, hx, hxy⟩
  apply hx
  apply h
  rw [Scheme.Pullback.range_fst]
  change f x ∈ Set.range g
  exact hxy ▸ hy

/-- If the projection is étale on an open chart, it is étale over this smaller target. -/
theorem properTargetOpen_etale [Etale (i ≫ f)] : Etale (f ∣_ properTargetOpen f i) := by
  let V := properTargetOpen f i
  have hr : Set.range (f ⁻¹ᵁ V).ι ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact properTargetOpen_preimage f i x.property
  let l := IsOpenImmersion.lift i (f ⁻¹ᵁ V).ι hr
  have hl : l ≫ i = (f ⁻¹ᵁ V).ι := IsOpenImmersion.lift_fac i _ hr
  haveI : IsOpenImmersion (l ≫ i) := hl ▸ inferInstance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l i
  have he : l ≫ (i ≫ f) = (f ⁻¹ᵁ V).ι ≫ f := by rw [← Category.assoc, hl]
  haveI : Etale ((f ⁻¹ᵁ V).ι ≫ f) := he ▸ inferInstance
  haveI : Etale (f ∣_ V ≫ V.ι) := (morphismRestrict_ι f V).symm ▸ inferInstance
  exact Etale.of_comp (f ∣_ V) V.ι

/-- Properness turns the étale restriction into a finite étale morphism. -/
theorem properTargetOpen_finite [IsProper f] [Etale (i ≫ f)] :
    IsFinite (f ∣_ properTargetOpen f i) := by
  haveI := properTargetOpen_etale f i
  haveI := etale_locallyQuasiFinite (f ∣_ properTargetOpen f i)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f ∣_ properTargetOpen f i)

/-- A proper map which is étale on an open neighborhood of a fiber is finite étale after shrinking the target. -/
theorem proper_finite_etale_neighborhood [IsProper f] [Etale (i ≫ f)] (g : Z ⟶ Y)
    (h : Set.range (pullback.fst f g) ⊆ Set.range i) :
    ∃ V : Y.Opens, Set.range g ⊆ (V : Set Y) ∧ IsFinite (f ∣_ V) ∧ Etale (f ∣_ V) :=
  ⟨properTargetOpen f i, properTargetOpen_contains_image f i g h,
    properTargetOpen_finite f i, properTargetOpen_etale f i⟩

end
end PfaffianDescent
