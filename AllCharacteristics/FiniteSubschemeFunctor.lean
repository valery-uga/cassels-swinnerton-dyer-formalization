import AllCharacteristics.RelativeFamilyFunctor
import AllCharacteristics.IdealSubschemeBaseChange

/-!
# The functor of finite flat subschemes of fixed rank

A datum is an actual ideal sheaf whose closed subscheme is finite, flat,
locally of finite presentation, and of the specified constant rank over the
base. Pullback preserves these properties. Thus these data define a functor
on schemes over the base. No representability assertion is assumed here.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace AllCharacteristics
universe u

/-- An ideal-defined finite flat subscheme of constant rank in an actual family. -/
noncomputable abbrev FiniteSubschemeDatum {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) : Type u :=
  { I : X.IdealSheafData //
    IsFinite (I.subschemeι ≫ f) ∧ Flat (I.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ f) ∧
        ∀ s : S, (I.subschemeι ≫ f).finrank s = n }

namespace FiniteSubschemeDatum
variable {X Y S T : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ T} {n : ℕ}

/-- Pullback of the ideal defines a finite flat subscheme of the same rank
under a Cartesian change of the ambient family. -/
noncomputable def baseChange (g : X ⟶ Y) (b : S ⟶ T) (h : IsPullback g p q b)
    (I : FiniteSubschemeDatum q n) : FiniteSubschemeDatum p n := by
  have : IsFinite (I.val.subschemeι ≫ q) := I.property.1
  have : Flat (I.val.subschemeι ≫ q) := I.property.2.1
  have : LocallyOfFinitePresentation (I.val.subschemeι ≫ q) := I.property.2.2.1
  have hc := isPullback_idealSubschemeFamily I.val g p q b h
  refine ⟨I.val.comap g,
    MorphismProperty.of_isPullback (P := @IsFinite.{u}) hc inferInstance,
    MorphismProperty.of_isPullback (P := @Flat.{u}) hc inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation.{u}) hc inferInstance, ?_⟩
  intro s
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hc s).trans (I.property.2.2.2 (b s))

/-- The pulled-back datum has exactly the ordinary pullback ideal sheaf. -/
theorem baseChange_ideal (g : X ⟶ Y) (b : S ⟶ T) (h : IsPullback g p q b)
    (I : FiniteSubschemeDatum q n) : (baseChange g b h I).val = I.val.comap g := rfl

end FiniteSubschemeDatum

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The relative functor of finite flat subschemes of constant rank `n`.
Its values consist of actual closed subschemes of the pulled-back family. -/
noncomputable def finiteSubschemeFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := FiniteSubschemeDatum ((relativeFamilyProjection f).app T.unop) n
  map {T U} φ := ↾fun I ↦ FiniteSubschemeDatum.baseChange (n := n)
    ((relativeFamilyFunctor f).map φ.unop) φ.unop.left
    (isPullback_relativeFamilyFunctor f φ.unop) I
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro I
    apply Subtype.ext
    change I.val.comap ((relativeFamilyFunctor f).map (𝟙 T.unop)) = I.val
    rw [CategoryTheory.Functor.map_id, Scheme.IdealSheafData.comap_id]
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro I
    apply Subtype.ext
    change I.val.comap ((relativeFamilyFunctor f).map (ψ.unop ≫ φ.unop)) =
      (I.val.comap ((relativeFamilyFunctor f).map φ.unop)).comap ((relativeFamilyFunctor f).map ψ.unop)
    rw [CategoryTheory.Functor.map_comp, Scheme.IdealSheafData.comap_comp]

end AllCharacteristics
