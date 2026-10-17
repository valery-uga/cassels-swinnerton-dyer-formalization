import AllCharacteristics.RelativeConfigurationOpen
import AllCharacteristics.RelativeOrderedReindex

/-!
# Reindexing distinct relative configurations

An injective choice of coordinates preserves the actual distinct-point open.
The proof tests the open at each residue-field point and uses the field-valued
criterion already proved. It consequently applies to arbitrary scheme points,
including points over imperfect fields.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- An injective reindexing of an actual relative tuple preserves distinctness. -/
theorem orderedFamilyReindex_mem_configuration {m n : ℕ} (ρ : Fin m → Fin n)
    (hρ : Function.Injective ρ) (x : (orderedFamilyPowerOver f n).left)
    (hx : x ∈ orderedFamilyConfigurationOpen f n) :
    Over.Hom.left (orderedFamilyReindex f ρ) x ∈ orderedFamilyConfigurationOpen f m := by
  let P := orderedFamilyPowerOver f n
  let K : Type u := P.left.residueField x
  let r : Spec (.of K) ⟶ P.left := P.left.fromSpecResidueField x
  let b : Spec (.of K) ⟶ S := r ≫ P.hom
  let a : Over.mk b ⟶ orderedFamilyPowerOver f n := Over.homMk r rfl
  have hr : r (IsLocalRing.closedPoint K) = x := Scheme.fromSpecResidueField_apply _ _
  have ha : Over.Hom.left a (IsLocalRing.closedPoint K) ∈
      orderedFamilyConfigurationOpen f n := by
    change r (IsLocalRing.closedPoint K) ∈ orderedFamilyConfigurationOpen f n
    rw [hr]
    exact hx
  have hc := (fieldTuple_mem_configuration_iff f n b a).mp ha
  have hm : Over.Hom.left (a ≫ orderedFamilyReindex f ρ)
      (IsLocalRing.closedPoint K) ∈ orderedFamilyConfigurationOpen f m := by
    apply (fieldTuple_mem_configuration_iff f m b (a ≫ orderedFamilyReindex f ρ)).mpr
    intro i j hij
    rw [Category.assoc, orderedFamilyReindex_coordinate,
      Category.assoc, orderedFamilyReindex_coordinate]
    exact hc (ρ i) (ρ j) (fun h ↦ hij (hρ h))
  have hv : Over.Hom.left (a ≫ orderedFamilyReindex f ρ)
      (IsLocalRing.closedPoint K) =
        Over.Hom.left (orderedFamilyReindex f ρ) x := by
    change Over.Hom.left (orderedFamilyReindex f ρ)
      (r (IsLocalRing.closedPoint K)) = Over.Hom.left (orderedFamilyReindex f ρ) x
    exact congrArg (Over.Hom.left (orderedFamilyReindex f ρ)) hr
  rwa [hv] at hm

/-- The morphism of actual configuration schemes induced by an injective
choice of coordinates. -/
noncomputable def orderedFamilyConfigurationReindex {m n : ℕ} (ρ : Fin m → Fin n)
    (hρ : Function.Injective ρ) :
    orderedFamilyConfigurationOver f n ⟶ orderedFamilyConfigurationOver f m := by
  let g := (orderedFamilyConfigurationOpen f n).ι ≫ Over.Hom.left (orderedFamilyReindex f ρ)
  have hg : Set.range g ⊆ Set.range (orderedFamilyConfigurationOpen f m).ι := by
    rw [(orderedFamilyConfigurationOpen f m).range_ι]
    rintro _ ⟨x, rfl⟩
    exact orderedFamilyReindex_mem_configuration f ρ hρ x.1 x.2
  let l := IsOpenImmersion.lift (orderedFamilyConfigurationOpen f m).ι g hg
  have hl : l ≫ (orderedFamilyConfigurationOpen f m).ι = g := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk l ?_
  change l ≫ ((orderedFamilyConfigurationOpen f m).ι ≫ (orderedFamilyPowerOver f m).hom) =
    (orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom
  rw [← Category.assoc, hl]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ (orderedFamilyConfigurationOpen f n).ι ≫ z)
      (Over.w (orderedFamilyReindex f ρ)))

/-- The restricted coordinate map is exactly the original reindexing after
inclusion into the ordered powers. -/
theorem orderedFamilyConfigurationReindex_ι {m n : ℕ} (ρ : Fin m → Fin n)
    (hρ : Function.Injective ρ) :
    Over.Hom.left (orderedFamilyConfigurationReindex f ρ hρ) ≫
      (orderedFamilyConfigurationOpen f m).ι =
        (orderedFamilyConfigurationOpen f n).ι ≫ Over.Hom.left (orderedFamilyReindex f ρ) :=
  by
    change IsOpenImmersion.lift (orderedFamilyConfigurationOpen f m).ι
      ((orderedFamilyConfigurationOpen f n).ι ≫ Over.Hom.left (orderedFamilyReindex f ρ)) _ ≫
        (orderedFamilyConfigurationOpen f m).ι =
      (orderedFamilyConfigurationOpen f n).ι ≫ Over.Hom.left (orderedFamilyReindex f ρ)
    exact IsOpenImmersion.lift_fac _ _ _

end AllCharacteristics
