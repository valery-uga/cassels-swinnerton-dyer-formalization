import AllCharacteristics.RelativeConfigurationReindex

/-!
# Permutations of actual configuration spaces

The inclusion of the configuration open is a monomorphism over the base.
Injective reindexings respect identities and composition, and permutations
therefore induce actual isomorphisms of the configuration scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- The actual open inclusion, regarded as a morphism over the original base. -/
noncomputable def orderedFamilyConfigurationι (n : ℕ) :
    orderedFamilyConfigurationOver f n ⟶ orderedFamilyPowerOver f n :=
  Over.homMk (orderedFamilyConfigurationOpen f n).ι rfl

/-- Inclusion of the configuration open is a monomorphism over the base. -/
instance mono_orderedFamilyConfigurationι (n : ℕ) : Mono (orderedFamilyConfigurationι f n) := by
  have : Mono (Over.Hom.left (orderedFamilyConfigurationι f n)) := by
    change Mono (orderedFamilyConfigurationOpen f n).ι
    infer_instance
  exact Over.mono_of_mono_left (orderedFamilyConfigurationι f n)

/-- Configuration reindexing is exactly the restriction of ordered-power reindexing. -/
theorem orderedFamilyConfigurationReindex_toPower {m n : ℕ} (ρ : Fin m → Fin n)
    (hρ : Function.Injective ρ) :
    orderedFamilyConfigurationReindex f ρ hρ ≫ orderedFamilyConfigurationι f m =
      orderedFamilyConfigurationι f n ≫ orderedFamilyReindex f ρ := by
  apply Over.OverMorphism.ext
  exact orderedFamilyConfigurationReindex_ι f ρ hρ

/-- The coordinates of an actual configuration reindexing are the selected
coordinates of the original configuration. -/
theorem orderedFamilyConfigurationReindex_coordinate {m n : ℕ} (ρ : Fin m → Fin n)
    (hρ : Function.Injective ρ) (i : Fin m) :
    Over.Hom.left (orderedFamilyConfigurationReindex f ρ hρ) ≫
        Over.Hom.left (orderedFamilyConfigurationι f m) ≫
        (orderedFamilyCoordinate f m i).left =
      Over.Hom.left (orderedFamilyConfigurationι f n) ≫
        (orderedFamilyCoordinate f n (ρ i)).left := by
  calc
    Over.Hom.left (orderedFamilyConfigurationReindex f ρ hρ) ≫
        Over.Hom.left (orderedFamilyConfigurationι f m) ≫
        (orderedFamilyCoordinate f m i).left =
      Over.Hom.left (orderedFamilyConfigurationReindex f ρ hρ ≫
        orderedFamilyConfigurationι f m) ≫
        (orderedFamilyCoordinate f m i).left := by
          rw [Over.comp_left, Category.assoc]
    _ = Over.Hom.left (orderedFamilyConfigurationι f n ≫
        orderedFamilyReindex f ρ) ≫
        (orderedFamilyCoordinate f m i).left := by
          rw [orderedFamilyConfigurationReindex_toPower]
    _ = Over.Hom.left (orderedFamilyConfigurationι f n) ≫
        (orderedFamilyCoordinate f n (ρ i)).left := by
          rw [Over.comp_left, Category.assoc]
          congr 1
          exact congrArg Over.Hom.left (orderedFamilyReindex_coordinate f ρ i)

/-- Forget the `i`th marked point of an actual ordered configuration. -/
noncomputable def orderedFamilyConfigurationDelete (n : ℕ) (i : Fin (n + 1)) :
    orderedFamilyConfigurationOver f (n + 1) ⟶ orderedFamilyConfigurationOver f n :=
  orderedFamilyConfigurationReindex f i.succAbove Fin.succAbove_right_injective

/-- After deleting one marked point, the remaining coordinate `j` is the
original coordinate selected by `i.succAbove j`. -/
theorem orderedFamilyConfigurationDelete_coordinate (n : ℕ) (i : Fin (n + 1))
    (j : Fin n) :
    Over.Hom.left (orderedFamilyConfigurationDelete f n i) ≫
        Over.Hom.left (orderedFamilyConfigurationι f n) ≫
        (orderedFamilyCoordinate f n j).left =
      Over.Hom.left (orderedFamilyConfigurationι f (n + 1)) ≫
        (orderedFamilyCoordinate f (n + 1) (i.succAbove j)).left := by
  exact orderedFamilyConfigurationReindex_coordinate f i.succAbove
    Fin.succAbove_right_injective j

/-- Identity coordinate reindexing is the identity on the actual configuration scheme. -/
theorem orderedFamilyConfigurationReindex_id (n : ℕ) :
    orderedFamilyConfigurationReindex f (id : Fin n → Fin n) Function.injective_id =
      𝟙 (orderedFamilyConfigurationOver f n) := by
  apply (cancel_mono (orderedFamilyConfigurationι f n)).mp
  rw [orderedFamilyConfigurationReindex_toPower, orderedFamilyReindex_id,
    Category.comp_id, Category.id_comp]

/-- Coordinate reindexing composes on configuration spaces exactly as on ordered powers. -/
theorem orderedFamilyConfigurationReindex_comp {l m n : ℕ}
    (ρ : Fin m → Fin n) (τ : Fin l → Fin m)
    (hρ : Function.Injective ρ) (hτ : Function.Injective τ) :
    orderedFamilyConfigurationReindex f ρ hρ ≫ orderedFamilyConfigurationReindex f τ hτ =
      orderedFamilyConfigurationReindex f (ρ ∘ τ) (hρ.comp hτ) := by
  apply (cancel_mono (orderedFamilyConfigurationι f l)).mp
  rw [Category.assoc, orderedFamilyConfigurationReindex_toPower,
    ← Category.assoc, orderedFamilyConfigurationReindex_toPower, Category.assoc,
    orderedFamilyReindex_comp, orderedFamilyConfigurationReindex_toPower]

/-- Every permutation gives an actual isomorphism of the distinct-point scheme over the base. -/
noncomputable def orderedFamilyConfigurationPermutationIso (n : ℕ) (e : Equiv.Perm (Fin n)) :
    orderedFamilyConfigurationOver f n ≅ orderedFamilyConfigurationOver f n where
  hom := orderedFamilyConfigurationReindex f e e.injective
  inv := orderedFamilyConfigurationReindex f e.symm e.symm.injective
  hom_inv_id := by
    rw [orderedFamilyConfigurationReindex_comp]
    have he : (e : Fin n → Fin n) ∘ e.symm = id := funext e.apply_symm_apply
    simpa only [he] using orderedFamilyConfigurationReindex_id f n
  inv_hom_id := by
    rw [orderedFamilyConfigurationReindex_comp]
    have he : (e.symm : Fin n → Fin n) ∘ e = id := funext e.symm_apply_apply
    simpa only [he] using orderedFamilyConfigurationReindex_id f n

end AllCharacteristics
