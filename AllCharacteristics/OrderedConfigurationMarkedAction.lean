import AllCharacteristics.OrderedConfigurationSubscheme
import AllCharacteristics.RelativeAffineConfigurationQuotient
import AllCharacteristics.BaseChangedFamilyMap

/-! # Permutations of the actual marked configuration

The configuration permutation acts on the pulled-back family and on the marked source. Reindexing the mark by the inverse permutation preserves its chosen point, so the original union immersion is equivariant.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

noncomputable def orderedConfigurationFamilyRightAction (g : Equiv.Perm (Fin n)) :
    pullback f (orderedFamilyConfigurationOver f n).hom ⟶
      pullback f (orderedFamilyConfigurationOver f n).hom :=
  baseChangedFamilyMap f (orderedFamilyConfigurationOver f n).hom
    (orderedFamilyConfigurationOver f n).hom (configurationRightAction f n g)
    (configurationRightAction_toBase f n g)

lemma orderedConfigurationFamilyRightAction_fst (g : Equiv.Perm (Fin n)) :
    orderedConfigurationFamilyRightAction f n g ≫
      pullback.fst f (orderedFamilyConfigurationOver f n).hom =
        pullback.fst f (orderedFamilyConfigurationOver f n).hom :=
  baseChangedFamilyMap_fst _ _ _ _ _

lemma orderedConfigurationFamilyRightAction_snd (g : Equiv.Perm (Fin n)) :
    orderedConfigurationFamilyRightAction f n g ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom =
        pullback.snd f (orderedFamilyConfigurationOver f n).hom ≫ configurationRightAction f n g :=
  baseChangedFamilyMap_snd _ _ _ _ _

lemma orderedConfigurationFamilyRightAction_one :
    orderedConfigurationFamilyRightAction f n 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [orderedConfigurationFamilyRightAction_fst, Category.id_comp]
  · rw [orderedConfigurationFamilyRightAction_snd, configurationRightAction_one,
      Category.comp_id, Category.id_comp]

lemma configurationRightAction_coordinate (g : Equiv.Perm (Fin n)) (i : Fin n) :
    configurationRightAction f n g ≫ (orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n i).left =
        (orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyCoordinate f n (g i)).left := by
  let C := (orderedFamilyConfigurationOver f n).left
  let T := (orderedFamilyPowerOver f n).left
  let l : C ⟶ T := (orderedFamilyConfigurationOpen f n).ι
  let c (k : Fin n) : T ⟶ X := (orderedFamilyCoordinate f n k).left
  have hr : configurationRightAction f n g ≫ l = l ≫ orderedFamilyRightAction f n g :=
    configurationRightAction_ι f n g
  have hc : orderedFamilyRightAction f n g ≫ c i = c (g i) :=
    congrArg (fun a => a.left) (orderedFamilyReindex_coordinate f g i)
  change configurationRightAction f n g ≫ l ≫ c i = l ≫ c (g i)
  rw [← Category.assoc, hr, Category.assoc, hc]

lemma orderedConfigurationSection_rightAction (g : Equiv.Perm (Fin n)) (i : Fin n) :
    orderedConfigurationSection f n i ≫ orderedConfigurationFamilyRightAction f n g =
      configurationRightAction f n g ≫ orderedConfigurationSection f n (g.symm i) := by
  apply pullback.hom_ext
  · rw [Category.assoc, orderedConfigurationFamilyRightAction_fst, orderedConfigurationSection_fst,
      Category.assoc, orderedConfigurationSection_fst]
    have h := (configurationRightAction_coordinate f n g (g.symm i)).symm
    simp only [Equiv.apply_symm_apply] at h
    exact h
  · rw [Category.assoc, orderedConfigurationFamilyRightAction_snd, ← Category.assoc,
      orderedConfigurationSection_snd, Category.id_comp, Category.assoc,
      orderedConfigurationSection_snd, Category.comp_id]

noncomputable def orderedConfigurationMarkedRightAction (g : Equiv.Perm (Fin n)) :
    orderedConfigurationMarkedSource f n ⟶ orderedConfigurationMarkedSource f n :=
  Sigma.desc (fun i : ULift.{u} (Fin n) => configurationRightAction f n g ≫
    Sigma.ι (fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left) ⟨g.symm i.down⟩)

lemma orderedConfigurationMarkedRightAction_one :
    orderedConfigurationMarkedRightAction f n 1 = 𝟙 _ := by
  change Sigma.desc (fun i : ULift.{u} (Fin n) => configurationRightAction f n 1 ≫
    Sigma.ι (fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left) ⟨(Equiv.symm (1 : Equiv.Perm (Fin n))) i.down⟩) =
      𝟙 (∐ fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left)
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc, configurationRightAction_one, Category.id_comp, Category.comp_id]
  rfl

lemma orderedConfigurationMarkedRightAction_union (g : Equiv.Perm (Fin n)) :
    orderedConfigurationMarkedRightAction f n g ≫ orderedConfigurationUnionMap f n =
      orderedConfigurationUnionMap f n ≫ orderedConfigurationFamilyRightAction f n g := by
  let C := (orderedFamilyConfigurationOver f n).left
  let D := ∐ fun _ : ULift.{u} (Fin n) => C
  let F := pullback f (orderedFamilyConfigurationOver f n).hom
  let a : D ⟶ D := orderedConfigurationMarkedRightAction f n g
  let j : D ⟶ F := orderedConfigurationUnionMap f n
  change a ≫ j = j ≫ orderedConfigurationFamilyRightAction f n g
  apply Sigma.hom_ext
  intro i
  have ha : Sigma.ι (fun _ : ULift.{u} (Fin n) => C) i ≫ a =
      configurationRightAction f n g ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) => C) ⟨g.symm i.down⟩ :=
    Sigma.ι_desc _ i
  have hj (k : ULift.{u} (Fin n)) : Sigma.ι (fun _ : ULift.{u} (Fin n) => C) k ≫ j =
      orderedConfigurationSection f n k.down := Sigma.ι_desc _ k
  rw [← Category.assoc, ha, Category.assoc, hj, ← Category.assoc, hj]
  exact (orderedConfigurationSection_rightAction f n g i.down).symm

/-- A nonempty collection of marked points which is invariant under every
permutation of the labels contains every marked point.  This is the finite
combinatorial step behind the full-symmetric-Galois argument in Voisin's
Lemma 3.3: if a moving curve contains one of a generic set of marked points,
permutation invariance forces it to contain them all. -/
theorem set_eq_univ_of_nonempty_perm_invariant
    {α : Type u} (U : Set α)
    (hinvariant : ∀ g : Equiv.Perm α, g '' U = U)
    (hne : U.Nonempty) : U = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, hx⟩ := hne
  let g : Equiv.Perm α := Equiv.swap x y
  have hgy : g x ∈ g '' U := ⟨x, hx, rfl⟩
  rw [hinvariant g] at hgy
  simpa only [g, Equiv.swap_apply_left] using hgy

/-- Predicate form of `set_eq_univ_of_nonempty_perm_invariant`.  It is ready
to apply when `P i` means that the curve under consideration contains the
`i`-th marked point. -/
theorem forall_of_exists_perm_invariant
    {α : Type u} (P : α → Prop)
    (hinvariant : ∀ (g : Equiv.Perm α) (i : α), P i ↔ P (g i))
    (hexists : ∃ i, P i) : ∀ i, P i := by
  let U : Set α := {i | P i}
  have hUinvariant : ∀ g : Equiv.Perm α, g '' U = U := by
    intro g
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hinvariant g j).mp hj
    · intro hi
      refine ⟨g.symm i, ?_, g.apply_symm_apply i⟩
      apply (hinvariant g (g.symm i)).mpr
      change P i at hi
      simpa using hi
  have hU : U = Set.univ := set_eq_univ_of_nonempty_perm_invariant U hUinvariant hexists
  intro i
  have hi : i ∈ U := by
    rw [hU]
    exact Set.mem_univ i
  exact hi

end AllCharacteristics
