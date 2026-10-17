import AllCharacteristics.RelativeConfigurationOpen
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The disjoint sections over an ordered configuration

Each coordinate of the original distinct-configuration scheme gives a closed
section of the pulled-back family. The section images are pairwise disjoint;
the proof uses the actual scheme-theoretic coordinate equalizers.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

/-- The section of the pulled-back family specified by an actual ordered coordinate. -/
noncomputable def orderedConfigurationSection (i : Fin n) :
    (orderedFamilyConfigurationOver f n).left ⟶
      pullback f (orderedFamilyConfigurationOver f n).hom :=
  pullback.lift ((orderedFamilyConfigurationOpen f n).ι ≫
    (orderedFamilyCoordinate f n i).left) (𝟙 _) (by
      change ((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left) ≫ f =
          𝟙 (orderedFamilyConfigurationOpen f n).toScheme ≫
            ((orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom)
      have hc : (orderedFamilyCoordinate f n i).left ≫ f = (orderedFamilyPowerOver f n).hom :=
        (orderedFamilyCoordinate f n i).w
      rw [Category.assoc, hc, Category.id_comp])

/-- The coordinate section retains its original map to the family. -/
lemma orderedConfigurationSection_fst (i : Fin n) :
    orderedConfigurationSection f n i ≫
      pullback.fst f (orderedFamilyConfigurationOver f n).hom =
        (orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyCoordinate f n i).left :=
  pullback.lift_fst _ _ _

/-- The coordinate map is a section over the original configuration scheme. -/
lemma orderedConfigurationSection_snd (i : Fin n) :
    orderedConfigurationSection f n i ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- A coordinate section is a closed immersion because the family is separated. -/
instance isClosedImmersion_orderedConfigurationSection (i : Fin n) :
    IsClosedImmersion (orderedConfigurationSection f n i) := by
  have : IsClosedImmersion (orderedConfigurationSection f n i ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom) := by
    rw [orderedConfigurationSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f (orderedFamilyConfigurationOver f n).hom)

/-- Different ordered coordinates give disjoint section images in the pulled-back family. -/
lemma disjoint_orderedConfigurationSection_ranges : Pairwise fun i j : Fin n =>
    Disjoint (Set.range (orderedConfigurationSection f n i))
      (Set.range (orderedConfigurationSection f n j)) := by
  intro i j hij
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  let si := orderedConfigurationSection f n i
  let sj := orderedConfigurationSection f n j
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := si) (g := sj) x y hxy
  let t := pullback.fst si sj
  let w : Over.mk (t ≫ (orderedFamilyConfigurationOver f n).hom) ⟶
      orderedFamilyPowerOver f n :=
    Over.homMk (t ≫ (orderedFamilyConfigurationOpen f n).ι) (by
      change (t ≫ (orderedFamilyConfigurationOpen f n).ι) ≫ (orderedFamilyPowerOver f n).hom =
        t ≫ ((orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom)
      exact Category.assoc _ _ _)
  have hc : w ≫ orderedFamilyCoordinate f n i = w ≫ orderedFamilyCoordinate f n j := by
    apply Over.OverMorphism.ext
    change (t ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
      (orderedFamilyCoordinate f n i).left = (t ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
      (orderedFamilyCoordinate f n j).left
    have he : pullback.fst si sj = pullback.snd si sj := by
      have hh := congrArg (fun a => a ≫ pullback.snd f (orderedFamilyConfigurationOver f n).hom)
        (pullback.condition (f := si) (g := sj))
      simpa only [si, sj, Category.assoc, orderedConfigurationSection_snd, Category.comp_id] using hh
    have hh := congrArg (fun a => a ≫ pullback.fst f (orderedFamilyConfigurationOver f n).hom)
      (pullback.condition (f := si) (g := sj))
    have hh' : t ≫ ((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left) =
          t ≫ ((orderedFamilyConfigurationOpen f n).ι ≫
            (orderedFamilyCoordinate f n j).left) := by
      dsimp only [si, sj] at hh
      rw [Category.assoc, orderedConfigurationSection_fst,
        Category.assoc, orderedConfigurationSection_fst] at hh
      have he' : pullback.fst (orderedConfigurationSection f n i) (orderedConfigurationSection f n j) =
          pullback.snd (orderedConfigurationSection f n i) (orderedConfigurationSection f n j) := he
      rw [← he'] at hh
      exact hh
    exact (Category.assoc _ _ _).trans (hh'.trans (Category.assoc _ _ _).symm)
  have hm := (mem_orderedFamilyConfigurationOpen_iff f n x.1).mp x.2 i j hij
  apply hm
  refine ⟨(equalizer.lift w hc).left z, ?_⟩
  have he := congrArg (fun a => a.left) (equalizer.lift_ι w hc)
  have he' := congrArg (fun a => a z) he
  change (equalizer.ι (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j)).left
    ((equalizer.lift w hc).left z) = x.1
  exact he'.trans (congrArg Subtype.val hz)

end AllCharacteristics
