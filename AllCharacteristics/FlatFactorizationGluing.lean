import Mathlib.AlgebraicGeometry.EffectiveEpi

/-!
# Gluing local factorizations through a faithfully flat scheme morphism

Local factorizations on an open cover of the quotient agree on overlaps because
the base changes of a flat surjection are epimorphisms. The glued morphism has
the prescribed composite with the original morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {X Y T : Scheme.{u}} (q : X ⟶ Y) [Flat q] [Surjective q]

/-- Local factorizations through the actual pullbacks of a flat surjection
glue uniquely on an arbitrary open cover of its target. -/
theorem existsUnique_factor_of_flat_openCover (a : X ⟶ T) (C : Y.OpenCover.{v})
    (h : ∀ i, ∃ b : C.X i ⟶ T,
      pullback.snd q (C.f i) ≫ b = pullback.fst q (C.f i) ≫ a) :
    ∃! b : Y ⟶ T, q ≫ b = a := by
  classical
  choose b hb using h
  have hcompat : ∀ i j,
      pullback.fst (C.f i) (C.f j) ≫ b i = pullback.snd (C.f i) (C.f j) ≫ b j := by
    intro i j
    let d := pullback.fst (C.f i) (C.f j) ≫ C.f i
    have hd : d = pullback.snd (C.f i) (C.f j) ≫ C.f j := pullback.condition
    have : Epi (pullback.snd q d) := Flat.epi_of_flat_of_surjective _
    let li : pullback q d ⟶ pullback q (C.f i) :=
      pullback.lift (pullback.fst q d)
        (pullback.snd q d ≫ pullback.fst (C.f i) (C.f j))
        (pullback.condition.trans (Category.assoc _ _ _).symm)
    let lj : pullback q d ⟶ pullback q (C.f j) :=
      pullback.lift (pullback.fst q d)
        (pullback.snd q d ≫ pullback.snd (C.f i) (C.f j))
        (pullback.condition.trans ((congrArg (fun z ↦ pullback.snd q d ≫ z) hd).trans
          (Category.assoc _ _ _).symm))
    apply (cancel_epi (pullback.snd q d)).mp
    have hi := congrArg (fun z ↦ li ≫ z) (hb i)
    have hj := congrArg (fun z ↦ lj ≫ z) (hb j)
    simp only [li, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
      Category.assoc] at hi
    simp only [lj, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
      Category.assoc] at hj
    exact hi.trans hj.symm
  let b' := C.glueMorphisms b hcompat
  have hb' : q ≫ b' = a := by
    apply Scheme.Cover.hom_ext (C.pullback₁ q)
    intro i
    change pullback.fst q (C.f i) ≫ (q ≫ b') = pullback.fst q (C.f i) ≫ a
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact (congrArg (fun z ↦ pullback.snd q (C.f i) ≫ z)
      (C.ι_glueMorphisms b hcompat i)).trans (hb i)
  have : Epi q := Flat.epi_of_flat_of_surjective q
  refine ⟨b', hb', ?_⟩
  intro c hc
  exact (cancel_epi q).mp (hc.trans hb'.symm)

/-- It suffices to construct factorizations on any open pullback square
around each point of the target of the original flat surjection. -/
theorem existsUnique_factor_of_flat_pullback_neighborhoods (a : X ⟶ T)
    (h : ∀ y : Y, ∃ (U V : Scheme.{u}) (i : U ⟶ X) (j : V ⟶ Y) (r : U ⟶ V),
      IsOpenImmersion j ∧ y ∈ Set.range j ∧ IsPullback i r q j ∧
        ∃ b : V ⟶ T, r ≫ b = i ≫ a) :
    ∃! b : Y ⟶ T, q ≫ b = a := by
  classical
  choose U V i j r hj hy hp b hb using h
  let C : Y.OpenCover := {
    I₀ := Y
    X := V
    f := j
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun y ↦ ⟨y, hy y⟩, hj⟩ }
  apply existsUnique_factor_of_flat_openCover q a C
  intro y
  change ∃ b' : V y ⟶ T, pullback.snd q (j y) ≫ b' = pullback.fst q (j y) ≫ a
  refine ⟨b y, ?_⟩
  rw [← (hp y).isoPullback_inv_snd, Category.assoc, hb,
    ← Category.assoc, (hp y).isoPullback_inv_fst]

end AllCharacteristics
