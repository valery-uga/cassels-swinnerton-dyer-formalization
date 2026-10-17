import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace PfaffianDescent
variable {X : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
variable (j : ∀ i, Z i ⟶ X) [∀ i, Mono (j i)]
variable [∀ i k, IsOpenImmersion (pullback.fst (j i) (j k))]

def monoFamilyTransition (x y z : ι) :
    pullback (pullback.fst (j x) (j y)) (pullback.fst (j x) (j z)) ⟶
      pullback (pullback.fst (j y) (j z)) (pullback.fst (j y) (j x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem monoFamilyTransition_fst_fst (x y z : ι) :
    monoFamilyTransition j x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta monoFamilyTransition; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem monoFamilyTransition_fst_snd (x y z : ι) :
    monoFamilyTransition j x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta monoFamilyTransition; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem monoFamilyTransition_snd_fst (x y z : ι) :
    monoFamilyTransition j x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta monoFamilyTransition; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem monoFamilyTransition_snd_snd (x y z : ι) :
    monoFamilyTransition j x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta monoFamilyTransition; simp

theorem monoFamilyCocycle_fst (x y z : ι) :
    monoFamilyTransition j x y z ≫ monoFamilyTransition j y z x ≫ monoFamilyTransition j z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

theorem monoFamilyCocycle_snd (x y z : ι) :
    monoFamilyTransition j x y z ≫ monoFamilyTransition j y z x ≫ monoFamilyTransition j z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

theorem monoFamilyCocycle (x y z : ι) :
    monoFamilyTransition j x y z ≫ monoFamilyTransition j y z x ≫ monoFamilyTransition j z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply monoFamilyCocycle_fst
  · apply monoFamilyCocycle_snd

/-- Canonical glue data for a family of monomorphisms with open pairwise overlaps. -/
@[simps]
def monoFamilyGlueData : Scheme.GlueData.{u} where
  J := ι
  U := Z
  V := fun ⟨x, y⟩ => pullback (j x) (j y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := monoFamilyTransition j x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := monoFamilyCocycle j x y z
  f_open _ _ := inferInstance


/-- The glued local schemes map to their original common ambient scheme. -/
def monoFamilyToBase : (monoFamilyGlueData j).glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact j
  rintro ⟨i, k⟩
  change pullback.fst (j i) (j k) ≫ j i =
    ((pullbackSymmetry (j i) (j k)).hom ≫ pullback.fst (j k) (j i)) ≫ j k
  simpa using (pullback.condition (f := j i) (g := j k))

@[reassoc (attr := simp)]
theorem monoFamily_ι_toBase (i : ι) :
    (monoFamilyGlueData j).ι i ≫ monoFamilyToBase j = j i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- No points outside the original local closed schemes are introduced. -/
theorem monoFamilyToBase_injective : Function.Injective (monoFamilyToBase j) := by
  intro x y h
  obtain ⟨i, x, rfl⟩ : ∃ (i : ι) (z : Z i),
      (monoFamilyGlueData j).ι i z = x := (monoFamilyGlueData j).ι_jointly_surjective x
  obtain ⟨k, y, rfl⟩ : ∃ (k : ι) (z : Z k),
      (monoFamilyGlueData j).ι k z = y := (monoFamilyGlueData j).ι_jointly_surjective y
  have hx : monoFamilyToBase j ((monoFamilyGlueData j).ι i x) = j i x :=
    congrArg (fun l : Z i ⟶ X => l x) (monoFamily_ι_toBase j i)
  have hy : monoFamilyToBase j ((monoFamilyGlueData j).ι k y) = j k y :=
    congrArg (fun l : Z k ⟶ X => l y) (monoFamily_ι_toBase j k)
  obtain ⟨w, hwx, hwy⟩ := Scheme.Pullback.exists_preimage_pullback x y
    (hx.symm.trans (h.trans hy))
  apply ((monoFamilyGlueData j).ι_eq_iff i k x y).mpr
  refine ⟨w, hwx, ?_⟩
  change ((pullbackSymmetry (j i) (j k)).hom ≫ pullback.fst (j k) (j i)) w = y
  simpa using hwy

end PfaffianDescent
end
