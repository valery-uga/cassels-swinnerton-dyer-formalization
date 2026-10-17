import PfaffianDescent.CompatibleClosedSubschemeOverlap
import PfaffianDescent.MonoFamilySchemeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Basic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace PfaffianDescent

/-- The actual local inclusion composite, with all dependent parameters
explicit. This is an abbreviation of the original native map, not new data. -/
private abbrev closedFamilyLocalToBase007
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
    (I : ∀ i : 𝒰.I₀, (𝒰.X i).IdealSheafData) :
    ∀ i : 𝒰.I₀, (I i).subscheme ⟶ X :=
  fun i => (I i).subschemeι ≫ 𝒰.f i

/-- The original cover index has its explicit native glued-chart open
immersion. No saturation or additional openness certificate is a premise. -/
private instance closedFamily_gluedChartOpen010
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
    (I : ∀ i : 𝒰.I₀, (𝒰.X i).IdealSheafData)
    [∀ (i k : 𝒰.I₀), IsOpenImmersion
      (pullback.fst (closedFamilyLocalToBase007 𝒰 I i) (closedFamilyLocalToBase007 𝒰 I k))]
    (i : 𝒰.I₀) :
    IsOpenImmersion ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i) :=
  Scheme.GlueData.ι_isOpenImmersion (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)) i

section Construction
variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
variable (I : ∀ i : 𝒰.I₀, (𝒰.X i).IdealSheafData)
variable [∀ (i k : 𝒰.I₀), IsOpenImmersion (pullback.fst ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k))]
variable (hsat : ∀ (i k : 𝒰.I₀),
  Set.range (pullback.snd ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k)) = ((closedFamilyLocalToBase007 𝒰 I) k) ⁻¹' Set.range (𝒰.f i))
include hsat

/-- The chart of the glued scheme occupies exactly the preimage of its
original ambient chart. Saturation is obtained from the whole overlap ideals. -/
theorem closedFamily_gluedChart_range (i : 𝒰.I₀) :
    Set.range ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i) =
      Set.range (pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)) := by
  have hr : Set.range ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i) =
      monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I) ⁻¹' Set.range (𝒰.f i) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(I i).subschemeι z, ?_⟩
      have hv : monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I) ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i z) = (closedFamilyLocalToBase007 𝒰 I) i z :=
        congrArg (fun l : (I i).subscheme ⟶ X => l z) (monoFamily_ι_toBase (closedFamilyLocalToBase007 𝒰 I) i)
      exact hv.symm
    · intro hy
      obtain ⟨k, z, rfl⟩ : ∃ (k : 𝒰.I₀) (z : (I k).subscheme),
          (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι k z = y :=
        (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι_jointly_surjective y
      have hv : monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I) ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι k z) = (closedFamilyLocalToBase007 𝒰 I) k z :=
        congrArg (fun l : (I k).subscheme ⟶ X => l z) (monoFamily_ι_toBase (closedFamilyLocalToBase007 𝒰 I) k)
      have hz : (closedFamilyLocalToBase007 𝒰 I) k z ∈ Set.range (𝒰.f i) := hv ▸ hy
      change z ∈ (closedFamilyLocalToBase007 𝒰 I k) ⁻¹' Set.range (𝒰.f i) at hz
      rw [← hsat i k] at hz
      obtain ⟨w, hw⟩ := hz
      refine ⟨pullback.fst ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w, ?_⟩
      have he : (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i (pullback.fst ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w) =
          (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι k (pullback.snd ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w) := by
        apply ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι_eq_iff i k
          (pullback.fst ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w) (pullback.snd ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w)).mpr
        refine ⟨w, rfl, ?_⟩
        change ((pullbackSymmetry ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k)).hom ≫ pullback.fst ((closedFamilyLocalToBase007 𝒰 I) k) ((closedFamilyLocalToBase007 𝒰 I) i)) w =
          pullback.snd ((closedFamilyLocalToBase007 𝒰 I) i) ((closedFamilyLocalToBase007 𝒰 I) k) w
        simp
      exact he.trans (congrArg ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι k) hw)
  exact hr.trans (Scheme.Pullback.range_fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)).symm

omit hsat in
/-- The local closed scheme is the actual restriction of the glued scheme,
not merely an abstract isomorphic family. -/
def closedFamily_gluedChartIso
    (hsat' : ∀ (i k : 𝒰.I₀),
      Set.range (pullback.snd (closedFamilyLocalToBase007 𝒰 I i) (closedFamilyLocalToBase007 𝒰 I k)) =
        (closedFamilyLocalToBase007 𝒰 I k) ⁻¹' Set.range (𝒰.f i))
    (i : 𝒰.I₀) :
    (I i).subscheme ≅ pullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) := by
  exact @IsOpenImmersion.isoOfRangeEq
    ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).U i)
    (pullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
    (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).glued
    ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i)
    (pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
    (closedFamily_gluedChartOpen010 𝒰 I i)
    (MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)).flip
      (𝒰.map_prop i))
    (closedFamily_gluedChart_range 𝒰 I hsat' i)

@[reassoc (attr := simp)]
theorem closedFamily_gluedChartIso_hom_fst (i : 𝒰.I₀) :
    (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫
      pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) = (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i := by
  dsimp only [closedFamily_gluedChartIso]
  exact @IsOpenImmersion.isoOfRangeEq_hom_fac
    ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).U i)
    (pullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
    (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).glued
    ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i)
    (pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
    (closedFamily_gluedChartOpen010 𝒰 I i)
    (MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)).flip
      (𝒰.map_prop i))
    (closedFamily_gluedChart_range 𝒰 I hsat i)

@[reassoc (attr := simp)]
theorem closedFamily_gluedChartIso_hom_snd (i : 𝒰.I₀) :
    (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫
      pullback.snd (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) = (I i).subschemeι := by
  apply (cancel_mono (𝒰.f i)).mp
  have hcondition :
      (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫
        pullback.snd (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) ≫ 𝒰.f i =
      (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫
        pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) ≫
          monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I) :=
    congrArg (fun l : pullback (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) ⟶ X =>
      (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫ l)
      (pullback.condition (f := monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I))
        (g := 𝒰.f i)).symm
  have hchart :
      (closedFamily_gluedChartIso 𝒰 I hsat i).hom ≫
        pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) ≫
          monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I) =
      (I i).subschemeι ≫ 𝒰.f i :=
    (Category.assoc (closedFamily_gluedChartIso 𝒰 I hsat i).hom
      (pullback.fst (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
      (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I))).symm.trans
      ((congrArg (fun l : (I i).subscheme ⟶
          (monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).glued =>
          l ≫ monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I))
        (closedFamily_gluedChartIso_hom_fst 𝒰 I hsat i)).trans
        (monoFamily_ι_toBase (closedFamilyLocalToBase007 𝒰 I) i))
  exact (Category.assoc (closedFamily_gluedChartIso 𝒰 I hsat i).hom
    (pullback.snd (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
    (𝒰.f i)).trans (hcondition.trans hchart)

/-- Closed immersion is derived by its native target-locality theorem. -/
theorem closedFamily_gluedMap_isClosedImmersion :
    IsClosedImmersion (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰
  intro i
  change IsClosedImmersion (pullback.snd (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i))
  have he : pullback.snd (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i) =
      (closedFamily_gluedChartIso 𝒰 I hsat i).inv ≫ (I i).subschemeι := by
    rw [← closedFamily_gluedChartIso_hom_snd 𝒰 I hsat i,
      Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- The whole ideal of the global closed immersion restricts to the given
whole local ideal on every original ambient chart. -/
theorem closedFamily_gluedMap_kernel_comap (i : 𝒰.I₀) :
    (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)).ker.comap (𝒰.f i) = I i := by
  letI : IsClosedImmersion (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) :=
    closedFamily_gluedMap_isClosedImmersion 𝒰 I hsat
  let e := closedFamily_gluedChartIso 𝒰 I hsat i ≪≫
    pullbackSymmetry (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)
  have he : e.hom ≫ pullback.fst (𝒰.f i) (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) =
      (I i).subschemeι := by
    simp [e]
  calc
    _ = (pullback.fst (𝒰.f i) (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I))).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = ((I i).subschemeι).ker := by
      rw [← he, Scheme.Hom.ker_comp_of_isIso]
    _ = I i := (I i).ker_subschemeι

/-- The actual local embedding square is Cartesian. -/
theorem closedFamily_gluedMap_isPullback (i : 𝒰.I₀) :
    IsPullback (I i).subschemeι ((monoFamilyGlueData (closedFamilyLocalToBase007 𝒰 I)).ι i)
      (𝒰.f i) (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) := by
  let e := closedFamily_gluedChartIso 𝒰 I hsat i ≪≫
    pullbackSymmetry (monoFamilyToBase (closedFamilyLocalToBase007 𝒰 I)) (𝒰.f i)
  apply IsPullback.of_iso_pullback
    ⟨(monoFamily_ι_toBase (closedFamilyLocalToBase007 𝒰 I) i).symm⟩ e
  · simp [e]
  · simp [e] <;> rfl

end Construction

/-- Ordinary equality of the two WHOLE ideals on the actual ambient
intersections constructs a global ideal sheaf. There is no gluing datum,
global scheme, global ideal, or conclusion certificate among the hypotheses. -/
theorem compatibleClosedSubschemes_openCover_exists_globalIdeal
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
    (I : ∀ i : 𝒰.I₀, (𝒰.X i).IdealSheafData)
    (h : ∀ i k, (I i).comap (pullback.fst (𝒰.f i) (𝒰.f k)) =
      (I k).comap (pullback.snd (𝒰.f i) (𝒰.f k))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (𝒰.f i) = I i := by
  let j := fun i => (I i).subschemeι ≫ 𝒰.f i
  letI (i k : 𝒰.I₀) : IsOpenImmersion (pullback.fst (j i) (j k)) :=
    compatibleClosedSubscheme_pullback_fst_isOpenImmersion
      (𝒰.f i) (𝒰.f k) (I i) (I k) (h i k)
  have hs : ∀ i k, Set.range (pullback.snd (j i) (j k)) =
      (j k) ⁻¹' Set.range (𝒰.f i) := fun i k =>
    compatibleClosedSubscheme_pullback_snd_range
      (𝒰.f i) (𝒰.f k) (I i) (I k) (h i k)
  exact ⟨(monoFamilyToBase j).ker, closedFamily_gluedMap_kernel_comap 𝒰 I hs⟩

/-- The stronger geometric endpoint retains each actual embedding in a
Cartesian square with the global closed immersion. -/
theorem compatibleClosedSubschemes_openCover_exists_globalClosedImmersion
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
    (I : ∀ i : 𝒰.I₀, (𝒰.X i).IdealSheafData)
    (h : ∀ i k, (I i).comap (pullback.fst (𝒰.f i) (𝒰.f k)) =
      (I k).comap (pullback.snd (𝒰.f i) (𝒰.f k))) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X), IsClosedImmersion f ∧
      ∃ (a : ∀ i, (I i).subscheme ⟶ Z),
        (∀ i, IsOpenImmersion (a i)) ∧
        (∀ i, IsPullback (I i).subschemeι (a i) (𝒰.f i) f) ∧
        (∀ i, f.ker.comap (𝒰.f i) = I i) := by
  let j := fun i => (I i).subschemeι ≫ 𝒰.f i
  letI (i k : 𝒰.I₀) : IsOpenImmersion (pullback.fst (j i) (j k)) :=
    compatibleClosedSubscheme_pullback_fst_isOpenImmersion
      (𝒰.f i) (𝒰.f k) (I i) (I k) (h i k)
  have hs : ∀ i k, Set.range (pullback.snd (j i) (j k)) =
      (j k) ⁻¹' Set.range (𝒰.f i) := fun i k =>
    compatibleClosedSubscheme_pullback_snd_range
      (𝒰.f i) (𝒰.f k) (I i) (I k) (h i k)
  refine ⟨(monoFamilyGlueData j).glued, monoFamilyToBase j,
    closedFamily_gluedMap_isClosedImmersion 𝒰 I hs,
    (monoFamilyGlueData j).ι, ?_,
    closedFamily_gluedMap_isPullback 𝒰 I hs,
    closedFamily_gluedMap_kernel_comap 𝒰 I hs⟩
  intro i
  exact Scheme.GlueData.ι_isOpenImmersion (monoFamilyGlueData j) i

end PfaffianDescent
end
