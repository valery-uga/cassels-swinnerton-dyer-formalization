import PfaffianDescent.GrassmannianLocalModuli
import Mathlib.AlgebraicGeometry.Cover.Open

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- An affine-source morphism locally factors through any open immersion containing its image point. -/
lemma scheme_morphism_basic_open_lift {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (f : Spec (.of A) ⟶ X) (p : PrimeSpectrum A)
    (hp : f p ∈ Set.range j) :
    ∃ a : A, a ∉ p.asIdeal ∧ ∃ g : Spec (.of (Localization.Away a)) ⟶ Y,
      g ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f := by
  have ho : IsOpen (f ⁻¹' Set.range j) := j.isOpenEmbedding.isOpen_range.preimage f.continuous
  obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp ho
  let l := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))
  have hr : Set.range (l ≫ f) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨x, rfl⟩
  exact ⟨a, ha, IsOpenImmersion.lift j (l ≫ f) hr, IsOpenImmersion.lift_fac _ _ hr⟩

section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- Every scheme-valued Grassmannian point is a graph on a basic neighborhood of each base prime. -/
theorem grassmannian_scheme_point_exists_basic_chart
    (f : GrassmannianAlgebraPoint K A m n) (p : PrimeSpectrum A) :
    ∃ a : A, a ∉ p.asIdeal ∧ ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
      (T : Matrix (Fin n) (Fin m) (Localization.Away a)),
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1 =
        (grassmannianChartAlgebraPoint K (Localization.Away a) m n σ T).1 := by
  obtain ⟨i, y, hy⟩ := (grassmannianGlueData K m n).openCover.exists_eq (f.1 p)
  let σ : Equiv.Perm (Fin m ⊕ Fin n) := i.down
  have hp : f.1 p ∈ Set.range (grassmannianChartι K σ) := ⟨y, hy⟩
  obtain ⟨a, ha, g, hg⟩ := scheme_morphism_basic_open_lift (grassmannianChartι K σ) f.1 p hp
  have hb : g ≫ grassmannianChartToBase K m n =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away a))) := by
    calc
      g ≫ grassmannianChartToBase K m n =
          (g ≫ grassmannianChartι K σ) ≫ grassmannianToBase K m n :=
        (congrArg (fun q => g ≫ q) (grassmannianChartι_toBase K σ).symm).trans
          (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1) ≫
          grassmannianToBase K m n := congrArg (fun q => q ≫ grassmannianToBase K m n) hg
      _ = _ := by
        rw [Category.assoc, f.2, ← Spec.map_comp]
        congr 1
  obtain ⟨T, hT⟩ := grassmannianChartEvaluation_exists K g hb
  exact ⟨a, ha, σ, T, hg.symm.trans (congrArg (fun q => q ≫ grassmannianChartι K σ) hT.symm)⟩

end
end PfaffianDescent
