import PfaffianDescent.GrassmannianQuotientOpenCover
import PfaffianDescent.GrassmannianChartPullbackCompatibility

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}
  (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n)

noncomputable def grassmannianQuotientChartMorphism (p : PrimeSpectrum A) :
    (grassmannianQuotientOpenCover W).X p ⟶ grassmannianScheme K m n :=
  (grassmannianChartAlgebraPoint K
    (Localization.Away (grassmannianBasicChartAt W p).denominator) m n
    (grassmannianBasicChartAt W p).permutation (grassmannianBasicChartAt W p).matrix).1

lemma grassmannianQuotientChartMorphism_overlap (p q : PrimeSpectrum A) :
    pullback.fst ((grassmannianQuotientOpenCover W).f p) ((grassmannianQuotientOpenCover W).f q) ≫
      grassmannianQuotientChartMorphism K W p =
    pullback.snd ((grassmannianQuotientOpenCover W).f p) ((grassmannianQuotientOpenCover W).f q) ≫
      grassmannianQuotientChartMorphism K W q := by
  exact grassmannianChart_morphism_eq_of_baseChange K
    (IsScalarTower.toAlgHom K A (Localization.Away (grassmannianBasicChartAt W p).denominator))
    (IsScalarTower.toAlgHom K A (Localization.Away (grassmannianBasicChartAt W q).denominator))
    W.toSubmodule _ _ _ _ (grassmannianBasicChartAt W p).submodule_eq
      (grassmannianBasicChartAt W q).submodule_eq _ _ _ (pullback.condition)

/-- The global Grassmannian morphism classified by a finite projective quotient over any affine base. -/
noncomputable def grassmannianQuotientMorphism : Spec (.of A) ⟶ grassmannianScheme K m n :=
  (grassmannianQuotientOpenCover W).glueMorphisms
    (grassmannianQuotientChartMorphism K W) (grassmannianQuotientChartMorphism_overlap K W)

lemma grassmannianQuotientMorphism_onCover (p : PrimeSpectrum A) :
    (grassmannianQuotientOpenCover W).f p ≫ grassmannianQuotientMorphism K W =
      grassmannianQuotientChartMorphism K W p :=
  (grassmannianQuotientOpenCover W).ι_glueMorphisms
    (grassmannianQuotientChartMorphism K W) (grassmannianQuotientChartMorphism_overlap K W) p

lemma grassmannianQuotientMorphism_toBase :
    grassmannianQuotientMorphism K W ≫ grassmannianToBase K m n =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  apply (grassmannianQuotientOpenCover W).hom_ext
  intro p
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫ grassmannianToBase K m n)
    (grassmannianQuotientMorphism_onCover K W p)).trans ?_
  change (grassmannianChartAlgebraPoint K
    (Localization.Away (grassmannianBasicChartAt W p).denominator) m n
    (grassmannianBasicChartAt W p).permutation (grassmannianBasicChartAt W p).matrix).1 ≫
      grassmannianToBase K m n =
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (grassmannianBasicChartAt W p).denominator))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A))
  rw [(grassmannianChartAlgebraPoint K _ m n _ _).2, ← Spec.map_comp]
  congr 1

/-- Classification of a quotient as an actual scheme-valued point over the coefficient algebra. -/
noncomputable def grassmannianQuotientAlgebraPoint : GrassmannianAlgebraPoint K A m n :=
  ⟨grassmannianQuotientMorphism K W, grassmannianQuotientMorphism_toBase K W⟩

lemma grassmannianQuotientMorphism_eq_chart
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A)
    (hW : W.toSubmodule = grassmannianChartSubmodule A σ T) :
    grassmannianQuotientMorphism K W = (grassmannianChartAlgebraPoint K A m n σ T).1 := by
  apply (grassmannianQuotientOpenCover W).hom_ext
  intro p
  refine (grassmannianQuotientMorphism_onCover K W p).trans ?_
  have h := grassmannianChart_morphism_eq_of_baseChange K
    (IsScalarTower.toAlgHom K A (Localization.Away (grassmannianBasicChartAt W p).denominator))
    (AlgHom.id K A) W.toSubmodule (grassmannianBasicChartAt W p).permutation σ
    (grassmannianBasicChartAt W p).matrix T (grassmannianBasicChartAt W p).submodule_eq
    (by
      change grassmannianSubmoduleBaseChange (RingHom.id A) W.toSubmodule = _
      rw [grassmannianSubmoduleBaseChange_id]
      exact hW)
    ((grassmannianQuotientOpenCover W).X p) (𝟙 _) ((grassmannianQuotientOpenCover W).f p)
    (by
      change (𝟙 _) ≫ (grassmannianQuotientOpenCover W).f p =
        (grassmannianQuotientOpenCover W).f p ≫ Spec.map (𝟙 (CommRingCat.of A))
      rw [Spec.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact (Category.id_comp (grassmannianQuotientChartMorphism K W p)).symm.trans h

lemma grassmannianQuotientAlgebraPoint_chart
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A) :
    grassmannianQuotientAlgebraPoint K (grassmannianChartQuotient A σ T) =
      grassmannianChartAlgebraPoint K A m n σ T := by
  apply Subtype.ext
  exact grassmannianQuotientMorphism_eq_chart K _ σ T rfl

end
end PfaffianDescent
