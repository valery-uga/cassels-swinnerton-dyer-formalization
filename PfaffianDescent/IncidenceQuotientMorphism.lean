import PfaffianDescent.IncidenceQuotientCharts
import PfaffianDescent.GrassmannianGlobalModuli
import PfaffianDescent.AmbientAlternatingKernelMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]
  (W : Module.Grassmannian A ((Fin 3 → A) × (Fin 3 → A)) 3)
  (B : IncidenceQuotientFiber A W)

noncomputable def incidenceQuotientChartMorphism (p : PrimeSpectrum A) :
    (grassmannianQuotientOpenCover W).X p ⟶ incidenceScheme K :=
  incidenceIsotropicChartMorphism K (grassmannianBasicChartAt W p).permutation
    (grassmannianBasicChartAt W p).matrix
    (fun k => ambientAlternatingMap
      (algebraMap A (Localization.Away (grassmannianBasicChartAt W p).denominator)) (B k).1)
    (fun k => by
      rw [← (grassmannianBasicChartAt W p).submodule_eq]
      exact ambientAlternatingMap_restriction_zero _ W.toSubmodule (B k).1 (B k).2)

lemma incidenceQuotientChartMorphism_toGrassmannian (p : PrimeSpectrum A) :
    incidenceQuotientChartMorphism K W B p ≫ incidenceToGrassmannian K =
      grassmannianQuotientChartMorphism K W p :=
  incidenceIsotropicChartMorphism_toGrassmannian K _ _ _ _

lemma incidenceQuotientChartMorphism_toTriples (p : PrimeSpectrum A) :
    incidenceQuotientChartMorphism K W B p ≫ incidenceToTriples K =
      (grassmannianQuotientOpenCover W).f p ≫ alternatingTripleEvaluation K (fun k => (B k).1) :=
  (incidenceIsotropicChartMorphism_toTriples K _ _ _ _).trans
    (alternatingTripleEvaluation_map K
      (IsScalarTower.toAlgHom K A (Localization.Away (grassmannianBasicChartAt W p).denominator))
      (fun k => (B k).1)).symm

lemma incidenceQuotientChartMorphism_overlap (p q : PrimeSpectrum A) :
    pullback.fst ((grassmannianQuotientOpenCover W).f p) ((grassmannianQuotientOpenCover W).f q) ≫
      incidenceQuotientChartMorphism K W B p =
    pullback.snd ((grassmannianQuotientOpenCover W).f p) ((grassmannianQuotientOpenCover W).f q) ≫
      incidenceQuotientChartMorphism K W B q := by
  apply incidence_hom_ext K
  · simp only [Category.assoc, incidenceQuotientChartMorphism_toGrassmannian]
    exact grassmannianQuotientChartMorphism_overlap K W p q
  · simp only [Category.assoc, incidenceQuotientChartMorphism_toTriples]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ alternatingTripleEvaluation K (fun k => (B k).1)) pullback.condition).trans
        (Category.assoc _ _ _))

/-- An actual quotient and three forms vanishing on its kernel define a global incidence point. -/
noncomputable def incidenceQuotientMorphism : Spec (.of A) ⟶ incidenceScheme K :=
  (grassmannianQuotientOpenCover W).glueMorphisms
    (incidenceQuotientChartMorphism K W B) (incidenceQuotientChartMorphism_overlap K W B)

lemma incidenceQuotientMorphism_onCover (p : PrimeSpectrum A) :
    (grassmannianQuotientOpenCover W).f p ≫ incidenceQuotientMorphism K W B =
      incidenceQuotientChartMorphism K W B p :=
  (grassmannianQuotientOpenCover W).ι_glueMorphisms
    (incidenceQuotientChartMorphism K W B) (incidenceQuotientChartMorphism_overlap K W B) p

lemma incidenceQuotientMorphism_toGrassmannian :
    incidenceQuotientMorphism K W B ≫ incidenceToGrassmannian K = grassmannianQuotientMorphism K W := by
  apply (grassmannianQuotientOpenCover W).hom_ext
  intro p
  rw [← Category.assoc]
  exact (congrArg (fun g => g ≫ incidenceToGrassmannian K)
    (incidenceQuotientMorphism_onCover K W B p)).trans
      ((incidenceQuotientChartMorphism_toGrassmannian K W B p).trans
        (grassmannianQuotientMorphism_onCover K W p).symm)

lemma incidenceQuotientMorphism_toTriples :
    incidenceQuotientMorphism K W B ≫ incidenceToTriples K =
      alternatingTripleEvaluation K (fun k => (B k).1) := by
  apply (grassmannianQuotientOpenCover W).hom_ext
  intro p
  rw [← Category.assoc]
  exact (congrArg (fun g => g ≫ incidenceToTriples K)
    (incidenceQuotientMorphism_onCover K W B p)).trans
      (incidenceQuotientChartMorphism_toTriples K W B p)

lemma incidenceQuotientMorphism_toBase :
    incidenceQuotientMorphism K W B ≫ incidenceToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  rw [← incidenceToTriples_toBase, ← Category.assoc, incidenceQuotientMorphism_toTriples]
  exact alternatingTripleEvaluation_toBase K _

end
section
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]

abbrev IncidenceAlgebraPoint :=
  {f : Spec (.of A) ⟶ incidenceScheme K //
    f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A))}

/-- The actual moduli of finite projective quotients with a common-isotropic triple. -/
abbrev IncidenceQuotientPoint :=
  (W : Module.Grassmannian A ((Fin 3 → A) × (Fin 3 → A)) 3) × IncidenceQuotientFiber A W

noncomputable def incidenceQuotientAlgebraPoint (p : IncidenceQuotientPoint A) : IncidenceAlgebraPoint K A :=
  ⟨incidenceQuotientMorphism K p.1 p.2, incidenceQuotientMorphism_toBase K p.1 p.2⟩

end
end PfaffianDescent
