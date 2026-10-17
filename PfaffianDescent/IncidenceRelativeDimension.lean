import PfaffianDescent.PolynomialRelativeDimension
import PfaffianDescent.IncidenceChartProduct
import PfaffianDescent.IncidenceGraphProjection

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

lemma grassmannianChartToBase_relativeDimension (m n : ℕ) :
    SmoothOfRelativeDimension (n * m) (grassmannianChartToBase K m n) := by
  change SmoothOfRelativeDimension (n * m)
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n × Fin m) K))))
  have hs := polynomial_smooth_relative_dimension K (Fin n × Fin m)
  simpa only [Nat.card_prod, Nat.card_fin] using hs

/-- The global Grassmannian is smooth of relative dimension `m*n`. -/
instance grassmannianToBase_relativeDimension (m n : ℕ) :
    SmoothOfRelativeDimension (n * m) (grassmannianToBase K m n) := by
  let 𝒰 := (grassmannianGlueData K m n).openCover
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    inferInstanceAs (IsAffine (Spec (.of (GrassmannianChartRing K m n))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension (n * m)) 𝒰
  intro i
  have hs : SmoothOfRelativeDimension (n * m) (𝒰.f i ≫ grassmannianToBase K m n) := by
    change SmoothOfRelativeDimension (n * m) (grassmannianChartι K i.down ≫ grassmannianToBase K m n)
    rw [grassmannianChartι_toBase]
    exact grassmannianChartToBase_relativeDimension K m n
  exact HasRingHomProperty.appTop _ _ hs

lemma incidenceGraphToBase_relativeDimension : SmoothOfRelativeDimension 45 (incidenceGraphToBase K) := by
  change SmoothOfRelativeDimension 45
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial IncidenceGraphIndex K))))
  have hs := polynomial_smooth_relative_dimension K IncidenceGraphIndex
  have hc : Nat.card IncidenceGraphIndex = 45 := by
    rw [Nat.card_eq_fintype_card, incidenceGraphIndex_card]
  simpa only [hc] using hs

/-- The actual global incidence scheme is smooth of relative dimension forty-five over the base. -/
instance incidenceToBase_relativeDimension : SmoothOfRelativeDimension 45 (incidenceToBase K) := by
  let 𝒰 := (incidenceGlueData K).openCover
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec (.of (IncidenceGraphRing K))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 45) 𝒰
  intro i
  have hs : SmoothOfRelativeDimension 45 (𝒰.f i ≫ incidenceToBase K) := by
    change SmoothOfRelativeDimension 45 (incidenceChartι K i.down ≫ incidenceToBase K)
    rw [incidenceChartι_toBase]
    exact incidenceGraphToBase_relativeDimension K
  exact HasRingHomProperty.appTop _ _ hs

instance alternatingTripleToBase_relativeDimension :
    SmoothOfRelativeDimension 45 (alternatingTripleToBase K) := by
  change SmoothOfRelativeDimension 45
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial AlternatingTripleIndex K))))
  have hs := polynomial_smooth_relative_dimension K AlternatingTripleIndex
  have hc : Nat.card AlternatingTripleIndex = 45 := by
    rw [Nat.card_eq_fintype_card, alternatingTripleIndex_card]
  simpa only [hc] using hs

lemma incidenceGraphToGrassmannianChart_relativeDimension :
    SmoothOfRelativeDimension 36 (incidenceGraphToGrassmannianChart K) := by
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (GrassmannianChartRing K 3 3)
      (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3))))
  have hc : Nat.card IncidenceFiberIndex = 36 := by
    rw [Nat.card_eq_fintype_card, incidenceFiberIndex_card]
  haveI : SmoothOfRelativeDimension 36 q := by
    simpa only [hc] using polynomial_smooth_relative_dimension (GrassmannianChartRing K 3 3) IncidenceFiberIndex
  have hs : SmoothOfRelativeDimension (0 + 36) ((incidenceChartProductIso K).hom ≫ q) :=
    smoothOfRelativeDimension_comp 0 36 (incidenceChartProductIso K).hom q
  change SmoothOfRelativeDimension (0 + 36) ((incidenceChartProductIso K).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (GrassmannianChartRing K 3 3)
        (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3))))) at hs
  rw [incidenceChartProductIso_toGrassmannian] at hs
  exact hs

/-- The vector-bundle projection has relative dimension thirty-six. -/
instance incidenceToGrassmannian_relativeDimension :
    SmoothOfRelativeDimension 36 (incidenceToGrassmannian K) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 36) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 36))
  let 𝒰 := (incidenceGlueData K).openCover
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 36) 𝒰
  intro i
  change SmoothOfRelativeDimension 36 (incidenceChartι K i.down ≫ incidenceToGrassmannian K)
  rw [incidenceChartι_toGrassmannian]
  haveI := incidenceGraphToGrassmannianChart_relativeDimension K
  have hs : SmoothOfRelativeDimension (36 + 0)
      (incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i.down) :=
    smoothOfRelativeDimension_comp 36 0 (incidenceGraphToGrassmannianChart K) (grassmannianChartι K i.down)
  exact hs

end
end PfaffianDescent
