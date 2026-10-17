import PfaffianDescent.ProjectiveClosedPointCoordinates
import PfaffianDescent.HomogeneousQuotientMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Adding equations which vanish on the coordinates of a given chart point
factors the EXACT original closed immersion, including its coefficient map. -/
theorem closed_field_point_factor_through_homogeneous_quotient
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {σ : Type} [Finite σ]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (p : Spec (.of L) ⟶ scheme I) [IsClosedImmersion p]
    (hp : p ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (j : σ) (g : ChartRing I j →+* L)
    (hgbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (hgpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = p)
    (hJ : ∀ r ∈ J.toIdeal,
      r.eval₂ (algebraMap K L) (fun k => g (chartCoordinate I j k)) = 0) :
    ∃ r : Spec (.of L) ⟶ scheme J, IsClosedImmersion r ∧
      r ≫ schemeQuotientMap I J hIJ = p ∧
      r ≫ toBase J = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let x : σ → L := fun k => g (chartCoordinate I j k)
  have hx : x j = 1 := by
    dsimp only [x]
    rw [chartCoordinate_self, map_one]
  let gJ := normalizedPointChartMap J x j hx hJ
  have hgJ : gJ.comp (chartQuotientMap I J hIJ j) = g := by
    apply RingHom.ext
    intro a
    obtain ⟨r, rfl⟩ := eval₂_chartCoordinate_surjective I j a
    rw [RingHom.comp_apply]
    change gJ ((chartQuotientMap I J hIJ j)
        (r.eval₂ (chartBaseMap I j) (chartCoordinate I j))) =
      g (r.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [chartQuotientMap_eval₂ I J hIJ j r]
    change normalizedPointChartMap J x j hx hJ
      (r.eval₂ (chartBaseMap J j) (chartCoordinate J j)) =
        g (r.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [normalizedPointChartMap_eval, hom_eval₂, hgbase]
  let r : Spec (.of L) ⟶ scheme J :=
    Spec.map (CommRingCat.ofHom gJ) ≫ chartι J j
  have hfactor : r ≫ schemeQuotientMap I J hIJ = p := by
    dsimp only [r]
    rw [Category.assoc, chartι_schemeQuotientMap, ← Category.assoc,
      ← Spec.map_comp]
    have hc : CommRingCat.ofHom (chartQuotientMap I J hIJ j) ≫
        CommRingCat.ofHom gJ = CommRingCat.ofHom g :=
      by
        apply CommRingCat.hom_ext
        exact hgJ
    rw [hc]
    exact hgpoint
  letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
    schemeQuotientMap_closedImmersion I J hIJ
  letI : IsClosedImmersion (r ≫ schemeQuotientMap I J hIJ) := by
    rw [hfactor]
    infer_instance
  letI : IsClosedImmersion r := IsClosedImmersion.of_comp r (schemeQuotientMap I J hIJ)
  refine ⟨r, inferInstance, hfactor, ?_⟩
  rw [← schemeQuotientMap_toBase I J hIJ, ← Category.assoc, hfactor, hp]

end PfaffianDescent
