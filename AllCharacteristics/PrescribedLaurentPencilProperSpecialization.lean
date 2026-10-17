import AllCharacteristics.LaurentPencilGenericCubic
import AllCharacteristics.SchemeSpecialization
import AllCharacteristics.HypersurfaceReduction

/-! SOURCE ONLY / UNVERIFIED. Proper specialization from the actual
k((t)) mapped generic cubic to the SAME original special cubic. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem prescribedLaurentGenericSection_specializes_original
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (a : Spec (.of (LaurentSeries k)) ⟶
      hypersurface (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg))
    (ha : a ≫ hypersurfaceToBase (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg) = 𝟙 _) :
    ∃ r : Spec (.of k) ⟶ hypersurface p hp,
      r ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  let f := hypersurfaceToBase (prescribedPowerSeriesPencil p g)
    (prescribedPowerSeriesPencil_homogeneous hp hg)
  let b := Spec.map (CommRingCat.ofHom
    (algebraMap (PowerSeries k) (LaurentSeries k)))
  let aF := a ≫ (prescribedLaurentGenericCubicIso p g hp hg).hom
  have haF : aF ≫ pullback.snd f b = 𝟙 _ := by
    dsimp only [aF, f, b]
    rw [Category.assoc, prescribedLaurentGenericCubicIso_hom_base, ha]
  have hK : HasPointOver f (algebraMap (PowerSeries k) (LaurentSeries k)) := by
    refine ⟨aF ≫ pullback.fst f b, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, haF, Category.id_comp]
  obtain ⟨rF, hrF⟩ := special_fiber_has_section f (PowerSeries.constantCoeff (R := k)) hK
  let e := hypersurfaceReductionIso (PowerSeries.constantCoeff (R := k))
    (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)
    p hp (prescribedPowerSeriesPencil_constantCoeff p g)
  refine ⟨rF ≫ e.inv, ?_⟩
  have he : e.inv ≫ hypersurfaceToBase p hp =
      pullback.snd f (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) := by
    rw [← hypersurfaceReductionIso_hom_snd (PowerSeries.constantCoeff (R := k))
      (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)
      p hp (prescribedPowerSeriesPencil_constantCoeff p g)]
    simp only [← Category.assoc, e, Iso.inv_hom_id, Category.id_comp]
  rw [Category.assoc, he, hrF]

end AllCharacteristics
