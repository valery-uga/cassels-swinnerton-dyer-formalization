import PfaffianDescent.VoisinChartFieldNormalizedPoint
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineFieldValues
import PfaffianDescent.VoisinPulledChartEquationVanishing

/-! Literal normalized coordinates of an actual affine field point. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem affineFieldPoint_normalizedPointAt
    {K E : Type u} [Field K] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellz : Ideal.Quotient.mk I.toIdeal ell = z)
    (U : Scheme.{u}) [IsAffine U]
    (t : U ⟶ Spec (.of (Away (grading I) z))) (tBase : U ⟶ Spec (.of K))
    (ht : t ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) = tBase)
    (h : Γ(U, ⊤) →+* E) :
    let b := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U tBase
    letI : Algebra K E := (h.comp b).toAlgebra
    let x : Fin 4 → E := fun j => h (pulledLinearChartCoordinate I z hz U t j)
    ell.eval₂ (algebraMap K E) x = 1 ∧
    ∃ (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K E) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K E) x) he) z = 1),
      linearNormalizedPointAt I x he z hz hzOne =
        (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ t) ≫
          Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
  dsimp only
  let b := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U tBase
  letI : Algebra K E := (h.comp b).toAlgebra
  let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
  let g : Away (grading I) z →+* E := (Spec.preimage (a ≫ t)).hom
  let x : Fin 4 → E := fun j => h (pulledLinearChartCoordinate I z hz U t j)
  have hg : Spec.map (CommRingCat.ofHom g) = a ≫ t := Spec.map_preimage _
  have hb : h.comp b = (Spec.preimage (a ≫ tBase)).hom :=
    voisinDegreeTenSelectedAvoidance_affineFieldPoint_baseCoefficientHom h tBase b rfl
  have hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K E := by
    have heq : CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) ≫
          CommRingCat.ofHom g = CommRingCat.ofHom (h.comp b) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, Category.assoc, ht, hb]
      exact (Spec.map_preimage (a ≫ tBase)).symm
    exact congrArg CommRingCat.Hom.hom heq
  have hcoords : (fun j => g (linearChartCoordinate I z hz j)) = x := by
    funext j
    simpa only [g, x, pulledLinearChartCoordinate_eq_affineFunctionHom] using
      voisinDegreeTenSelectedAvoidance_affineFieldPoint_coordinate_value h t
        (linearChartCoordinate I z hz j)
  have hnat := chartFieldPoint_normalizedPointAt I z hz ell hell hellz g hbase
  dsimp only at hnat
  rw [hcoords] at hnat
  obtain ⟨hellx, he, hzOne, hpoint⟩ := hnat
  refine ⟨hellx, he, hzOne, ?_⟩
  exact hpoint.trans (congrArg (fun s => s ≫
    Proj.awayι (grading I) z hz (by decide : 0 < 1)) hg)

end PfaffianDescent
