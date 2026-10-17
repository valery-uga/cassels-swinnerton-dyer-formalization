import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFractionPoint
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridPulledCoordinates
import PfaffianDescent.VoisinChartSchemePointNormalized

/-! Exact normalized marked points at every field point of the actual chart. -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_orderedChartLift_fieldPoint_baseRingHom
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (toBase I) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading I) (coordinate I 0)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) (coordinate I 0)
        (coordinate_mem I 0) (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (toBase I) n)) ≫
        (orderedFamilyCoordinate (toBase I) n k).left)
    (a : Spec (.of F) ⟶ U) (k : Fin n) :
    (Spec.preimage (a ≫ t k)).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I 0)) =
    (Spec.preimage (a ≫ i ≫ (orderedFamilyConfigurationOver (toBase I) n).hom)).hom := by
  have hscheme := congrArg (fun v : U ⟶ Spec (.of K) => a ≫ v)
    (voisinDegreeTenSelectedAvoidance_orderedChartLift_baseMap I n U i t ht k)
  have hpre := congrArg Spec.preimage hscheme
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_orderedChartLift_fieldPoint_normalizedPoint
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (toBase I) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading I) (coordinate I 0)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) (coordinate I 0)
        (coordinate_mem I 0) (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (toBase I) n)) ≫
        (orderedFamilyCoordinate (toBase I) n k).left)
    (a : Spec (.of F) ⟶ U) (k : Fin n) :
    let b : K →+* F := (Spec.preimage (a ≫ i ≫
      (orderedFamilyConfigurationOver (toBase I) n).hom)).hom
    letI : Algebra K F := b.toAlgebra
    let x : Fin 4 → F := fun j => (Spec.preimage (a ≫ t k)).hom
      (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) j)
    x 0 = 1 ∧
    ∃ (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) (coordinate I 0) = 1),
      linearNormalizedPointAt I x he (coordinate I 0) (coordinate_mem I 0) hzOne =
        (a ≫ i ≫ Over.Hom.left (orderedFamilyConfigurationι (toBase I) n)) ≫
          (orderedFamilyCoordinate (toBase I) n k).left := by
  dsimp only
  let b : K →+* F := (Spec.preimage (a ≫ i ≫
    (orderedFamilyConfigurationOver (toBase I) n).hom)).hom
  letI : Algebra K F := b.toAlgebra
  have hbase : (Spec.preimage (a ≫ t k)).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I 0)) =
      algebraMap K F :=
    voisinDegreeTenSelectedAvoidance_orderedChartLift_fieldPoint_baseRingHom I n U i t ht a k
  obtain ⟨hnorm, he, hzOne, hpoint⟩ := chartSchemePoint_normalizedPointAt I
    (coordinate I 0) (coordinate_mem I 0) (X 0) (isHomogeneous_X K 0) rfl
    (a ≫ t k) hbase
  refine ⟨?_, he, hzOne, ?_⟩
  · simpa only [MvPolynomial.eval₂_X] using hnorm
  · rw [hpoint, Category.assoc, ht k]
    simp only [Category.assoc]

end PfaffianDescent
