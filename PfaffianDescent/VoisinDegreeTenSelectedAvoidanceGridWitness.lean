import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridEvaluation
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCoordinateSelection

/-! # A native sixteen-point cubic witness whose kernel contains a proper pair -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Sixteen actual geometric grid points impose independent cubic
conditions. Both explicit grid cubics belong to their actual restriction
kernel, so that kernel contains a pair with finite native intersection. -/
theorem voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_witness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ v : Fin 16 → Fin 4 → L,
      Function.Injective v ∧ (∀ i, v i 0 = 1) ∧
      Function.Surjective (eval₂Hom (algebraMap L (Fin 16 → L)) (fun j i => v i j)) ∧
      Function.Surjective (homogeneousSectionRestriction (K := L) (fun j i => v i j) 3) ∧
      (p.map (algebraMap K L)).eval₂ (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 1).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 2).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 := by
  classical
  obtain ⟨x, hxin, hx0, hxzero, -, hxrank⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_grid_cubic_rank_seventeen (L := L) p hp hno
  letI : FiniteDimensional L (homogeneousSubmodule (Fin 4) L 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp (homogeneousSubmodule_fg (Fin 4) L 3)
  obtain ⟨a, ha, hsurj⟩ := voisinDegreeTenSelectedAvoidance_select_sixteen_of_rank_seventeen
    (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x) hxrank
  let v : Fin 16 → Fin 4 → L := x ∘ a
  have hrestriction : homogeneousSectionRestriction (K := L) (fun j i => v i j) 3 =
      LinearMap.pi (fun j => (LinearMap.proj (a j)).comp
        (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x)) := by
    ext s i
    exact finite_product_evaluation_apply v s.1 i
  have hsurj' : Function.Surjective
      (homogeneousSectionRestriction (K := L) (fun j i => v i j) 3) := by
    rw [hrestriction]
    exact hsurj
  have heval : Function.Surjective
      (eval₂Hom (algebraMap L (Fin 16 → L)) (fun j i => v i j)) := by
    intro z
    obtain ⟨s, hs⟩ := hsurj' z
    exact ⟨s.1, hs⟩
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
    (hp.map (algebraMap K L))
  have hzero (s : MvPolynomial (Fin 4) L) (hs : s ∈ J.toIdeal) :
      s.eval₂ (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 := by
    ext i
    rw [finite_product_evaluation_apply]
    simpa [v] using hxzero (a i) s hs
  refine ⟨v, hxin.comp ha, (fun i => hx0 (a i)), heval, hsurj', ?_, ?_, ?_⟩
  · apply hzero
    exact Ideal.subset_span (by simp [J, voisinDegreeTenSelectedAvoidance_gridIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal])
  · apply hzero
    exact Ideal.subset_span (by simp [J, voisinDegreeTenSelectedAvoidance_gridIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal])
  · apply hzero
    exact Ideal.subset_span (by simp [J, voisinDegreeTenSelectedAvoidance_gridIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal])

end PfaffianDescent
