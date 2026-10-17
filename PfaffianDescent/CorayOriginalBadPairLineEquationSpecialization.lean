import PfaffianDescent.CorayOriginalDistinctPairGraphMinorCoverage
import PfaffianDescent.CorayOriginalPairMinorMatrixUniqueness
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u
set_option autoImplicit false

private theorem graphCoefficientMap_comp_eq001
    {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* C) (g : C →+* D) (x : (Fin 2 → B) × (Fin 2 → B)) :
    graphCoefficientMap g (graphCoefficientMap f x) = graphCoefficientMap (g.comp f) x := rfl

/-- An ACTUAL normalized distinct pair in the SAME prescribed graph plane
constructs the literal localization lift and specializes every actual full
kernel equation to that SAME matrix. No lift, matrix equality, nonzero
minor, alternate line or norm outcome is supplied. -/
theorem originalPairMinorOpen_fullKernelEquation_vanishes_on_sameGraph001
    {K B M : Type u} [Field K] [CommRing B] [Field M]
    [Algebra K B] [Algebra K M]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x y : (Fin 2 → B) × (Fin 2 → B))
    (h : B →ₐ[K] M) (T : Matrix (Fin 2) (Fin 2) M)
    (ell : ((Fin 2 → M) × (Fin 2 → M)) →ₗ[M] M)
    (hx : graphCoefficientMap h.toRingHom x ∈ grassmannianChartSubmodule M rho T)
    (hy : graphCoefficientMap h.toRingHom y ∈ grassmannianChartSubmodule M rho T)
    (hEllx : ell (graphCoefficientMap h.toRingHom x) = 1)
    (hElly : ell (graphCoefficientMap h.toRingHom y) = 1)
    (hne : graphCoefficientMap h.toRingHom x ≠ graphCoefficientMap h.toRingHom y) :
    let d := originalPairGrassmannMinor rho x y
    let C := Localization.Away d
    let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
    let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
    let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
    let phi : GrassmannianChartRing K 2 2 →ₐ[K] C :=
      MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)
    ∀ q : GrassmannianChartRing K 2 2, phi q = 0 →
      (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) q = 0 := by
  let d := originalPairGrassmannMinor rho x y
  let C := Localization.Away d
  let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
  let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
  let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
  let phi : GrassmannianChartRing K 2 2 →ₐ[K] C :=
    MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)
  have hMinorMap : originalPairGrassmannMinor rho
      (graphCoefficientMap h.toRingHom x) (graphCoefficientMap h.toRingHom y) = h d := by
    dsimp only [originalPairGrassmannMinor, d]
    change originalPairFirstBlockMinor
      (graphCoordinatePermutation M rho (h.toRingHom ∘ x.1, h.toRingHom ∘ x.2))
      (graphCoordinatePermutation M rho (h.toRingHom ∘ y.1, h.toRingHom ∘ y.2)) =
        h (originalPairFirstBlockMinor (graphCoordinatePermutation B rho x)
          (graphCoordinatePermutation B rho y))
    rw [graphCoordinatePermutation_map h.toRingHom rho x,
      graphCoordinatePermutation_map h.toRingHom rho y]
    change h ((graphCoordinatePermutation B rho x).1 0) *
      h ((graphCoordinatePermutation B rho y).1 1) -
      h ((graphCoordinatePermutation B rho x).1 1) *
      h ((graphCoordinatePermutation B rho y).1 0) = h
        ((graphCoordinatePermutation B rho x).1 0 * (graphCoordinatePermutation B rho y).1 1 -
         (graphCoordinatePermutation B rho x).1 1 * (graphCoordinatePermutation B rho y).1 0)
    rw [map_sub, map_mul, map_mul]
  have hD : h d ≠ 0 := by
    rw [← hMinorMap]
    exact normalizedDistinctGrassmannPlanePair_selectedMinor_ne_zero001 rho T ell _ _ hx hy hEllx hElly hne
  let hLift : C →ₐ[K] M := IsLocalization.Away.liftAlgHom d (f := h) (isUnit_iff_ne_zero.mpr hD)
  have hLiftComp : hLift.toRingHom.comp (algebraMap B C) = h.toRingHom :=
    IsLocalization.Away.lift_comp d (isUnit_iff_ne_zero.mpr hD)
  have hxMap : graphCoefficientMap hLift.toRingHom xC =
      graphCoordinatePermutation M rho (graphCoefficientMap h.toRingHom x) := by
    change graphCoefficientMap hLift.toRingHom
      (graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)) = _
    rw [graphCoefficientMap_comp_eq001, hLiftComp]
    exact (graphCoordinatePermutation_map h.toRingHom rho x).symm
  have hyMap : graphCoefficientMap hLift.toRingHom yC =
      graphCoordinatePermutation M rho (graphCoefficientMap h.toRingHom y) := by
    change graphCoefficientMap hLift.toRingHom
      (graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)) = _
    rw [graphCoefficientMap_comp_eq001, hLiftComp]
    exact (graphCoordinatePermutation_map h.toRingHom rho y).symm
  have hMinorC : originalPairFirstBlockMinor xC yC * IsLocalization.Away.invSelf d = 1 := by
    have hMap : originalPairFirstBlockMinor xC yC = algebraMap B C d := by
      change algebraMap B C ((graphCoordinatePermutation B rho x).1 0) *
        algebraMap B C ((graphCoordinatePermutation B rho y).1 1) -
        algebraMap B C ((graphCoordinatePermutation B rho x).1 1) *
        algebraMap B C ((graphCoordinatePermutation B rho y).1 0) = algebraMap B C d
      dsimp only [d, originalPairGrassmannMinor, originalPairFirstBlockMinor]
      rw [map_sub, map_mul, map_mul]
    rw [hMap]
    exact IsLocalization.Away.mul_invSelf d
  have hxGraph : graphCoordinatePermutation M rho (graphCoefficientMap h.toRingHom x) ∈
      (Matrix.toLin' T).graph := by
    rw [← grassmannianChartSubmodule_own_chart M rho T]
    exact Submodule.mem_map_of_mem hx
  have hyGraph : graphCoordinatePermutation M rho (graphCoefficientMap h.toRingHom y) ∈
      (Matrix.toLin' T).graph := by
    rw [← grassmannianChartSubmodule_own_chart M rho T]
    exact Submodule.mem_map_of_mem hy
  have hMatrix : N.map hLift.toRingHom = T :=
    originalPairMinorGraphMatrix_map_eq_givenGraphMatrix001 hLift.toRingHom xC yC _ hMinorC T
      (by rw [hxMap]; exact ((LinearMap.mem_graph_iff _ _).mp hxGraph).symm)
      (by rw [hyMap]; exact ((LinearMap.mem_graph_iff _ _).mp hyGraph).symm)
  have hComp : hLift.comp phi =
      MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) := by
    apply MvPolynomial.algHom_ext
    intro ij
    change hLift ((MvPolynomial.aeval (R := K)
      (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)) (MvPolynomial.X ij)) =
      (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) (MvPolynomial.X ij)
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact congrFun (congrFun hMatrix ij.1) ij.2
  dsimp only
  intro q hq
  have hZero : (hLift.comp phi) q = 0 := by
    rw [AlgHom.comp_apply, hq, map_zero]
  rw [hComp] at hZero
  exact hZero

end PfaffianDescent.Coray
