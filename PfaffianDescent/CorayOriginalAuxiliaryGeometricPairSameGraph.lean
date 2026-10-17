import PfaffianDescent.CorayOriginalAuxiliaryNormalizedCoordinatesInjective
import PfaffianDescent.CorayOriginalWholePairChartLineMap
import PfaffianDescent.CorayOriginalDistinctPairGraphMinorCoverage

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem selectedAuxiliary_chartBlockCoordinates_eq001
    {K B : Type u} [Field K] [CommRing B]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* B) :
    graphCoefficientMap g
      ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
       (fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) =
      (finiteProductCoordinateEquiv (R := B) 2 2).symm
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) := by
  apply (finiteProductCoordinateEquiv (R := B) 2 2).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective k
  cases s <;> simp [graphCoefficientMap, finiteProductCoordinateEquiv,
    LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Each ACTUAL geometric point of the SAME original auxiliary algebra
lies on the SAME selected original-K graph. Exact coefficient extension
and the chart coordinates prove this; scalar-extended graph membership
and normalized-point outcomes are not supplied. -/
theorem cubicOriginalAuxiliaryGeometricPoint_sameOriginalGraph001
    {K B M : Type u} [Field K] [CommRing B] [Field M]
    [Algebra K B] [Algebra K M] [Algebra.FiniteType K B]
    [Algebra.FormallyEtale K B] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) K) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ hB : R →ₐ[K] B,
      (finiteProductCoordinateEquiv (R := B) 2 2).symm
        (fun i => hB (chartCoordinate (equationIdeal p hp) j i)) ∈
          grassmannianChartSubmodule B rho (T.map (algebraMap K B)) →
    ∀ s : PrimeSpectrum (M ⊗[K] B),
      (finiteProductCoordinateEquiv (R := M) 2 2).symm
        (fun i => originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) s
          (hB (chartCoordinate (equationIdeal p hp) j i))) ∈
            grassmannianChartSubmodule M rho (T.map (algebraMap K M)) := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  dsimp only
  intro hB hGraph s
  let sigma := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) s
  let xB := (finiteProductCoordinateEquiv (R := B) 2 2).symm
    (fun i => hB (chartCoordinate (equationIdeal p hp) j i))
  have hMapGraph : graphCoefficientMap sigma.toRingHom xB ∈
      grassmannianChartSubmodule M rho ((T.map (algebraMap K B)).map sigma.toRingHom) := by
    rw [← grassmannianChartSubmodule_baseChange sigma.toRingHom rho (T.map (algebraMap K B))]
    exact Submodule.subset_span ⟨xB, hGraph, rfl⟩
  have hMatrix : (T.map (algebraMap K B)).map sigma.toRingHom = T.map (algebraMap K M) := by
    ext i k
    change sigma (algebraMap K B (T i k)) = algebraMap K M (T i k)
    exact sigma.commutes _
  rw [hMatrix] at hMapGraph
  have hCoordinates : graphCoefficientMap sigma.toRingHom xB =
      (finiteProductCoordinateEquiv (R := M) 2 2).symm
        (fun i => sigma (hB (chartCoordinate (equationIdeal p hp) j i))) := by
    apply (finiteProductCoordinateEquiv (R := M) 2 2).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := finiteProductCoordinateEquiv_baseChange sigma.toRingHom 2 2 xB
    rw [show finiteProductCoordinateEquiv (R := B) 2 2 xB =
      (fun i => hB (chartCoordinate (equationIdeal p hp) j i)) from
        (finiteProductCoordinateEquiv (R := B) 2 2).apply_symm_apply _] at h
    exact h.symm
  rw [hCoordinates] at hMapGraph
  exact hMapGraph

/-- ALL actual geometric points are enumerated. Original chart
surjectivity derives distinctness of points0/1. Their literal original-K
tensor evaluation gives both actual normalized vectors on the SAME graph
and its selected minor nonzero, without a distinctness, minor, tensor
point or scalar graph-membership outcome premise. -/
theorem cubicOriginalAuxiliaryGeometricEnumeration_actualTensorPair_distinct_sameOriginalGraph001
    {K B M : Type u} [Field K] [CommRing B] [Field M]
    [Algebra K B] [Algebra K M] [Algebra.FiniteType K B]
    [Algebra.FormallyEtale K B] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) K) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ (hB : R →ₐ[K] B), Function.Surjective hB →
      (finiteProductCoordinateEquiv (R := B) 2 2).symm
        (fun i => hB (chartCoordinate (equationIdeal p hp) j i)) ∈
          grassmannianChartSubmodule B rho (T.map (algebraMap K B)) →
    ∀ points : Fin 3 ≃ PrimeSpectrum (M ⊗[K] B),
    let h0 := (originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)).comp hB
    let h1 := (originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 1)).comp hB
    let pair := Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _)
    let xy := cubicOriginalWholePairChartAmbientVectors p hp j
    let x := graphCoefficientMap pair.toRingHom xy.1
    let y := graphCoefficientMap pair.toRingHom xy.2
    x ∈ grassmannianChartSubmodule M rho (T.map (algebraMap K M)) ∧
      y ∈ grassmannianChartSubmodule M rho (T.map (algebraMap K M)) ∧
      originalAmbientCoordinateFunctional j x = 1 ∧
      originalAmbientCoordinateFunctional j y = 1 ∧ x ≠ y ∧
      originalPairGrassmannMinor rho x y ≠ 0 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  dsimp only
  intro hB hSurj hGraph points
  let sigma0 := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)
  let sigma1 := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 1)
  let h0 := sigma0.comp hB
  let h1 := sigma1.comp hB
  let pair := Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _)
  let xy := cubicOriginalWholePairChartAmbientVectors p hp j
  let x := graphCoefficientMap pair.toRingHom xy.1
  let y := graphCoefficientMap pair.toRingHom xy.2
  let z0 : Fin 4 → M := fun i => h0 (chartCoordinate (equationIdeal p hp) j i)
  let z1 : Fin 4 → M := fun i => h1 (chartCoordinate (equationIdeal p hp) j i)
  have hLeft : x = (finiteProductCoordinateEquiv (R := M) 2 2).symm z0 := by
    have hMap : x = graphCoefficientMap h0.toRingHom
        ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
         (fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) := by
      change ((fun i => pair (chartCoordinate (equationIdeal p hp) j
        (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) ⊗ₜ[K] (1 : R))),
        (fun i => pair (chartCoordinate (equationIdeal p hp) j
        (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) ⊗ₜ[K] (1 : R)))) = _
      apply Prod.ext
      · funext i
        change (Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _))
          (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) ⊗ₜ[K] (1 : R)) =
          h0 (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)))
        simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      · funext i
        change (Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _))
          (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) ⊗ₜ[K] (1 : R)) =
          h0 (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))
        simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    exact hMap.trans (selectedAuxiliary_chartBlockCoordinates_eq001 p hp j h0.toRingHom)
  have hRight : y = (finiteProductCoordinateEquiv (R := M) 2 2).symm z1 := by
    have hMap : y = graphCoefficientMap h1.toRingHom
        ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
         (fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) := by
      change ((fun i => pair ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j
        (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)))),
        (fun i => pair ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j
        (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))))) = _
      apply Prod.ext
      · funext i
        change (Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _))
          ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))) =
          h1 (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)))
        simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      · funext i
        change (Algebra.TensorProduct.lift h0 h1 (fun _ _ => Commute.all _ _))
          ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))) =
          h1 (chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))
        simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact hMap.trans (selectedAuxiliary_chartBlockCoordinates_eq001 p hp j h1.toRingHom)
  have hx : x ∈ grassmannianChartSubmodule M rho (T.map (algebraMap K M)) := by
    rw [hLeft]
    exact cubicOriginalAuxiliaryGeometricPoint_sameOriginalGraph001 p hp j rho T hB hGraph (points 0)
  have hy : y ∈ grassmannianChartSubmodule M rho (T.map (algebraMap K M)) := by
    rw [hRight]
    exact cubicOriginalAuxiliaryGeometricPoint_sameOriginalGraph001 p hp j rho T hB hGraph (points 1)
  have hNormx : originalAmbientCoordinateFunctional j x = 1 := by
    rw [hLeft]
    change ((finiteProductCoordinateEquiv (R := M) 2 2)
      ((finiteProductCoordinateEquiv (R := M) 2 2).symm z0)) j = 1
    rw [LinearEquiv.apply_symm_apply]
    change h0 (chartCoordinate (equationIdeal p hp) j j) = 1
    rw [chartCoordinate_self, map_one]
  have hNormy : originalAmbientCoordinateFunctional j y = 1 := by
    rw [hRight]
    change ((finiteProductCoordinateEquiv (R := M) 2 2)
      ((finiteProductCoordinateEquiv (R := M) 2 2).symm z1)) j = 1
    rw [LinearEquiv.apply_symm_apply]
    change h1 (chartCoordinate (equationIdeal p hp) j j) = 1
    rw [chartCoordinate_self, map_one]
  have hNe : x ≠ y := by
    intro hxy
    have hZ : z0 = z1 := by
      have h := congrArg (finiteProductCoordinateEquiv (R := M) 2 2) hxy
      rw [hLeft, hRight] at h
      simpa only [LinearEquiv.apply_symm_apply] using h
    have hp := cubicOriginalAuxiliaryGeometricPoint_normalizedCoordinates_injective001 p hp j hB hSurj hZ
    have hIndex : (0 : Fin 3) = 1 := points.injective hp
    exact (by decide : (0 : Fin 3) ≠ 1) hIndex
  exact ⟨hx, hy, hNormx, hNormy, hNe,
    normalizedDistinctGrassmannPlanePair_selectedMinor_ne_zero001 rho (T.map (algebraMap K M))
      (originalAmbientCoordinateFunctional j) x y hx hy hNormx hNormy hNe⟩

end PfaffianDescent.Coray
