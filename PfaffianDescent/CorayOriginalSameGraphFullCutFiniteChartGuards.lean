import PfaffianDescent.CorayOriginalCubicFiniteChartFunctionGraphChoice
import PfaffianDescent.CorayOriginalGrassmannGraphRankThreePoint
import PfaffianDescent.CorayOriginalGraphCutChartMapSurjective

/-! SOURCE ONLY. Finite original chart guards are attached to the SAME
constructed explicit AdjoinRoot cubic cut, retaining its original closed
immersion, original coefficient map and full-degree-three closed point. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem originalChartMap_blockCoordinates_eq_actualNormalizedVector001
    {K B : Type u} [Field K] [CommRing B]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (g : ChartRing I j →+* B) (x : Fin 4 → B)
    (hCoords : ∀ k, g (chartCoordinate I j k) = x k) :
    graphCoefficientMap g
      ((fun i => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
       (fun i => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) =
      (finiteProductCoordinateEquiv (R := B) 2 2).symm x := by
  apply (finiteProductCoordinateEquiv (R := B) 2 2).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective k
  cases s <;>
    simpa [graphCoefficientMap, finiteProductCoordinateEquiv,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr] using hCoords _

/-- Actual finite chart functions select an original-K matrix, then noSection
constructs its SAME explicit cubic AdjoinRoot cut/field and original degree3
point. The exact cut chart map takes every supplied actual chart function to
a nonzero value. No rank, A, maps, field, generic avoidance or desired endpoint
is supplied as a premise. The honest individual nonzero chart functions and
separate nonzero original graph polynomial remain geometric inputs. -/
theorem originalChartFunctions_noSection_exists_sameGraph_fullDegreeThreeCut_all_nonzero001
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (hypersurface p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (hPivot : finSumFinEquiv (m := 2) (n := 2) (rho (Sum.inl (1 : Fin 2))) = j)
    {ι : Type u} [Finite ι] :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ h : ι → R, (∀ i, h i ≠ 0) →
    ∀ Q : GrassmannianChartRing K 2 2, Q ≠ 0 →
    ∃ T : Matrix (Fin 2) (Fin 2) K,
      MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) Q ≠ 0 ∧
      ∃ (c : Cubic K 4) (hc : c.toMvPolynomial = p),
      let a := originalGrassmannChartLineColumn001 rho T 0
      let b := originalGrassmannChartLineColumn001 rho T 1
      let i := originalGrassmannChartLinePivot001 rho 0
      let F := cubicLinePolynomial c a b
      let B := AdjoinRoot F
      let x : Fin 4 → B :=
        AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
          (fun k => algebraMap K B (b k))
      let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
      let I := equationIdeal p hp
      ∃ hBFinite : Module.Finite K B,
        letI := hBFinite
        ∃ hField : IsField B,
          letI : Field B := hField.toField
          ∃ (hell : ell.IsHomogeneous 1)
            (hxell : ell.eval₂ (algebraMap K B) x = 1)
            (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0),
          let r : Spec (.of B) ⟶ hypersurface p hp :=
            linearNormalizedPoint I x ell hell hxell heI
          x j = 1 ∧
          (finiteProductCoordinateEquiv (R := B) 2 2).symm x ∈
            grassmannianChartSubmodule B rho (T.map (algebraMap K B)) ∧
          IsClosedImmersion r ∧
          r ≫ hypersurfaceToBase p hp =
            Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
          Module.finrank K B = 3 ∧
          ∃ g : R →ₐ[K] B,
            (∀ k, g (chartCoordinate I j k) = x k) ∧
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ chartι I j = r ∧
            (∀ i, g (h i) ≠ 0) ∧
            Function.Surjective g ∧
            ∃ A : closedPoints (hypersurface p hp),
              A.1 = r (IsLocalRing.closedPoint B) ∧
              IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
              (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  intro R
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  intro h hh Q hQ
  obtain ⟨T, hTQ, hGuard⟩ :=
    cubicOriginalChartFunctions_exists_originalKMatrix_sameGraph_all_nonzero001
      p hp hp0 j rho hPivot h hh Q hQ
  have hCut := originalGrassmannChartMatrix_noSection_exists_explicit_sameGraph_rankThree_cut_and_fullDegreePoint001
    p hp rho T hno
  have hPivot' : originalGrassmannChartLinePivot001 rho 1 = j := hPivot
  rw [hPivot'] at hCut
  obtain ⟨c, hc, hxj, hxGraph, hBFinite, hell, hxell, heI,
    hClosed, hbase, hRank, _hLinearCoords, hChart, hFinite, hRest⟩ := hCut
  let a := originalGrassmannChartLineColumn001 rho T 0
  let b := originalGrassmannChartLineColumn001 rho T 1
  let i := originalGrassmannChartLinePivot001 rho 0
  let F := cubicLinePolynomial c a b
  let B := AdjoinRoot F
  let x : Fin 4 → B :=
    AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
      (fun k => algebraMap K B (b k))
  let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
  let I := equationIdeal p hp
  letI : Module.Finite K B := hBFinite
  let r : Spec (.of B) ⟶ hypersurface p hp := linearNormalizedPoint I x ell hell hxell heI
  letI : IsFinite (r ≫ hypersurfaceToBase p hp) := hFinite
  obtain ⟨_hFiniteRank, hField, hA⟩ := hRest
  letI : Field B := hField.toField
  obtain ⟨gRing, hgBase, hgCoords, hgFactor⟩ := hChart
  let g : R →ₐ[K] B :=
    { gRing with
      commutes' k := DFunLike.congr_fun hgBase k }
  have hgGraph : graphCoefficientMap g.toRingHom
      ((fun k => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl k))),
       (fun k => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr k)))) ∈
      grassmannianChartSubmodule B rho (T.map (algebraMap K B)) := by
    rw [originalChartMap_blockCoordinates_eq_actualNormalizedVector001 I j g.toRingHom x hgCoords]
    exact hxGraph
  have hNonzero : ∀ k, g (h k) ≠ 0 := hGuard B g hgGraph
  have hSurjective : Function.Surjective g :=
    originalFixedGraphAdjoinRoot_chartMap_surjective001 p hp j F rho T g hgCoords
  exact ⟨T, hTQ, c, hc, hBFinite, hField, hell, hxell, heI,
    hxj, hxGraph, hClosed, hbase, hRank, g, hgCoords, hgFactor, hNonzero, hSurjective, hA⟩

end PfaffianDescent.Coray
