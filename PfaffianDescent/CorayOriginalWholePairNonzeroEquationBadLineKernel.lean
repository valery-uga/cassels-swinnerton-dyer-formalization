import PfaffianDescent.CorayOriginalGrassmannWholeSourceKernel
import PfaffianDescent.CorayOriginalWholePairChartLineMap
import PfaffianDescent.CorayOriginalPairChartDimension
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.FiniteStability

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The ACTUAL pair-to-line map on its literal selected-minor open gives
an ORIGINAL-K nonzero full-kernel equation. The full possibly nonreduced
pair source, derived graph matrix and original base maps are retained. -/
theorem originalPairMinorOpen_dimension_le_three_exists_actualBadLineEquation001
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x y : (Fin 2 → B) × (Fin 2 → B))
    (hDim : ringKrullDim B ≤ 3) :
    let d := originalPairGrassmannMinor rho x y
    let C := Localization.Away d
    let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
    let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
    let T := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧
      (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) q = 0 ∧
      closure (Set.range (originalPairMinorOpenToGrassmann (K := K) rho x y)) ≠
        (Set.univ : Set (grassmannianScheme K 2 2)) := by
  let d := originalPairGrassmannMinor rho x y
  let C := Localization.Away d
  let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
  let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
  let T := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
  let phi : GrassmannianChartRing K 2 2 →ₐ[K] C :=
    MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)
  have hDimC : ringKrullDim C ≤ 3 :=
    (localization_ringKrullDim_le001 (Submonoid.powers d)).trans hDim
  obtain ⟨q, hq0, hq⟩ :=
    grassmannLineChartMap_whole_dimension_le_three_exists_nonzero_kernel001 phi hDimC
  have hProper := grassmannLineChartMap_whole_dimension_le_three_wholeImageClosure_ne_univ001 phi rho hDimC
  exact ⟨q, hq0, hq, hProper⟩

/-- Every literal nonzero ORIGINAL pair equation, on the WHOLE quotient,
constructs an ORIGINAL-K bad-line polynomial for its actual minor-open map.
The source dimension and finite type are DERIVED from the actual cubic. -/
theorem cubicOriginalWholePairChart_nonzeroEquation_exists_actualBadLineEquation001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let T := R ⊗[K] R
    ∀ F : T, F ≠ 0 →
    let B := T ⧸ Ideal.span ({F} : Set T)
    let xy := cubicOriginalWholePairChartAmbientVectors p hp j
    let x := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.1
    let y := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.2
    let d := originalPairGrassmannMinor rho x y
    let C := Localization.Away d
    let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
    let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
    let M := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
    ∃ bad : GrassmannianChartRing K 2 2, bad ≠ 0 ∧
      (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => M ij.1 ij.2)) bad = 0 ∧
      closure (Set.range (originalPairMinorOpenToGrassmann (K := K) rho x y)) ≠
        (Set.univ : Set (grassmannianScheme K 2 2)) := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let T := R ⊗[K] R
  let ev : MvPolynomial (Fin 4) K →ₐ[K] R := aeval (chartCoordinate (equationIdeal p hp) j)
  have hEv : Function.Surjective ev := by
    intro r
    obtain ⟨q, hq⟩ := eval₂_chartCoordinate_surjective (equationIdeal p hp) j r
    exact ⟨q, hq⟩
  letI : Algebra.FiniteType K R := Algebra.FiniteType.of_surjective ev hEv
  letI : Algebra.FiniteType K T := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K R) (inferInstance : Algebra.FiniteType R T)
  dsimp only
  intro F hF
  let B := T ⧸ Ideal.span ({F} : Set T)
  let xy := cubicOriginalWholePairChartAmbientVectors p hp j
  let x := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.1
  let y := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.2
  have hDim : ringKrullDim B ≤ 3 :=
    cubicOriginalWholePairChart_nonzeroEquation_ringKrullDim_le_three001 p hp hp0 j F hF
  exact originalPairMinorOpen_dimension_le_three_exists_actualBadLineEquation001 rho x y hDim

end PfaffianDescent.Coray
