import PfaffianDescent.CorayOriginalPairLineMinorMap
import PfaffianDescent.CorayLiteralOriginalPairPolynomial

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open _root_.Matrix
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The two literal ORIGINAL projective coordinate vectors on the WHOLE
original cubic chart tensor ring, with both native K coefficient actions. -/
def cubicOriginalWholePairChartAmbientVectors
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let B := R ⊗[K] R
    ((Fin 2 → B) × (Fin 2 → B)) × ((Fin 2 → B) × (Fin 2 → B)) := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  exact
    ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) ⊗ₜ[K] (1 : R),
      fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) ⊗ₜ[K] (1 : R)),
     (fun i => (1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)),
      fun i => (1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))))

/-- Every literal original two-coordinate minor open has a constructed
ORIGINAL-K line parameter in the WHOLE G(2,4), whose plane is EXACTLY the
span of the SAME two original projective coordinate vectors. The original
whole pair tensor ring and localization are retained. No dominance, norm,
line-map, spanning outcome or prescribed good line is a premise. -/
theorem cubicOriginalWholePairChart_minorOpen_exists_actualGrassmannLine001
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let B := R ⊗[K] R
    let xy := cubicOriginalWholePairChartAmbientVectors p hp j
    let d := originalPairGrassmannMinor rho xy.1 xy.2
    let C := Localization.Away d
    let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho xy.1)
    let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho xy.2)
    ∃ f : Spec (.of C) ⟶ grassmannianScheme K 2 2,
      f = grassmannianChartEvaluation K
        (originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)) ≫ grassmannianChartι K rho ∧
      f ≫ grassmannianToBase K 2 2 = Spec.map (CommRingCat.ofHom (algebraMap K C)) ∧
      grassmannianChartSubmodule C rho
        (originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)) =
        Submodule.span C
          ({graphCoefficientMap (algebraMap B C) xy.1, graphCoefficientMap (algebraMap B C) xy.2} :
            Set ((Fin 2 → C) × (Fin 2 → C))) := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let B := R ⊗[K] R
  let xy := cubicOriginalWholePairChartAmbientVectors p hp j
  exact ⟨originalPairMinorOpenToGrassmann (K := K) rho xy.1 xy.2, rfl,
    originalPairMinorOpenToGrassmann_originalBaseSquare001 rho xy.1 xy.2,
    originalPairMinorOpen_graph_eq_originalSpan001 rho xy.1 xy.2⟩

end PfaffianDescent.Coray
