import PfaffianDescent.ProjectiveLineAtlas
import AllCharacteristics.ProjectiveSpaceChartEvaluation
import AllCharacteristics.ProjectiveOverlapLifting

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable (K : Type u) [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard Proj model of the projective line over the coefficient ring. -/
noncomputable def projectiveLineProj : Scheme.{u} :=
  scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

noncomputable def projectiveLineProjToBase : projectiveLineProj K ⟶ Spec (.of K) :=
  toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

end

/-- The only non-distinguished homogeneous variable indexes the one graph coordinate. -/
def lineProjectiveVariableEquiv (b : Bool) : (Fin 1 × Fin 1) ≃ {i : Bool // i ≠ b} where
  toFun _ := ⟨!b, by cases b <;> decide⟩
  invFun _ := (0, 0)
  left_inv i := by apply Prod.ext <;> exact Subsingleton.elim _ _
  right_inv i := by
    apply Subtype.ext
    rcases i with ⟨i, hi⟩
    cases b <;> cases i <;> simp_all

section
variable (K : Type u) [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

lemma projectiveChartPolynomialEquiv_X {σ : Type} (j : σ) (i : {i : σ // i ≠ j}) :
    chartPolynomialEquiv (R := K) j (X i) =
      chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j i.val := by
  have hx : (coordinateOneQuotientEquiv (R := K) j).symm (X i) =
      Ideal.Quotient.mk (coordinateOneIdeal j) (X i.val) := by
    change coordinateOneQuotientInverse j (X i) = _
    exact MvPolynomial.aeval_X _ i
  change chartPresentationEquiv _ j
    (Ideal.quotEquivOfEq (chartPresentationIdeal_bot (R := K) j).symm
      ((coordinateOneQuotientEquiv j).symm (X i))) = _
  rw [hx, Ideal.quotEquivOfEq_mk, chartPresentationEquiv_mk]
  exact MvPolynomial.eval₂_X _ _ i.val

/-- Each line Grassmannian chart is the corresponding actual Proj chart ring. -/
noncomputable def lineGrassmannianProjChartRingEquiv (b : Bool) :
    GrassmannianChartRing K 1 1 ≃+* ChartRing I₀ b :=
  (MvPolynomial.renameEquiv K (lineProjectiveVariableEquiv b)).toRingEquiv.trans
    (chartPolynomialEquiv b)

lemma lineGrassmannianProjChartRingEquiv_C (b : Bool) (k : K) :
    lineGrassmannianProjChartRingEquiv K b (C k) = chartBaseMap I₀ b k := by
  change chartPolynomialEquiv b ((MvPolynomial.renameEquiv K (lineProjectiveVariableEquiv b)) (C k)) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
  exact chartPolynomialEquiv_C b k

lemma lineGrassmannianProjChartRingEquiv_X (b : Bool) (i : Fin 1 × Fin 1) :
    lineGrassmannianProjChartRingEquiv K b (X i) = chartCoordinate I₀ b (!b) := by
  change chartPolynomialEquiv b ((MvPolynomial.renameEquiv K (lineProjectiveVariableEquiv b)) (X i)) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  exact projectiveChartPolynomialEquiv_X K b (lineProjectiveVariableEquiv b i)

/-- The actual affine chart isomorphism between the Proj model and the graph model. -/
noncomputable def lineGrassmannianProjChartIso (b : Bool) :
    Spec (.of (ChartRing I₀ b)) ≅ grassmannianChartScheme K 1 1 :=
  Scheme.Spec.mapIso (lineGrassmannianProjChartRingEquiv K b).toCommRingCatIso.op

lemma lineGrassmannianProjChartIso_toBase (b : Bool) :
    (lineGrassmannianProjChartIso K b).hom ≫ grassmannianChartToBase K 1 1 =
      chartι I₀ b ≫ projectiveLineProjToBase K := by
  change _ = chartι I₀ b ≫ toBase I₀
  rw [chartι_toBase]
  change Spec.map (CommRingCat.ofHom (lineGrassmannianProjChartRingEquiv K b).toRingHom) ≫
    Spec.map (CommRingCat.ofHom MvPolynomial.C) = Spec.map (CommRingCat.ofHom (chartBaseMap I₀ b))
  rw [← Spec.map_comp]
  exact congrArg (fun φ : K →+* ChartRing I₀ b => Spec.map (CommRingCat.ofHom φ))
    (RingHom.ext (lineGrassmannianProjChartRingEquiv_C K b))

end
end PfaffianDescent
