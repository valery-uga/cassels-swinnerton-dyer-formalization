import PfaffianDescent.LineProjChartFunctions
import PfaffianDescent.ProjectiveChartMorphisms
import PfaffianDescent.LineNormalizedCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {R : Type*} [CommRing R]

lemma lineChartMatrix_eta (T : Matrix (Fin 1) (Fin 1) R) : lineChartMatrix R (T 0 0) = T := by
  funext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  rfl

end
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- The Proj-to-Grassmannian chart isomorphisms agree on all actual overlaps. -/
theorem lineProjToGrassmannian_compatible (b c : Bool)
    (f : X ⟶ Spec (.of (ChartRing I₀ b))) (g : X ⟶ Spec (.of (ChartRing I₀ c)))
    (h : f ≫ chartι I₀ b = g ≫ chartι I₀ c) :
    (f ≫ (lineGrassmannianProjChartIso K b).hom) ≫ grassmannianChartι K (lineChartPermutation b) =
      (g ≫ (lineGrassmannianProjChartIso K c).hom) ≫ grassmannianChartι K (lineChartPermutation c) := by
  apply grassmannianChartFunctions_ext K
  · rw [Category.assoc, Category.assoc, lineGrassmannianProjChartIso_toBase,
      lineGrassmannianProjChartIso_toBase]
    exact (Category.assoc f (chartι I₀ b) (projectiveLineProjToBase K)).symm.trans
      ((congrArg (fun q => q ≫ projectiveLineProjToBase K) h).trans
        (Category.assoc g (chartι I₀ c) (projectiveLineProjToBase K)))
  · rw [lineGrassmannianProjChartIso_functions, lineGrassmannianProjChartIso_functions]
    exact lineProjChartFunctions_submodule_eq K b c f g h

/-- The inverse chart isomorphisms agree on all actual Grassmannian overlaps. -/
theorem lineGrassmannianToProj_compatible (b c : Bool)
    (f g : X ⟶ grassmannianChartScheme K 1 1)
    (h : f ≫ grassmannianChartι K (lineChartPermutation b) =
      g ≫ grassmannianChartι K (lineChartPermutation c)) :
    (f ≫ (lineGrassmannianProjChartIso K b).inv) ≫ chartι I₀ b =
      (g ≫ (lineGrassmannianProjChartIso K c).inv) ≫ chartι I₀ c := by
  have hW := grassmannianChartFunctions_submodule_eq K (lineChartPermutation b) (lineChartPermutation c) f g h
  have hW' := (congrArg (grassmannianChartSubmodule Γ(X, ⊤) (lineChartPermutation b))
    (lineChartMatrix_eta (grassmannianChartFunctions K f))).trans
      (hW.trans (congrArg (grassmannianChartSubmodule Γ(X, ⊤) (lineChartPermutation c))
        (lineChartMatrix_eta (grassmannianChartFunctions K g))).symm)
  have hbd := (lineGrassmannianChartSubmodule_eq_iff Γ(X, ⊤) b c _ _).mp hW'
  have hc := lineNormalizedCoordinates_ratio b c
    (grassmannianChartFunctions K f 0 0) (grassmannianChartFunctions K g 0 0) hbd
  apply projectiveChartMorphisms_eq_of_ratio b c
  · rw [lineGrassmannianProjChartIso_inv_base, lineGrassmannianProjChartIso_inv_base]
    have hb : f ≫ grassmannianChartToBase K 1 1 = g ≫ grassmannianChartToBase K 1 1 := by
      simpa only [Category.assoc, grassmannianChartι_toBase] using
        congrArg (fun q => q ≫ grassmannianToBase K 1 1) h
    exact (affineFunctionHom_comp_Spec f MvPolynomial.C).symm.trans
      ((congrArg affineFunctionHom hb).trans (affineFunctionHom_comp_Spec g MvPolynomial.C))
  · simpa only [lineGrassmannianProjChartIso_inv_coordinate, lineNormalizedCoordinates] using hc.1
  · intro i
    simpa only [lineGrassmannianProjChartIso_inv_coordinate, lineNormalizedCoordinates] using hc.2 i

end
end PfaffianDescent
