import PfaffianDescent.VoisinDegreeElevenSerreIncidenceParameterRankTransport

/-! # Actual canonical parameter basis transport preserves bases and chart maps -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceParameterRankChart_base
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) (j : Fin n) (a : K) :
    serreIncidenceParameterRankChartEquiv K h j
      (chartBaseMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j a) =
    chartBaseMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) ((finCongr h) j) a := by
  subst m
  rfl

theorem serreIncidenceParameterRankChart_map
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) (j : Fin n) :
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≫
      (serreIncidenceParameterRankIso K h).hom =
    Spec.map (CommRingCat.ofHom (serreIncidenceParameterRankChartEquiv K h j).symm.toRingHom) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) ((finCongr h) j) := by
  subst m
  change chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j =
    Spec.map (𝟙 (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) j))) ≫ chartι _ j
  rw [Spec.map_id, Category.id_comp]

@[reassoc]
theorem serreIncidenceNineParameterIso_toBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9) :
    (serreIncidenceNineParameterIso base M h9).hom ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) =
    schemeModuleGlobalSectionsProjectiveParametersToBase base M :=
  serreIncidenceParameterRankIso_toBase K h9

end PfaffianDescent
