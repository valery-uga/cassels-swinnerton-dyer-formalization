import PfaffianDescent.GrassmannianSchemeFiniteCharts
import PfaffianDescent.GrassmannianLocalNaturality
import PfaffianDescent.GrassmannianLocalizationMembership

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- Scheme chart compatibility gives the denominator-clearing condition needed to descend ambient submodules. -/
theorem grassmannianSchemeCharts_clear_denominators
    (f : GrassmannianAlgebraPoint K A m n) (a b : A)
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) (Localization.Away a))
    (U : Matrix (Fin n) (Fin m) (Localization.Away b))
    (hT : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1 =
      (grassmannianChartAlgebraPoint K (Localization.Away a) m n σ T).1)
    (hU : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) ≫ f.1 =
      (grassmannianChartAlgebraPoint K (Localization.Away b) m n τ U).1)
    (x : (Fin m → A) × (Fin n → A))
    (hx : graphCoefficientMap (algebraMap A (Localization.Away a)) x ∈
      grassmannianChartSubmodule (Localization.Away a) σ T) :
    ∃ e : ℕ, (a ^ e) • graphCoefficientMap (algebraMap A (Localization.Away b)) x ∈
      grassmannianChartSubmodule (Localization.Away b) τ U := by
  let B := Localization.Away b
  let D := Localization.Away (algebraMap A B a)
  let ψ : B →ₐ[K] D := IsScalarTower.toAlgHom K B D
  have hu : IsUnit (algebraMap A D a) := by
    rw [IsScalarTower.algebraMap_apply A B D]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A B a)
  let φ : Localization.Away a →ₐ[K] D :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom K A D) a hu
  have hφ : φ.toRingHom.comp (algebraMap A (Localization.Away a)) = algebraMap A D :=
    IsLocalization.Away.lift_comp a hu
  have hc : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact hφ.trans (IsScalarTower.algebraMap_eq A B D)
  have hpc : (grassmannianChartAlgebraPoint K D m n σ (T.map φ)).1 =
      (grassmannianChartAlgebraPoint K D m n τ (U.map ψ)).1 := by
    have heT := congrArg Subtype.val (grassmannianAlgebraPointMap_chart K φ m n σ T)
    have heU := congrArg Subtype.val (grassmannianAlgebraPointMap_chart K ψ m n τ U)
    calc
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (grassmannianChartAlgebraPoint K (Localization.Away a) m n σ T).1 := heT.symm
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1) :=
        congrArg (fun q => Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q) hT.symm
      _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f.1) := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ f.1) hc).trans (Category.assoc _ _ _))
      _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
          (grassmannianChartAlgebraPoint K B m n τ U).1 :=
        congrArg (fun q => Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ q) hU
      _ = _ := heU
  have hS := (grassmannianChartEvaluation_eq_iff_submodule K σ τ (T.map φ) (U.map ψ)).mp hpc
  have hmem : graphCoefficientMap φ.toRingHom
      (graphCoefficientMap (algebraMap A (Localization.Away a)) x) ∈
      grassmannianSubmoduleBaseChange φ.toRingHom
        (grassmannianChartSubmodule (Localization.Away a) σ T) :=
    Submodule.subset_span ⟨_, hx, rfl⟩
  have hST : grassmannianSubmoduleBaseChange φ.toRingHom
      (grassmannianChartSubmodule (Localization.Away a) σ T) =
      grassmannianSubmoduleBaseChange ψ.toRingHom (grassmannianChartSubmodule B τ U) :=
    (grassmannianChartSubmodule_baseChange φ.toRingHom σ T).trans
      (hS.trans (grassmannianChartSubmodule_baseChange ψ.toRingHom τ U).symm)
  rw [hST] at hmem
  have hcoeff : graphCoefficientMap φ.toRingHom
      (graphCoefficientMap (algebraMap A (Localization.Away a)) x) =
      graphCoefficientMap (algebraMap B D) (graphCoefficientMap (algebraMap A B) x) := by
    change graphCoefficientMap (φ.toRingHom.comp (algebraMap A (Localization.Away a))) x =
      graphCoefficientMap ((algebraMap B D).comp (algebraMap A B)) x
    rw [hφ, ← IsScalarTower.algebraMap_eq A B D]
  rw [hcoeff] at hmem
  obtain ⟨e, he⟩ := (grassmannian_localized_mem_iff B D (algebraMap A B a)
    (grassmannianChartSubmodule B τ U) (graphCoefficientMap (algebraMap A B) x)).mp hmem
  refine ⟨e, ?_⟩
  simpa only [← map_pow, algebraMap_smul] using he

end
end PfaffianDescent
