import PfaffianDescent.GrassmannianChartFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}} {m n : ℕ}

/-- Equal regular-function graph submodules determine equal chart morphisms into the Grassmannian. -/
theorem grassmannianChartFunctions_ext
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (f g : X ⟶ grassmannianChartScheme K m n)
    (hb : f ≫ grassmannianChartToBase K m n = g ≫ grassmannianChartToBase K m n)
    (hW : grassmannianChartSubmodule Γ(X, ⊤) σ (grassmannianChartFunctions K f) =
      grassmannianChartSubmodule Γ(X, ⊤) τ (grassmannianChartFunctions K g)) :
    f ≫ grassmannianChartι K σ = g ≫ grassmannianChartι K τ := by
  obtain ⟨h, ht⟩ := grassmannianChartSubmodule_eq_transition Γ(X, ⊤) σ τ _ _ hW
  let a := grassmannianChartLift K f (grassmannianChartChange σ τ) h
  have ha : a ≫ grassmannianOverlapι K (grassmannianChartChange σ τ) = f :=
    grassmannianChartLift_fac K f _ h
  have hag : a ≫ grassmannianOverlapOtherι K (grassmannianChartChange σ τ) = g := by
    apply grassmannianChart_morphism_ext K
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => a ≫ q) (grassmannianOverlapOtherι_toBase K _)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ grassmannianChartToBase K m n) ha).trans hb)))
    · have he := grassmannianChartMatrix_transition K (grassmannianChartChange σ τ) a
        (ha.symm ▸ h)
      exact he.trans ((graphTransitionMatrix_congr _ (congrArg (grassmannianChartMatrix K) ha) _ h).trans ht)
  exact (congrArg (fun q => q ≫ grassmannianChartι K σ) ha.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => a ≫ q) (grassmannianChartOverlap_isPullback K σ τ).w).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ grassmannianChartι K τ) hag))))

end
end PfaffianDescent
