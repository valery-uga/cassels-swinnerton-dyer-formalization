import PfaffianDescent.GrassmannianCoordinateFunctor
import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C] {m n : ℕ}

/-- Chart morphisms obtained from the same ambient quotient agree on every scheme over their overlap. -/
theorem grassmannianChart_morphism_eq_of_baseChange
    (α : A →ₐ[K] B) (β : A →ₐ[K] C)
    (W : Submodule A ((Fin m → A) × (Fin n → A)))
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) B) (U : Matrix (Fin n) (Fin m) C)
    (hT : grassmannianSubmoduleBaseChange α.toRingHom W = grassmannianChartSubmodule B σ T)
    (hU : grassmannianSubmoduleBaseChange β.toRingHom W = grassmannianChartSubmodule C τ U)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of B)) (g : X ⟶ Spec (.of C))
    (h : f ≫ Spec.map (CommRingCat.ofHom α.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom β.toRingHom)) :
    f ≫ (grassmannianChartAlgebraPoint K B m n σ T).1 =
      g ≫ (grassmannianChartAlgebraPoint K C m n τ U).1 := by
  have hfg : (affineFunctionHom f).comp α.toRingHom = (affineFunctionHom g).comp β.toRingHom := by
    simpa only [affineFunctionHom_comp_Spec] using congrArg affineFunctionHom h
  let κ : K →+* Γ(X, ⊤) := (affineFunctionHom f).comp (algebraMap K B)
  letI : Algebra K Γ(X, ⊤) := κ.toAlgebra
  let φ : B →ₐ[K] Γ(X, ⊤) :=
    { __ := affineFunctionHom f, commutes' := fun _ => rfl }
  let ψ : C →ₐ[K] Γ(X, ⊤) :=
    { __ := affineFunctionHom g
      commutes' := fun k => by
        change affineFunctionHom g (algebraMap K C k) = affineFunctionHom f (algebraMap K B k)
        rw [← β.commutes, ← α.commutes]
        exact (congrArg (fun t : A →+* Γ(X, ⊤) => t (algebraMap K A k)) hfg).symm }
  have hs : grassmannianChartSubmodule Γ(X, ⊤) σ (T.map φ) =
      grassmannianChartSubmodule Γ(X, ⊤) τ (U.map ψ) := by
    change grassmannianChartSubmodule Γ(X, ⊤) σ (T.map φ.toRingHom) =
      grassmannianChartSubmodule Γ(X, ⊤) τ (U.map ψ.toRingHom)
    rw [← grassmannianChartSubmodule_baseChange φ.toRingHom, ← hT,
      grassmannianSubmoduleBaseChange_comp]
    change grassmannianSubmoduleBaseChange ((affineFunctionHom f).comp α.toRingHom) W = _
    rw [hfg, ← grassmannianSubmoduleBaseChange_comp, hU,
      grassmannianChartSubmodule_baseChange]
  have he := (grassmannianChartEvaluation_eq_iff_submodule K σ τ (T.map φ) (U.map ψ)).mpr hs
  have hf : f ≫ (grassmannianChartAlgebraPoint K B m n σ T).1 =
      X.toSpecΓ ≫ (grassmannianChartAlgebraPoint K Γ(X, ⊤) m n σ (T.map φ)).1 := by
    rw [← from_affineFunctionHom f]
    change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
      (grassmannianChartEvaluation K T ≫ grassmannianChartι K σ) = _
    rw [Category.assoc, ← Category.assoc (Spec.map _) _, grassmannianChartEvaluation_map]
    rfl
  have hg : g ≫ (grassmannianChartAlgebraPoint K C m n τ U).1 =
      X.toSpecΓ ≫ (grassmannianChartAlgebraPoint K Γ(X, ⊤) m n τ (U.map ψ)).1 := by
    rw [← from_affineFunctionHom g]
    change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
      (grassmannianChartEvaluation K U ≫ grassmannianChartι K τ) = _
    rw [Category.assoc, ← Category.assoc (Spec.map _) _, grassmannianChartEvaluation_map]
    rfl
  exact hf.trans ((congrArg (fun q => X.toSpecΓ ≫ q) he).trans hg.symm)

end
end PfaffianDescent
