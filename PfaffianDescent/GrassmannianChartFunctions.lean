import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.GrassmannianChartSubmodules
import PfaffianDescent.GrassmannianSmooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable {X : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- An affine-target morphism induces its corresponding map from the spectrum of global functions. -/
noncomputable def affineFunctionSpec (f : X ⟶ Spec (.of R)) :
    Spec (.of Γ(X, ⊤)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (affineFunctionHom f))

lemma affineFunctionSpec_comp (f : X ⟶ Spec (.of R)) (g : Spec (.of R) ⟶ Spec (.of S)) :
    affineFunctionSpec (f ≫ g) = affineFunctionSpec f ≫ g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  change Spec.map (CommRingCat.ofHom (affineFunctionHom (f ≫ Spec.map φ))) =
    Spec.map (CommRingCat.ofHom (affineFunctionHom f)) ≫ Spec.map φ
  rw [← Spec.map_comp]
  exact congrArg (fun ψ : S →+* Γ(X, ⊤) => Spec.map (CommRingCat.ofHom ψ))
    (affineFunctionHom_comp_Spec f φ.hom)

end
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}} {m n : ℕ}

/-- Chart coordinates as actual regular functions on an arbitrary test scheme. -/
noncomputable def grassmannianChartFunctions (f : X ⟶ grassmannianChartScheme K m n) :
    Matrix (Fin n) (Fin m) Γ(X, ⊤) :=
  fun i j => affineFunctionHom f (MvPolynomial.X (i, j))

lemma polynomial_aeval_ringHom {A : Type u} [CommRing A] [Algebra K A]
    (ι : Type) (φ : MvPolynomial ι K →+* A)
    (hφ : φ.comp (algebraMap K (MvPolynomial ι K)) = algebraMap K A) :
    (MvPolynomial.aeval (R := K) (fun i => φ (MvPolynomial.X i))).toRingHom = φ := by
  apply MvPolynomial.ringHom_ext
  · intro k
    change MvPolynomial.aeval _ (MvPolynomial.C k) = φ (MvPolynomial.C k)
    rw [MvPolynomial.aeval_C]
    exact (RingHom.congr_fun hφ k).symm
  · intro i
    exact MvPolynomial.aeval_X _ _

lemma grassmannianChartFunctions_evaluation
    [Algebra K Γ(X, ⊤)] (f : X ⟶ grassmannianChartScheme K m n)
    (hf : (affineFunctionHom f).comp (algebraMap K (GrassmannianChartRing K m n)) = algebraMap K Γ(X, ⊤)) :
    grassmannianChartEvaluation K (grassmannianChartFunctions K f) = affineFunctionSpec f := by
  have he := polynomial_aeval_ringHom K (Fin n × Fin m) (affineFunctionHom f) hf
  exact congrArg (fun ψ : GrassmannianChartRing K m n →+* Γ(X, ⊤) => Spec.map (CommRingCat.ofHom ψ)) he

/-- On every test scheme, equal Grassmannian chart morphisms define the same submodule of regular functions. -/
theorem grassmannianChartFunctions_submodule_eq
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (f g : X ⟶ grassmannianChartScheme K m n)
    (h : f ≫ grassmannianChartι K σ = g ≫ grassmannianChartι K τ) :
    grassmannianChartSubmodule Γ(X, ⊤) σ (grassmannianChartFunctions K f) =
      grassmannianChartSubmodule Γ(X, ⊤) τ (grassmannianChartFunctions K g) := by
  let κ := (affineFunctionHom f).comp (algebraMap K (GrassmannianChartRing K m n))
  letI : Algebra K Γ(X, ⊤) := κ.toAlgebra
  have hb : f ≫ grassmannianChartToBase K m n = g ≫ grassmannianChartToBase K m n := by
    have hh := congrArg (fun t => t ≫ grassmannianToBase K m n) h
    simpa only [Category.assoc, grassmannianChartι_toBase] using hh
  have hg : (affineFunctionHom g).comp (algebraMap K (GrassmannianChartRing K m n)) =
      algebraMap K Γ(X, ⊤) := by
    change (affineFunctionHom g).comp (algebraMap K (GrassmannianChartRing K m n)) =
      (affineFunctionHom f).comp (algebraMap K (GrassmannianChartRing K m n))
    exact (affineFunctionHom_comp_Spec g (algebraMap K (GrassmannianChartRing K m n))).symm.trans
      ((congrArg affineFunctionHom hb).symm.trans
        (affineFunctionHom_comp_Spec f (algebraMap K (GrassmannianChartRing K m n))))
  apply (grassmannianChartEvaluation_eq_iff_submodule K σ τ _ _).mp
  rw [grassmannianChartFunctions_evaluation K f rfl, grassmannianChartFunctions_evaluation K g hg]
  let H := grassmannianChartOverlap_isPullback K σ τ
  let a := H.lift f g h
  have ha : a ≫ grassmannianOverlapι K (grassmannianChartChange σ τ) = f := H.lift_fst _ _ h
  have hb : a ≫ grassmannianOverlapOtherι K (grassmannianChartChange σ τ) = g := H.lift_snd _ _ h
  have hfa : affineFunctionSpec a ≫ grassmannianOverlapι K (grassmannianChartChange σ τ) =
      affineFunctionSpec f := (affineFunctionSpec_comp a _).symm.trans (congrArg affineFunctionSpec ha)
  have hga : affineFunctionSpec a ≫ grassmannianOverlapOtherι K (grassmannianChartChange σ τ) =
      affineFunctionSpec g := (affineFunctionSpec_comp a _).symm.trans (congrArg affineFunctionSpec hb)
  exact (congrArg (fun q => q ≫ grassmannianChartι K σ) hfa.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => affineFunctionSpec a ≫ q) H.w).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ grassmannianChartι K τ) hga))))

end
end PfaffianDescent
