import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentFiber

noncomputable section
open AlgebraicGeometry TrivSqZeroExt TensorProduct
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- The derivative is linear over the actual chart ring acting through
its literal residue map. -/
def cubicClosedPointSerreSurfaceJetCotangent_derivativeResidueLinear
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    cubicClosedPointSerreSurfaceJetCotangent_ideal φ →ₗ[A] (Fin 2 → K) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  refine { toFun := cubicClosedPointSerreSurfaceJetCotangent_derivative φ
           map_add' := fun x y => map_add _ x y
           map_smul' := ?_ }
  intro r a
  have ha : (φ a.1).fst = 0 := a.2
  change (φ (r * a.1)).snd = (φ r).fst • (φ a.1).snd
  rw [map_mul, TrivSqZeroExt.snd_mul, ha]
  simp

/-- Literal scalar extension of the ideal derivative; no cotangent
or dimension certificate is supplied. -/
def cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    K ⊗[A] cubicClosedPointSerreSurfaceJetCotangent_ideal φ →ₗ[K] (Fin 2 → K) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  exact TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton K _
      (cubicClosedPointSerreSurfaceJetCotangent_derivativeResidueLinear φ))

@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative_tmul
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    ∀ (c : K) (a : cubicClosedPointSerreSurfaceJetCotangent_ideal φ),
      cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative φ (c ⊗ₜ[A] a) =
        c • cubicClosedPointSerreSurfaceJetCotangent_derivative φ a := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  intro c a
  rfl

 theorem cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative_surjective
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) (hφ : Function.Surjective φ) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    Function.Surjective (cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative φ) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  intro v
  obtain ⟨a, ha⟩ := cubicClosedPointSerreSurfaceJetCotangent_derivative_surjective φ hφ v
  refine ⟨1 ⊗ₜ[A] a, ?_⟩
  rw [cubicClosedPointSerreSurfaceJetCotangent_tensorDerivative_tmul, one_smul, ha]

/-- Restrict the derivative to the actual eleven-point ideal H. -/
def cubicClosedPointSerreSurfaceJetCotangent_idealDerivativeResidueLinear
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    H →ₗ[A] (Fin 2 → K) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  exact (cubicClosedPointSerreSurfaceJetCotangent_derivativeResidueLinear φ).comp
    (Submodule.inclusion hH)

/-- The actual H fiber, without replacing H by the maximal ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    K ⊗[A] H →ₗ[K] (Fin 2 → K) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  exact TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton K _
      (cubicClosedPointSerreSurfaceJetCotangent_idealDerivativeResidueLinear φ H hH))

@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative_tmul
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    ∀ (c : K) (a : H),
      cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ H hH (c ⊗ₜ[A] a) =
        c • (φ a.1).snd := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  intro c a
  rfl

/-- The product rule kills mH for the actual ideal H. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_idealDerivative_mul
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ)
    (r : cubicClosedPointSerreSurfaceJetCotangent_ideal φ) (a : H) :
    (φ (r.1 * a.1)).snd = 0 := by
  exact cubicClosedPointSerreSurfaceJetCotangent_derivative_mul φ r ⟨a.1, hH a.2⟩

/-- A checked ideal derivative surjection survives passage to the literal
point fiber. This helper does not assert geometric surjectivity for H. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative_surjective
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ)
    (hd : Function.Surjective (fun a : H => (φ a.1).snd)) :
    letI : Algebra A K :=
      (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ H hH) := by
  letI : Algebra A K :=
    (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom.toAlgebra
  intro v
  obtain ⟨a, ha⟩ := hd v
  refine ⟨1 ⊗ₜ[A] a, ?_⟩
  rw [cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative_tmul, one_smul]
  exact ha

/-- The actual affine point-pullback ideal sections carry the literal jet
first derivative. H is retained throughout. -/
def cubicClosedPointSerreSurfaceJetCotangent_closedIdealFiberDerivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (H : Ideal A) (hH : H ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    let g := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
        (IdealSheafDataModule.closedImmersionModule
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))))) →ₗ[K]
      (Fin 2 → K) := by
  let g := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
  letI : Algebra A K := g.toAlgebra
  exact (cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ H hH).comp
    (cubicClosedPointSerreSurfaceJetCotangent_closedIdealFiberSectionsEquiv g H).toLinearMap

end PfaffianDescent
