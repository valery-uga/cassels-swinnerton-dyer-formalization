import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSections

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
set_option backward.isDefEq.respectTransparency false

/-- Ring-level residue allows the chart ground field and geometric point field to differ. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap
    (φ : A →+* CubicSurfaceFirstJet K) : A →+* K :=
  (TrivSqZeroExt.fstHom K K (Fin 2 → K)).toRingHom.comp φ

/-- The literal derivative is A-linear on SAME H through the actual point residue. -/
def cubicClosedPointSerreSurfaceJetCotangent_ringIdealDerivativeResidueLinear
    (φ : A →+* CubicSurfaceFirstJet K) (g : A →+* B) (β : B →+* K)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    letI : Algebra A K := (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ).toAlgebra
    RingHom.ker g →ₗ[A] (Fin 2 → K) := by
  letI : Algebra A K := (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ).toAlgebra
  refine { toFun := fun a => (φ a.1).snd, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    change (φ (a.1 + b.1)).snd = _
    rw [map_add, TrivSqZeroExt.snd_add]
  · intro r a
    have ha : (φ a.1).fst = 0 := by
      change cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ a.1 = 0
      rw [hres]
      change β (g a.1) = 0
      rw [show g a.1 = 0 from a.2, map_zero]
    change (φ (r * a.1)).snd = (φ r).fst • (φ a.1).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, ha]
    simp

/-- The actual H fibre derivative over the geometric point field, without changing the chart field. -/
def cubicClosedPointSerreSurfaceJetCotangent_ringIdealTensorDerivative
    (φ : A →+* CubicSurfaceFirstJet K) (g : A →+* B) (β : B →+* K)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    letI : Algebra A K := (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ).toAlgebra
    K ⊗[A] RingHom.ker g →ₗ[K] (Fin 2 → K) := by
  letI : Algebra A K := (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ).toAlgebra
  exact TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton K _
    (cubicClosedPointSerreSurfaceJetCotangent_ringIdealDerivativeResidueLinear φ g β hres))

/-- Native actual ideal point-fibre derivative over an arbitrary geometric point field. -/
def cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative
    (φ : A →+* CubicSurfaceFirstJet K)
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (β : B →+* K)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)))).obj
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))) →ₗ[K]
      (Fin 2 → K) := by
  let r := cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ
  letI : Algebra A K := r.toAlgebra
  exact (cubicClosedPointSerreSurfaceJetCotangent_ringIdealTensorDerivative φ g β hres).comp
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv g r).toLinearMap

/-- Literal ACTUAL Γ ideal section evaluation gives the original ring-jet derivative.
The chart field and point field may differ. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative_evaluation
    (φ : A →+* CubicSurfaceFirstJet K)
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (β : B →+* K)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g)
    (a : RingHom.ker g) :
    cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative φ g β hres
      ((cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
        (CommRingCat.ofHom (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ))
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))).hom
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a)) =
    (φ a.1).snd := by
  let r := cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ
  letI : Algebra A K := r.toAlgebra
  change cubicClosedPointSerreSurfaceJetCotangent_ringIdealTensorDerivative φ g β hres
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv g r _) = _
  rw [cubicClosedPointSerreSurfaceJetCotangent_nativeIdealPointEvaluation_apply]
  change (1 : K) • (φ a.1).snd = _
  exact one_smul K _

end PfaffianDescent
