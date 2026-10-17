import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Canonical extension of an F-linear map into restriction of an actual E-module. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift
    {F E V : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] (N : ModuleCat E)
    (f : V →ₗ[F] (ModuleCat.restrictScalars (algebraMap F E)).obj N) :
    E ⊗[F] V →ₗ[E] N := by
  letI : Module F N := Module.compHom N (algebraMap F E)
  letI : IsScalarTower F E N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f' : V →ₗ[F] N := f
  exact LinearMap.liftBaseChange E f'

@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift_tmul
    {F E V : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] (N : ModuleCat E)
    (f : V →ₗ[F] (ModuleCat.restrictScalars (algebraMap F E)).obj N)
    (c : E) (v : V) :
    cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift N f (c ⊗ₜ[F] v) = c • f v := rfl

/-- Tensor extension retains the original literal naturality square. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift_naturality
    {F E V W : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (N P : ModuleCat E)
    (f : V →ₗ[F] (ModuleCat.restrictScalars (algebraMap F E)).obj N)
    (g : W →ₗ[F] (ModuleCat.restrictScalars (algebraMap F E)).obj P)
    (a : V →ₗ[F] W) (b : N →ₗ[E] P) (h : ∀ v, b (f v) = g (a v))
    (w : E ⊗[F] V) :
    b (cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift N f w) =
      cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift P g (a.baseChange E w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c v => simp only [cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift_tmul,
      LinearMap.baseChange_tmul, map_smul, h]

end PfaffianDescent
