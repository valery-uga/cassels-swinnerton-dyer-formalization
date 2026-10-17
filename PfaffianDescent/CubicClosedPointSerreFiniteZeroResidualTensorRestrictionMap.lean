import PfaffianDescent.SchemeModuleTensor
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_tensorRestrictionMap
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (M N : ModuleCat.{u} S) :
    let MR := (ModuleCat.restrictScalars φ).obj M
    let NR := (ModuleCat.restrictScalars φ).obj N
    MR ⊗[R] NR →ₗ[R] (ModuleCat.restrictScalars φ).obj
      (ModuleCat.of S (M ⊗[S] N)) := by
  dsimp only
  let a : (ModuleCat.restrictScalars φ).obj M →ₛₗ[φ] M :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b : (ModuleCat.restrictScalars φ).obj N →ₛₗ[φ] N :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let t := TensorProduct.map a b
  exact
    { toFun := t
      map_add' := t.map_add
      map_smul' := t.map_smulₛₗ }

theorem cubicClosedPointSerreFiniteZeroResidual_tensorRestrictionMap_tmul
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (M N : ModuleCat.{u} S)
    (m : (ModuleCat.restrictScalars φ).obj M)
    (n : (ModuleCat.restrictScalars φ).obj N) :
    cubicClosedPointSerreFiniteZeroResidual_tensorRestrictionMap φ M N (m ⊗ₜ[R] n) =
      m ⊗ₜ[S] n := by
  let a : (ModuleCat.restrictScalars φ).obj M →ₛₗ[φ] M :=
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b : (ModuleCat.restrictScalars φ).obj N →ₛₗ[φ] N :=
    { toFun := fun n => n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change TensorProduct.map a b (m ⊗ₜ[R] n) = m ⊗ₜ[S] n
  rw [TensorProduct.map_tmul]
  rfl
end PfaffianDescent
