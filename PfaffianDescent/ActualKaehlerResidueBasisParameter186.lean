import PfaffianDescent.ActualKaehlerLineDualSurjectivity
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! SOURCE ONLY / UNVERIFIED. The ordinary actual one-vector basis
constructs the fiber functional and its bijectivity. Separable residue
then constructs a parameter in the SAME residue kernel whose differential
is the SAME basis vector in the actual fiber. No coefficient premise. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential
open scoped TensorProduct
universe u
variable {k R F : Type u} [Field k] [CommRing R] [Field F]
  [Algebra k R] [Algebra k F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal coordinate in the base change of the original basis. -/
def actualKaehlerResidueBasisCoordinate186 [Algebra R F]
    (b : Module.Basis Unit R (KaehlerDifferential k R)) :
    F ⊗[R] KaehlerDifferential k R →ₗ[F] F :=
  (b.baseChange F).coord ()

lemma actualKaehlerResidueBasisCoordinate_basisVector186 [Algebra R F]
    (b : Module.Basis Unit R (KaehlerDifferential k R)) :
    actualKaehlerResidueBasisCoordinate186 (F := F) b (1 ⊗ₜ[R] b ()) = 1 := by
  change (b.baseChange F).repr (1 ⊗ₜ[R] b ()) () = 1
  rw [Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self]
  simp

lemma actualKaehlerResidueBasisCoordinate_bijective186 [Algebra R F]
    (b : Module.Basis Unit R (KaehlerDifferential k R)) :
    Function.Bijective (actualKaehlerResidueBasisCoordinate186 (F := F) b) := by
  constructor
  · intro x y hxy
    apply (b.baseChange F).repr.injective
    apply Finsupp.ext
    intro a
    cases a
    exact hxy
  · intro c
    refine ⟨c • (1 ⊗ₜ[R] b ()), ?_⟩
    rw [map_smul, actualKaehlerResidueBasisCoordinate_basisVector186]
    exact mul_one c

/-- A genuine parameter whose actual differential fiber is the original
basis vector. The fiber functional and normalization are derived internally. -/
theorem actualKaehlerResidueBasis_exists_normalizedParameter186
    [Algebra.IsSeparable k F]
    (b : Module.Basis Unit R (KaehlerDifferential k R))
    (rho : R →ₐ[k] F) (hrho : Function.Surjective rho) :
    letI : Algebra R F := rho.toRingHom.toAlgebra
    ∃ t : R, rho t = 0 ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t : F ⊗[R] KaehlerDifferential k R) =
        1 ⊗ₜ[R] b () := by
  letI : Algebra R F := rho.toRingHom.toAlgebra
  letI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq
    (fun c => (rho.commutes c).symm)
  let q := actualKaehlerResidueBasisCoordinate186 (F := F) b
  have hq : Function.Bijective q := actualKaehlerResidueBasisCoordinate_bijective186 b
  obtain ⟨t, ht, hd⟩ := actualKaehlerLine_exists_residueIdeal_derivative_one hrho q hq.2
  refine ⟨t, ht, hq.1 ?_⟩
  exact hd.trans (actualKaehlerResidueBasisCoordinate_basisVector186 b).symm

end PfaffianDescent
