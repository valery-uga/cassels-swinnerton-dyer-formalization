import PfaffianDescent.NativeResidueTensorRelations316
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-! Injectivity of the actual base-changed cotangent map from its concrete
relation criterion, over the actual quotient of the presentation ring. -/
namespace PfaffianDescent
open TensorProduct KaehlerDifferential

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
  [Algebra R P] [Algebra P S]

theorem residueCotangent_injective_of_relation_criterion316 (m : Ideal P)
    [Algebra S (P ⧸ m)] [IsScalarTower P S (P ⧸ m)]
    (hrel : ∀ x : RingHom.ker (algebraMap P S),
      D R P x ∈ m • (⊤ : Submodule P Ω[P⁄R]) →
        (x : P) ∈ m * RingHom.ker (algebraMap P S)) :
    Function.Injective (cotangentComplexBaseChange R S P (P ⧸ m)) := by
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  obtain ⟨x, rfl⟩ := residueTensor_exists_one_tmul316 m v
  have hD : (1 : P ⧸ m) ⊗ₜ[P] D R P x = 0 := by
    simpa only [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply] using hv
  exact (residueTensor_relation_eq_zero316 m _ x).2
    (hrel x ((residueTensor_one_tmul_eq_zero316 m (D R P x)).1 hD))

end PfaffianDescent
