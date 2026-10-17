import PfaffianDescent.FrameHomogeneousGorenstein
import PfaffianDescent.SelfInjectiveDimensionTransport
import PfaffianDescent.FrameIdealNormalization

namespace PfaffianDescent
open CategoryTheory MvPolynomial
section
variable {K : Type*} [Field K] [CharZero K]

/-- Every five-point projective frame has a Noetherian homogeneous coordinate
ring of self-injective dimension at most one. The ideal is the actual
intersection of the homogeneous prime ideals of the points. -/
theorem five_point_homogeneous_ring_gorenstein
    (p : Fin 5 → (Fin 4 → K)) (hp : FivePointGeneralPosition p) :
    IsNoetherianRing (MvPolynomial (Fin 4) K ⧸ fiveVectorIdeal p) ∧
      HasInjectiveDimensionLE (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ fiveVectorIdeal p)
        (MvPolynomial (Fin 4) K ⧸ fiveVectorIdeal p)) 1 := by
  obtain ⟨E, _, hE⟩ := fiveVectorIdeal_normalization p hp
  let e : FrameCoordinateRing K ≃ₐ[K] (MvPolynomial (Fin 4) K ⧸ fiveVectorIdeal p) :=
    Ideal.quotientEquivAlg frameIdeal (fiveVectorIdeal p) E hE.symm
  exact ⟨inferInstance, (self_injectiveDimensionLE_ringEquiv e.toRingEquiv 1).mp
    FrameCoordinateRing.self_injectiveDimensionLE_one⟩

end
end PfaffianDescent
