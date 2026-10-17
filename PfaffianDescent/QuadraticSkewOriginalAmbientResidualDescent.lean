import PfaffianDescent.QuadraticSkewConjugateParameterNonvanishing
/-! SOURCE ONLY / UNVERIFIED. Coefficient conjugation of the actual paired
frame and actual transformed ground cubic derives all exchange identities
for the varying secant, then descends its ORIGINAL ambient coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
open QuarticNet MixedNormalForm OriginalBridge ActualSecant MixedNonvanishing
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E]


private theorem coefficientConjugation_planeT
    (σ : E ≃ₐ[k] E) :
    MvPolynomial.map σ.toRingHom (planeT.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      planeT.{u, v} := by
  change MvPolynomial.map σ.toRingHom
      (MvPolynomial.X (ULift.up (0 : Fin 2)) : MvPolynomial (ULift.{v} (Fin 2)) E) =
    MvPolynomial.X (ULift.up (0 : Fin 2))
  exact MvPolynomial.map_X _ _

private theorem coefficientConjugation_planeU
    (σ : E ≃ₐ[k] E) :
    MvPolynomial.map σ.toRingHom (planeU.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      planeU.{u, v} := by
  change MvPolynomial.map σ.toRingHom
      (MvPolynomial.X (ULift.up (1 : Fin 2)) : MvPolynomial (ULift.{v} (Fin 2)) E) =
    MvPolynomial.X (ULift.up (1 : Fin 2))
  exact MvPolynomial.map_X _ _

theorem polynomial_conjugation_involutive
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (p : MvPolynomial SecantPlaneIndex E) :
    MvPolynomial.map σ.toRingHom (MvPolynomial.map σ.toRingHom p) = p := by
  have hc : σ.toRingHom.comp σ.toRingHom = RingHom.id E := by
    ext a
    exact DFunLike.congr_fun hσsq a
  rw [MvPolynomial.map_map, hc, MvPolynomial.map_id]

theorem actualSecantA_conjugation
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl) (α : E)
    (G : MvPolynomial (Fin 4) E)
    (hGExchange : MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G) :
    MvPolynomial.map σ.toRingHom (actualSecantA α (σ α) G) = actualSecantB α (σ α) G := by
  have hcoeff (i : Fin 6) : σ.toRingHom ((mixedCoefficients G).left i) =
      (mixedCoefficients G).right i := mixedCoefficients_exchange σ G hGExchange i
  have hβ : σ.toRingHom (σ α) = α := DFunLike.congr_fun hσsq α
  have hα : σ.toRingHom α = σ α := rfl
  rw [actualSecantA_eq_leftMixedValue, actualSecantB_eq_rightMixedValue]
  simp only [leftMixedValue, rightMixedValue, mappedMixedCoefficients,
    map_add, map_mul, map_pow, map_one, MvPolynomial.map_C,
    coefficientConjugation_planeT, coefficientConjugation_planeU, hcoeff, hα, hβ]

theorem actualSecantB_conjugation
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl) (α : E)
    (G : MvPolynomial (Fin 4) E)
    (hGExchange : MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G) :
    MvPolynomial.map σ.toRingHom (actualSecantB α (σ α) G) = actualSecantA α (σ α) G := by
  rw [← actualSecantA_conjugation σ hσsq α G hGExchange]
  exact polynomial_conjugation_involutive σ hσsq _

def leftEndpoint (C : Basis (Fin 4) E (Fin 4 → E)) (α : E) :
    Fin 4 → MvPolynomial SecantPlaneIndex E :=
  fun m => MvPolynomial.C (C 0 m) + (planeT + MvPolynomial.C α * planeU) * MvPolynomial.C (C 1 m)

def rightEndpoint (C : Basis (Fin 4) E (Fin 4 → E)) (β : E) :
    Fin 4 → MvPolynomial SecantPlaneIndex E :=
  fun m => MvPolynomial.C (C 2 m) + (planeT + MvPolynomial.C β * planeU) * MvPolynomial.C (C 3 m)

theorem pairedEndpoint_conjugation
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) (α : E) :
    (∀ m, MvPolynomial.map σ.toRingHom (leftEndpoint C α m) = rightEndpoint C (σ α) m) ∧
    (∀ m, MvPolynomial.map σ.toRingHom (rightEndpoint C (σ α) m) = leftEndpoint C α m) := by
  have h₀ (m) : σ.toRingHom (C 0 m) = C 2 m := (hPair 0 m).symm
  have h₁ (m) : σ.toRingHom (C 1 m) = C 3 m := (hPair 1 m).symm
  have h₂ (m) : σ.toRingHom (C 2 m) = C 0 m := by
    exact paired_basis_slots_exchange σ hσsq C hPair 2 m
  have h₃ (m) : σ.toRingHom (C 3 m) = C 1 m := by
    exact paired_basis_slots_exchange σ hσsq C hPair 3 m
  have hα : σ.toRingHom α = σ α := rfl
  have hβ : σ.toRingHom (σ α) = α := DFunLike.congr_fun hσsq α
  constructor <;> intro m
  · simp only [leftEndpoint, rightEndpoint, map_add, map_mul,
      MvPolynomial.map_C, coefficientConjugation_planeT,
      coefficientConjugation_planeU, h₀, h₁, hα]
  · simp only [leftEndpoint, rightEndpoint, map_add, map_mul,
      MvPolynomial.map_C, coefficientConjugation_planeT,
      coefficientConjugation_planeU, h₂, h₃, hβ]

def originalAmbientResidual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) : Fin 4 → MvPolynomial SecantPlaneIndex E :=
  fun m => actualSecantB α β G * leftEndpoint C α m -
    actualSecantA α β G * rightEndpoint C β m

theorem originalAmbientResidual_antiInvariant
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) (α : E)
    (G : MvPolynomial (Fin 4) E)
    (hGExchange : MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G) :
    ∀ m, MvPolynomial.map σ.toRingHom (originalAmbientResidual C α (σ α) G m) =
      -originalAmbientResidual C α (σ α) G m := by
  obtain ⟨hp, hq⟩ := pairedEndpoint_conjugation σ hσsq C hPair α
  exact residualVector_antiInvariant (MvPolynomial.map σ.toRingHom)
    (actualSecantA α (σ α) G) (actualSecantB α (σ α) G)
    (leftEndpoint C α) (rightEndpoint C (σ α))
    (actualSecantA_conjugation σ hσsq α G hGExchange)
    (actualSecantB_conjugation σ hσsq α G hGExchange) hp hq

/-- The native descent theorem puts its coordinate index in the coefficient
field universe. Lift the four ambient slots, then restrict back to their
original indices without changing the polynomial-variable universe. -/
private theorem conjugate_residual_finFour_coordinates_descend
    [FiniteDimensional k E] [IsGalois k E]
    {J : Type v} (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (h₂ : finrank k E = 2) (A B : MvPolynomial J E)
    (p q : Fin 4 → MvPolynomial J E)
    (hA : MvPolynomial.map σ.toRingHom A = B)
    (hB : MvPolynomial.map σ.toRingHom B = A)
    (hp : ∀ m, MvPolynomial.map σ.toRingHom (p m) = q m)
    (hq : ∀ m, MvPolynomial.map σ.toRingHom (q m) = p m) :
    ∃ δ : E, δ ≠ 0 ∧ ∃ r : Fin 4 → MvPolynomial J k,
      ∀ m, MvPolynomial.map (algebraMap k E) (r m) =
        MvPolynomial.C δ * (B * p m - A * q m) := by
  obtain ⟨δ, hδ, r, hr⟩ :=
    conjugate_residual_polynomial_coordinates_descend
      (I := ULift.{u} (Fin 4)) σ hσ h₂ A B
      (fun i => p i.down) (fun i => q i.down) hA hB
      (fun i => hp i.down) (fun i => hq i.down)
  exact ⟨δ, hδ, (fun m => r (ULift.up m)), fun m => hr (ULift.up m)⟩

/-- No endpoint/exchange certificate is assumed here. The paired C is
constructed by packet003 from the original lines; the original ground
cubic itself gives the polynomial exchange. All varying secant coordinates
are then genuine ground polynomials in the original ambient coordinates. -/
theorem original_ground_cubic_varying_residual_descends
    [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2) (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) (α : E)
    (F : MvPolynomial (Fin 4) k) :
    let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
    ∃ δ : E, δ ≠ 0 ∧ ∃ r : Fin 4 → MvPolynomial SecantPlaneIndex k,
      ∀ m, MvPolynomial.map (algebraMap k E) (r m) =
        MvPolynomial.C δ * originalAmbientResidual C α (σ α) G m := by
  let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
  have hσsq := galois_involution_of_finrank_two σ hσ h₂
  have hGExchange := original_cubic_paired_equation_exchange σ hσsq C hPair F
  refine conjugate_residual_finFour_coordinates_descend σ hσ h₂
    (actualSecantA α (σ α) G) (actualSecantB α (σ α) G)
    (leftEndpoint C α) (rightEndpoint C (σ α))
    (actualSecantA_conjugation σ hσsq α G hGExchange)
    (actualSecantB_conjugation σ hσsq α G hGExchange) ?_ ?_
  · exact (pairedEndpoint_conjugation.{u, _, 0} σ hσsq C hPair α).1
  · exact (pairedEndpoint_conjugation.{u, 0, _} σ hσsq C hPair α).2

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
