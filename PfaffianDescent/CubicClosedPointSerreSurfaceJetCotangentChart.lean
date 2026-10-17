import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAlgebra

/-! # Actual eliminated cubic-chart square-zero quotients -/
noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The normalized polynomial coordinate elimination literally preserves
square-zero jet evaluation. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_coordinateOne_jet
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0) (i : Fin 4) :
    (aeval (fun j : {j : Fin 4 // j ≠ i} => cubicSurfaceCoordinateJet U i j.1)).comp
      (coordinateOneEvaluation (R := K) i) = aeval (cubicSurfaceCoordinateJet U i) := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases h : j = i
  · subst j
    simp [coordinateOneEvaluation, cubicSurfaceCoordinateJet, hdiag,
      TrivSqZeroExt.algebraMap_eq_inl]
  · simp [coordinateOneEvaluation, h]

/-- The actual square-zero jet descends through the literal principal
presentation of the actual normalized cubic chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_chartMap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0) :
    letI : Algebra K (ChartRing (equationIdeal p hp) i) :=
      (chartBaseMap (equationIdeal p hp) i).toAlgebra
    ChartRing (equationIdeal p hp) i →ₐ[K] CubicSurfaceFirstJet K := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I i) := (chartBaseMap I i).toAlgebra
  let e : MvPolynomial {j : Fin 4 // j ≠ i} K →ₐ[K] ChartRing I i :=
    aeval (fun j => chartCoordinate I i j.1)
  let v : MvPolynomial {j : Fin 4 // j ≠ i} K →ₐ[K] CubicSurfaceFirstJet K :=
    aeval (fun j => cubicSurfaceCoordinateJet U i j.1)
  let h := smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 i
  have he : Function.Surjective e := h.1
  have hker : RingHom.ker e.toRingHom = Ideal.span
      ({coordinateOneEvaluation i p} : Set (MvPolynomial {j : Fin 4 // j ≠ i} K)) := h.2.1
  have hle : RingHom.ker e.toRingHom ≤ RingHom.ker v.toRingHom := by
    rw [hker]
    apply Ideal.span_le.mpr
    rintro q rfl
    change v (coordinateOneEvaluation i p) = 0
    rw [← AlgHom.comp_apply, cubicClosedPointSerreSurfaceJetCotangent_coordinateOne_jet U hdiag i]
    exact hzero
  exact AlgHom.liftOfSurjective e he v hle

/-- The chart quotient agrees literally with the original polynomial jet. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_chartMap_eval
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0)
    (q : MvPolynomial (Fin 4) K) :
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I i) := (chartBaseMap I i).toAlgebra
    cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero
      (aeval (chartCoordinate I i) q) = aeval (cubicSurfaceCoordinateJet U i) q := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I i) := (chartBaseMap I i).toAlgebra
  let e : MvPolynomial {j : Fin 4 // j ≠ i} K →ₐ[K] ChartRing I i :=
    aeval (fun j => chartCoordinate I i j.1)
  have hc : e (coordinateOneEvaluation i q) = aeval (chartCoordinate I i) q := by
    exact DFunLike.congr_fun
      (smoothCubic_eliminatedChartMap_comp_coordinateOneEvaluation p hp i) q
  dsimp only
  rw [← hc]
  simp only [cubicClosedPointSerreSurfaceJetCotangent_chartMap]
  dsimp only [e, I]
  rw [AlgHom.liftOfSurjective_apply]
  have hv := DFunLike.congr_fun
    (cubicClosedPointSerreSurfaceJetCotangent_coordinateOne_jet U hdiag i) q
  exact hv

/-- Actual full tangent-spanning makes the native chart jet quotient
surjective; no coordinate-ring dimension is supplied. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_chartMap_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective (Fintype.linearCombination K (U i.castSucc)))
    (i : Fin 3) (hzero : aeval (cubicSurfaceCoordinateJet U i.castSucc) p = 0) :
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I i.castSucc) := (chartBaseMap I i.castSucc).toAlgebra
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i.castSucc hzero) := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I i.castSucc) := (chartBaseMap I i.castSucc).toAlgebra
  dsimp only
  intro v
  obtain ⟨q, hq⟩ := cubicSurfaceCoordinateJet_aeval_surjective U hdiag hU i v
  exact ⟨aeval (chartCoordinate I i.castSucc) q,
    (cubicClosedPointSerreSurfaceJetCotangent_chartMap_eval p hp hp0 U hdiag
      i.castSucc hzero q).trans hq⟩

end PfaffianDescent
