import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentChart

/-! # Native vertex ideal and cubic derivative compatibility

The missing subsequent adapter is Γ of the actual point pullback of I(+3)
versus this affine ideal cotangent quotient, including the actual positive-
twist chart unit. No such comparison is assumed or asserted in this file.
-/
noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_map_apply
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (a : cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    cubicClosedPointSerreSurfaceJetCotangent_map φ
      ((cubicClosedPointSerreSurfaceJetCotangent_ideal φ).toCotangent a) =
      cubicClosedPointSerreSurfaceJetCotangent_derivative φ a := rfl

theorem cubicClosedPointSerreSurfaceJetCotangent_map_surjective
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) (hφ : Function.Surjective φ) :
    Function.Surjective (cubicClosedPointSerreSurfaceJetCotangent_map φ) := by
  intro v
  obtain ⟨a, ha⟩ := cubicClosedPointSerreSurfaceJetCotangent_derivative_surjective φ hφ v
  exact ⟨(cubicClosedPointSerreSurfaceJetCotangent_ideal φ).toCotangent a, ha⟩

/-- The residue of literal polynomial jet evaluation is literal vertex evaluation. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_fst_eval
    (U : Fin 4 → Fin 4 → Fin 2 → K) (i : Fin 4)
    (q : MvPolynomial (Fin 4) K) :
    (aeval (cubicSurfaceCoordinateJet U i) q).fst =
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) q := by
  have h : (TrivSqZeroExt.fstHom K K (Fin 2 → K)).comp
      (aeval (cubicSurfaceCoordinateJet U i)) =
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [cubicSurfaceCoordinateJet, cubicClosedPointSerreSurfaceJets_vertex]
  exact DFunLike.congr_fun h q

local instance cubicClosedPointSerreSurfaceJetCotangent_chartAlgebra
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (i : Fin 4) :
    Algebra K (ChartRing (equationIdeal p hp) i) :=
  (chartBaseMap (equationIdeal p hp) i).toAlgebra

/-- The actual chart residue specialization is the literal vertex evaluation. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_chart_residue_eval
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0)
    (q : MvPolynomial (Fin 4) K) :
    cubicClosedPointSerreSurfaceJetCotangent_residueMap
      (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero)
      (aeval (chartCoordinate (equationIdeal p hp) i) q) =
        aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) q := by
  change (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero
    (aeval (chartCoordinate (equationIdeal p hp) i) q)).fst = _
  rw [cubicClosedPointSerreSurfaceJetCotangent_chartMap_eval]
  exact cubicClosedPointSerreSurfaceJetCotangent_fst_eval U i q

/-- The chart's actual residue ideal pulls back to the literal vertex kernel. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_chart_ideal_comap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0) :
    (cubicClosedPointSerreSurfaceJetCotangent_ideal
      (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero)).comap
      (aeval (R := K) (chartCoordinate (equationIdeal p hp) i)).toRingHom =
    RingHom.ker (aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i)).toRingHom := by
  ext q
  change cubicClosedPointSerreSurfaceJetCotangent_residueMap
    (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero)
    (aeval (chartCoordinate (equationIdeal p hp) i) q) = 0 ↔ _
  rw [cubicClosedPointSerreSurfaceJetCotangent_chart_residue_eval]
  rfl

/-- A polynomial vanishing at the vertex gives an actual element of the
actual chart residue ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_chart_ideal_polynomial
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0)
    (q : MvPolynomial (Fin 4) K)
    (hq : aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) q = 0) :
    cubicClosedPointSerreSurfaceJetCotangent_ideal
      (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero) :=
  ⟨aeval (chartCoordinate (equationIdeal p hp) i) q, by
    change cubicClosedPointSerreSurfaceJetCotangent_residueMap _ _ = 0
    rw [cubicClosedPointSerreSurfaceJetCotangent_chart_residue_eval]
    exact hq⟩

/-- The actual ideal derivative is exactly the original polynomial jet's
square-zero component, with no supplied section comparison. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_chart_derivative_polynomial
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (U : Fin 4 → Fin 4 → Fin 2 → K) (hdiag : ∀ i, U i i = 0)
    (i : Fin 4) (hzero : aeval (cubicSurfaceCoordinateJet U i) p = 0)
    (q : MvPolynomial (Fin 4) K)
    (hq : aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) q = 0) :
    cubicClosedPointSerreSurfaceJetCotangent_derivative
      (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero)
      (cubicClosedPointSerreSurfaceJetCotangent_chart_ideal_polynomial
        p hp hp0 U hdiag i hzero q hq) = (aeval (cubicSurfaceCoordinateJet U i) q).snd := by
  change (cubicClosedPointSerreSurfaceJetCotangent_chartMap p hp hp0 U hdiag i hzero
    (aeval (chartCoordinate (equationIdeal p hp) i) q)).snd = _
  rw [cubicClosedPointSerreSurfaceJetCotangent_chartMap_eval]

end PfaffianDescent
