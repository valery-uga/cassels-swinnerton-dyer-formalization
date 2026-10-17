import PfaffianDescent.OriginalDualCoordinatesAnyChartZeroEntryGeometry
import PfaffianDescent.LinearSubstitutedMatchingLinesInOriginalCubic

/-! SOURCE ONLY, UNVERIFIED. A small proof-valued OUTPUT interface for the
actual matching-line/ground-point or finite FULL-base geometry. This is not
an assumed construction certificate of any public original-Z theorem. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

def OriginalEmbeddedZeroEntryGeometry
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) : Prop :=
  (∃ (M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure k)) (hM : IsUnit M.det)
    (lines : ∀ side : Bool,
      scheme (QuarticNet.coordinateMatchingLineIdeal (K := AlgebraicClosure k) side) ⟶
        hypersurface (map (algebraMap k (AlgebraicClosure k)) p)
          (hp.map (algebraMap k (AlgebraicClosure k)))),
      (∀ side, IsClosedImmersion (lines side)) ∧
      (∀ side, lines side ≫ quotientProjMap
          (equationIdeal (map (algebraMap k (AlgebraicClosure k)) p)
            (hp.map (algebraMap k (AlgebraicClosure k)))) =
        quotientProjMap (QuarticNet.coordinateMatchingLineIdeal side) ≫
          (linearCoordinateChangeAmbientIso M hM).inv) ∧
      (∃ a : Fin 4 → k, a ≠ 0 ∧ aeval a p = 0)) ∨
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal q))

namespace QuarticNet
variable [PerfectField k]
variable {L A : Type u} [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

theorem originalDualCoordinates_any_chart_zero_entry_actual_scheme_geometry
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b j = 1) (hv : v j = 0) (hvne : v ≠ 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hFx : aeval (R := k) x p = 0)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) :
    let U := rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))
    (∀ r s, U r s = -U s r) → (∃ r s, r ≠ s ∧ U r s = 0) →
    OriginalEmbeddedZeroEntryGeometry p hp (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) := by
  classical
  dsimp only
  intro hskew hmissing
  have h := originalDualCoordinates_any_chart_zero_entry_geometry
    eA x j hxj b v hx hb hv hvne full p hp hFx l hl hskew hmissing
  rcases h with hMatching | hFinite
  · obtain ⟨rho, h01, h23, hPoint⟩ := hMatching
    let B := (conjugateBasis full b (conjugate_basis_span b full)).reindex rho.symm
    let M := basisCoordinateMatrix B
    have hM : IsUnit M.det := basisCoordinateMatrix_isUnit B
    obtain ⟨lines, hClosed, hAmbient⟩ := linearSubstituted_matching_lines_in_original_cubic
      (map (algebraMap k (AlgebraicClosure k)) p)
      (hp.map (algebraMap k (AlgebraicClosure k))) M hM h01 h23
    exact Or.inl ⟨M, hM, lines, hClosed, hAmbient, hPoint⟩
  · exact Or.inr hFinite

end QuarticNet
end PfaffianDescent
