import PfaffianDescent.CubicElevenPointNormalizedDerivativeSpan
import PfaffianDescent.CubicGroundChartJetResidue

/-! The ground chart kernel constructs the three actual mixed-field jet
maps, their literal component residues, and all six derivative directions. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPoint_groundChart_exists_derivativeMaps
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hgb : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (α : Fin 11 → (L →ₐ[F] E))
    (y : Fin 11 → Fin 4 → E) (hnz : ∀ k, y k j ≠ 0)
    (hcoords : ∀ k r, α k (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
      (y k j)⁻¹ * y k r)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hzero : ∀ k, aeval (J k) (P.map (algebraMap F E)) = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J))
    (hL : finrank F L ≤ 11)
    (hmem : ∀ q, cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g q = 0 →
      cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0) :
    let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g
    ∃ φ : Fin 3 → (ChartRing (equationIdeal P hP) j →+* CubicSurfaceFirstJet E),
      (∀ k, (TrivSqZeroExt.fstHom E E (Fin 2 → E)).toRingHom.comp (φ k) =
        (α (k.castAdd 8)).toRingHom.comp g) ∧
      ∀ B : Basis (Fin 9) F R.ker,
        Submodule.span E (Set.range (fun k : Fin 9 => fun r : Fin 3 =>
          (φ r ((B k).1.1.eval₂ (chartBaseMap (equationIdeal P hP) j)
            (linearChartCoordinate (equationIdeal P hP)
              (coordinate (equationIdeal P hP) j)
              (coordinate_mem (equationIdeal P hP) j)))).snd)) = ⊤ := by
  have hu : ∀ k, IsUnit (J k j) := by
    intro k
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, hresidue k j]
    exact hnz (k.castAdd 8)
  refine ⟨fun k => cubicGroundChartJetMap P hP j (J k) (hu k) (hzero k), ?_, ?_⟩
  · intro k
    apply cubicGroundChartJetMap_residue_comp P hP j (J k) (hu k) (hzero k)
      g hgb (α (k.castAdd 8))
    intro r
    rw [hresidue k j, hresidue k r]
    exact hcoords (k.castAdd 8) r
  · intro B
    exact cubicElevenPoint_groundKernel_normalizedDerivativeFamily_spans _ hL y J
      hresidue hfull hmem P hP j hu hzero B

end PfaffianDescent
