import PfaffianDescent.CorayOriginalGenericFullJetFractionLift
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A genuine native generic derivation and its dimension-two universal
Kähler isomorphism, constructed from the actual original fieldjet.
No tangent rank/open certificate is supplied. SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The square-zero part of a fieldjet with identity residue is a genuine
K derivation. Its coefficient identity gives actual K-linearity. -/
def nativeFieldJetDerivation {K F : Type u} [Field K] [Field F] [Algebra K F]
    (ell : F →+* SurfacePlaneJet F) (hfst : ∀ x, (ell x).fst = x)
    (hcoeff : ∀ c : K, ell (algebraMap K F c) = TrivSqZeroExt.inl (algebraMap K F c)) :
    Derivation K F (Fin 2 → F) where
  toLinearMap :=
    { toFun := fun x => (ell x).snd
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        change (ell (c • x)).snd = c • (ell x).snd
        rw [Algebra.smul_def, map_mul, hcoeff]
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
          zero_smul, smul_zero, add_zero]
        exact algebraMap_smul F c (ell x).snd }
  map_one_eq_zero' := by change (ell 1).snd = 0; rw [map_one]; rfl
  leibniz' := fun x y => by
    change (ell (x * y)).snd = x • (ell y).snd + y • (ell x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]

/-- ORIGINAL smoothness constructs a genuine native generic derivation
whose coordinate directions are the actual pivot row. The universal
map Ω[F/K] -> F² is proved bijective from row-spanning and actual Ωdim2. -/
theorem smoothOriginalCubic_generic_exists_nativeDerivationKaehlerIso001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    ∃ pivot : Fin 3,
      MvPolynomial.aeval z (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 ∧
      ∃ d : Derivation K F (Fin 2 → F),
      Function.Bijective d.liftKaehlerDifferential ∧
      ∀ i : Fin 4, d (z i) = PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g := @affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  obtain ⟨pivot, hgrad, ell, hfst, hcoeff, hcoord⟩ :=
    smoothOriginalCubic_generic_exists_nativeFieldJet001 p hp hp0 j
  let d := nativeFieldJetDerivation ell hfst hcoeff
  let row : Fin 4 → Fin 2 → F := PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
    (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot
  have hd : ∀ i, d (z i) = row i := by
    intro i
    have h := congrArg TrivSqZeroExt.snd (hcoord i)
    change (ell (z i)).snd = row i
    simpa only [surfacePlaneJetCoordinates, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, z, row] using h
  have hsurj : Function.Surjective d.liftKaehlerDifferential := by
    intro w
    obtain ⟨c, hc⟩ := PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_surjective j
      (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot w
    refine ⟨∑ i : Fin 4, c i • KaehlerDifferential.D K F (z i), ?_⟩
    rw [map_sum]
    calc
      (∑ t : Fin 4, d.liftKaehlerDifferential (c t • KaehlerDifferential.D K F (z t))) =
          ∑ t : Fin 4, c t • row t := by
        apply Finset.sum_congr rfl
        intro t _
        rw [map_smul]
        exact congrArg (fun v : Fin 2 → F => c t • v)
          ((d.liftKaehlerDifferential_comp_D (z t)).trans (hd t))
      _ = w := by simpa only [Fintype.linearCombination_apply, row] using hc
  have hdim := smoothCubic_originalFunctionFieldKaehler_finrank_two p hp hp0 j
  letI : Module.Finite F (KaehlerDifferential K F) := Module.finite_of_finrank_eq_succ hdim
  have hbij : Function.Bijective d.liftKaehlerDifferential :=
    OrzechProperty.bijective_of_surjective_of_finrank_le d.liftKaehlerDifferential hsurj
      (by rw [hdim, Module.finrank_fin_fun])
  exact ⟨pivot, hgrad, d, hbij, hd⟩

end PfaffianDescent.Coray
end
