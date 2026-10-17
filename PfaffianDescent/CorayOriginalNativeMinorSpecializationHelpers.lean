import PfaffianDescent.CorayOriginalGenericFullJetFractionLift
import PfaffianDescent.CorayNativeSurfaceJetRowWeightedSum

/-! Literal pointwise native chart-jet identities on a fixed pivot and
projective denominator open, for spreading the actual original minor.
No desired rank certificate supplied. SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual cubic chart fieldpoint on the fixed pivot-open constructs
its full cubic jet relation and normalized anchor for that SAME pivot. -/
theorem cubicChartFieldPoint_pivotFullJet_relation_anchor001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (pivot : Fin 3)
    (hPivot : (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M)
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) ≠ 0) :
    let z : Fin 4 → M := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    let v : Fin 2 → Fin 4 → M := fun r i =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r
    p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0 ∧
      surfacePlaneJetCoordinates z v j = 1 := by
  let I := equationIdeal p hp
  let z : Fin 4 → M := fun i => g (chartCoordinate I j i)
  let v : Fin 2 → Fin 4 → M := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r
  have hz : z j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (Set.mem_singleton p)
  have hpz : p.eval₂ (algebraMap K M) z = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hpI)
    rw [hom_eval₂, hBase, map_zero] at h
    exact h
  let f := algebraMap K M
  have hpMz : aeval z (p.map f) = 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.eval_map] using hpz
  have hpivotM : aeval z (pderiv (j.succAbove pivot) (p.map f)) ≠ 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hPivot
  have hCoordinates : surfacePlaneJetCoordinates z v =
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot :
        Fin 4 → SurfacePlaneJet M) := rfl
  have hCoeff : (algebraMap M (SurfacePlaneJet M)).comp f =
      algebraMap K (SurfacePlaneJet M) :=
    (IsScalarTower.algebraMap_eq K M (SurfacePlaneJet M)).symm
  constructor
  · rw [hCoordinates]
    have h := PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet_cubic
      (p.map f) j z pivot hpMz hpivotM
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at h
    change p.eval₂ ((algebraMap M (SurfacePlaneJet M)).comp f)
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot) = 0 at h
    rw [hCoeff] at h
    exact h
  · have hRow : (fun r => v r j) = 0 := by
      funext r
      exact congrFun (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag j
        (fun t => aeval z (pderiv (j.succAbove t) (p.map f))) pivot) r
    change (inl (z j) + inr (fun r => v r j) : SurfacePlaneJet M) = 1
    rw [hz, hRow]
    simp only [TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.inl_one]

/-- The native target chart multiplication relation computes its exact
normalized tangent row. It uses the entire square-zero jet, retaining
its nilpotent denominator component. -/
theorem nativeLocalizedProjectiveChartMap_fulljet_row_eq_quotientRule001
    {K R M : Type u} [CommRing K] [CommRing R] [Field M]
    {m : ℕ} (f : K →+* R) (x : Fin m → R) (a : Fin m)
    (g : R →+* M) (J : R →+* SurfacePlaneJet M)
    (hfst : ∀ t, (J t).fst = g t) (ha : g (x a) ≠ 0) (i : Fin m) (r : Fin 2) :
    let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (by rw [hfst]; exact isUnit_iff_ne_zero.mpr ha)
    let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
    (mu (nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i))).snd r =
      ((J (x i)).snd r * g (x a) - g (x i) * (J (x a)).snd r) / g (x a) ^ 2 := by
  let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (by rw [hfst]; exact isUnit_iff_ne_zero.mpr ha)
  let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
  let w : SurfacePlaneJet M := mu (nativeLocalizedProjectiveChartMap f x a
    (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i))
  have hApply (t : R) : mu (algebraMap R (Localization.Away (x a)) t) = J t :=
    RingHom.congr_fun (IsLocalization.Away.lift_comp (x a) hUnit) t
  have hData := nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a
  have hNative : nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i) *
      algebraMap R (Localization.Away (x a)) (x a) =
      algebraMap R (Localization.Away (x a)) (x i) := by
    rw [hData.2.1 i, mul_assoc]
    rw [show IsLocalization.Away.invSelf (x a) *
      algebraMap R (Localization.Away (x a)) (x a) = 1 from
        (mul_comm _ _).trans (IsLocalization.Away.mul_invSelf (x a)), mul_one]
  have hMult : w * J (x a) = J (x i) := by
    have h := congrArg mu hNative
    rw [map_mul, hApply, hApply] at h
    exact h
  have hResidue : w.fst * g (x a) = g (x i) := by
    have h := congrArg TrivSqZeroExt.fst hMult
    simpa only [TrivSqZeroExt.fst_mul, hfst] using h
  have hDirection : w.fst * (J (x a)).snd r + g (x a) * w.snd r = (J (x i)).snd r := by
    have h := congrArg (fun t : SurfacePlaneJet M => t.snd r) hMult
    simpa only [TrivSqZeroExt.snd_mul, Pi.add_apply, Pi.smul_apply,
      op_smul_eq_smul, smul_eq_mul, hfst] using h
  change w.snd r = _
  apply (eq_div_iff (pow_ne_zero 2 ha)).mpr
  linear_combination g (x a) * hDirection - (J (x a)).snd r * hResidue

/-- Exact original polynomial chart representatives evaluate under the
native fulljet to the original cleared pivot direction numerators. -/
theorem cubicNormalizedFullJetChartMap_polynomialDirection_eq_cleared001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (pivot : Fin 3)
    (hPivot : (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M)
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) ≠ 0)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => g (chartCoordinate (equationIdeal p hp) j i))
        (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => aeval (fun i => g (chartCoordinate (equationIdeal p hp) j i))
            (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r)) = 0)
    (hAnchor : surfacePlaneJetCoordinates (fun i => g (chartCoordinate (equationIdeal p hp) j i))
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => aeval (fun i => g (chartCoordinate (equationIdeal p hp) j i))
          (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r) j = 1)
    (q : MvPolynomial (Fin 4) K) (r : Fin 2) :
    let I := equationIdeal p hp
    let z : Fin 4 → M := fun i => g (chartCoordinate I j i)
    let grad : Fin 3 → ChartRing I j := fun t =>
      (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
    let v : Fin 2 → Fin 4 → M := fun r i =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r
    (cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).snd r =
      g (grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) q).eval₂
          (chartBaseMap I j) (chartCoordinate I j) -
        grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) q).eval₂
          (chartBaseMap I j) (chartCoordinate I j)) / g (grad pivot) := by
  let I := equationIdeal p hp
  let z : Fin 4 → M := fun i => g (chartCoordinate I j i)
  let grad : Fin 3 → ChartRing I j := fun t =>
    (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
  let v : Fin 2 → Fin 4 → M := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  have hCoeff : J.comp (chartBaseMap I j) = algebraMap K (SurfacePlaneJet M) := by
    apply RingHom.ext
    intro c
    exact cubicNormalizedFullJetChartMap_base001 p hp j z v hpJ hAnchor c
  have hCoord : (fun i => J (chartCoordinate I j i)) = surfacePlaneJetCoordinates z v := by
    funext i
    exact cubicNormalizedFullJetChartMap_coordinate001 p hp j z v hpJ hAnchor i
  have hEval (q' : MvPolynomial (Fin 4) K) :
      g (q'.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = q'.eval₂ (algebraMap K M) z := by
    rw [hom_eval₂, hBase]
  have hGradFamily : (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) =
      (fun t => g (grad t)) := by
    funext t
    rw [hEval]
    simp only [MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map]
  have hG : g (grad pivot) ≠ 0 := by rwa [hEval]
  change (J (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).snd r = _
  rw [hom_eval₂, hCoeff, hCoord, surfacePlaneJet_tangent_value_eq_directional_derivative]
  change (∑ i, (pderiv i q).eval₂ (algebraMap K M) z *
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r) = _
  rw [hGradFamily, nativeSurfaceJetRow_weighted_sum001]
  rw [← hEval, ← hEval, map_sub, map_mul, map_mul]
  simp only [grad, I] at hG ⊢
  field_simp [hG]
  <;> ring

end PfaffianDescent.Coray
end
