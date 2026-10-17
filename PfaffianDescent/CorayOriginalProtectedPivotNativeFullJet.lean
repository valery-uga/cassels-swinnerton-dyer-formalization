import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary

/-! The OWN original nonzero pivot at an actual original chart point
constructs its literal polynomial fulljet and normalized anchor. This
removes the need to supply those conclusions to the native Ksection
caller, without selecting or equating a different pivot. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A protected original chart pivot produces the exact OWN native
fulljet. Original p/K, fieldpoint, coefficient triangle, all nilpotent
jet values and the pivot are unchanged. No smooth/jet/anchor conclusion
is supplied as a premise. -/
theorem cubicOriginalChartFieldPoint_nonzeroOriginalPivot_nativeFullJet001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (pivot : Fin 3)
    (hPivot : g ((pderiv (j.succAbove pivot) p).eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) ≠ 0) :
    let z : Fin 4 → M := fun s => g (chartCoordinate (equationIdeal p hp) j s)
    let v : Fin 2 → Fin 4 → M := fun r s => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun l => g ((pderiv (j.succAbove l) p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j))) pivot s r
    p.eval₂ (algebraMap K M) z = 0 ∧
      p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0 ∧
      surfacePlaneJetCoordinates z v j = 1 := by
  let I := equationIdeal p hp
  let z : Fin 4 → M := fun s => g (chartCoordinate I j s)
  let f := algebraMap K M
  let gradient : Fin 3 → M := fun l => g ((pderiv (j.succAbove l) p).eval₂
    (chartBaseMap I j) (chartCoordinate I j))
  let v : Fin 2 → Fin 4 → M := fun r s =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j gradient pivot s r
  have hz : z j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (Set.mem_singleton p)
  have hpz : p.eval₂ (algebraMap K M) z = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hpI)
    rw [hom_eval₂, hBase, map_zero] at h
    exact h
  have hGradient : (fun l => aeval z (pderiv (j.succAbove l) (p.map f))) = gradient := by
    funext l
    have h := MvPolynomial.hom_eval₂ (pderiv (j.succAbove l) p) (chartBaseMap I j) g (chartCoordinate I j)
    rw [hBase] at h
    symm
    simpa only [MvPolynomial.aeval_eq_eval, MvPolynomial.pderiv_map,
      MvPolynomial.eval_map] using h
  have hpMz : aeval z (p.map f) = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map] using hpz
  have hpivotM : aeval z (pderiv (j.succAbove pivot) (p.map f)) ≠ 0 := by
    rw [congrFun hGradient pivot]
    exact hPivot
  have hCoordinates : surfacePlaneJetCoordinates z v =
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot :
        Fin 4 → SurfacePlaneJet M) := by
    change surfacePlaneJetCoordinates z
      (fun r s => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j gradient pivot s r) = _
    rw [← hGradient]
    rfl
  have hCoeff : (algebraMap M (SurfacePlaneJet M)).comp f = algebraMap K (SurfacePlaneJet M) :=
    (IsScalarTower.algebraMap_eq K M (SurfacePlaneJet M)).symm
  have hpJet : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0 := by
    rw [hCoordinates]
    have h := PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet_cubic (p.map f) j z pivot hpMz hpivotM
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at h
    change p.eval₂ ((algebraMap M (SurfacePlaneJet M)).comp f)
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot) = 0 at h
    rw [hCoeff] at h
    exact h
  have hAnchor : surfacePlaneJetCoordinates z v j = 1 := by
    have hRow : (fun r => v r j) = 0 := by
      funext r
      exact congrFun (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag j gradient pivot) r
    change (inl (z j) + inr (fun r => v r j) : SurfacePlaneJet M) = 1
    rw [hz, hRow]
    simp only [TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.inl_one]
  exact ⟨hpz, hpJet, hAnchor⟩

end PfaffianDescent.Coray
