import PfaffianDescent.CorayDisjointAuxiliaryCubicClosedPoint
import PfaffianDescent.CorayClosedPointResiduePresentation
import PfaffianDescent.CorayDoubleJetCurveChoice
import AllCharacteristics.ProjectiveFiberSmoothness

/-! SOURCE ONLY / UNVERIFIED. Actual original P, constructed disjoint cubic
closed A, actual original residue fields and actual smooth Jacobian-pivot
jet select a genuine boundary-degree q. No jet-surjectivity, GI, reduced
cycle or original/auxiliary curve regularity premise is supplied. These are
polynomial construction outputs; own intersection point/stalk transport is
separate and is not claimed by this leaf. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exactChartMap_groundAffine_coordinates
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (g : ChartRing I j →+* M) (hgs : Function.Surjective g)
    (hgbase : g.comp (chartBaseMap I j) = algebraMap K M) :
    let x : Fin 4 → M := fun i => g (chartCoordinate I j i)
    x j = 1 ∧
      Function.Surjective (eval₂Hom (algebraMap K M)
        (fun r : Fin 3 => x (j.succAbove r))) ∧
      ∀ a ∈ I.toIdeal, a.eval₂ (algebraMap K M) x = 0 := by
  let x : Fin 4 → M := fun i => g (chartCoordinate I j i)
  have hx : x j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have he : eval₂Hom (algebraMap K M) x =
      g.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply RingHom.ext
    intro a
    change a.eval₂ (algebraMap K M) x = g (a.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [hom_eval₂, hgbase]
  have hsurj : Function.Surjective (eval₂Hom (algebraMap K M) x) := by
    rw [he]
    exact hgs.comp (eval₂_chartCoordinate_surjective I j)
  refine ⟨hx, normalizedGroundAffine_eval_surjective j x hx hsurj, ?_⟩
  intro a ha
  change eval₂Hom (algebraMap K M) x a = 0
  rw [he, RingHom.comp_apply]
  change g (a.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0
  rw [eval₂_chartCoordinate_eq_zero_of_mem I j a ha, map_zero]

/-- At boundary curve degree m+1>=4, the original point degree equals the
previous cubic section count G_(m+1). A disjoint ORIGINAL closed cubic point
and the q with its ACTUAL full tangent jet zero are constructed. Nonzero q
modulo p follows from the actual section count, not a surjectivity input. -/
theorem boundary_actualOriginalPoint_exists_disjoint_cubicPoint_fullJet_equation
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) :
    ∃ A : closedPoints (hypersurface p hp),
      A ≠ P ∧ (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧
      let S := hypersurface p hp
      let pi := hypersurfaceToBase p hp
      letI := AllCharacteristics.pointAlgebra pi P.1
      letI := AllCharacteristics.pointAlgebra pi A.1
      ∃ (anchorP : Fin 4) (y : Fin 4 → S.residueField P.1)
        (anchorA : Fin 4) (z : Fin 4 → S.residueField A.1)
        (pivot : Fin 3) (q : MvPolynomial (Fin 4) K),
        (∃ gP : ChartRing (equationIdeal p hp) anchorP →+* S.residueField P.1,
          gP.comp (chartBaseMap (equationIdeal p hp) anchorP) = algebraMap K (S.residueField P.1) ∧
          Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) anchorP =
            S.fromSpecResidueField P.1 ∧
          y = (fun i => gP (chartCoordinate (equationIdeal p hp) anchorP i))) ∧
        (∃ gA : ChartRing (equationIdeal p hp) anchorA →+* S.residueField A.1,
          gA.comp (chartBaseMap (equationIdeal p hp) anchorA) = algebraMap K (S.residueField A.1) ∧
          Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) anchorA =
            S.fromSpecResidueField A.1 ∧
          z = (fun i => gA (chartCoordinate (equationIdeal p hp) anchorA i))) ∧
        y anchorP = 1 ∧
        Function.Surjective (eval₂Hom (algebraMap K (S.residueField P.1))
          (fun r : Fin 3 => y (anchorP.succAbove r))) ∧
        z anchorA = 1 ∧
        Function.Surjective (eval₂Hom (algebraMap K (S.residueField A.1))
          (fun r : Fin 3 => z (anchorA.succAbove r))) ∧
        p.eval₂ (algebraMap K (S.residueField P.1)) y = 0 ∧
        p.eval₂ (algebraMap K (S.residueField A.1)) z = 0 ∧
        (pderiv (anchorA.succAbove pivot) p).eval₂
          (algebraMap K (S.residueField A.1)) z ≠ 0 ∧
        q.IsHomogeneous (m + 1) ∧
        q.eval₂ (algebraMap K (S.residueField P.1)) y = 0 ∧
        q.eval₂ ((algebraMap (S.residueField A.1)
            (PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1))).comp
          (algebraMap K (S.residueField A.1)))
          (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
            (p.map (algebraMap K (S.residueField A.1))) anchorA z pivot) = 0 ∧
        q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  classical
  letI : Infinite K := CharZero.infinite K
  obtain ⟨A, hAP, hAdegree⟩ :=
    hypersurface_exists_disjoint_cubicClosedPoint_of_no_section p hp hp0 P hPcop hno
  refine ⟨A, hAP, hAdegree, ?_⟩
  let S := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  let I := equationIdeal p hp
  letI := AllCharacteristics.pointAlgebra pi P.1
  letI := AllCharacteristics.pointAlgebra pi A.1
  let L := S.residueField P.1
  let M := S.residueField A.1
  letI : Module.Finite K L := AllCharacteristics.closedPoint_moduleFinite pi P
  letI : Module.Finite K M := AllCharacteristics.closedPoint_moduleFinite pi A
  have hdimP : finrank K L = pi.residueDegree P.1 :=
    AllCharacteristics.closedPoint_finrank_eq_residueDegree pi P
  have hdimA : finrank K M = pi.residueDegree A.1 :=
    AllCharacteristics.closedPoint_finrank_eq_residueDegree pi A
  letI : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (S.fromSpecResidueField A.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp A.2
  obtain ⟨anchorP, gP, hgsP, hgbaseP, hgpointP⟩ := PfaffianDescent.closed_projective_point_chart
    (K := K) (L := S.residueField P.1) I (S.fromSpecResidueField P.1) (AllCharacteristics.pointAlgebra_spec pi P.1).symm
  obtain ⟨anchorA, gA, hgsA, hgbaseA, hgpointA⟩ := PfaffianDescent.closed_projective_point_chart
    (K := K) (L := S.residueField A.1) I (S.fromSpecResidueField A.1) (AllCharacteristics.pointAlgebra_spec pi A.1).symm
  let y : Fin 4 → L := fun i => gP (chartCoordinate I anchorP i)
  let z : Fin 4 → M := fun i => gA (chartCoordinate I anchorA i)
  obtain ⟨hy, hevalP, hzeroP⟩ := exactChartMap_groundAffine_coordinates I anchorP gP hgsP hgbaseP
  obtain ⟨hz, hevalA, hzeroA⟩ := exactChartMap_groundAffine_coordinates I anchorA gA hgsA hgbaseA
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (by simp)
  have hpy : p.eval₂ (algebraMap K L) y = 0 := by
    exact hzeroP p hpI
  have hpz : p.eval₂ (algebraMap K M) z = 0 := by
    exact hzeroA p hpI
  let f := algebraMap K M
  have hpM0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    apply MvPolynomial.map_injective f f.injective
    simpa using h
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hpMz : aeval z (p.map f) = 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.eval_map, f] using hpz
  obtain ⟨pivot, hpivotM⟩ := PfaffianDescent.cubicNormalizedSurfacePoint_exists_nonzero_gradient
    (p.map f) (hp.map f) hpM0 anchorA z hz hpMz
  have hpivot : (pderiv (anchorA.succAbove pivot) p).eval₂ f z ≠ 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hpivotM
  let v : Fin 2 → Fin 4 → M := fun r j =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row anchorA
      (fun t => aeval z (pderiv (anchorA.succAbove t) (p.map f))) pivot j r
  have hdimL : finrank K L = (m + 3).choose 3 - m.choose 3 := hdimP.trans hdegree
  have hdimM : finrank K M = 3 := hdimA.trans hAdegree
  obtain ⟨q, hqhom, hqP, hqjet, hqnot⟩ :=
    exists_boundary_degree_curve_with_degree_three_full_jet p hp hp0 m hm y z v hdimM hdimL
  have hqnative : q.eval₂ ((algebraMap M (PfaffianDescent.CubicSurfaceFirstJet M)).comp f)
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) anchorA z pivot) = 0 := by
    rw [← IsScalarTower.algebraMap_eq K M (PfaffianDescent.CubicSurfaceFirstJet M)]
    change q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0
    exact hqjet
  exact ⟨anchorP, y, anchorA, z, pivot, q,
    ⟨gP, hgbaseP, hgpointP, rfl⟩, ⟨gA, hgbaseA, hgpointA, rfl⟩,
    hy, hevalP, hz, hevalA, hpy, hpz, hpivot, hqhom, hqP, hqnative, hqnot⟩

end PfaffianDescent.Coray
