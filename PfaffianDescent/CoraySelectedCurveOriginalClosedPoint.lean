import PfaffianDescent.CorayHomogeneousCurveChoice
import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ClosedImmersionCyclePushforward

/-! L1: an additional equation vanishing on an EXACT recovered original
residue-field chart gives a SAME original closed point of the literal
selected intersection, preserving the actual cubic point and residue field.
No regularity, integrality, normalization lift, or q selection is asserted.
SOURCE ONLY / UNVERIFIED. Root alone compiles and audits. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual additional q vanishing on the normalized coordinates of an
EXACT chart of the original canonical residue point constructs a closed
point of the literal original p/q scheme. The exact chart recovery is the
installed `closed_projective_point_chart` output, not a point-degree premise.
The canonical curve immersion has an actual residue-field isomorphism at
this point, and its ORIGINAL-K degree equals the original cubic point degree. -/
theorem selectedCurve_originalClosedPoint_of_original_chart_q_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (P : closedPoints (hypersurface p hp)) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        S.fromSpecResidueField P.1 →
      q.eval₂ (algebraMap K (S.residueField P.1))
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 →
      ∃ Q : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
        cubicSecondEquationCurveImmersion p q hp n hq Q.1 = P.1 ∧
        IsIso ((cubicSecondEquationCurveImmersion p q hp n hq).residueFieldMap Q.1) ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 =
          (hypersurfaceToBase p hp).residueDegree P.1 := by
  classical
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro j g hgbase hgpoint hqzero
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let L := S.residueField P.1
  let x : Fin 4 → L := fun i => g (chartCoordinate I j i)
  have heI : ∀ a ∈ I.toIdeal, (eval₂Hom (algebraMap K L) x) a = 0 := by
    intro a ha
    have hz := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j a ha)
    rw [hom_eval₂, hgbase, map_zero] at hz
    exact hz
  have hpzero : (eval₂Hom (algebraMap K L) x) p = 0 :=
    heI p (Ideal.subset_span (Set.mem_singleton p))
  have hspan : J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K L) x) := by
    rw [projectiveIntersectionIdeal_toIdeal]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hpzero
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact hqzero
  have heJ : ∀ a ∈ J.toIdeal, (eval₂Hom (algebraMap K L) x) a = 0 :=
    fun a ha => hspan ha
  let z : CoordinateRing I := coordinate I j
  have hz : z ∈ grading I 1 := coordinate_mem I j
  have hxj : x j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hzOneI : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K L) x) heI) z = 1 := by
    change (eval₂Hom (algebraMap K L) x) (X j) = 1
    simpa only [eval₂Hom_X'] using hxj
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal (eval₂Hom (algebraMap K L) x) heJ)
      (gradedQuotientMap I J le_sup_left z) = 1 := by
    change (eval₂Hom (algebraMap K L) x) (X j) = 1
    simpa only [eval₂Hom_X'] using hxj
  let r : Spec (.of L) ⟶ scheme J := linearNormalizedPointAt J x heJ
    (gradedQuotientMap I J le_sup_left z) ((gradedQuotientMap I J le_sup_left).map_mem hz) hzOneJ
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  have hfactor : r ≫ i = S.fromSpecResidueField P.1 := by
    have hquotient := linearNormalizedPointAt_comp_schemeQuotientMap I J le_sup_left
      x heI heJ z hz hzOneI hzOneJ
    change r ≫ i = linearNormalizedPointAt I x heI z hz hzOneI at hquotient
    rw [hquotient]
    change Spec.map (CommRingCat.ofHom
      (linearNormalizedPointChartMapAt I x heI z hz hzOneI)) ≫ chartι I j = _
    have hmaps : linearNormalizedPointChartMapAt I x heI z hz hzOneI = g := by
      symm
      apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
        I x heI z hz hzOneI g
      · exact hgbase
      · intro k
        rfl
    rw [hmaps]
    exact hgpoint
  letI : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (r ≫ i) := hfactor.symm ▸ inferInstance
  letI : IsClosedImmersion r := IsClosedImmersion.of_comp r i
  let b : Spec (.of L) := IsLocalRing.closedPoint L
  let Q : closedPoints (scheme J) := ⟨r b, by
    change IsClosed ({r b} : Set (scheme J))
    rw [← Set.image_singleton]
    exact r.isClosedMap _ isClosed_singleton⟩
  have hpoint : i Q.1 = P.1 := by
    change (r ≫ i) b = P.1
    rw [hfactor]
    exact Scheme.fromSpecResidueField_apply (X := S) P.1 b
  letI : IsIso (i.residueFieldMap Q.1) := isIso_residueFieldMap_of_surjectiveOnStalks i Q.1
  refine ⟨Q, hpoint, inferInstance, ?_⟩
  have hd := residueDegree_comp_of_residueFieldMap_isIso i (hypersurfaceToBase p hp) Q.1
  rw [cubicSecondEquationCurveImmersion_toBase, hpoint] at hd
  exact hd

/-- Genuine L1 construction from the original cubic closed point and the
proved interpolation dimension inequality. The recovered coordinates belong
to the canonical ORIGINAL residue point; equation choice and its actual
curve point are both constructed. This asserts neither regularity at that
point nor integrality/reducedness of the selected curve. -/
theorem exists_selectedCurve_originalClosedPoint_of_section_dimension
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (P : closedPoints (hypersurface p hp))
    (hsize : (hypersurfaceToBase p hp).residueDegree P.1 <
      (n + 3).choose 3 - n.choose 3) :
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      ∃ Q : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
        cubicSecondEquationCurveImmersion p q hp n hq Q.1 = P.1 ∧
        IsIso ((cubicSecondEquationCurveImmersion p q hp n hq).residueFieldMap Q.1) ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 =
          (hypersurfaceToBase p hp).residueDegree P.1 := by
  classical
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let L := S.residueField P.1
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  letI : Module.Finite K L := closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨j, g, _hgs, hgbase, hgpoint⟩ := closed_projective_point_chart
    (K := K) (L := S.residueField P.1) I (S.fromSpecResidueField P.1) (pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
  let x : Fin 4 → L := fun i => g (chartCoordinate I j i)
  have hsizeL : Module.finrank K L < (n + 3).choose 3 - n.choose 3 := by
    rw [closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P]
    exact hsize
  obtain ⟨q, hq, hqzero, hnot⟩ := exists_homogeneous_curve_equation p hp hp0 n x hsizeL
  refine ⟨q, hq, hnot, ?_⟩
  exact selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq P
    j g hgbase hgpoint hqzero

end PfaffianDescent.Coray
