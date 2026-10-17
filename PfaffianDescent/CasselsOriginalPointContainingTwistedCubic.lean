import PfaffianDescent.CasselsContainingTwistedCubicCoordinateIdeal
import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.PerfectFieldPointGeometricPosition
import PfaffianDescent.GroundTwistedCubicCubicIntersectionAnyField
import AllCharacteristics.ClosedPointAlgebra

/-! SOURCE ONLY. The original point morphism factors through the whole
intersection with a constructed ground twisted cubic. Every ambient/base
square is with the original point; no curve/containment certificate is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A field point's literal chosen chart factors through extra homogeneous
equations that vanish on that chart's SAME coordinates. -/
theorem fieldPoint_originalChart_lifts_to_whole_ideal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (i : Spec (.of L) ⟶ scheme I) [IsClosedImmersion i]
    (j : Fin 4) (g : ChartRing I j →+* L)
    (hbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = i)
    (heJ : ∀ f ∈ J.toIdeal,
      f.eval₂ (algebraMap K L) (fun r => g (chartCoordinate I j r)) = 0) :
    ∃ l : Spec (.of L) ⟶ scheme J,
      IsClosedImmersion l ∧ l ≫ schemeQuotientMap I J hIJ = i := by
  let x : Fin 4 → L := fun r => g (chartCoordinate I j r)
  have heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K L) x = 0 := by
    intro f hf
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j f hf)
    rw [hom_eval₂, hbase, map_zero] at h
    exact h
  let z : CoordinateRing I := coordinate I j
  have hz : z ∈ grading I 1 := coordinate_mem I j
  have hzOneI : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) x) heI) z = 1 := by
    change eval₂Hom (algebraMap K L) x (X j) = 1
    simp only [eval₂Hom_X', x, chartCoordinate_self, map_one]
  let zJ := gradedQuotientMap I J hIJ z
  have hzJ : zJ ∈ grading J 1 := (gradedQuotientMap I J hIJ).map_mem hz
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K L) x) heJ) zJ = 1 := by
    change eval₂Hom (algebraMap K L) x (X j) = 1
    simp only [eval₂Hom_X', x, chartCoordinate_self, map_one]
  let l := linearNormalizedPointAt J x heJ zJ hzJ hzOneJ
  have hmaps : g = linearNormalizedPointChartMapAt I x heI z hz hzOneI := by
    apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I x heI z hz hzOneI g
    · exact hbase
    · intro r
      rfl
  have hfactor : l ≫ schemeQuotientMap I J hIJ = i := by
    rw [show l ≫ schemeQuotientMap I J hIJ =
      linearNormalizedPointAt I x heI z hz hzOneI from
        linearNormalizedPointAt_comp_schemeQuotientMap I J hIJ x heI heJ z hz
          hzOneI hzOneJ]
    change Spec.map (CommRingCat.ofHom
      (linearNormalizedPointChartMapAt I x heI z hz hzOneI)) ≫ chartι I j = i
    rw [← hmaps]
    exact hpoint
  letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
    schemeQuotientMap_closedImmersion I J hIJ
  letI : IsClosedImmersion (l ≫ schemeQuotientMap I J hIJ) := by
    rw [hfactor]
    infer_instance
  exact ⟨l, IsClosedImmersion.of_comp l (schemeQuotientMap I J hIJ), hfactor⟩

/-- The canonical projection from the entire curve/cubic summed-ideal
intersection to the original cubic surface. -/
def casselsTwistedCubicIntersectionToSurface
    {K : Type u} [Field K]
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF) ⟶
      hypersurface F hF :=
  schemeQuotientMap (equationIdeal F hF)
    (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)
    (by rw [QuarticNet.groundTwistedCubicCubicIntersectionIdeal,
      HomogeneousIdeal.toIdeal_sup]; exact le_sup_right)

instance casselsTwistedCubicIntersectionToSurface_isClosedImmersion
    {K : Type u} [Field K]
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    IsClosedImmersion (casselsTwistedCubicIntersectionToSurface B F hF) :=
  schemeQuotientMap_closedImmersion _ _ _

theorem casselsTwistedCubicIntersectionToSurface_toBase
    {K : Type u} [Field K]
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    casselsTwistedCubicIntersectionToSurface B F hF ≫ hypersurfaceToBase F hF =
      toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF) :=
  schemeQuotientMap_toBase _ _ _

/-- Literal perfect-field Cassels construction from the ORIGINAL closed
point: a constructed ground twisted cubic, and the SAME residue-field
immersion into its WHOLE intersection with the original cubic. The projection
identifies the original closed-point morphism exactly, not only its degree. -/
theorem perfectField_original_closedPoint_exists_containing_twistedCubic
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :
    ∃ B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∃ l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
          scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF),
        IsClosedImmersion l ∧
        l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
          (hypersurface F hF).fromSpecResidueField P.1 := by
  classical
  let I := equationIdeal F hF
  let L := (hypersurface F hF).residueField P.1
  let i : Spec (.of L) ⟶ scheme I := (hypersurface F hF).fromSpecResidueField P.1
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase F hF) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase F hF) P
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  have hi : i ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase F hF) P.1).symm
  obtain ⟨j, g, hbase, hpoint⟩ := exists_chart_hom_eq_of_point I (algebraMap K L) i hi
  have hplane' : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c) ∈
        (i (IsLocalRing.closedPoint L)).asHomogeneousIdeal := by
    rintro ⟨c, hc, hmem⟩
    apply hplane
    refine ⟨c, hc, ?_⟩
    have hP : i (IsLocalRing.closedPoint L) = P.1 :=
      (hypersurface F hF).fromSpecResidueField_apply P.1 _
    erw [hP] at hmem
    exact hmem
  have hp : LinearIndependent K (fun r => g (chartCoordinate I j r)) := by
    exact fieldPoint_linearChart_coordinates_independent I i hplane'
      (coordinate I j) (coordinate_mem I j) g hbase hpoint
  have hdim' : finrank K L = 4 ∨ finrank K L = 5 := by
    rw [AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase F hF) P]
    exact hdim
  obtain ⟨B, hB, heB⟩ :=
    perfectField_independent_degree_four_or_five_exists_containing_twistedCubicIdeal
      hdim' (fun r => g (chartCoordinate I j r)) hp
  let J := QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF
  have hIJ : I.toIdeal ≤ J.toIdeal := by
    change I.toIdeal ≤ (B ⊔ I).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_right
  have heI : ∀ f ∈ I.toIdeal,
      f.eval₂ (algebraMap K L) (fun r => g (chartCoordinate I j r)) = 0 := by
    intro f hf
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j f hf)
    rw [hom_eval₂, hbase, map_zero] at h
    exact h
  have heJ : ∀ f ∈ J.toIdeal,
      f.eval₂ (algebraMap K L) (fun r => g (chartCoordinate I j r)) = 0 := by
    have hker : J.toIdeal ≤ RingHom.ker
        (eval₂Hom (algebraMap K L) (fun r => g (chartCoordinate I j r))) := by
      change (B ⊔ I).toIdeal ≤ _
      rw [HomogeneousIdeal.toIdeal_sup]
      exact sup_le heB heI
    exact fun f hf => hker hf
  obtain ⟨l, hl, hfactor⟩ :=
    fieldPoint_originalChart_lifts_to_whole_ideal I J hIJ i j g hbase hpoint heJ
  exact ⟨B, hB, l, hl, hfactor⟩

/-- The constructed curve contains the ORIGINAL point as an actual closed
subscheme; its embedding and base map retain the original point morphisms. -/
theorem perfectField_original_closedPoint_exists_twistedCubic_ambient_containment
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :
    ∃ B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∃ lB : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶ scheme B,
        IsClosedImmersion lB ∧
        lB ≫ quotientProjMap B =
          (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToAmbient F hF ∧
        lB ≫ toBase B =
          (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToBase F hF := by
  obtain ⟨B, hB, l, hl, hfactor⟩ :=
    perfectField_original_closedPoint_exists_containing_twistedCubic F hF P hdim hplane
  let J := QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF
  have hBJ : B.toIdeal ≤ J.toIdeal := by
    change B.toIdeal ≤ (B ⊔ equationIdeal F hF).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  let cB : scheme J ⟶ scheme B := schemeQuotientMap B J hBJ
  let lB := l ≫ cB
  letI : IsClosedImmersion cB := schemeQuotientMap_closedImmersion B J hBJ
  letI : IsClosedImmersion l := hl
  have hambient : lB ≫ quotientProjMap B =
      (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToAmbient F hF := by
    calc
      _ = l ≫ quotientProjMap J := by
        dsimp only [lB, cB]
        rw [Category.assoc, schemeQuotientMap_comp_quotientProjMap]
      _ = (l ≫ casselsTwistedCubicIntersectionToSurface B F hF) ≫
          hypersurfaceToAmbient F hF := by
        rw [Category.assoc]
        exact congrArg (fun f => l ≫ f)
          (schemeQuotientMap_comp_quotientProjMap _ _ _).symm
      _ = _ := by rw [hfactor]
  have hbase : lB ≫ toBase B =
      (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToBase F hF := by
    calc
      _ = l ≫ toBase J := by
        dsimp only [lB, cB]
        rw [Category.assoc, schemeQuotientMap_toBase]
      _ = (l ≫ casselsTwistedCubicIntersectionToSurface B F hF) ≫
          hypersurfaceToBase F hF := by
        rw [Category.assoc, casselsTwistedCubicIntersectionToSurface_toBase]
      _ = _ := by rw [hfactor]
  have hlB : IsClosedImmersion lB := IsClosedImmersion.comp l cB
  exact ⟨B, hB, lB, hlB, hambient, hbase⟩

end PfaffianDescent
