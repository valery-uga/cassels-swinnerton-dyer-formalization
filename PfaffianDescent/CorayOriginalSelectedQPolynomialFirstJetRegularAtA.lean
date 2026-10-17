import PfaffianDescent.CorayNativeSpecPrincipalFirstJetRegularity
import PfaffianDescent.CorayOriginalLiteralPQChartPrincipalKernel
import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.VoisinSmoothCubicChartLocalRegularity
import PfaffianDescent.LinearNormalizedProjectivePoint

/-! Source only. The SAME selected original q, vanishing at the SAME actual
original auxiliary A, has a nonzero normalized polynomial first derivative.
The actual original p/q curve stalk at its OWN point AX is then regular.
All native chart/stalk maps and point identifications are constructed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original full jet carries its own local-ring structure. -/
private def originalRegularCurveFirstJetLocalRing001
    (M : Type u) [Field M] : IsLocalRing (SurfacePlaneJet M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst with h | h
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
    · exact Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        (by simpa only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using h))

attribute [local instance] originalRegularCurveFirstJetLocalRing001

/-- Construct an actual field-valued point of a surjective ring quotient
from its actual original residue evaluation. -/
private theorem ringHom_surjective_exists_factor_of_kernel_le001
    {R S M : Type u} [CommRing R] [CommRing S] [CommRing M]
    (f : R →+* S) (hf : Function.Surjective f) (g : R →+* M)
    (h : RingHom.ker f ≤ RingHom.ker g) :
    ∃ gS : S →+* M, gS.comp f = g := by
  let g₀ : R ⧸ RingHom.ker f →+* M := Ideal.Quotient.lift _ g (fun r hr => h hr)
  let gS : S →+* M := g₀.comp (f.quotientKerEquivOfSurjective hf).symm.toRingHom
  refine ⟨gS, ?_⟩
  ext r
  change g₀ ((f.quotientKerEquivOfSurjective hf).symm (f r)) = g r
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- Actual residue-factor identities give literal equality of source
points for the full jet and the original field-valued curve-chart point. -/
private theorem nativeJet_chartPoint_incidence_of_residue_factor001
    {R S M : Type u} [CommRing R] [CommRing S] [Field M]
    (f : R →+* S) (gS : S →+* M) (gA : R →+* M)
    (gJ : R →+* SurfacePlaneJet M)
    (hFactor : gS.comp f = gA)
    (hResidue : (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom.comp gJ = gA) :
    Spec.map (CommRingCat.ofHom f)
      (Spec.map (CommRingCat.ofHom gS) (IsLocalRing.closedPoint M)) =
      Spec.map (CommRingCat.ofHom gJ) (IsLocalRing.closedPoint (SurfacePlaneJet M)) := by
  let ρ := (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom
  letI : IsLocalHom ρ := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  have hρ : Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint M) =
      IsLocalRing.closedPoint (SurfacePlaneJet M) := by
    exact IsLocalRing.comap_closedPoint ρ
  rw [← hρ]
  change (Spec.map (CommRingCat.ofHom gS) ≫ Spec.map (CommRingCat.ofHom f))
      (IsLocalRing.closedPoint M) =
    (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom gJ))
      (IsLocalRing.closedPoint M)
  have hLeft : Spec.map (CommRingCat.ofHom gS) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (gS.comp f)) := by
    change _ = Spec.map ((CommRingCat.ofHom f) ≫ CommRingCat.ofHom gS)
    rw [Spec.map_comp]
  have hRight : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom gJ) =
      Spec.map (CommRingCat.ofHom (ρ.comp gJ)) := by
    change _ = Spec.map ((CommRingCat.ofHom gJ) ≫ CommRingCat.ofHom ρ)
    rw [Spec.map_comp]
  rw [hLeft, hRight, hFactor, hResidue]

/-- The actual normalized polynomial jet gives the native original chart
map, its exact polynomial evaluation, and its original residue evaluation. -/
private theorem originalChartJet_exists_nativeMap_polynomial_and_residue001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJet : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v j = 1) :
    ∃ gJ : ChartRing (equationIdeal p hp) j →+* SurfacePlaneJet M,
      (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom.comp gJ = gA ∧
      ∀ q : MvPolynomial (Fin 4) K,
        gJ (q.eval₂ (chartBaseMap (equationIdeal p hp) j)
          (chartCoordinate (equationIdeal p hp) j)) =
          q.eval₂ (algebraMap K (SurfacePlaneJet M))
            (surfacePlaneJetCoordinates
              (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v) := by
  let I := equationIdeal p hp
  let x : Fin 4 → M := fun i => gA (chartCoordinate I j i)
  let τ : Fin 4 → SurfacePlaneJet M := surfacePlaneJetCoordinates x v
  have heJet : ∀ a ∈ I.toIdeal, (eval₂Hom (algebraMap K (SurfacePlaneJet M)) τ) a = 0 := by
    have h : I.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K (SurfacePlaneJet M)) τ) := by
      change Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ≤ _
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJet)
    exact fun a ha => h ha
  have hOneJet : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K (SurfacePlaneJet M)) τ) heJet) (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K (SurfacePlaneJet M)) τ) (X j) = 1
    simpa only [eval₂Hom_X'] using hAnchor
  let gJ := linearNormalizedPointChartMapAt I τ heJet
    (coordinate I j) (coordinate_mem I j) hOneJet
  have heM : ∀ a ∈ I.toIdeal, (eval₂Hom (algebraMap K M) x) a = 0 := by
    have h : I.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K M) x) := by
      change Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ≤ _
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpz)
    exact fun a ha => h ha
  have hx : x j = 1 := by
    simp only [x, chartCoordinate_self, map_one]
  have hOneM : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K M) x) heM)
      (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K M) x) (X j) = 1
    simpa only [eval₂Hom_X'] using hx
  let ρ := (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom
  have hOrdinary : gA = linearNormalizedPointChartMapAt I x heM
      (coordinate I j) (coordinate_mem I j) hOneM := by
    apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
    · exact hBase
    · intro i
      rfl
  have hResidue : ρ.comp gJ = gA := by
    rw [hOrdinary]
    apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
    · ext c
      change ρ ((linearNormalizedPointChartMapAt I τ heJet
        (coordinate I j) (coordinate_mem I j) hOneJet)
          (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I j) c)) =
        algebraMap K M c
      exact (congrArg ρ (linearNormalizedPointChartMapAt_base I τ heJet
        (coordinate I j) (coordinate_mem I j) hOneJet c)).trans rfl
    · intro i
      change ρ ((linearNormalizedPointChartMapAt I τ heJet
        (coordinate I j) (coordinate_mem I j) hOneJet)
          (linearChartCoordinate I (coordinate I j) (coordinate_mem I j) i)) = x i
      calc
        _ = ρ (τ i) := congrArg ρ (linearNormalizedPointChartMapAt_coordinate I τ heJet
          (coordinate I j) (coordinate_mem I j) hOneJet i)
        _ = x i := by
          change (surfacePlaneJetCoordinates x v i).fst = x i
          simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  refine ⟨gJ, hResidue, ?_⟩
  intro q
  exact linearNormalizedPointChartMapAt_eval I τ heJet
    (coordinate I j) (coordinate_mem I j) hOneJet q

/-- Construct the SAME original p/q chart point from the original field
evaluation and prove its OWN native stalk regularity from the nonzero
actual polynomial derivative. No curve regularity, local jet map, native
stalk kernel or source-point incidence is supplied. -/
private theorem originalCurveChart_exists_regular_nativePolynomialJet_point001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n) (j : Fin 4)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (hqz : q.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJet : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v j = 1)
    (hqDerivative : (q.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v)).snd ≠ 0) :
    ∃ z : Spec (.of (ChartRing (projectiveIntersectionIdeal p q hp hq) j)),
      Spec.map (CommRingCat.ofHom (PfaffianDescent.chartQuotientMap (equationIdeal p hp)
        (projectiveIntersectionIdeal p q hp hq) le_sup_left j)) z =
          Spec.map (CommRingCat.ofHom gA) (IsLocalRing.closedPoint M) ∧
      IsRegularLocalRing
        ((Spec (.of (ChartRing (projectiveIntersectionIdeal p q hp hq) j))).presheaf.stalk z) := by
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let R := ChartRing I j
  let T := ChartRing J j
  let f := PfaffianDescent.chartQuotientMap I J le_sup_left j
  let q₀ : R := q.eval₂ (chartBaseMap I j) (chartCoordinate I j)
  have hf : Function.Surjective f := PfaffianDescent.chartQuotientMap_surjective I J le_sup_left j
  have hKernel : RingHom.ker f = Ideal.span ({q₀} : Set R) :=
    cubicSecondEquation_chartQuotientMap_ker_eq_normalizedEquation001 p q hp n hq j
  have hValueA : gA q₀ = 0 := by
    dsimp only [q₀]
    rw [MvPolynomial.hom_eval₂, hBase]
    exact hqz
  have hKernelA : RingHom.ker f ≤ RingHom.ker gA := by
    rw [hKernel]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hValueA)
  obtain ⟨gT, hgT⟩ := ringHom_surjective_exists_factor_of_kernel_le001 f hf gA hKernelA
  let z := Spec.map (CommRingCat.ofHom gT) (IsLocalRing.closedPoint M)
  have hOriginalPoint : Spec.map (CommRingCat.ofHom f) z =
      Spec.map (CommRingCat.ofHom gA) (IsLocalRing.closedPoint M) := by
    change (Spec.map (CommRingCat.ofHom gT) ≫ Spec.map (CommRingCat.ofHom f))
      (IsLocalRing.closedPoint M) = _
    have hComp : Spec.map (CommRingCat.ofHom gT) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (gT.comp f)) := by
      change _ = Spec.map ((CommRingCat.ofHom f) ≫ CommRingCat.ofHom gT)
      rw [Spec.map_comp]
    rw [hComp, hgT]
  obtain ⟨gJ, hResidue, hEvaluation⟩ :=
    originalChartJet_exists_nativeMap_polynomial_and_residue001 p hp j gA hBase hpz v hpJet hAnchor
  have hPoint := nativeJet_chartPoint_incidence_of_residue_factor001 f gT gA gJ hgT hResidue
  have hJetValue : (gJ q₀).fst = 0 := by
    have h := RingHom.congr_fun hResidue q₀
    change (gJ q₀).fst = gA q₀ at h
    exact h.trans hValueA
  have hJetDerivative : (gJ q₀).snd ≠ 0 := by
    rw [hEvaluation q]
    exact hqDerivative
  letI : IsRegularRing R := PfaffianDescent.smoothCubic_chartRing_isRegularRing p hp j
  refine ⟨z, hOriginalPoint, ?_⟩
  exact nativeSpec_surjectivePrincipal_regular_of_actualFirstJet001
    f hf q₀ hKernel gJ hJetValue hJetDerivative z hPoint

/-- At the SAME original auxiliary point, the actual selected original q
value zero and nonzero normalized polynomial first derivative imply regularity
of the SAME unsaturated p/q curve's OWN AX stalk. Source incidence, polynomial
evaluation, native local jet/stalk kernel and exact original-point transport
are constructed internally; smoothness supplies only ambient regularity. -/
theorem selectedCurve_sameOriginalAuxiliaryPoint_regular_of_nonzero_polynomialFirstJet001
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (A : closedPoints (hypersurface p hp))
    (AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hAX : cubicSecondEquationCurveImmersion p q hp n hq AX.1 = A.1) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (j : Fin 4) (gA : ChartRing (equationIdeal p hp) j →+* S.residueField A.1),
      gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j =
        S.fromSpecResidueField A.1 →
      ∀ (hpz : p.eval₂ (algebraMap K (S.residueField A.1))
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
        (hqz : q.eval₂ (algebraMap K (S.residueField A.1))
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
        (v : Fin 2 → Fin 4 → S.residueField A.1),
      p.eval₂ (algebraMap K (SurfacePlaneJet (S.residueField A.1)))
        (surfacePlaneJetCoordinates
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v) = 0 →
      surfacePlaneJetCoordinates
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v j = 1 →
      (q.eval₂ (algebraMap K (SurfacePlaneJet (S.residueField A.1)))
        (surfacePlaneJetCoordinates
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v)).snd ≠ 0 →
      IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk AX.1) := by
  classical
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro j gA hBase hOriginalMap hpz hqz v hpJet hAnchor hDerivative
  let M := S.residueField A.1
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let f := PfaffianDescent.chartQuotientMap I J le_sup_left j
  obtain ⟨z, hPoint, hRegular⟩ := originalCurveChart_exists_regular_nativePolynomialJet_point001
    p q hp n hq j gA hBase hpz hqz v hpJet hAnchor hDerivative
  letI : IsRegularLocalRing ((Spec (.of (ChartRing J j))).presheaf.stalk z) := hRegular
  have hRegularWhole : IsRegularLocalRing ((scheme J).presheaf.stalk (chartι J j z)) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_openImmersion_image (chartι J j) z
  have hSquare : Spec.map (CommRingCat.ofHom f) ≫ chartι I j = chartι J j ≫ i :=
    (PfaffianDescent.chartι_schemeQuotientMap I J le_sup_left j).symm
  have hSamePoint : chartι J j z = AX.1 := by
    apply i.isClosedEmbedding.injective
    calc
      i (chartι J j z) = chartι I j (Spec.map (CommRingCat.ofHom f) z) :=
        (congrArg (fun h => h z) hSquare).symm
      _ = chartι I j (Spec.map (CommRingCat.ofHom gA) (IsLocalRing.closedPoint M)) := by
        rw [hPoint]
      _ = A.1 := by
        change (Spec.map (CommRingCat.ofHom gA) ≫ chartι I j) (IsLocalRing.closedPoint M) = A.1
        rw [hOriginalMap]
        exact Scheme.fromSpecResidueField_apply (X := S) A.1
          (show Spec (.of (S.residueField A.1)) from IsLocalRing.closedPoint M)
      _ = i AX.1 := hAX.symm
  change IsRegularLocalRing ((scheme J).presheaf.stalk AX.1)
  exact hSamePoint ▸ hRegularWhole

/-- An actual original-residue embedding into the splitting field may be
used for the native polynomial jet. The target remains the SAME original
curve's OWN AX stalk; the point is identified through the literal embedding
and original fromSpecResidue map, with no regularity-descent premise. -/
theorem selectedCurve_sameOriginalAuxiliaryPoint_regular_of_nonzero_extensionPolynomialFirstJet001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (A : closedPoints (hypersurface p hp))
    (AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hAX : cubicSecondEquationCurveImmersion p q hp n hq AX.1 = A.1) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (σ : S.residueField A.1 →ₐ[K] M)
      (j : Fin 4) (gA : ChartRing (equationIdeal p hp) j →+* M),
      gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ S.fromSpecResidueField A.1 →
      ∀ (hpz : p.eval₂ (algebraMap K M)
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
        (hqz : q.eval₂ (algebraMap K M)
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
        (v : Fin 2 → Fin 4 → M),
      p.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v) = 0 →
      surfacePlaneJetCoordinates
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v j = 1 →
      (q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates
          (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) v)).snd ≠ 0 →
      IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk AX.1) := by
  classical
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro σ j gA hBase hOriginalMap hpz hqz v hpJet hAnchor hDerivative
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let f := PfaffianDescent.chartQuotientMap I J le_sup_left j
  obtain ⟨z, hPoint, hRegular⟩ := originalCurveChart_exists_regular_nativePolynomialJet_point001
    p q hp n hq j gA hBase hpz hqz v hpJet hAnchor hDerivative
  letI : IsRegularLocalRing ((Spec (.of (ChartRing J j))).presheaf.stalk z) := hRegular
  have hRegularWhole : IsRegularLocalRing ((scheme J).presheaf.stalk (chartι J j z)) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_openImmersion_image (chartι J j) z
  have hSquare : Spec.map (CommRingCat.ofHom f) ≫ chartι I j = chartι J j ≫ i :=
    (PfaffianDescent.chartι_schemeQuotientMap I J le_sup_left j).symm
  have hSamePoint : chartι J j z = AX.1 := by
    apply i.isClosedEmbedding.injective
    calc
      i (chartι J j z) = chartι I j (Spec.map (CommRingCat.ofHom f) z) :=
        (congrArg (fun h => h z) hSquare).symm
      _ = chartι I j (Spec.map (CommRingCat.ofHom gA) (IsLocalRing.closedPoint M)) := by
        rw [hPoint]
      _ = A.1 := by
        change (Spec.map (CommRingCat.ofHom gA) ≫ chartι I j) (IsLocalRing.closedPoint M) = A.1
        rw [hOriginalMap]
        exact Scheme.fromSpecResidueField_apply (X := S) A.1
          (Spec.map (CommRingCat.ofHom σ.toRingHom) (IsLocalRing.closedPoint M))
      _ = i AX.1 := hAX.symm
  change IsRegularLocalRing ((scheme J).presheaf.stalk AX.1)
  exact hSamePoint ▸ hRegularWhole

/-- An actual native field-valued chart point above the ORIGINAL closed A
constructs its SAME original q-curve closed lift, OWN regular stalk and exact
FULL original degree. No residue-field replacement, AX or regularity is
supplied; actual source-point incidence suffices for the jet-stalk map. -/
theorem selectedCurve_actualNativeFieldPoint_exists_regular_originalClosedLift001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (A : closedPoints (hypersurface p hp)) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hOriginalPoint : chartι (equationIdeal p hp) j
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint M)) = A.1)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (hqz : q.eval₂ (algebraMap K M)
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJet : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v j = 1)
    (hqDerivative : (q.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v)).snd ≠ 0) :
    ∃ AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
      cubicSecondEquationCurveImmersion p q hp n hq AX.1 = A.1 ∧
      IsIso ((cubicSecondEquationCurveImmersion p q hp n hq).residueFieldMap AX.1) ∧
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 =
        (hypersurfaceToBase p hp).residueDegree A.1 ∧
      IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk AX.1) := by
  classical
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let f := PfaffianDescent.chartQuotientMap I J le_sup_left j
  obtain ⟨z, hPoint, hRegular⟩ := originalCurveChart_exists_regular_nativePolynomialJet_point001
    p q hp n hq j g hBase hpz hqz v hpJet hAnchor hqDerivative
  let x := chartι J j z
  letI : IsRegularLocalRing ((Spec (.of (ChartRing J j))).presheaf.stalk z) := hRegular
  have hRegularWhole : IsRegularLocalRing ((scheme J).presheaf.stalk x) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_openImmersion_image (chartι J j) z
  have hSquare : Spec.map (CommRingCat.ofHom f) ≫ chartι I j = chartι J j ≫ i :=
    (PfaffianDescent.chartι_schemeQuotientMap I J le_sup_left j).symm
  have hx : i x = A.1 := by
    calc
      i x = chartι I j (Spec.map (CommRingCat.ofHom f) z) :=
        (congrArg (fun h => h z) hSquare).symm
      _ = chartι I j (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint M)) := by
        rw [hPoint]
      _ = A.1 := hOriginalPoint
  have hPre : i ⁻¹' ({A.1} : Set (hypersurface p hp)) = ({x} : Set (scheme J)) := by
    ext y
    change i y = A.1 ↔ y = x
    constructor
    · intro hy
      exact i.isClosedEmbedding.injective (hy.trans hx.symm)
    · rintro rfl
      exact hx
  have hxClosed : IsClosed ({x} : Set (scheme J)) := by
    have h := A.2.preimage i.continuous
    rw [hPre] at h
    exact h
  let AX : closedPoints (scheme J) := ⟨x, hxClosed⟩
  letI : IsIso (i.residueFieldMap AX.1) :=
    isIso_residueFieldMap_of_surjectiveOnStalks i AX.1
  have hDegree := residueDegree_comp_of_residueFieldMap_isIso i (hypersurfaceToBase p hp) AX.1
  rw [cubicSecondEquationCurveImmersion_toBase] at hDegree
  have hAX : i AX.1 = A.1 := hx
  rw [hAX] at hDegree
  exact ⟨AX, hAX, inferInstance, hDegree, hRegularWhole⟩

end PfaffianDescent.Coray
