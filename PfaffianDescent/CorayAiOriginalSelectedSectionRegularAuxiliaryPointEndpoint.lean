import PfaffianDescent.CorayOriginalSelectedQPolynomialFirstJetRegularAtA
import PfaffianDescent.CorayIntegralAiRegularDegreeThreePointBranchClosure
import PfaffianDescent.CorayAiNativeBasisDenominator
import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original chart evaluation already lies on the cubic. -/
private theorem originalChartFieldPoint_cubic_value_zero001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* F)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F) :
    p.eval₂ (algebraMap K F)
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
  have hpI : p ∈ (equationIdeal p hp).toIdeal := Ideal.subset_span (Set.mem_singleton p)
  have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem (equationIdeal p hp) j p hpI)
  rw [hom_eval₂, hBase, map_zero] at h
  exact h

/-- The entire native chart jet is the polynomial jet of the SAME
original homogeneous representative. This bounded copy has no image or
closed-point transport context. -/
private theorem selectedSection_nativeJet_polynomial_representative001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy) (q : MvPolynomial (Fin 4) K)
    (hRep : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) =
      q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) := by
  rw [cubicNormalizedFullJetChartMap_section001]
  change cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ s.1.1 = _
  rw [← hRep]
  exact cubicCoordinateAlgebraEvaluation_mk p hp (surfacePlaneJetCoordinates z v) hpJ q

/-- Ordinary polynomial evaluation commutes with the actual original
residue embedding into the native jet field. -/
private theorem polynomial_eval_originalResidueEmbedding001
    {K A M : Type u} [Field K] [Field A] [Field M] [Algebra K A] [Algebra K M]
    (sigma : A →ₐ[K] M) (x : Fin 4 → A) (q : MvPolynomial (Fin 4) K) :
    q.eval₂ (algebraMap K M) (fun i => sigma (x i)) =
      sigma (q.eval₂ (algebraMap K A) x) := by
  have h := MvPolynomial.hom_eval₂ q (algebraMap K A) sigma.toRingHom x
  have hCoefficient : sigma.toRingHom.comp (algebraMap K A) = algebraMap K M :=
    RingHom.ext sigma.commutes
  change sigma (q.eval₂ (algebraMap K A) x) =
    q.eval₂ (sigma.toRingHom.comp (algebraMap K A)) (fun i => sigma (x i)) at h
  rw [hCoefficient] at h
  exact h.symm

/-- Zero ordinary value and nonzero ENTIRE polynomial jet give a
nonzero tangent part. This is checked before actual curve point transport. -/
private theorem polynomial_nativeJet_derivative_ne_zero001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (x : Fin 4 → M) (v : Fin 2 → Fin 4 → M) (q : MvPolynomial (Fin 4) K)
    (hValue : q.eval₂ (algebraMap K M) x = 0)
    (hJet : q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates x v) ≠ 0) :
    (q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates x v)).snd ≠ 0 := by
  let rho : SurfacePlaneJet M →ₐ[K] M := TrivSqZeroExt.fstHom K M (Fin 2 → M)
  have hCoordinates : (fun i => rho (surfacePlaneJetCoordinates x v i)) = x := by
    funext i
    change (surfacePlaneJetCoordinates x v i).fst = x i
    simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  have hFst : (q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates x v)).fst = 0 := by
    have h := MvPolynomial.hom_eval₂ q (algebraMap K (SurfacePlaneJet M))
      rho.toRingHom (surfacePlaneJetCoordinates x v)
    have hCoefficient : rho.toRingHom.comp (algebraMap K (SurfacePlaneJet M)) = algebraMap K M :=
      RingHom.ext rho.commutes
    change (q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates x v)).fst =
      q.eval₂ (rho.toRingHom.comp (algebraMap K (SurfacePlaneJet M)))
        (fun i => rho (surfacePlaneJetCoordinates x v i)) at h
    rw [hCoefficient, hCoordinates] at h
    exact h.trans hValue
  intro hSnd
  apply hJet
  apply TrivSqZeroExt.ext
  · exact hFst
  · exact hSnd

/-- An original through-P section with actual auxiliary value zero and
nonzero full jet constructs its fresh original homogeneous polynomial
representative through BOTH actual coordinate points. -/
private theorem originalSelectedSection_exists_fresh_polynomial001
    {K L A M : Type u} [Field K] [Field L] [Field A] [Field M]
    [Algebra K L] [Algebra K A] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (gA : ChartRing (equationIdeal p hp) j →+* A)
    (hBaseA : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K A)
    (sigma : A →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (hAux : gA (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0)
    (hJet : cubicNormalizedFullJetChartMap p hp j
      (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) ≠ 0) :
    ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K A) (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1 ∧
      q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v) ≠ 0 := by
  obtain ⟨q, hq, hP, hRep⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy s.1).mp s.2
  have hsNonzero : s ≠ 0 := by
    intro h
    apply hJet
    rw [h, map_zero, map_zero]
  have hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    have hqZero : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    apply hsNonzero
    apply Subtype.ext
    apply Subtype.ext
    exact hRep.symm.trans hqZero
  have hA : q.eval₂ (algebraMap K A) (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
    have hEq := congrArg gA
      (cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001 p hp n y hpy j s q hq hRep)
    rw [MvPolynomial.hom_eval₂, hBaseA] at hEq
    exact hEq.trans hAux
  have hPolyJet := selectedSection_nativeJet_polynomial_representative001
    p hp n y hpy j (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i)))
      v hpJ hAnchor s q hRep
  exact ⟨q, hq, hP, hA, hnot, hRep, hPolyJet ▸ hJet⟩

/-- Composition with the literal original residue embedding preserves
both the actual original coefficient map and original point incidence. -/
private theorem originalChartPoint_residueEmbedding_map001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (A : closedPoints (hypersurface p hp)) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (j : Fin 4) (gA : ChartRing (equationIdeal p hp) j →+* S.residueField A.1)
      (sigma : S.residueField A.1 →ₐ[K] M),
      gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j = S.fromSpecResidueField A.1 →
      let g := sigma.toRingHom.comp gA
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫ S.fromSpecResidueField A.1 := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro j gA sigma hBase hPoint g
  refine ⟨?_, ?_⟩
  · change (sigma.toRingHom.comp gA).comp (chartBaseMap (equationIdeal p hp) j) = _
    rw [RingHom.comp_assoc, hBase]
    exact sigma.comp_algebraMap
  · change Spec.map ((CommRingCat.ofHom gA) ≫ CommRingCat.ofHom sigma.toRingHom) ≫
      chartι (equationIdeal p hp) j = _
    rw [Spec.map_comp, Category.assoc, hPoint]

/-- A SAME originalK section through P, actually zero at the original
auxiliary A and nonzero on its normalized native full jet, constructs the
fresh original q and the degree-three regular closed point AX of the SAME
whole original p/q curve. No q, AX, regularity or derivative is supplied. -/
theorem originalSelectedSection_nonzeroNativeAuxiliaryJet_exists_fresh_equation_regular_degreeThreePoint001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (A : closedPoints (hypersurface p hp))
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (j : Fin 4) (gA : ChartRing (equationIdeal p hp) j →+* S.residueField A.1),
      gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j = S.fromSpecResidueField A.1 →
      ∀ (sigma : S.residueField A.1 →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
        (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v) = 0)
        (hAnchor : surfacePlaneJetCoordinates
          (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v j = 1)
        (s : cubicThroughCoordinateSections p hp n y hpy),
      gA (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0 →
      cubicNormalizedFullJetChartMap p hp j
        (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
        (cubicThroughPointChartEvaluation p hp n y hpy j s) ≠ 0 →
      ∃ q : MvPolynomial (Fin 4) K, ∃ hq : q.IsHomogeneous n,
        q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1 ∧
        ∃ AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
          cubicSecondEquationCurveImmersion p q hp n hq AX.1 = A.1 ∧
          (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 = 3 ∧
          IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk AX.1) := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro j gA hBase hPoint sigma v hpJ hAnchor s hAux hJet
  obtain ⟨q, hq, hP, hQA, hnot, hRep, hQJet⟩ :=
    originalSelectedSection_exists_fresh_polynomial001 p hp n y hpy j gA hBase sigma v hpJ hAnchor s hAux hJet
  obtain ⟨AX, hAX, _hAXiso, hAXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq A j gA hBase hPoint hQA
  let g := sigma.toRingHom.comp gA
  have hG := originalChartPoint_residueEmbedding_map001 p hp A j gA sigma hBase hPoint
  have hpG := originalChartFieldPoint_cubic_value_zero001 p hp j g hG.1
  have hQG : q.eval₂ (algebraMap K M)
      (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) = 0 := by
    rw [polynomial_eval_originalResidueEmbedding001 sigma _ q, hQA, map_zero]
  have hDerivative := polynomial_nativeJet_derivative_ne_zero001
    (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) j i))) v q hQG hQJet
  have hRegular := selectedCurve_sameOriginalAuxiliaryPoint_regular_of_nonzero_extensionPolynomialFirstJet001
    p q hp n hq A AX hAX sigma j g hG.1 hG.2 hpG hQG v hpJ hAnchor hDerivative
  exact ⟨q, hq, hP, hnot, hRep, AX, hAX, hAXdegree.trans hAdegree, hRegular⟩

/-- Conditional natural Ai endpoint: an actually selected original
through-P section with a nonzero auxiliary native jet supplies q, its SAME
regular full-degree-three curve point, and the full-constants downstream
argument. The strict original least-window integral clause is explicit;
section/tangent-good auxiliary selection remains to be constructed. -/
theorem coray_case_Ai_originalSelectedSection_nonzeroNativeAuxiliaryJet_exists_smaller_originalCubic_closedPoint001
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (P A : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hstrict : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1)
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (jP : Fin 4) (gP : ChartRing (equationIdeal p hp) jP →+* S.residueField P.1),
      gP.comp (chartBaseMap (equationIdeal p hp) jP) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) jP = S.fromSpecResidueField P.1 →
      ∀ (hpP : p.eval₂ (algebraMap K (S.residueField P.1))
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0),
      (∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
        q.eval₂ (algebraMap K (S.residueField P.1))
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0 →
        q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
        IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) →
      ∀ (jA : Fin 4) (gA : ChartRing (equationIdeal p hp) jA →+* S.residueField A.1),
      gA.comp (chartBaseMap (equationIdeal p hp) jA) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) jA = S.fromSpecResidueField A.1 →
      ∀ (sigma : S.residueField A.1 →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
        (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) jA i))) v) = 0)
        (hAnchor : surfacePlaneJetCoordinates
          (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) jA i))) v jA = 1)
        (s : cubicThroughCoordinateSections p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP),
      gA (cubicThroughPointChartEvaluation p hp n
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) = 0 →
      cubicNormalizedFullJetChartMap p hp jA
        (fun i => sigma (gA (chartCoordinate (equationIdeal p hp) jA i))) v hpJ hAnchor
        (cubicThroughPointChartEvaluation p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) ≠ 0 →
      ∃ R : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 ≤ 3 * n.choose 2 + 1 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree P.1 := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro jP gP hBaseP hPointP hpP hAllIntegral jA gA hBaseA hPointA sigma v hpJ hAnchor s hAux hJet
  obtain ⟨q, hq, hqP, hnot, _hRep, AX, hAX, hAXdegree, hAXregular⟩ :=
    originalSelectedSection_nonzeroNativeAuxiliaryJet_exists_fresh_equation_regular_degreeThreePoint001
      p hp n (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP
      A hAdegree jA gA hBaseA hPointA sigma v hpJ hAnchor s hAux hJet
  letI : IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := hAllIntegral q hq hqP hnot
  obtain ⟨PX, hPX, _hPXiso, hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq P jP gP hBaseP hPointP hqP
  have hPXcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1) 3 := by
    rw [hPXdegree]
    exact hPcop
  have hPXstrict : 3 * n.choose 2 + 1 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1 := by
    rw [hPXdegree]
    exact hstrict
  obtain ⟨R, hRcop, hRbound, hRsmall⟩ :=
    coray_case_Ai_integral_originalPoint_exists_smaller_originalCubic_closedPoint_of_regular_degreeThreePoint001
      p q hp hp0 n hn hq hnot PX AX hPXcop hPXstrict hAXdegree hAXregular
  rw [hPX] at hRsmall
  exact ⟨R, hRcop, hRbound, hRsmall⟩

/-- The named literal auxiliary field point and its actual chart factor
remain unchanged after the original-K embedding into the native jet field.
No equality of the auxiliary field with the original residue field is used. -/
private theorem originalAuxiliaryFieldChartPoint_nativeEmbedding_map001
    {K B M : Type u} [Field K] [Field B] [Field M] [Algebra K B] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (A : closedPoints (hypersurface p hp)) (r : Spec (.of B) ⟶ hypersurface p hp)
    (j : Fin 4) (gB : ChartRing (equationIdeal p hp) j →+* B)
    (hBaseB : gB.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K B)
    (hChart : Spec.map (CommRingCat.ofHom gB) ≫ chartι (equationIdeal p hp) j = r)
    (hOriginalPoint : r (IsLocalRing.closedPoint B) = A.1) (sigma : B →ₐ[K] M) :
    let g := sigma.toRingHom.comp gB
    g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M ∧
    chartι (equationIdeal p hp) j
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint M)) = A.1 := by
  intro g
  have hFieldPoint : Spec.map (CommRingCat.ofHom sigma.toRingHom) (IsLocalRing.closedPoint M) =
      IsLocalRing.closedPoint B := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · change (sigma.toRingHom.comp gB).comp (chartBaseMap (equationIdeal p hp) j) = _
    rw [RingHom.comp_assoc, hBaseB]
    exact sigma.comp_algebraMap
  · change (Spec.map ((CommRingCat.ofHom gB) ≫ CommRingCat.ofHom sigma.toRingHom) ≫
      chartι (equationIdeal p hp) j) (IsLocalRing.closedPoint M) = _
    rw [Spec.map_comp, Category.assoc, hChart]
    change r (Spec.map (CommRingCat.ofHom sigma.toRingHom) (IsLocalRing.closedPoint M)) = A.1
    rw [hFieldPoint]
    exact hOriginalPoint

/-- The actual literal auxiliary field B, its named closed point map r,
SAME original section and actual sigmaB native jet construct original q and
OWN original regular degree-three AX. All original curve points and full
degrees are derived without replacing B by a canonical residue field. -/
theorem originalSelectedSection_actualAuxiliaryField_nonzeroNativeJet_exists_fresh_equation_regular_degreeThreePoint001
    {K L B M : Type u} [Field K] [Field L] [Field B] [Field M]
    [Algebra K L] [Algebra K B] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (A : closedPoints (hypersurface p hp))
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3)
    (r : Spec (.of B) ⟶ hypersurface p hp) (j : Fin 4)
    (gB : ChartRing (equationIdeal p hp) j →+* B)
    (hBaseB : gB.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K B)
    (hChart : Spec.map (CommRingCat.ofHom gB) ≫ chartι (equationIdeal p hp) j = r)
    (hOriginalPoint : r (IsLocalRing.closedPoint B) = A.1)
    (sigma : B →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) j i))) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) j i))) v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (hAux : gB (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0)
    (hJet : cubicNormalizedFullJetChartMap p hp j
      (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) ≠ 0) :
    ∃ q : MvPolynomial (Fin 4) K, ∃ hq : q.IsHomogeneous n,
      q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1 ∧
      ∃ AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
        cubicSecondEquationCurveImmersion p q hp n hq AX.1 = A.1 ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 = 3 ∧
        IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk AX.1) := by
  obtain ⟨q, hq, hP, hQB, hnot, hRep, hQJet⟩ :=
    originalSelectedSection_exists_fresh_polynomial001 p hp n y hpy j gB hBaseB sigma v hpJ hAnchor s hAux hJet
  let g := sigma.toRingHom.comp gB
  have hG := originalAuxiliaryFieldChartPoint_nativeEmbedding_map001
    p hp A r j gB hBaseB hChart hOriginalPoint sigma
  have hpG := originalChartFieldPoint_cubic_value_zero001 p hp j g hG.1
  have hQG : q.eval₂ (algebraMap K M)
      (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) j i))) = 0 := by
    rw [polynomial_eval_originalResidueEmbedding001 sigma _ q, hQB, map_zero]
  have hDerivative := polynomial_nativeJet_derivative_ne_zero001
    (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) j i))) v q hQG hQJet
  obtain ⟨AX, hAX, _hAXiso, hAXdegree, hAXregular⟩ :=
    selectedCurve_actualNativeFieldPoint_exists_regular_originalClosedLift001
      p q hp n hq A j g hG.1 hG.2 hpG hQG v hpJ hAnchor hDerivative
  exact ⟨q, hq, hP, hnot, hRep, AX, hAX, hAXdegree.trans hAdegree, hAXregular⟩

/-- Natural conditional Ai endpoint on the SAME literal auxiliary B.
Actual chart/r/embedding data and selected section yield q, regular AX and
full degree3; the strict original window derives WHOLE integrality, and the
actual full-constants downstream argument produces a smaller original R.
No regularity, curve points, canonical residue-field replacement or q is
supplied. Auxiliary/section selection remains an explicit construction. -/
theorem coray_case_Ai_originalSelectedSection_actualAuxiliaryField_nonzeroNativeJet_exists_smaller_originalCubic_closedPoint001
    {K B M : Type u} [Field K] [CharZero K] [Field B] [Field M]
    [Algebra K B] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (P A : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hstrict : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1)
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (jP : Fin 4) (gP : ChartRing (equationIdeal p hp) jP →+* S.residueField P.1),
      gP.comp (chartBaseMap (equationIdeal p hp) jP) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) jP = S.fromSpecResidueField P.1 →
      ∀ (hpP : p.eval₂ (algebraMap K (S.residueField P.1))
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0),
      (∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
        q.eval₂ (algebraMap K (S.residueField P.1))
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0 →
        q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
        IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) →
      ∀ (r : Spec (.of B) ⟶ S) (jA : Fin 4) (gB : ChartRing (equationIdeal p hp) jA →+* B),
      gB.comp (chartBaseMap (equationIdeal p hp) jA) = algebraMap K B →
      Spec.map (CommRingCat.ofHom gB) ≫ chartι (equationIdeal p hp) jA = r →
      r (IsLocalRing.closedPoint B) = A.1 →
      ∀ (sigma : B →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
        (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v) = 0)
        (hAnchor : surfacePlaneJetCoordinates
          (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v jA = 1)
        (s : cubicThroughCoordinateSections p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP),
      gB (cubicThroughPointChartEvaluation p hp n
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) = 0 →
      cubicNormalizedFullJetChartMap p hp jA
        (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v hpJ hAnchor
        (cubicThroughPointChartEvaluation p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) ≠ 0 →
      ∃ R : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 ≤ 3 * n.choose 2 + 1 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree P.1 := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro jP gP hBaseP hPointP hpP hAllIntegral r jA gB hBaseB hChart hOriginalPoint sigma v hpJ hAnchor s hAux hJet
  obtain ⟨q, hq, hqP, hnot, _hRep, AX, hAX, hAXdegree, hAXregular⟩ :=
    originalSelectedSection_actualAuxiliaryField_nonzeroNativeJet_exists_fresh_equation_regular_degreeThreePoint001
      p hp n (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP
      A hAdegree r jA gB hBaseB hChart hOriginalPoint sigma v hpJ hAnchor s hAux hJet
  letI : IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := hAllIntegral q hq hqP hnot
  obtain ⟨PX, hPX, _hPXiso, hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq P jP gP hBaseP hPointP hqP
  have hPXcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1) 3 := by
    rw [hPXdegree]
    exact hPcop
  have hPXstrict : 3 * n.choose 2 + 1 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1 := by
    rw [hPXdegree]
    exact hstrict
  obtain ⟨R, hRcop, hRbound, hRsmall⟩ :=
    coray_case_Ai_integral_originalPoint_exists_smaller_originalCubic_closedPoint_of_regular_degreeThreePoint001
      p q hp hp0 n hn hq hnot PX AX hPXcop hPXstrict hAXdegree hAXregular
  rw [hPX] at hRsmall
  exact ⟨R, hRcop, hRbound, hRsmall⟩

end PfaffianDescent.Coray
