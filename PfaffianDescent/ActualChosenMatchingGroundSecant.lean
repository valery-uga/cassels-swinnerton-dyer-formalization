import PfaffianDescent.ActualProjectivePointIdealFactorization
import PfaffianDescent.QuadraticConjugateSecantGroundFrame
import PfaffianDescent.ActualOriginalMatchingQuadraticLinePair

/-! SOURCE ONLY / UNVERIFIED. A ground embedded P1 through the SAME arbitrary
chosen E-point and its actual exchanged conjugate. The quadratic field,
projectors and exchange are derived by the original matching caller below.
This file constructs the secant; it does not claim its cubic residual branch. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open QuarticNet
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A literal ground projector line is P1 over the original ground field.
The coordinate change retains its original ambient embedding. -/
theorem groundFrameProjectorLine_projectiveLine_iso
    {k : Type u} [Field k] (C : Basis (Fin 4) k (Fin 4 → k)) :
    ∃ e : scheme (projectorLineIdeal (matchingEdgeProjectorMatrix C)) ≅
        Proj (homogeneousSubmodule (Fin 2) k),
      e.hom ≫ ambientToBase (R := k) (σ := Fin 2) =
        toBase (projectorLineIdeal (matchingEdgeProjectorMatrix C)) := by
  let M := basisCoordinateMatrix C
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit C
  have hN : IsUnit M⁻¹.det := Matrix.isUnit_nonsing_inv_det hM
  let I := coordinateMatchingLineIdeal (K := k) false
  let J := projectorLineIdeal (matchingEdgeProjectorMatrix C)
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M⁻¹ hN).toRingHom :=
    projectorLineIdeal_eq_originalMatchingLine C
  let d := linearCoordinateChangeSchemeIso M⁻¹ hN I J hIJ
  let b := coordinateMatchingLineP1Iso k
  have hd : d.hom ≫ toBase J = toBase I :=
    linearCoordinateChangeSchemeIso_hom_toBase M⁻¹ hN I J hIJ
  refine ⟨d.symm ≪≫ b, ?_⟩
  change (d.inv ≫ b.hom) ≫ ambientToBase (R := k) (σ := Fin 2) = toBase J
  rw [Category.assoc, coordinateMatchingLineP1Iso_hom_toBase, ← hd,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem ambientCoefficientMap_identity {E : Type u} [Field E] :
    ambientCoefficientMap (σ := Fin 4) (RingHom.id E) = 𝟙 _ := by
  have h : ambientCoefficientGradedRingHom (σ := Fin 4) (RingHom.id E) =
      GradedRingHom.id (homogeneousSubmodule (Fin 4) E) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_id p
  unfold ambientCoefficientMap
  cases h
  exact Proj.map_id

private theorem ambientCoefficientMap_automorphism_mono
    {k E : Type u} [Field k] [Field E] [Algebra k E] (sigma : E ≃ₐ[k] E) :
    Mono (ambientCoefficientMap (σ := Fin 4) sigma.toRingHom) := by
  have hId : sigma.toRingHom.comp sigma.symm.toRingHom = RingHom.id E := by
    ext z
    exact sigma.apply_symm_apply z
  have hComp : ambientCoefficientMap (σ := Fin 4) sigma.toRingHom ≫
      ambientCoefficientMap (σ := Fin 4) sigma.symm.toRingHom = 𝟙 _ := by
    rw [ambientCoefficientMap_comp, hId]
    exact ambientCoefficientMap_identity
  constructor
  intro W f g hfg
  have h := congrArg (fun t => t ≫ ambientCoefficientMap (σ := Fin 4) sigma.symm.toRingHom) hfg
  simpa only [Category.assoc, hComp, Category.comp_id] using h

/-- The actual geometric secant data. M is a literal homogeneous ground
linear ideal, not a supplied descent witness. Its E-extension contains the
same chosen point and the conjugate produced by the actual exchange square.
The span equality retains the two points' actual coordinate two-space. -/
def ActualChosenMatchingGroundSecantAt
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    (P : Matrix (Fin 4) (Fin 4) E) (sigma : E ≃ₐ[k] E)
    (a : Spec (.of E) ⟶ scheme (projectorLineIdeal P)) : Prop :=
  ∃ j : Fin 4, ∃ g : ChartRing (projectorLineIdeal P) j →+* E,
    g.comp (chartBaseMap (projectorLineIdeal P) j) = RingHom.id E ∧
    Spec.map (CommRingCat.ofHom g) ≫ chartι (projectorLineIdeal P) j = a ∧
    ∃ u v : Fin 4 → k, ∃ C : Basis (Fin 4) k (Fin 4 → k),
      C 0 = u ∧ C 1 = v ∧ LinearIndependent k ![u, v] ∧
      Submodule.span E (Set.range ![(fun m => g (chartCoordinate (projectorLineIdeal P) j m)),
        (fun m => sigma (g (chartCoordinate (projectorLineIdeal P) j m)))]) =
        Submodule.span E (Set.range ![(fun m => algebraMap k E (u m)),
          (fun m => algebraMap k E (v m))]) ∧
      let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
      let ME := projectorLineIdeal ((matchingEdgeProjectorMatrix C).map (algebraMap k E))
      ∃ e : scheme M ≅ Proj (homogeneousSubmodule (Fin 2) k),
        e.hom ≫ ambientToBase (R := k) (σ := Fin 2) = toBase M ∧
        IsClosedImmersion (quotientProjMap M) ∧
        ∃ hBC : M.toIdeal.map (MvPolynomial.map (algebraMap k E)) = ME.toIdeal,
          IsPullback (projectiveCoefficientMap (algebraMap k E) M ME hBC)
            (toBase ME) (toBase M) (Spec.map (CommRingCat.ofHom (algebraMap k E))) ∧
          projectiveCoefficientMap (algebraMap k E) M ME hBC ≫ quotientProjMap M =
            quotientProjMap ME ≫ ambientCoefficientMap (algebraMap k E) ∧
          ∃ hExchange : (projectorLineIdeal P).toIdeal.map (MvPolynomial.map sigma.toRingHom) =
              (projectorLineIdeal (1 - P)).toIdeal,
            ∃ aM bM : Spec (.of E) ⟶ scheme ME,
              ∃ b : Spec (.of E) ⟶ scheme (projectorLineIdeal (1 - P)),
                aM ≫ toBase ME = 𝟙 _ ∧ bM ≫ toBase ME = 𝟙 _ ∧
                b ≫ toBase (projectorLineIdeal (1 - P)) = 𝟙 _ ∧
                aM ≫ quotientProjMap ME = a ≫ quotientProjMap (projectorLineIdeal P) ∧
                b ≫ projectiveCoefficientMap sigma.toRingHom
                  (projectorLineIdeal P) (projectorLineIdeal (1 - P)) hExchange =
                    Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫ a ∧
                bM ≫ quotientProjMap ME = b ≫ quotientProjMap (projectorLineIdeal (1 - P))

/-- Generic structural bridge. No ground line, rank-two space, or scheme
comparison is an input. The original matching factory derives P and sigma. -/
theorem actualChosenMatchingPoint_groundSecant
    {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (P : Matrix (Fin 4) (Fin 4) E)
    (sigma : E ≃ₐ[k] E) (hNe : sigma ≠ 1)
    (hExchange : P.map sigma.toRingHom = 1 - P)
    (a : Spec (.of E) ⟶ scheme (projectorLineIdeal P))
    (ha : a ≫ toBase (projectorLineIdeal P) = 𝟙 _) :
    ActualChosenMatchingGroundSecantAt P sigma a := by
  classical
  let I := projectorLineIdeal P
  let I' := projectorLineIdeal (1 - P)
  obtain ⟨j, g, hb, hg⟩ := exists_chart_hom_eq_of_point I (RingHom.id E) a (by
    simpa only [Spec.map_id] using ha)
  let x := fun m => g (chartCoordinate I j m)
  have hx : x ≠ 0 := by
    intro h
    have hm := congrFun h j
    exact one_ne_zero (by simpa only [x, chartCoordinate_self, map_one, Pi.zero_apply] using hm)
  have hIx (p : MvPolynomial (Fin 4) E) (hp : p ∈ I.toIdeal) :
      p.eval₂ (RingHom.id E) x = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
    simpa only [hom_eval₂, hb, map_zero] using h
  have hPx : P.mulVec x = x := by
    have hKill : (1 - P).mulVec x = 0 := by
      funext m
      have h := hIx (linearCoordinate (1 - P) m) (Ideal.subset_span ⟨m, rfl⟩)
      change MvPolynomial.aeval x (linearCoordinate (1 - P) m) = 0 at h
      rw [linearCoordinate_eval] at h
      exact h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hKill
    exact (sub_eq_zero.mp hKill).symm
  have hLI := exchangedProjector_conjugate_vector_independent P sigma hExchange x hx hPx
  obtain ⟨alpha, hAlpha, u, v, hDecomp, hGround, hExtension, hSpan, C, hC0, hC1⟩ :=
    quadraticConjugateVector_groundFrame hdeg sigma hNe x hLI
  let Q := matchingEdgeProjectorMatrix C
  let QE := Q.map (algebraMap k E)
  let M := projectorLineIdeal Q
  let ME := projectorLineIdeal QE
  have hQu : Q.mulVec u = u := by
    rw [← hC0]
    simpa only [Q] using matchingEdgeProjectorMatrix_mulVec_basis C 0
  have hQv : Q.mulVec v = v := by
    rw [← hC1]
    simpa only [Q] using matchingEdgeProjectorMatrix_mulVec_basis C 1
  have hQU : QE.mulVec (fun m => algebraMap k E (u m)) =
      (fun m => algebraMap k E (u m)) := by
    funext m
    exact (RingHom.map_mulVec (algebraMap k E) Q u m).symm.trans
      (congrArg (algebraMap k E) (congrFun hQu m))
  have hQV : QE.mulVec (fun m => algebraMap k E (v m)) =
      (fun m => algebraMap k E (v m)) := by
    funext m
    exact (RingHom.map_mulVec (algebraMap k E) Q v m).symm.trans
      (congrArg (algebraMap k E) (congrFun hQv m))
  have hQx : QE.mulVec x = x := by
    rw [hDecomp, Matrix.mulVec_add, Matrix.mulVec_smul, hQU, hQV]
  have hMEx : ∀ p ∈ ME.toIdeal, p.eval₂ (RingHom.id E) x = 0 := by
    have hle : ME.toIdeal ≤ RingHom.ker (eval₂Hom (RingHom.id E) x) := by
      apply Ideal.span_le.mpr
      rintro p ⟨m, rfl⟩
      change MvPolynomial.aeval x (linearCoordinate (1 - QE) m) = 0
      rw [linearCoordinate_eval, Matrix.sub_mulVec, Matrix.one_mulVec, hQx, sub_self]
      rfl
    exact hle
  obtain ⟨aM, haM, hAmbient⟩ := actualProjectivePoint_factors_of_chart_equations
    I ME (RingHom.id E) j g hb hMEx
  rw [hg] at hAmbient
  have haM' : aM ≫ toBase ME = 𝟙 _ := by simpa only [Spec.map_id] using haM
  have hLine : I.toIdeal.map (MvPolynomial.map sigma.toRingHom) = I'.toIdeal := by
    rw [projectorLineIdeal_baseChange, hExchange]
  have hStable : ME.toIdeal.map (MvPolynomial.map sigma.toRingHom) = ME.toIdeal := by
    rw [projectorLineIdeal_baseChange]
    have he : QE.map sigma.toRingHom = QE := by
      ext m n
      exact sigma.commutes (Q m n)
    rw [he]
  let sSigma := Spec.map (CommRingCat.ofHom sigma.toRingHom)
  let hLinePB := isPullback_projectiveCoefficientMap sigma.toRingHom I I' hLine
  let hMPB := isPullback_projectiveCoefficientMap sigma.toRingHom ME ME hStable
  let b := hLinePB.lift (sSigma ≫ a) (𝟙 _) (by
    simp only [Category.assoc, ha, Category.comp_id, Category.id_comp])
  let bM := hMPB.lift (sSigma ≫ aM) (𝟙 _) (by
    simp only [Category.assoc, haM', Category.comp_id, Category.id_comp])
  have hbBase : b ≫ toBase I' = 𝟙 _ := hLinePB.lift_snd _ _ _
  have hbMap : b ≫ projectiveCoefficientMap sigma.toRingHom I I' hLine = sSigma ≫ a :=
    hLinePB.lift_fst _ _ _
  have hbMBase : bM ≫ toBase ME = 𝟙 _ := hMPB.lift_snd _ _ _
  have hbMMap : bM ≫ projectiveCoefficientMap sigma.toRingHom ME ME hStable = sSigma ≫ aM :=
    hMPB.lift_fst _ _ _
  letI : Mono (ambientCoefficientMap (σ := Fin 4) sigma.toRingHom) :=
    ambientCoefficientMap_automorphism_mono sigma
  have hbAmbient : bM ≫ quotientProjMap ME = b ≫ quotientProjMap I' := by
    apply (cancel_mono (ambientCoefficientMap (σ := Fin 4) sigma.toRingHom)).mp
    calc
      (bM ≫ quotientProjMap ME) ≫ ambientCoefficientMap sigma.toRingHom =
          bM ≫ projectiveCoefficientMap sigma.toRingHom ME ME hStable ≫ quotientProjMap ME := by
            rw [Category.assoc, ← projectiveCoefficientMap_comp_quotientProjMap]
      _ = sSigma ≫ aM ≫ quotientProjMap ME := by rw [← Category.assoc, hbMMap, Category.assoc]
      _ = sSigma ≫ a ≫ quotientProjMap I := by rw [hAmbient]
      _ = b ≫ projectiveCoefficientMap sigma.toRingHom I I' hLine ≫ quotientProjMap I := by
        rw [← Category.assoc, hbMap, Category.assoc]
      _ = (b ≫ quotientProjMap I') ≫ ambientCoefficientMap sigma.toRingHom := by
        rw [Category.assoc, projectiveCoefficientMap_comp_quotientProjMap, ← Category.assoc]
  obtain ⟨e, he⟩ := groundFrameProjectorLine_projectiveLine_iso C
  let hBC := projectorLineIdeal_baseChange (algebraMap k E) Q
  refine ⟨j, g, hb, hg, u, v, C, hC0, hC1, hGround, hSpan, e, he,
    inferInstance, hBC, isPullback_projectiveCoefficientMap _ _ _ hBC,
    projectiveCoefficientMap_comp_quotientProjMap _ _ _ hBC, hLine, aM, bM, b, haM', hbMBase, hbBase, hAmbient, hbMap, hbAmbient⟩

/-- Original matching branch caller. It derives the SAME E and actual exchange
from the literal original quartic conjugates, tangent frame and cubic jets;
then every chosen point on the first original E-line has a ground secant.
No quadratic-field, ground-line, exchange or comparison certificate is input. -/
theorem originalMatchingBranch_arbitrary_chosen_groundSecants
    {k L : Type u} [Field k] [PerfectField k] [Field L] [Algebra k L]
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k)) (p v : Fin 4 → L)
    (hs : Submodule.span (AlgebraicClosure k)
      (Set.range (fun tau : L →ₐ[k] AlgebraicClosure k => fun m => tau (p m))) = ⊤)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (c d : AlgebraicClosure k) (hc : c ≠ 0) (hd : d ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l (conjugateTangentMatrix full p v hs)) pi =
      skewTangentDirections c 0 0 0 0 d)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint (skewTangentDirections c 0 0 0 0 d) r)
      (linearSubstitution (basisCoordinateMatrix ((conjugateBasis full p hs).reindex pi.symm))
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) F)) = 0) :
    ∃ E : IntermediateField k (AlgebraicClosure k), ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k
        (Set.range (fun m => ((conjugateBasis full p hs).reindex pi.symm) 0 m +
          ((conjugateBasis full p hs).reindex pi.symm) 1 m)) ∧
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = matchingEdgeProjectorMatrix
          ((conjugateBasis full p hs).reindex pi.symm) ∧
        ∃ sigma : E ≃ₐ[k] E, sigma ≠ 1 ∧ sigma ^ 2 = 1 ∧
          (∀ side : Bool,
            ∃ i : scheme (projectorLineIdeal (matchingSideProjector P side)) ⟶
                hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
              IsClosedImmersion i ∧ i ≫ quotientProjMap
                (equationIdeal (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E))) =
                  quotientProjMap (projectorLineIdeal (matchingSideProjector P side))) ∧
          Disjoint (Set.range (quotientProjMap (projectorLineIdeal P)))
            (Set.range (quotientProjMap (projectorLineIdeal (1 - P)))) ∧
          ∀ a : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
            a ≫ toBase (projectorLineIdeal P) = 𝟙 _ →
              ActualChosenMatchingGroundSecantAt P sigma a := by
  classical
  obtain ⟨E, hFD, hDeg, hGal, hE, P, hP, sigma, hNe, hSq, hEx,
      hLine, hOther, hSquares, hP1, hCubic, hDisjoint, hBC, hGroundUnion⟩ :=
    originalMatchingBranch_actualQuadraticLinePair full p v hs l hl pi c d hc hd hU F hF hvan
  letI : FiniteDimensional k E := hFD
  exact ⟨E, hFD, hDeg, hGal, hE, P, hP, sigma, hNe, hSq, hCubic, hDisjoint,
    fun a ha => actualChosenMatchingPoint_groundSecant hDeg P sigma hNe hEx a ha⟩

end PfaffianDescent
