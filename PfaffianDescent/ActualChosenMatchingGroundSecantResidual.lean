import PfaffianDescent.ChosenConjugatePointSameFrameNormalization
import PfaffianDescent.SingleSupportOriginalSuppliedMatchingChosenSecants
import PfaffianDescent.VoisinQuotientAmbientChart

/-! SOURCE ONLY / UNVERIFIED. Complete the chosen-point residual branch on
exactly the E/P/sigma/chart/frame/secant retained by031. The original embedded
line-to-cubic square supplies cubic vanishing. No new secant, field, frame,
normalized root, factorization or residual point is a primitive premise. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective QuarticNet
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem sameSecant_ambientCoefficientMap_identity {E : Type u} [Field E] :
    ambientCoefficientMap (σ := Fin 4) (RingHom.id E) = 𝟙 _ := by
  have h : ambientCoefficientGradedRingHom (σ := Fin 4) (RingHom.id E) =
      GradedRingHom.id (homogeneousSubmodule (Fin 4) E) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_id p
  unfold ambientCoefficientMap
  cases h
  exact Proj.map_id

/-- Derive vanishing on the GIVEN normalized chart coordinates of a,
using its actual embedding into the SAME cubic and ambient square. -/
theorem actualEmbeddedCubic_givenChartCoordinates_vanish
    {E : Type u} [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (F : MvPolynomial (Fin 4) E) (hF : F.IsHomogeneous 3)
    (c : scheme I ⟶ hypersurface F hF)
    (hEmbedding : c ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap I)
    (a : Spec (.of E) ⟶ scheme I) (ha : a ≫ toBase I = 𝟙 _)
    (j : Fin 4) (g : ChartRing I j →+* E)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = a) :
    aeval (fun m => g (chartCoordinate I j m)) F = (0 : E) := by
  let q := a ≫ c
  have hcBase : c ≫ hypersurfaceToBase F hF = toBase I := by
    have h := congrArg (fun t => t ≫ ambientToBase (R := E) (σ := Fin 4)) hEmbedding
    simpa only [Category.assoc, quotientProjMap_toBase] using h
  have hqBase : q ≫ hypersurfaceToBase F hF = 𝟙 _ := by
    dsimp only [q]
    rw [Category.assoc, hcBase]
    exact ha
  let h := g.comp (quotientAmbientChartMap I j)
  have hAmbient : q ≫ hypersurfaceToAmbient F hF ≫
      ambientCoefficientMap (σ := Fin 4) (RingHom.id E) =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) E) (X j)
          (isHomogeneous_X E j) (by decide : 0 < 1) := by
    rw [sameSecant_ambientCoefficientMap_identity, Category.comp_id]
    calc
      q ≫ hypersurfaceToAmbient F hF = a ≫ quotientProjMap I := by
        dsimp only [q, hypersurfaceToAmbient]
        rw [Category.assoc, hEmbedding]
      _ = Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
        rw [← hg, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom h) ≫ _ := by
        rw [chartι_comp_quotientProjMap, ← Category.assoc, ← Spec.map_comp]
        rfl
  have hz := aeval_map_eq_zero_of_ambient_eq (RingHom.id E) F hF (RingHom.id E)
    q (by simpa only [Spec.map_id] using hqBase) j h hAmbient
  simpa only [MvPolynomial.map_id, h, RingHom.comp_apply,
    quotientAmbientChartMap_coordinate] using hz

/-- This is exactly the literal factor/intersection output of033 on fixed C.
The contained and residual branches both keep the SAME embedded M and F. -/
def ActualSameFrameChosenResidualOutcome
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    (sigma : E ≃ₐ[k] E) (alpha : E)
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) : Prop :=
    ∃ r s c d : k,
      alpha ^ 2 = algebraMap k E r + algebraMap k E s * alpha ∧
      groundFrameLineRestriction C F =
        quadraticSecantBinaryFactor r s * quadraticSecantResidualLinearFactor c d s ∧
      MvPolynomial.map (algebraMap k E) (quadraticSecantBinaryFactor r s) =
        (X 1 - MvPolynomial.C alpha * X 0) * (X 1 - MvPolynomial.C (sigma alpha) * X 0) ∧
      ((groundFrameLineRestriction C F = 0 ∧
        let M := projectorLineIdeal (matchingEdgeProjectorMatrix C)
        ∃ i : scheme M ⟶ hypersurface F hF,
          IsClosedImmersion i ∧ i ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap M ∧
          ∃ rM : Spec (.of k) ⟶ scheme M, ∃ rS : Spec (.of k) ⟶ hypersurface F hF,
            rM ≫ toBase M = 𝟙 _ ∧ rS ≫ hypersurfaceToBase F hF = 𝟙 _ ∧
            rS = rM ≫ i ∧
            rM ≫ quotientProjMap M = rS ≫ quotientProjMap (equationIdeal F hF)) ∨
       (groundFrameLineRestriction C F ≠ 0 ∧
        let w : Fin 2 → k := ![d, -(c + s * d)]
        w ≠ 0 ∧ aeval w (quadraticSecantResidualLinearFactor c d s) = 0 ∧
          ActualGroundFrameResidualIntersectionPoint C F hF c d s))

def ActualChosenMatchingGroundSecantWithResidualAt
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
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
      (∃ e : scheme M ≅ Proj (homogeneousSubmodule (Fin 2) k),
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
                bM ≫ quotientProjMap ME = b ≫ quotientProjMap (projectorLineIdeal (1 - P))) ∧
      ∃ lambda alpha : E, lambda ≠ 0 ∧ alpha ≠ sigma alpha ∧
        (fun m => g (chartCoordinate (projectorLineIdeal P) j m)) =
          lambda • ((fun m => algebraMap k E (C 0 m)) +
            alpha • (fun m => algebraMap k E (C 1 m))) ∧
        aeval ![1, alpha] (groundFrameLineRestriction C F) = (0 : E) ∧
        ActualSameFrameChosenResidualOutcome sigma alpha C F hF

/-- Internally strengthen the existing given-point secant, never replace
its chart, frame or embedded ground line. The embedding premise here is
ordinary internal data from the derived quadratic-line package. -/
theorem actualChosenMatchingGroundSecant_add_sameFrameResidual
    {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (hdeg : finrank k E = 2) (P : Matrix (Fin 4) (Fin 4) E)
    (sigma : E ≃ₐ[k] E) (hExchange : P.map sigma.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : scheme (projectorLineIdeal P) ⟶
      hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)))
    (hEmbedding : c ≫ quotientProjMap
      (equationIdeal (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E))) =
        quotientProjMap (projectorLineIdeal P))
    (a : Spec (.of E) ⟶ scheme (projectorLineIdeal P))
    (ha : a ≫ toBase (projectorLineIdeal P) = 𝟙 _)
    (hSecant : ActualChosenMatchingGroundSecantAt P sigma a) :
    ActualChosenMatchingGroundSecantWithResidualAt F hF P sigma a := by
  classical
  obtain ⟨j, g, hb, hg, u, v, C, hC0, hC1, hGround, hSpan, hGeometry⟩ := hSecant
  let I := projectorLineIdeal P
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
  have hSpanC : Submodule.span E (Set.range ![x, fun m => sigma (x m)]) =
      Submodule.span E (Set.range ![(fun m => algebraMap k E (C 0 m)),
        (fun m => algebraMap k E (C 1 m))]) := by
    rw [hC0, hC1]
    exact hSpan
  obtain ⟨lambda, alpha, hlambda, hAlpha, hNorm⟩ :=
    chosenConjugateVector_normalizes_in_same_groundFrame sigma x hLI C hSpanC
  have hFE := actualEmbeddedCubic_givenChartCoordinates_vanish I
    (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)) c hEmbedding a ha j g hg
  have hFx : aeval x F = 0 := by
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHom.id_comp, x] using hFE
  have hRoot := chosenConjugatePoint_sameFrame_cubicRoot C F hF x lambda alpha hlambda hNorm hFx
  have hResidual : ActualSameFrameChosenResidualOutcome sigma alpha C F hF :=
    groundFrame_chosenQuadratic_actualResidualIntersection hdeg sigma alpha hAlpha C F hF hRoot
  exact ⟨j, g, hb, hg, u, v, C, hC0, hC1, hGround, hSpan,
    hGeometry, lambda, alpha, hlambda, hAlpha, hNorm, hRoot, hResidual⟩

end PfaffianDescent
